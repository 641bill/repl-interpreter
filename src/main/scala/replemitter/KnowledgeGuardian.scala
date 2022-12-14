/*
 * Scala.js (https://www.scala-js.org/)
 *
 * Copyright EPFL.
 *
 * Licensed under Apache License 2.0
 * (https://www.apache.org/licenses/LICENSE-2.0).
 *
 * See the NOTICE file distributed with this work for
 * additional information regarding copyright ownership.
 */

package replemitter

import scala.collection.mutable

import org.scalajs.ir.ClassKind
import org.scalajs.ir.Names._
import org.scalajs.ir.Trees._
import org.scalajs.ir.Types.Type

import org.scalajs.linker.interface.ModuleKind
import org.scalajs.linker.standard._
import org.scalajs.linker.standard.ModuleSet.ModuleID

import EmitterNames._

private[replemitter] final class KnowledgeGuardian(config: Emitter.Config) {
  import KnowledgeGuardian._

  private var specialInfo: SpecialInfo = _
  private val classes = mutable.Map.empty[ClassName, Class]
  
  def getAncestors(classDef: ClassDef) = {
    calculateAncestors(classDef) // classes miss some keys
  }

  def calculateAncestors(classDef: ClassDef): List[ClassName] = {
    val ancestors = scala.collection.mutable.Set.empty[ClassName]
    val className = classDef.name.name
    val superClass = classDef.superClass
    val interfaces = classDef.interfaces
    val parents = superClass.toList ::: interfaces
    parents.foreach(parent => {
      val parentName = parent.name
      if (classes.contains(parentName))
        ancestors ++= calculateAncestors(classes(parentName).getInitClass())
    })
    ancestors += ObjectClass
    ancestors += className
    ancestors.toList
  }

  /** Returns `true` if *all* caches should be invalidated.
   *
   *  For global properties that are rarely changed and heavily used (such as
   *  isParentDataAccessed), we do not want to pay the price of the
   *  dependency graph, in terms of memory consumption and time spent
   *  maintaining it. It is a better trade-off to invalidate everything in
   *  the rare events where they do change.
   */
  def update(classDefs: Seq[ClassDef]): Boolean = {
    val hasInlineableInit = computeHasInlineableInit(classDefs)
    val staticFieldMirrors = computeStaticFieldMirrors(classDefs)

    // Object is optional, because the module splitter might remove everything.
    var objectClass: Option[ClassDef] = None
    var classClass: Option[ClassDef] = None
    val hijackedClasses = Iterable.newBuilder[ClassDef]

    // Update classes
    for {
      classDef <- classDefs
    } {
      updateClass(classDef)
    }

    def updateClass(classDef: ClassDef): Unit = {
      val className = classDef.className
      val thisClassHasInlineableInit = hasInlineableInit(className)
      val thisClassStaticFieldMirrors =
        staticFieldMirrors.getOrElse(className, Map.empty)

      classes.get(className).fold[Unit] {
        // new class
        classes.put(className,
            new Class(classDef, thisClassHasInlineableInit, thisClassStaticFieldMirrors, None))
      } { existingCls =>
        existingCls.update(classDef, thisClassHasInlineableInit, thisClassStaticFieldMirrors, None)
      }

      classDef.className match {
        case ClassClass =>
          classClass = Some(classDef)

        case ObjectClass =>
          objectClass = Some(classDef)

        case name if HijackedClasses(name) =>
          hijackedClasses += classDef

        case _ =>
      }
    }

    // Garbage collection
    // classes.filterInPlace((_, cls) => cls.testAndResetIsAlive())

    val invalidateAll = {
      if (specialInfo == null) {
        specialInfo = new SpecialInfo(objectClass, classClass, hijackedClasses.result())
        false
      } else {
        specialInfo.update(objectClass, classClass, hijackedClasses.result())
      }
    }

    if (invalidateAll) {
      classes.valuesIterator.foreach(_.unregisterAll())
      specialInfo.unregisterAll()
    }

    invalidateAll
  }

  private def computeHasInlineableInit(classDefs: Seq[ClassDef]): Set[ClassName] = {
    val scalaClassDefs = classDefs.filter(_.kind.isClass)

    val classesWithInstantiatedSubclasses = scalaClassDefs
      // .withFilter(_.hasInstances)
      .flatMap(_.superClass)
      .map(_.name)
      .toSet

    def enableInlineableInitFor(classDef: ClassDef): Boolean = {
      /* We can enable inlined init if all of the following apply:
       * - It does not have any instantiated subclass
       * - It has exactly one constructor
       *
       * By construction, this is always true for module classes.
       */
      !classesWithInstantiatedSubclasses(classDef.className) && {
        classDef.memberDefs.collect{
          case m: MethodDef => m
        } .count(
            x => x.flags.namespace == MemberNamespace.Constructor) == 1
      }
    }

    scalaClassDefs
      .withFilter(enableInlineableInitFor(_))
      .map(_.className)
      .toSet
  }

  private def computeStaticFieldMirrors(
      classDefs: Seq[ClassDef]): Map[ClassName, Map[FieldName, List[String]]] = {
    if (config.moduleKind != ModuleKind.NoModule) {
      Map.empty
    } else {
      var result = Map.empty[ClassName, Map[FieldName, List[String]]]
      val classNameToTopLevelExports = classDefs.map(classDef => (classDef.name.name -> classDef.topLevelExportDefs)).toMap
      for {
        (className, topLevelExportDefs) <- classNameToTopLevelExports
        topLevelExportDef <- topLevelExportDefs
      } {
        topLevelExportDef match {
          case TopLevelFieldExportDef(_, exportName, FieldIdent(fieldName)) =>
            val mirrors = result.getOrElse(className, Map.empty)
            val newExportNames = exportName :: mirrors.getOrElse(fieldName, Nil)
            val newMirrors = mirrors.updated(fieldName, newExportNames)
            result = result.updated(className, newMirrors)

          case _ =>
        }
      }
      result
    }
  }

  abstract class KnowledgeAccessor extends GlobalKnowledge with Invalidatable {
    /* In theory, a KnowledgeAccessor should *contain* a GlobalKnowledge, not
     * *be* a GlobalKnowledge. We organize it that way to reduce memory
     * footprint and pointer indirections.
     */

    def isParentDataAccessed: Boolean = {
      false
    }

    def isClassClassInstantiated: Boolean =
      true

    def isInterface(className: ClassName): Boolean =
      if (classes.contains(className))
        classes(className).askIsInterface(this)
      else
        false

    def getAllScalaClassFieldDefs(className: ClassName): List[(ClassName, List[AnyFieldDef])] =
      ???

    def hasInlineableInit(className: ClassName): Boolean = {
      false
    }

    def hasStoredSuperClass(className: ClassName): Boolean =
        classes(className).askHasStoredSuperClass(this)

    def hasInstances(className: ClassName): Boolean =
      true

    def getJSClassCaptureTypes(className: ClassName): Option[List[Type]] =
      classes(className).askJSClassCaptureTypes(this)

    def getJSNativeLoadSpec(className: ClassName): Option[JSNativeLoadSpec] =
      if (classes.contains(className))
        classes(className).askJSNativeLoadSpec(this)
      else
        None

    def getJSNativeLoadSpec(className: ClassName, member: MethodName): JSNativeLoadSpec =
      classes(className).askJSNativeLoadSpec(this, member)

    def getSuperClassOfJSClass(className: ClassName): ClassName =
      classes(className).askJSSuperClass(this)

    def getJSClassFieldDefs(className: ClassName): List[AnyFieldDef] =
      if (classes.contains(className))
        classes(className).askJSClassFieldDefs(this)
      else
        Nil

    def getStaticFieldMirrors(className: ClassName, field: FieldName): List[String] =
      if (classes.contains(className))
        classes(className).askStaticFieldMirrors(this, field)
      else
        Nil

    def getModule(className: ClassName): ModuleID =
      classes(className).askModule(this)

    def methodsInRepresentativeClasses(): List[(MethodName, Set[ClassName])] =
      if (specialInfo == null)
        Nil
      else
        specialInfo.askMethodsInRepresentativeClasses(this)

    def methodsInObject(): List[MethodDef] =
      if (specialInfo == null)
        Nil
      else
        specialInfo.askMethodsInObject(this)

    def hijackedDescendants(className: ClassName): Set[ClassName] =
      if (specialInfo == null)
        Set.empty
      else
        specialInfo.askHijackedDescendants(this).getOrElse(className, Set.empty)

    def isAncestorOfHijackedClass(className: ClassName): Boolean = {
      if (specialInfo == null)
        false
      else
        specialInfo.askHijackedDescendants(this).contains(className)
    }
  }

  private class Class(initClass: ClassDef,
      initHasInlineableInit: Boolean,
      initStaticFieldMirrors: Map[FieldName, List[String]],
      initModule: Option[ModuleID])
      extends Unregisterable {

    private val className = initClass.className

    private var isAlive: Boolean = true

    private var isInterface = computeIsInterface(initClass)
    private var hasInlineableInit = initHasInlineableInit
    private var hasStoredSuperClass = computeHasStoredSuperClass(initClass)
    private var hasInstances = true
    private var jsClassCaptureTypes = computeJSClassCaptureTypes(initClass)
    private var jsNativeLoadSpec = computeJSNativeLoadSpec(initClass)
    private var jsNativeMemberLoadSpecs = computeJSNativeMemberLoadSpecs(initClass)
    private var superClass = computeSuperClass(initClass)
    private var fieldDefs = computeFieldDefs(initClass)
    private var staticFieldMirrors = initStaticFieldMirrors
    private var module = initModule

    private val isInterfaceAskers = mutable.Set.empty[Invalidatable]
    private val hasInlineableInitAskers = mutable.Set.empty[Invalidatable]
    private val hasStoredSuperClassAskers = mutable.Set.empty[Invalidatable]
    private val hasInstancesAskers = mutable.Set.empty[Invalidatable]
    private val jsClassCaptureTypesAskers = mutable.Set.empty[Invalidatable]
    private val jsNativeLoadSpecAskers = mutable.Set.empty[Invalidatable]
    private val jsNativeMemberLoadSpecsAskers = mutable.Set.empty[Invalidatable]
    private val superClassAskers = mutable.Set.empty[Invalidatable]
    private val fieldDefsAskers = mutable.Set.empty[Invalidatable]
    private val staticFieldMirrorsAskers = mutable.Set.empty[Invalidatable]
    private val moduleAskers = mutable.Set.empty[Invalidatable]

    def update(linkedClass: ClassDef, newHasInlineableInit: Boolean,
        newStaticFieldMirrors: Map[FieldName, List[String]],
        newModule: Option[ModuleID]): Unit = {
      isAlive = true

      val newIsInterface = computeIsInterface(linkedClass)
      if (newIsInterface != isInterface) {
        isInterface = newIsInterface
        invalidateAskers(isInterfaceAskers)
      }

      if (newHasInlineableInit != hasInlineableInit) {
        hasInlineableInit = newHasInlineableInit
        invalidateAskers(hasInlineableInitAskers)
      }

      val newHasStoredSuperClass = computeHasStoredSuperClass(linkedClass)
      if (newHasStoredSuperClass != hasStoredSuperClass) {
        hasStoredSuperClass = newHasStoredSuperClass
        invalidateAskers(hasStoredSuperClassAskers)
      }

      val newHasInstances = true
      if (newHasInstances != hasInstances) {
        hasInstances = newHasInstances
        invalidateAskers(hasInstancesAskers)
      }

      val newJSClassCaptureTypes = computeJSClassCaptureTypes(linkedClass)
      if (newJSClassCaptureTypes != jsClassCaptureTypes) {
        jsClassCaptureTypes = newJSClassCaptureTypes
        invalidateAskers(jsClassCaptureTypesAskers)
      }

      val newJSNativeLoadSpec = computeJSNativeLoadSpec(linkedClass)
      if (newJSNativeLoadSpec != jsNativeLoadSpec) {
        jsNativeLoadSpec = newJSNativeLoadSpec
        invalidateAskers(jsNativeLoadSpecAskers)
      }

      val newJSNativeMemberLoadSpecs = computeJSNativeMemberLoadSpecs(linkedClass)
      if (newJSNativeMemberLoadSpecs != jsNativeMemberLoadSpecs) {
        jsNativeMemberLoadSpecs = newJSNativeMemberLoadSpecs
        invalidateAskers(jsNativeMemberLoadSpecsAskers)
      }

      val newSuperClass = computeSuperClass(linkedClass)
      if (newSuperClass != superClass) {
        superClass = newSuperClass
        invalidateAskers(superClassAskers)
      }

      val newFieldDefs = computeFieldDefs(linkedClass)
      if (newFieldDefs != fieldDefs) {
        fieldDefs = newFieldDefs
        invalidateAskers(fieldDefsAskers)
      }

      if (newStaticFieldMirrors != staticFieldMirrors) {
        staticFieldMirrors = newStaticFieldMirrors
        invalidateAskers(staticFieldMirrorsAskers)
      }

      if (newModule != module) {
        module = newModule
        invalidateAskers(moduleAskers)
      }
    }

    private def computeIsInterface(linkedClass: ClassDef): Boolean =
      linkedClass.kind == ClassKind.Interface

    private def computeHasStoredSuperClass(linkedClass: ClassDef): Boolean =
      linkedClass.jsSuperClass.isDefined

    private def computeJSClassCaptureTypes(linkedClass: ClassDef): Option[List[Type]] =
      linkedClass.jsClassCaptures.map(_.map(_.ptpe))

    private def computeJSNativeLoadSpec(linkedClass: ClassDef): Option[JSNativeLoadSpec] =
      linkedClass.jsNativeLoadSpec

    private def computeJSNativeMemberLoadSpecs(
        linkedClass: ClassDef): Map[MethodName, JSNativeLoadSpec] = {
      val jsNativeMembers = linkedClass.memberDefs.collect({
        case m: JSNativeMemberDef => m
      })
      
      if (jsNativeMembers.isEmpty) {
        // Fast path
        Map.empty
      } else {
        jsNativeMembers
          .map(m => m.name.name -> m.jsNativeLoadSpec)
          .toMap
      }
    }

    private def computeSuperClass(linkedClass: ClassDef): ClassName =
      linkedClass.superClass.fold[ClassName](null.asInstanceOf[ClassName])(_.name)

    private def computeFieldDefs(linkedClass: ClassDef): List[AnyFieldDef] =
      linkedClass.memberDefs.collect{
        case a: AnyFieldDef => a
      }

    def testAndResetIsAlive(): Boolean = {
      val result = isAlive
      isAlive = false
      result
    }

    def askIsInterface(invalidatable: Invalidatable): Boolean = {
      invalidatable.registeredTo(this)
      isInterfaceAskers += invalidatable
      isInterface
    }

    def askAllScalaClassFieldDefs(
        invalidatable: Invalidatable): List[(ClassName, List[AnyFieldDef])] = {
      invalidatable.registeredTo(this)
      superClassAskers += invalidatable
      fieldDefsAskers += invalidatable
      val inheritedFieldDefs =
        if (superClass == null) Nil
        else classes(superClass).askAllScalaClassFieldDefs(invalidatable)
      inheritedFieldDefs :+ (className -> fieldDefs)
    }

    def askHasInlineableInit(invalidatable: Invalidatable): Boolean = {
      invalidatable.registeredTo(this)
      hasInlineableInitAskers += invalidatable
      hasInlineableInit
    }

    def askHasStoredSuperClass(invalidatable: Invalidatable): Boolean = {
      invalidatable.registeredTo(this)
      hasStoredSuperClassAskers += invalidatable
      hasStoredSuperClass
    }

    def askHasInstances(invalidatable: Invalidatable): Boolean = {
      invalidatable.registeredTo(this)
      hasInstancesAskers += invalidatable
      hasInstances
    }

    def askJSClassCaptureTypes(invalidatable: Invalidatable): Option[List[Type]] = {
      invalidatable.registeredTo(this)
      jsClassCaptureTypesAskers += invalidatable
      jsClassCaptureTypes
    }

    def askJSNativeLoadSpec(invalidatable: Invalidatable): Option[JSNativeLoadSpec] = {
      invalidatable.registeredTo(this)
      jsNativeLoadSpecAskers += invalidatable
      jsNativeLoadSpec
    }

    def askJSNativeLoadSpec(invalidatable: Invalidatable, member: MethodName): JSNativeLoadSpec = {
      invalidatable.registeredTo(this)
      jsNativeMemberLoadSpecsAskers += invalidatable
      jsNativeMemberLoadSpecs(member)
    }

    def askJSSuperClass(invalidatable: Invalidatable): ClassName = {
      invalidatable.registeredTo(this)
      superClassAskers += invalidatable
      superClass
    }

    def askJSClassFieldDefs(invalidatable: Invalidatable): List[AnyFieldDef] = {
      invalidatable.registeredTo(this)
      fieldDefsAskers += invalidatable
      fieldDefs
    }

    def askStaticFieldMirrors(invalidatable: Invalidatable,
        field: FieldName): List[String] = {
      invalidatable.registeredTo(this)
      staticFieldMirrorsAskers += invalidatable
      staticFieldMirrors.getOrElse(field, Nil)
    }

    def askModule(invalidatable: Invalidatable): ModuleID = {
      invalidatable.registeredTo(this)
      moduleAskers += invalidatable
      module.getOrElse {
        throw new AssertionError(
            "trying to get module of abstract class " + className.nameString)
      }
    }

    def getInitClass(): ClassDef =
      initClass

    def unregister(invalidatable: Invalidatable): Unit = {
      isInterfaceAskers -= invalidatable
      hasInlineableInitAskers -= invalidatable
      hasStoredSuperClassAskers -= invalidatable
      hasInstancesAskers -= invalidatable
      jsClassCaptureTypesAskers -= invalidatable
      jsNativeLoadSpecAskers -= invalidatable
      jsNativeMemberLoadSpecsAskers -= invalidatable
      superClassAskers -= invalidatable
      fieldDefsAskers -= invalidatable
      staticFieldMirrorsAskers -= invalidatable
      moduleAskers -= invalidatable
    }

    /** Call this when we invalidate all caches. */
    def unregisterAll(): Unit = {
      isInterfaceAskers.clear()
      hasInlineableInitAskers.clear()
      hasStoredSuperClassAskers.clear()
      hasInstancesAskers.clear()
      jsClassCaptureTypesAskers.clear()
      jsNativeLoadSpecAskers.clear()
      jsNativeMemberLoadSpecsAskers.clear()
      superClassAskers.clear()
      fieldDefsAskers.clear()
      staticFieldMirrorsAskers.clear()
      moduleAskers.clear()
    }
  }

  private class SpecialInfo(initObjectClass: Option[ClassDef],
      initClassClass: Option[ClassDef],
      initHijackedClasses: Iterable[ClassDef]) extends Unregisterable {

    private var isClassClassInstantiated =
      computeIsClassClassInstantiated(initClassClass)

    private var isParentDataAccessed =
      computeIsParentDataAccessed(initClassClass)

    private var methodsInRepresentativeClasses =
      computeMethodsInRepresentativeClasses(initObjectClass, initHijackedClasses)

    private var methodsInObject =
      computeMethodsInObject(initObjectClass)

    private var hijackedDescendants =
      computeHijackedDescendants(initHijackedClasses)

    private val isClassClassInstantiatedAskers = mutable.Set.empty[Invalidatable]
    private val methodsInRepresentativeClassesAskers = mutable.Set.empty[Invalidatable]
    private val methodsInObjectAskers = mutable.Set.empty[Invalidatable]

    def update(objectClass: Option[ClassDef], classClass: Option[ClassDef],
        hijackedClasses: Iterable[ClassDef]): Boolean = {
      var invalidateAll = false

      val newIsClassClassInstantiated = computeIsClassClassInstantiated(classClass)
      if (newIsClassClassInstantiated != isClassClassInstantiated) {
        isClassClassInstantiated = newIsClassClassInstantiated
        invalidateAskers(isClassClassInstantiatedAskers)
      }

      val newIsParentDataAccessed = computeIsParentDataAccessed(classClass)
      if (newIsParentDataAccessed != isParentDataAccessed) {
        isParentDataAccessed = newIsParentDataAccessed
        invalidateAll = true
      }

      val newMethodsInRepresentativeClasses =
          computeMethodsInRepresentativeClasses(objectClass, hijackedClasses)
      if (newMethodsInRepresentativeClasses != methodsInRepresentativeClasses) {
        methodsInRepresentativeClasses = newMethodsInRepresentativeClasses
        invalidateAskers(methodsInRepresentativeClassesAskers)
      }

      /* Usage-sites of methodsInObject never cache.
       * Therefore, we do not bother comparing (which is expensive), but simply
       * invalidate.
       */
      methodsInObject = computeMethodsInObject(objectClass)
      invalidateAskers(methodsInObjectAskers)

      val newHijackedDescendants = computeHijackedDescendants(hijackedClasses)
      if (newHijackedDescendants != hijackedDescendants) {
        hijackedDescendants = newHijackedDescendants
        invalidateAll = true
      }

      invalidateAll
    }

    private def computeIsClassClassInstantiated(classClass: Option[ClassDef]): Boolean =
      true

    private def computeIsParentDataAccessed(classClass: Option[ClassDef]): Boolean = {
      def methodExists(linkedClass: ClassDef, methodName: MethodName): Boolean = {
        linkedClass.memberDefs.collect{
          case m: MethodDef => m
        }.exists { m =>
          m.flags.namespace == MemberNamespace.Public &&
          m.methodName == methodName
        }
      }

      classClass.exists(methodExists(_, getSuperclassMethodName))
    }

    private def computeMethodsInRepresentativeClasses(objectClass: Option[ClassDef],
        hijackedClasses: Iterable[ClassDef]): List[(MethodName, Set[ClassName])] = {
      val representativeClasses =
        objectClass.iterator ++ hijackedClasses.iterator

      val result = mutable.HashMap.empty[MethodName, mutable.Set[ClassName]]

      for {
        representativeClass <- representativeClasses
        method <- representativeClass.memberDefs.collect {
          case m: MethodDef => m
        }
        if method.flags.namespace == MemberNamespace.Public
      } {
        result.getOrElseUpdate(method.methodName, mutable.Set.empty) +=
          representativeClass.className
      }

      result.toList.sortBy(_._1.nameString).map(kv => (kv._1, kv._2.toSet))
    }

    private def computeMethodsInObject(objectClass: Option[ClassDef]): List[MethodDef] = {
      objectClass.toList.flatMap(
          _.memberDefs.collect({ case m: MethodDef => m })
          filter(_.flags.namespace == MemberNamespace.Public))
    }

    // Recursively calculate all ancestors by walking the inheritance hierarchy
    // using the information from classes: mutable.Map.empty[ClassName, Class]
    def calculateAncestors(classDef: ClassDef): List[ClassName] = {
      var ancestors = List[ClassName]()
      val className = classDef.name.name
      val superClass = classDef.superClass
      if (superClass.isDefined) {
        val superClassName = superClass.get.name
        if (superClassName != className && classes.contains(superClassName)) 
          ancestors = calculateAncestors(classes(superClassName).getInitClass())
      }
      ancestors
    }
    

    private def computeHijackedDescendants(
        hijackedClasses: Iterable[ClassDef]): Map[ClassName, Set[ClassName]] = {
      val pairs = for {
        hijackedClass <- hijackedClasses
        ancestor <- calculateAncestors(hijackedClass)
        if ancestor != hijackedClass.className
      } yield {
        (ancestor, hijackedClass)
      }

      for {
        (ancestor, pairs) <- pairs.groupBy(_._1)
      } yield {
        (ancestor, pairs.map(_._2.className).toSet)
      }
    }

    def askIsClassClassInstantiated(invalidatable: Invalidatable): Boolean = {
      invalidatable.registeredTo(this)
      isClassClassInstantiatedAskers += invalidatable
      isClassClassInstantiated
    }

    def askIsParentDataAccessed(invalidatable: Invalidatable): Boolean =
      isParentDataAccessed

    def askMethodsInRepresentativeClasses(
        invalidatable: Invalidatable): List[(MethodName, Set[ClassName])] = {
      invalidatable.registeredTo(this)
      methodsInRepresentativeClassesAskers += invalidatable
      methodsInRepresentativeClasses
    }

    def askMethodsInObject(invalidatable: Invalidatable): List[MethodDef] = {
      invalidatable.registeredTo(this)
      methodsInObjectAskers += invalidatable
      methodsInObject
    }

    def askHijackedDescendants(
        invalidatable: Invalidatable): Map[ClassName, Set[ClassName]] = {
      hijackedDescendants
    }

    def unregister(invalidatable: Invalidatable): Unit = {
      isClassClassInstantiatedAskers -= invalidatable
      methodsInRepresentativeClassesAskers -= invalidatable
      methodsInObjectAskers -= invalidatable
    }

    /** Call this when we invalidate all caches. */
    def unregisterAll(): Unit = {
      isClassClassInstantiatedAskers.clear()
      methodsInRepresentativeClassesAskers.clear()
      methodsInObjectAskers.clear()
    }
  }

  private def invalidateAskers(askers: mutable.Set[Invalidatable]): Unit = {
    /* Calling `invalidate` cause the `Invalidatable` to call `unregister()` in
     * this class, which will mutate the `askers` set. Therefore, we cannot
     * directly iterate over `askers`, and need to take a snapshot instead.
     */
    val snapshot = askers.toSeq
    askers.clear()
    snapshot.foreach(_.invalidate())
  }
}

private[replemitter] object KnowledgeGuardian {
  private trait Unregisterable {
    def unregister(invalidatable: Invalidatable): Unit
  }

  trait Invalidatable {
    private val _registeredTo = mutable.Set.empty[Unregisterable]

    private[KnowledgeGuardian] def registeredTo(
        unregisterable: Unregisterable): Unit = {
      _registeredTo += unregisterable
    }

    /** To be overridden to perform subclass-specific invalidation.
     *
     *  All overrides should call the default implementation with `super` so
     *  that this `Invalidatable` is unregistered from the dependency graph.
     */
    def invalidate(): Unit = {
      _registeredTo.foreach(_.unregister(this))
      _registeredTo.clear()
    }
  }
}
