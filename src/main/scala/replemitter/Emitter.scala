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

import scala.annotation.tailrec

import scala.collection.mutable

import org.scalajs.ir.{ClassKind, Position}
import org.scalajs.ir.Names._
import org.scalajs.ir.OriginalName.NoOriginalName
import org.scalajs.ir.Trees.{JSNativeLoadSpec, MemberNamespace}

import org.scalajs.logging._

import org.scalajs.linker.interface._
import org.scalajs.linker.standard._
import org.scalajs.linker.standard.ModuleSet.ModuleID
import org.scalajs.linker.backend.javascript.{Trees => js, _}
import org.scalajs.linker.backend.emitter.PrivateLibHolder
import org.scalajs.linker.backend.javascript
import replinterpreter.IRBuilder

import EmitterNames._
import GlobalRefUtils._
import org.scalajs.ir.Trees
import scala.concurrent._
import org.scalajs.linker.interface.unstable.IRFileImpl
import org.scalajs.ir.Types
import scala.scalajs.js.annotation._
import replinterpreter.scalajsCom

@JSImport("vm", "Script")
@scala.scalajs.js.native
class Script(code: String, options: scala.scalajs.js.Any) extends scala.scalajs.js.Object {
  def runInThisContext(): Unit = scala.scalajs.js.native
}

/** Emits a desugared JS tree to a builder */
final class Emitter(config: Emitter.Config) {

  implicit val pos = Position.NoPosition
  import Emitter._
  import config._

  private val knowledgeGuardian = new KnowledgeGuardian(config)

  private val uncachedKnowledge = new knowledgeGuardian.KnowledgeAccessor {}

  private val nameGen: NameGen = new NameGen

  private class State(val lastMentionedDangerousGlobalRefs: Set[String]) {
    val sjsGen: SJSGen = {
      val jsGen = new JSGen(config)
      val varGen = new VarGen(jsGen, nameGen, lastMentionedDangerousGlobalRefs)
      new SJSGen(jsGen, nameGen, varGen)
    }

    val classEmitter: ClassEmitter = new ClassEmitter(sjsGen)

    val coreJSLibCache: CoreJSLibCache = new CoreJSLibCache

    val classCaches: mutable.Map[ClassID, ClassCache] = mutable.Map.empty
  }

  private var state: State = new State(Set.empty)

  private def jsGen: JSGen = state.sjsGen.jsGen
  private def sjsGen: SJSGen = state.sjsGen
  private def classEmitter: ClassEmitter = state.classEmitter
  private def classCaches: mutable.Map[ClassID, ClassCache] = state.classCaches
  private def functionEmitter = new FunctionEmitter(sjsGen)

  private[this] var statsClassesReused: Int = 0
  private[this] var statsClassesInvalidated: Int = 0
  private[this] var statsMethodsReused: Int = 0
  private[this] var statsMethodsInvalidated: Int = 0

  val symbolRequirements: SymbolRequirement =
    Emitter.symbolRequirements(config)

  val injectedIRFiles: Seq[IRFile] = PrivateLibHolder.files

	val coreJSLibFlag = new java.util.concurrent.atomic.AtomicBoolean(true)

  // Don't generate classDefs with the same name twice
  val classNameSet = mutable.Set.empty[String]

  def loadIRFiles(irFiles: Seq[IRFile]): Future[Unit] = {
    import ExecutionContext.Implicits.global
    import replinterpreter.IRBuilder.noPosition
    Future.traverse(irFiles ++ injectedIRFiles)(i => IRFileImpl.fromIRFile(i).tree).
      map(loadClassDefs(_))
  }

  // A counter to count the number of times loadClassDefs is called
  val counter = new java.util.concurrent.atomic.AtomicInteger(0)

  val moduleInitializerCounter = new java.util.concurrent.atomic.AtomicInteger(0)

  def loadClassDefs(classDefs: Seq[Trees.ClassDef]): Unit = {
    // Filter out classes that have already been loaded
    val filteredClassDefs = classDefs.filterNot(c => classNameSet.contains(c.name.name.nameString))
    // Add all classNames to the set
    classNameSet ++= filteredClassDefs.map(_.name.name.nameString)
    // Update all classdefs before genclass
    val _ = knowledgeGuardian.update(filteredClassDefs)

    val generatedClasses = filteredClassDefs.toList.map((genclass(_)))
    // Order it by number of ancestors
    val coreJSLib =
      if (coreJSLibFlag.get() == true) {
        coreJSLibFlag.set(false)
        Some(state.coreJSLibCache.build().value) // Only emit once the coreJSLib
      } else {
        None
      }

    def classIter = generatedClasses.iterator

    val objectClass = classIter.find(_.className == ObjectClass)

    /* Emit everything but module imports in the appropriate order.
      *
      * We do not emit module imports to be able to assert that the
      * resulting module is non-empty. This is a non-trivial condition that
      * requires consistency between the Analyzer and the Emitter. As such,
      * it is crucial that we verify it.
      */

    val defTreesBuilder = List.newBuilder[js.Tree]

    if (objectClass.isDefined) {
      defTreesBuilder ++= (
        /* The definitions of the CoreJSLib that come before the definition
          * of `j.l.Object`. They depend on nothing else.
          */

        coreJSLib.map(_.preObjectDefinitions).iterator ++

        /* The definition of `j.l.Object` class. Unlike other classes, this
          * does not include its instance tests nor metadata.
          */
        objectClass.get.main ++

        /* The definitions of the CoreJSLib that come after the definition
          * of `j.l.Object` because they depend on it. This includes the
          * definitions of the array classes, as well as type data for
          * primitive types and for `j.l.Object`.
          */
        coreJSLib.map(_.postObjectDefinitions).iterator
      )
    }

    defTreesBuilder ++= (
      /* All class definitions, except `j.l.Object`, which depend on
        * nothing but their superclasses.
        */
      classIter.filterNot(_.className == ObjectClass).flatMap(_.main)
    )

    if (objectClass.isDefined) {
      defTreesBuilder ++= (
        /* The initialization of the CoreJSLib, which depends on the
          * definition of classes (n.b. the RuntimeLong class).
          */
        coreJSLib.map(_.initialization).iterator
      )
    }

    defTreesBuilder ++= (
      /* All static field definitions, which depend on nothing, except
        * those of type Long which need $L0.
        */
      classIter.flatMap(_.staticFields) ++

      /* All static initializers, which in the worst case can observe some
        * "zero" state of other static field definitions, but must not
        * observe a *non-initialized* (undefined) state.
        */
      classIter.flatMap(_.staticInitialization)
    )

    val defTrees = defTreesBuilder.result()
    val stringWriter = new java.io.StringWriter()
    new javascript.Printers.JSTreePrinter(stringWriter).printTopLevelTree(js.Block(defTrees))
    val generatedCode = stringWriter.toString()

    // Write to file
    scala.scalajs.js.Dynamic.global.require("fs").writeFileSync("generated-code" + counter.get() + ".js", generatedCode)

    val script = new Script(generatedCode, scala.scalajs.js.Dynamic.literal(filename = "generated-code" + counter.getAndAdd(1) + ".js"))
    script.runInThisContext()
    ()
  }

  def runModuleInitializers(moduleInitializers: Seq[ModuleInitializer]): Future[Unit] = {
    import ExecutionContext.Implicits.global
    val initializerTrees = moduleInitializers.map(moduleInitializer =>
      classEmitter.genModuleInitializer(moduleInitializer.initializer)(uncachedKnowledge)).map(_.value)
    val defTrees = js.Block(
      initializerTrees
    )(Position.NoPosition)

    // Write to file
    scala.scalajs.js.Dynamic.global.require("fs").writeFileSync("generated-code-run" + moduleInitializerCounter.get() + ".js", defTrees.show)
    
    val script = new Script(defTrees.show, scala.scalajs.js.Dynamic.literal(filename = "generated-code-run" + moduleInitializerCounter.getAndAdd(1) + ".js"))
    script.runInThisContext()
    Future[Unit](())
  }

  private def genModuleImports(module: ModuleSet.Module): WithGlobals[List[js.Tree]] = {
    implicit val pos = Position.NoPosition

    def importParts = (
        (
            module.externalDependencies.map { x =>
              sjsGen.varGen.externalModuleFieldIdent(x) -> x
            }
        ) ++ (
            module.internalDependencies.map { x =>
              sjsGen.varGen.internalModuleFieldIdent(x) -> config.internalModulePattern(x)
            }
        )
    ).toList.sortBy(_._1.name)

    moduleKind match {
      case ModuleKind.NoModule =>
        WithGlobals(Nil)

      case ModuleKind.ESModule =>
        val imports = importParts.map { case (ident, moduleName) =>
          val from = js.StringLiteral(moduleName)
          js.ImportNamespace(ident, from)
        }
        WithGlobals(imports)

      case ModuleKind.CommonJSModule =>
        val imports = importParts.map { case (ident, moduleName) =>
          for (requireRef <- jsGen.globalRef("require")) yield {
            val rhs = js.Apply(requireRef, List(js.StringLiteral(moduleName)))
            jsGen.genLet(ident, mutable = false, rhs)
          }
        }
        WithGlobals.list(imports)
    }
  }

  private def compareClasses(lhs: LinkedClass, rhs: LinkedClass) = {
    val lhsAC = lhs.ancestors.size
    val rhsAC = rhs.ancestors.size
    if (lhsAC != rhsAC) lhsAC < rhsAC
    else lhs.className.compareTo(rhs.className) < 0
  }

  private def genclass(classDef: Trees.ClassDef): GeneratedClass = {

    val className = classDef.name.name

    val classCache: ClassCache = new ClassCache()

    val kind = classDef.kind

    val main = List.newBuilder[js.Tree]

    val (linkedInlineableInit, linkedMethods) =
      classEmitter.extractInlineableInit(classDef)

    // Symbols for private JS fields
    if (kind.isJSClass) {
      val fieldDefs = classEmitter.genCreatePrivateJSFieldDefsOfJSClass(classDef)(classCache)
      main ++= fieldDefs.value
    }

    // Static-like methods
    for (m <- linkedMethods) {
      val methodDef = m
      val namespace = methodDef.flags.namespace

      val emitAsStaticLike = {
        namespace != MemberNamespace.Public ||
        kind == ClassKind.Interface ||
        kind == ClassKind.HijackedClass
      }

      if (emitAsStaticLike) {
        val methodCache =
          classCache.getStaticLikeMethodCache(namespace, methodDef.methodName)

        if (methodDef.body.isDefined)
          main += classEmitter.genStaticLikeMethod(className, methodDef)(methodCache).value
      }
    }

    // Class definition
    if (kind.isAnyNonNativeClass) {
      val useESClass = if (jsGen.useClassesForRegularClasses) {
        assert(jsGen.useClassesForJSClassesAndThrowables)
        true
      } else {
        jsGen.useClassesForJSClassesAndThrowables &&
        kind.isJSClass
      }

      // JS constructor
      val ctorCache = classCache.getConstructorCache()
      val initToInline = linkedInlineableInit.map(_.value)
      val ctorWithGlobals = classEmitter.genConstructor(classDef, useESClass, initToInline)(ctorCache)

      /* Bridges from Throwable to methods of Object, which are necessary
       * because Throwable is rewired to extend JavaScript's Error instead of
       * j.l.Object.
       */
      val linkedMethodsAndBridges = if (ClassEmitter.shouldExtendJSError(classDef)) {
        val existingMethods = linkedMethods
          .withFilter(_.flags.namespace == MemberNamespace.Public)
          .map(_.methodName)
          .toSet

        val bridges = for {
          m <- uncachedKnowledge.methodsInObject()
          methodName = m.methodName
          if !existingMethods.contains(methodName)
        } yield {
          import org.scalajs.ir.Trees._
          import org.scalajs.ir.Types._

          val methodDef = m
          implicit val pos = methodDef.pos

          val methodName = methodDef.name
          val newBody = ApplyStatically(ApplyFlags.empty,
              This()(ClassType(className)), ObjectClass, methodName,
              methodDef.args.map(_.ref))(
              methodDef.resultType)
          val newMethodDef = MethodDef(MemberFlags.empty, methodName,
              methodDef.originalName, methodDef.args, methodDef.resultType,
              Some(newBody))(
              OptimizerHints.empty, None)
          newMethodDef
        }

        linkedMethods ++ bridges
      } else {
        linkedMethods
      }

      // Normal methods
      val memberMethodsWithGlobals = for {
        m <- linkedMethodsAndBridges
        if m.flags.namespace == MemberNamespace.Public && m.body.isDefined
      } yield {
        val methodCache =
          classCache.getMemberMethodCache(m.methodName)

        classEmitter.genMemberMethod(className, m)(methodCache)
      }

      // Exported members
      val exportedMembers = classEmitter.genExportedMembers(classDef, useESClass)(classCache).value
      val setTypeData = if (kind.isClass && className != ObjectClass) classEmitter.genSetTypeData(classDef)(classCache) else js.Skip()
      val fullClass = for {
        ctor <- ctorWithGlobals
        memberMethods <- WithGlobals.list(memberMethodsWithGlobals)
        clazz <- classEmitter.buildClass(classDef, useESClass, ctor,
            memberMethods, exportedMembers, setTypeData)(classCache)
      } yield {
        clazz
      }

      main += fullClass.value
    }

    if (className != ObjectClass) {
      /* Instance tests and type data are hardcoded in the CoreJSLib for
       * j.l.Object. This is important because their definitions depend on the
       * `$TypeData` definition, which only comes in the `postObjectDefinitions`
       * of the CoreJSLib. If we wanted to define them here as part of the
       * normal logic of `ClassEmitter`, we would have to further divide `main`
       * into two parts. Since the code paths are in fact completely different
       * for `j.l.Object` anyway, we do not do this, and instead hard-code them
       * in the CoreJSLib. This explains why we exclude `j.l.Object` as this
       * level, rather than inside `ClassEmitter.needInstanceTests` and
       * similar: it is a concern that goes beyond the organization of the
       * class `j.l.Object`.
       */

      main += classEmitter.genTypeData(classDef)(uncachedKnowledge, knowledgeGuardian).value

      if (classEmitter.needInstanceTests(classDef)(classCache)) 
        main += classEmitter.genInstanceTests(classDef)(classCache).value
    }

    if (classDef.kind.hasModuleAccessor) {
      main += classEmitter.genModuleAccessor(classDef)(classCache).value
    }

    // Static fields
    val staticFields = if (classDef.kind.isJSType) {
      Nil
    } else {
      classEmitter.genCreateStaticFieldsOfScalaClass(classDef)(classCache).value
    }

    // Static initialization

    val staticInitialization =
      classEmitter.genStaticInitialization(classDef)(uncachedKnowledge)

    new GeneratedClass(
        className,
        main.result(),
        staticFields,
        staticInitialization,
        trackedGlobalRefs = null
    )
  }

  // Helpers

  private def mergeVersions(v1: Option[String],
      v2: Option[String]): Option[String] = {
    v1.flatMap(s1 => v2.map(s2 => "" + s1.length + "-" + s1 + s2))
  }

  // Caching

  private final class ClassCache extends knowledgeGuardian.KnowledgeAccessor {
    private[this] var _cache: DesugaredClassCache = null
    private[this] var _lastVersion: Option[String] = None
    private[this] var _cacheUsed = false

    private[this] val _methodCaches =
      Array.fill(MemberNamespace.Count)(mutable.Map.empty[MethodName, MethodCache[js.Tree]])

    private[this] val _memberMethodCache =
      mutable.Map.empty[MethodName, MethodCache[js.MethodDef]]

    private[this] var _constructorCache: Option[MethodCache[js.Tree]] = None

    override def invalidate(): Unit = {
      /* Do not invalidate contained methods, as they have their own
       * invalidation logic.
       */
      super.invalidate()
      _cache = null
      _lastVersion = None
    }

    def startRun(): Unit = {
      _cacheUsed = false
      _methodCaches.foreach(_.valuesIterator.foreach(_.startRun()))
      _memberMethodCache.valuesIterator.foreach(_.startRun())
      _constructorCache.foreach(_.startRun())
    }

    def getCache(version: Option[String]): DesugaredClassCache = {
      if (_cache == null || _lastVersion.isEmpty || _lastVersion != version) {
        invalidate()
        statsClassesInvalidated += 1
        _lastVersion = version
        _cache = new DesugaredClassCache
      } else {
        statsClassesReused += 1
      }
      _cacheUsed = true
      _cache
    }

    def getMemberMethodCache(
        methodName: MethodName): MethodCache[js.MethodDef] = {
      _memberMethodCache.getOrElseUpdate(methodName, new MethodCache)
    }

    def getStaticLikeMethodCache(namespace: MemberNamespace,
        methodName: MethodName): MethodCache[js.Tree] = {
      _methodCaches(namespace.ordinal)
        .getOrElseUpdate(methodName, new MethodCache)
    }

    def getConstructorCache(): MethodCache[js.Tree] = {
      _constructorCache.getOrElse {
        val cache = new MethodCache[js.Tree]
        _constructorCache = Some(cache)
        cache
      }
    }

    def cleanAfterRun(): Boolean = {
      _methodCaches.foreach(_.filterInPlace((_, c) => c.cleanAfterRun()))
      _memberMethodCache.filterInPlace((_, c) => c.cleanAfterRun())

      if (_constructorCache.exists(!_.cleanAfterRun()))
        _constructorCache = None

      if (!_cacheUsed)
        invalidate()

      _methodCaches.exists(_.nonEmpty) || _cacheUsed
    }
  }

  private final class MethodCache[T <: js.Tree] extends knowledgeGuardian.KnowledgeAccessor {
    private[this] var _tree: WithGlobals[T] = null
    private[this] var _lastVersion: Option[String] = None
    private[this] var _cacheUsed = false

    override def invalidate(): Unit = {
      super.invalidate()
      _tree = null
      _lastVersion = None
    }

    def startRun(): Unit = _cacheUsed = false

    def getOrElseUpdate(version: Option[String],
        v: => WithGlobals[T]): WithGlobals[T] = {
      if (_tree == null || _lastVersion.isEmpty || _lastVersion != version) {
        invalidate()
        statsMethodsInvalidated += 1
        _tree = v
        _lastVersion = version
      } else {
        statsMethodsReused += 1
      }
      _cacheUsed = true
      _tree
    }

    def cleanAfterRun(): Boolean = {
      if (!_cacheUsed)
        invalidate()

      _cacheUsed
    }
  }

  private class CoreJSLibCache extends knowledgeGuardian.KnowledgeAccessor {
    private[this] var _lastModuleContext: ModuleContext = _
    private[this] var _lib: WithGlobals[CoreJSLib.Lib] = _

    def build(): WithGlobals[CoreJSLib.Lib] = {
      if (_lib == null) {
        _lib = CoreJSLib.build(sjsGen, this)
      }
      _lib
    }

    override def invalidate(): Unit = {
      super.invalidate()
      _lib = null
    }
  }
}

object Emitter {
  /** Result of an emitter run. */
  final class Result private[Emitter](
      val header: String,
      val body: Map[ModuleID, js.Tree],
      val footer: String,
      val topLevelVarDecls: List[String],
      val globalRefs: Set[String]
  )

  /** Configuration for the Emitter. */
  final class Config (
      val semantics: Semantics,
      val moduleKind: ModuleKind,
      val esFeatures: ESFeatures,
      val jsHeader: String,
      val internalModulePattern: ModuleID => String,
      val optimizeBracketSelects: Boolean,
      val trackAllGlobalRefs: Boolean
  ) {
    def this(
        semantics: Semantics,
        moduleKind: ModuleKind,
        esFeatures: ESFeatures) = {
      this(
          semantics,
          moduleKind,
          esFeatures,
          jsHeader = "",
          internalModulePattern = "./" + _.id,
          optimizeBracketSelects = true,
          trackAllGlobalRefs = false)
    }

    def withSemantics(f: Semantics => Semantics): Config =
      copy(semantics = f(semantics))

    def withModuleKind(moduleKind: ModuleKind): Config =
      copy(moduleKind = moduleKind)

    def withESFeatures(f: ESFeatures => ESFeatures): Config =
      copy(esFeatures = f(esFeatures))

    def withJSHeader(jsHeader: String): Config = {
      require(StandardConfig.isValidJSHeader(jsHeader), jsHeader)
      copy(jsHeader = jsHeader)
    }

    def withInternalModulePattern(internalModulePattern: ModuleID => String): Config =
      copy(internalModulePattern = internalModulePattern)

    def withOptimizeBracketSelects(optimizeBracketSelects: Boolean): Config =
      copy(optimizeBracketSelects = optimizeBracketSelects)

    def withTrackAllGlobalRefs(trackAllGlobalRefs: Boolean): Config =
      copy(trackAllGlobalRefs = trackAllGlobalRefs)

    private def copy(
        semantics: Semantics = semantics,
        moduleKind: ModuleKind = moduleKind,
        esFeatures: ESFeatures = esFeatures,
        jsHeader: String = jsHeader,
        internalModulePattern: ModuleID => String = internalModulePattern,
        optimizeBracketSelects: Boolean = optimizeBracketSelects,
        trackAllGlobalRefs: Boolean = trackAllGlobalRefs): Config = {
      new Config(semantics, moduleKind, esFeatures, jsHeader,
          internalModulePattern, optimizeBracketSelects, trackAllGlobalRefs)
    }
  }

  object Config {
    def apply(coreSpec: CoreSpec): Config =
      new Config(coreSpec.semantics, coreSpec.moduleKind, coreSpec.esFeatures)
  }

  private final class DesugaredClassCache {
    val privateJSFields = new OneTimeCache[WithGlobals[List[js.Tree]]]
    val exportedMembers = new OneTimeCache[WithGlobals[js.Tree]]
    val instanceTests = new OneTimeCache[WithGlobals[js.Tree]]
    val typeData = new OneTimeCache[WithGlobals[js.Tree]]
    val setTypeData = new OneTimeCache[js.Tree]
    val moduleAccessor = new OneTimeCache[WithGlobals[js.Tree]]
    val staticFields = new OneTimeCache[WithGlobals[List[js.Tree]]]
  }

  private final class GeneratedClass(
      val className: ClassName,
      val main: List[js.Tree],
      val staticFields: List[js.Tree],
      val staticInitialization: List[js.Tree],
      val trackedGlobalRefs: Set[String]
  )

  private final class OneTimeCache[A >: Null] {
    private[this] var value: A = null
    def getOrElseUpdate(v: => A): A = {
      if (value == null)
        value = v
      value
    }
  }

  private case class ClassID(
      ancestors: List[ClassName], moduleContext: ModuleContext)

  private def symbolRequirements(config: Config): SymbolRequirement = {
    import config.semantics._
    import CheckedBehavior._

    val factory = SymbolRequirement.factory("emitter")
    import factory._

    def cond(p: Boolean)(v: => SymbolRequirement): SymbolRequirement =
      if (p) v else none()

    multiple(
        cond(asInstanceOfs != Unchecked) {
          instantiateClass(ClassCastExceptionClass, StringArgConstructorName)
        },

        cond(arrayIndexOutOfBounds != Unchecked) {
          instantiateClass(ArrayIndexOutOfBoundsExceptionClass,
              StringArgConstructorName)
        },

        cond(stringIndexOutOfBounds != Unchecked) {
          instantiateClass(StringIndexOutOfBoundsExceptionClass,
              IntArgConstructorName)
        },

        cond(asInstanceOfs == Fatal || arrayIndexOutOfBounds == Fatal || stringIndexOutOfBounds == Fatal) {
          instantiateClass(UndefinedBehaviorErrorClass,
              ThrowableArgConsructorName)
        },

        cond(moduleInit == Fatal) {
          instantiateClass(UndefinedBehaviorErrorClass,
              StringArgConstructorName)
        },

        // See systemIdentityHashCode in CoreJSLib
        callMethod(BoxedDoubleClass, hashCodeMethodName),
        callMethod(BoxedStringClass, hashCodeMethodName),

        cond(!config.esFeatures.allowBigIntsForLongs) {
          multiple(
              instanceTests(LongImpl.RuntimeLongClass),
              instantiateClass(LongImpl.RuntimeLongClass, LongImpl.AllConstructors.toList),
              callMethods(LongImpl.RuntimeLongClass, LongImpl.AllMethods.toList),
              callOnModule(LongImpl.RuntimeLongModuleClass, LongImpl.AllModuleMethods.toList)
          )
        }
    )
  }


}
