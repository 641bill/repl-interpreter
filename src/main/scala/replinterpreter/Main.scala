package replinterpreter

import org.scalajs.linker.NodeIRFile
import org.scalajs.linker.NodeIRContainer
import org.scalajs.linker.interface.IRFileCache
import org.scalajs.linker.interface.unstable.IRContainerImpl
import org.scalajs.linker.interface.ModuleInitializer
import org.scalajs.linker.interface.IRFile
import org.scalajs.linker.interface.Semantics
import org.scalajs.sjsirinterpreter.core.Interpreter
import scala.concurrent._
import scala.scalajs.js
import org.scalajs.ir.Names._
import org.scalajs.ir.Trees._
import org.scalajs.ir.Types._
import replemitter._
import org.scalajs.linker.interface.ModuleKind
import org.scalajs.linker.interface.ESFeatures

object Main {
	// Create a counter for the number of classes we created
	val counter = new java.util.concurrent.atomic.AtomicInteger(0)
  def main(args: Array[String]): Unit = {

		val interpreter = new Emitter(
			new Emitter.Config(Semantics.Defaults, ModuleKind.NoModule, ESFeatures.Defaults)
			  .withESFeatures(_.withAvoidClasses(false)))

    js.Dynamic.global.Error.stackTraceLimit = 100

		scalajsCom.init((msg: String) => {

			import IRBuilder.noPosition

			// in the callback, call the interpreter
			import ExecutionContext.Implicits.global

			// case 1: msg starts with "classpath:"
			if (msg.startsWith("classpath:")) {
				val path = msg.substring("classpath:".length)
				val jars = NodeIRContainer.fromClasspath(path.split(':').toList)

				val files = jars.flatMap { case (irContainers, _) =>
					val libIRFiles = Future.sequence(irContainers.map(c =>
						IRContainerImpl.fromIRContainer(c).sjsirFiles))
					libIRFiles.map(_.flatten)
				}
				files.flatMap(irFiles => {// foreach because of Future
					val result = interpreter.loadIRFiles(irFiles)
					result.map(_ => {
						scalajsCom.send("classpath files loaded") // An ack to the jvm side
					})
				}).recover {
					case e: Exception => e.printStackTrace()
				}
			}

			// case 2: msg starts with "irfiles:"
			else if (msg.startsWith("irfiles:")) {
				val paths = msg.substring("irfiles:".length)
				val irFiles: Future[List[IRFile]] = Future.sequence(
					paths.split(",").map(NodeIRFile(_)).toList)

				irFiles.flatMap(irFiles => {
					val result = interpreter.loadIRFiles(irFiles)
					result.map(_ => {
						scalajsCom.send("Several sjsir files loaded") // An ack to the jvm side
					})
				}).recover {
					case e: Exception => println(e)
				}
			}

			// case 3: objectName
			// synthesize a class with a main method that loads the module
			else if (msg.startsWith("objectName:")) {
				val objectName = msg.substring("objectName:".length)

				var className = ClassName(objectName)

				// Create the mainClassDef
				val classDef = IRBuilder.mainClassDef(LoadModule(className), counter.get())
				val irFile = MemClassDefIRFile(classDef)
				val result = interpreter.loadIRFiles(List(irFile))

				result.flatMap(_ => {
					interpreter.runModuleInitializers(ModuleInitializer.mainMethodWithArgs(
						IRBuilder.MainClassName.nameString + counter.getAndIncrement(),
					IRBuilder.MainMethodName.simpleName.nameString) :: Nil)
				}).map(_ => {
					scalajsCom.send(s"Loaded $objectName") // An ack to the jvm side
				}).recover {
					case e: Exception => e.printStackTrace()
				}
			}

			// case 4: objectName and methodName
			else if (msg.startsWith("objectNameAndMethodName:")) {
				val objectNameAndMethodName = msg.substring("objectNameAndMethodName:".length).split(":")
				val objectNameReceivedFromJVM = if (objectNameAndMethodName(0).last != '$')
					objectNameAndMethodName(0) + "$" 
					else objectNameAndMethodName(0)
				val methodNameReceivedFromJVM = objectNameAndMethodName(1)
				val irTypeStr = objectNameAndMethodName(2)
				val irType = irTypeStr.charAt(0) match {
					case 'V' => VoidRef
					case 'Z' => BooleanRef
					case 'C' => CharRef
					case 'B' => ByteRef
					case 'S' => ShortRef
					case 'I' => IntRef
					case 'J' => LongRef
					case 'F' => FloatRef
					case 'D' => DoubleRef
					case 'L' => ClassRef(ClassName(irTypeStr.substring(1)))
				}

				var className = ClassName(objectNameReceivedFromJVM)
				val simpleMethodName = SimpleMethodName(methodNameReceivedFromJVM)
				val methodName = MethodName(simpleMethodName, Nil, irType)
				val apply = Apply(ApplyFlags.empty, LoadModule(className), MethodIdent(methodName), Nil)(NoType)
				val resultString = BinaryOp(BinaryOp.String_+, StringLiteral(""), apply)
				val scalajsComSend = JSMethodApply(JSGlobalRef("scalajsCom"), StringLiteral("send"), List(resultString))
				val classDef = IRBuilder.mainClassDef(scalajsComSend, counter.get())
				val irFile = MemClassDefIRFile(classDef)
				val result = interpreter.loadIRFiles(List(irFile))

				result.flatMap(_ => {
					interpreter.runModuleInitializers(ModuleInitializer.mainMethodWithArgs(
						IRBuilder.MainClassName.nameString + counter.getAndIncrement(),
					IRBuilder.MainMethodName.simpleName.nameString) :: Nil)
				}).map(_ => {
				}).recover {
					case e: Exception => e.printStackTrace()
				}
			}
		})
	}
}
