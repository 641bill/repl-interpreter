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

object Main {
	// Create a counter for the number of classes we created
	var counter = new java.util.concurrent.atomic.AtomicInteger(0)

  def main(args: Array[String]): Unit = {
		
		val interpreter = new Interpreter(Semantics.Defaults)

		scalajsCom.init((msg: String) => {

			import IRBuilder.noPosition

			println("Received: " + msg)
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
				files.foreach(irFiles => {// foreach because of Future
					val result = interpreter.loadIRFiles(irFiles)
					result.foreach(_ => {
						println("Loaded") 
						scalajsCom.send("classpath files loaded") // An ack to the jvm side
					})
				})
			}

			// case 2: msg starts with "irfiles:"
			else if (msg.startsWith("irfiles:")) {
				val paths = msg.substring("irfiles:".length)
				val irFiles: Future[List[IRFile]] = Future.sequence(
					paths.split(",").map(NodeIRFile(_)).toList)

				irFiles.map(irFiles => {
					val result = interpreter.loadIRFiles(irFiles)
					result.foreach(_ => {
						println("Loaded") 
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
				println("objectName: " + objectName)

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
					scalajsCom.send("Object loaded") // An ack to the jvm side
					println(s"Loaded $objectName")
				}).recover {
					case e: Exception => e.printStackTrace()
				}
			}

			// case 4: objectName and methodName
			else if (msg.startsWith("objectNameAndMethodName:")) {
				val objectNameAndMethodName = msg.substring("objectNameAndMethodName:".length)
				val objectNameReceivedFromJVM = if (objectNameAndMethodName.split(":")(0).last != '$') 
					objectNameAndMethodName.split(":")(0) + "$" else objectNameAndMethodName.split(":")(0)
				val methodNameReceivedFromJVM = objectNameAndMethodName.split(":")(1)
				println("objectName: " + objectNameReceivedFromJVM)
				println("methodName: " + methodNameReceivedFromJVM)

				var className = ClassName(objectNameReceivedFromJVM)
				val simpleMethodName = SimpleMethodName(methodNameReceivedFromJVM)
				val methodName = MethodName.reflectiveProxy(simpleMethodName, Nil)
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
					println(s"Ran $objectNameReceivedFromJVM.$methodNameReceivedFromJVM")
				}).recover {
					case e: Exception => e.printStackTrace()
				}
			
			}

			
			// case 5: msg is "exit"
			else if (msg == "exit") {
				println("Exiting REPL Interpreter...")
				scalajsCom.send("exit")
			}

			// case 6: msg is something else
			else {
				println("Unknown command: " + msg)
			}
		})
	}
}
