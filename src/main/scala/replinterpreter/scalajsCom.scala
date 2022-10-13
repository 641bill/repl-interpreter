package replinterpreter
import scala.scalajs.js
import scala.scalajs.js.annotation._

@js.native
@JSGlobal
object scalajsCom extends js.Any {

	def init(onReceive: js.Function1[String, Unit]): Unit = js.native

	def send(msg: String): Unit = js.native
  
}


