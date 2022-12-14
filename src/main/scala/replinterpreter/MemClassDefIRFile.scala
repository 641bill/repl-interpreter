package replinterpreter

import scala.concurrent._

import org.scalajs.ir.EntryPointsInfo
import org.scalajs.ir.Trees.ClassDef

import org.scalajs.linker.interface.IRFile
import org.scalajs.linker.interface.unstable.IRFileImpl

private final class MemClassDefIRFile(classDef: ClassDef)
    extends IRFileImpl("mem://" + classDef.name.name + ".sjsir", None) {

  def tree(implicit ec: ExecutionContext): Future[ClassDef] =
    Future(classDef)

  def entryPointsInfo(implicit ec: ExecutionContext): Future[EntryPointsInfo] =
    tree.map(EntryPointsInfo.forClassDef)
}

object MemClassDefIRFile {
  def apply(classDef: ClassDef): IRFile =
    new MemClassDefIRFile(classDef)
}
