enablePlugins(ScalaJSPlugin)
scalaJSLinkerConfig ~= { _.withModuleKind(ModuleKind.ESModule) }
scalaJSLinkerConfig ~= { _.withModuleKind(ModuleKind.CommonJSModule) }
scalaVersion := "2.13.8"
libraryDependencies += "be.doeraene" %%% "sjsir-interpreter" % "0.2.0"
libraryDependencies += "org.scala-js" %%% "scalajs-linker-interface" % "1.12.0"
libraryDependencies += "org.scala-js" %%% "scalajs-linker" % "1.12.0"
scalaJSUseMainModuleInitializer := true
scalacOptions += "-deprecation"