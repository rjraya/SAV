name := "labs03"

scalaVersion := "2.11.8"

lazy val welder = RootProject(uri("git://github.com/epfl-lara/welder.git#79f9fffb49770f6078e8a1c0676efe38b51e7161"))

lazy val root = (project in file(".")).dependsOn(welder)
