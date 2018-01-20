name := "TableauxMachine"

version := "0.1"

scalaVersion := "2.11.8"

libraryDependencies += "org.scala-graph" %% "graph-core" % "1.12.1"

// The names of organization/artifact/version do not matter since we specify an absolute URI anyway.
libraryDependencies += "UniFormal" % "MMT" % "7641de1" from "https://github.com/UniFormal/MMT/releases/download/20-Dec-2017/mmt.jar"

// libraryDependencies += "org.scalactic" %% "scalactic" % "3.0.4"

libraryDependencies += "org.scalatest" %% "scalatest" % "3.0.4" % "test"
