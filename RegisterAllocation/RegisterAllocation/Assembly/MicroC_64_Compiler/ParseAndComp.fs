(* File MicroC_64_Compiler/ParseAndComp.fs *)

module ParseAndComp

let fromString = Parse.fromString

let fromFile = Parse.fromFile

let compileToFile = X64Comp.compileToFile
