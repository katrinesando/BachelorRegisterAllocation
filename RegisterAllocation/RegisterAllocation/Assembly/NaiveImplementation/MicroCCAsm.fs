(* File Assembly/MicroCCAsm.fs *)

module MicroCCAsm

let args = System.Environment.GetCommandLineArgs();;

let _ = printf "Micro-C register-based x86-64 compiler v 1.0.0.0 of 2024-05-15\n";;

let _ = 
   if args.Length > 1 then
      let source = args.[1]
      let stem = if source.EndsWith(".c")
                 then source.Substring(0,source.Length-2) 
                 else source
      let target = stem + ".asm"
      printf "Compiling %s to %s\n" source target;
      try ignore (X64Comp.compileToFile (Parse.fromFile source) target)
      with Failure msg -> printf "ERROR: %s\n" msg
   else
      printf "Usage: microccasm <source file>\n";;
