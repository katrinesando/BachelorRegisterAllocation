Compiling and loading the micro-C evaluator and parser (Assembly/README.TXT)
----------------------------------------------------------------------------
Archive assembly.zip contains the files used below.
NOT TESTED ON MAC
A. To assemble, link and run x86-64 assembly programs, see nasm/README.TXT


B. To compile the nasm-generating micro-C compiler and use it.

   First compile and load the micro-C lexer and parser specifications,
   the bytecode assembler, and the assembly-generating micro-C
   compiler:
   
   Windows:
   fslex --unicode CLex.fsl
   fsyacc --module CPar CPar.fsy
   
   Linux:
   (Need to have downloaded mono for running windows .exe)
   mono <path/to/fsyacc.exe> --module CPar CPar.fsy
   mono <path/to/fslex.exe> --unicode CLex.fsl
   dotnet fsi -r "../LexAndParse/FsLexYacc.Runtime.dll" Absyn.fs Absyn.fs CPar.fs CLex.fs Allocate.fs Parse.fs X64.fs X64Comp.fs ParseAndComp.fs
   
   (For linux use / instead of \ for file paths)
   open ParseAndComp;;
   compileToFile (fromFile "..\mcexamples\print_num.c") "print_num.asm";;
   compileToFile (fromFile "..\mcexamples\ex6.c") "ex6.asm";;
   compileToFile (fromFile "..\mcexamples\ex11.c") "ex11.asm";;
   
   Then the generated assembly code in the .asm files must be
   assembled and linked with the C driver code in driver.c.  Precisely
   how depends on the platform; see below.

C. Build a micro-C compiler (generating assembly code) as a command-line program microccasm

   Windows:
   fslex --unicode CLex.fsl
   fsyacc --module CPar CPar.fsy
   
   Linux:
   (Need to have downloaded mono for running windows .exe)
   mono <path/to/fsyacc.exe> --module CPar CPar.fsy
   mono <path/to/fslex.exe> --unicode CLex.fsl
   
   fsc --standalone -r "../LexAndParse/FSharp.Core.dll" -r "../LexAndParse/FsLexYacc.Runtime.dll" Absyn.fs CPar.fs CLex.fs Allocate.fs Parse.fs X64.fs X64Comp.fs ParseAndComp.fs MicroCCAsm.fs -o microccasm.exe   
   
   ./microccasm ..\mcexamples\ex11.c

----------------------------------------------------------------------

ASSEMBLING, LINKING AND RUNNING COMPILED MICRO-C PROGRAMS
Currently, linking and running the compiled Micro-C programs only works on either Linux or WSL.

MacOS: NOT SUPPORTED
Windows: NOT SUPPORTED (only supported on Windows with WSL)

------

Linux/WSL:
   gcc -m64 -c driver.c		
   nasm -f elf64 print_num.asm
   gcc -no-pie -m64 driver.o print_num.o -o print_num
   ./print_num 

   No underscores (_) in external function names.

   Stack alignment constraints are not needed, but harmless.

------