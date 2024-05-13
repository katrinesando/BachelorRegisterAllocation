Running x86 assembly programs (Assembly/nasm/README.TXT)
--------------------------------------------------------

A1. To assemble and run assembly program macsimple.asm on MacOS:

NOT SUPPORTED

A2. To assemble and run assembly program linsimple.asm on Linux or Windows with WSL:

   nasm -f elf64 linsimple.asm -o try.o

   Then link the object file with the C library for the 64-bit x86
   architecture, producing an executable file called "try":
   
   gcc -no-pie -m64 try.o -o try

   Then run the executable file:

   ./try

Should print the number 123456 and a newline.