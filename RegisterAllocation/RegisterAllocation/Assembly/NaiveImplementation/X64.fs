module X64
(* File NaiveImplementation/X64.fs

   Instructions and assembly code emission for a x86-x64 machine.
   sestoft@itu.dk * 2017-05-01
   ahad@itu.dk, biha@itu.dk, and kmsa@itu.dk * 2024-05-15

   We use some aspects of Niels Kokholm's SML version (March 2002).

   This compiler takes a less template-based approach closer to the
   x86 spirit:

   * Expressions are compiled to register-based code without use of
     the stack.

   * All local variables and parameters are stored in the stack.

   * All function arguments are passed on the stack.

   * There is no optimized register allocation across expressions and statements. 

   * We have access to all 64-bit registers of the x86-64 architecture, 
     but only use 2 registers at a time.  

   * We use the native x86-64 call and ret instructions, which means that
     we must pust some prologue code at each function start to obey
     the calling conventions of the abstract machine.  This is the
     most important reason for splitting labels into ordinary labels
     and function entry point labels.  *)

(* The MacOS and Windows linkers are not tested. The Linux/gcc linker does not expect an underscore (_) before
   external and global names. *)
open Allocate
let isLinux = true
let prefix = if isLinux then "" else "_"

let printi    = prefix + "printi"
let printc    = prefix + "printc"
let checkargc = prefix + "checkargc"
let asm_main  = prefix + "asm_main"

let operand rand : string =
    match rand with
        | Cst n    -> string n
        | Reg reg  -> fromReg reg
        | Ind reg  -> "[" + fromReg reg + "]"
        | RbpOff n -> "[rbp - " + string n + "]"
        | Glovars  -> "[glovars]"

(* Preserve all live registers around code, eg a function call *)
let rec preserveAll pres code =
    match pres with
    | []          -> code
    | reg :: rest -> preserveAll rest (pushAndPop reg code)

(* Generate new distinct labels *)
let (resetLabels, newLabel) = 
    let lastlab = ref -1
    ((fun () -> lastlab := 0), (fun () -> (lastlab := 1 + !lastlab; "L" + string(!lastlab))))

(* Convert one bytecode instr into x86 instructions in text form and pass to out *)
let x86instr2int out instr =
    let outlab lab = out (lab + ":\t\t\t\t;Label\n")
    let outins ins = out ("\t" + ins + "\n")
    match instr with
      | Label lab -> outlab lab
      | FLabel (lab, n)  -> out (lab + ":\t\t\t\t;start set up frame\n" +
                                 "\tpop rax\t\t\t; retaddr\n" +
                                 "\tpop rbx\t\t\t; oldbp\n" +
                                 "\tsub rsp, 16\n" +
                                 "\tmov rsi, rsp\n" +
                                 "\tmov rbp, rsp\n" +
                                 "\tadd rbp, " + string(8*n) + "\t\t; 8*arity\n" + 
                                 lab + "_pro_1:\t\t\t; slide arguments\n" +
                                 "\tcmp rbp, rsi\n" +
                                 "\tjz " + lab + "_pro_2\n" +
                                 "\tmov rcx, [rsi+16]\n" +
                                 "\tmov [rsi], rcx\n" +
                                 "\tadd rsi, 8\n" +
                                 "\tjmp " + lab + "_pro_1\n" +
                                 lab + "_pro_2:\n" +
                                 "\tsub rbp, 8\n" +
                                 "\tmov [rbp+16], rax\n" + 
                                 "\tmov [rbp+8], rbx\n" +             
                                   lab + "_tc:\t;end set up frame\n")
      | Ins ins               -> outins ins
      | Ins1 (ins, op1)       -> outins (ins + " " + operand op1)
      | Ins2 (ins, op1, op2)  -> outins (ins + " " + operand op1 + ", " + operand op2)
      | Jump (ins, lab)       -> outins (ins + " near " + lab)
      | PRINTI         -> List.iter outins [ "call_prolog"; "call " + printi; "call_epilog"]
      | PRINTC         -> List.iter outins [ "call_prolog"; "call " + printc; "call_epilog"]

(* Convert instruction list to list of assembly code fragments *)
let code2x86asm (code : x86 list) : string list =
    let bytecode = ref []
    let outinstr i   = (bytecode := i :: !bytecode)
    List.iter (x86instr2int outinstr) code;
    List.rev (!bytecode)

let stdheader = ";; Prolog and epilog for 1-argument C function call \n" +
                "%macro call_prolog 0\n" +
                "       mov rbx,rsp            ; Save pre-alignment stack pointer\n" +
                "       pop rax                 ; Pop the argument\n" +
                "       and rsp, 0xFFFFFFFFFFFFFFF0   ; Align rsp to 16 byte multiple\n" + 
                "       sub rsp, 16             ; Pad 16 bytes\n" + 
                "       push rbx                ; Push old stack top\n" +
                "       push rax                ; Push argument again\n" +
                "%endmacro\n" +
                "\n" +
                "%macro call_epilog 0\n" +
                "       add rsp, 8              ; Pop argument\n" + 
                "       pop rbx                 ; Get saved pre-alignment stack pointer\n" +
                "       mov rsp, rbx            ; Restore stack top to pre-alignment state\n" +
                "%endmacro\n" +
                "\n" +
                "EXTERN " + printi + "\n" + 
                "EXTERN " + printc + "\n" +
                "EXTERN " + checkargc + "\n" +
                "GLOBAL " + asm_main + "\n" +
                "section .data\n" +
                "\tglovars dq 0\n" +
                "section .text\n"
let beforeinit argc =
    asm_main + ":\n" +
    "\tpush rbp ;old bp\n" +
    "\tmov rbp, rsp ;new bp\n" +
    "\tmov qword [glovars], rsp\n" +
    "\t;check arg count:\n" +
    "\tpush qword [rbp+16]\n" + 
    "\tpush rsi\n" + //aligns stackpointer to 16-byte boundary
    "\tmov rsi, rdi\n" +
    "\tmov rdi, " + string(argc)+"\n" +
    "\tcall " + checkargc + "\n" +
    "\tpop rsi\n"+
    "\tadd rsp, 16\n" + 
    "\t; allocate globals:\n"
let pushargs = "\t;set up command line arguments on stack:\n" +
                "_args_next:\n" +
                "\tcmp rdi, 0\n" + 
                "\tjz _args_end\n" +
                "\tpush qword [rsi]\n" + 
                "\tadd rsi, 8\n" + 
                "\tsub rdi, 1\n" + 
                "\tjmp _args_next           ;repeat until --rdi == 0\n" +
                "_args_end:\n"
               
let popargs =   "\t;clean up stuff pushed onto stack:\n" + 
                "\tmov rsp, qword [glovars]\n" +
                "\tadd rsp, 8\n" + 
                "\tmov rsp, rbp\n" +
                "\tpop rbp\n" +
                "\tret\n"

