module X64
(* File Assembly/X86.fs

   Instructions and assembly code emission for a x86 machine.
   sestoft@itu.dk * 2017-05-01

   We use some aspects of Niels Kokholm's SML version (March 2002).

   This compiler takes a less template-based approach closer to the
   x86 spirit:

   * We use 32 bit (aka double word) protected mode code.

   * Expressions are compiled to register-based code without use of
     the stack.

   * All local variables and parameters are stored in the stack.

   * All function arguments are passed on the stack.

   * There is no optimized register allocation across expressions and statements. 

   * We use all 32-bit registers of the x86-64 architecture.  

   * We use the native x86 call and ret instructions, which means that
     we must pust some prologue code at each function start to obey
     the calling conventions of the abstract machine.  This is the
     most important reason for splitting labels into ordinary labels
     and function entry point labels.  *)

(* The MacOS and Windows linkers expect an underscore (_) before
   external and global names, whereas the Linux/gcc linker does not. *)

let isLinux = true
let prefix = if isLinux then "" else "_"

let printi    = prefix + "printi"
let printc    = prefix + "printc"
let checkargc = prefix + "checkargc"
let asm_main  = prefix + "asm_main"

type label = string

type flabel = string

//Todo: Change 32-bit to 64-bit -> include all registers
type reg32 =
    | Eax | Ecx | Edx | Ebx | Esi | Edi | Esp | Ebp

//General purpose registers for 64-bit
type reg64 =
    | Rax | Rcx | Rdx | Rbx | Rsi | Rdi | Rsp | Rbp | R8 | R9 | R10 | R11 | R12 | R13 | R14| R15 

(* Operands of x86 instructions *)
type rand =
    | Cst of int                        (* immediate dword n               *)
    | Reg of reg64                      (* register rbx                    *)
    | Ind of reg64                      (* register indirect [rbx]         *)
    | RbpOff of int                     (* rbp offset indirect [rbp - n]   *)
    | Glovars                           (* stackbase [glovars]             *)

(* Instructions represented by the x86 type *)
type x86 =
    | Label of label                    (* symbolic label; pseudo-instruc. *)
    | FLabel of flabel * int            (* function label, arity; pseudo.  *)
    | Ins of string                     (* eg. sub rsp, 4                  *)
    | Ins1 of string * rand             (* eg. push rax                    *)
    | Ins2 of string * rand * rand      (* eg. add rax, [rbp - 32]         *)
    | Jump of string * label            (* eg. jz near lab                 *)
    | PRINTI                            (* print [rsp] as integer          *)
    | PRINTC                            (* print [rsp] as character        *)

//Todo: Change to include all 64-bit registers
let fromReg reg =
    match reg with
    | Rax  -> "rax"
    | Rcx  -> "rcx"
    | Rdx  -> "rdx"
    | Rbx  -> "rbx"
    | Rsi  -> "rsi"
    | Rdi  -> "rdi"
    | Rsp  -> "rsp"
    | Rbp  -> "rbp"
    | R8   -> "r8"
    | R9   -> "r9"
    | R10  -> "r10"
    | R11  -> "r11"
    | R12  -> "r12"
    | R13  -> "r13"
    | R14  -> "r14"
    | R15  -> "r15"

let operand rand : string =
    match rand with
        | Cst n    -> string n
        | Reg reg  -> fromReg reg
        | Ind reg  -> "[" + fromReg reg + "]"
        | RbpOff n -> "[rbp - " + string n + "]"
        | Glovars  -> "[glovars]"

(* The 13 registers that can be used for temporary values in i386.
Allowing RDX requires special handling across IMUL and IDIV *)
let temporaries =
    [Rcx; Rdx; Rbx; Rsi; Rdi; R8; R9; R10; R11; R12; R13; R14; R15]

let mem x xs = List.exists (fun y -> x=y) xs

//Todo: Spilling might be happening here
let getTemp pres : reg64 option =
    let rec aux available =
        match available with
            | []          -> None
            | reg :: rest -> if mem reg pres then aux rest else Some reg
    aux temporaries

(* Get temporary register not in pres; throw exception if none available *)

let getTempFor (pres : reg64 list) : reg64 =
    match getTemp pres with
    | None     -> failwith "no more registers, expression too complex"
    | Some reg -> reg

//Might run into problems with push and pop with 64-bit nasm (might be a bug that's fixed though)
let pushAndPop reg code = [Ins1("push", Reg reg)] @ code @ [Ins1("pop", Reg reg)]

(* Preserve reg across code, on the stack if necessary *)

let preserve reg pres code =
    if mem reg pres then
       pushAndPop reg code
    else
        code

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
                                 "\tadd rbp, " + string(8*n) + "\t\t; 8*arity\n" + //4 originalt
                                 lab + "_pro_1:\t\t\t; slide arguments\n" +
                                 "\tcmp rbp, rsi\n" +
                                 "\tjz " + lab + "_pro_2\n" +
                                 "\tmov rcx, [rsi+16]\n" + //8 originalt
                                 "\tmov [rsi], rcx\n" +
                                 "\tadd rsi, 8\n" + //4 originalt
                                 "\tjmp " + lab + "_pro_1\n" +
                                 lab + "_pro_2:\n" +
                                 "\tsub rbp, 8\n" + //4 originalt
                                 "\tmov [rbp+16], rax\n" + //8 originalt
                                 "\tmov [rbp+8], rbx\n" + //4 originalt               
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

let stdheader = ";; Prolog and epilog for 1-argument C function call (needed on MacOS)\n" +
                "%macro call_prolog 0\n" +
                "       mov rbx,rsp            ; Save pre-alignment stack pointer\n" +
                "       pop rax                 ; Pop the argument\n" +
                "       and rsp, 0xFFFFFFFFFFFFFFF0   ; Align rsp to 16 byte multiple\n" + //0xFFFFFFF0 originalt
                "       sub rsp, 16             ; Pad 16 bytes\n" + //8 originalt - hvorfor paddes der helt præcist? den gør plads lige nu til nyt variables, men kan det også bare være 8?
                "       push rbx                ; Push old stack top\n" +
                "       push rax                ; Push argument again\n" +
                "%endmacro\n" +
                "\n" +
                "%macro call_epilog 0\n" +
                "       add rsp, 8              ; Pop argument\n" + //4 originalt
                "       pop rbx                 ; Get saved pre-alignment stack pointer\n" +
                "       mov rsp, rbx            ; Restore stack top to pre-alignment state\n" +
                "%endmacro\n" +
                "\n" +
                "EXTERN " + printi + "\n" + //was EXTERN not GLOBAL
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
    "\tpush qword [rbp+16]\n" + //8 originalt
    "\tpush rsi\n" + //aligns stackpointer to 16-byte boundary
    "\tmov rsi, rdi\n" +
    "\tmov rdi, " + string(argc)+"\n" +
    "\tcall " + checkargc + "\n" +
    "\tpop rsi\n"+
    "\tadd rsp, 16\n" + //8 originalt
    "\t; allocate globals:\n"// skal formentlig poppe ind i rsi/rdi for at få cmd-args tilbage


let pushargs = "\t;set up command line arguments on stack:\n" +
                "_args_next:\n" +
                "\tcmp rdi, 0\n" + 
                "\tjz _args_end\n" +
                "\tpush qword [rsi]\n" + //push decrements rsp based on size of operand esi is 4-byte rsi is 8-byte
                "\tadd rsi, 8\n" + //4 originalt - this means the array can only hold ints
                "\tsub rdi, 1\n" + //was rcx
                "\tjmp _args_next           ;repeat until --rcx == 0\n" +
                "_args_end:\n"
               
let popargs =   "\t;clean up stuff pushed onto stack:\n" + //furthest we've gotten in execution
                "\tmov rsp, qword [glovars]\n" +
                "\tadd rsp, 8\n" + //4 originalt
                "\tmov rsp, rbp\n" +
                "\tpop rbp\n" +
                "\tret\n"

