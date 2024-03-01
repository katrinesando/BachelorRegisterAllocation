module Allocate

open System

type reg64 =
    | Rax | Rcx | Rdx | Rbx | Rsi | Rdi | Rsp | Rbp | R8 | R9 | R10 | R11 | R12 | R13 | R14| R15 

type label = string

type flabel = string

//General purpose registers for 64-bit

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

(* The 13 registers that can be used for temporary values in i386.
Allowing RDX requires special handling across IMUL and IDIV *)
let temporaries =
    [Rcx; Rdx; Rbx; Rsi; Rdi; R8; R9; R10; R11; R12; R13; R14; R15]

let mem x xs = List.exists (fun y -> x=y) xs


(* Get temporary register not in pres; throw exception if none available *)
let getTemp pres : reg64 option =
    let rec aux available =
        match available with
            | []          -> None
            | reg :: rest -> if mem reg pres then aux rest else Some reg
    aux temporaries

let getTempFor (pres : reg64 list) : reg64 =
    match getTemp pres with
    | None     -> failwith "no more registers, expression too complex"
    | Some reg -> reg
let free (reg:reg64) (pres:reg64 list) = List.filter (fun x -> x <> reg) pres

//Might run into problems with push and pop with 64-bit nasm (might be a bug that's fixed though)
let pushAndPop reg code = [Ins1("push", Reg reg)] @ code @ [Ins1("pop", Reg reg)]

(* Preserve reg across code, on the stack if necessary *)
(* Maybe move to Allocate.fs if spilling needs it*)
let preserve reg pres code =
    if mem reg pres then
       pushAndPop reg code
    else
        code


(* Make a backwards pass over the x86 instr*)
let allocationPass code =
    let rec aux rest acc = 
        match rest with
        |[] -> acc
        |x::xs ->
            match (x, xs) with
            | Ins2("mov", rand, rand1), (Ins2("add", rand2, rand3)::xs1) ->
               Ins1("push", rand3) :: acc
            | _,_ -> aux xs acc
    aux (List.rev code) []
