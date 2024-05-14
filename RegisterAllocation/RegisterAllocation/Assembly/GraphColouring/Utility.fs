module Utility
(* File GraphColouring/Utility.fs
   A type and a function used in multiple otherwise unrelated files
   ahad@itu.dk, biha@itu.dk, and kmsa@itu.dk 2024-05-15
   Must precede X64Comp.fs, Comp.fs and Contcomp.fs in Solution Explorer
 *)


//General purpose registers for 64-bit
type reg64 =
    | Rax | Rcx | Rdx | Rbx | Rsi | Rdi | Rsp | Rbp | R8 | R9 | R10 | R11 | R12 | R13 | R14| R15 | Spill | Dummy

let removeFromList lst elem =
     List.filter (fun n -> n<>elem) lst 
