module Allocate

open Absyn

type node =
    | InnerNode of stmtordec list //basic block (node)
    | OuterNode of topdec list
    
type CFG =
    | Empty
    | Nodes of node * node * Map<node, node list> //entry, exit, and Map of bb & adjencency list (edges)
 
type reg64 =
    | Rax | Rcx | Rdx | Rbx | Rsi | Rdi | Rsp | Rbp | R8 | R9 | R10 | R11 | R12 | R13 | R14| R15 
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

let join p q =
    Map(Seq.concat [(Map.toSeq p);(Map.toSeq q)])
    
let stmtToCFG stmt  =
    let rec aux rest acc =
        match rest with
        | If(cond, s1, s2) ->
            let entry = InnerNode
        | Block stmtordecs
    aux stmt Empty
    
let createCFG prog =
    let rec aux rest acc = 
        match rest with
        | [] -> acc
        | x :: xs ->
            match x, acc with
            | Vardec _, Empty ->
                let first = OuterNode (x::[])
                let newCFG = Nodes (first,first,Map.empty |> Map.add first [])
                aux xs newCFG
            | Vardec _, Nodes(OuterNode decs, _, nodeMap) ->
                let newEntry = OuterNode ([x]@decs)
                let newCFG = Nodes (newEntry,newEntry,nodeMap)
                aux xs newCFG
            | Fundec (_, name, args, body), Empty -> //Subject to change
                let newCFG = stmtToCFG body
                aux xs newCFG
            | Fundec(_, name, args, body), Nodes(entry, exit, nodeMap) -> //this is wrong
                let (subEntry, subExit, subNMap) = stmtToCFG body
                let newAdj = subEntry :: (Map.find exit nodeMap)
                let newMap = Map.add exit newAdj nodeMap |> join subNMap
                aux xs (Nodes(entry,subExit,newMap))
                
    aux prog Empty 
 
