module Allocate

open Utility
open DecorAbsyn
type reg64 =
    | Rax | Rcx | Rdx | Rbx | Rsi | Rdi | Rsp | Rbp | R8 | R9 | R10 | R11 | R12 | R13 | R14| R15 | Dummy
let mem x xs = List.exists (fun y -> x=y) xs
type node = string * reg64 //varname * colour
type interferenceGraph = Map<string,node list>

let rec addVarToGraph name graph liveness=
    if Map.containsKey name graph then
        graph
    else
        let newNode = node(name,Dummy)
        let newLst = removeFromList liveness name
        let newGraph = List.fold (fun acc elem-> addVarToGraph elem graph newLst) graph newLst
        Map.fold (fun acc k lst ->
            if mem k newLst then
                Map.add k (newNode::lst) acc else acc) newGraph newGraph |>
        Map.add name (List.fold (fun acc elem -> node(elem,Dummy)::acc) [] newLst) 

let rec graphFromDStmt dstmt graph =
    match dstmt with
    |DIf(_, s1, s2, liveness) ->
        List.fold (fun acc elem -> addVarToGraph elem acc liveness) graph liveness |>
        graphFromDStmt s1 |> graphFromDStmt s2
    |DWhile(_, body, liveness) ->
        List.fold (fun acc elem -> addVarToGraph elem acc liveness) graph liveness|>
        graphFromDStmt body
    |DExpr(_, liveness) ->
        List.fold (fun acc elem -> addVarToGraph elem acc liveness) graph liveness
    |DBlock(stmtordecs, liveness) ->
        List.fold (fun acc elem -> addVarToGraph elem acc liveness) graph liveness |>
        List.fold (fun acc elem -> graphFromDStmtOrDec elem acc) <| stmtordecs
    |DReturn(_, liveness) ->
        List.fold (fun acc elem -> addVarToGraph elem acc liveness) graph liveness
    
and graphFromDStmtOrDec stmtOrDec graph =
    match stmtOrDec with
    | DStmt (dstmt,_) -> graphFromDStmt dstmt graph
    | DDec(_, name, liveness) ->
        List.fold (fun acc elem -> addVarToGraph elem acc liveness) graph liveness

let buildGraph (DProg prog) : interferenceGraph =
    let rec loop rest acc =
        match rest with
        | [] -> acc
        | x::xs ->
            match x with
            | DVardec(_, name, liveness) -> loop xs (addVarToGraph name acc liveness)
            | DFundec(_, _, _, body, liveness) ->
                let newlst = List.fold (fun acc elem -> addVarToGraph elem acc liveness) acc liveness
                loop xs (graphFromDStmt body newlst)  
    loop prog Map.empty