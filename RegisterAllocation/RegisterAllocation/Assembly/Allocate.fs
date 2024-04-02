module Allocate

open Utility
open DecorAbsyn

type reg64 =
    | Rax | Rcx | Rdx | Rbx | Rsi | Rdi | Rsp | Rbp | R8 | R9 | R10 | R11 | R12 | R13 | R14| R15 | Spill | Dummy

(* The 13 registers that can be used for temporary values in i386.
Allowing RDX requires special handling across IMUL and IDIV *)
let temporaries =
    [Rcx; Rdx]//; Rbx; Rsi; Rdi; R8; R9; R10; R11; R12; R13; R14; R15]

let mem x xs = List.exists (fun y -> x=y) xs

type node = string //varname
type interferenceGraph = Map<node,int * reg64 * node list> //name, degree * colour * node list

let rec addVarToGraph name (graph : Map<string,int * reg64 * node list>) liveness=
    if Map.containsKey name graph then
        graph
    else
        let newNode = node name
        let newLst = removeFromList liveness name
        let newGraph = List.fold (fun acc elem-> addVarToGraph elem graph newLst) graph newLst
        Map.fold (fun acc k (_,_,lst) ->
            if mem k newLst then
                Map.add k (0,Dummy,newNode::lst) acc else acc) newGraph newGraph |>
        Map.add name (List.fold (fun (_,_,acc) elem -> (0,Dummy,(elem::acc))) (0,Dummy,[]) newLst) 

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
    loop prog Map.empty |>
    Map.map (fun _ (degree,_, lst) -> (List.length lst, Dummy, lst)) //Populate map with degree information
    
let decrementDegree g adjList = List.fold (fun acc elem ->
                        match Map.tryFind elem g with
                        | Some (deg, c, lst) -> Map.add elem (deg-1, c, lst) g
                        | None -> acc ) g adjList

//let sortList graph =
    

(* Helper function for searching in the interference graph *)
let simplify (graph : interferenceGraph) =
    let k = List.length temporaries
    let rec aux g stack mindeg =
        match g with
        | _ when Map.count g = 0 -> stack
        | _ ->
            let ng,ns, degree = Map.fold (fun (g, stack, min) name (degree,cl,adjList) ->    
                if degree < k then
                    let newGraph = decrementDegree g adjList 
                    Map.remove name newGraph, (name,cl,adjList)::stack, if degree > mindeg then degree else mindeg
                    else
                        if min <= k then
                            g,stack, min
                            else
                                let newGraph = decrementDegree g adjList
                                //Reset mindeg after spilling
                                Map.remove name newGraph, (name,Spill,adjList)::stack,mindeg) (graph,[], mindeg) graph
            
            if degree > mindeg then
                aux ng ns degree
                else
                    aux ng ns mindeg
    aux graph [] k
    
    
   
    