module Allocate
(* File Assembly/Allocate.fs
   graph colouring register allocation for micro-c
   ahad@itu.dk, biha@itu.dk, and kmsa@itu.dk 2024-05-15
   Must precede X64Comp.fs in Solution Explorer
 *)
open System
open Utility
open DecorAbsyn


type node = string //varname
type interferenceGraph = Map<node,int * node list> //name, degree * colour * node list

let temporaries =
    [Rcx;Rbx; Rsi; Rdi; R8; R9; R10; R11; R12; R13; R14; R15]
    
let mem x xs = List.exists (fun y -> x=y) xs
let addVarToGraph name (graph : interferenceGraph) liveness =
    if Map.containsKey name graph then
        graph
    else
        let newNode = node name
        let newLst = removeFromList liveness name
        let newGraph = List.fold (fun acc elem->
            match Map.tryFind elem acc with
            |Some (d,lst)->
                if mem newNode lst then acc else Map.add elem (d+1,newNode::lst) acc
            |None -> acc) graph newLst
        (*Uses newLst as the adjacency list of newNode*)
        Map.add newNode (List.length newLst,newLst) newGraph

(*Adds variables from liveness information annotated to dstmt to graph*)
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

(* Builds an interference graph for the given program *)
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
    
(* Decrements the degree of all nodes whose names appear in adjList in the graph g *)    
let decrementDegree g adjList = List.fold (fun acc elem ->
                        match Map.tryFind elem acc with
                        | Some (deg, lst) -> Map.add elem (deg-1, lst) acc
                        | None -> acc ) g adjList
  

(* Removes each node from the graph in order of ascending degree,
   each node is added to a list either with a dummy register value 
   or Spill, marking it such that spill code can be generated
*)
let simplify (graph : interferenceGraph) =
    let k = List.length temporaries
    let maximins = Map.fold (fun (mn,min,mxn,max as acc) name (deg,_) ->
                       let nmn, nmin, nmxn, nmax as na = if deg < min then (name,deg,mxn,max) else acc
                       if deg > max then (nmn,nmin,name,deg) else na)
    
    let rec aux g stack (minname, mindeg,maxname,maxdeg) =
        match Map.tryFind minname g with
        | None->
            stack
        | Some(degree, adjList) ->
                let newGraph = decrementDegree g adjList |> Map.remove minname
                let newMins = maximins (minname,Int32.MaxValue,maxname,Int32.MinValue) newGraph
                if degree < k then
                    aux newGraph ((minname,Dummy,adjList)::stack) newMins
                else
                    aux newGraph ((minname,Spill,adjList)::stack) newMins                   
    aux graph [] (maximins ("",Int32.MaxValue,"",Int32.MinValue) graph)
   
(*
    Gets a register used by none of the variables in lst as denoted by graph
*) 
let getUnusedRegister graph lst =
    let toExclude = List.fold (fun acc node ->
                       match Map.tryFind node graph with
                       | None -> acc
                       | Some col -> col :: acc) [] lst 
    let l = List.except toExclude temporaries
    if List.length l <> 0 then Some (List.head l) else None

(* colours the graph from which stack was made*) 
let rebuildAndColour stack =
    let rec aux s graph =
        match s with
        | [] -> graph
        | (name, Dummy, lst) :: ns ->
            match getUnusedRegister graph lst with
            | None -> failwith "something went wrong in colouring"
            | Some reg ->
                Map.add name reg graph |>
                aux ns
        | (name, Spill, lst) :: ns ->
            Map.add name Spill graph |>
            aux ns
        | _ -> failwith "something went wrong"
    aux stack Map.empty 
   
let regAlloc prog = buildGraph prog |> simplify |> rebuildAndColour 