module Allocate

open System
open Utility
open DecorAbsyn

(* The 13 registers that can be used for temporary values in x86-64.
Allowing RDX requires special handling across IMUL and IDIV *)

let mem x xs = List.exists (fun y -> x=y) xs

type node = string //varname
type interferenceGraph = Map<node,int * reg64 * node list> //name, degree * colour * node list

let rec addVarToGraph name (graph : Map<string,int * reg64 * node list>) liveness =
    if Map.containsKey name graph then
        graph
    else
        let newNode = node name
        let newLst = removeFromList liveness name
        let newGraph = List.fold (fun acc elem-> addVarToGraph elem graph newLst) graph newLst
        Map.fold (fun acc k (_,_,lst) ->
            if mem k newLst && not (mem newNode lst) then 
                Map.add k (0,Dummy,newNode::lst) acc 
            else acc) newGraph newGraph |>
        Map.add name (List.fold (fun (_,_,acc) elem -> (0,Dummy,(elem::acc))) (0,Dummy,[]) newLst) //adds all elem from newLst to adj of k

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
        List.fold (fun acc elem -> addVarToGraph elem acc liveness) graph liveness |> //create graph
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
  

(* Helper function for searching in the interference graph *)
let simplify (graph : interferenceGraph) =
    let k = List.length temporaries
    let mins = Map.fold (fun (_,min as acc) name (deg,_,_) ->
                        if deg < min then (name,deg) else acc)
    let rec aux g stack (minname, mindeg) =
        match Map.tryFind minname g with
        | None-> stack
        | Some(degree, cl, adjList) ->
                let newGraph = decrementDegree g adjList |> Map.remove minname
                let newMins = mins (minname,Int32.MaxValue) newGraph
                if degree < k then
                    aux newGraph ((minname,cl,adjList)::stack) newMins
                else aux newGraph ((minname,Spill,adjList)::stack) newMins    
            
    aux graph [] (mins ("",Int32.MaxValue) graph)
    
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
        | (name, Spill, _) :: ns ->
            Map.add name Spill graph |>
            aux ns
        | _ -> failwith "something went wrong"
    aux stack Map.empty
   
let regAlloc prog = buildGraph prog |> simplify |> rebuildAndColour 