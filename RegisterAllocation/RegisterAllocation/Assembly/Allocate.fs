module Allocate

open System
open Utility
open DecorAbsyn

(* The 13 registers that can be used for temporary values in x86-64.
Allowing RDX requires special handling across IMUL and IDIV *)



type node = string //varname
type interferenceGraph = Map<node,int * reg64 * node list> //name, degree * colour * node list

let rec addVarToGraph name (graph : Map<string,int * reg64 * node list>) liveness =
    if Map.containsKey name graph then
        graph
    else
        let newNode = node name
        let newLst = removeFromList liveness name
        let newGraph = List.fold (fun acc elem->
            match Map.tryFind elem acc with
            |Some (d,_,lst)->
                if mem newNode lst then acc else Map.add elem (d+1,Dummy,newNode::lst) acc
            |None -> acc) graph newLst
        Map.add newNode (List.length newLst,Dummy,newLst) newGraph//adds all elem from newLst to adj of newNode

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
    loop prog Map.empty
    
let decrementDegree g adjList = List.fold (fun acc elem ->
                        match Map.tryFind elem acc with
                        | Some (deg, c, lst) -> Map.add elem (deg-1, c, lst) acc
                        | None -> acc ) g adjList
  

(* Helper function for searching in the interference graph *)
let simplify (graph : interferenceGraph) =
    let k = List.length temporaries
    let maximins = Map.fold (fun (mn,min,mxn,max as acc) name (deg,_,_) ->
                       let nmn, nmin, nmxn, nmax as na = if deg < min then (name,deg,mxn,max) else acc
                       if deg > max then (nmn,nmin,name,deg) else na)
    
    let rec aux g stack (minname, mindeg,maxname,maxdeg) =
        match Map.tryFind minname g with
        | None->
            stack
        | Some(degree, cl, adjList) ->
                let newGraph = decrementDegree g adjList |> Map.remove minname
                let newMins = maximins (minname,Int32.MaxValue,maxname,Int32.MinValue) newGraph
                if degree < k then
                    aux newGraph ((minname,cl,adjList)::stack) newMins
                else
                    aux newGraph ((minname,Spill,adjList)::stack) newMins
                    //match Map.tryFind maxname g with
                    //| None -> stack
                    //| Some (_, cl, adjList) ->
                    //    let newGraph = decrementDegree g adjList |> Map.remove maxname
                    //    let newMins = maximins (minname,Int32.MaxValue,maxname,Int32.MinValue) newGraph
                    //    aux newGraph ((maxname,Spill,adjList)::stack) newMins
                            
            
    aux graph [] (maximins ("",Int32.MaxValue,"",Int32.MinValue) graph)
    
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
            Map.add name Spill graph |> //If everything is over k, everything is Spilled - look into fix for future
            aux ns
        | _ -> failwith "something went wrong"
    aux stack Map.empty 
   
let regAlloc prog = buildGraph prog |> simplify |> rebuildAndColour 