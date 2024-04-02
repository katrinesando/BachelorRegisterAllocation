module Allocate

open System
open Absyn
open DecorAbsyn
type reg64 =
    | Rax | Rcx | Rdx | Rbx | Rsi | Rdi | Rsp | Rbp | R8 | R9 | R10 | R11 | R12 | R13 | R14| R15 | Spill | Dummy
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

let removeFromList lst elem =
     List.filter (fun n -> n<>elem) lst
     
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

let rec aStmt stmt lst =
    match stmt with
    | If(e, stmt1, stmt2) ->
        let (elseStmt, lst1) = aStmt stmt2 lst
        let (thenStmt, lst2) = aStmt stmt1 lst1
        let ex,newlist = aExpr e lst2
        DIf(ex, thenStmt, elseStmt, lst), newlist
    | While(e, body) ->
        let ex, lst1 = aExpr e lst
        let newbody,newlist = aStmt body lst1
        DWhile(ex,newbody, lst), newlist
    | Expr e ->
        let ex, newlist = aExpr e lst
        DExpr(ex,newlist), newlist
    | Block stmts ->
        let rec loop rest (accStmts, accLive as acc) =
            match rest with
            |[] -> acc
            |x::xs ->
                let newstmt, list = aStmtOrDec x accLive
                loop xs (newstmt::accStmts, list)
        let (stmtLst, newlist) = loop (List.rev stmts) ([],lst)
        DBlock(stmtLst, lst),newlist
    | Return None -> DReturn(None, lst), lst
    | Return (Some e) ->
        let ex, newlist = aExpr e lst
        DReturn(Some ex, lst), newlist
  
and aStmtOrDec stmtOrDec lst  =
    match stmtOrDec with 
    | Stmt stmt    ->
        let newstmt, newlist = aStmt stmt lst
        (DStmt(newstmt,lst), newlist)
    | Dec (typ, x) ->
        let newlist = removeFromList lst x
        DDec(typ, x, lst),newlist
    
and aExpr (e : expr) lst = 
    match e with
    | Access acc     ->
        let newAcc, newlst = aAccess acc lst
        Access newAcc, newlst
    | Assign(acc, e) ->
        let newAcc, accLst = aAccess acc lst
        let newExpr,newlst = aExpr e accLst
        Assign (newAcc,newExpr), newlst
    | Addr acc         ->
         let newAcc, newlst = aAccess acc lst
         Addr newAcc, newlst
    | CstI i         -> CstI i,lst
    | Prim1(ope, e)  ->
        let newExpr, newlst = aExpr e lst
        Prim1(ope, newExpr), newlst
    | Prim2 (ope, e1, e2) ->
        let newExpr1, lst1 = aExpr e1 lst
        let newExpr2, newlst = aExpr e2 lst1
        Prim2(ope, newExpr1, newExpr2), newlst
    | Andalso(e1,e2)   ->
        let newExpr1, lst1 = aExpr e1 lst
        let newExpr2, newlst = aExpr e2 lst1
        Andalso(newExpr1, newExpr2), newlst
    | Orelse(e1, e2) ->
        let newExpr1, lst1 = aExpr e1 lst
        let newExpr2, newlst = aExpr e2 lst1
        Orelse(newExpr1, newExpr2), newlst
    | Call(name, param) ->
        let rec loop rest acc =
            match rest with
            | [] -> acc
            | x::xs ->
                let newExpr, newlst = aExpr x acc
                loop xs newlst
        let newlst = (loop param lst)
        Call(name,param), newlst
and aAccess access lst  =
  match access with
  | AccVar x            ->
      if List.contains x lst |> not
      then
        AccVar x, (x::lst)  //adds live variable to list
      else
        AccVar x, (lst)
  | AccDeref e          ->
      let newExpr, newLst = aExpr e lst
      AccDeref newExpr, newLst
  | AccIndex (acc, idx) ->
      let newExpr, exprLst = aExpr idx lst
      let newAcc, newLst = aAccess acc exprLst
      AccIndex(newAcc, newExpr), newLst

let livenessAnotator (Prog prog) =
    let rec aux res (dtree,livelist as acc) =
        match res with
        | [] -> dtree
        | x :: xs ->
            match x with
            | Vardec(t, name) ->
                let newlist = removeFromList livelist name
                aux xs (DVardec(t,name,newlist) :: dtree,newlist) 
            | Fundec(rtyp, name, args, body) ->
                let (decoratedBody,stmtList) = aStmt body livelist
                let newlist = List.fold (fun acc elem -> removeFromList acc (snd elem)) stmtList args
                aux xs (DFundec(rtyp,name,args, decoratedBody, stmtList)::dtree,newlist) 
    DProg(aux (List.rev prog) ([],[])) //starts from the bottom of the program

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
                        if min < k then
                            g,stack, min
                            else
                                let newGraph = decrementDegree g adjList
                                //Reset mindeg after spilling
                                Map.remove name newGraph, (name,Spill,adjList)::stack,mindeg) (graph,[], mindeg) graph
            if degree > mindeg then
                aux ng ns degree
                else
                    aux ng ns mindeg
    aux graph [] (k-1)
    
    
   
    