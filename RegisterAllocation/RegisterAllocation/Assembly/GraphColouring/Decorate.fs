module Decorate
(* File GraphColouring/Decorate.fs
   Decoration of abstract syntax of micro-c
   ahad@itu.dk, biha@itu.dk, and kmsa@itu.dk 2024-05-15
   Must precede Parse.fs in Solution Explorer
 *)

open Utility
open Absyn
open DecorAbsyn
let removeTemps lst =
    List.filter(fun (elem:string) -> if (elem.StartsWith "/") then false else true) lst 

(* Decoration and dataflow analysis of micro-c statements*)
let rec aStmt stmt lst =
    match stmt with
    | If(e, stmt1, stmt2) ->
        let elseStmt, lst1 = aStmt stmt2 lst
        let thenStmt, lst2 = aStmt stmt1 lst1
        let ex,newlist = aExpr e lst2
        DIf(ex, thenStmt, elseStmt, newlist), newlist
    | While(e, body) ->
        let ex, lst1 = aExpr e lst
        let newbody,newlist = aStmt body lst1
        DWhile(ex,newbody, lst1), newlist
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
        DBlock(stmtLst, removeTemps lst),newlist
    | Return None -> DReturn(None, lst), lst
    | Return (Some e) ->
        let ex, newlist = aExpr e lst
        DReturn(Some ex, newlist), newlist
  
and aStmtOrDec stmtOrDec lst  =
    (*for simplicity all temps are removed from liveness after each statement*)
    let tempsRemoved = removeTemps lst
    match stmtOrDec with 
    | Stmt stmt    ->
        let newstmt, newlist = aStmt stmt tempsRemoved
        (DStmt(newstmt,tempsRemoved), newlist)
    | Dec (typ, x) ->
        let newlist = removeFromList tempsRemoved x
        DDec(typ, x, tempsRemoved),newlist

(* dataflow analysis of micro-c expressions*)    
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
    | Temp(name, e) ->
        let newExpr1, lst1 = aExpr e lst
        Temp(name, newExpr1), name::lst1

(* dataflow analysis of variable accesses, pointer dereferences, and array indexing *)    
and aAccess access lst  =
  match access with
  | AccVar x            ->
      if List.contains x lst |> not
      then
        AccVar x, (x::lst)
      else
        AccVar x, lst
  | AccDeref e          ->
      let newExpr, newLst = aExpr e lst
      AccDeref newExpr, newLst
  | AccIndex (acc, idx) ->
      let newExpr, exprLst = aExpr idx lst
      let newAcc, newLst = aAccess acc exprLst
      AccIndex (newAcc, newExpr), newLst

(* Determines liveness of variables and temporaries in prog*)
let bottomUpAnalysis (Prog prog) =
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
    DProg(aux (List.rev prog) ([],[]))

     
let rec topDownStmt dstmt glovars =
    match dstmt with
    | DIf(e, dstmt1, dstmt2, info) ->
        let newLiveness = List.except glovars info
        let thenDstmt,_ = topDownStmt dstmt1 glovars
        let elseDstmt,_ = topDownStmt dstmt2 glovars
        DIf(e, thenDstmt, elseDstmt, newLiveness), newLiveness
    | DWhile(e, dstmt, info) ->
        let newLiveness = List.except glovars info
        let body, lst1 = topDownStmt dstmt glovars
        DWhile(e, body, newLiveness), newLiveness
    | DExpr(e, info) ->
        let newLiveness = List.except glovars info
        DExpr(e, newLiveness), newLiveness
    | DReturn (None, info) ->
        let newLiveness = List.except glovars info
        DReturn(None, newLiveness), []
    | DReturn (Some e, info) ->
        let newLiveness = List.except glovars info
        DReturn(Some e, newLiveness), []
    | DBlock(stmtordecs, info) ->
        let rec loop rest (accStmts as acc) =
            match rest with
            |[] -> acc
            |x::xs ->
                let newstmt = topDownDStmtordec x glovars
                loop xs (newstmt::accStmts)
        let stmtLst = loop stmtordecs []
        let newLiveness = List.except glovars info
        DBlock(List.rev stmtLst, newLiveness),newLiveness
        
and topDownDStmtordec dstmtordec glovars =
    match dstmtordec with
    | DDec(typ, name, info) ->
        let newLiveness = List.except glovars info
        DDec(typ, name, newLiveness)
    | DStmt(ds, info) ->
        let dstmt, liveness = topDownStmt ds glovars
        DStmt(dstmt, liveness)

(* Forward dataflow pass to remove global variables from liveness information*)  
let topDownAnalysis (DProg prog) =
    let rec aux res (dtree,glovars as acc) =
        match res with
        | [] -> List.rev dtree
        | x::xs ->
            match x with
            | DVardec(t, name, info) ->
                let newGlovars = Set.add name glovars
                aux xs (DVardec(t,name,info) :: dtree,newGlovars) 
            | DFundec(rtyp, name, args, body, info) ->
                let decoratedBody,stmtList = topDownStmt body glovars 
                aux xs (DFundec(rtyp,name,List.rev args, decoratedBody, stmtList)::dtree,glovars) 
    DProg(aux (prog) ([],Set.empty)) 


let livenessAnotator prog = bottomUpAnalysis prog |> topDownAnalysis