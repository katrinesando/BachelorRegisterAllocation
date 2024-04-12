module Decorate

open Utility
open Absyn
open DecorAbsyn
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
    let tempRemoved = List.filter(fun (elem:string) -> if (elem.StartsWith "/") then false else true ) lst //for simplicity all temp are removed from liveness
    match stmtOrDec with 
    | Stmt stmt    ->
        let newstmt, newlist = aStmt stmt tempRemoved
        (DStmt(newstmt,tempRemoved), newlist)
    | Dec (typ, x) ->
        let newlist = removeFromList tempRemoved x
        DDec(typ, x, tempRemoved),newlist
    
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
        (*match e with
        | Prim1("printc", _) | Prim1("printi", _) ->
            let newExpr1, lst1 = aExpr e lst
            newExpr1, lst1
        | _ ->*)
            let newExpr1, lst1 = aExpr e lst
            Temp(name, newExpr1), name::lst1
and aAccess access lst  =
  match access with
  | AccVar x            ->
    //If is pointer then variable should stay alive for same amount of time as left side
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
    
let rec topDownStmt dstmt livelist pointerRefs=
    match dstmt with
    | DIf(e, dstmt1, dstmt2, info) ->
        let (expr, lst, pr) = topDownExpr e info pointerRefs
        let (thenDstmt, lst1, pr1) = topDownStmt dstmt1 lst pr
        let (elseDstmt, lst2, pr2) = topDownStmt dstmt1 lst1 pr1
        DIf(expr, thenDstmt, elseDstmt, lst2), lst2, pr2
    | DWhile(e, dstmt, info) ->
        let (expr, lst, pr) = topDownExpr e info pointerRefs
        let (body, lst1, pr1) = topDownStmt dstmt lst pr
        DWhile(expr, body, lst1), lst1, pr1
    | DExpr(e, info) ->
        let (expr, lst, pr) = topDownExpr e info pointerRefs
        DExpr(expr, lst), lst, pr
    | DReturn (None, info)-> DReturn(None, info), info, pointerRefs
    | DReturn (Some e, info) ->
        let (expr, lst, pr) = topDownExpr e info pointerRefs
        DReturn(Some expr, lst), lst, pr
    | DBlock(stmtordecs, info) ->
        let rec loop rest (accStmts, accLive, accPr as acc) =
            match rest with
            |[] -> acc
            |x::xs ->
                let newstmt, list, pr = topDownDStmtordec x accLive accPr
                loop xs (newstmt::accStmts, list, pr)
        let (stmtLst, newlist, pr) = loop stmtordecs ([],info, pointerRefs) 
        DBlock(List.rev stmtLst, newlist),newlist, pr
        
and topDownDStmtordec dstmtordec livelist pointerRefs =
    match dstmtordec with
    | DDec(typ, name, info) ->
        match typ with
        | TypP _ -> DDec(typ, name, info), livelist, Map.add name None pointerRefs
        | _ -> DDec(typ, name, info), livelist, pointerRefs
    | DStmt(ds, info) ->
        let (dstmt, lst, pr) = topDownStmt ds info pointerRefs
        DStmt(dstmt, lst), lst, pr
and topDownExpr expr liveList pointerRefs =
    match expr with
    | Access acc ->
        let a, lst, pr = topDownAccess acc liveList pointerRefs
        Access a, lst, pr
    | Assign(acc, e) ->
        let expr, lst, pr = topDownExpr e liveList pointerRefs
        let a, lst1, pr1 = topDownAccess acc lst pr
        let newLive =
            match a with
            | AccVar n ->
                match Map.tryFind name pointerRefs with
                | None -> lst1
                | Some ref ->
                    if mem ref liveList then removeFromList lst1 ref
                    else lst1
            | _ -> lst1
        let newRefs =
            match expr with
            | Temp(_, expr)
        Assign (a,),newLive
    | Addr acc ->
        let a, lst, pr = topDownAccess acc liveList pointerRefs
        Addr a,lst,pr
    | CstI i -> CstI i, liveList, pointerRefs
    | Prim1(ope, e) ->
        let(expr, lst, pr) = topDownExpr e liveList pointerRefs
        Prim1(ope, expr), lst, pr
    | Prim2(ope, e1, e2) ->
        let(expr1, lst1, pr1) = topDownExpr e1 liveList pointerRefs
        let(expr2, lst2, pr2) = topDownExpr e2 lst1 pr1
        Prim2(ope, expr1, expr2), lst2, pr2
    | Andalso(e1, e2) ->
        let(expr1, lst1, pr1) = topDownExpr e1 liveList pointerRefs
        let(expr2, lst2, pr2) = topDownExpr e2 lst1 pr1
        Andalso(expr1, expr2), lst2, pr2
    | Orelse(e1, e2) ->
        let(expr1, lst1, pr1) = topDownExpr e1 liveList pointerRefs
        let(expr2, lst2, pr2) = topDownExpr e2 lst1 pr1
        Orelse(expr1, expr2), lst2, pr2
    | Call(name, e) ->
        let (expr, lst, pr) = List.fold(fun (exprs, liveVars, prMap) elem ->
            let(expr, lst, pr) = topDownExpr elem liveVars prMap
            (expr :: exprs, lst, pr)) ([],liveList, pointerRefs) e
        Call(name, expr), lst, pr
    | Temp(name, e) ->
        let(expr, lst, pr) = topDownExpr e liveList pointerRefs
        Temp(name, expr),lst ,pr
and topDownAccess acc liveList pointerRefs varsAccessed=
    match acc with
    |AccVar name ->
        match Map.tryFind name pointerRefs with
        | None ->
            AccVar name, liveList, pointerRefs, name :: varsAccessed
        | Some ref ->
            if mem ref liveList then AccVar name, liveList, pointerRefs
            else AccVar name, ref :: liveList, pointerRefs, name :: varsAccessed
    |AccDeref e->
        let(expr, lst, pr) = topDownExpr e liveList pointerRefs
        AccDeref expr ,lst, pr
    |AccIndex(acc, idx) ->
        let(expr, lst, pr) = topDownExpr idx liveList pointerRefs
        let a, lst1, pr1 = topDownAccess acc lst pr
        AccIndex (a,expr),lst1, pr1
let topDownAnalysis (DProg prog) =
    let rec aux res (dtree,livelist as acc) =
        match res with
        | [] -> dtree
        | x::xs ->
            match x with
            | DVardec(t, name, info) ->
                let newlist = removeFromList livelist name
                aux xs (DVardec(t,name,newlist) :: dtree,newlist) 
            | DFundec(rtyp, name, args, body, info) ->
                let (decoratedBody,stmtList) = aStmt body livelist
                let newlist = List.fold (fun acc elem -> removeFromList acc (snd elem)) stmtList args
                aux xs (DFundec(rtyp,name,args, decoratedBody, stmtList)::dtree,newlist) 
    DProg(aux (prog) ([],[]))   


let livenessAnotator prog = bottomUpAnalysis prog |> topDownAnalysis