module Decorate

open Utility
open Absyn
open DecorAbsyn
let removeTemps lst =
    List.filter(fun (elem:string) -> if (elem.StartsWith "/") then false else true) lst //for simplicity all temp are removed from liveness

let rec aStmt stmt lst =
    match stmt with
    | If(e, stmt1, stmt2) ->
        let (elseStmt, lst1) = aStmt stmt2 lst
        let (thenStmt, lst2) = aStmt stmt1 lst1
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
        DReturn(Some ex, lst), newlist
  
and aStmtOrDec stmtOrDec lst  =
    let tempsRemoved = removeTemps lst
    match stmtOrDec with 
    | Stmt stmt    ->
        let newstmt, newlist = aStmt stmt tempsRemoved
        (DStmt(newstmt,tempsRemoved), newlist)
    | Dec (typ, x) ->
        let newlist = removeFromList tempsRemoved x
        DDec(typ, x, tempsRemoved),newlist
    
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
        let (expr, lst, pr, _) = topDownExpr e info pointerRefs []
        let (thenDstmt, lst1, pr1) = topDownStmt dstmt1 lst pr
        let (elseDstmt, lst2, pr2) = topDownStmt dstmt2 lst1 pr1
        DIf(expr, thenDstmt, elseDstmt, (lst2, pr2)), lst2, pr2
    | DWhile(e, dstmt, info) ->
        let (expr, lst, pr, _) = topDownExpr e info pointerRefs []
        let (body, lst1, pr1) = topDownStmt dstmt lst pr
        DWhile(expr, body, (lst1, pr1)), lst1, pr1
    | DExpr(e, info) ->
        let (expr, lst, pr, _) = topDownExpr e info pointerRefs []
        DExpr(expr, (lst,pr)), lst, pr
    | DReturn (None, info)-> DReturn(None, (info, pointerRefs)), info, pointerRefs
    | DReturn (Some e, info) ->
        let (expr, lst, pr, _) = topDownExpr e info pointerRefs []
        DReturn(Some expr, (lst, pr)), lst, pr
    | DBlock(stmtordecs, info) ->
        let rec loop rest (accStmts, accLive, accPr as acc) =
            match rest with
            |[] -> acc
            |x::xs ->
                let newstmt, list, pr = topDownDStmtordec x accLive accPr
                loop xs (newstmt::accStmts, list, pr)
        let (stmtLst, newlist, pr) = loop stmtordecs ([],info, pointerRefs) 
        DBlock(List.rev stmtLst, (newlist, pr)),newlist, pr
        
and topDownDStmtordec dstmtordec livelist pointerRefs =
    match dstmtordec with
    | DDec(typ, name, info) ->
        match typ with
        | TypP _ ->
            let pr =  Map.add name None pointerRefs
            DDec(typ, name, (info, pr)), livelist, pr
        | _ -> DDec(typ, name, (info, pointerRefs)), livelist, pointerRefs
    | DStmt(ds, info) ->
        let (dstmt, lst, pr) = topDownStmt ds info pointerRefs
        DStmt(dstmt, (lst, pr)), lst, pr
and topDownExpr expr liveList pointerRefs varsAccessed =
    match expr with
    | Access acc ->
        let a, lst, pr, va = topDownAccess acc liveList pointerRefs varsAccessed
        Access a, lst, pr, va
    | Assign(acc, e) ->
        let expr, lst, pr, va = topDownExpr e liveList pointerRefs varsAccessed
        let a, lst1, pr1, va1 = topDownAccess acc lst pr va
        let newLive, newRefs, varAcc =
            match a with
            | AccVar n ->
                match Map.tryFind n pr1 with
                | None -> lst1, pr1, [n]
                | Some None -> lst1, Map.add n (Some va1) pr1, [n] //fx if pointer is not initalized
                | Some (Some refs) ->
                        let newPr = Map.add n (Some va1) pr1
                        lst1, newPr, [n]
            | _ -> lst1,pr1, va1
        Assign (a,expr),newLive, newRefs, varAcc
    | Addr acc ->
        let a, lst, pr, va  = topDownAccess acc liveList pointerRefs varsAccessed
        Addr a,lst,pr, va
    | CstI i -> CstI i, liveList, pointerRefs, varsAccessed
    | Prim1(ope, e) ->
        let expr, lst, pr, va = topDownExpr e liveList pointerRefs varsAccessed
        Prim1(ope, expr), lst, pr, va
    | Prim2(ope, e1, e2) ->
        let expr1, lst1, pr1, va1 = topDownExpr e1 liveList pointerRefs varsAccessed
        let(expr2, lst2, pr2, va2) = topDownExpr e2 lst1 pr1 va1
        Prim2(ope, expr1, expr2), lst2, pr2, va2
    | Andalso(e1, e2) ->
        let(expr1, lst1, pr1, va1) = topDownExpr e1 liveList pointerRefs varsAccessed
        let(expr2, lst2, pr2, va2) = topDownExpr e2 lst1 pr1 va1
        Andalso(expr1, expr2), lst2, pr2, va2
    | Orelse(e1, e2) ->
        let(expr1, lst1, pr1, va1) = topDownExpr e1 liveList pointerRefs varsAccessed
        let(expr2, lst2, pr2, va2) = topDownExpr e2 lst1 pr1 va1
        Orelse(expr1, expr2), lst2, pr2, va2
    | Call(name, e) ->
        let (expr, lst, pr, va) = List.fold(fun (exprs, liveVars, prMap, vars) elem ->
            let(expr, lst, pr, va) = topDownExpr elem liveVars prMap vars
            (expr :: exprs, lst, pr, va)) ([],liveList, pointerRefs, varsAccessed) e
        Call(name, expr), lst, pr, va
    | Temp(name, e) ->
        let(expr, lst, pr, va) = topDownExpr e liveList pointerRefs varsAccessed
        Temp(name, expr),lst ,pr, va
and topDownAccess acc liveList pointerRefs varsAccessed=
    match acc with
    |AccVar name ->
        AccVar name, liveList, pointerRefs, name :: varsAccessed
    |AccDeref e->
        let(expr, lst, pr, va) = topDownExpr e liveList pointerRefs varsAccessed
        AccDeref expr ,lst, pr, va
    |AccIndex(acc, idx) ->
        let(expr, lst, pr, va ) = topDownExpr idx liveList pointerRefs varsAccessed
        let a, lst1, pr1, va1 = topDownAccess acc lst pr va
        AccIndex (a,expr),lst1, pr1, va1
let topDownAnalysis (DProg prog) =
    let rec aux res (dtree,livelist, pointerRefs as acc) =
        match res with
        | [] -> dtree
        | x::xs ->
            match x with
            | DVardec(t, name, info) ->
                match t with
                | TypP _ ->
                    let pr = Map.add name None pointerRefs
                    aux xs (DVardec(t,name,(info, pr)) :: dtree,info,pr) 
                | _ ->
                    aux xs (DVardec(t,name,(info, pointerRefs)) :: dtree,info,pointerRefs) 
            | DFundec(rtyp, name, args, body, info) ->
                let (decoratedBody,stmtList, pr) = topDownStmt body livelist pointerRefs //Cannot assign to variable from function
                aux xs (DFundec(rtyp,name,List.rev args, decoratedBody, (stmtList, pr))::dtree,info, pointerRefs) // pointerRefs - local pointers don't effect other local pointers - hence not updated
    DProg(aux (prog) ([],[], Map.empty))   


let livenessAnotator prog = bottomUpAnalysis prog |> topDownAnalysis