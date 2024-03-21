module Rename

open Absyn
open Utility
let rec rStmt stmt depth map counter =
    match stmt with
    | If(e, stmt1, stmt2) ->
        let ex = rExpr e depth map 
        let thenStmt, newCounter1 = rStmt stmt1 (depth+1)  map counter
        let elseStmt, newCounter2 = rStmt stmt2 (depth+1)  map newCounter1 
        If(ex, thenStmt, elseStmt), newCounter2  
    | While(e, body) ->
        let ex = rExpr e depth  map 
        let newBody, newCounter = rStmt body (depth+1) map counter
        While(ex, newBody), newCounter
    | Expr e -> Expr(rExpr e depth map), counter
    | Block stmts ->
        let rec loop rest acc c =
            match rest with
            | [] -> List.rev (fst acc), c
            | r::res ->
                let (s,newMap), newCounter = rStmtOrDec r (depth+1) (snd acc) c
                loop res (s:: fst acc,newMap) newCounter
        let body, newCounter2 = loop stmts ([],map) counter
        Block(body), newCounter2        
    | Return None -> Return None, counter
    | Return (Some e) -> Return (Some (rExpr e depth map)), counter
  
and rStmtOrDec stmtOrDec depth map counter =
    match stmtOrDec with 
    | Stmt stmt    ->
        let stmt, newCounter = rStmt stmt depth map counter
        (Stmt(stmt), map), newCounter
    | Dec (typ, x) ->
        let newName = x + string counter 
        let newmap = addToMap depth newName map
        (Dec(typ, newName), newmap), counter+1
    
and rExpr (e : expr) depth map = 
    match e with
    | Access acc     -> Access (rAccess acc depth map)
    | Assign(acc, e) -> Assign (rAccess acc depth map,rExpr e depth map)
    | CstI i         -> CstI i
    | Addr acc       -> Addr (rAccess acc depth map)
    | Prim1(ope, e)  -> Prim1(ope, rExpr e depth map)
    | Prim2 (ope, e1, e2) ->
        let ex1 = rExpr e1 depth map
        let ex2 = rExpr e2 depth map
        Prim2 (ope, ex1, ex2)
    | Andalso(e1,e2)   ->
        let ex1 = rExpr e1 depth map
        let ex2 = rExpr e2 depth map
        Andalso(ex1,ex2)
    | Orelse(e1, e2) ->
        let ex1 = rExpr e1 depth map
        let ex2 = rExpr e2 depth map
        Orelse(ex1,ex2)
    | Call(name, lst) ->
        let rec loop rest acc =
            match rest with
            | [] -> List.rev acc
            | r::res ->
                let s = rExpr r depth map
                loop res (s:: acc)
        Call (name,loop lst [])
and rAccess access depth map  =
  match access with
  | AccVar x            -> AccVar (lookupInMap depth x map)
  | AccDeref e          -> AccDeref (rExpr e depth map)
  | AccIndex (acc, idx) -> AccIndex (rAccess acc depth map,rExpr idx depth map)

(*function arguments are depth 1*)
let addFunArgsToMap args map =
    List.fold (fun m arg -> addToMap 1 (snd arg) m) map args

let renameVars (Prog prog) =
    let rec aux res (tree,map) counter =
        match res with
        | [] -> List.rev tree
        | x :: xs ->
            match x with
            | Vardec(t, name) ->
                let newName = (name + string counter)
                let newMap = addToMap 0 newName map
                aux xs (Vardec(t,newName) :: tree, newMap) (counter+1)
            | Fundec(rtyp, name, args, body) ->
                let renamedArgs, newCounter1 =
                    List.fold (fun (lst, c) (typ, name) -> (typ,name + string c) :: lst, c+1) ([], counter) args 
                let newMap= addFunArgsToMap renamedArgs map
                let newBody,newCounter2 = rStmt body 1 newMap newCounter1
                aux xs (Fundec(rtyp,name,renamedArgs,newBody)::tree,newMap) newCounter2
    Prog (aux prog ([],Map.empty) 0)