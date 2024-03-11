module Rename

open Absyn
open Utility
let rec rStmt stmt depth funEnv map =
    match stmt with
    | If(e, stmt1, stmt2) ->
        let ex = rExpr e depth funEnv map 
        let thenStmt = rStmt stmt1 (depth+1) funEnv map
        let elseStmt = rStmt stmt2 (depth+1) funEnv map
        If(ex, thenStmt, elseStmt)  
    | While(e, body) ->
        let ex = rExpr e depth funEnv map 
        let newBody = rStmt body (depth+1) funEnv map
        While(ex, newBody)
    | Expr e -> Expr(rExpr e depth funEnv map) 
    | Block stmts ->
        let rec loop rest acc =
            match rest with
            | [] -> List.rev (fst acc)
            | r::res ->
                let (s,newMap) = rStmtOrDec r (depth+1) funEnv (snd acc)
                loop res (s:: fst acc,newMap)
        Block(loop stmts ([],map))        
    | Return None -> Return None
    | Return (Some e) -> Return (Some (rExpr e depth funEnv map))
  
and rStmtOrDec stmtOrDec depth funEnv map  =
    match stmtOrDec with 
    | Stmt stmt    -> (Stmt(rStmt stmt depth funEnv map), map)
    | Dec (typ, x) ->
        let newmap = addToMap depth x map
        (Dec(typ, x), newmap)
    
and rExpr (e : expr) depth (funEnv : funEnv) map = 
    match e with
    | Access acc     -> Access (rAccess acc depth funEnv map)
    | Assign(acc, e) -> Assign (rAccess acc depth funEnv map,rExpr e depth funEnv map)
    | CstI i         -> CstI i
    | Prim1(ope, e)  -> Prim1(ope, rExpr e depth funEnv map)
    | Prim2 (ope, e1, e2) ->
        let ex1 = rExpr e1 depth funEnv map
        let ex2 = rExpr e2 depth funEnv map
        Prim2 (ope, ex1, ex2)
    | Andalso(e1,e2)   ->
        let ex1 = rExpr e1 depth funEnv map
        let ex2 = rExpr e2 depth funEnv map
        Andalso(ex1,ex2)
    | Orelse(e1, e2) ->
        let ex1 = rExpr e1 depth funEnv map
        let ex2 = rExpr e2 depth funEnv map
        Orelse(ex1,ex2)
    | Call(name, lst) ->
        let rec loop rest acc =
            match rest with
            | [] -> List.rev acc
            | r::res ->
                let s = rExpr r depth funEnv map
                loop res (s:: acc)
        Call (name,loop lst [])
and rAccess access depth funEnv map  =
  match access with
  | AccVar x            -> AccVar (lookupInMap depth x map)
  | AccDeref e          -> AccDeref (rExpr e depth funEnv map)
  | AccIndex (acc, idx) -> AccIndex (rAccess acc depth funEnv map,rExpr idx depth funEnv map)


let renameVars prog =
    let ((varEnv,_),funEnv, m) = makeEnvs prog 
    let rec aux res acc =
        match res with
        | [] -> List.rev acc
        | x :: xs ->
            match x with
            | Vardec(t, name) ->
                aux xs (Vardec(t,name) :: acc) 
            | Fundec(rtyp, name, args, body) ->
                let (_,_,paras) = lookup funEnv name
                let locEnv = bindParams paras (varEnv,0)
                let decoratedBody = rStmt body (snd locEnv) funEnv m
                aux xs (Fundec(rtyp,name,args,decoratedBody)::acc)
    aux prog []