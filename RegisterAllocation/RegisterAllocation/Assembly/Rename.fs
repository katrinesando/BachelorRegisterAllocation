module Rename

open Absyn
open Utility
let rec rStmt stmt depth map =
    match stmt with
    | If(e, stmt1, stmt2) ->
        let ex = rExpr e depth map 
        let thenStmt = rStmt stmt1 (depth+1)  map
        let elseStmt = rStmt stmt2 (depth+1)  map
        If(ex, thenStmt, elseStmt)  
    | While(e, body) ->
        let ex = rExpr e depth  map 
        let newBody = rStmt body (depth+1)  map
        While(ex, newBody)
    | Expr e -> Expr(rExpr e depth map) 
    | Block stmts ->
        let rec loop rest acc =
            match rest with
            | [] -> List.rev (fst acc)
            | r::res ->
                let (s,newMap) = rStmtOrDec r (depth+1) (snd acc)
                loop res (s:: fst acc,newMap)
        Block(loop stmts ([],map))        
    | Return None -> Return None
    | Return (Some e) -> Return (Some (rExpr e depth map))
  
and rStmtOrDec stmtOrDec depth map  =
    match stmtOrDec with 
    | Stmt stmt    -> (Stmt(rStmt stmt depth map), map)
    | Dec (typ, x) ->
        let newmap = addToMap depth x map
        (Dec(typ, x), newmap)
    
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
    List.fold (fun acc arg -> addToMap 1 (snd arg) acc) map args

let renameVars (Prog prog) = 
    let rec aux res (tree,map) =
        match res with
        | [] -> List.rev tree
        | x :: xs ->
            match x with
            | Vardec(t, name) ->
                let newMap = addToMap 0 name map
                aux xs (Vardec(t,name) :: tree, newMap) 
            | Fundec(rtyp, name, args, body) ->
                let newMap = addFunArgsToMap args map
                let newBody = rStmt body 1 newMap
                aux xs (Fundec(rtyp,name,args,newBody)::tree,newMap)
    Prog (aux prog ([],Map.empty))