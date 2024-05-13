module Rename
(* File Assembly/Rename.fs
   Renames variables, as well as wrapping expressions in temporaries 
   ahad@itu.dk, biha@itu.dk, and kmsa@itu.dk 2024-05-15
   Must precede Parse.fs in Solution Explorer
 *)

open Absyn

(* Looks up in map to replace uses of renamed variables:

    * depth     is the current program depth
    * name      is the name of the variable to replace
    * m         is the map used for lookup
 *)
let rec lookupInMap depth (name : string) m =
    if depth >= 0 then
        match Map.tryFind depth m with
        | None -> lookupInMap (depth-1) name m
        | Some vars ->                
                let rec aux rest  = 
                    match rest with
                    |[] ->  lookupInMap (depth-1) name m 
                    |(n:string)::xs -> if n.StartsWith(name) then n else aux xs
                aux vars
    else
        failwith ("variable " + name + " not declared")

(* Add depth (key) and name (value) to map. Used for replacing uses of renamed variables *)
let addToMap depth name m =
    match Map.tryFind depth m with
    |None -> Map.add depth [name] m
    |Some vars ->
        let newlst = name::vars
        Map.add depth newlst m

(* Traverses statements and traps expressions as temporaries:
   
   * stmt   is the statement to be traversed
   * depth  is the current depth of the program
   * map    is the map used to store renamed variable names
   * counter is the global counter used for renaming variables
   * tempCount is the global counter used for unique temporary names
      
 *)     
let rec rStmt stmt depth map counter tempCount =
    match stmt with
    | If(e, stmt1, stmt2) ->
        let ex, newTempCount1 = rExpr e depth map tempCount
        let thenStmt, newCounter1, newTempCount2 = rStmt stmt1 (depth+1)  map counter newTempCount1
        let elseStmt, newCounter2, newTempCount3 = rStmt stmt2 (depth+1)  map newCounter1 newTempCount2
        If(Temp(("/"+ string newTempCount3), ex), thenStmt, elseStmt), newCounter2, newTempCount3+1  
    | While(e, body) ->
        let ex, newTempCount1 = rExpr e depth  map tempCount
        let newBody, newCounter, newTempCount2 = rStmt body (depth+1) map counter newTempCount1
        While(Temp(("/"+ string newTempCount2), ex), newBody), newCounter, newTempCount2+1
    | Expr e ->
        let ex, newTempCount1 = rExpr e depth map tempCount
        Expr(Temp(("/"+ string newTempCount1), ex)), counter, newTempCount1+1
    | Block stmts ->
        let rec loop rest acc c tc =
            match rest with
            | [] -> List.rev (fst acc), c, tc
            | r::res ->
                let (s,newMap), newCounter, newTempCount  = rStmtOrDec r (depth+1) (snd acc) c tc
                loop res (s:: fst acc,newMap) newCounter newTempCount
        let body, newCounter2, newTempCount2 = loop stmts ([],map) counter tempCount
        Block(body), newCounter2, newTempCount2         
    | Return None -> Return None, counter, tempCount
    | Return (Some e) ->
        let ex, newTempCount = rExpr e depth map tempCount
        Return (Some (Temp(("/"+ string newTempCount), ex))), counter, newTempCount+1

(* Traverses statements or declarations and renames the declaration of variables *)
and rStmtOrDec stmtOrDec depth map counter tempCount =
    match stmtOrDec with 
    | Stmt stmt    ->
        let stmt, newCounter, newTempCount = rStmt stmt depth map counter tempCount
        (Stmt(stmt), map), newCounter, newTempCount
    | Dec (typ, x) ->
        let newName = x + string counter 
        let newmap = addToMap depth newName map
        (Dec(typ, newName), newmap), counter+1, tempCount

(* Traverses expressions and wraps expressions in temporaries *)
and rExpr (e : expr) depth map tempCount = 
    match e with
    | Access acc     ->
        let rac, newTempCount = rAccess acc depth map tempCount
        Access rac, newTempCount
    | Assign(acc, e) ->
        let ex, newTempCount1 = rExpr e depth map tempCount
        let rac, newTempCount2 = rAccess acc depth map newTempCount1 
        Assign (rac, Temp("/" + string newTempCount2,ex)), newTempCount2+1
    | CstI i         -> CstI i, tempCount
    | Addr acc       ->
        let rac, newTempCount = rAccess acc depth map tempCount
        Addr rac, newTempCount
    | Prim1(ope, e)  ->
        let ex, newTempCount = rExpr e depth map tempCount
        Prim1(ope, Temp("/" + string newTempCount,ex)), newTempCount+1
    | Prim2 (ope, e1, e2) ->
        let ex1, newTempCount1 = rExpr e1 depth map tempCount
        let ex2, newTempCount2 = rExpr e2 depth map newTempCount1
        Prim2 (ope, Temp ("/"+ string newTempCount2,ex1), Temp ("/"+ string (newTempCount2+1),ex2)), newTempCount2+2
    | Andalso(e1,e2)   ->
        let ex1, newTempCount1 = rExpr e1 depth map tempCount
        let ex2, newTempCount2 = rExpr e2 depth map newTempCount1
        Andalso(ex1,ex2), newTempCount2
    | Orelse(e1, e2) ->
        let ex1, newTempCount1 = rExpr e1 depth map tempCount
        let ex2, newTempCount2 = rExpr e2 depth map newTempCount1
        Orelse(ex1,ex2), newTempCount2
    | Call(name, lst) ->
        let rec loop rest acc tc=
            match rest with
            | [] -> List.rev acc, tc
            | r::res ->
                let s, newTempCount1 = rExpr r depth map tc
                (* function arguments are not wrapped in temps to avoid additional mov instructions*)
                loop res (s:: acc) newTempCount1 
        let exLst, newTempCount2 = loop lst [] tempCount
        Call (name,exLst), newTempCount2

(* Traverses accesses, renames variable uses, and wraps expressions in temporaries *)
and rAccess access depth map tempCount =
  match access with
  | AccVar x            -> AccVar (lookupInMap depth x map), tempCount
  | AccDeref e          ->
      let ex, newTempCount = rExpr e depth map tempCount
      AccDeref (Temp ("/"+ string newTempCount,ex)), newTempCount+1
  | AccIndex (acc, idx) ->
      let rac, newTempCount1= rAccess acc depth map tempCount
      let ex, newTempCount2 = rExpr idx depth map newTempCount1
      AccIndex (rac,Temp ("/"+ string newTempCount2,ex)), newTempCount2+1

(* Adds functions arguments to map for renaming:
   
   * args   is function arguments
   * map    is the map used to store renamed variable names

   AddToMap is called with 1 as argument, as function arguments are depth 1 in the program
*)
let addFunArgsToMap args map =
    List.fold (fun m arg -> addToMap 1 (snd arg) m) map args

(* Initiates rename pass calling other recursive functions
  
   AddToMap is called with 1 for function arguments, as they are depth 1 in the program
   AddToMap is called with 0 for global variables, as they are depth 0 in the program 
*)
let renameVars (Prog prog) =
    let rec aux res (tree,map) counter tc =
        match res with
        | [] -> List.rev tree
        | x :: xs ->
            match x with
            | Vardec(t, name) ->
                let newName = (name + string counter)
                let newMap = addToMap 0 newName map
                aux xs (Vardec(t,newName) :: tree, newMap) (counter+1) tc
            | Fundec(rtyp, name, args, body) ->
                let renamedArgs, newCounter1 =
                    List.fold (fun (lst, c) (typ, name) -> (typ,name + string c) :: lst, c+1) ([], counter) args 
                let newMap= addFunArgsToMap renamedArgs map
                let newBody,newCounter2, newTc = rStmt body 1 newMap newCounter1 tc
                aux xs (Fundec(rtyp,name,renamedArgs,newBody)::tree,newMap) newCounter2 newTc
    Prog (aux prog ([],Map.empty) 0 0)