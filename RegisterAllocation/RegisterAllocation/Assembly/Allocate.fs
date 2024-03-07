module Allocate

open Absyn
open DecorAbsyn
open MapUtility
type reg64 =
    | Rax | Rcx | Rdx | Rbx | Rsi | Rdi | Rsp | Rbp | R8 | R9 | R10 | R11 | R12 | R13 | R14| R15 
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


(* Simple environment operations *)

type 'data env = (string * 'data) list

let rec lookup env x = 
    match env with 
    | []         -> failwith (x + " not found")
    | (y, v)::yr -> if x=y then v else lookup yr x
type var = 
    Glovar of int                   (* address relative to bottom of stack *)
  | Locvar of int                   (* address relative to bottom of frame *)

(* The variable environment keeps track of global and local variables, and 
   keeps track of next available offset for local variables *)
type flabel = string
type varEnv = (var * typ) env * int

(* The function environment maps function name to label and parameter decs *)

type paramdecs = (typ * string) list
type funEnv = (flabel * typ option * paramdecs) env
    
let expandEnv kind (typ, x) (env,depth) =
    match typ with
    | TypA(TypA _, _) -> raise (Failure "expandEnv: array of arrays not permitted")
    | TypA(_, Some i) -> ((x, (kind (depth+i), typ)) :: env, depth+i+1)
    | _ -> ((x, (kind depth, typ)) :: env, depth+1)

let makeGlobalEnvs (topdecs : topdec list) : varEnv * funEnv * Map<int, string list> = 
    let rec addv decs varEnv funEnv map = 
        match decs with 
        | []         -> (varEnv, funEnv, map)
        | dec::decr  -> 
          match dec with
          | Vardec (typ, var) ->
            let varEnv1         = expandEnv Glovar (typ, var) varEnv
            let newmap = addToMap (snd varEnv1) var map
            let (varEnvr, funEnvr, m) = addv decr varEnv1 funEnv newmap
            (varEnvr, funEnvr, m)
          | Fundec (tyOpt, f, xs, body) ->
            addv decr varEnv ((f, ("_" + f, tyOpt, xs)) :: funEnv) map
    addv topdecs ([], 0) [] Map.empty

let bindParam (env, fdepth) (typ, x)  : varEnv = 
    ((x, (Locvar fdepth, typ)) :: env , fdepth+1)

let bindParams paras ((env, fdepth) : varEnv) : varEnv = 
    List.fold bindParam (env, fdepth) paras;
let rec aStmt stmt (env, depth as varEnv) funEnv map : dstmt<'a> =
    match stmt with
    | If(e, stmt1, stmt2) ->
        let ex = aExpr e varEnv funEnv map 
        let thenStmt = aStmt stmt1 (env, depth+1) funEnv map
        let elseStmt = aStmt stmt2 (env, depth+1) funEnv map
        DIf(ex, thenStmt, elseStmt, ())
    | While(e, body) ->failwith "not implemented"
    | Expr e -> failwith "not implemented"
    | Block stmts -> failwith "not implemented"
    | Return None ->failwith "not implemented"
    | Return (Some e) -> failwith "not implemented"
  
and aStmtOrDec stmtOrDec varEnv funEnv map  =
    match stmtOrDec with 
    | Stmt stmt    -> (DStmt(aStmt stmt varEnv funEnv map,()), map)
    | Dec (typ, x) ->
        let newmap = addToMap (snd varEnv) x map
        (DDec(typ, x, ()), newmap)
    
and aExpr (e : expr) (varEnv : varEnv) (funEnv : funEnv) map = 
    match e with
    | Access acc     ->failwith "not implemented"
    | Assign(acc, e) -> failwith "not implemented"
    | CstI i         -> failwith "not implemented"
    | Prim1(ope, e)  ->        failwith "not implemented"
    | Prim2 (ope, e1, e2) ->failwith "not implemented"
    | Andalso(e1,e2)   ->failwith "not implemented"
    | Orelse(e1, e2) ->failwith "not implemented"
    | Call(name, lst) ->failwith "not implemented"
and aAccess access varEnv funEnv map  =
  match access with
  | AccVar x            ->failwith "not implemented"
  | AccDeref e          ->failwith "not implemented"
  | AccIndex (acc, idx) ->failwith "not implemented"


let livenessAnotator prog =
    let ((varEnv,_),funEnv, m) = makeGlobalEnvs prog 
    let rec aux res (dtree as acc) =
        match res with
        | [] -> List.rev dtree
        | x :: xs ->
            match x with
            | Vardec(t, name) ->
                aux xs (DVardec(t,name,()) :: dtree)
            | Fundec(rtyp, name, args, body) ->
                let (_,_,paras) = lookup funEnv name
                let locEnv = bindParams paras (varEnv,0)
                let decoratedBody = aStmt body locEnv funEnv m
                aux xs (DFundec(rtyp,name,args,decoratedBody, ())::dtree)
    aux prog []


