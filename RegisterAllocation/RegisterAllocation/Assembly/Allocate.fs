module Allocate

open Absyn
open DecorAbsyn
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

let rec lookupInMap depth name m=
    if depth >= 0 then
        match Map.tryFind depth m with
        | None -> lookupInMap (depth-1) name m
        | Some (n,_,_) as v -> if n = name then v else lookupInMap (depth-1) name m 
    else
        failwith ("variable " + name + " not declared")
    
let expandEnv kind (typ, x) (env,depth) =
    match typ with
    | TypA(TypA _, _) -> raise (Failure "expandEnv: array of arrays not permitted")
    | TypA(_, Some i) -> ((x, (kind (depth+i), typ)) :: env, depth+i+1)
    | _ -> ((x, (kind depth, typ)) :: env, depth+1)

let makeGlobalEnvs (topdecs : topdec list) : varEnv * funEnv = 
    let rec addv decs varEnv funEnv = 
        match decs with 
        | []         -> (varEnv, funEnv)
        | dec::decr  -> 
          match dec with
          | Vardec (typ, var) ->
            let varEnv1         = expandEnv Glovar (typ, var) varEnv
            let (varEnvr, funEnvr) = addv decr varEnv1 funEnv
            (varEnvr, funEnvr)
          | Fundec (tyOpt, f, xs, body) ->
            addv decr varEnv ((f, ("_" + f, tyOpt, xs)) :: funEnv)
    addv topdecs ([], 0) []

let bindParam (env, fdepth) (typ, x)  : varEnv = 
    ((x, (Locvar fdepth, typ)) :: env , fdepth+1)

let bindParams paras ((env, fdepth) : varEnv) : varEnv = 
    List.fold bindParam (env, fdepth) paras;
let rec aStmt stmt varEnv funEnv = failwith ("not implemented")

and aStmtOrDec stmtOrDec varEnv funEnv  = failwith "not implemented"

let livenessAnotator prog =
    let ((varEnv,_),funEnv) = makeGlobalEnvs prog 
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
                let decoratedBody = aStmt body locEnv funEnv
                aux xs (DFundec(rtyp,name,args,decoratedBody)::dtree)
    aux prog []


