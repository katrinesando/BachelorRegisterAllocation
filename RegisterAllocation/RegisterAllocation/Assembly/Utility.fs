module Utility
open Absyn

let mem x xs = List.exists (fun y -> x=y) xs
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

let temporaries =
    [Rcx; Rdx]// ;Rbx; Rsi; Rdi; R8; R9; R10; R11; R12; R13; R14; R15] 

type flabel = string
type 'data env = (string * 'data) list
type var = 
    Glovar of int                   (* address relative to bottom of stack *)
  | Locvar of int  

type varEnv = (var * typ) env * int

(* The function environment maps function name to label and parameter decs *)

type paramdecs = (typ * string) list
type funEnv = (flabel * typ option * paramdecs) env

let removeFromList lst elem =
     List.filter (fun n -> n<>elem) lst
let rec lookup env x = 
    match env with 
    | []         -> failwith (x + " not found")
    | (y, v)::yr -> if x=y then v else lookup yr x

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
   
let addToMap depth name m =
    match Map.tryFind depth m with
    |None -> Map.add depth [name] m
    |Some vars ->
        let newlst = name::vars
        Map.add depth newlst m
 
(* Bind declared parameters in env: *)       
let bindParam (env, fdepth) (typ, x)  : varEnv = 
    ((x, (Locvar fdepth, typ)) :: env , fdepth+1)

let bindParams paras ((env, fdepth) : varEnv) : varEnv = 
    List.fold bindParam (env, fdepth) paras
    
let getUnusedRegister graph lst =
    let toExclude = List.fold (fun acc node ->
                       match Map.tryFind node graph with
                       | None -> acc
                       | Some col -> col :: acc) [] lst 
    let l = List.except toExclude temporaries
    if List.length l <> 0 then Some (List.head l) else None
