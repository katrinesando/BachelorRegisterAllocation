module Utility
open Absyn
open System.Text.RegularExpressions
type flabel = string
type 'data env = (string * 'data) list
type var = 
    Glovar of int                   (* address relative to bottom of stack *)
  | Locvar of int  

type varEnv = (var * typ) env * int

(* The function environment maps function name to label and parameter decs *)

type paramdecs = (typ * string) list
type funEnv = (flabel * typ option * paramdecs) env

let rec lookup env x = 
    match env with 
    | []         -> failwith (x + " not found")
    | (y, v)::yr -> if x=y then v else lookup yr x

let rec lookupInMap depth (name : string) m =
    let rex = Regex (name+"[0-9]+",RegexOptions.Compiled)
    if depth >= 0 then
        match Map.tryFind depth m with
        | None -> lookupInMap (depth-1) name m
        | Some vars ->                
                let rec aux rest  = 
                    match rest with
                    |[] ->  lookupInMap (depth-1) name m 
                    |(n:string)::xs -> if rex.IsMatch n then n else aux xs
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
