module DecorAbsyn

open Microsoft.VisualBasic

(* File MicroC/Absyn.fs
   Abstract syntax of micro-C, an imperative language.
   sestoft@itu.dk 2009-09-25

   Must precede Interp.fs, Comp.fs and Contcomp.fs in Solution Explorer
 *)
open Absyn

type dexpr<'info> =                                                         
  | DAccess of daccess<'info> * 'info                (* x    or  *p    or  a[e]     *)
  | DAssign of daccess<'info> * dexpr<'info> * 'info         (* x=e  or  *p=e  or  a[e]=e   *)
  | DAddr of daccess<'info> * 'info                  (* &x   or  &*p   or  &a[e]    *)
  | DCstI of int * 'info                     (* Constant                    *)
  | DPrim1 of string * dexpr<'info> * 'info         (* Unary primitive operator    *)
  | DPrim2 of string * dexpr<'info> * dexpr<'info> * 'info  (* Binary primitive operator   *)
  | DAndalso of dexpr<'info>  * dexpr<'info> * 'info      (* Sequential and              *)
  | DOrelse of dexpr<'info>  * dexpr<'info> * 'info          (* Sequential or               *)
  | DCall of string * dexpr<'info>  list * 'info     (* Function call f(...)        *)                                                                
and daccess<'info> =                                                       
  | DAccVar of string * 'info           (* Variable access        x    *) 
  | DAccDeref of dexpr<'info>                  (* Pointer dereferencing  *p   *)
  | DAccIndex of daccess<'info> * dexpr<'info> * 'info       (* Array indexing         a[e] *)
and dstmt<'info> =                                                     
  | DIf of expr * dstmt<'info> * dstmt<'info> * 'info           (* Conditional                 *)
  | DWhile of expr * dstmt<'info> * 'info                (* While loop                  *)
  | DExpr of expr * 'info                        (* Expression statement   e;   *)
  | DReturn of expr option * 'info               (* Return from method          *)
  | DBlock of stmtordec<'info> list * 'info            (* Block: grouping and scope   *)
                                                                   
and stmtordec<'info> =                                                    
  | DDec of typ * string * 'info           (* Local variable declaration  *)
  | DStmt of dstmt<'info> * 'info                       (* A statement                 *)

and topdec<'info> = 
  | DFundec of typ option * string * (typ * string) list * dstmt<'info> * 'info   
  | DVardec of typ * string * 'info

and program<'info> = 
  | DProg of topdec<'info> list
