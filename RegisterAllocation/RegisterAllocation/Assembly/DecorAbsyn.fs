module DecorAbsyn

open Microsoft.VisualBasic

(* File MicroC/Absyn.fs
   Abstract syntax of micro-C, an imperative language.
   sestoft@itu.dk 2009-09-25

   Must precede Interp.fs, Comp.fs and Contcomp.fs in Solution Explorer
 *)
open Absyn

type dstmt<'info> = ddstmt<'info> * 'info
                                                                  
and ddstmt<'info> =                                                         
  | DIf of expr * dstmt<'info> * dstmt<'info>        (* Conditional                 *)
  | DWhile of expr * dstmt<'info>             (* While loop                  *)
  | DExpr of expr                     (* Expression statement   e;   *)
  | DReturn of expr option            (* Return from method          *)
  | DBlock of stmtordec<'info> list          (* Block: grouping and scope   *)
                                                                   
and stmtordec<'info> =                                                    
  | DDec of typ * string * 'info             (* Local variable declaration  *)
  | DStmt of dstmt<'info>                     (* A statement                 *)

and topdec<'info> = 
  | DFundec of typ option * string * (typ * string) list * dstmt<'info>
  | DVardec of typ * string * 'info

and program<'info> = 
  | DProg of topdec<'info> list
