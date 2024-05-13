module DecorAbsyn
(* File Assembly/DecorAbsyn.fs
   Decorated Abstract syntax of micro-C, an imperative language.
   sestoft@itu.dk 2009-09-25
   ahad@itu.dk, biha@itu.dk, and kmsa@itu.dk 2024-05-15
   Must precede Decorate.fs, Allocate.fs and X64Comp.fs in Solution Explorer
 *)
open Absyn


type dstmt<'info> =                                                     
  | DIf of expr * dstmt<'info> * dstmt<'info> * 'info           (* Conditional                 *)
  | DWhile of expr * dstmt<'info> * 'info                (* While loop                  *)
  | DExpr of expr * 'info                        (* Expression statement   e;   *)
  | DReturn of expr option * 'info               (* Return from method          *)
  | DBlock of dstmtordec<'info> list * 'info            (* Block: grouping and scope   *)
                                                                   
and dstmtordec<'info> =                                                    
  | DDec of typ * string * 'info           (* Local variable declaration  *)
  | DStmt of dstmt<'info> * 'info                       (* A statement                 *)

and topdec<'info> = 
  | DFundec of typ option * string * (typ * string) list * dstmt<'info> * 'info   
  | DVardec of typ * string * 'info

and program<'info> = 
  | DProg of topdec<'info> list
