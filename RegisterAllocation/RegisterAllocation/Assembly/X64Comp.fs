﻿module X64Comp
(* File Assembly/X86Comp.sml

   Micro-C compiler that generate an x86 assembler-oriented bytecode.
   Based on Niels Kokholm's SML version (March 2002) and
   MicroC/Comp.fs

   sestoft@itu.dk * 2017-05-01

   Differences from MicroC/Comp.fs:

    * Uses X86.fs for code emission instead of Machine.fs.

    * The label of a function entry point is of type flabel instead of
      label. This changes type funEnv. The label for function "fname"
      is "_fname" instead of a label created by newLabel(). Also a
      change in function cProgram.

    * Some changes in compileToFile to enable insertion of a standard
      assembler file header and headers for the functions init and
      main.

    * The argc is added to the return type of cProgram so that
      compileToFile can insert code to check the number of
      arguments. This eliminates one source of mysterious crashes.

    The created assembly file can be translated (by nasm) to a .o or
    .obj file defining two entry points: init and main. This file can
    be linked together with the compiled driver.o to a complete
    executable file.  This has been tested 2016-12-12 with gcc on
    MacOS and Linux, and should work on Windows also, provided one has
    the Visual Studio C linker cl.

    For a general description of the compiler, see chapter 14 of
    Programming Language Concepts, second edition, 2017.
*)

open System.IO
open Absyn
open DecorAbsyn
open X64
open Allocate
open Utility

(* ------------------------------------------------------------------- *)

let allocate (kind : int -> var) (typ, x) (varEnv : varEnv) : varEnv * x86 list =
    let (env, fdepth) = varEnv 
    match typ with
    | TypA (TypA _, _) -> 
      raise (Failure "allocate: array of arrays not permitted")
    | TypA (t, Some i) -> 
      let newEnv = ((x, (kind (fdepth+i), typ)) :: env, fdepth+i+1)
      //let labtest = newLabel()
      //let labbegin = newLabel()
      let code = [Ins("mov rax, rsp");
                  Ins("sub rax, 8"); //4 originalt - this means the array can only hold ints
                  Ins2("sub", Reg Rsp, Cst (8*i));
                  Ins1("push", Reg Rax)]
      (newEnv, code) 
    | _ -> 
      let newEnv = ((x, (kind fdepth, typ)) :: env, fdepth+1)
      let code = [Ins "sub rsp, 8"] //4 originalt
      (newEnv, code)



(* ------------------------------------------------------------------- *)

(* Global environments for variables and functions *)

let makeGlobalEnvs (topdecs) : varEnv * funEnv * x86 list = 
    let rec addv decs varEnv funEnv = 
        match decs with 
        | []         -> (varEnv, funEnv, [])
        | dec::decr  -> 
          match dec with
          | DVardec (typ, var,info) ->
            let (varEnv1, code1)          = allocate Glovar (typ, var) varEnv
            let (varEnvr, funEnvr, coder) = addv decr varEnv1 funEnv
            (varEnvr, funEnvr, code1 @ coder)
          | DFundec (tyOpt, f, xs, body,info) ->
            addv decr varEnv ((f, ("_" + f, tyOpt, xs)) :: funEnv)
    addv topdecs ([], 0) []

(* ------------------------------------------------------------------- *)

(* Compiling micro-C statements *)
let rec cStmt stmt (varEnv : varEnv) (funEnv : funEnv) : x86 list = 
    match stmt with
    | DIf(e, stmt1, stmt2,info) -> 
      let labelse = newLabel()
      let labend  = newLabel()
      cExpr e varEnv funEnv Rbx []
      @ [Ins2("cmp", Reg Rbx, Cst 0);
         Jump("jz", labelse)] 
      @ cStmt stmt1 varEnv funEnv
      @ [Jump("jmp", labend)]
      @ [Label labelse] @ cStmt stmt2 varEnv funEnv
      @ [Label labend]           
    | DWhile(e, body,info) ->
      let labbegin = newLabel()
      let labtest  = newLabel()
      [Jump("jmp", labtest);
       Label labbegin] @ cStmt body varEnv funEnv
      @ [Label labtest] @ cExpr e varEnv funEnv Rbx []
      @ [Ins2("cmp", Reg Rbx, Cst 0);
         Jump("jnz", labbegin)]
    | DExpr(e,info) -> 
      cExpr e varEnv funEnv Rbx []
    | DBlock(stmts,info) -> 
      let rec loop stmts varEnv =
          match stmts with 
          | []     -> (snd varEnv, [])
          | s1::sr -> 
            let (varEnv1, code1) = cStmtOrDec s1 varEnv funEnv
            let (fdepthr, coder) = loop sr varEnv1 
            (fdepthr, code1 @ coder)
      let (fdepthend, code) = loop stmts varEnv
      code @ [Ins2("sub", Reg Rsp, Cst (8 * (snd varEnv - fdepthend)))]      // was 4
    | DReturn(None,info) ->
        [Ins2("add", Reg Rsp, Cst (8 * snd varEnv)); //was 4
         Ins("pop rbp");
         Ins("ret")]
    | DReturn(Some e,info) -> 
    cExpr e varEnv funEnv Rbx [] 
    @ [Ins2("add", Reg Rsp, Cst (8 * snd varEnv)); //was 4 - never 4 in RSP
       Ins("pop rbp");
       Ins("ret")]


and cStmtOrDec stmtOrDec (varEnv : varEnv) (funEnv : funEnv) : varEnv * x86 list = 
    match stmtOrDec with 
    | DStmt (stmt,info)    -> (varEnv, cStmt stmt varEnv funEnv) 
    | DDec (typ, x,info) -> allocate Locvar (typ, x) varEnv

(* Compiling micro-C expressions: 

   * e       is the expression to compile
   * varEnv  is the local and gloval variable environment 
   * funEnv  is the global function environment
   * tr      is the x86 register in which the result should be computed
   * pres    is a list of registers that must be preserved during the computation
   
   Net effect principle: if the compilation (cExpr e varEnv funEnv tr pres) of
   expression e returns the instruction sequence instrs, then the
   execution of instrs will leave the rvalue of expression e in register tr,
   leave the registers in pres unchanged, and leave the stack depth unchanged.
*)

and cExpr (e : expr) (varEnv : varEnv) (funEnv : funEnv) (tr : reg64) (pres : reg64 list) : x86 list = 
    match e with
    | Access acc     ->
        cAccess acc varEnv funEnv tr pres @ [Ins2("mov", Reg tr, Ind tr)] 
    | Assign(acc, e) ->
        let tr' = getTempFor (tr :: pres) 
        in cAccess acc varEnv funEnv tr' (tr :: pres)
           @ cExpr e varEnv funEnv tr (tr' :: pres)
           @ [Ins2("mov", Ind tr', Reg tr)]
    | CstI i         ->
        [Ins2("mov", Reg tr, Cst i)]
    | Addr acc       ->
        cAccess acc varEnv funEnv tr pres
    | Prim1(ope, e1) ->
        cExpr e1 varEnv funEnv tr pres
        @ (match ope with
           | "!"      -> [Ins("xor rax, rax");
                          Ins2("cmp", Reg tr, Reg Rax);
                          Ins("sete al");
                          Ins2("mov", Reg tr, Reg Rax)]
           | "printi" -> [Ins2("mov",Reg Rdi, Reg tr);PRINTI]
           | "printc" -> [Ins2("mov",Reg Rdi, Reg tr);PRINTC]
           | _        -> raise (Failure "unknown primitive 1"))
    | Prim2(ope, e1, e2) ->
        let avoid = if ope = "/" || ope = "%" then [Rdx; tr] else [tr]
        in
        cExpr e1 varEnv funEnv tr pres
        @ let tr' = getTempFor (avoid @ pres)
          in cExpr e2 varEnv funEnv tr' (tr :: pres)
             @ match ope with
               | "+"   -> [Ins2("add", Reg tr, Reg tr')]
               | "-"   -> [Ins2("sub", Reg tr, Reg tr')]
               | "*"   -> [Ins2("mov", Reg Rax, Reg tr)]
                          @ preserve Rdx (tr :: pres)
                            [Ins1("imul", Reg tr')] // Invalidates Rdx
                          @ [Ins2("mov", Reg tr, Reg Rax)]
               | "/"   -> [Ins2("mov", Reg Rax, Reg tr)]
                          @ preserve Rdx (tr :: pres) 
                            [Ins("cdq");            // Invalidates Rdx
                             Ins1("idiv", Reg tr')] // Invalidates Rax Rdx
                          @ [Ins2("mov", Reg tr, Reg Rax)]
               | "%"   -> [Ins2("mov", Reg Rax, Reg tr)]
                          @ preserve Rdx (tr :: pres) 
                            [Ins("cdq");            // Invalidates Rdx
                             Ins1("idiv", Reg tr'); // Invalidates Rax Rdx
                             Ins2("mov", Reg tr, Reg Rdx)] 
               | "==" | "!=" | "<" | ">=" | ">" | "<="
                  -> let setcompbits = (match ope with
                                        | "==" -> "sete al"
                                        | "!=" -> "setne al"
                                        | "<"  -> "setl al"
                                        | ">=" -> "setge al"
                                        | ">"  -> "setg al"
                                        | "<=" -> "setle al"
                                        | _    -> failwith "internal error")
                     [Ins("xor rax, rax");
                      Ins2("cmp", Reg tr, Reg tr');
                      Ins(setcompbits);
                      Ins2("mov", Reg tr, Reg Rax)]
               | _     -> raise (Failure "unknown primitive 2")
    | Andalso(e1, e2) ->
        let labend = newLabel()
        cExpr e1 varEnv funEnv tr pres
        @ [Ins2("cmp", Reg tr, Cst 0);
           Jump("jz", labend)]
        @ cExpr e2 varEnv funEnv tr pres
        @ [Label labend] 
    | Orelse(e1, e2) -> 
        let labend = newLabel()
        cExpr e1 varEnv funEnv tr pres
        @ [Ins2("cmp", Reg tr, Cst 0);
           Jump("jnz", labend)]
        @ cExpr e2 varEnv funEnv tr pres
        @ [Label labend]            
    | Call(f, es) -> callfun f es varEnv funEnv tr pres

(* Generate code to access variable, dereference pointer or index array: *)
//pres = registers currently in use
and cAccess access varEnv funEnv (tr : reg64) (pres : reg64 list) : x86 list =
    match access with 
    | AccVar x ->
      match lookup (fst varEnv) x with
      | Glovar addr, _ -> [Ins2("mov", Reg tr, Glovars);
                           Ins2("sub", Reg tr, Cst (8*addr))]
      | Locvar addr, _ -> [Ins2("lea", Reg tr, RbpOff (8*addr))]
    | AccDeref e ->
        match e with
        | Prim2(ope, e1, e2) -> //pointer arithmetic
            cExpr e1 varEnv funEnv tr pres @
            let tr' = getTempFor (tr::pres) 
            in cExpr e2 varEnv funEnv tr' (tr :: pres) @
            match ope with //+/- need to be flipped due to how the stack grow towards lower addresses
            | "+" -> [Ins2("sal", Reg tr', Cst 3);Ins2("sub", Reg tr, Reg tr')]
            | "-" -> [Ins2("sal", Reg tr', Cst 3);Ins2("add", Reg tr, Reg tr')]
            | _   -> raise (Failure (ope + " operator not allowed when dereferencing"))
        | _ -> cExpr e varEnv funEnv tr pres
    | AccIndex(acc, idx) ->
      cAccess acc varEnv funEnv tr pres
      @ [Ins2("mov", Reg tr, Ind tr)]
      @ let tr' = getTempFor (tr :: pres) 
        in cExpr idx varEnv funEnv tr' (tr :: pres)
           @ [Ins2("sal", Reg tr', Cst 3);
              Ins2("sub", Reg tr, Reg tr')]

(* Generate code to evaluate a list es of expressions: *)

and cExprs es varEnv funEnv tr : x86 list = 
    List.concat(List.map (fun e -> cExpr e varEnv funEnv tr [] @ [Ins1("push", Reg tr)]) es)

(* Generate code to evaluate arguments es and then call function f: *)

and callfun f es varEnv funEnv tr pres : x86 list =
    let (labf, tyOpt, paramdecs) = lookup funEnv f
    let argc = List.length es
    if argc = List.length paramdecs then
        preserveAll pres (cExprs es varEnv funEnv tr
                          @ [Ins("push rbp");
                             Jump("call", labf);
                             Ins2("mov", Reg tr, Reg Rbx)])
    else
        raise (Failure (f + ": parameter/argument mismatch"))

(* Compile a complete micro-C program: globals, call to main, functions *)

let cProgram (DProg topdecs) : x86 list * int * x86 list * x86 list = 
    let _ = resetLabels ()
    let ((globalVarEnv, _), funEnv, globalInit) = makeGlobalEnvs topdecs
    let compilefun (tyOpt, f, xs, body) =
        let (labf, _, paras) = lookup funEnv f
        let (envf, fdepthf) = bindParams paras (globalVarEnv, 0)
        let code = cStmt body (envf, fdepthf) funEnv
        let arity = List.length paras
        [FLabel (labf, arity)] @ code @ [Ins2("add", Reg Rsp, Cst (8*arity));
                                         Ins("pop rbp");
                                         Ins("ret")]
    let functions = 
        List.choose (function 
                         | DFundec (rTy, name, argTy, body,info) 
                                    -> Some (compilefun (rTy, name, argTy, body))
                         | DVardec _ -> None)
                    topdecs 
    let (mainlab, _, mainparams) = lookup funEnv "main"
    let argc = List.length mainparams
    (globalInit,
     argc, 
     [Ins("push rbp"); Jump("call", mainlab)],
     List.concat functions)

(* Compile a complete micro-C and write the resulting assembly code
   file fname; also, return the program as a list of instructions.  *)

let asmToFile (inss : string list) (fname : string) : unit = 
    File.WriteAllText(fname, String.concat "" (List.map string inss))

let compileToFile program fname = 
    let (globalinit, argc, maincall, functions) = cProgram program 
    let code = [stdheader;
                beforeinit argc]
               @ code2x86asm globalinit
               @ [pushargs]
               @ code2x86asm maincall
               @ [popargs]
               @ code2x86asm functions
    asmToFile code fname;
    functions 

(* Example programs are found in the files ex1.c, ex2.c, etc *)

