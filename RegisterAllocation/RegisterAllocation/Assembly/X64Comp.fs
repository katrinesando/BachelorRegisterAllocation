module X64Comp
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

//Might run into problems with push and pop with 64-bit nasm (might be a bug that's fixed though)
let pushAndPop reg code = [Ins1("push", Reg reg)] @ code @ [Ins1("pop", Reg reg)]

(* Preserve reg across code, on the stack if necessary *)
let preserve reg live code graph = //TODO stress test with many live variables
    let inUse = List.fold (fun inUse elem ->
        if reg = Map.find elem graph then true else inUse) false live
    if inUse then
       pushAndPop reg code
    else
        code

(* Preserve all live registers around code, eg a function call *)
let rec preserveAll pres code graph =
    match pres with
    | []          -> code
    | name :: rest ->
        let reg = Map.find name graph
        preserveAll rest (pushAndPop reg code) graph

let allocate (kind : int -> var) (typ, x) (varEnv : varEnv) : varEnv * x86 list =
    let (env, fdepth) = varEnv 
    match typ with
    | TypA (TypA _, _) -> 
      raise (Failure "allocate: array of arrays not permitted")
    | TypA (t, Some i) -> 
      let newEnv = ((x, (kind (fdepth+i), typ)) :: env, fdepth+i+1)
      let code = [Ins("mov rax, rsp");
                  Ins("sub rax, 8"); //4 originalt - this means the array can only hold ints
                  Ins2("sub", Reg Rsp, Cst (8*i));
                  Ins1("push", Reg Rax)]
      (newEnv, code) 
    | _ -> 
      let newEnv = ((x, (kind fdepth, typ)) :: env, fdepth+1)
      let code = [Ins "sub rsp, 8"] //4 originalt
      (newEnv, code)
     
(* Get temporary register not used by a var in liveVars that isn't pres *)
let getTemp pres liveVars graph =
    List.fold (fun toEvict elem ->
        let used = Map.find elem graph
        if not (mem used [pres;Dummy;Spill]) then used else toEvict) Rdx liveVars


(* ------------------------------------------------------------------- *)

let evictAndRestore temp tr varEnv code=
    let evictCode = [Ins1("push", Reg tr)]
    let restoreCode =
        match lookup (fst varEnv) temp with
        | Glovar addr,_ -> [Ins1("push", Reg tr); Ins2("mov", Reg tr, Glovars);
                        Ins2("sub", Reg tr, Cst (8*addr)); Ins2 ("mov", Ind tr,Reg Rsp);
                        Ins1("pop", Reg tr); Ins1("pop", Reg tr)]
        | Locvar addr,_ -> [Ins2("mov", RbpOff(8*addr), Reg tr); Ins1("pop", Reg tr)]
    evictCode @ code @ restoreCode
    

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
let movToRetReg retReg curReg =
    if curReg <> retReg then [Ins2 ("mov", Reg retReg, Reg curReg)] else []

let prim1Code ope tr liveVars graph =
    match ope with
           | "!"      -> [Ins("xor rax, rax");
                          Ins2("cmp", Reg tr, Reg Rax);
                          Ins("sete al");
                          Ins2("mov", Reg tr, Reg Rax)]
           | "printi" -> preserve Rdi liveVars [Ins2("mov",Reg Rdi, Reg tr);PRINTI] graph
           | "printc" -> preserve Rdi liveVars [Ins2("mov",Reg Rdi, Reg tr);PRINTC] graph
           | _        -> raise (Failure "unknown primitive 1")
let prim2Code ope liveVars graph tr tr' =
    match ope with
               | "+"   -> [Ins2("add", Reg tr, Reg tr')]
               | "-"   -> [Ins2("sub", Reg tr, Reg tr')]
               | "*"   -> [Ins2("mov", Reg Rax, Reg tr)]
                          @ preserve Rdx liveVars [Ins1("imul", Reg tr')] graph
                          @ [Ins2("mov", Reg tr, Reg Rax)]
               | "/"   -> [Ins2("mov", Reg Rax, Reg tr)]
                          @ preserve Rdx liveVars [Ins("cdq"); Ins1("idiv", Reg tr')] graph
                          @ [Ins2("mov", Reg tr, Reg Rax)]
               | "%"   -> [Ins2("mov", Reg Rax, Reg tr)]
                          @ ([Ins("cdq"); Ins1("idiv", Reg tr');Ins2("mov", Reg tr, Reg Rdx)] |>
                          preserve Rdx liveVars <| graph)
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
     
let pointerArithmeticCode ope tr tr' =
    match ope with //+/- need to be flipped due to how the stack grow towards lower addresses
    | "+" -> [Ins2("sal", Reg tr', Cst 3);Ins2("sub", Reg tr, Reg tr')]
    | "-" -> [Ins2("sal", Reg tr', Cst 3);Ins2("add", Reg tr, Reg tr')]
    | _   -> raise (Failure (ope + " operator not allowed when dereferencing"))

let getAddrOfTemp name reg varEnv=
    match lookup (fst varEnv) name with
                | Locvar addr,_ -> [Ins2("lea", Reg reg, RbpOff (8*addr))]
                | _ -> failwith "a temporary should not be a Glovar"
let putValInAddrOfTemp name reg varEnv =
    match lookup (fst varEnv) name with
                | Locvar addr,_ -> [Ins2("mov", RbpOff (8*addr), Reg reg)]
                | _ -> failwith "a temporary should not be a Glovar"
let getAddrOfVarInReg tr reg graph liveVars env =
    let name = List.fold(fun acc elem ->
            if Map.find elem graph = tr then elem else acc) "" liveVars
    match lookup (fst env) name with
    | Locvar addr,_ -> [Ins2("lea", Reg reg, RbpOff (8*addr))]
    | Glovar addr, _ -> [Ins2("mov", Reg reg, Glovars);Ins2("sub", Reg reg, Cst (8*addr))]

(* Compiling micro-C statements *)
let rec cStmt stmt (varEnv : varEnv) (funEnv : funEnv) graph : x86 list =
    match stmt with
    | DIf(e, stmt1, stmt2,info) ->
        let labelse = newLabel()
        let labend  = newLabel()
        let ifCode env =
                    [Jump("jz", labelse)] 
                    @ cStmt stmt1 env funEnv graph @ [Jump("jmp", labend)]
                    @ [Label labelse] @ cStmt stmt2 env funEnv graph
                    @ [Label labend]
        match e with
        | Temp(n, _) ->
            match Map.find n graph with
            | Spill ->
                let tempReg = getTemp Dummy info graph //no reg needs to be preserved
                let eCode,env1 = cExpr e varEnv funEnv tempReg info graph
                eCode @ evictAndRestore n tempReg env1 (getAddrOfTemp n tempReg env1 @ [Ins2("cmp", Reg tempReg, Cst 0)])
                @ ifCode env1
            | r ->
                let eCode,env1 = cExpr e varEnv funEnv r info graph
                eCode @ [Ins2("cmp", Reg r, Cst 0)] @ ifCode env1
        | _ -> failwith "condition not in temp in If"
    | DWhile(e, body,info) ->
        let labbegin = newLabel()
        let labcondition  = newLabel()
        let loopCode env = [Jump("jmp", labcondition);Label labbegin]
                           @ cStmt body env funEnv graph
                           @ [Label labcondition] 
        match e with
        | Temp(n,_) ->
            match Map.find n graph with
            | Spill ->
                let tempReg = getTemp Dummy info graph
                let code,env = cExpr e varEnv funEnv tempReg info graph
                loopCode env @ code @ evictAndRestore n tempReg env (getAddrOfTemp n tempReg env
                         @ [Ins2("cmp", Reg tempReg, Cst 0)])  @ [Jump("jnz", labbegin)]
            | r ->
                 let code,env = cExpr e varEnv funEnv r info graph
                 loopCode env @ code @ [Ins2("cmp", Reg r, Cst 0);Jump("jnz", labbegin)]
        | _ -> failwith "condition not in temp in While"
    | DExpr(e,info) ->
        match e with
        | Temp(n,_) ->
            match Map.find n graph with
            | Spill ->
                let tempReg = getTemp Dummy info graph
                let code, env = cExpr e varEnv funEnv tempReg info graph
                evictAndRestore n tempReg env code
            | r -> cExpr e varEnv funEnv r info graph |> fst
        | _ -> failwith "condition not in temp in Expr" 
    | DBlock(stmts,info) -> 
        let rec loop stmts varEnv =
            match stmts with 
            | []     -> (snd varEnv, [])
            | s1::sr -> 
              let (varEnv1, code1) = cStmtOrDec s1 varEnv funEnv graph
              let (fdepthr, coder) = loop sr varEnv1 
              (fdepthr, code1 @ coder)
        let (fdepthend, code) = loop stmts varEnv
        code @ [Ins2("sub", Reg Rsp, Cst (8 * (snd varEnv - fdepthend)))] //Which varEnv that is given might fuck something up, since temp now also are in varEnv
    | DReturn(None,info) ->
        [Ins2("add", Reg Rsp, Cst (8 * snd varEnv)); 
         Ins("pop rbp");
         Ins("ret")]
    | DReturn(Some e,info) ->  //Returns need to be in specific register every time
        let code,env = cExpr e varEnv funEnv Rbx info graph
        code @ [Ins2("add", Reg Rsp, Cst (8 * snd env)); 
           Ins("pop rbp");
           Ins("ret")]


and cStmtOrDec stmtOrDec (varEnv : varEnv) (funEnv : funEnv) graph : varEnv * x86 list = 
    match stmtOrDec with 
    | DStmt (stmt,_)    -> (varEnv, cStmt stmt varEnv funEnv graph) 
    | DDec (typ, x,_) -> allocate Locvar (typ, x) varEnv

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

and cExpr (e : expr) (varEnv : varEnv) (funEnv : funEnv) (reg : reg64) liveVars graph : x86 list * varEnv = 
    match e with
    | Access acc     ->
        let code,newEnv, tr = cAccess acc varEnv funEnv reg liveVars graph
        match code with
        | [] -> movToRetReg reg tr,newEnv
        | _ ->
            match acc with
            | AccIndex _ | AccVar _-> code @ [Ins2("mov", Reg tr, Ind tr)] @ movToRetReg reg tr,newEnv 
            | _ -> code @ movToRetReg reg tr,newEnv 
    | Assign(acc, e) -> //TODO figure out how this works when acc is not spilled vs when it is
        let accCode,env1, tr' = cAccess acc varEnv funEnv reg liveVars graph
        match e with
        | Temp(n, _) ->
            match Map.find n graph with
            | Spill -> 
                let (eCode,env2), tempReg = 
                    if reg <> tr' then cExpr e env1 funEnv reg liveVars graph, reg
                    else
                        let tempReg = getTemp tr' liveVars graph
                        cExpr e env1 funEnv tempReg liveVars graph, tempReg
                match accCode with
                | [] -> 
                    let code = getAddrOfTemp n tempReg env2 @ [Ins2("mov", Reg tr', Reg tempReg)] //tr' is the register returned from cAccess
                    let addrCode = getAddrOfVarInReg tr' tempReg graph liveVars env2
                    accCode @
                    evictAndRestore n tempReg env2 (eCode @ [Ins1("push", Reg tempReg)] @ addrCode @[Ins1("pop", Reg tr');Ins2("mov", Ind tempReg, Reg tr')]@ code)
                    @ movToRetReg reg tr', env2
                | _  ->
                    let code = getAddrOfTemp n tempReg env2 @ [Ins2("mov", Ind tr', Reg tempReg)] //tr' is the register returned from cAccess
                    accCode @ evictAndRestore n tempReg env2 (eCode @ code) @ movToRetReg reg tr', env2
            | r ->
                let eCode, env2 = cExpr e env1 funEnv reg liveVars graph
                match accCode with //If empty list, accCode register contains values
                | [] ->
                    let addrCode = getAddrOfVarInReg tr' r graph liveVars env2
                    eCode@ [Ins1("push", Reg r)] @ addrCode @ [Ins1("pop", Reg tr');Ins2("mov", Ind r, Reg tr')]  @ movToRetReg reg tr',env2
                | _  -> accCode @ eCode @ [Ins2("mov", Ind tr', Reg r)]  @ movToRetReg reg tr',env2                
        | _ -> failwith "wrong absyn in Assign"
    | CstI i         ->
        [Ins2("mov", Reg reg, Cst i)],varEnv
    | Addr acc       ->
        let code, env, tr = cAccess acc varEnv funEnv reg liveVars graph
        match code with
        | [] -> getAddrOfVarInReg tr reg graph liveVars env, env
        | _  -> code @ movToRetReg reg tr, env
    | Prim1(ope, e1) ->
        let eCode, env1 = cExpr e1 varEnv funEnv reg liveVars graph           
        match e1 with
        | Temp(n,_)->
            match Map.find n graph with
            | Spill ->
                eCode @ getAddrOfTemp n reg env1 @ prim1Code ope reg liveVars graph, env1
            | r ->
                eCode @ prim1Code ope r liveVars graph
                        @ movToRetReg reg r, env1
        | _ -> failwith "wrong abstract syntax in Prim1"
    | Prim2(ope, e1, e2) ->
        let avoid = if ope = "/" || ope = "%" then [Rdx; reg] else [reg]
        let e1Code,env1 = cExpr e1 varEnv funEnv reg liveVars graph
        let e2Code,env2 = cExpr e2 env1 funEnv reg liveVars graph
        let exprCodes = e1Code @ e2Code 
        match e1,e2 with
        | Temp(n1,_),Temp(n2,_) ->
            match Map.find n1 graph, Map.find n2 graph with
            | Spill,Spill->
                let tempReg2 = getTemp reg liveVars graph
                let code =  getAddrOfTemp n1 reg env2 @ getAddrOfTemp n2 tempReg2 env2
                            @ prim2Code ope liveVars graph reg tempReg2
                exprCodes @ evictAndRestore n2 tempReg2 env2 code,env2
            | Spill,r->
                let code = getAddrOfTemp n1 reg env2 @ prim2Code ope liveVars graph reg r
                exprCodes @ code, env2
            | r, Spill-> 
                let code = getAddrOfTemp n2 reg env2 @ prim2Code ope liveVars graph r reg
                exprCodes @ code @ [Ins2("mov",Reg reg, Reg r)],env2
            | r1,r2 ->
                exprCodes @ prim2Code ope liveVars graph r1 r2
                @ movToRetReg reg r1,env2
        | _ -> failwith "wrong abstract syntax in Prim2"
    | Andalso(e1, e2) ->
        //e2 should also be saved in tr
        let labend = newLabel()
        let e1Code, env1 = cExpr e1 varEnv funEnv reg liveVars graph
        let e2Code, env2 = cExpr e2 env1 funEnv reg liveVars graph
        match e1,e2 with
        | Temp(n1, _),Temp(n2, _) ->
            match Map.find n1 graph, Map.find n2 graph with
            | Spill, Spill ->
                let code1 = getAddrOfTemp n1 reg env2
                let code2 = getAddrOfTemp n2 reg env2
                let retCode = e1Code @ code1 @ [Ins2("cmp", Reg reg, Cst 0);Jump("jz", labend)]
                                                   @ e2Code @ code2 @ [Label labend]               
                retCode,env2
            | r, Spill ->
                let code1 = getAddrOfTemp n1 r env2
                let retCode = e1Code @ code1 @ [Ins2("cmp", Reg r, Cst 0);Jump("jz", labend)]
                                     @ e2Code @ [Label labend] @ movToRetReg reg r           
                retCode,env2
            | Spill, r ->
                let code2 = getAddrOfTemp n2 r env2
                let retCode = e1Code @ [Ins2("cmp", Reg r, Cst 0);Jump("jz", labend)]
                                     @ e2Code @ code2 @ [Label labend] @ movToRetReg reg r  
                retCode, env2
            | r1,r2 ->
                e1Code @ [Ins2("cmp", Reg r1, Cst 0);Jump("jz", labend)]
                     @ e2Code @ [Label labend] @ movToRetReg reg r2 ,env2
        | _ -> failwith "wrong abstract syntax in Andalso"        
    | Orelse(e1,e2) ->
        let labend = newLabel()
        let e1Code, env1 = cExpr e1 varEnv funEnv reg liveVars graph
        let e2Code, env2 = cExpr e2 env1 funEnv reg liveVars graph 
        match e1,e2 with
        | Temp(n1, _),Temp(n2, _) ->
            match Map.find n1 graph, Map.find n2 graph with
            | Spill, Spill ->
                let code1 = getAddrOfTemp n1 reg env2
                let code2 = getAddrOfTemp n2 reg env2
                let retCode = e1Code @ code1 @ [Ins2("cmp", Reg reg, Cst 0);Jump("jnz", labend)]
                                                   @ e2Code @ code2 @ [Label labend]               
                retCode, env2
            | r, Spill -> //TODO make sure the correct side of || is moved into reg
                let code2 = getAddrOfTemp n2 r env2
                let retCode = e1Code @ [Ins2("cmp", Reg r, Cst 0);Jump("jnz", labend)]
                                     @ e2Code @ code2 @ [Label labend] @ movToRetReg reg r
                retCode, env2
            | Spill, r ->
                let code1 = getAddrOfTemp n1 r env2
                let retCode = e1Code @ code1 @ [Ins2("cmp", Reg r, Cst 0);Jump("jnz", labend)]
                                 @ e2Code @ [Label labend] @ movToRetReg reg r   
                retCode, env2
            | r1,r2 ->
                e1Code @ [Ins2("cmp", Reg r1, Cst 0)] @ movToRetReg r2 r1 @[Jump("jnz", labend)]
                       @ e2Code @ [Label labend] @ movToRetReg reg r2,env2
        | _ -> failwith "wrong abstract syntax in Orelse"        
    | Call(f, es) ->
        let code = callfun f es varEnv funEnv reg liveVars graph
        code,varEnv
    | Temp(n, e) ->
        match Map.find n graph with
        | Spill ->
            let newEnv,code = allocate Locvar (TypI, n) varEnv
            match getUnusedRegister graph liveVars with
            | None ->
                let tr = getTemp Dummy liveVars graph //getTemp always returns a register that is not spill.
                let eCode,env1 = cExpr e newEnv funEnv tr liveVars graph
                code @ evictAndRestore n tr env1 (eCode @ putValInAddrOfTemp n tr env1),env1
            | Some r ->
                let eCode, env1 = cExpr e newEnv funEnv r liveVars graph
                code @ eCode @ putValInAddrOfTemp n r env1, env1
        | r -> cExpr e varEnv funEnv r liveVars graph
            
        
        
(* Generate code to access variable, dereference pointer or index array: *)
(* If return empty list tr is a register with a value otherwise it contains an address*)
and cAccess access varEnv funEnv reg liveVars graph =
    match access with 
    | AccVar x ->
      match lookup (fst varEnv) x with
      | Glovar addr, TypA _ ->
          match Map.find x graph with
          | Spill ->
              [Ins2("mov", Reg reg, Glovars);Ins2("sub", Reg reg, Cst (8*addr))],varEnv, reg
          | r -> [Ins2("mov", Reg r, Glovars);Ins2("sub", Reg r, Cst (8*addr))],varEnv, r
      | Locvar addr, TypA _->
          match Map.find x graph with
          | Spill ->
              [Ins2("lea", Reg reg, RbpOff (8*addr))],varEnv, reg
          | r -> [Ins2("lea", Reg r, RbpOff (8*addr))],varEnv, r
      | Glovar addr, _ ->
          match Map.find x graph with
          | Spill ->
              [Ins2("mov", Reg reg, Glovars);Ins2("sub", Reg reg, Cst (8*addr))],varEnv, reg
          | r -> [],varEnv, r
      | Locvar addr, _ ->
          match Map.find x graph with
          | Spill ->
              [Ins2("lea", Reg reg, RbpOff (8*addr))],varEnv, reg
          | r -> [],varEnv, r
    | AccDeref e ->
        match e with
        |Temp(n,expr) ->
            match expr with 
            | Prim2(ope, e1, e2) -> //pointer arithmetic
                let e1Code, env1 = cExpr e1 varEnv funEnv reg liveVars graph
                let e2Code,env2 = cExpr e2 env1 funEnv reg liveVars graph
                let exprCodes = e1Code @ e2Code
                match e1,e2 with
                | Temp(n1, _),Temp(n2, _) ->
                    match Map.find n1 graph, Map.find n2 graph with
                    | Spill,Spill->
                        let tempReg2 = getTemp reg liveVars graph
                        let code =  getAddrOfTemp n1 reg env2 @ getAddrOfTemp n2 tempReg2 env2
                                    @ pointerArithmeticCode ope reg tempReg2
                        exprCodes @ evictAndRestore n2 tempReg2 env2 code,env2, reg //returns reg cause the result is there
                    | Spill,r->
                        let code = getAddrOfTemp n1 reg env2 @ pointerArithmeticCode ope reg r
                        exprCodes @ code, env2, reg
                    | r, Spill-> 
                        let code = getAddrOfTemp n2 reg env2 @ pointerArithmeticCode ope r reg
                        exprCodes @ code @ [Ins2("mov",Reg reg, Reg r)],env2, r
                    | r1,r2 ->
                        exprCodes @ pointerArithmeticCode ope r1 r2, env2, r1
                | _ -> failwith "wrong abstract syntax for pointer arithmetic - should contain temp" 
            | _ ->
                let code, env = cExpr e varEnv funEnv reg liveVars graph
                match Map.find n graph with
                | Spill -> failwith "not implemented"
                | addr     -> code @ [Ins2("mov", Reg reg, Ind addr)], env, reg
        | _ -> failwith "wrong abstract syntax in AccDeref"
    | AccIndex(acc, idx) ->
      let accCode, env1, tr' = cAccess acc varEnv funEnv reg liveVars graph
      let idxCode,env2 = cExpr idx env1 funEnv reg liveVars graph
      match idx with
      | Temp(n, _) ->
             match Map.find n graph with
                | Spill -> accCode @ [Ins2("mov", Reg tr', Ind tr')] @ idxCode
                            @ [Ins2("sal", Reg reg, Cst 3);Ins2("sub", Reg tr', Reg reg)],env2, tr' //tr' from access
                | r -> accCode @ [Ins2("mov", Reg tr', Ind tr')] @ idxCode
                        @ [Ins2("sal", Reg r, Cst 3);Ins2("sub", Reg tr', Reg r)],env2, tr' //tr' from access
      | _ -> failwith "wrong abstract syntax in AccIndex"
          

(* Generate code to evaluate a list es of expressions: *)

and cExprs es varEnv funEnv reg liveVars graph = 
    List.concat(List.map (fun e ->
        let eCode,_ = cExpr e varEnv funEnv reg liveVars graph
        eCode @ [Ins1("push", Reg reg)]) es)

(* Generate code to evaluate arguments es and then call function f: *)

and callfun f es varEnv funEnv tr liveVars graph =
    let (labf, tyOpt, paramdecs) = lookup funEnv f
    let argc = List.length es
    if argc = List.length paramdecs then
        preserveAll liveVars (cExprs es varEnv funEnv tr liveVars graph
                          @ [Ins("push rbp");Jump("call", labf);Ins2("mov", Reg tr, Reg Rbx)]) graph
    else
        raise (Failure (f + ": parameter/argument mismatch"))

(* Compile a complete micro-C program: globals, call to main, functions *)

let cProgram (DProg topdecs) graph : x86 list * int * x86 list * x86 list = 
    let _ = resetLabels ()
    let ((globalVarEnv, _), funEnv, globalInit) = makeGlobalEnvs topdecs
    let compilefun (tyOpt, f, xs, body) =
        let (labf, _, paras) = lookup funEnv f
        let (envf, fdepthf) = bindParams paras (globalVarEnv, 0)
        let code = cStmt body (envf, fdepthf) funEnv graph
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
    let (globalinit, argc, maincall, functions) = regAlloc program |> cProgram program 
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

