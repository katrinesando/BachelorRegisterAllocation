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


type 'data env = (string * 'data) list
type var = 
    Glovar of int*bool                  (* address relative to bottom of stack *)
  | Locvar of int*bool

type varEnv = (var * typ) env * int

(* The function environment maps function name to label and parameter decs *)

type paramdecs = (typ * string) list
type funEnv = (flabel * typ option * paramdecs) env
let pushAndPop reg code = [Ins1("push", Reg reg)] @ code @ [Ins1("pop", Reg reg)]

let rec lookup env x = 
    match env with 
    | []         -> failwith (x + " not found")
    | (y, v)::yr -> if x=y then v else lookup yr x
    
(* Preserve reg across code, on the stack if necessary *)
let preserve reg live code graph =
    let inUse = List.fold (fun inUse elem ->
        if reg = Map.find elem graph then true else inUse) false live
    if inUse then
       pushAndPop reg code
    else
        code

let allocate kind (typ, x) (varEnv : varEnv) : varEnv * x86 list =
    let env, fdepth = varEnv 
    match typ with
    | TypA (TypA _, _) -> 
      raise (Failure "allocate: array of arrays not permitted")
    | TypA (t, Some i) -> 
      let newEnv = ((x, (kind (fdepth+i,false), typ)) :: env, fdepth+i+1)
      let code = [Ins("mov rax, rsp");
                  Ins("sub rax, 8");
                  Ins2("sub", Reg Rsp, Cst (8*i));
                  Ins1("push", Reg Rax)]
      (newEnv, code) 
    | _ -> 
      let newEnv = ((x, (kind (fdepth,false), typ)) :: env, fdepth+1)
      let code = [Ins "sub rsp, 8"] 
      (newEnv, code)
     
(* Get temporary register not used by a var in liveVars that isn't pres *)
let getTemp pres liveVars graph =
    let r = List.fold (fun toEvict elem ->
        let used = Map.find elem graph
        if not (mem used [pres;Dummy;Spill]) then used else toEvict) Rdx liveVars
    if pres <> Rdx then r else Rcx


(* ------------------------------------------------------------------- *)
let preserveCallerSaveRegs live graph env code =
    let resCode = List.fold (fun acc elem ->
                match Map.find elem graph with
                | Spill -> acc
                | tr -> 
                    if (string elem).StartsWith "/" then acc
                    else
                        let addr =
                            match lookup (fst env) elem with
                            | Locvar (i,_), _ -> i
                            | _ -> failwith "huh"
                        Ins2("lea", Reg tr, RbpOff (addr * 8)):: Ins2("mov",Reg tr, Ind tr)::acc) [] live
    code @ resCode

(* Global environments for variables and functions *)
let makeGlobalEnvs topdecs : varEnv * funEnv * x86 list = 
    let rec addv decs varEnv funEnv = 
        match decs with 
        | []         -> (varEnv, funEnv, [])
        | dec::decr  -> 
          match dec with
          | DVardec (typ, var,info) ->
            let varEnv1, code1          = allocate Glovar (typ, var) varEnv
            let varEnvr, funEnvr, coder = addv decr varEnv1 funEnv
            (varEnvr, funEnvr, code1 @ coder)
          | DFundec (tyOpt, f, xs, body,info) ->
            addv decr varEnv ((f, ("_" + f, tyOpt, xs)) :: funEnv)
    addv topdecs ([], 0) []

(* ------------------------------------------------------------------- *)
let movToRetReg retReg curReg =
    if curReg <> retReg then [Ins2 ("mov", Reg retReg, Reg curReg)] else []

let prim1Code ope tr liveVars graph env code=
    match ope with
           | "!"      -> code @ [Ins("xor rax, rax");
                          Ins2("cmp", Reg tr, Reg Rax);
                          Ins("sete al");
                          Ins2("mov", Reg tr, Reg Rax)]
           | "printi" -> preserveCallerSaveRegs liveVars graph env (code @ [Ins2("mov",Reg Rdi, Reg tr);PRINTI])
           | "printc" -> preserveCallerSaveRegs liveVars graph env (code @ [Ins2("mov",Reg Rdi, Reg tr);PRINTC])
           | _        -> raise (Failure "unknown primitive 1")
let prim2Code ope liveVars graph tr tr' =
    match ope with
               | "+"   -> [Ins2("add", Reg tr, Reg tr')]
               | "-"   -> [Ins2("sub", Reg tr, Reg tr')]
               | "*"   -> [Ins2("mov", Reg Rax, Reg tr)
                           Ins1("imul", Reg tr');Ins2("mov", Reg tr, Reg Rax)]
               | "/"   -> [Ins2("mov", Reg Rax, Reg tr)] @
                          if tr' <> Rdx then
                              preserve Rdx liveVars [Ins("cqo"); Ins1("idiv", Reg tr')] graph
                          else
                              [Ins2("mov",Reg tr, Reg tr');Ins("cqo"); Ins1("idiv", Reg tr)]
                          @ [Ins2("mov", Reg tr, Reg Rax)]
               | "%"   ->
                          [Ins2("mov", Reg Rax, Reg tr)] @
                          if tr' <> Rdx && tr <> Rdx then
                              [Ins("cqo"); Ins1("idiv", Reg tr'); Ins2("mov", Reg tr, Reg Rdx)] |>
                              preserve Rdx liveVars <| graph
                          
                          else
                              [Ins2("mov",Reg tr, Reg tr');Ins("cqo"); Ins1("idiv", Reg tr); 
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
     
let pointerArithmeticCode ope tr tr' =
    match ope with //+/- need to be flipped due to how the stack grow towards lower addresses
    | "+" -> [Ins2("sal", Reg tr', Cst 3);Ins2("sub", Reg tr, Reg tr')]
    | "-" -> [Ins2("sal", Reg tr', Cst 3);Ins2("add", Reg tr, Reg tr')]
    | _   -> raise (Failure (ope + " operator not allowed when dereferencing"))

let getValOfTemp name reg varEnv=
    match lookup (fst varEnv) name with
                | Locvar (addr,_),_ -> [Ins2("lea", Reg reg, RbpOff (8*addr)); Ins2 ("mov", Reg reg, Ind reg)]
                | _ -> failwith "a temporary should not be a Glovar"
let putValInAddrOfTemp name reg varEnv =
    match lookup (fst varEnv) name with
                | Locvar (addr,_),_ -> [Ins2("mov", RbpOff (8*addr), Reg reg)]
                | _ -> failwith "a temporary should not be a Glovar"
let getAddrOfVarInReg tr reg graph liveVars env =
    let name = List.fold(fun acc elem ->
            if Map.find elem graph = tr then elem else acc) "" liveVars
    match lookup (fst env) name with
    | Locvar (addr,_),_ -> [Ins2("lea", Reg reg, RbpOff (8*addr))]
    | Glovar (addr,_), _ -> [Ins2("mov", Reg reg, Glovars);Ins2("sub", Reg reg, Cst (8*addr))]

let restoreCode live graph env tr =
                    let varName = List.fold (fun acc elem ->
                        if Map.find elem graph = tr then elem else acc) "" live 
                    if varName.StartsWith '/' || varName = "" then []
                    else
                        let addr =
                            match lookup (fst env) varName with
                            | Locvar (i,_), _ -> i
                            | _ -> failwith "huh"
                        [Ins2("lea", Reg tr, RbpOff (addr * 8));Ins2("mov",Reg tr, Ind tr)]

let updateVarEnv toInsert name varenv =
    let rec aux rest acc =
        match rest with
        | [] -> acc, snd varenv
        | (n,_ as x)::xs ->
            if n = name then
                (name,toInsert) :: acc @ xs, snd varenv
            else
                aux xs (x::acc)
    aux (fst varenv) []

let deprecateRegisters liveVars varEnv graph =
    let rec loop envRest acc =
        match envRest with
        | [] -> (acc,snd varEnv)
        | n,(v,t) as x::xs ->
            let updated = List.fold (fun newElem elem ->
                if n = elem && Map.find elem graph <> Spill then
                    match v with
                    | Locvar(addr, _) -> (n,(Locvar(addr,false),t))
                    | _ -> failwith "huh"
                else
                    newElem) x liveVars
            loop xs (updated::acc)
    loop (fst varEnv) []            

        
        
let rec allocTsExpr exp graph varEnv code =
    match exp with
    |Access acc -> allocTsAccess acc graph varEnv code
    |Assign(acc, e) ->
        let newEnv1,c1 = allocTsAccess acc graph varEnv code
        allocTsExpr e graph newEnv1 c1
    |Addr acc -> allocTsAccess acc graph varEnv code
    |CstI _ -> varEnv,code
    |Prim1 (_,e) -> allocTsExpr e graph varEnv code
    |Prim2(_,e1,e2) ->
        let newEnv1,c1 = allocTsExpr e1 graph varEnv code
        allocTsExpr e2 graph newEnv1 c1
    |Andalso(e1, e2)->
        let newEnv1,c1 = allocTsExpr e1 graph varEnv code
        allocTsExpr e2 graph newEnv1 c1
    |Orelse(e1, e2) ->
        let newEnv1,c1 = allocTsExpr e1 graph varEnv code
        allocTsExpr e2 graph newEnv1 c1
    |Call(_, es) ->
        let rec aux (envAcc,codeAcc as acc) rest =
            match rest with
            | [] -> acc
            | x::xs ->
                let ne,c = allocTsExpr x graph envAcc codeAcc
                aux (ne,c) xs
        aux (varEnv,code) es
    |Temp(n, e) ->
        match Map.find n graph with
        | Spill ->
            let newEnv1,c1 = allocate Locvar (TypI, n) varEnv
            allocTsExpr e graph newEnv1 (code @ c1)
        | _ -> allocTsExpr e graph varEnv code
        
and allocTsAccess ac graph varEnv code =
    match ac with
    |AccVar _   -> varEnv,code
    |AccDeref e -> allocTsExpr e graph varEnv code
    |AccIndex(acc, idx) ->
        let newEnv1,c1 = allocTsAccess acc graph varEnv code
        allocTsExpr idx graph newEnv1 c1

let allocateTemps expr graph varEnv =
    let env,c = allocTsExpr expr graph varEnv []
    env,[Ins2("sub", Reg Rsp, Cst (8 * List.length c))]
    

(* Compiling micro-C statements *)
let rec cStmt stmt (varEnv : varEnv) (funEnv : funEnv) graph : x86 list =
    match stmt with
    | DIf(e, stmt1, stmt2,info) ->
        let labelse = newLabel()
        let labend  = newLabel()
        let ifCode =
                    let thenCode = cStmt stmt1 varEnv funEnv graph
                    let elseCode = cStmt stmt2 varEnv funEnv graph
                    [Jump("jz", labelse)] 
                    @ thenCode @ [Jump("jmp", labend)]
                    @ [Label labelse] @ elseCode
                    @ [Label labend]
        let env,allocCode = allocateTemps e graph varEnv
        match e with
        | Temp(n, _) ->
            match Map.find n graph with
            | Spill ->
                let tempReg = getTemp Dummy info graph
                let env2, eCode = cExpr e env funEnv tempReg info graph
                allocCode @ eCode @ getValOfTemp n tempReg env
                @ [Ins2 ("add", Reg Rsp, Cst (8 * (snd env2 - snd varEnv))); Ins2("cmp", Reg tempReg, Cst 0)]
                @ restoreCode info graph env tempReg @ ifCode
            | r ->
                let env2, eCode = cExpr e env funEnv r info graph
                allocCode @ eCode @ [Ins2("add", Reg Rsp, Cst (8 * (snd env2 - snd varEnv)));Ins2("cmp", Reg r, Cst 0)]
                @ ifCode
        | _ -> failwith "condition not in temp in If"
    | DWhile(e, body,info) ->
        let labbegin = newLabel()
        let labcondition  = newLabel()
        let loopCode =
                   let code1 = cStmt body varEnv funEnv graph
                   [Jump("jmp", labcondition);Label labbegin]
                   @ code1
                   @ [Label labcondition]
        let env,allocCode = allocateTemps e graph varEnv
        match e with
        | Temp(n,_) ->
            match Map.find n graph with
            | Spill ->
                let tempReg = getTemp Dummy info graph
                let env2, eCode = cExpr e env funEnv tempReg info graph
                allocCode @ loopCode @ eCode @ getValOfTemp n tempReg env
                @ [Ins2("cmp", Reg tempReg, Cst 0)]
                @ restoreCode info graph env tempReg
                @ [ Jump("jnz", labbegin);Ins2("add", Reg Rsp, Cst (8 * (snd env2 - snd varEnv)))]
            | r ->
                 let env2, eCode = cExpr e env funEnv r info graph
                 allocCode @ loopCode @ eCode @
                 [Ins2("cmp", Reg r, Cst 0);Jump("jnz", labbegin)
                  Ins2("add", Reg Rsp, Cst (8 * (snd env2 - snd varEnv)))]
        | _ -> failwith "condition not in temp in While"
    | DExpr(e,info) -> 
        match e with
        | Temp(n,_) ->
            let env,allocCode = allocateTemps e graph varEnv
            match Map.find n graph with
            | Spill ->
                let tempReg = getTemp Dummy info graph
                let env2,eCode = cExpr e env funEnv tempReg info graph
                //Since temps always die after DExpr, the final instr to move val into addr of temp is useless
                allocCode @ (List.removeAt ((List.length eCode)-1) eCode)
                @ [Ins2 ("add", Reg Rsp, Cst (8 * (snd env2 - snd varEnv)))]
                @ restoreCode info graph env2 tempReg
            | r -> let env2, eCode = cExpr e env funEnv r info graph
                   allocCode @ eCode @ [Ins2 ("add", Reg Rsp, Cst (8 * (snd env2 - snd varEnv)))]
        | _ -> failwith "condition not in temp in Expr" 
    | DBlock(stmts,info) -> 
        let rec loop stmts varEnv =
            match stmts with 
            | []     -> (snd varEnv, [])
            | s1::sr -> 
              let varEnv1, code1 = cStmtOrDec s1 varEnv funEnv graph
              let fdepthr, coder = loop sr varEnv1 
              (fdepthr, code1 @ coder)
        let fdepthend, code = loop stmts varEnv
        code @ [Ins2("sub", Reg Rsp, Cst (8 * (snd varEnv - fdepthend)))] 
    | DReturn(None,info) ->
        [Ins2("add", Reg Rsp, Cst (8 * snd varEnv)); 
                 Ins("pop rbp");
                 Ins("ret")]
    | DReturn(Some e,info) ->  
        match e with
        |Temp(n, _) ->
            let env,allocCode = allocateTemps e graph varEnv
            match Map.find n graph with
            | Spill ->
                let tempReg = getTemp Dummy info graph
                let env2, eCode = cExpr e env funEnv tempReg info graph
                allocCode @ eCode @ [Ins2 ("add", Reg Rsp, Cst (8 * (snd env2)))]
                @ movToRetReg Rbx tempReg @ [Ins("pop rbp");Ins("ret")]
            | r ->
                let env2,eCode = cExpr e env funEnv r info graph
                allocCode @ eCode @ [Ins2("add", Reg Rsp, Cst (8 * snd env2))] 
                @ movToRetReg Rbx r @ [Ins("pop rbp");Ins("ret")]


and cStmtOrDec stmtOrDec (varEnv : varEnv) (funEnv : funEnv) graph : varEnv * x86 list = 
    match stmtOrDec with 
    | DStmt (stmt,_)    -> varEnv,cStmt stmt varEnv funEnv graph 
    | DDec (typ, x,_) -> allocate Locvar (typ, x) varEnv

(* Compiling micro-C expressions: 

   * e       is the expression to compile
   * varEnv  is the local and gloval variable environment 
   * funEnv  is the global function environment
   * reg      is the x86-64 register in which the result should be computed
   * liveVars  is a list of variable names that are live during the computation
   * graph     is the interference graph of the program
   
   Net effect principle: if the compilation (cExpr e varEnv funEnv reg liveVars graph) of
   expression e returns the instruction sequence instrs, then the
   execution of instrs will leave the rvalue of expression e in register tr,
   and leave the stack depth unchanged.
*)

and cExpr (e : expr) (varEnv : varEnv) (funEnv : funEnv) (reg : reg64) liveVars graph : varEnv * x86 list = 
    match e with
    | Access acc     ->
        let code,newEnv, tr = cAccess acc varEnv funEnv reg liveVars graph
        match code with
        | [] -> newEnv, movToRetReg reg tr
        | _ ->
            newEnv, code @ [Ins2("mov", Reg tr, Ind tr)] @ movToRetReg reg tr 
    | Assign(acc, e) ->
        let accCode,env1, tr = cAccess acc varEnv funEnv reg liveVars graph
        match e with
        | Temp(n, _) ->
            let newEnv,code =
                match Map.find n graph with
                | Spill ->
                    if tr <> reg then 
                        let env2, eCode = cExpr e env1 funEnv reg liveVars graph
                        match accCode with
                        | [] -> 
                            let addrCode = getAddrOfVarInReg tr reg graph liveVars env2
                            env2,eCode @ [Ins1("push", Reg reg)] @ addrCode
                                        @ [Ins1("pop", Reg tr);Ins2("mov", Ind reg, Reg tr)] @ movToRetReg reg tr
                        | _ ->
                            env2,eCode @ accCode @ [Ins2("mov", Ind tr, Reg reg)]
                    else
                        let tempReg = getTemp reg liveVars graph
                        let env2, eCode = cExpr e env1 funEnv reg liveVars graph
                        match accCode with
                        | [] ->
                            env2, eCode @ preserve tempReg liveVars ([Ins2("mov", Reg tempReg, Reg reg)]
                                            @ getAddrOfVarInReg reg tempReg graph liveVars env2
                                            @ [Ins2("mov", Ind tempReg, Reg reg)]) graph 
                        | _ ->       
                            env2, eCode @ accCode @
                                  preserve tempReg liveVars (getValOfTemp n tempReg env2
                                                             @ [Ins2("mov", Ind tr, Reg tempReg)]
                                                             @ movToRetReg reg tempReg) graph
                | r ->
                    let env2, eCode = cExpr e env1 funEnv r liveVars graph
                    match accCode with 
                    | [] ->
                        let addrCode = getAddrOfVarInReg tr r graph liveVars env2
                        env2, eCode@ [Ins1("push", Reg r)] @ addrCode @ [Ins1("pop", Reg tr);Ins2("mov", Ind r, Reg tr)]  @ movToRetReg reg tr
                    | _  ->
                        env2, eCode @ accCode @ [Ins2("mov", Ind tr, Reg r);Ins2("mov", Reg tr, Ind tr)]  @ movToRetReg reg tr                
            match acc with
            | AccDeref _ -> deprecateRegisters liveVars newEnv graph,code
            | _ -> newEnv,code
        | _ -> failwith "wrong absyn in Assign"
    | CstI i         ->
        varEnv, [Ins2("mov", Reg reg, Cst i)]
    | Addr acc       ->
        let code, env, tr = cAccess acc varEnv funEnv reg liveVars graph
        match code with
        | [] -> env, getAddrOfVarInReg tr reg graph liveVars env
        | _  -> env, code @ movToRetReg reg tr
    | Prim1(ope, e1) ->
        let env1, eCode = cExpr e1 varEnv funEnv reg liveVars graph           
        match e1 with
        | Temp(n,_)->
            match Map.find n graph with
            | Spill ->
                 env1, prim1Code ope reg liveVars graph env1 (eCode@ getValOfTemp n reg env1)
            | r ->
                env1, prim1Code ope r liveVars graph env1 eCode
                        @ movToRetReg reg r
        | _ -> failwith "wrong abstract syntax in Prim1"
    | Prim2(ope, e1, e2) ->
        let exprCodes r1 r2 =
            let env1, e1Code = cExpr e1 varEnv funEnv r1 liveVars graph
            let env2, e2Code = cExpr e2 env1 funEnv r2 liveVars graph
            env2, e1Code @ e2Code 
        match e1,e2 with
        | Temp(n1,_),Temp(n2,_) ->
            match Map.find n1 graph, Map.find n2 graph with
            | Spill,Spill->
                let tempReg = getTemp reg liveVars graph
                let env, eCodes = exprCodes reg reg
                env,eCodes @
                preserve tempReg liveVars (getValOfTemp n1 reg env @
                                           getValOfTemp n2 tempReg env
                                           @ prim2Code ope liveVars graph reg tempReg) graph
            | Spill,r->
                if reg <> r then
                    let env, eCodes = exprCodes reg r
                    env, eCodes @ getValOfTemp n1 reg env @ prim2Code ope liveVars graph reg r
                else
                    let tempReg = getTemp reg liveVars graph
                    let env, eCodes = exprCodes reg reg
                    env, eCodes @ preserve tempReg liveVars (getValOfTemp n1 tempReg env
                                           @ prim2Code ope liveVars graph tempReg reg @ movToRetReg reg tempReg) graph
                                            
            | r, Spill->
                let env1, e1Code = cExpr e1 varEnv funEnv r liveVars graph
                let env2, e2Code = cExpr e2 env1 funEnv reg liveVars graph
                if reg <> r then
                    env2, e2Code @ e1Code @ getValOfTemp n2 reg env2 @
                            prim2Code ope liveVars graph r reg @ movToRetReg reg r
                else
                    let tempReg = getTemp r liveVars graph
                    env2, e2Code @ e1Code @ preserve tempReg liveVars (getValOfTemp n2 tempReg env2
                                           @ prim2Code ope liveVars graph r tempReg) graph
            | r1,r2 ->
                let env, eCodes = exprCodes r1 r2
                env, eCodes @ prim2Code ope liveVars graph r1 r2 @ movToRetReg reg r1
        | _ -> failwith "wrong abstract syntax in Prim2"
    | Andalso(e1, e2) ->
        let labend = newLabel()
        let env1, e1Code = cExpr e1 varEnv funEnv reg liveVars graph
        let env2, e2Code = cExpr e2 env1 funEnv reg liveVars graph
        env2, e1Code @ [Ins2("cmp", Reg reg, Cst 0);Jump("jz", labend)]
                                           @ e2Code @ [Label labend]        
    | Orelse(e1,e2) ->
        let labend = newLabel()
        let env1, e1Code = cExpr e1 varEnv funEnv reg liveVars graph
        let env2, e2Code = cExpr e2 env1 funEnv reg liveVars graph
        env2, e1Code @ [Ins2("cmp", Reg reg, Cst 0);Jump("jnz", labend)]
                                           @ e2Code @ [Label labend]                       
    | Call(f, es) ->
        let code = callfun f es varEnv funEnv reg liveVars graph
        varEnv, code
    | Temp(n, e) ->
        match Map.find n graph with
        | Spill ->
            let env1, eCode = cExpr e varEnv funEnv reg liveVars graph
            match e with
            | Call _ -> env1, preserveCallerSaveRegs liveVars graph env1 (eCode @ putValInAddrOfTemp n reg env1)
            | _ -> env1, eCode @ putValInAddrOfTemp n reg env1
        | r ->
            let env1,code = cExpr e varEnv funEnv r liveVars graph
            match e with
            | Call _ -> env1, preserveCallerSaveRegs liveVars graph env1 code
            | _ -> env1, code
                
            
        
        
(* Generate code to access variable, dereference pointer or index array:*)
and cAccess access varEnv funEnv reg liveVars graph =
    match access with 
    | AccVar x ->
      match lookup (fst varEnv) x with
      | Glovar (addr,_), _ -> [Ins2("mov", Reg reg, Glovars);Ins2("sub", Reg reg, Cst (8*addr))],varEnv, reg
      | Locvar (addr,_), TypA _->
          match Map.find x graph with
          | Spill ->
              [Ins2("lea", Reg reg, RbpOff (8*addr))],varEnv, reg
          | r -> [Ins2("lea", Reg r, RbpOff (8*addr))],varEnv, r
      | Locvar (addr,b), t ->
          match Map.find x graph with
          | Spill ->
              [Ins2("lea", Reg reg, RbpOff (8*addr))],varEnv, reg
          | r ->
              if b then [],varEnv, r
              else
                  let newVar = Locvar(addr,true)
                  [Ins2("lea", Reg r, RbpOff (8*addr))],updateVarEnv (newVar,t) x varEnv, r
    | AccDeref e ->
        match e with
        |Temp(n,expr) ->
            match expr with 
            | Prim2(ope, e1, e2) -> //pointer arithmetic
                let exprCodes r1 r2 =
                    let env1, e1Code = cExpr e1 varEnv funEnv r1 liveVars graph
                    let env2, e2Code = cExpr e2 env1 funEnv r2 liveVars graph
                    env2, e1Code @ e2Code
                match e1,e2 with
                | Temp(n1, _),Temp(n2, _) ->
                    match Map.find n1 graph, Map.find n2 graph with
                    | Spill,Spill->
                        let tempReg = getTemp reg liveVars graph
                        let env,eCodes = exprCodes reg tempReg
                        eCodes @ preserve tempReg liveVars (getValOfTemp n1 reg env @
                                           getValOfTemp n2 tempReg env
                                           @ pointerArithmeticCode ope reg tempReg) graph,env,reg
                    | Spill,r->
                        let env,eCodes = exprCodes reg r
                        eCodes @ pointerArithmeticCode ope reg r,env,reg
                    | r, Spill->
                        let env,eCodes = exprCodes r reg
                        eCodes @ pointerArithmeticCode ope reg r,env,r
                    | r1,r2 ->
                        let env,eCodes = exprCodes r1 r2
                        eCodes @ pointerArithmeticCode ope r1 r2, env, r1
                | _ -> failwith "wrong abstract syntax for pointer arithmetic - should contain temp" 
            | _ ->
                match Map.find n graph with
                | Spill ->
                    let env, code = cExpr e varEnv funEnv reg liveVars graph
                    code,env,reg
                | addr     ->
                    let env, code = cExpr e varEnv funEnv addr liveVars graph
                    code, env, addr
        | _ -> failwith "wrong abstract syntax in AccDeref"
    | AccIndex(acc, idx) ->
      let accCode, env1, tr = cAccess acc varEnv funEnv reg liveVars graph
      match idx with
      | Temp(n, _) ->
             match Map.find n graph with
                | Spill ->
                        if tr <> reg then
                            let env2, idxCode = cExpr idx env1 funEnv reg liveVars graph
                            accCode @ [Ins2("mov", Reg tr, Ind tr)] @ idxCode
                            @ [Ins2("sal", Reg reg, Cst 3);Ins2("sub", Reg tr, Reg reg)],env2, tr
                        else
                            let tempReg = getTemp reg liveVars graph
                            let env2, idxCode = cExpr idx env1 funEnv reg liveVars graph
                            idxCode @ accCode @ [Ins2("mov", Reg reg, Ind reg)] @
                            preserve tempReg liveVars (getValOfTemp n tempReg env2 @
                            [Ins2("sal", Reg tempReg, Cst 3);Ins2("sub", Reg reg, Reg tempReg)]) graph
                            ,env2, reg
                | r ->
                        let env2, idxCode = cExpr idx env1 funEnv r liveVars graph
                        accCode @ [Ins2("mov", Reg tr, Ind tr)] @ idxCode
                        @ [Ins2("sal", Reg r, Cst 3);Ins2("sub", Reg tr, Reg r)],env2, tr
      | _ -> failwith "wrong abstract syntax in AccIndex"
          

(* Generate code to evaluate a list es of expressions: *)
and cExprs es varEnv funEnv reg liveVars graph =
        List.fold(fun instrs elem ->
            let env,eCode = cExpr elem varEnv funEnv reg liveVars graph
            eCode @ [Ins1("push", Reg reg)]
                    @ instrs) [] es
        
(* Generate code to evaluate arguments es and then call function f: *)
and callfun f es varEnv funEnv tr liveVars graph =
    let labf, tyOpt, paramdecs = lookup funEnv f
    let argc = List.length es
    if argc = List.length paramdecs then
        let code = cExprs es varEnv funEnv tr liveVars graph
        code @ [Ins("push rbp");Jump("call", labf);Ins2("mov", Reg tr, Reg Rbx)]
    else
        raise (Failure (f + ": parameter/argument mismatch"))


(* Bind declared parameters in env: *)       
let bindParam (env, fdepth) (typ, x)  : varEnv = 
    ((x, (Locvar (fdepth,false), typ)) :: env , fdepth+1)

let bindParams paras ((env, fdepth) : varEnv) : varEnv = 
    List.fold bindParam (env, fdepth) paras
(* Compile a complete micro-C program: globals, call to main, functions *)
let cProgram (DProg topdecs) graph : x86 list * int * x86 list * x86 list = 
    let _ = resetLabels ()
    let (globalVarEnv, _), funEnv, globalInit = makeGlobalEnvs topdecs
    let compilefun (tyOpt, f, xs, body) =
        let labf, _, paras = lookup funEnv f
        let envf, fdepthf = bindParams paras (globalVarEnv, 0)
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
    let mainlab, _, mainparams = lookup funEnv "main"
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
    let globalinit, argc, maincall, functions = regAlloc program |> cProgram program
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

