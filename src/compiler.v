Require Import ZArith.
Local Open Scope Z_scope.

Require Import String.
Open Scope list_scope.

Require Import wacket.
Require Import wasmLite.
Require Import List.


Inductive compilerResult : Type := 
| Succ (C: wasmCode)
| Error (err: string)
.

Definition typeSame t1 t2 := match (t1,t2) with 
| (typ_Int,typ_Int) => true
| (typ_Bool,typ_Bool) => true
| (typ_Error,typ_Error) => true
| _ => false
end.

Definition compileUniOp op := match op with 
| D_U_add1 => (i64.const 1)::(i64.add)::nil
| D_U_sub1 => (i64.const 1)::(i64.sub)::nil
| D_U_zero => i64.eqz::nil
| D_U_not => i32.eqz::nil
end.

Fixpoint compile_typed (source: dupe) := match source with 
| D_Integer z => (typ_Int, Succ ((i64.const z)::nil))
| D_Boolean b => (typ_Bool, Succ ((i32.const (if b then 1 else 0))::nil)) 

| D_UniOp op expr => 
    match compile_typed expr with 
    | (t, Succ code) => 
        if typeSame t (uniOpExpectedType op) 
        then (uniOpResultType op ,Succ (code ++ (compileUniOp op)))
        else (typ_Error, Error (
            (uniOpToString op) ++ "expression had type of: " ++ (typeToString t) ++
            " expected type of : " ++ (typeToString (uniOpExpectedType op))
        ))
    | (_, (Error err)) => (typ_Error, Error err)
    end
| D_if b t e => 
    match (compile_typed b, compile_typed t, compile_typed e) with 
    | ((typ_Bool, Succ codeB),(t1, Succ codeT),(t2, Succ codeE)) =>
        if(typeSame t1 t2) 
        then (t1, Succ (codeB ++ (ifThenElse codeT codeE)::nil))
        else (typ_Error, Error "if type mismatch")
    | ((typ_Int, Succ codeB),(t1, Succ codeT),(t2, Succ codeE)) =>
        if(typeSame t1 t2) 
        then (t1, Succ codeT)
        else (typ_Error, Error "if type mismatch")
    | ((_, Error err),(_, _),(_, _)) => (typ_Error, Error err)
    | ((_, _),(_, Error err),(_, _)) => (typ_Error, Error err)
    | ((_, _),(_, _),(_, Error err)) => (typ_Error, Error err)
    | _ => (typ_Error, Error "unkown error")
    end
end.


Definition compile (source :dupe) := match compile_typed source with 
| (_,Succ code) => Succ code
| (_,Error err) => Error err
end.

Lemma uniaryOp_ImpliesSource:
forall src compiled op, 
    compile (D_UniOp op src) = Succ compiled ->
    exists code, ((compile src = Succ code) /\ (compiled = code ++ (compileUniOp op))).
Proof.
   Admitted.

Lemma ifBool_ImpliesSource :
forall srcIf srcThen srcElse compiled b, 
    compile (If srcIf Then srcThen Else srcElse) = Succ compiled ->
    srcIf d==> (DR_Bool b)->
    exists codeIf codeThen codeElse, 
        ((compile srcIf = Succ codeIf) /\ (compile srcThen = Succ codeThen) /\ (compile srcElse = Succ codeElse) /\
        (compiled = codeIf ++ ((ifThenElse codeThen codeElse)::nil))).
Proof.
    Admitted.


Lemma ifInt_ImpliesSource :
forall srcIf srcThen srcElse compiled z, 
    compile (If srcIf Then srcThen Else srcElse) = Succ compiled ->
    srcIf d==> (DR_Int z)->
    exists codeIf codeThen codeElse, 
        ((compile srcIf = Succ codeIf) /\ (compile srcThen = Succ codeThen) /\ (compile srcElse = Succ codeElse) /\
        (compiled = codeThen)).
Proof.
    Admitted.



