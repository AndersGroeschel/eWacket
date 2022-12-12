Require Import ZArith.
Local Open Scope Z_scope.

Require Import String.
Require Import List.
Open Scope list_scope.

Require Import language.definition.

Require Import wasmLite.


Definition uniOpToString op: string := match op with 
| D_U_add1 => "add1"
| D_U_sub1 => "sub1"
| D_U_zero => "zero"
| D_U_not => "not"
end.

Definition typeToString type: string := match type with 
| D_type_Int => "Int"
| D_type_Bool => "Bool"
| D_type_Error => "Error"
end.


Inductive compilerResult : Type := 
| Succ (C: wasmCode)
| Error (err: string)
.


Definition compileUniOp op t := match (op,t) with 
| (D_U_add1,D_type_Int) => (i64.const 1)::(i64.add)::nil
| (D_U_sub1,D_type_Int) => (i64.const 1)::(i64.sub)::nil
| (D_U_zero,D_type_Int) => i64.eqz::nil
| (D_U_not,D_type_Bool) => i32.eqz::nil
| _ => nil
end.

Fixpoint compile_typed (source: dupe) := match source with 
| D_Integer z => (D_type_Int, Succ ((i64.const z)::nil))
| D_Boolean b => (D_type_Bool, Succ ((i32.const (if b then 1 else 0))::nil)) 

| D_UniOp op expr => 
    match compile_typed expr with 
    | (t, Succ code) => 
        match uniOpTypeSignatureForAccept op t with 
        | Some(accepts,returns) => (returns, Succ (code ++ (compileUniOp op accepts)) )
        | None => (D_type_Error, Error (
            (uniOpToString op) ++ "expression had invalid type of: " ++ (typeToString t)
        ))
        end
    | (_, (Error err)) => (D_type_Error, Error err)
    end
| D_if b t e => 
    match (compile_typed b, compile_typed t, compile_typed e) with 
    | ((D_type_Bool, Succ codeB),(t1, Succ codeT),(t2, Succ codeE)) =>
        if(typeSame t1 t2) 
        then (t1, Succ (codeB ++ (ifThenElse codeT codeE)::nil))
        else (D_type_Error, Error "if type mismatch")
    | ((D_type_Int, Succ codeB),(t1, Succ codeT),(t2, Succ codeE)) =>
        if(typeSame t1 t2) 
        then (t1, Succ codeT)
        else (D_type_Error, Error "if type mismatch")
    | ((_, Error err),(_, _),(_, _)) => (D_type_Error, Error err)
    | ((_, _),(_, Error err),(_, _)) => (D_type_Error, Error err)
    | ((_, _),(_, _),(_, Error err)) => (D_type_Error, Error err)
    | _ => (D_type_Error, Error "unkown error")
    end
end.

Definition compile (source :dupe) := match compile_typed source with 
| (_,Succ code) => Succ code
| (_,Error err) => Error err
end.

Lemma compileSucc_implies_typedSucc :
forall src compiled, 
    compile src = compiled ->
    exists t, compile_typed src = (t,compiled).
Proof.
intros.
unfold compile in H.
destruct compiled; destruct (compile_typed src); destruct c;
(try discriminate); exists d;rewrite H; reflexivity.
Qed.


Lemma uniaryOp_ImpliesSource:
forall src compiled op, 
    compile (D_UniOp op src) = Succ compiled ->
    exists code, ((compile src = Succ code) /\ (compiled = code ++ (compileUniOp op (typeOfDupe src)))).
Proof.
   Admitted.

Lemma ifBool_ImpliesSource :
forall srcIf srcThen srcElse compiled, 
    compile (If srcIf Then srcThen Else srcElse) = Succ compiled ->
    typeOfDupe srcIf = D_type_Bool ->
    exists codeIf codeThen codeElse, 
        ((compile srcIf = Succ codeIf) /\ (compile srcThen = Succ codeThen) /\ (compile srcElse = Succ codeElse) /\
        (compiled = codeIf ++ ((ifThenElse codeThen codeElse)::nil))).
Proof.
    Admitted.


Lemma ifInt_ImpliesSource :
forall srcIf srcThen srcElse compiled, 
    compile (If srcIf Then srcThen Else srcElse) = Succ compiled ->
    typeOfDupe srcIf = D_type_Int->
    exists codeIf codeThen codeElse, 
        ((compile srcIf = Succ codeIf) /\ (compile srcThen = Succ codeThen) /\ (compile srcElse = Succ codeElse) /\
        (compiled = codeThen)).
Proof.
    Admitted.



