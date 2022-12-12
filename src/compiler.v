Require Import wacket.
Require Import wasmLite.
Require Import List.

Require Import ZArith.
Local Open Scope Z_scope.
Open Scope list_scope.

Require Import String.


Inductive compilerResult : Type := 
| Succ (C: wasmCode)
| Error (err: string)
.

Inductive typ: Type :=
| typ_Int
| typ_Bool
| typ_Error
.

Definition typeToString (t:typ) : string := match t with 
| typ_Int => "Int"
| typ_Bool => "Bool"
| typ_Error => "Error"
end.

Definition typeSame t1 t2 := match (t1,t2) with 
| (typ_Int,typ_Int) => true
| (typ_Bool,typ_Bool) => true
| (typ_Error,typ_Error) => true
| _ => false
end.

Fixpoint compile_typed (source: dupe) := match source with 
| D_Integer z => (typ_Int, Succ ((i64.const z)::nil))
| D_Boolean b => (typ_Bool, Succ ((i32.const (if b then 1 else 0))::nil))
| D_add1 e => 
    match compile_typed e with 
    | (typ_Int, Succ code) => (typ_Int, Succ(code ++ ((i64.const 1)::(i64.add)::nil)))
    | (_, (Error err)) => (typ_Error, Error err)
    | (typ, Succ _) => 
        (typ_Error, Error ("add1 expression had type of: "++(typeToString typ) ++ 
            " expected type of : " ++(typeToString typ_Int)) )
    end
| D_sub1 e => 
    match compile_typed e with 
    | (typ_Int, Succ code) => (typ_Int, Succ(code ++ ((i64.const 1)::(i64.sub)::nil)))
    | (_, (Error err)) => (typ_Error, Error err)
    | (typ, Succ _) => 
        (typ_Error, Error ("sub1 expression had type of: "++(typeToString typ) ++ 
            " expected type of : " ++(typeToString typ_Int)) )
    end
| D_zero e => 
    match compile_typed e with 
    | (typ_Int, Succ code) => (typ_Int, Succ(code ++ (i64.eqz::nil)))
    | (_, (Error err)) => (typ_Error, Error err)
    | (typ, Succ _) => 
        (typ_Error, Error ("zero? expression had type of: "++(typeToString typ) ++ 
            " expected type of : " ++(typeToString typ_Int)) )
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

(* need these lemmas *)
Lemma add1_ImpliesSource :
forall src compiled, 
    compile (add1 src) = Succ compiled ->
    exists code, ((compile src = Succ code) /\ (compiled = code ++ ((i64.const 1)::(i64.add)::nil))).
Proof.
    Admitted.

Lemma sub1_ImpliesSource :
forall src compiled, 
    compile (sub1 src) = Succ compiled ->
    exists code, ((compile src = Succ code) /\ (compiled = code ++ ((i64.const 1)::(i64.sub)::nil))).
Proof.
    Admitted.

Lemma zero_ImpliesSource :
forall src compiled, 
    compile (zero? src) = Succ compiled ->
    exists code, ((compile src = Succ code) /\ (compiled = code ++ (i64.eqz::nil))).
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



