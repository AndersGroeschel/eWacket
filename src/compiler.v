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

Definition typeToString (t: dupeType) : string := match t with 
| D_type_Int => "Int"
| D_type_Bool => "Bool"
| D_type_Error => "Error"
end.

Definition typeSame t1 t2 := match (t1,t2) with 
| (D_type_Int,D_type_Int) => true
| (D_type_Bool,D_type_Bool) => true
| (D_type_Error,D_type_Error) => true
| _ => false
end.

Fixpoint compile_typed (source: dupe) := match source with 
| D_Integer z => (D_type_Int, Succ ((i64.const z)::nil))
| D_Boolean b => (D_type_Bool, Succ ((i32.const (if b then 1 else 0))::nil))
| D_add1 e => 
    match compile_typed e with 
    | (D_type_Int, Succ code) => (D_type_Int, Succ(code ++ ((i64.const 1)::(i64.add)::nil)))
    | (_, (Error err)) => (D_type_Error, Error err)
    | (typ, Succ _) => 
        (D_type_Error, Error ("add1 expression had type of: "++(typeToString typ) ++ 
            " expected type of : " ++(typeToString D_type_Int)) )
    end
| D_sub1 e => 
    match compile_typed e with 
    | (D_type_Int, Succ code) => (D_type_Int, Succ(code ++ ((i64.const 1)::(i64.sub)::nil)))
    | (_, (Error err)) => (D_type_Error, Error err)
    | (typ, Succ _) => 
        (D_type_Error, Error ("sub1 expression had type of: "++(typeToString typ) ++ 
            " expected type of : " ++(typeToString D_type_Int)) )
    end
| D_zero e => 
    match compile_typed e with 
    | (D_type_Int, Succ code) => (D_type_Bool, Succ(code ++ (i64.eqz::nil)))
    | (_, (Error err)) => (D_type_Error, Error err)
    | (typ, Succ _) => 
        (D_type_Error, Error ("zero? expression had type of: "++(typeToString typ) ++ 
            " expected type of : " ++(typeToString D_type_Int)) )
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

Lemma compile_implies_typed :
forall src compiled, 
    compile src = compiled ->
    exists t, compile_typed src = (t,compiled).
Proof.
intros.
unfold compile in H.
destruct compiled; destruct (compile_typed src); destruct c;
(try discriminate);exists d;rewrite H; reflexivity.
Qed.


(* need these lemmas *)
Lemma add1_ImpliesSource :
forall src compiled, 
    compile (add1 src) = Succ compiled ->
    exists code, ((compile src = (Succ code)) /\ (compiled = code ++ ((i64.const 1)::(i64.add)::nil))).
Proof.
    intros.
    assert (exists c, compile src = c).
    - exists (compile src). reflexivity.
    - destruct H0. remember H0. clear Heqe. 
        apply compile_implies_typed in e. 
        destruct e.
        destruct x.
        + exists C. split.
            * assumption.
            * unfold compile in H. simpl in H.
                rewrite H1 in H. destruct x0.
                -- inversion H. reflexivity.
                -- inversion H.
                -- inversion H.
        + * unfold compile in H. simpl in H.
            rewrite H1 in H. destruct x0; try discriminate.
Qed.

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
    srcIf d==> (D_type_Bool, DR_Bool b)->
    exists codeIf codeThen codeElse, 
        ((compile srcIf = Succ codeIf) /\ (compile srcThen = Succ codeThen) /\ (compile srcElse = Succ codeElse) /\
        (compiled = codeIf ++ ((ifThenElse codeThen codeElse)::nil))).
Proof.
    Admitted.


Lemma ifInt_ImpliesSource :
forall srcIf srcThen srcElse compiled z, 
    compile (If srcIf Then srcThen Else srcElse) = Succ compiled ->
    srcIf d==> (D_type_Int, DR_Int z)->
    exists codeIf codeThen codeElse, 
        ((compile srcIf = Succ codeIf) /\ (compile srcThen = Succ codeThen) /\ (compile srcElse = Succ codeElse) /\
        (compiled = codeThen)).
Proof.
    Admitted.



