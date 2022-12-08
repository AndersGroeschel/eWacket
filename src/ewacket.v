Require Import Arith Bool List ZArith.
Local Open Scope Z_scope.

Require Import wacket.
Require Import wasmLite.
Require Import compiler.
Require Import utils.



Definition dupeResult_to_wasmVal (res: dupeResult) :=
match res with 
| DR_Int z => v_i64 z
| DR_Bool b => if b then v_i32 1 else v_i32 0
| DR_Error => trap
end.

Ltac applyInstructionOrder := 
eapply instruction_order;
eauto.

(* does not work *)
Ltac refineInductiveHypothesis := 
match goal with 
|   H0 : compile ?source = Succ ?compiled,
    H1 : ?source d==> ?value,
    IH : forall (c: wasmCode) (d: dupeResult),
        compile ?source = Succ c ->
        ?source d==> d -> _
    |- _ => specialize ((IH ?compiler ?value) H0)
| _ => fail
end.

Ltac unfoldCompiled H :=
    unfold compile in H; 
    simpl in H;
    inversion H. 

Ltac logicAuto :=
match goal with 
| H: _ /\ _ |- _ => destruct H
| H: _ \/ _ |- _ => destruct H
| H: exists _, _ |- _ => destruct H
| _ => fail
end.

Ltac destructBools := match goal with 
| [H : ?x = true |- context[if ?x then _ else _] ] => rewrite H
| [H : ?x = false |- context[if ?x then _ else _] ] => rewrite H
| [H : true = ?x |- context[if ?x then _ else _] ] => rewrite H
| [H : false = ?x |- context[if ?x then _ else _] ] => rewrite H
| [|- context[if ?x then _ else _] ] => destruct x eqn: eq
end.

Ltac removeNils := match goal with
| [|- context[_ ++ nil] ] => rewrite app_nil_r
| [|- context[nil ++ _] ] => rewrite app_nil_l
| [H: context[_ ++ nil] |- _ ] => rewrite app_nil_r  in H
| [H: context[nil ++ _] |- _ ] => rewrite app_nil_l  in H
end.

Ltac stepCompletes := 
    (reflexivity || 
    (apply Z.eqb_neq;reflexivity))
.

Ltac doesSingleStep := 
    ( (eapply W_ST_64Const; stepCompletes)
    || (eapply W_ST_32Const; stepCompletes)
    || (eapply W_ST_64Add; stepCompletes)
    || (eapply W_ST_64Sub; stepCompletes)
    || (eapply W_ST_64Eqz; stepCompletes)
    || (eapply W_ST_64IfTrue; stepCompletes)
    || (eapply W_ST_64IfFalse; stepCompletes)
    || (eapply W_ST_32IfTrue; stepCompletes)
    || (eapply W_ST_32IfFalse; stepCompletes)
    || (eapply W_ST_nop; stepCompletes)
    || (eapply W_ST_unreachable; stepCompletes)
    )
.
Ltac doesStep :=
simpl;
repeat (
    (repeat destructBools);
    (repeat removeNils);
    (try assumption);
    match goal with 
    | [|- _ w-->* _ ]=> econstructor
    | [|- multi wasmStepInd _ _] => econstructor
    | [|- _ w--> _] => doesSingleStep
    end
).


(* going to need that dupe is well typed, 
and therefor evalDupe cannot produce an error, 
honestly this should be a feature of the compiler*)
Theorem semanticPreservation:
    forall source compiled dupeResult,
    (compile source) = (Succ compiled) ->
    source d==> dupeResult ->
    (compiled,nil) w-->* ((nil, (dupeResult_to_wasmVal dupeResult)::nil)).
Proof.
    induction source; intros;
    inversion H0;subst.
    (* int *)
    - unfoldCompiled H.
        doesStep.
    (* bool *)
    - unfoldCompiled H.
        doesStep.
    (* add 1*)
    - apply add1_ImpliesSource in H. 
        repeat logicAuto.
        subst.
        applyInstructionOrder.
        doesStep.
    (* sub1 *)
    - apply sub1_ImpliesSource in H. 
        repeat logicAuto.
        subst.
        applyInstructionOrder.
        doesStep.
    (* eqz *)
    - apply zero_ImpliesSource in H. 
        repeat logicAuto.
        subst.
        applyInstructionOrder.
        doesStep.
    (* if false*)
    - apply (ifBool_ImpliesSource source1 source2 source3 compiled #f) in H. 
        repeat logicAuto.
        subst.
        + apply (IHsource3 x1 dupeResult) in H6.
            * applyInstructionOrder. doesStep.
            * assumption.
        + assumption.
    (* if true *)
    - apply (ifBool_ImpliesSource source1 source2 source3 compiled #t) in H. 
        repeat logicAuto.
        subst.
        + apply (IHsource2 x0 dupeResult) in H6.
            * applyInstructionOrder. doesStep.
            * assumption.
        + assumption.
    (* if int *)
    - apply (ifInt_ImpliesSource source1 source2 source3 compiled z) in H. 
        repeat logicAuto.
        subst.
        + apply (IHsource2 x0 dupeResult) in H6; assumption.
        + assumption.
Qed.

