Require Import Arith Bool List ZArith.
Local Open Scope Z_scope.

Require Import language.definition.
Require Import language.eval.

Require Import wasmLite.
Require Import compiler.
Require Import utils.
Require Import helperTactics.



Definition dupeResult_to_wasmVal res :=
match res with 
| DR_Int z => v_i64 z
| DR_Bool b => if b then v_i32 1 else v_i32 0
| DR_Error => trap
end.

Ltac applyInstructionOrder := 
eapply instruction_order;
eauto.



Ltac unfoldCompiled H :=
    unfold compile in H; 
    simpl in H;
    inversion H. 




Ltac solveCase := 
    repeat refineHypothesis;
    unfoldCommon;
    simpl in *;
    (repeat specializeIH);
    subst;
    (try applyInstructionOrder);
    (try doesStep);
    (try assumption)
.



(* going to need that dupe is well typed, 
and therefor evalDupe cannot produce an error, 
honestly this should be a feature of the compiler*)
Theorem semanticPreservation:
    forall source compiled dupeResult type,
    (compile source) = (Succ compiled) ->
    source d==> (type, dupeResult) ->
    (compiled,nil) w-->* ((nil, (dupeResult_to_wasmVal dupeResult)::nil)).
Proof.
    induction source; intros;
    inversion H0;subst.
    (* int *)
    - unfoldCompiled H.
        solveCase.
    (* bool *)
    - unfoldCompiled H.
        solveCase.
    (* uniary operators *)
    - apply uniaryOp_ImpliesSource in H.
        repeat destructDupeProperties;
        repeat refineHypothesis; 
        simpl in *; 
        (try applyInstructionOrder).
        doesStep.
        
        solveCase.
    (* if false*)
    - apply (ifBool_ImpliesSource source1 source2 source3 compiled #f) in H.
        + solveCase.
        + assumption.
    (* if true *)
    - apply (ifBool_ImpliesSource source1 source2 source3 compiled #t) in H. 
        + solveCase.
        + assumption.
    (* if int *)
    - apply (ifInt_ImpliesSource source1 source2 source3 compiled z) in H. 
        + solveCase.
        + assumption.
Qed.

