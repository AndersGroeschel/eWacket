Require Import Arith Bool List ZArith.
Local Open Scope Z_scope.

Require Import wacket.
Require Import wasmLite.
Require Import compiler.
Require Import utils.
Require Import helperTactics.



Definition dupeResult_to_wasmVal (res: dupeResult) :=
match res with 
| DR_Int z => v_i64 z
| DR_Bool b => if b then v_i32 1 else v_i32 0
| DR_Error => trap
end.

Ltac applyInstructionOrder := 
eapply instruction_order;
eauto.

Ltac unfoldCommon :=
unfold testopOperation in *;
unfold binopOperation in *;
unfold UniOpTransform in *
.

Ltac unfoldCompiled H :=
    unfold compile in H; 
    simpl in H;
    inversion H. 

Ltac stepCompletes := (
    reflexivity || 
    (apply Z.eqb_neq;reflexivity)
).

Ltac doesSingleStep := 
    ( (eapply W_ST_64Const; stepCompletes)
    || (eapply W_ST_32Const; stepCompletes)
    || (eapply W_ST_inn_ibinop; stepCompletes)
    || (eapply W_ST_inn_itestop; stepCompletes)
    || (eapply W_ST_64IfTrue; stepCompletes)
    || (eapply W_ST_64IfFalse; stepCompletes)
    || (eapply W_ST_32IfTrue; stepCompletes)
    || (eapply W_ST_32IfFalse; stepCompletes)
    || (eapply W_ST_nop; stepCompletes)
    || (eapply W_ST_unreachable; stepCompletes)
    )
.

Ltac doesStep :=
repeat (
    unfoldCommon;
    simpl in *;
    (repeat destructBools);
    (repeat removeListNils); 
    (try assumption);
    (try discriminate);
    match goal with 
    | [|- _ w-->* _ ]=> econstructor
    | [|- multi wasmStepInd _ _] => econstructor
    | [|- _ w--> _] => doesSingleStep
    end
).


Ltac solveCase := 
    repeat logicAuto;
    unfoldCommon;
    simpl in *;
    (repeat refineInductiveHypothesis);
    subst;
    (try applyInstructionOrder);
    (try doesStep);
    (try assumption)
.



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
        solveCase.
    (* bool *)
    - unfoldCompiled H.
        solveCase.
    (* uniary operators *)
    - apply uniaryOp_ImpliesSource in H.
        destruct v; destruct d; (try discriminate); solveCase.
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

