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
    (repeat removeListNils); 
    (try assumption);
    match goal with 
    | [|- _ w-->* _ ]=> econstructor
    | [|- multi wasmStepInd _ _] => econstructor
    | [|- _ w--> _] => doesSingleStep
    end
).


Ltac solveCase := 
    repeat logicAuto;
    subst;
    (repeat refineInductiveHypothesis);
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
    (* add 1*)
    - apply add1_ImpliesSource in H.
        solveCase.
    (* sub1 *)
    - apply sub1_ImpliesSource in H. 
        solveCase.
    (* eqz *)
    - apply zero_ImpliesSource in H. 
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

