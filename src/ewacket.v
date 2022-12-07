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


Ltac compileNil := match goal with 
| [ H0: nil = compile_unsafe _ ++ _ |- _] =>
    symmetry in H0;
    apply app_eq_nil in H0; 
    destruct H0; subst;simpl
| [ H0: compile_unsafe _ ++ _ = nil |- _] =>
    apply app_eq_nil in H0; 
    destruct H0; subst;simpl
| _ => fail
end.

Ltac compileNotPossible := 
match goal with 
| [ H0: compile_unsafe ?src = nil, H1: ?src d==> _|- _] => 
    inversion H1; subst;
    try (discriminate);
    try (simpl in H0; apply app_eq_nil in H0;
    destruct H0; discriminate)
| _ => fail
end.


Ltac destructCompile H := 
simpl in H;
apply app_eq_app in H;
do 3 destruct H;
[
    rewrite app_nil_l in H;
    simpl
    | (try compileNil);(try compileNotPossible)
].


(* does not work for some reason*)
Ltac refineInductiveHypothesis := match goal with 
| [ H0: compile_unsafe ?src = ?comp,
    _ : (?src d==> ?val),
    IH: (forall (c : list wasmInstruction) (d : dupeResult), 
    compile_unsafe ?src = c -> ?src d==> d -> _)
    |- _]=> apply (IH ?comp ?val) in H0; (try assumption)
end.

Ltac applyInstructionOrder := 
eapply instruction_order;
eauto.


Ltac doesBoolStep := 
simpl;
repeat ( econstructor;[simpl; do 2 constructor | simpl]);
try (do 2 constructor)
.

Ltac doesArithStep := 
simpl;
(repeat (econstructor; [do 2 constructor |]));
try (apply multi_refl);
try (rewrite Z.add_comm; apply multi_refl)
.

Ltac unfoldCompiled H :=
    unfold compile in H; 
    simpl in H;
    inversion H. 

Ltac doesBaseStep := 
    simpl;
    econstructor; 
    constructor; 
    reflexivity.

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
        doesBaseStep.
    (* bool *)
    - unfoldCompiled H.
        destruct b;
        doesBaseStep.
    (* add 1*)
    - apply add1_ImpliesSource in H. 
        do 2 destruct H. 
        subst.
        apply (IHsource x (DR_Int z)) in H;
        simpl; (simpl in H).
        +  applyInstructionOrder.
            doesArithStep.
        + assumption.
    (* sub1 *)
    - apply sub1_ImpliesSource in H. 
        do 2 destruct H. 
        subst.
        apply (IHsource x (DR_Int z)) in H;
        simpl; (simpl in H).
        +  applyInstructionOrder.
            doesArithStep.
        + assumption.
    (* eqz *)
    - apply zero_ImpliesSource in H. 
        do 2 destruct H. 
        subst.
        apply (IHsource x (DR_Int z)) in H;
        simpl; (simpl in H).
        + applyInstructionOrder.
            econstructor.
            * apply W_ST_64Eqz; constructor.
            * destruct (z =? 0); constructor.
        + assumption.
    (* if false*)
    - apply (ifBool_ImpliesSource source1 source2 source3 compiled #f) in H. 
        do 3 destruct H.
        destruct H.
        destruct H1.
        destruct H2.
        subst.
        apply (IHsource1 x (DR_Bool #f)) in H.
        + applyInstructionOrder.
            destruct dupeResult; econstructor;
                (try (eapply W_ST_32IfFalse; (constructor||(apply Z.eqb_neq; reflexivity)||reflexivity)));
                (try simpl; 
                    (apply (IHsource3 x1 (DR_Int z)) in H6 ||
                    apply (IHsource3 x1 (DR_Bool b)) in H6 ||
                    apply (IHsource3 x1 (DR_Error)) in H6)
                );
            (try (applyInstructionOrder; constructor));
            (try assumption).
        + assumption.
        + assumption.
    (* if true *)
    - apply (ifBool_ImpliesSource source1 source2 source3 compiled #t) in H. 
        do 3 destruct H.
        destruct H.
        destruct H1.
        destruct H2.
        subst.
        apply (IHsource1 x (DR_Bool #t)) in H.
        + applyInstructionOrder.
            destruct dupeResult; econstructor;
                (try (eapply W_ST_32IfTrue; (constructor||(apply Z.eqb_neq; reflexivity)||reflexivity)));
                (try simpl; 
                    (apply (IHsource2 x0 (DR_Int z)) in H6 ||
                    apply (IHsource2 x0 (DR_Bool b)) in H6 ||
                    apply (IHsource2 x0 (DR_Error)) in H6)
                );
            (try (applyInstructionOrder; constructor));
            (try assumption).
        + assumption.
        + assumption.

    (* if int *)
    - apply (ifInt_ImpliesSource source1 source2 source3 compiled z) in H. 
        do 3 destruct H.
        destruct H.
        destruct H1.
        destruct H2.
        subst.
        + apply (IHsource2 x0 dupeResult) in H6; assumption.
        + assumption.
Qed.

