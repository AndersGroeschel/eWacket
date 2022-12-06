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
rewrite <- (app_nil_l) in H;
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
subst;
eapply instruction_order;
eauto.


(* going to need that dupe is well typed, 
and therefor evalDupe cannot produce an error, 
honestly this should be a feature of the compiler*)
Theorem semanticPreservation:
    forall source compiled dupeResult,
    (compile_unsafe source) = compiled ->
    source d==> dupeResult ->
    (compiled,nil) w-->* ((nil, (dupeResult_to_wasmVal dupeResult)::nil)).
Proof.
    induction source; intros;
    inversion H0;
    (try destruct b);
    try (subst;econstructor;constructor;
    reflexivity).
    (* add 1*)
    - rewrite <- H3 in H0. 
        clear t H1 H3. 
        destructCompile H.
        simpl.
        apply (IHsource x (DR_Int z)) in H. 
        + applyInstructionOrder.
            doesArithStep.
        + assumption.
    (* sub1 *)
    - rewrite <- H3 in H0.
        clear t H1 H3.
        destructCompile H.
        apply (IHsource x (DR_Int z)) in H.
        + applyInstructionOrder.
            doesArithStep.
        + assumption.
    (* eqz *)
    - rewrite <- H3 in H0.
        clear t H1 H3.
        destructCompile H.
        apply (IHsource x (DR_Int z)) in H. 
        + applyInstructionOrder.
            destruct z; doesBoolStep.
        + assumption.
    (* if *)
    - rewrite <- H3 in *.
        clear H1 H2 H3 H4 t_if t_then t_else.
        destructCompile H.
        remember H.
        clear Heqe.
        apply (IHsource1 x (DR_Bool #f)) in H.
        + applyInstructionOrder.
            simpl.
            simpl in H.
            destruct v.
            * econstructor.
                -- eapply W_ST_32IfFalse; constructor.
                -- simpl. 
                    assert (Hcompile3: exists (compile3:wasmCode), compile_unsafe source3 = compile3).
                    ++ apply existsCompiledForDupe.
                    ++ destruct Hcompile3.
                        apply (IHsource3 x (DR_Int z)) in H1.
                        ** applyInstructionOrder.
                            constructor.
                        ** assumption.
            * econstructor.
                -- eapply W_ST_32IfFalse;constructor.
                -- simpl. 
                    assert (Hcompile3: exists (compile3:wasmCode), compile_unsafe source3 = compile3).
                    ++ apply existsCompiledForDupe.
                    ++ destruct Hcompile3.
                        apply (IHsource3 x (DR_Bool b)) in H1.
                        ** applyInstructionOrder.
                            constructor.
                        ** assumption.
            * econstructor.
                -- eapply W_ST_32IfFalse;constructor.
                -- simpl. 
                    assert (Hcompile3: exists (compile3:wasmCode), compile_unsafe source3 = compile3).
                    ++ apply existsCompiledForDupe.
                    ++ destruct Hcompile3.
                        apply (IHsource3 x (DR_Error)) in H1.
                        ** applyInstructionOrder.
                            constructor.
                        ** assumption.
            


    
Admitted.

