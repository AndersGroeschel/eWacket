Require Import Arith Bool List ZArith.
Local Open Scope Z_scope.

Require Import wacket.
Require Import wasmLite.
Require Import compiler.




Definition dupeResult_to_wasmVal (res: dupeResult) :=
match res with 
| DR_Int z => v_i64 z
| DR_Bool b => if b then v_i32 1 else v_i32 0
| DR_Error => trap
end.

(* going to need that dupe is well typed, 
and therefor evalDupe cannot produce an error, 
honestly this should be a feature of the compiler*)
Theorem semanticPreservation:
    forall source compiled result,
    (compile_unsafe source) = compiled ->
    (dupeResult_to_wasmVal (evalDupe source)) = result ->
    (compiled,nil) w-->* ((nil, result::nil)).
Proof.
    induction source; intros;
    (try (
        rewrite <- H;rewrite <- H0;
        (try destruct b);
        econstructor;constructor; reflexivity
    )).
    - simpl in H. 
        rewrite <- (app_nil_l compiled) in H. 
        apply app_eq_app in H. 
        do 3 destruct H.
        + rewrite app_nil_l in H.
            simpl in H0.

    
Admitted.

