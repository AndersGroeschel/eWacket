Require Import definition.
Require Import eval.

Require Import helperTactics.

Require Import List.


Theorem TypeOfDupe_same_as_Eval:
    forall src type val,
        src d==> (type, val) -> 
        typeOfDupe src = type.
Proof.
    evalAuto.
Qed.
    

Theorem evalDupe_implies_dupeEval: 
    forall src val,
    evalDupe src = val ->
    ((resultType val) <> D_type_Error) ->
    src d==> (resultType val, val).
Proof.
    evalAuto.
Qed.


Theorem dupeEval_implies_evalDupe: 
    forall src val,
    src d==> (resultType val, val) ->
    evalDupe src = val.
Proof.
    evalAuto.
Qed.


Theorem dupeNotEvalError:
forall src val,
    src d==> (resultType val, val) ->
    ((resultType val) <> D_type_Error).
Proof.
    evalAuto.
Qed.


Theorem evalEquivalence: 
    forall src val,
    src d==> (resultType val, val) <-> ((evalDupe src = val) /\ ((resultType val) <> D_type_Error)).
Proof.
    intros. 
    split.
    - split.
        + apply dupeEval_implies_evalDupe. assumption.
        + apply (dupeNotEvalError src). assumption.
    - intros. 
        destruct H.
        apply  evalDupe_implies_dupeEval.
        + assumption.
        + assumption.
Qed.



