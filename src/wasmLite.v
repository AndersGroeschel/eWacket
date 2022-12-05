Require Import List ZArith.
Local Open Scope Z_scope.

Require Import utils.

(* based on definitions laid out here: 
   https://webassembly.github.io/spec/core/intro/index.html *)

Inductive wasmInstruction : Type :=
| i64_const: i64 -> wasmInstruction (* adds i64 to stack*)
| i32_const: i32 -> wasmInstruction (* adds i32 to stack*)
| i64_add: wasmInstruction (* pops 2 i64 from stack and pushes there sum*)
| i64_sub: wasmInstruction (* pops 2 i64 from stack and pushes there difference*)
| i64_eqz: wasmInstruction (* pops 1 i64 from stack and pushes an i32, 0 if false, 1 if true*)

(* pops a value (i64 or i32) from the stack, 
    if zero then add else branch to code otherwise add if branch to code*)
| ifThenElse: (list wasmInstruction) -> (list wasmInstruction) -> wasmInstruction 
| nop: wasmInstruction
| unreachable: wasmInstruction
.

Inductive wasmValue : Type :=
| v_i64: i64 -> wasmValue
| v_i32: i32 -> wasmValue
| trap
.


Notation "'i64.const' x" := (i64_const x) (at level 99).
Notation "'i32.const' x" := (i32_const x) (at level 99).
Notation "'i64.add'" := (i64_add) (at level 99).
Notation "'i64.sub'" := (i64_sub) (at level 99).
Notation "'i64.eqz'" := (i64_eqz) (at level 99).
Notation "'if' '(then' t ) '(else' e )" := (ifThenElse t e) (at level 99).


Definition wasmStack := list wasmValue.

Definition wasmCode := list wasmInstruction.

Definition wasmState := (wasmCode * wasmStack)%type.

Definition wasmStepEval (st : wasmState) : wasmState := match st with 
(* any time we have trap on top then don't eval*)
| (_::rest, trap::st') => (rest,trap::st')
| ((i64.add)::rest, _::trap::st') => (rest,trap::st')
| ((i64.sub)::rest, _::trap::st') => (rest,trap::st')

(* good eval states*)
| ((i64.const z)::rest, st) => (rest, (v_i64 z)::st)
| ((i32.const z)::rest, st) => (rest, (v_i32 z)::st)
| ((i64.add)::rest, (v_i64 x)::(v_i64 y)::st') 
        => (rest, (v_i64 (x + y))::st')
| ((i64.sub)::rest, (v_i64 x)::(v_i64 y)::st') 
        => (rest, (v_i64 (x - y))::st')
| ((i64.eqz)::rest, (v_i64 z)::st') 
        => (rest,(v_i32 (if z =? 0 then 1 else 0))::st')
| ((if (then t) (else e))::rest, (v_i64 z)::st')
        => if Z.eqb 0 z then (e ++ rest, st') else (t ++ rest, st')
| ((if (then t) (else e))::rest, (v_i32 z)::st')
        => if Z.eqb 0 z then (e ++ rest, st') else (t ++ rest, st')
| (nop::rest, st) => (rest,st)
| (unreachable::rest, st) => (rest, trap::st)

(* bad eval states*)
| ((i64.add)::rest, _::st') => (rest,trap::st')
| ((i64.sub)::rest, _::st') => (rest,trap::st')
| ((i64.eqz)::rest, _::st') => (rest,trap::st')

| (i64.add::rest, nil) => (rest,trap::nil) 
| (i64.sub::rest, nil) => (rest,trap::nil) 
| (i64.eqz::rest, nil) => (rest,trap::nil) 
| ((if (then _) (else _))::rest, nil) => (rest,trap::nil) 

| (nil,st) => (nil,st)
end.

Reserved Notation "st 'w-->' st'" (at level 50, left associativity).

Inductive wasmStepInd: wasmState -> wasmState -> Prop :=
| W_ST_64Const: forall C st z C',
    C = (i64_const z)::C' ->
    (C,st) w--> (C',((v_i64 z)::st))
| W_ST_32Const: forall C st z C',
    C = (i32_const z)::C' ->
    (C, st) w--> (C', ((v_i32 z)::st))
| W_ST_64Add: forall C C' st x y st',
    C = i64_add::C' ->
    st = (v_i64 x)::(v_i64 y)::st' ->
    (C, st) w--> (C', (v_i64 (x + y))::st')
| W_ST_64Sub: forall C C' st x y st',
    C = i64_sub::C' ->
    st = (v_i64 x)::(v_i64 y)::st' ->
    (C, st) w--> (C', (v_i64 (x - y))::st')

| W_ST_64EqzTrue: forall C C' st z st',
    C = i64_eqz::C' ->
    st = (v_i64 z)::st' ->
    (z = 0) -> 
    (C, st) w--> (C', (v_i32 1)::st')
| W_ST_64EqzFalse: forall C C' st z st',
    C = i64_eqz::C' ->
    st = (v_i64 z)::st' ->
    ~(z = 0) -> 
    (C, st) w--> (C', (v_i32 0)::st')


| W_ST_64IfTrue: forall C Ct Ce C' st z st',
    C = (ifThenElse Ct Ce)::C' ->
    st = (v_i64 z)::st' ->
    ~(z = 0) ->
    (C, st) w--> (Ct ++ C', st')
| W_ST_64IfFalse: forall C Ct Ce C' st z st',
    C = (ifThenElse Ct Ce)::C' ->
    st = (v_i64 z)::st' ->
    (z = 0) ->
    (C, st) w--> (Ce ++ C', st')

| W_ST_32IfTrue: forall C Ct Ce C' st z st',
    C = (ifThenElse Ct Ce)::C' ->
    st = (v_i32 z)::st' ->
    ~(z = 0) ->
    (C, st) w--> (Ct ++ C', st')
| W_ST_32IfFalse: forall C Ct Ce C' st z st',
    C = (ifThenElse Ct Ce)::C' ->
    st = (v_i32 z)::st' ->
    (z = 0) ->
    (C, st) w--> (Ce ++ C', st')

| W_ST_nop: forall C C' st,
    C = nop::C' ->
    (C,st) w--> (C',st)

| W_ST_unreachable: forall C C' st,
    C = unreachable::C' ->
    (C,st) w--> (C',trap::st)

where "st 'w-->' st'" := (wasmStepInd st st').



Definition wasmMultistepInd := multi wasmStepInd.

Notation "st 'w-->*' st'" := (wasmMultistepInd st st') (at level 40).

Definition wasmLite_terminates (C : wasmCode) : Prop :=
    exists stack_final, (C,nil) w-->* (nil,stack_final).


Lemma wasmLite_deterministic: 
forall st st' st'', 
st w--> st' -> st w--> st'' -> st' = st''.
Proof.
    intros. 
    inversion H; subst; 
    inversion H0; subst; 
    (try congruence).
Qed.

Theorem add_instruction_ok:
forall C v instr v',
(C,nil) w-->* (nil,v) ->
(instr::nil,v) w--> (nil,v') ->
(C ++ (instr::nil),nil) w-->* (nil,v').
Proof.
    Admitted.
    (*intros.
    inversion H0; subst.
    - inversion H2; subst. clear H2.
Qed.*)


Theorem instruction_order:
forall C C' v v',
(C , nil) w-->* (nil,v) ->
(C',v) w-->* (nil,v') ->
(C++C',nil) w-->* (nil,v').
Proof.
    Admitted.
    (*
    induction C'; intros.
    - rewrite app_nil_r. inversion H0; subst.
        + assumption.
        + inversion H1; discriminate.
    - 
*)

(*don't know for sure if we need this yet, 
        also would need assumption that prog is well typed
Theorem wasmLite_terminates_always: 
    forall Code, (wasmLite_terminates Code).
Proof.
    intros.
    unfold wasmLite_terminates.
    induction Code.
    - exists nil. apply multi_refl.
    - inversion IHCode.

Qed.
*)