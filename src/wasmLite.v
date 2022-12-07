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
    (C, st) w--> (C', (v_i64 (y + x))::st')
| W_ST_64Sub: forall C C' st x y st',
    C = i64_sub::C' ->
    st = (v_i64 x)::(v_i64 y)::st' ->
    (C, st) w--> (C', (v_i64 (y - x))::st')

| W_ST_64Eqz: forall C C' st z st',
    C = i64_eqz::C' ->
    st = (v_i64 z)::st' ->
    (C, st) w--> (C', (v_i32 (if z =? 0 then 1 else 0))::st')

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
    (try congruence);
    destruct z;
    destruct z0; 
    simpl; 
    (try congruence).
Qed.

Theorem instruction_order:
forall C C' v v',
(C , nil) w-->* (nil,v) ->
(C',v) w-->* (nil,v') ->
(C++C',nil) w-->* (nil,v').
Proof.
    Admitted.
