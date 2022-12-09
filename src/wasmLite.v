Require Import List ZArith.
Local Open Scope Z_scope.

Require Import utils.

Inductive wasm_dataRepresentation: Type :=
| W_DR_int
| W_DR_na
.

Inductive wasm_size: Type :=
| W_Sz_32
| W_Sz_64
| W_Sz_na
.

Definition wasmType := ( wasm_dataRepresentation * wasm_size)%type.


Inductive wasmValue : Type :=
| v_i64: i64 -> wasmValue
| v_i32: i32 -> wasmValue
| trap
.

Definition typeOfValue val := match val with 
| v_i64 _ => (W_DR_int,W_Sz_64)
| v_i32 _ => (W_DR_int,W_Sz_32)
| trap => (W_DR_na,W_Sz_na)
end.

Inductive wasm_binop: Type := 
| W_bin_add 
| W_bin_sub
.

Definition binopOperation op x y := match (op,x,y) with 
| (W_bin_add, v_i64 x' ,v_i64 y' ) => v_i64 (y' + x')
| (W_bin_add, v_i32 x' ,v_i32 y' ) => v_i32 (y' + x')
| (W_bin_sub, v_i64 x' ,v_i64 y' ) => v_i64 (y' - x')
| (W_bin_sub, v_i32 x' ,v_i32 y' ) => v_i32 (y' - x')
| _ => trap
end.


Inductive wasm_itestop: Type := 
| W_itest_eqz
.

Definition testopOperation op x := match (op,x) with 
| (W_itest_eqz, v_i64 x') => v_i32 (if (x' =? 0) then 1 else 0)
| (W_itest_eqz, v_i32 x') => v_i32 (if (x' =? 0) then 1 else 0)
| _ => trap
end.


(* based on definitions laid out here: 
   https://webassembly.github.io/spec/core/intro/index.html *)

Inductive wasmInstruction : Type :=
| i64_const: i64 -> wasmInstruction (* adds i64 to stack*)
| i32_const: i32 -> wasmInstruction (* adds i32 to stack*)

| inn_ibinop: wasm_size-> wasm_binop -> wasmInstruction
| inn_itestop: wasm_size-> wasm_itestop -> wasmInstruction

(* pops a value (i64 or i32) from the stack, 
    if zero then add else branch to code otherwise add if branch to code*)
| ifThenElse: (list wasmInstruction) -> (list wasmInstruction) -> wasmInstruction 
| nop: wasmInstruction
| unreachable: wasmInstruction
.



Notation "'i64.const' x" := (i64_const x) (at level 99).
Notation "'i32.const' x" := (i32_const x) (at level 99).

Notation "'i64.add'" := (inn_ibinop W_Sz_64 W_bin_add) (at level 99).
Notation "'i64.sub'" := (inn_ibinop W_Sz_64 W_bin_sub) (at level 99).
Notation "'i64.eqz'" := (inn_itestop W_Sz_64 W_itest_eqz) (at level 99).

Notation "'i32.add'" := (inn_ibinop W_Sz_32 W_bin_add) (at level 99).
Notation "'i32.sub'" := (inn_ibinop W_Sz_32 W_bin_sub) (at level 99).
Notation "'i32.eqz'" := (inn_itestop W_Sz_32 W_itest_eqz) (at level 99).

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

| W_ST_inn_ibinop: forall C C' st x y st' sz ibinop,
    C = (inn_ibinop sz ibinop)::C' ->
    st = x::y::st' ->
    typeOfValue x = (W_DR_int, sz) ->
    typeOfValue y = (W_DR_int, sz) ->
    (C,st) w--> (C', (binopOperation ibinop x y)::st') 

| W_ST_inn_itestop: forall C C' st z st' sz itestop,
    C = (inn_itestop sz itestop)::C' ->
    st = z::st' -> 
    typeOfValue z = (W_DR_int,sz) ->
    (C,st) w--> (C', (testopOperation itestop z)::st')

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
forall C C' s v v',
(C , s) w-->* (nil,v) ->
(C',v) w-->* (nil,v') ->
(C++C',nil) w-->* (nil,v').
Proof.
    Admitted.
