Require Import List ZArith.
Local Open Scope Z_scope.

Require Import typeDefs.

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
Notation "'i64.add' ( x ) ( y )" := (i64_add) (at level 99).
Notation "'i64.sub' ( x ) ( y )" := (i64_sub) (at level 99).
Notation "'i64.eqz' ( x )" := (i64_eqz) (at level 99).
Notation "'if' '(then' t ) '(else' e )" := (ifThenElse t e) (at level 99).


Definition wasmStack := list wasmValue.

Definition wasmCode := list wasmInstruction.

Definition wasmState := (wasmCode * wasmStack)%type.

Definition wasmStepEval (st : wasmState) : wasmState := match st with 
(* any time we have trap on top then don't eval*)
| (_::rest, trap::st') => (rest,trap::st')
| ((i64_add)::rest, _::trap::st') => (rest,trap::st')
| ((i64_sub)::rest, _::trap::st') => (rest,trap::st')

(* good eval states*)
| ((i64_const z)::rest, st) => (rest, (v_i64 z)::st)
| ((i32_const z)::rest, st) => (rest, (v_i32 z)::st)
| ((i64_add)::rest, (v_i64 x)::(v_i64 y)::st') 
        => (rest, (v_i64 (x + y))::st')
| ((i64_sub)::rest, (v_i64 x)::(v_i64 y)::st') 
        => (rest, (v_i64 (x - y))::st')
| ((i64_eqz)::rest, (v_i64 z)::st') 
        => (rest,(v_i32 (if z =? 0 then 1 else 0))::st')
| ((ifThenElse t e)::rest, (v_i64 z)::st')
        => if Z.eqb 0 z then (e ++ rest, st') else (t ++ rest, st')
| ((ifThenElse t e)::rest, (v_i32 z)::st')
        => if Z.eqb 0 z then (e ++ rest, st') else (t ++ rest, st')
| (nop::rest, st) => (rest,st)
| (unreachable::rest, st) => (rest, trap::st)

(* bad eval states*)
| ((i64_add)::rest, _::st') => (rest,trap::st')
| ((i64_sub)::rest, _::st') => (rest,trap::st')
| ((i64_eqz)::rest, _::st') => (rest,trap::st')

| (i64_add::rest, nil) => (rest,trap::nil) 
| (i64_sub::rest, nil) => (rest,trap::nil) 
| (i64_eqz::rest, nil) => (rest,trap::nil) 
| ((ifThenElse _ _)::rest, nil) => (rest,trap::nil) 

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

