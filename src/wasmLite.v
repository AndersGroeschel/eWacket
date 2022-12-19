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

Definition wasmStep code stack := match code with 
| (i64_const i)::rest=> (rest,(v_i64 i)::stack)
| (i32_const i)::rest => (rest,(v_i32 i)::stack)
| i64_add::rest => match stack with 
    | (v_i64 x)::(v_i64 y)::st' => (rest,(v_i64 (y + x))::st')
    | stack => (rest,trap::stack)
    end
| i64_sub::rest => match stack with 
    | (v_i64 x)::(v_i64 y)::st' => (rest,(v_i64 (y - x))::st')
    | stack => (rest,trap::stack)
    end
| i64_eqz::rest => match stack with 
    | (v_i64 z)::st' => (rest,(v_i32 (if z =? 0 then 1 else 0))::st')
    | stack => (rest,trap::stack)
    end
| (ifThenElse tExp eExp)::rest => match stack with 
    | (v_i32 z)::st' => if z =? 0 then ( eExp++rest,st') 
                    else (tExp++rest,st')
    | stack => (rest,trap::stack)
    end
| nil => (nil,stack)
end.


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

Lemma noIntruction_implies_sameState:
forall v v',
    (nil,v) w-->* (nil,v') ->
    v = v'.
Proof.
    intros.
    inversion H; subst.
    - reflexivity.
    - inversion H0; subst; discriminate.
Qed.

Ltac removeListNils := match goal with
| [|- context[_ ++ nil] ] => rewrite app_nil_r
| [|- context[nil ++ _] ] => rewrite app_nil_l
| [H: context[_ ++ nil] |- _ ] => rewrite app_nil_r  in H
| [H: context[nil ++ _] |- _ ] => rewrite app_nil_l  in H
end.



Print multi.

Theorem instruction_order:
forall C' C x y z,
(C , x) w-->* (nil,y) ->
(C', y) w-->* (nil,z) ->
(C++C',x) w-->* (nil,z).
Proof. 
    intros. generalize dependent C'. generalize dependent z.
    remember (C, x) as pre.
    remember (nil, y) as post.
    induction H; intros.
    - subst; inversion Heqpost; subst; removeListNils; assumption.
    - apply IHmulti; auto. rewrite <- Heqpre.
    (* We have x0 w--> y0 but we're trying to prove y0 = x0 so we might have an error here*)
Admitted.
