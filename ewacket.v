Require Import Arith Bool List ZArith.
Require Import String. Local Open Scope string.


Inductive wack: Type :=
| S_Int: Z -> wack 
| S_Plus: wack -> wack -> wack
| S_Minus: wack -> wack -> wack
| S_Mult: wack -> wack -> wack
| S_Div: wack -> wack -> wack
| S_Eq: wack -> wack -> wack

| S_Bool: bool -> wack
| S_And: wack -> wack -> wack
| S_Or: wack -> wack -> wack
| S_Not: wack -> wack

| S_IfElse: wack -> wack -> wack -> wack 
(* maybe function calls or something I don't 
know everything thats supposed to be in this language*)
.

(* don't know how to do notation for integers or bools*)
Notation "x + y" := (S_Plus x y).
Notation "x - y" := (S_Minus x y).
Notation "x * y" := (S_Mult x y).
Notation "x / y" := (S_Div x y).
Notation "x = y" := (S_Eq x y).

Notation "a && b" := (S_And a b).
Notation "a || b" := (S_Or a b).
Notation "! a" := (S_Not a) (at level 99). (* don't know if that's the right level*)

Notation "'if' a 'then' x 'else' y" := 
    (S_IfElse a x y) (at level 89,
            a at level 99,
            x at level 99,
            y at level 99).


(* this should be taken from an open source project*)
Inductive wasm : Type :=

.

Inductive observable : Type :=
(* don't know how we want to define this yet, one option 
is to take printed values, another is to take output*)
| O_Int: Z -> observable
| O_Bool: bool -> observable
.

Reserved Notation " t 's==>' n " (at level 50, left associativity).
Inductive wackEval: wack -> observable -> Prop :=

| E_S_Int: forall n, (S_Int n) s==> (O_Int n)
| E_S_Bool: forall b, (S_Bool b) s==> (O_Bool b)

| E_S_Plus: forall t1 t2 v1 v2,
    t1 s==> (O_Int v1) -> t2 s==> (O_Int v2) ->
    (S_Plus t1 t2) s==> O_Int (v1 + v2)
| E_S_Minus: forall t1 t2 v1 v2,
    t1 s==> (O_Int v1) -> t2 s==> (O_Int v2) ->
    (S_Minus t1 t2) s==> O_Int (v1 - v2)
| E_S_Mult: forall t1 t2 v1 v2,
    t1 s==> (O_Int v1) -> t2 s==> (O_Int v2) ->
    (S_Mult t1 t2) s==> O_Int (v1 * v2)
| E_S_Div: forall t1 t2 v1 v2,
    t1 s==> (O_Int v1) -> t2 s==> (O_Int v2) ->
    (S_Div t1 t2) s==> O_Int (v1 / v2)
| E_S_Eq: forall t1 t2 v1 v2,
    t1 s==> (O_Int v1) -> t2 s==> (O_Int v2) ->
    (S_Eq t1 t2) s==> O_Bool (Z.eqb v1 v2)

| E_S_And: forall t1 t2 b1 b2,
    t1 s==> (O_Bool b1) -> t2 s==> (O_Bool b2) ->
    (S_And t1 t2) s==> O_Bool (b1 && b2)
| E_S_Or: forall t1 t2 b1 b2,
    t1 s==> (O_Bool b1) -> t2 s==> (O_Bool b2) ->
    (S_And t1 t2) s==> O_Bool (b1 || b2)
| E_S_Not: forall t b,
    t s==> (O_Bool b) ->
    (S_Not t) s==> O_Bool (negb b)

| E_S_IfElse_True: forall t1 t2 v2, 
    t1 s==> (O_Bool true) -> 
    t2 s==> v2 -> 
    forall t3, (S_IfElse t1 t2 t3) s==> v2
| E_S_IfElse_False: forall t1 t3 v3, 
    t1 s==> (O_Bool false) -> 
    t3 s==> v3 -> 
    forall t2, (S_IfElse t1 t2 t3) s==> v3


where " t 's==>' n " := (wackEval t n).


Reserved Notation " t 'c==>' n " (at level 50, left associativity).
Inductive wasmEval: wasm -> observable -> Prop :=
    
.


Inductive compilerResult : Type :=
| Succ : wasm -> compilerResult
| Error : string -> compilerResult
.







(* the compiler from wacket to wasm, if *)
Fixpoint wasmCompiler (source : wack) : compilerResult := Error "not implemented" .

Theorem semanticPreservation:
    forall (S : wack) (C : wasm), (wasmCompiler S) = (Succ C) ->
    (* the observable behavior of C improves on one of the allowed observable behaviors of ‍S *).
Proof.
    
Qed.







