Require Import String. Local Open Scope string.
Require Import Arith Bool List ZArith.

Inductive wack: Type :=
(* note this needs to be changed to integers, 
I'm just lazy and haven't figured out the proper 
way to do this yet*)
| S_Int: nat -> wack 
| S_Plus: wack -> wack -> wack
| S_Minus: wack -> wack -> wack
| S_Mult: wack -> wack -> wack
| S_Div: wack -> wack -> wack

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
(* don't know how we want to define this yet, one option is to *)
.

Reserved Notation " t 's==>' n " (at level 50, left associativity).
Inductive wackEval: wack -> observable -> Prop :=

.


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







