Require Import String. Local Open Scope string.
Require Import Arith Bool List ZArith.

Inductive wack: Type :=
| S_Int Int -> wack
| S_Plus: wack -> wack -> wack
| S_Minus: wack -> wack -> wack
| S_Mult: wack -> wack -> wack
| S_Div: wack -> wack -> wack

| S_Bool bool -> wack
| S_And wack -> wack -> wack
| S_Or wack -> wack -> wack
| S_Not wack -> wack

| S_IfElse wack -> wack -> wack -> wack 
(* maybe function calls or something I don't 
know everything thats supposed to be in this language*)
.

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







