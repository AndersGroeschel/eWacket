Require Import Arith Bool List ZArith.
Require Import String. Local Open Scope string.
Require Import wacket.
Require Import observable.


(* this should be taken from an open source project*)
Inductive wasm : Type :=

.

Reserved Notation " t 'c==>' n " (at level 50, left associativity).
Inductive wasmEval: wasm -> observable -> Prop :=
    
where " t 'c==>' n " := (wasmEval t n).


Inductive compilerResult : Type :=
| Succ : wasm -> compilerResult
| Error : string -> compilerResult
.




(* the compiler from wacket to wasm, if *)
Fixpoint wasmCompiler (source : wack) : compilerResult := Error "not implemented" .

Theorem semanticPreservation:
    forall (S : wack) (C : wasm) (obs: observable), (wasmCompiler S) = (Succ C) ->
    S s==> obs -> C c==> obs.
Proof.
    
Qed.







