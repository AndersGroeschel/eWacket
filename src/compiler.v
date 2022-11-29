Require Import wacket.
Require Import observable.
Require Import String. Local Open Scope string.

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
Fixpoint wasmCompiler (source : dupe) := Error "not implemented" .
