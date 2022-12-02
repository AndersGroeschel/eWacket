Require Import wacket.
Require Import observable.
Require Import String. Local Open Scope string.
Require Import wasmLite.


Inductive compilerResult : Type :=
| Succ : wasmLite -> compilerResult
| Error : string -> compilerResult
.

(* the compiler from wacket to wasm, if *)
Fixpoint wasmCompiler (source : dupe) := Error "not implemented" .
