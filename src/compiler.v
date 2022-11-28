Require Import wacket.
Require Import observable.

Inductive compilerResult : Type :=
| Succ : wasm -> compilerResult
| Error : string -> compilerResult
.


(* the compiler from wacket to wasm, if *)
Fixpoint wasmCompiler (source : wack) : compilerResult := Error "not implemented" .
