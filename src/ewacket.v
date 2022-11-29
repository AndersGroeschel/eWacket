Require Import Arith Bool List ZArith.
Require Import wacket.
Require Import observable.
Require Import compiler.





Theorem semanticPreservation:
    forall (S : dupe) (C : wasm) (obs: observable), (wasmCompiler S) = (Succ C) ->
    (S d==> obs) -> (C c==> obs).
Proof.
Admitted.

