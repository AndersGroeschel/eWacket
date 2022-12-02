Require Import Arith Bool List ZArith.


(* this might not be all of wasm we need*)
Inductive wasmLite : Type :=
| i64_const: Z -> wasmLite
| i64_add: wasmLite -> wasmLite -> wasmLite
| i64_sub: wasmLite -> wasmLite-> wasmLite
| i64_eqz: wasmLite -> wasmLite

| ifThenElse: wasmLite -> wasmLite -> wasmLite -> wasmLite
.

Notation "'i64.const' x" := (i64_const x) (at level 99).
Notation "'i64.add' ( x ) ( y )" := (i64_add x y) (at level 99).
Notation "'i64.sub' ( x ) ( y )" := (i64_sub x y) (at level 99).
Notation "'i64.eqz' ( x )" := (i64_eqz x) (at level 99).
Notation "'if' ( b ) ( t ) ( e )" := (ifThenElse b t e) (at level 99).



