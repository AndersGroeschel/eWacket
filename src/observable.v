Require Import Arith Bool List ZArith.

Inductive observable : Type :=
(* don't know how we want to define this yet, one option 
is to take printed values, another is to take output*)
| O_Int: Z -> observable
| O_Bool: bool -> observable
| O_Error
.
