Require Import Arith Bool List ZArith.
Require Import observable.


(* based on the dupe language 
https://www.cs.umd.edu/class/spring2022/cmsc430/Dupe.html *)

Inductive dupe: Type :=
| D_Integer: Z -> dupe
| D_Boolean: bool -> dupe
| D_add1: dupe -> dupe
| D_sub1: dupe -> dupe
| D_zero: dupe -> dupe
| D_if: dupe -> dupe -> dupe -> dupe
.


(* this will probably have to be changed because of how integers are represented in binary*)
Reserved Notation " t 'd==>' n " (at level 50, left associativity).
Inductive dupeEval: dupe -> observable -> Prop :=
| E_D_Interger: forall z, (D_Integer z) d==> (O_Int z)
| E_D_Boolean: forall b, (D_Boolean b) d==> (O_Bool b)

| E_D_add1: forall t z, 
    t d==> (O_Int z) ->
    (D_add1 t) d==> (O_Int (z + 1))
| E_D_sub1: forall t z, 
    t d==> (O_Int z) ->
    (D_sub1 t) d==> (O_Int (z - 1))

| E_D_isZero: forall t z,
    t d==> (O_Int z) ->
    (D_zero t) d==> (O_Bool (Z.eqb z 0))

| E_D_ifFalse: forall t_if t_then t_else v,
    t_if d==> (O_Bool false) -> 
    t_else d==> v ->
    (D_if t_if t_then t_else) d==> v
| E_D_ifTrue: forall t_if t_then v t_else ,
    t_if d==> (O_Bool true) -> 
    t_then d==> v ->
    (D_if t_if t_then t_else) d==> v
| E_D_ifInt: forall t_if z t_then v t_else ,
    t_if d==> (O_Int z) -> 
    t_then d==> v ->
    (D_if t_if t_then t_else) d==> v

where " t 'd==>' n " := (dupeEval t n).


