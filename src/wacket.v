Require Import Bool List ZArith.



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

Notation "#t" := true.
Notation "#f" := false.

Notation "'(' 'Int' z ')'" := (D_Integer z).
Notation "'(' 'Bool' b ')'" := (D_Boolean b).
Notation "'(' 'add1' e ')'" := (D_add1 e).
Notation "'(' 'sub1' e ')'" := (D_sub1 e).
Notation "'(' 'zero?' e ')'" := (D_zero e).
Notation "'(' 'If' b 'Then' t 'Else' e ')'" := (D_if b t e).

Inductive dupeResult : Type :=
| DR_Int: Z -> dupeResult
| DR_Bool: bool -> dupeResult
| DR_Error: dupeResult
.

Fixpoint evalDupe(d : dupe) := match d with 
| (Int z) => (DR_Int z)
| (Bool b) => (DR_Bool b)
| (add1 e) => match (evalDupe e) with 
    | DR_Int i => DR_Int (i + 1)
    | DR_Bool b => DR_Error
    | DR_Error => DR_Error
    end
| (sub1 e) => match (evalDupe e) with 
    | DR_Int i => DR_Int (i - 1)
    | DR_Bool b => DR_Error
    | DR_Error => DR_Error
    end
| (zero? e) => match (evalDupe e) with 
    | DR_Int i => DR_Bool (Z.eqb i 0)
    | DR_Bool b => DR_Error
    | DR_Error => DR_Error
    end
| (If e1 Then e2 Else e3) => match (evalDupe e1) with 
    | DR_Int i => evalDupe e2
    | DR_Bool b => if b then evalDupe e2  else evalDupe e3 
    | DR_Error => DR_Error
    end
end.

Inductive dupeType: Type :=
| D_type_Int
| D_type_Bool
| D_type_Error
.

Definition typeOfDupeResult d := match d with 
| DR_Int _ => D_type_Int
| DR_Bool _ => D_type_Bool
| DR_Error => D_type_Error
end.


(* this will probably have to be changed because of how integers are represented in binary*)
Reserved Notation " src 'd==>' val " (at level 50, left associativity).
Inductive dupeEval: dupe -> (dupeType * dupeResult)%type -> Prop :=
| E_D_Interger: forall z, (D_Integer z) d==> (D_type_Int, (DR_Int z))
| E_D_Boolean: forall b, (D_Boolean b) d==> (D_type_Bool ,(DR_Bool b))

| E_D_add1: forall t z, 
    t d==> (D_type_Int, DR_Int z) ->
    (D_add1 t) d==> (D_type_Int, DR_Int (z + 1))
| E_D_sub1: forall t z, 
    t d==> (D_type_Int,DR_Int z) ->
    (D_sub1 t) d==> (D_type_Int,DR_Int (z - 1))

| E_D_isZero: forall t z,
    t d==> (D_type_Int,DR_Int z) ->
    (D_zero t) d==> (D_type_Bool, DR_Bool (Z.eqb z 0))

| E_D_ifFalse: forall t_if t_then vt t_else ve evalType,
    t_if d==> (D_type_Bool,(DR_Bool false)) -> 
    t_then d==> (evalType,vt) ->
    t_else d==> (evalType,ve) ->
    (D_if t_if t_then t_else) d==> (evalType,ve)
| E_D_ifTrue: forall t_if t_then vt t_else ve evalType,
    t_if d==> (D_type_Bool,(DR_Bool true)) -> 
    t_then d==> (evalType,vt) ->
    t_else d==> (evalType,ve) ->
    (D_if t_if t_then t_else) d==> (evalType,vt)
| E_D_ifInt: forall t_if z t_then vt t_else ve evalType,
    t_if d==> (D_type_Int,(DR_Int z)) -> 
    t_then d==> (evalType,vt) ->
    t_else d==> (evalType,ve) ->
    (D_if t_if t_then t_else) d==> (evalType,vt)

where " src 'd==>' val " := (dupeEval src val).
