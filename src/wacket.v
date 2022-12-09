Require Import Bool List ZArith.
Require Import String.

Local Open Scope Z_scope.

(* based on the dupe language 
https://www.cs.umd.edu/class/spring2022/cmsc430/Dupe.html *)

Inductive dupeUniaryOp : Type :=
| D_U_add1 
| D_U_sub1 
| D_U_zero
.

Definition uniOpToString (u :dupeUniaryOp) : string := match u with 
| D_U_add1 => "add1"
| D_U_sub1 => "sub1"
| D_U_zero => "zero?"
end.

Inductive dupe: Type :=
| D_Integer: Z -> dupe
| D_Boolean: bool -> dupe
| D_UniOp: dupeUniaryOp -> dupe -> dupe
| D_if: dupe -> dupe -> dupe -> dupe
.

Notation "#t" := true.
Notation "#f" := false.

Notation " 'add1' " := D_U_add1.
Notation " 'sub1' " := D_U_sub1.
Notation " 'zero?' " := D_U_zero.

Notation "'(' 'Int' z ')'" := (D_Integer z).
Notation "'(' 'Bool' b ')'" := (D_Boolean b).
Notation "'(' 'Prim1' op exp ')'" := (D_UniOp op exp).
Notation "'(' 'If' b 'Then' t 'Else' e ')'" := (D_if b t e).

Inductive typ: Type :=
| typ_Int
| typ_Bool
| typ_Error
.

Definition typeToString (t:typ) : string := match t with 
| typ_Int => "Int"
| typ_Bool => "Bool"
| typ_Error => "Error"
end.

Inductive dupeResult : Type :=
| DR_Int: Z -> dupeResult
| DR_Bool: bool -> dupeResult
| DR_Error: dupeResult
.

Definition resultType result := match result with 
| DR_Int _ => typ_Int
| DR_Bool _ => typ_Bool
| DR_Error => typ_Error
end.

Definition uniOpExpectedType op := match op with 
| D_U_add1 => typ_Int
| D_U_sub1 => typ_Int
| D_U_zero => typ_Int
end. 

Definition uniOpResultType op := match op with 
| D_U_add1 => typ_Int
| D_U_sub1 => typ_Int
| D_U_zero => typ_Bool
end. 

Definition UniOpTransform op result := match (op, result) with 
| (D_U_add1, DR_Int z) => DR_Int (z + 1)
| (D_U_sub1, DR_Int z) => DR_Int (z - 1)
| (D_U_zero, DR_Int z) => DR_Bool (z =? 0)
| _ => DR_Error
end.

Fixpoint evalDupe(d : dupe) := match d with 
| (D_Integer z) => (DR_Int z)
| (D_Boolean b) => (DR_Bool b)
| D_UniOp op exp => UniOpTransform op (evalDupe exp)
| (D_if e1 e2 e3) => match (evalDupe e1) with 
    | DR_Int i => evalDupe e2
    | DR_Bool b => if b then evalDupe e2  else evalDupe e3 
    | DR_Error => DR_Error
    end
end.


(* this will probably have to be changed because of how integers are represented in binary*)
Reserved Notation " t 'd==>' n " (at level 50, left associativity).
Inductive dupeEval: dupe -> dupeResult -> Prop :=
| E_D_Interger: forall z, (D_Integer z) d==> (DR_Int z)
| E_D_Boolean: forall b, (D_Boolean b) d==> (DR_Bool b)

| E_D_UniOp: forall t v op,
    t d==> v ->
    (resultType v) = (uniOpExpectedType op) ->
    (D_UniOp op t) d==> (UniOpTransform op v)

| E_D_ifFalse: forall t_if t_then t_else v,
    t_if d==> (DR_Bool false) -> 
    t_else d==> v ->
    (D_if t_if t_then t_else) d==> v
| E_D_ifTrue: forall t_if t_then v t_else ,
    t_if d==> (DR_Bool true) -> 
    t_then d==> v ->
    (D_if t_if t_then t_else) d==> v
| E_D_ifInt: forall t_if z t_then v t_else ,
    t_if d==> (DR_Int z) -> 
    t_then d==> v ->
    (D_if t_if t_then t_else) d==> v

where " t 'd==>' n " := (dupeEval t n).
