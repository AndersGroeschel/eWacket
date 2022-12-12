Require Import Bool List ZArith.

Local Open Scope Z_scope.

Require Import definition.

Inductive dupeResult : Type :=
| DR_Int: Z -> dupeResult
| DR_Bool: bool -> dupeResult
| DR_Error: dupeResult
.

Definition resultType result := match result with 
| DR_Int _ => D_type_Int
| DR_Bool _ => D_type_Bool
| DR_Error => D_type_Error
end.


Definition uniOpTransform op result := match (op, result) with 
| (D_U_add1, DR_Int z) => DR_Int (z + 1)
| (D_U_sub1, DR_Int z) => DR_Int (z - 1)
| (D_U_zero, DR_Int z) => DR_Bool (z =? 0)
| (D_U_not, DR_Bool b) => DR_Bool (negb b)
| _ => DR_Error
end.


Fixpoint evalDupe(d : dupe) := match d with 
| (D_Integer z) => (DR_Int z)
| (D_Boolean b) => (DR_Bool b)
| (D_UniOp op exp) => uniOpTransform op (evalDupe exp)
| (D_if e1 e2 e3) => match (evalDupe e1, evalDupe e2, evalDupe e3) with 
    | (DR_Bool b, res1, res2) => 
        if (typeSame (resultType res1) (resultType res2)) && (negb (typeSame (resultType res1) D_type_Error))
        then if b then res1 else res2
        else DR_Error
    | (DR_Int _, res1, res2 ) =>
        if (typeSame (resultType res1) (resultType res2)) && (negb (typeSame (resultType res1) D_type_Error))
        then res1
        else DR_Error
    | _ => DR_Error
    end
end.


(* this will probably have to be changed because of how integers are represented in binary*)
Reserved Notation " src 'd==>' val " (at level 50, left associativity).
Inductive dupeEval: dupe -> (dupeType * dupeResult)%type -> Prop :=
| E_D_Interger: forall z, (D_Integer z) d==> (D_type_Int, (DR_Int z))
| E_D_Boolean: forall b, (D_Boolean b) d==> (D_type_Bool ,(DR_Bool b))

| E_D_UniOp: forall t v inputType op evalType,
    t d==> (inputType, v) ->
    In (inputType, evalType) (uniOpTypeSignature op) ->
    (D_UniOp op t) d==> (evalType,(uniOpTransform op v))

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
