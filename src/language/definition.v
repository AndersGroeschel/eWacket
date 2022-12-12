Require Import Bool List ZArith.

Local Open Scope Z_scope.

(* based on the dupe language 
https://www.cs.umd.edu/class/spring2022/cmsc430/Dupe.html *)

Inductive dupeType: Type :=
| D_type_Int
| D_type_Bool
| D_type_Error
.

Definition typeSame t1 t2 := match (t1,t2) with 
| (D_type_Int,D_type_Int) => true
| (D_type_Bool,D_type_Bool) => true
| (D_type_Error,D_type_Error) => true
| _ => false
end.



Inductive dupeUniaryOp : Type :=
| D_U_add1 
| D_U_sub1 
| D_U_zero
| D_U_not
.

Definition uniOpTypeSignature op := match op with 
| D_U_add1 => (D_type_Int,D_type_Int)::nil
| D_U_sub1 => (D_type_Int,D_type_Int)::nil
| D_U_zero => (D_type_Int,D_type_Bool)::nil
| D_U_not => (D_type_Bool,D_type_Bool)::nil
end. 

Definition uniOpAcceptsType op typ := 
    let (accepts,returns) := split (uniOpTypeSignature op) in
    In typ accepts
. 

Definition uniOpTypeSignatureForAccept op t := 
    let signatureList := uniOpTypeSignature op in 
    let fix search lst := match lst with 
    | (accepts,returns)::tail => if typeSame accepts t 
            then Some (accepts,returns)
            else search tail 
    | nil => None
    end in search signatureList
.



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

Fixpoint typeOfDupe (source :dupe) := match source with 
| D_Integer _ => D_type_Int
| D_Boolean _ => D_type_Bool
| D_UniOp op exp => let t := typeOfDupe exp in 
    match uniOpTypeSignatureForAccept op t with 
    | Some (accepts,returns) => returns
    | None => D_type_Error
    end
| D_if b t e => match (typeOfDupe b, typeOfDupe t, typeOfDupe e ) with 
    | (D_type_Bool,t1,t2) => if typeSame t1 t2 then t1 else D_type_Error
    | (D_type_Int,t1,t2) => if typeSame t1 t2 then t1 else D_type_Error
    | _ => D_type_Error
    end
end.



