Require Import Bool List ZArith.
Require Import String.

Local Open Scope Z_scope.

(* based on the dupe language 
https://www.cs.umd.edu/class/spring2022/cmsc430/Dupe.html *)

Inductive dupeUniaryOp : Type :=
| D_U_add1 
| D_U_sub1 
| D_U_zero
| D_U_not
.

Definition uniOpToString (u :dupeUniaryOp) : string := match u with 
| D_U_add1 => "add1"
| D_U_sub1 => "sub1"
| D_U_zero => "zero?"
| D_U_not => "!"
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


Definition typeToString (t:dupeType) : string := match t with 
| D_type_Int => "Int"
| D_type_Bool => "Bool"
| D_type_Error => "Error"
end.

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

Definition uniOpTypeSignatureForReturn op t := 
    let signatureList := uniOpTypeSignature op in 
    let fix search lst := match lst with 
    | (accepts,returns)::tail => if typeSame returns t 
            then Some (accepts,returns)
            else search tail 
    | nil => None
    end in search signatureList
.

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


Theorem evalTypesSame:
    forall src val type,
        src d==> (type, val) ->
        resultType val = type.
Proof.
    induction src; intros;
    destruct val; destruct type; (try reflexivity); simpl in *;
    try (solve [inversion H]);
    try (
        destruct d; inversion H; subst; destruct H5; inversion H0; subst;
        (eapply (IHsrc v) in H3);
        destruct v
    );
    try (discriminate);
    try (solve [inversion H; subst; 
                eapply IHsrc3 in H7; eapply IHsrc2 in H6; 
                (try discriminate)
        ]).
Qed.

Ltac copyHypothesis H := 
    let tmp := fresh "H" in 
    let eq := fresh "eq" in
    remember H as tmp eqn: eq; clear eq
.

Ltac rewriteLeft := match goal with 
| H: ?l = _ |- context[?l] => rewrite -> H
| H: ?l = _, H0: context[?l] |- _ => rewrite -> H in H0
| _ => fail
end.
Ltac rewriteRight := match goal with 
| H: _ = ?r |- context[?r] => rewrite <- H
| H: _ = ?r, H0: context[?r] |- _ => rewrite <- H in H0
| _ => fail
end.


Ltac specializeIH := match goal with 
| IH: ?hyp -> ?prop, H: ?hyp |- _ => specialize (IH H)

| H: ?src d==> (?type, ?val),
    IH: forall val : dupeResult, 
    ?src d==> (resultType val, val) -> evalDupe ?src = val |- _ =>

    let tmp := fresh "H" in 
    let eq := fresh "eq" in
    remember H as tmp eqn: eq; clear eq;
    specialize (IH val);
    eapply evalTypesSame in tmp; rewrite tmp in IH;
    specialize (IH H);
    clear tmp

| IH: forall val: dupeResult,
    evalDupe ?src = val -> _ |- _ => specialize (IH (evalDupe src))

| IH: ?a = ?a -> _ |- _ => 
    let tmp := fresh "H" in 
    assert (a = a) as tmp;[reflexivity | (specialize (IH tmp));clear tmp]

| IH: (?t1 <> ?t2) -> _ |-  _ => 
    let tmp := fresh "H" in 
    assert (t1 <> t2) as tmp;[
        solve[discriminate]|
        specialize (IH tmp); clear tmp
    ]
end.


Ltac solveUniOp := 
    (repeat specializeIH);
    repeat (
        (try assumption);
        (try discriminate);
        (try contradiction);
        (try reflexivity);
        match goal with 
        | dUniop: dupeUniaryOp, dResult: dupeResult |- _ => 
            destruct dUniop; destruct dResult; simpl in *;
            (try discriminate)
        | H: uniOpTransform ?op (evalDupe ?src) = ?val |- (D_UniOp ?op ?src) d==> (_,?val) =>
            rewrite <- H
        | |- (D_UniOp ?op ?src) d==> (?type, uniOpTransform ?op ?srcResult) => 
            apply (E_D_UniOp src srcResult (resultType srcResult) op type)
        | H: uniOpTransform ?op ?srcVal = ?val |- In (resultType ?srcVal, ?resType) (uniOpTypeSignature ?op) => 
            destruct srcVal; solve[(try discriminate H); (try contradiction); repeat ((left; reflexivity) || right)]
        | IH: resultType ?srcResult <> D_type_Error -> _,
            H0: uniOpTransform ?op ?srcResult = ?result |- _ => 
            destruct srcResult; (try discriminate H0); simpl in IH
        | IH: ?t1 <> ?t2 -> _ |-  _ => 
            let tmp := fresh "H" in
            assert (t1 <> t2) as tmp; [
                solve[discriminate]|
                specialize (IH tmp); clear tmp
            ]
        | H: ?val1 = ?val2 |- uniOpTransform ?op ?val1 = uniOpTransform ?op ?val2 =>
            rewrite H
        | H : _ \/ _ |- _ => destruct H
        | H : _ /\ _ |- _ => destruct H
        | H: ?l = _ |- context[?l] => rewrite -> H
        | H: ?l = _, H0: context[?l] |- _ => rewrite -> H in H0
        | _ => idtac "fail";fail
        end
    ).

Ltac solveIfs := repeat (match goal with 
| H: dupeResult |- _ => destruct H
| |- evalDupe (D_if ?src1 ?src2 ?src3) = _ => simpl
end); try match goal with 
| H: D_if ?src1 ?src2 ?src3 d==> (_,_) |- _ => inversion H;subst
end;
repeat specializeIH;
repeat (
(try discriminate);
(try contradiction);
(try reflexivity);
match goal with 
| H: evalDupe (D_if ?src1 ?src2 ?src3) = _ |- _ => 
    simpl in H; destruct (evalDupe src1); 
    destruct (evalDupe src2); destruct (evalDupe src3);
    simpl in *
| IH: (?t1 <> ?t2) -> _ |-  _ => 
    let tmp := fresh "H" in 
    assert (t1 <> t2) as tmp;[
        solve[discriminate]|
        specialize (IH tmp); clear tmp
    ]
| H: context[if ?b then _ else _] |- _ => destruct b
| H: ?l = _ |- context[?l] => rewrite -> H
| H: ?l = _, H0: context[?l] |- _ => rewrite -> H in H0
| Hsrc1: ?src1 d==> (D_type_Int, DR_Int ?z),
    Hsrc2: ?src2 d==> (?evalType, ?valThen),
    Hsrc3: ?src3 d==> (?evalType, ?valElse)
    |- (D_if ?src1 ?src2 ?src3) d==> (?evalType, ?valThen) => 
        apply (E_D_ifInt src1 z src2 valThen src3 valElse evalType); assumption
| Hsrc1: ?src1 d==> (D_type_Bool, DR_Bool true),
    Hsrc2: ?src2 d==> (?evalType, ?valThen),
    Hsrc3: ?src3 d==> (?evalType, ?valElse)
    |- (D_if ?src1 ?src2 ?src3) d==> (?evalType, ?valThen) => 
        apply (E_D_ifTrue src1 src2 valThen src3 valElse evalType); assumption
| Hsrc1: ?src1 d==> (D_type_Bool, DR_Bool false),
    Hsrc2: ?src2 d==> (?evalType, ?valThen),
    Hsrc3: ?src3 d==> (?evalType, ?valElse)
    |- (D_if ?src1 ?src2 ?src3) d==> (?evalType, ?valElse) => 
        apply (E_D_ifFalse src1 src2 valThen src3 valElse evalType); assumption
| H: ?src d==> (?type, ?value) |- context[typeSame (resultType ?value) ?type] =>
    let new := fresh "H" in 
    let eq := fresh "eq" in
    remember H as new eqn: eq; clear eq;
    apply evalTypesSame in new;
    rewrite new
| H: ?src d==> (?type, ?value) |- context[typeSame ?type (resultType ?value)] =>
    let new := fresh "H" in 
    let eq := fresh "eq" in
    remember H as new eqn: eq; clear eq;
    apply evalTypesSame in new;
    rewrite new
end
).




Theorem evalDupe_implies_dupeEval: 
    forall src val,
    evalDupe src = val ->
    ((resultType val) <> D_type_Error) ->
    src d==> (resultType val, val).
Proof.
    induction src; intros;
    try (simpl in *; subst; constructor).
    - solveUniOp.
    - solveIfs.
Qed.




Theorem dupeEval_implies_evalDupe: 
    forall src val,
    src d==> (resultType val, val) ->
    evalDupe src = val.
Proof.
    induction src; intros; (try (inversion H; subst; reflexivity)).
    - inversion H; subst. solveUniOp.
    - solveIfs.
Qed.

Theorem dupeNotEvalError:
forall src val,
    src d==> (resultType val, val) ->
    ((resultType val) <> D_type_Error).
Proof.
    induction src; intros;
    try (inversion H; subst; discriminate).
    - solveUniOp.
    - repeat (match goal with 
    | H: dupeResult |- _ => destruct H
    | |- evalDupe (D_if ?src1 ?src2 ?src3) = _ => simpl
    end).
    try match goal with 
    | H: D_if ?src1 ?src2 ?src3 d==> (_,_) |- _ => inversion H;subst
    end.
    repeat specializeIH.
    repeat (
    (try discriminate);
    (try contradiction);
    (try reflexivity);
    match goal with 
    | H: evalDupe (D_if ?src1 ?src2 ?src3) = _ |- _ => 
        simpl in H; destruct (evalDupe src1); 
        destruct (evalDupe src2); destruct (evalDupe src3);
        simpl in *
    | IH: (?t1 <> ?t2) -> _ |-  _ => 
        let tmp := fresh "H" in 
        assert (t1 <> t2) as tmp;[
            solve[discriminate]|
            specialize (IH tmp); clear tmp
        ]
    | H: context[if ?b then _ else _] |- _ => destruct b
    | H: ?l = _ |- context[?l] => rewrite -> H
    | H: ?l = _, H0: context[?l] |- _ => rewrite -> H in H0
    | Hsrc1: ?src1 d==> (D_type_Int, DR_Int ?z),
        Hsrc2: ?src2 d==> (?evalType, ?valThen),
        Hsrc3: ?src3 d==> (?evalType, ?valElse)
        |- (D_if ?src1 ?src2 ?src3) d==> (?evalType, ?valThen) => 
            apply (E_D_ifInt src1 z src2 valThen src3 valElse evalType); assumption
    | Hsrc1: ?src1 d==> (D_type_Bool, DR_Bool true),
        Hsrc2: ?src2 d==> (?evalType, ?valThen),
        Hsrc3: ?src3 d==> (?evalType, ?valElse)
        |- (D_if ?src1 ?src2 ?src3) d==> (?evalType, ?valThen) => 
            apply (E_D_ifTrue src1 src2 valThen src3 valElse evalType); assumption
    | Hsrc1: ?src1 d==> (D_type_Bool, DR_Bool false),
        Hsrc2: ?src2 d==> (?evalType, ?valThen),
        Hsrc3: ?src3 d==> (?evalType, ?valElse)
        |- (D_if ?src1 ?src2 ?src3) d==> (?evalType, ?valElse) => 
            apply (E_D_ifFalse src1 src2 valThen src3 valElse evalType); assumption
    | H: ?src d==> (?type, ?value) |- context[typeSame (resultType ?value) ?type] =>
        let new := fresh "H" in 
        let eq := fresh "eq" in
        remember H as new eqn: eq; clear eq;
        apply evalTypesSame in new;
        rewrite new
    | H: ?src d==> (?type, ?value) |- context[typeSame ?type (resultType ?value)] =>
        let new := fresh "H" in 
        let eq := fresh "eq" in
        remember H as new eqn: eq; clear eq;
        apply evalTypesSame in new;
        rewrite new
    end
    ). 
    
        
