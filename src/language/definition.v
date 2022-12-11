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


Ltac evalPreamble := 
try match goal with 
| |- forall (src : dupe) (val : dupeResult), src d==> (resultType val, val) -> _ => 
        induction src; intros
| |- forall (src : dupe) (val : dupeResult), evalDupe src = val -> _ =>
        induction src; intros; try (simpl in *; subst; constructor)
end.

Ltac destructDupeProperties := 
repeat match goal with 
| dUniop: dupeUniaryOp |- _ => 
        destruct dUniop; simpl in *;(try discriminate)
| dResult: dupeResult |- _ => 
        destruct dResult; simpl in *;(try discriminate)
| dType: dupeType |- _ => 
        destruct dType; simpl in *;(try discriminate)
end.

Ltac refineHypothesis := 
repeat match goal with 
    | H : False |- _ => contradiction H
    | H : _ \/ _ |- _ => destruct H
    | H : _ /\ _ |- _ => destruct H
    | H: ?a = ?a |- _ => clear H
    | H: (_,_) = (_,_) |- _ => inversion H;subst
    | H: context[In _ _] |- _ => simpl in H
end.

Ltac invertConstructiveDupe := 
    match goal with 
    | H: D_Integer ?z d==> (?type,?val) |- _ => inversion H; subst
    | H: D_Boolean ?b d==> (?type,?val) |- _ => inversion H; subst
    | H: (D_UniOp ?op ?src) d==> (?type,?val) |- _ => inversion H; subst
    | H: (D_if ?srcIf ?srcThen ?srcElse) d==> (?type,?val) |- _ => inversion H; subst
    end; (try reflexivity)
.


Theorem evalTypesSame:
    forall src type val,
        src d==> (type, val) ->
        resultType val = type.
Proof. 
    induction src; intros;
    evalPreamble;
    destructDupeProperties;
    invertConstructiveDupe;
    refineHypothesis; (try discriminate);
    repeat match goal with 
    | H : ?src d==> (?type, ?val),
        IH: forall (type : dupeType) (val : dupeResult),
        ?src d==> (type, val) -> resultType val = type 
        |- _ =>
        specialize (IH type val H); subst
    end; 
    destructDupeProperties;
    try reflexivity.
Qed.

Ltac removeSpecificType := 
match goal with 
| |- forall (src : dupe) (type : dupeType) (val : dupeResult), src d==> (type, val) -> _ => 
    intros; let tmp := fresh "H" in 
    let eq := fresh "eq" in
    match goal with 
    | H: ?src d==> (?type, ?val) |- _ => 
        remember H as tmp eqn: eq; clear eq;
        apply evalTypesSame in tmp;
        rewrite <- tmp in *; (try discriminate);
        clear tmp; clear type;
        generalize dependent val;
        generalize dependent src
    end
| H: ?src d==> (?type, ?val) |- _ => 
    lazymatch goal with 
    | H1: ?src1 d==> (type, ?val1),
        H2: resultType ?val1 = type |- _ => fail
    | H1: resultType val = type |- _ => fail
    | |- _ => let tmp := fresh "H" in 
        let eq := fresh "eq" in
        remember H as tmp eqn: eq; clear eq;
        apply evalTypesSame in tmp; 
        rewrite <- tmp in *; (try discriminate)
    end
end.

Ltac specializeIH := match goal with 
| IH: ?hyp -> ?prop, H: ?hyp |- _ => specialize (IH H)

| H: ?src d==> (?type, ?val),
    IH: forall val : dupeResult, 
    ?src d==> (resultType val, val) -> _ |- _ =>

    let tmp := fresh "H" in 
    let eq := fresh "eq" in
    remember H as tmp eqn: eq; clear eq;
    specialize (IH val);
    eapply evalTypesSame in tmp; rewrite tmp in IH;
    specialize (IH H);
    clear tmp

| IH: forall val: dupeResult,
    evalDupe ?src = val -> _ |- _ => specialize (IH (evalDupe src))

| H: ?src d==> (resultType ?val, ?val),
    IH: forall (val: dupeResult),
    ?src d==> (resultType val, val) -> _ |- _ => specialize (IH val H)

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

Ltac applyEvalRules := 
match goal with 
    | |- (D_UniOp ?op ?src) d==> (?type, uniOpTransform ?op ?srcResult) => 
        apply (E_D_UniOp src srcResult (resultType srcResult) op type); simpl;[
            solve [try specializeIH; (try assumption)]| 
            solve[(try contradiction);repeat ((left; reflexivity) || right)]
        ]
    | Hsrc1: ?src1 d==> (D_type_Int, DR_Int ?z),
        Hsrc2: ?src2 d==> (?evalType, ?valThen),
        Hsrc3: ?src3 d==> (?evalType, ?valElse)
        |- (D_if ?src1 ?src2 ?src3) d==> (?evalType, ?valThen) => 
            apply (E_D_ifInt src1 z src2 valThen src3 valElse evalType); assumption
    | Hsrc1: ?src1 d==> (D_type_Bool, DR_Bool ?b),
        Hsrc2: ?src2 d==> (?evalType, ?valThen),
        Hsrc3: ?src3 d==> (?evalType, ?valElse)
        |- (D_if ?src1 ?src2 ?src3) d==> (?evalType, if ?b then ?valThen else ?valElse) => 
            destruct b; simpl; [
                apply (E_D_ifTrue src1 src2 valThen src3 valElse evalType); assumption
                | apply (E_D_ifFalse src1 src2 valThen src3 valElse evalType); assumption
            ]  
end.

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


Ltac evalAuto := 
    try removeSpecificType;
    evalPreamble;
    destructDupeProperties;
    try invertConstructiveDupe;
    refineHypothesis; (try discriminate);
    destructDupeProperties;
    repeat removeSpecificType;
    repeat specializeIH; repeat rewriteLeft;
    (try reflexivity);
    repeat match goal with 
    | IH : resultType (evalDupe ?src) <> D_type_Error ->
            ?src d==> (resultType (evalDupe ?src), evalDupe ?src)
        |- _ => destruct (evalDupe src); simpl in IH; (try discriminate)
    end;
    repeat specializeIH;
    try match goal with 
    | H: _ = ?val |- _ d==> (_,?val) => rewrite <- H in *
    end;
    (simpl in *);
    (try discriminate);
    try applyEvalRules;
    try match goal with 
    | H: (if ?b then _ else _) = _ |- _=> destruct b; discriminate
    | H: D_type_Error <> D_type_Error |- _ => contradiction
    end
.


Theorem TypeOfDupe_same_as_Eval:
    forall src type val,
        src d==> (type, val) -> 
        typeOfDupe src = type.
Proof.
    evalAuto.
Qed.
    

Theorem evalDupe_implies_dupeEval: 
    forall src val,
    evalDupe src = val ->
    ((resultType val) <> D_type_Error) ->
    src d==> (resultType val, val).
Proof.
    evalAuto.
Qed.


Theorem dupeEval_implies_evalDupe: 
    forall src val,
    src d==> (resultType val, val) ->
    evalDupe src = val.
Proof.
    evalAuto.
Qed.


Theorem dupeNotEvalError:
forall src val,
    src d==> (resultType val, val) ->
    ((resultType val) <> D_type_Error).
Proof.
    evalAuto.
Qed.


Theorem evalEquivalence: 
    forall src val,
    src d==> (resultType val, val) <-> ((evalDupe src = val) /\ ((resultType val) <> D_type_Error)).
Proof.
    intros. 
    split.
    - split.
        + apply dupeEval_implies_evalDupe. assumption.
        + apply (dupeNotEvalError src). assumption.
    - intros. 
        destruct H.
        apply  evalDupe_implies_dupeEval.
        + assumption.
        + assumption.
Qed.

