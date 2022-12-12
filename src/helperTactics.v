Require Import Arith Bool List ZArith.
Local Open Scope Z_scope.


Require Import wasmLite.
Require Import language.definition.
Require Import language.eval.
Require Import compiler.
Require Import utils.

Ltac refineHypothesis := 
repeat match goal with 
    | H : False |- _ => contradiction H
    | H : _ \/ _ |- _ => destruct H
    | H : _ /\ _ |- _ => destruct H
    | H: ?a = ?a |- _ => clear H
    | H: exists _, _ |- _ => destruct H
    | H: (_,_) = (_,_) |- _ => inversion H;subst
    | H: context[In _ _] |- _ => simpl in H
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

Ltac destructBools := match goal with 
| [H : ?x = true |- context[if ?x then _ else _] ] => rewrite H
| [H : ?x = false |- context[if ?x then _ else _] ] => rewrite H
| [H : true = ?x |- context[if ?x then _ else _] ] => rewrite H
| [H : false = ?x |- context[if ?x then _ else _] ] => rewrite H
| [|- context[if ?x then _ else _] ] => let eq := fresh "eq" in destruct x eqn: eq
end.

Ltac removeListNils := match goal with
| [|- context[_ ++ nil] ] => rewrite app_nil_r
| [|- context[nil ++ _] ] => rewrite app_nil_l
| [H: context[_ ++ nil] |- _ ] => rewrite app_nil_r  in H
| [H: context[nil ++ _] |- _ ] => rewrite app_nil_l  in H
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
|   IH: ?hyp -> ?prop, H: ?hyp |- _ => specialize (IH H)

|   H: ?src d==> (?type, ?val),
    IH: forall val : dupeResult, 
    ?src d==> (resultType val, val) -> _ |- _ =>

    let tmp := fresh "H" in 
    let eq := fresh "eq" in
    remember H as tmp eqn: eq; clear eq;
    specialize (IH val);
    eapply evalTypesSame in tmp; rewrite tmp in IH;
    specialize (IH H);
    clear tmp

|   H0 : compile ?source = Succ ?compiled,
    H1 : ?source d==> ?value,
    IH : forall (compiled : wasmCode) (dupeResult : dupeResult),
        compile ?source = Succ compiled ->
        ?source d==> dupeResult -> _
    |- _ => specialize ((IH compiled value) H0)

|   IH: forall val: dupeResult,
    evalDupe ?src = val -> _ |- _ => specialize (IH (evalDupe src))

|   H: ?src d==> (resultType ?val, ?val),
    IH: forall (val: dupeResult),
    ?src d==> (resultType val, val) -> _ |- _ => specialize (IH val H)

|   IH: ?a = ?a -> _ |- _ => 
    let tmp := fresh "H" in 
    assert (a = a) as tmp;[reflexivity | (specialize (IH tmp));clear tmp]
| IH : resultType (evalDupe ?src) <> D_type_Error ->
            ?src d==> (resultType (evalDupe ?src), evalDupe ?src)
        |- _ => destruct (evalDupe src); simpl in IH; (try discriminate)
|   IH: (?t1 <> ?t2) -> _ |-  _ => 
    let tmp := fresh "H" in 
    assert (t1 <> t2) as tmp;[
        solve[discriminate]|
        specialize (IH tmp); clear tmp
    ]
end.

Ltac applyDupeEvalRule := 
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

    try match goal with 
    | H: _ = ?val |- _ d==> (_,?val) => rewrite <- H in *
    end;
    (simpl in *);
    (try discriminate);
    try applyDupeEvalRule;
    try match goal with 
    | H: (if ?b then _ else _) = _ |- _=> destruct b; discriminate
    | H: D_type_Error <> D_type_Error |- _ => contradiction
    end
.

Ltac stepCompletes := (
    reflexivity || 
    (apply Z.eqb_neq;reflexivity)
).

Ltac doesSingleStep := 
    ( (eapply W_ST_64Const; stepCompletes)
    || (eapply W_ST_32Const; stepCompletes)
    || (eapply W_ST_inn_ibinop; stepCompletes)
    || (eapply W_ST_inn_itestop; stepCompletes)
    || (eapply W_ST_32IfTrue; stepCompletes)
    || (eapply W_ST_32IfFalse; stepCompletes)
    || (eapply W_ST_nop; stepCompletes)
    || (eapply W_ST_unreachable; stepCompletes)
    )
.

Ltac unfoldCommon :=
    unfold testopOperation in *;
    unfold binopOperation in *;
    unfold uniOpTransform in *;
    unfold compileUniOp in *
.


Ltac doesStep :=
repeat (
    unfoldCommon;
    simpl in *;
    (repeat destructBools);
    (repeat removeListNils); 
    (try assumption);
    (try discriminate);
    match goal with 
    | [|- _ w-->* _ ]=> econstructor
    | [|- multi wasmStepInd _ _] => econstructor
    | [|- _ w--> _] => doesSingleStep
    end
).

