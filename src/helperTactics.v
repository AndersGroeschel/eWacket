Require Import List.

Require Import wasmLite.
Require Import wacket.
Require Import compiler.


Ltac refineInductiveHypothesis := 
match goal with 
|   H0 : compile ?source = Succ ?compiled,
    H1 : ?source d==> ?value,
    IH : forall (compiled : wasmCode) (dupeResult : dupeResult),
        compile ?source = Succ compiled ->
        ?source d==> dupeResult -> _
    |- _ => specialize ((IH compiled value) H0)
|  H0: ?h1 -> ?h2, H1: ?h1 |- _ => specialize (H0 H1)
end.

Ltac logicAuto :=
match goal with 
| H: _ /\ _ |- _ => destruct H
| H: _ \/ _ |- _ => destruct H
| H: exists _, _ |- _ => destruct H
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

