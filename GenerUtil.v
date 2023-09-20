Require Import Setoid.
Require Import Bool.
Require Import List.

Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).
Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

Lemma bneq_eq_neg : forall (a b : bool), a <> b -> negb a = b.
Proof.
  intros a b H. destruct b.
  - apply not_true_iff_false in H. rewrite H. reflexivity.
  - apply not_false_iff_true in H. rewrite H. reflexivity.
Qed.