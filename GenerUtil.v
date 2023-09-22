Require Import Bool.

Lemma bneq_eq_neg : forall (a b : bool), a <> b -> negb a = b.
Proof.
  intros a b H. destruct b.
  - apply not_true_iff_false in H. rewrite H. reflexivity.
  - apply not_false_iff_true in H. rewrite H. reflexivity.
Qed.