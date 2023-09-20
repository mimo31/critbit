Require Import Setoid.
Require Import Bool.
Require Import List.

(* our tree has one-terminated strings as keys *)
Fixpoint one_terminated (k : list bool) : bool :=
  match k with
  | cons b nil => b
  | cons b k' => one_terminated k'
  | nil => false
  end.

Inductive OneTerminated : (list bool) -> Prop :=
  | ot_singleton                                              : OneTerminated (true :: nil)
  | ot_cond (b : bool) (k' : list bool) (H: OneTerminated k') : OneTerminated (b :: k')
.

(* no additional assuptions on k1 and k2; just standard equality *)
Fixpoint key_eqb (k1 k2 : list bool) : bool :=
  match k1, k2 with
  | cons b1 k1', cons b2 k2' => eqb b1 b2 && key_eqb k1' k2'
  | nil, nil => true
  | _, _ => false
  end.

Lemma key_eqb_iff : forall (k1 k2 : list bool),
  (key_eqb k1 k2 = true) <-> (k1 = k2).
Proof.
  induction k1 as [| x k1' IH].
  - intro k2. split.
    + intro H. destruct k2. reflexivity. simpl in H. discriminate.
    + intro H. rewrite <- H. simpl. reflexivity.
  - intro k2. destruct k2.
    + split.
      * intro H. simpl in H. discriminate.
      * intro H. discriminate.
    + split.
      * intro H. simpl in H. destruct (eqb x b) eqn:E. simpl in H.
        apply IH in H. apply eqb_prop in E. f_equal. exact E. exact H.
        simpl in H. discriminate.
      * intro H. injection H as H. rewrite H. rewrite <- H0. simpl.
        assert (eqb b b = true). { apply eqb_reflx. } rewrite H1.
        simpl. apply IH. reflexivity.
Qed.

Lemma key_eqb_niff : forall (k1 k2 : list bool),
  (key_eqb k1 k2 = false) <-> (k1 <> k2).
Proof.
  split.
  - intros H1 H2. apply key_eqb_iff in H2. rewrite H2 in H1. discriminate.
  - intros H1. rewrite <- key_eqb_iff in H1. destruct (key_eqb k1 k2).
    assert (true = true). reflexivity. apply H1 in H. destruct H.
    reflexivity.
Qed.

Lemma key_eqb_reflx : forall (k : list bool),
  key_eqb k k = true.
Proof.
  intro k. apply key_eqb_iff. reflexivity.
Qed.