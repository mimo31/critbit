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
  induction k1 as [| x k1' IH]; intro k2.
  - split; intro H.
    + destruct k2. reflexivity. simpl in H. discriminate.
    + rewrite <- H. reflexivity.
  - destruct k2.
    + split; discriminate.
    + split; intro H.
      * simpl in H. apply andb_prop in H. destruct H. apply IH in H0.
        apply eqb_prop in H. congruence.
      * inversion H. simpl. apply andb_true_intro. split.
        -- apply eqb_reflx.
        -- subst k2. apply IH. reflexivity.
Qed.

Lemma key_eqb_niff : forall (k1 k2 : list bool),
  (key_eqb k1 k2 = false) <-> (k1 <> k2).
Proof.
  intros.
  assert (key_eqb k1 k2 = false <-> key_eqb k1 k2 <> true).
  { split; intro.
    - rewrite H. discriminate.
    - apply not_true_is_false. assumption. }
    pose proof (key_eqb_iff k1 k2). tauto.
Qed.

Lemma key_eqb_reflx : forall (k : list bool),
  key_eqb k k = true.
Proof.
  intro k. apply key_eqb_iff. reflexivity.
Qed.

Lemma key_eqb_sym : forall (k1 k2 : list bool),
    key_eqb k1 k2 = key_eqb k2 k1.
Proof.
  intros. destruct (key_eqb k1 k2) eqn:E1; destruct (key_eqb k2 k1) eqn:E2;
    try rewrite key_eqb_iff in *; try rewrite key_eqb_niff in *; subst; tauto.
Qed.
