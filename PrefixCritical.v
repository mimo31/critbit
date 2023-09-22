Require Import Setoid.
Require Import Bool.
Require Import List. 
Require Import PeanoNat.
Import ListNotations.

From CritBit Require Import GenerUtil.
From CritBit Require Import KeyUtil.
From CritBit Require Import SeqAccess.

(* --- prefix related below --- *)

Inductive prefix : Type :=
  | ZeroExt (p : list bool)
  | Finite (p : list bool).

Inductive is_prefix_fin : (list bool) -> (list bool) -> Prop :=
  | ipff1 (k : list bool)
      : is_prefix_fin nil k
  | ipff2 (b : bool) (p' : list bool) (k' : list bool) (H: is_prefix_fin p' k')
      : is_prefix_fin (b :: p') (b :: k').

Inductive is_prefix_zer : (list bool) -> (list bool) -> Prop :=
  | ipfz1 (k : list bool)
      : is_prefix_zer nil k
  | ipfz2 (p' : list bool) (H: is_prefix_zer p' nil)
      : is_prefix_zer (false :: p') nil
  | ipfz3 (b : bool) (p' : list bool) (k' : list bool) (H: is_prefix_zer p' k')
      : is_prefix_zer (b :: p') (b :: k').

Lemma is_prefix_fin_zer : forall (k p : list bool), is_prefix_fin k p -> is_prefix_zer k p.
Proof.
  intros k p H.
  induction H.
  - apply ipfz1.
  - apply ipfz3. exact IHis_prefix_fin.
Qed.

Lemma is_prefix_fin_length : forall (k p : list bool), is_prefix_fin k p -> length k <= length p.
Proof.
  intros k p H.
  induction H.
  - simpl. apply le_0_n.
  - simpl. apply le_n_S. exact IHis_prefix_fin.
Qed.

Lemma is_prefix_zer_fin : forall (k p : list bool),
  (is_prefix_zer k p /\ length k <= length p) -> (is_prefix_fin k p).
Proof.
  induction k as [| b k' IH].
  - intros p [H1 H2]. apply ipff1.
  - intros p [H1 H2]. destruct p.
    + simpl in H2. inversion H2.
    + inversion H1. apply ipff2. apply IH. split.
      * exact H0.
      * simpl in H2. apply le_S_n in H2. exact H2.
Qed.

Definition is_prefix (k : list bool) (p : prefix) : Prop :=
  match p with
  | ZeroExt l => is_prefix_zer k l
  | Finite l => is_prefix_fin k l
  end.

Lemma is_prefix_nil : forall (p : prefix), is_prefix [] p.
Proof.
  destruct p.
  - simpl. apply ipfz1.
  - simpl. apply ipff1.
Qed.

Lemma prefix_iff_take_eq : forall (p k : list bool),
  (is_prefix_zer p k <-> take_zer (length p) k = p).
Proof.
  induction p as [| b p' IH].
  - intro k. split.
    + intro H. reflexivity.
    + intro H. apply ipfz1.
  - intro k. split.
    + intro H. inversion H.
      * simpl. f_equal. apply IH. exact H3.
      * simpl. f_equal. apply IH. exact H3.
    + intro H. simpl in H. destruct k.
      * simpl in H. injection H as H. rewrite <- H. apply ipfz2. apply IH. exact H0.
      * injection H as H. rewrite H. apply ipfz3. apply IH. exact H0.
Qed.

Definition is_prefix_zerb (p k : list bool) : bool := key_eqb (take_zer (length p) k) p.

Lemma is_prefix_zer_iff : forall (p k : list bool), is_prefix_zerb k p = true <-> is_prefix_zer k p.
Proof.
  intros p k. generalize dependent p.
  induction k as [| b k IH].
  - intro p. split.
    + intro H. apply ipfz1.
    + intro H. unfold is_prefix_zerb. reflexivity.
  - intro p. split.
    + intro H. unfold is_prefix_zerb in H. destruct p.
      * simpl in H. destruct b. simpl in H. discriminate.
        simpl in H. apply ipfz2. apply IH. unfold is_prefix_zerb. exact H.
      * simpl in H. destruct (eqb b0 b) eqn:E.
       -- apply eqb_prop in E. rewrite E. apply ipfz3. apply IH. simpl in H.
          unfold is_prefix_zerb. exact H.
       -- simpl in H. discriminate.
    + intro H. unfold is_prefix_zerb in H. destruct p.
      * inversion H. unfold is_prefix_zerb. simpl. apply IH in H1. unfold is_prefix_zerb in H1.
        exact H1.
      * inversion H. unfold is_prefix_zerb. simpl. rewrite eqb_reflx. simpl. apply IH in H1.
        unfold is_prefix_zerb in H1. exact H1.
Qed.

Lemma take_is_prefix : forall (k : list bool) (i : nat),
  (is_prefix_zer (take_zer i k) k).
Proof.
  intros k i. apply prefix_iff_take_eq. rewrite take_length. reflexivity.
Qed.

Lemma app_is_prefix_zer : forall (k1 k2 p : list bool), is_prefix_zer (k1 ++ k2) p -> is_prefix_zer k1 p.
Proof.
  intros k1 k2 p H. apply prefix_iff_take_eq in H. apply prefix_iff_take_eq.
  rewrite app_length in H. rewrite <- (take_take (length k1) (length k1 + length k2)).
  rewrite H. apply take_length_app. apply PeanoNat.Nat.le_add_r.
Qed.

Lemma app_is_prefix_fin : forall (k1 k2 p : list bool), is_prefix_fin (k1 ++ k2) p -> is_prefix_fin k1 p.
Proof.
  intros k1 k2 p H. assert (length (k1 ++ k2) <= length p). { apply is_prefix_fin_length. exact H. }
  apply is_prefix_zer_fin. split.
  - apply is_prefix_fin_zer in H. apply app_is_prefix_zer in H. exact H.
  - rewrite app_length in H0. apply (Arith_prebase.le_plus_trans_stt _ _ (length k2)) in H0.
    rewrite PeanoNat.Nat.add_comm in H0. rewrite (PeanoNat.Nat.add_comm (length p)) in H0.
    apply Plus.plus_le_reg_l_stt in H0. exact H0.
Qed.

Lemma app_is_prefix : forall (k1 k2 : list bool) (p : prefix), is_prefix (k1 ++ k2) p -> is_prefix k1 p.
Proof.
  intros k1 k2 p. destruct p.
  - apply app_is_prefix_zer.
  - apply app_is_prefix_fin.
Qed.

Lemma prefix_zer_trans : forall (p1 p2 p3 : list bool),
  (is_prefix_fin p1 p2) ->
  (is_prefix_zer p2 p3) ->
  (is_prefix_zer p1 p3).
Proof.
  intros p1 p2 p3 H1 H2.
  assert (length p1 <= length p2). { apply is_prefix_fin_length in H1. exact H1. }
  apply is_prefix_fin_zer in H1. apply prefix_iff_take_eq in H1. apply prefix_iff_take_eq in H2.
  apply prefix_iff_take_eq. rewrite <- H2 in H1. rewrite (take_take _ _ _ H) in H1.
  exact H1.
Qed.

Lemma prefix_fin_trans : forall (p1 p2 p3 : list bool),
  (is_prefix_fin p1 p2) ->
  (is_prefix_fin p2 p3) ->
  (is_prefix_fin p1 p3).
Proof.
  intros p1 p2 p3 H1 H2.
  assert (length p1 <= length p2). { apply is_prefix_fin_length in H1. exact H1. }
  assert (length p2 <= length p3). { apply is_prefix_fin_length in H2. exact H2. }
  apply is_prefix_fin_zer in H2.
  apply is_prefix_zer_fin. split.
  - apply prefix_zer_trans with p2. exact H1. exact H2.
  - apply PeanoNat.Nat.le_trans with (length p2). exact H. exact H0.
Qed.

Lemma prefix_trans : forall (p1 p2 : list bool) (p : prefix),
  (is_prefix_fin p1 p2) ->
  (is_prefix p2 p) ->
  (is_prefix p1 p).
Proof.
  intros p1 p2 p H1 H2.
  destruct p.
  - apply prefix_zer_trans with p2. exact H1. exact H2.
  - apply prefix_fin_trans with p2. exact H1. exact H2.
Qed.

Lemma is_prefix_zer_with_ith : forall (p k : list bool),
  (is_prefix_zer p k) -> (is_prefix_zer (p ++ [ith_zer (length p) k]) k).
Proof.
  intros p k H. apply prefix_iff_take_eq. rewrite app_length. simpl. rewrite PeanoNat.Nat.add_comm.
  simpl (_+_). rewrite <- take_with_ith. f_equal. apply prefix_iff_take_eq. exact H.
Qed.

Lemma is_prefix_zer_reflx : forall (k : list bool), is_prefix_zer k k.
Proof.
  intro k. apply prefix_iff_take_eq. apply take_full.
Qed.

Lemma same_prefix_zer : forall (p k1 k2 : list bool),
  (is_prefix_zer p k1) -> (is_prefix_zer p k2) -> (take_zer (length p) k1 = take_zer (length p) k2).
Proof.
  intros p k1 k2 H1 H2. apply prefix_iff_take_eq in H1. apply prefix_iff_take_eq in H2.
  rewrite H1. rewrite H2. reflexivity.
Qed.

(* --- critical bit related below --- *)

Definition o_map {X Y : Type} (f: X -> Y) (o : option X) : option Y :=
  match o with
  | Some x => Some (f x)
  | None => None
  end.

Lemma map_S_S : forall a b, o_map S a = Some (S b) -> a = Some b.
Proof.
  intros a b. destruct a.
  - simpl. intro H. injection H as H. f_equal. exact H.
  - simpl. intro H. discriminate.
Qed.

Lemma map_S_0 : forall a, o_map S a = Some 0 -> False.
Proof.
  intros a H. destruct a.
  - simpl in H. injection H as H. discriminate.
  - simpl in H. discriminate.
Qed.

Lemma map_S_N : forall a, o_map S a = None -> a = None.
Proof.
  intros a H. destruct a.
  - simpl in H. discriminate.
  - reflexivity.
Qed.

(* returns the index of the first 1 (true) in the list or None if there is none *)
Fixpoint first_one (k : list bool) : option nat :=
  match k with
  | cons true k' => Some 0
  | cons false k' => o_map S (first_one k')
  | nil => None
  end.

(* both k1 and k2 are implicitly zero-extended; no preconditions on them *)
Fixpoint critical_bit_zer (k1 k2 : list bool) : (option nat) :=
  match k1, k2 with
  | cons b1 k1', cons b2 k2' => if eqb b1 b2 then
      o_map S (critical_bit_zer k1' k2')
    else
      Some 0
  | nil, _ => first_one k2
  | _, nil => first_one k1
  end.

Lemma critical_bit_zer_nil : forall (k : list bool), critical_bit_zer k [] = first_one k.
Proof.
  intro k. destruct k. reflexivity. reflexivity.
Qed.

(* k is implicitly zero-extended; p is not *)
Fixpoint critical_bit_fin (k p : list bool) : (option nat) :=
  match k, p with
  | _, nil => None
  | nil, p => first_one p
  | cons bk k', cons bp p' => if eqb bk bp then
      o_map S (critical_bit_fin k' p')
    else
      Some 0
  end.

Lemma critical_bit_fin_nil : forall (k : list bool), critical_bit_fin k [] = None.
Proof.
  intro k. destruct k. reflexivity. reflexivity.
Qed.

Lemma length_critical_bit_fin : forall (k p : list bool) (i : nat),
  critical_bit_fin k p = Some i -> S i <= length p.
Proof.
  intros k p. generalize dependent k.
  induction p as [| b p IH].
  - intros k i H. rewrite critical_bit_fin_nil in H. discriminate.
  - intros k i H. destruct k.
    + specialize (IH []). destruct b.
      * simpl in H. injection H as H. rewrite <- H. simpl. apply le_n_S. apply le_0_n.
      * simpl in H. destruct i.
       -- apply map_S_0 in H. destruct H.
       -- apply map_S_S in H. simpl. apply le_n_S. apply IH. destruct p.
         ++ simpl in H. discriminate.
         ++ simpl in H. simpl. exact H.
    + simpl. apply le_n_S. simpl in H. destruct (eqb b0 b).
      * destruct i.
       -- apply le_0_n.
       -- apply map_S_S in H. apply IH in H. exact H.
      * injection H as H. rewrite <- H. apply le_0_n.
Qed.

Lemma critical_bit_fin_zer : forall (k p : list bool) (i : nat),
  critical_bit_fin k p = Some i -> critical_bit_zer k p = Some i.
Proof.
  intros k p. generalize dependent k.
  induction p as [| b p IH].
  - intros k i H. rewrite critical_bit_fin_nil in H. discriminate.
  - intros k i H. destruct k.
    + exact H.
    + simpl. simpl in H. destruct (eqb b0 b).
     * destruct i.
      -- apply map_S_0 in H. destruct H.
      -- apply map_S_S in H. apply IH in H. rewrite H. reflexivity.
     * exact H.
Qed.

Lemma critical_bit_zer_fin : forall (k p : list bool) (i : nat),
  (S i <= length p) ->
  (critical_bit_zer k p = Some i) ->
  (critical_bit_fin k p = Some i).
Proof.
  intros k p. generalize dependent k.
  induction p as [| b p IH].
  - intros k i H. simpl in H. inversion H.
  - intros k i H1 H2. destruct k.
    + simpl. simpl in H2. exact H2.
    + simpl. simpl in H2. destruct (eqb b0 b).
      * destruct i.
       -- apply map_S_0 in H2. destruct H2.
       -- apply map_S_S in H2. simpl in H1. apply le_S_n in H1.
          rewrite (IH k i H1 H2). reflexivity.
      * exact H2.
Qed.

Definition critical_bit (k : list bool) (p : prefix) : (option nat) :=
  match p with
  | ZeroExt l => critical_bit_zer k l
  | Finite l => critical_bit_fin k l
  end.

Lemma critical_bit_zer_take_eq : forall (i : nat) (k1 k2 : list bool),
  (critical_bit_zer k1 k2 = Some i) -> (take_zer i k1 = take_zer i k2).
Proof.
  induction i as [| i IH].
  - intros k1 k2 _. reflexivity.
  - intros k1 k2 H. destruct k1.
    + destruct k2.
     -- reflexivity.
     -- simpl. simpl in H. destruct b.
       ++ injection H as H. discriminate.
       ++ f_equal. apply map_S_S in H. apply (IH []) in H. exact H.
    + destruct k2.
     -- simpl. simpl in H. destruct b.
       ++ injection H as H. discriminate.
       ++ f_equal. apply map_S_S in H. apply (IH []) in H. symmetry. exact H.
     -- simpl. simpl in H. destruct (eqb b b0) eqn:E.
       ++ rewrite eqb_true_iff in E. rewrite E. f_equal. apply map_S_S in H.
          apply IH in H. exact H.
       ++ injection H as H. discriminate.
Qed.

Lemma critical_bit_zer_ith_neq : forall (i : nat) (k1 k2 : list bool),
  (critical_bit_zer k1 k2 = Some i) -> (ith_zer i k1 <> ith_zer i k2).
Proof.
  induction i as [| i IH].
  - intros k1 k2 H. destruct k1.
    + destruct k2.
      * simpl in H. discriminate.
      * simpl in H. simpl. intro H2. unfold ith_zer in H2. simpl in H2.
        rewrite <- H2 in H. apply map_S_0 in H. exact H.
    + destruct k2.
      * simpl in H. simpl. intro H2. unfold ith_zer in H2. simpl in H2.
        rewrite H2 in H. apply map_S_0 in H. exact H.
      * simpl in H. simpl. intro H2. unfold ith_zer in H2. simpl in H2.
        rewrite H2 in H. rewrite eqb_reflx in H.
        apply map_S_0 in H. exact H.
  - intros k1 k2 H. destruct k1.
    + destruct k2.
      * simpl in H. discriminate.
      * simpl in H. simpl. destruct b.
       -- injection H as H. discriminate.
       -- apply map_S_S in H. apply (IH []) in H. rewrite ith_zer_nil in H. exact H.
    + destruct k2.
      * simpl in H. simpl. destruct b.
       -- injection H as H. discriminate.
       -- apply map_S_S in H. rewrite <- critical_bit_zer_nil in H. apply IH in H.
          rewrite ith_zer_nil in H. exact H.
      * simpl in H. simpl. destruct (eqb b b0).
       -- apply map_S_S in H. apply IH in H. exact H.
       -- injection H as H. discriminate.
Qed.

Lemma critical_bit_zer_from_parts : forall (i : nat) (k1 k2 : list bool),
  (take_zer i k1 = take_zer i k2) ->
  (ith_zer i k1 <> ith_zer i k2) ->
  (critical_bit_zer k1 k2 = Some i).
Proof.
  induction i as [| i IH].
  - intros k1 k2 H1 H2. destruct k1.
    + destruct k2.
      * exfalso. apply H2. reflexivity.
      * simpl. simpl in H2. assert (b <> false). intro L. apply H2. rewrite L. reflexivity.
        apply not_false_is_true in H. rewrite H. simpl. reflexivity.
    + destruct k2.
      * simpl. simpl in H2. apply not_false_is_true in H2. unfold ith_zer in H2. simpl in H2.
        rewrite H2. reflexivity.
      * simpl. simpl in H2. apply eqb_false_iff in H2. unfold ith_zer in H2. simpl in H2.
        rewrite H2. reflexivity.
  - intros k1 k2 H1 H2. destruct k1.
    + destruct k2.
      * simpl in H2. apply bneq_eq_neg in H2. simpl in H2. discriminate.
      * simpl in H2. apply bneq_eq_neg in H2. simpl in H2. simpl in H1. injection H1 as H1.
        simpl. rewrite <- H1. assert (critical_bit_zer [] k2 = Some i). {
          apply IH. apply H. unfold ith_zer in H2. simpl in H2. rewrite ith_zer_nil.
          unfold ith_zer. rewrite <- H2. intro L. discriminate.
        } simpl in H0. rewrite H0. reflexivity.
    + destruct k2.
      * simpl. simpl in H1. simpl in H2. injection H1 as H1. rewrite H1.
        assert (critical_bit_zer k1 [] = Some i). { apply IH. exact H. rewrite ith_zer_nil.
          exact H2. } rewrite critical_bit_zer_nil in H0. rewrite H0. reflexivity.
      * simpl in H1. injection H1 as H1. rewrite H1. simpl. rewrite eqb_reflx. simpl in H2.
        apply IH in H. rewrite H. reflexivity. exact H2.
Qed.
 
Lemma critical_bit_zer_prefix : forall (k p : list bool) (i : nat),
  critical_bit_zer k p = Some i -> is_prefix_zer (take_zer i k ++ [negb (ith_zer i k)]) p.
Proof.
  intros k p i. generalize dependent k. generalize dependent p.
  induction i as [| i' IH].
  - intros p k H. simpl. destruct k.
    + destruct p.
      * simpl in H. discriminate.
      * destruct b.
       -- simpl. apply ipfz3. apply ipfz1.
       -- simpl in H. apply map_S_0 in H. destruct H.
    + destruct p.
      * destruct b.
       -- simpl. apply ipfz2. apply ipfz1.
       -- simpl in H. apply map_S_0 in H. destruct H.
      * simpl in H. destruct (eqb b b0) eqn:E.
       -- apply map_S_0 in H. destruct H.
       -- apply eqb_false_iff in E. apply bneq_eq_neg in E. unfold ith_zer. simpl.
          rewrite E. apply ipfz3. apply ipfz1.
  - intros p k H. destruct k.
    + destruct p.
      * simpl in H. discriminate.
      * destruct b.
       -- simpl in H. injection H as H. discriminate.
       -- simpl. apply ipfz3. replace (true) with (negb (ith_zer i' [])).
         ++ apply IH. simpl in H. simpl. apply map_S_S in H. exact H.
         ++ destruct i'. reflexivity. reflexivity.
    + destruct p.
      * destruct b.
       -- simpl in H. injection H as H. discriminate.
       -- simpl in H. simpl. apply ipfz2. apply IH. apply map_S_S in H.
          rewrite critical_bit_zer_nil. exact H.
      * simpl in H. simpl. destruct (eqb b b0) eqn:E.
       -- apply -> eqb_true_iff in E. apply map_S_S in H. apply IH in H. rewrite E.
          apply ipfz3. exact H.
       -- injection H as H. discriminate.
Qed.

Lemma critical_bit_fin_prefix : forall (k p : list bool) (i : nat),
  critical_bit_fin k p = Some i -> is_prefix_fin (take_zer i k ++ [negb (ith_zer i k)]) p.
Proof.
  intros k p i H. apply is_prefix_zer_fin. split.
  - apply critical_bit_zer_prefix. apply critical_bit_fin_zer. exact H.
  - rewrite app_length. rewrite take_length. simpl. rewrite PeanoNat.Nat.add_comm.
    simpl. apply length_critical_bit_fin in H. exact H.
Qed.

Lemma critical_bit_prefix : forall (k : list bool) (p : prefix) (i : nat),
  critical_bit k p = Some i -> is_prefix (take_zer i k ++ [negb (ith_zer i k)]) p.
Proof.
  intros k p i H. destruct p.
  - simpl. simpl in H. apply critical_bit_zer_prefix in H. exact H.
  - simpl. simpl in H. apply critical_bit_fin_prefix in H. exact H.
Qed.

Lemma critical_bit_in_prefix : forall (k k' p : list bool) (i : nat),
  (S i <= length p) ->
  (critical_bit_zer k k' = Some i) ->
  (is_prefix_zer p k') ->
  (critical_bit_fin k p = Some i).
Proof.
  intros k k' p i H1 H2 H3. apply critical_bit_zer_fin. exact H1.
  apply critical_bit_zer_from_parts. assert (take_zer i k = take_zer i k').
  apply critical_bit_zer_take_eq. exact H2. assert (take_zer (length p) k' = p).
  { apply prefix_iff_take_eq. exact H3. } rewrite <- H0. rewrite take_take. exact H.
  apply le_S_n. apply le_S. exact H1. apply critical_bit_zer_ith_neq in H2.
  apply prefix_iff_take_eq in H3. rewrite <- H3. rewrite ith_from_take. exact H2. exact H1.
Qed.

Lemma critical_bit_fin_none_prefix : forall (k p : list bool),
  (critical_bit_fin k p = None) <-> (is_prefix_zer p k).
Proof.
  split.
  - generalize dependent k. induction p as [| b p IH].
    + intros k H. apply ipfz1.
    + intros k H. destruct k.
      * simpl in H. destruct b.
       -- discriminate.
       -- apply ipfz2. apply map_S_N in H. apply IH. simpl. destruct p. reflexivity. exact H.
      * simpl in H. destruct (eqb b0 b) eqn:E.
       -- apply map_S_N in H. apply eqb_prop in E. rewrite E. apply ipfz3. apply IH. exact H.
       -- discriminate.
  - intro H. destruct (critical_bit_fin k p) eqn:E.
    + pose proof (length_critical_bit_fin _ _ _ E). apply critical_bit_fin_zer in E.
      apply critical_bit_zer_ith_neq in E. exfalso. apply E. apply prefix_iff_take_eq in H.
      rewrite <- H. rewrite ith_from_take. reflexivity. exact H0.
    + reflexivity.
Qed.

Lemma critical_bit_zer_none_eqv : forall (k1 k2 : list bool),
  critical_bit_zer k1 k2 = None <-> (forall n : nat, take_zer n k1 = take_zer n k2).
Proof.
  split.
  - intros H n. generalize dependent k1. generalize dependent k2. induction n as [| n IH].
    + reflexivity.
    + intros k2 k1 H. simpl. destruct k1.
      * destruct k2.
       -- reflexivity.
       -- simpl in H. destruct b. discriminate. apply map_S_N in H. f_equal.
          specialize (IH k2 []). simpl in IH. apply IH. exact H.
      * destruct k2.
       -- simpl in H. destruct b. discriminate. apply map_S_N in H. f_equal.
          specialize (IH [] k1). rewrite critical_bit_zer_nil in IH. apply IH. exact H.
       -- simpl in H. destruct (eqb b b0) eqn:E.
         ++ apply map_S_N in H. apply eqb_prop in E. rewrite <- E in *. f_equal. apply IH. exact H.
         ++ discriminate.
  - intro H. destruct (critical_bit_zer k1 k2) eqn:E.
    + apply critical_bit_zer_ith_neq in E. exfalso. apply E. specialize (H (S n)).
      rewrite <- (ith_from_take n (S n) k1). rewrite <- (ith_from_take n (S n) k2). rewrite H.
      reflexivity. apply le_n. apply le_n.
    + reflexivity.
Qed.

Lemma critical_bit_zer_none_prefix : forall (k1 k2 : list bool),
  critical_bit_zer k1 k2 = None -> is_prefix_zer k1 k2.
Proof.
  intros k1 k2 H. apply prefix_iff_take_eq. rewrite critical_bit_zer_none_eqv in H.
  specialize (H (length k1)). rewrite <- H. apply take_full.
Qed.

Lemma critical_bit_zer_comm : forall (k p : list bool),
  critical_bit_zer k p = critical_bit_zer p k.
Proof.
  intros k p. destruct (critical_bit_zer p k) eqn:E.
  - apply critical_bit_zer_from_parts.
    + apply critical_bit_zer_take_eq in E. symmetry. exact E.
    + apply critical_bit_zer_ith_neq in E. intro H. apply E. symmetry. exact H.
  - apply critical_bit_zer_none_eqv. rewrite critical_bit_zer_none_eqv in E.
    intro n. specialize (E n). symmetry. exact E.
Qed.

Lemma critical_bit_zer_after : forall (k1 k2 : list bool) (n m : nat),
  (take_zer n k1 = take_zer n k2) -> (critical_bit_zer k1 k2 = Some m) -> (n <= m).
Proof.
  intros k1 k2 n m H1 H2. destruct (Nat.le_gt_cases n m). exact H. unfold "<" in H.
  apply critical_bit_zer_ith_neq in H2. exfalso. apply H2.
  rewrite <- (ith_from_take m n). rewrite <- (ith_from_take m n k2). rewrite H1.
  reflexivity. exact H. exact H.
Qed.

Lemma oterm_nil_cbit : forall k : list bool,
  OneTerminated k -> critical_bit_zer [] k = None -> False.
Proof.
  induction k as [| b k IH].
  - intro H. inversion H.
  - intros H1 H2. simpl in H2. destruct b.
    + discriminate.
    + apply map_S_N in H2. inversion H1.
      * apply IH in H0. destruct H0. simpl. exact H2.
Qed.

Lemma critical_bit_zer_none_eq : forall (k1 k2 : list bool),
  OneTerminated k1 -> OneTerminated k2 -> critical_bit_zer k1 k2 = None -> k1 = k2.
Proof.
  induction k1 as [| b1 k1 IH].
  - intros k2 H1 H2. inversion H1.
  - intros k2 H1 H2 H3. destruct k2.
    + inversion H2.
    + simpl in H3. destruct (eqb b1 b) eqn:E.
      * apply eqb_prop in E. rewrite E in *. clear E b1. f_equal. apply map_S_N in H3. inversion H1.
       -- destruct k2.
         ++ reflexivity.
         ++ inversion H2. rewrite <- H4 in H3. apply oterm_nil_cbit in H3.
            destruct H3. exact H5.
       -- destruct k2.
         ++ rewrite critical_bit_zer_comm in H3. apply oterm_nil_cbit in H3. destruct H3. exact H0.
         ++ inversion H2. apply IH. exact H0. exact H6. exact H3.
      * discriminate.
Qed.