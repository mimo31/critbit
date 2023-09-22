(* defines take_zer and ith_zer together with several lemmas and their proofs *)

Require Import Arith.
Require Import Setoid.
Require Import Bool.
Require Import List.
Import ListNotations.

Definition ith_zer (i : nat) (k : list bool) : bool := nth i k false.

Lemma ith_zer_nil : forall (i : nat), ith_zer i [] = false.
Proof.
  intro i. destruct i. reflexivity. reflexivity.
Qed.

Fixpoint take_zer (n : nat) (li : list bool) : (list bool) :=
  match n, li with
  | 0, _ => nil
  | S n', nil => false :: take_zer n' nil
  | S n', cons e li' => e :: take_zer n' li'
  end.

Lemma take_length : forall (n : nat) (li : list bool),
  length (take_zer n li) = n.
Proof.
  induction n as [| n' IH].
  - intro li. reflexivity.
  - intro li. destruct li.
    + simpl. f_equal. apply IH.
    + simpl. f_equal. apply IH.
Qed.

Lemma take_take : forall (n m : nat) (li : list bool),
  (n <= m) -> take_zer n (take_zer m li) = take_zer n li.
Proof.
  induction n as [| n' IH].
  - intros m li _. reflexivity.
  - intros m li H. inversion H.
    + simpl. destruct li.
      * f_equal. apply IH. apply le_n.
      * f_equal. apply IH. apply le_n.
    + simpl. destruct li.
      * f_equal. apply IH. apply le_S_n. rewrite H1. exact H.
      * f_equal. apply IH. apply le_S_n. rewrite H1. exact H.
Qed.

Lemma take_length_app : forall (k1 k2 : list bool), take_zer (length k1) (k1 ++ k2) = k1.
Proof.
  induction k1 as [| b k1 IH].
  - intro k2. reflexivity.
  - intro k2. simpl. f_equal. apply IH.
Qed.

Lemma take_with_ith : forall (k : list bool) (i : nat),
  (take_zer i k ++ [ith_zer i k]) = take_zer (S i) k.
Proof.
  intros k i. generalize dependent k.
  induction i as [| i' IH].
  - destruct k.
    + reflexivity.
    + reflexivity.
  - destruct k.
    + simpl. f_equal. specialize (IH []). destruct i'. reflexivity. simpl in IH. simpl. exact IH.
    + simpl. f_equal. rewrite IH. reflexivity.
Qed.

Lemma ith_from_take : forall (j i : nat) (k: list bool),
  (S j <= i) -> (ith_zer j (take_zer i k) = ith_zer j k).
Proof.
  induction j as [| j IH].
  - intros i k H. destruct i.
    + inversion H.
    + destruct k.
      * reflexivity.
      * reflexivity.
  - intros i k H. destruct k.
    + simpl. destruct i.
      * reflexivity.
      * apply le_S_n in H. simpl. apply (IH i []) in H. rewrite ith_zer_nil in H. exact H.
    + simpl. destruct i.
      * inversion H.
      * simpl. apply le_S_n in H. apply IH. exact H.
Qed.

Lemma take_full : forall (l : list bool), take_zer (length l) l = l.
Proof.
  induction l as [| b l IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.