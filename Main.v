(* CRIT-BIT TREES *)
(* type of keys: list bool
     -- only lists ending with `true` are allowed as keys (both in lookups and insertions) *)
(* type of values: arbitrary
     -- all the tree types and the relevant functions are parametrized by this type *)
(* implemented operations:
     - creating a new tree ("seed"ing)
     - inserting into a tree
     - looking up in a tree *)

(* convention: left subtree is for false, right subtree is for true *)

(* abbreviations and ideas:
  CBT        crit-bit tree (we usually mean this to be a *non-empty* crit-bit tree)

  augCBT     augmented crit-bit tree:
             For the purposes of the proofs, we augment the basic CBT with additional data.
             Specifically, we store the full current prefix at every internal node.
             There is a natural bijection between valid CBTs and valid augCBTs. (Given a CBT,
             we can construct the *unique* augmenting data. Given a augCBT, we can just forget
             the augmenting data. This latter direction of the bijection is obviously much easier
             to compute -- we call it stripping -- see strip_augCBT.)
             A CBT is defined to be valid iff it can be obtained by stripping some valid augCBT.
             The core property of a valid augCBT is that for an internal node with prefix p,
             p ++ [false] is a prefix of the left child's prefix and p ++ [true] is a prefix of the
             right child's prefix.

             In general, this permits the following high-level structure of proofs about properties of
             operations on CBTs.
             - For an operation defined as op: CBT -> CBT, define this operation in a more convenient way
               as aug_op: augCBT -> augCBT.
             - Prove that these two 'do the same thing':

                   aut  -- aug_op -->   aut'

                    |                    |
                  strip                strip
                    |                    |
                    v                    v

                    t   --  op    -->    t'


                    commutes (if aut is valid)

             - Prove that aug_op has the desired functional properties.

  content    We define the keys and values that a CBT / augCBT contains in terms of
             what the lookup function returns.
*)

Require Import List.
Require Import Nat.
Require Import Bool.
Require Import Arith.
Require Import Arith.Compare.
Require Import Logic.FunctionalExtensionality.

From CritBit Require Import GenerUtil.
From CritBit Require Import KeyUtil.
From CritBit Require Import PrefixCritical.
From CritBit Require Import SeqAccess.

(* a CBT (non-empty) *)
Inductive CBT {X : Type} : Type :=
  | Leaf (k : list bool) (v : X)
  | Branch (i : nat) (l r : CBT).

(* an augmented CBT tree (non-empty) *)
Inductive augCBT {X : Type} : Type :=
  | AugLeaf (k : list bool) (v : X)
  | AugBranch (p : list bool) (l r : augCBT).

(* strip an augCBT -- forget the augmenting data *)
Fixpoint strip_augCBT {X : Type} (t : @augCBT X) : CBT :=
  match t with
  | AugLeaf k v => Leaf k v
  | AugBranch p l r => Branch (length p) (strip_augCBT l) (strip_augCBT r)
  end.

Definition prefix_from_aug {X : Type} (aut : @augCBT X) : prefix :=
  match aut with
  | AugLeaf k _ => ZeroExt k
  | AugBranch k _ _ => Finite k
  end.

Inductive augCBT_valid {X : Type} : augCBT -> Prop :=
  | acv_leaf (k : list bool) (v : X) (H: OneTerminated k)
      : augCBT_valid (AugLeaf k v)
  | acv_branch (p : list bool) (l r : augCBT)
    (H1: augCBT_valid l) (H2: is_prefix (p ++ (false :: nil)) (prefix_from_aug l))
    (H3: augCBT_valid r) (H4: is_prefix (p ++ (true :: nil)) (prefix_from_aug r))
      : augCBT_valid (AugBranch p l r).

Inductive CBT_valid {X : Type} : (@CBT X) -> Prop :=
  | cv (t : CBT) (aut : augCBT)
    (H1: strip_augCBT aut = t) (H2: augCBT_valid aut) : CBT_valid t.

Definition seed_CBT {X : Type} (k : list bool) (v : X) : CBT :=
  Leaf k v.

Definition empty_map {X : Type} (k : list bool) :=
  @None X.

Definition insert_map
  {X : Type} (k : list bool) (v : X) (m : (list bool) -> option X) (k' : list bool) :=
  if key_eqb k' k then Some v else m k'.

(* precond: one-terminated k *)
(* precond: t is a valid tree w.r.t. CBT_valid *)
Fixpoint lookup {X : Type} (k : list bool) (t : CBT) : option X :=
  match t with
  | Leaf k' v => if key_eqb k k' then Some v else None
  | Branch i l r => if ith_zer i k then lookup k r else lookup k l
  end.

Definition content {X : Type} (t : CBT) (k : list bool) := @lookup X k t.

Definition equal_content {X : Type} (c1 c2 : (list bool) -> option X) : Prop :=
  forall k, (OneTerminated k) -> c1 k = c2 k.

Definition content_aug {X : Type} (aut : augCBT) (k : list bool) := @lookup X k (strip_augCBT aut).

Theorem seeded_spec : forall (X : Type) (k : list bool) (v : X) (k' : list bool),
  (OneTerminated k) ->
  (OneTerminated k') ->
  (CBT_valid (seed_CBT k v) /\ equal_content (content (seed_CBT k v)) (insert_map k v empty_map)).
Proof.
  intros X k v k' Hotk Hotk'.
  simpl.
  split.
  - apply cv with (AugLeaf k v).
    + unfold seed_CBT. reflexivity.
    + apply (acv_leaf _ _ Hotk).
  - unfold equal_content. intros k0 _. unfold insert_map. unfold empty_map. reflexivity.
Qed.

Fixpoint find_best_key {X : Type} (k : list bool) (t : @CBT X) : (list bool) :=
  match t with
  | Leaf k' _ => k'
  | Branch i l r => find_best_key k (if ith_zer i k then r else l)
  end.

Lemma find_key_has_prefix : forall (X : Type) (k p : list bool) (l r : augCBT),
  (augCBT_valid (AugBranch p l r)) ->
  (is_prefix_zer p (@find_best_key X k (strip_augCBT (AugBranch p l r)))).
Proof.
  intros X k p l r E.
  remember (AugBranch p l r) as aut.
  generalize dependent p. generalize dependent l. generalize dependent r.
  induction E.
  - intros r l p H2. discriminate.
  - intros r' l' p' H3. injection H3 as H3. rewrite <- H3 in *.
    clear H3 H H0 p' l' r'. simpl. destruct (ith_zer (length p) k).
    + clear IHE1 E1 H2 l. inversion E2.
      * simpl. rewrite <- H0 in H4. simpl in H4. apply app_is_prefix_zer in H4.
        exact H4.
      * symmetry in H. specialize (IHE2 r0 l p0 H). rewrite H in H4. simpl in H4.
        apply app_is_prefix_fin in H4. apply prefix_zer_trans with p0. exact H4.
        rewrite H in IHE2. exact IHE2.
    + clear IHE2 E2 H4 r. inversion E1.
      * simpl. rewrite <- H0 in H2. simpl in H2. apply app_is_prefix_zer in H2.
        exact H2.
      * symmetry in H. specialize (IHE1 r l0 p0 H). rewrite H in H2. simpl in H2.
        apply app_is_prefix_fin in H2. apply prefix_zer_trans with p0. exact H2.
        rewrite H in IHE1. exact IHE1.
Qed.

Definition critical_bit_CBT {X : Type} (k : list bool) (t : @CBT X) : option nat :=
  critical_bit_zer k (find_best_key k t).

Definition is_beforeb (pos : option nat) (bound : nat) : bool :=
  match pos with
  | None => false
  | Some i => i <? bound
  end.

Definition insert_as_branch {X : Type} (k : list bool) (v : X) (i : nat) (t : CBT) : CBT :=
  if ith_zer i k then Branch i t (Leaf k v) else Branch i (Leaf k v) t.

(* precond: t is a valid tree w.r.t. CBT_valid *)
(* precond: i is the critical bit of k w.r.t. t *)
Fixpoint insert_at {X : Type} (k : list bool) (v : X) (i : option nat) (t : CBT) : CBT :=
  match t with
  | Leaf k' v' =>  match i with
                   | None => Leaf k v
                   | Some cbit => insert_as_branch k v cbit t
                   end
  | Branch j l r => if is_beforeb i j
      then match i with
           | None => Leaf k v (* never happens *)
           | Some cbit => insert_as_branch k v cbit t
           end
      else (if ith_zer j k
            then Branch j l (insert_at k v i r)
            else Branch j (insert_at k v i l) r)
  end.

(* precond: one-terminated k *)
Definition insert {X : Type} (k : list bool) (v : X) (t : CBT) : CBT :=
  insert_at k v (critical_bit_CBT k t) t.

Fixpoint critical_bit_augCBT {X : Type} (k : list bool) (aut : @augCBT X) : option nat :=
  match aut with
  | AugLeaf k' _ => critical_bit_zer k' k
  | AugBranch p l r => if is_prefix_zerb p k then
      if ith_zer (length p) k then
        critical_bit_augCBT k r
      else
        critical_bit_augCBT k l
    else
      critical_bit_zer p k
  end.

Lemma critical_bit_aug_match : forall (X : Type) (k : list bool) (aut : @augCBT X),
  (augCBT_valid aut) -> (critical_bit_augCBT k aut = critical_bit_CBT k (strip_augCBT aut)).
Proof.
  induction aut as [k' v | p' l IHl r IHr ].
  - intro H. unfold critical_bit_CBT. simpl. apply critical_bit_zer_comm.
  - unfold critical_bit_CBT in IHl. unfold critical_bit_CBT in IHr. unfold critical_bit_CBT.
    intro H. simpl. destruct (is_prefix_zerb p' k) eqn:E.
    + inversion H. destruct (ith_zer (length p') k) eqn:E2.
      * apply IHr. exact H5.
      * apply IHl. exact H0.
    + remember (find_best_key k (if ith_zer (length p') k then strip_augCBT r else strip_augCBT l)) as fb.
      assert (fb = find_best_key k (strip_augCBT (AugBranch p' l r))). { simpl. exact Heqfb. }
      assert (is_prefix_zer p' fb). { rewrite H0. apply find_key_has_prefix. exact H. }
      symmetry. destruct (critical_bit_zer p' k) eqn:E2.
      * assert (S n <= length p').
        { assert ({S n <= length p'} + {length p' <= S n}). apply le_dec. destruct H2. exact l0.
        apply le_decide in l0. unfold lt_or_eq in l0. destruct l0. unfold ">" in g. unfold "<" in g.
        apply le_S_n in g. apply critical_bit_zer_take_eq in E2.
        assert (take_zer (length p') p' = take_zer (length p') k). rewrite <- (take_take (length p') n p').
        rewrite <- (take_take (length p') n k). rewrite E2. reflexivity. exact g. exact g.
        rewrite take_full in H2. symmetry in H2. apply prefix_iff_take_eq in H2.
        apply is_prefix_zer_iff in H2. rewrite H2 in E. discriminate. rewrite e. apply le_n. }
        assert (n <= length p'). { apply le_S in H2. apply le_S_n in H2. exact H2. }
        apply critical_bit_zer_from_parts.
       -- apply critical_bit_zer_take_eq in E2. apply prefix_iff_take_eq in H1.
          assert (take_zer n fb = take_zer n p'). { rewrite <- (take_take n (length p') fb).
          rewrite H1. reflexivity. exact H3. } symmetry. transitivity (take_zer n p').
          exact H4. exact E2.
       -- apply critical_bit_zer_ith_neq in E2. assert (ith_zer n p' = ith_zer n fb).
          { rewrite <- (ith_from_take n (length p') fb). apply prefix_iff_take_eq in H1.
          rewrite H1. reflexivity. exact H2. } intro H5. apply E2. symmetry in H5.
          transitivity (ith_zer n fb). exact H4. exact H5.
      * apply critical_bit_zer_none_prefix in E2. apply is_prefix_zer_iff in E2.
        rewrite E2 in E. discriminate.
Qed.

Lemma critical_bit_augCBT_increasing : forall (X : Type) (k p : list bool) (l r : augCBT),
  (augCBT_valid (AugBranch p l r)) ->
  (is_prefix_zer p k) ->
  (is_beforeb (@critical_bit_augCBT X k (AugBranch p l r)) (length p) = false).
Proof.
  intros X k p l r E. remember (AugBranch p l r) as aut.
  generalize dependent p. generalize dependent l. generalize dependent r.
  induction E.
  - intros r l p H2 H3. discriminate.
  - intros r' l' p' H3 H5. injection H3 as H3. rewrite <- H3 in *. clear H3 H H0 p' l' r'.
    unfold is_beforeb. simpl. apply is_prefix_zer_iff in H5. rewrite H5.
    assert (HS: forall (aut : augCBT),
      (augCBT_valid aut) -> (is_prefix p (prefix_from_aug aut)) ->
      (forall (r' l' : augCBT) (p' : list bool),
        aut = AugBranch p' l' r' -> is_prefix_zer p' k -> is_beforeb (@critical_bit_augCBT X k aut) (length p') = false)
      -> match critical_bit_augCBT k aut with
         | Some i => i <? length p
         | None => false
        end = false). {
      clear IHE1 IHE2 E1 H2 E2 H4 l r. intros aut H1 H2 IH. destruct aut.
      - simpl. simpl in H2. destruct (critical_bit_zer k0 k) eqn:E3.
        apply Nat.ltb_ge. apply is_prefix_zer_iff in H5. apply (same_prefix_zer p k0 k) in H2.
        apply (critical_bit_zer_after k0 k). exact H2. exact E3. exact H5. reflexivity.
      - simpl. simpl in H2. destruct (is_prefix_zerb p0 k) eqn:E3.
       -- assert (AugBranch p0 aut1 aut2 = AugBranch p0 aut1 aut2). reflexivity.
          apply is_prefix_fin_length in H2. apply is_prefix_zer_iff in E3.
          specialize (IH aut2 aut1 p0 H E3). unfold is_beforeb in IH. simpl in IH.
          apply is_prefix_zer_iff in E3. rewrite E3 in IH. destruct (ith_zer (length p0) k) eqn:E4.
         ++ destruct (critical_bit_augCBT k aut2) eqn:E5.
            apply Nat.ltb_ge. apply Nat.ltb_ge in IH. apply Nat.le_trans with (length p0).
            exact H2. exact IH. reflexivity.
         ++ destruct (critical_bit_augCBT k aut1) eqn:E5.
            apply Nat.ltb_ge. apply Nat.ltb_ge in IH. apply Nat.le_trans with (length p0).
            exact H2. exact IH. reflexivity.
       -- destruct (critical_bit_zer p0 k) eqn:E4. apply Nat.ltb_ge. apply is_prefix_zer_iff in H5.
          apply prefix_iff_take_eq in H5. apply (critical_bit_zer_after p0 k).
          apply is_prefix_fin_zer in H2. apply prefix_iff_take_eq in H2.
          rewrite H2. symmetry. exact H5. exact E4. reflexivity.
    }
    destruct (ith_zer (length p) k).
    + apply (HS r E2 (app_is_prefix p [true] _ H4) IHE2).
    + apply (HS l E1 (app_is_prefix p [false] _ H2) IHE1).
Qed.
 
Definition insert_as_branch_aug {X : Type} (k : list bool) (v : X) (i : nat) (aut : augCBT) : augCBT :=
  if ith_zer i k then AugBranch (take_zer i k) aut (AugLeaf k v) else AugBranch (take_zer i k) (AugLeaf k v) aut.

Fixpoint insert_aug {X : Type} (k : list bool) (v : X) (aut : augCBT) : augCBT :=
  match aut with
  | AugLeaf k' _ =>
    match critical_bit_zer k' k with
    | None => AugLeaf k' v
    | Some cbit => insert_as_branch_aug k v cbit aut
    end
  | AugBranch p l r =>
    match critical_bit_fin k p with
    | None => if ith_zer (length p) k
      then AugBranch p l (insert_aug k v r)
      else AugBranch p (insert_aug k v l) r
    | Some cbit => insert_as_branch_aug k v cbit aut
    end
  end.

Lemma insert_aug_match : forall (X : Type) (k : list bool) (v : X) (aut : augCBT) (p : list bool),
  (OneTerminated k) ->
  (augCBT_valid aut) ->
  (is_prefix_zer p k) ->
  (is_prefix p (prefix_from_aug aut)) ->
  (
    augCBT_valid (insert_aug k v aut)
    /\ strip_augCBT (insert_aug k v aut) = insert_at k v (critical_bit_augCBT k aut) (strip_augCBT aut)
    /\ is_prefix p (prefix_from_aug (insert_aug k v aut))
  ).
Proof.
  induction aut as [k' v' | p l IHl r IHr].
  - intros p H1 H2 H3 H4. split.
    + simpl. destruct (critical_bit_zer k' k) eqn:E.
      * simpl. unfold insert_as_branch_aug. assert (take_zer n k' = take_zer n k).
        { apply critical_bit_zer_take_eq. exact E. } apply critical_bit_zer_ith_neq in E.
        destruct (ith_zer n k) eqn:E2.
       -- apply acv_branch.
         ++ exact H2.
         ++ simpl. apply prefix_iff_take_eq. rewrite app_length. rewrite PeanoNat.Nat.add_comm.
            simpl (_ + _). rewrite take_length. apply not_true_is_false in E.
            rewrite <- H. rewrite <- E. symmetry. apply take_with_ith.
         ++ apply acv_leaf. exact H1.
         ++ simpl. apply prefix_iff_take_eq. rewrite app_length. rewrite PeanoNat.Nat.add_comm.
            simpl (_ + _). rewrite take_length. symmetry. rewrite <- E2. apply take_with_ith.
       -- apply acv_branch.
         ++ apply acv_leaf. exact H1.
         ++ simpl. apply prefix_iff_take_eq. rewrite app_length. rewrite PeanoNat.Nat.add_comm.
            simpl (_ + _). rewrite take_length. symmetry. rewrite <- E2. apply take_with_ith.
         ++ exact H2.
         ++ simpl. apply prefix_iff_take_eq. rewrite app_length. rewrite PeanoNat.Nat.add_comm.
            simpl (_ + _). rewrite take_length. apply not_false_is_true in E.
            rewrite <- H. rewrite <- E. symmetry. apply take_with_ith.
      * apply acv_leaf. inversion H2. exact H0.
    + split.
      * simpl. destruct (critical_bit_zer k' k) eqn:E.
       -- unfold insert_as_branch_aug. unfold insert. unfold insert_as_branch.
          destruct (ith_zer n k) eqn:E2.
         ++ simpl. rewrite take_length. reflexivity.
         ++ simpl. rewrite take_length. reflexivity.
       -- simpl. inversion H2. apply critical_bit_zer_none_eq in E. rewrite E. reflexivity.
          exact H0. exact H1.
      * simpl. destruct (critical_bit_zer k' k) eqn:E.
       -- unfold insert_as_branch_aug. simpl. simpl in H4.
          assert (length p <= n).
          { apply critical_bit_zer_ith_neq in E. apply prefix_iff_take_eq in H3.
          apply prefix_iff_take_eq in H4. assert (S n <= length p \/ length p <= n).
          { assert ({n <= length p} + {length p <= n}). apply le_dec. destruct H.
          apply le_le_S_eq in l. destruct l. left. exact H. right. rewrite H. apply le_n.
          right. exact l. } destruct H.
          assert (ith_zer n k = ith_zer n p).
          { rewrite <- (ith_from_take n (length p)). rewrite H3. reflexivity. exact H. }
          assert (ith_zer n k' = ith_zer n p).
          { rewrite <- (ith_from_take n (length p)). rewrite H4. reflexivity. exact H. }
          rewrite <- H5 in H0. symmetry in H0. apply E in H0. destruct H0. exact H. }
          assert (is_prefix_fin p (take_zer n k)). { apply is_prefix_zer_fin. split.
          apply prefix_iff_take_eq. rewrite take_take. apply prefix_iff_take_eq.
          exact H3. exact H. rewrite take_length. exact H. } destruct (ith_zer n k).
         ++ simpl. exact H0.
         ++ simpl. exact H0.
       -- simpl. simpl in H4. exact H4.
  - intros p' H1 H2 H3 H4. split.
    + simpl. destruct (critical_bit_fin k p) eqn:E.
      * unfold insert_as_branch_aug. destruct (ith_zer n k) eqn:E2.
       -- apply acv_branch.
         ++ exact H2.
         ++ simpl in H4. simpl. replace false with (negb (ith_zer n k)).
            apply critical_bit_fin_prefix. exact E. rewrite E2. reflexivity.
         ++ apply acv_leaf. exact H1.
         ++ simpl. rewrite <- E2. rewrite take_with_ith. apply take_is_prefix.
       -- apply acv_branch.
         ++ apply acv_leaf. exact H1.
         ++ simpl. rewrite <- E2. rewrite take_with_ith. apply take_is_prefix.
         ++ apply H2.
         ++ simpl. replace true with (negb (ith_zer n k)).
            apply critical_bit_fin_prefix. exact E. rewrite E2. reflexivity.
      * destruct (ith_zer (length p) k) eqn:E2.
       -- clear IHl. inversion H2. clear H0 H5 H6 p0 l0 r0.
          assert (is_prefix_zer (p ++ [true]) k). { rewrite <- E2.
          apply is_prefix_zer_with_ith. apply critical_bit_fin_none_prefix.
          exact E. }
          specialize (IHr (p ++ [true]) H1 H9 H H10). destruct IHr as [IH1 [IH2 IH3]].
          apply acv_branch.
         ++ exact H7.
         ++ exact H8.
         ++ exact IH1.
         ++ exact IH3.
       -- clear IHr. inversion H2. clear H0 H5 H6 p0 l0 r0.
          assert (is_prefix_zer (p ++ [false]) k). { rewrite <- E2.
          apply is_prefix_zer_with_ith. apply critical_bit_fin_none_prefix.
          exact E. }
          specialize (IHl (p ++ [false]) H1 H7 H H8). destruct IHl as [IH1 [IH2 IH3]].
          apply acv_branch.
         ++ exact IH1.
         ++ exact IH3.
         ++ exact H9.
         ++ exact H10.
    + split.
      * simpl (strip_augCBT (AugBranch _ _ _)). simpl (insert_aug _ _ _).
        destruct (critical_bit_fin k p) eqn:E.
       -- unfold insert_as_branch_aug. assert (is_prefix_zerb p k = false).
          { destruct (is_prefix_zerb p k) eqn:Ep. rewrite is_prefix_zer_iff in Ep.
          rewrite <- critical_bit_fin_none_prefix in Ep.
          rewrite E in Ep. discriminate. reflexivity. }
          assert (is_beforeb (critical_bit_zer p k) (length p) = true). {
            destruct (is_beforeb (critical_bit_zer p k) (length p)) eqn:E2.
            reflexivity. unfold is_beforeb in E2. destruct (critical_bit_zer p k) eqn:E3.
            - apply critical_bit_zer_take_eq in E3. apply Nat.ltb_ge in E2.
              assert (take_zer (length p) p = take_zer (length p) k).
              { rewrite <- (take_take (length p) n0 p).
              rewrite <- (take_take (length p) n0 k). rewrite E3. reflexivity.
              exact E2. exact E2. } symmetry in H0. rewrite take_full in H0.
              rewrite <- prefix_iff_take_eq in H0. apply is_prefix_zer_iff in H0.
              rewrite H0 in H. discriminate.
            - apply critical_bit_zer_none_prefix in E3. apply is_prefix_zer_iff in E3.
              rewrite E3 in H. discriminate. }
            destruct (ith_zer n k) eqn:E4.
         ++ simpl (strip_augCBT (AugBranch _ _ _)). rewrite take_length. simpl.
            rewrite H. destruct (is_beforeb (critical_bit_zer p k) (length p)) eqn:E2.
           ** unfold is_beforeb in E2. destruct (critical_bit_zer p k) eqn:E3.
            --- unfold insert_as_branch. rewrite critical_bit_zer_comm in E3.
                apply critical_bit_fin_zer in E. rewrite E3 in E. injection E as E.
                rewrite E in *. clear E n0. rewrite E4. reflexivity.
            --- discriminate.
           ** discriminate.
         ++ simpl (strip_augCBT (AugBranch _ _ _)). rewrite take_length. simpl.
            rewrite H. destruct (is_beforeb (critical_bit_zer p k) (length p)) eqn:E2.
           ** unfold is_beforeb in E2. destruct (critical_bit_zer p k) eqn:E3.
            --- unfold insert_as_branch. rewrite critical_bit_zer_comm in E3.
                apply critical_bit_fin_zer in E. rewrite E3 in E. injection E as E.
                rewrite E in *. clear E n0. rewrite E4. reflexivity.
            --- discriminate.
           ** discriminate.
       -- simpl. assert (is_prefix_zerb p k = true). {
          apply critical_bit_fin_none_prefix in E. apply is_prefix_zer_iff. exact E. }
          rewrite H.
          assert (is_beforeb (critical_bit_augCBT k (AugBranch p l r)) (length p) = false).
          { apply critical_bit_augCBT_increasing. exact H2. apply is_prefix_zer_iff.
          exact H. } simpl in H0. rewrite H in H0. rewrite H0.
          inversion H2. assert (is_prefix_zer (p ++ [ith_zer (length p) k]) k).
          { apply is_prefix_zer_with_ith. apply critical_bit_fin_none_prefix in E.
          apply is_prefix_zer_iff. exact H. }
          destruct (ith_zer (length p) k) eqn:E4.
         ++ simpl. f_equal. clear IHl. inversion H2.
            specialize (IHr (p ++ [true]) H1 H10 H12 H11). destruct IHr as [IH1 [IH2 IH3]].
            exact IH2.
         ++ simpl. f_equal. clear IHr. inversion H2.
            specialize (IHl (p ++ [false]) H1 H16 H12 H9). destruct IHl as [IH1 [IH2 IH3]].
            exact IH2.
      * simpl in H4. simpl. unfold insert_as_branch_aug. destruct (critical_bit_fin k p) eqn:E.
       -- assert (n <= length p). { apply length_critical_bit_fin in E.
          apply le_S in E. apply le_S_n in E. exact E. } apply critical_bit_fin_zer in E.
          assert (length p' <= n). {
            assert (ith_zer n k <> ith_zer n p). apply critical_bit_zer_ith_neq in E. exact E.
            assert ({length p' <= n} + {n <= length p'}). apply le_dec. destruct H5.
            exact l0. apply le_decide in l0. unfold lt_or_eq in l0. destruct l0. unfold ">" in g.
            unfold "<" in g. rewrite <- (ith_from_take n (length p')) in H0.
            rewrite <- (ith_from_take n (length p') p) in H0. apply prefix_iff_take_eq in H3.
            apply is_prefix_fin_zer in H4. apply prefix_iff_take_eq in H4. rewrite H3 in H0.
            rewrite H4 in H0. exfalso. apply H0. reflexivity. exact g. exact g. rewrite e.
            apply le_n. } destruct (ith_zer n k) eqn:E2.
         ++ simpl. apply is_prefix_zer_fin. split.
           ** apply prefix_iff_take_eq. rewrite take_take. apply prefix_iff_take_eq. exact H3.
              exact H0.
           ** rewrite take_length. exact H0.
         ++ simpl. apply is_prefix_zer_fin. split.
           ** apply prefix_iff_take_eq. rewrite take_take. apply prefix_iff_take_eq. exact H3.
              exact H0.
           ** rewrite take_length. exact H0.
       -- assert (prefix_from_aug (if ith_zer (length p) k
            then AugBranch p l (insert_aug k v r) else AugBranch p (insert_aug k v l) r) = Finite p).
          { destruct (ith_zer (length p) k). reflexivity. reflexivity. } rewrite H. exact H4.
Qed.

Lemma lookup_some_has_prefix : forall (X : Type) (k : list bool) (v : X) (p : list bool) (l r : augCBT),
  (OneTerminated k) -> 
  (augCBT_valid (AugBranch p l r)) ->
  (lookup k (strip_augCBT (AugBranch p l r)) = Some v) ->
  (is_prefix_zer p k).
Proof.
  intros X k v p l r. remember (AugBranch p l r) as aut. intros H E. revert Heqaut. generalize p l r.
  clear p l r. induction E.
  - intros p0 l0 r0 Heq. discriminate.
  - simpl. intros p0 l0 r0 Heq. injection Heq as Heq. rewrite <- Heq. clear p0 l0 r0 H0 H1 Heq.
    assert (L: forall (aut : augCBT),
      (forall (p : list bool) (l r0 : augCBT),
       aut = AugBranch p l r0 -> lookup k (strip_augCBT aut) = Some v -> is_prefix_zer p k) ->
       (is_prefix p (prefix_from_aug aut)) ->
       (augCBT_valid aut) ->
       lookup k (strip_augCBT aut) = Some v -> is_prefix_zer p k). {
      clear IHE1 IHE2 H4 E2 H2 E1 l r H. intros aut IH H1 H2 H3. inversion H2.
        - rewrite <- H0 in H3. simpl in H3. assert (key_eqb k k0 = true). destruct (key_eqb k k0).
          reflexivity. discriminate. rewrite <- H0 in H1. simpl in H1. apply key_eqb_iff in H4.
          rewrite H4. exact H1.
        - symmetry in H. rewrite H in H1. simpl in H1. pose proof (IH _ _ _ H H3).
          apply (prefix_zer_trans p p0 k). exact H1. exact H7. 
    }
    destruct (ith_zer (length p) k).
    + apply app_is_prefix in H4. exact (L r IHE2 H4 E2).
    + apply app_is_prefix in H2. exact (L l IHE1 H2 E1).
Qed.

Lemma insert_content_aug : forall (X : Type) (k : list bool) (v : X) (aut : augCBT),
  (OneTerminated k) -> (augCBT_valid aut) ->
  (equal_content (content_aug (insert_aug k v aut)) (insert_map k v (content_aug aut))).
Proof.
  intros X k v. induction aut.
  - intros H1 H2. unfold equal_content. intro k'. unfold insert_map. unfold content_aug. simpl.
    destruct (critical_bit_zer k0 k) eqn:E.
    + unfold insert_as_branch_aug. destruct (ith_zer n k) eqn:E2.
      * simpl. rewrite take_length. destruct (key_eqb k' k) eqn:E3.
       -- apply key_eqb_iff in E3. rewrite E3 in *. rewrite E2. reflexivity.
       -- destruct (ith_zer n k') eqn:E4. assert (k' <> k0). intro. rewrite <- H in E.
          apply critical_bit_zer_ith_neq in E. apply E. rewrite E2. rewrite E4. reflexivity.
          apply key_eqb_niff in H. rewrite H. reflexivity. reflexivity.
      * simpl. rewrite take_length. destruct (key_eqb k' k) eqn:E3.
       -- apply key_eqb_iff in E3. rewrite E3. rewrite E2. reflexivity.
       -- destruct (ith_zer n k') eqn:E4. reflexivity. assert (k' <> k0). intro.
          rewrite <- H in E. apply critical_bit_zer_ith_neq in E. apply E.
          rewrite E2. rewrite E4. reflexivity. apply key_eqb_niff in H. rewrite H. reflexivity.
    + inversion H2. apply (critical_bit_zer_none_eq _ _ H0 H1) in E. rewrite E in *.
      simpl. destruct (key_eqb k' k). reflexivity. reflexivity.
  - intros H1 H2. simpl. destruct (critical_bit_fin k p) eqn:E.
    (* inserting k creates a new top-level branch *)
    + clear IHaut1 IHaut2. unfold insert_as_branch_aug. unfold equal_content. intros k' H.
      unfold insert_map. unfold content_aug. simpl. destruct (key_eqb k' k) eqn:E2.
      * apply key_eqb_iff in E2. rewrite E2 in *. destruct (ith_zer n k) eqn:E3.
       -- simpl. rewrite take_length. rewrite E3. rewrite key_eqb_reflx. reflexivity.
       -- simpl. rewrite take_length. rewrite E3. rewrite key_eqb_reflx. reflexivity.
      * remember (AugBranch p aut1 aut2) as aut. destruct (lookup k' (strip_augCBT aut)) eqn:E3.
       -- assert (is_prefix_zer p k'). rewrite Heqaut in H2. rewrite Heqaut in E3.
          exact (lookup_some_has_prefix _ _ x _ _ _ H H2 E3). assert (ith_zer n k <> ith_zer n k').
          { intro. apply prefix_iff_take_eq in H0. assert (S n <= length p).
          apply (length_critical_bit_fin _ _ _ E). apply critical_bit_fin_zer in E.
          apply critical_bit_zer_ith_neq in E. apply (ith_from_take _ _ k') in H4. rewrite H0 in H4.
          apply E. rewrite H3. rewrite H4. reflexivity. } rewrite Heqaut in E3. pose proof E3. simpl in E3.
          rewrite E3. clear E3 H0. destruct (ith_zer n k).
         ++ simpl. rewrite take_length. apply not_eq_sym in H3. apply not_true_is_false in H3. rewrite H3.
          rewrite Heqaut. exact H4.
         ++ simpl. rewrite take_length. apply not_eq_sym in H3. apply not_false_is_true in H3. rewrite H3.
          rewrite Heqaut. exact H4.
       -- pose proof E3. rewrite Heqaut in E3. simpl in E3. rewrite E3. clear E3. destruct (ith_zer n k).
         ++ simpl. rewrite take_length. rewrite H0. rewrite E2. destruct (ith_zer n k').
            reflexivity. reflexivity.
         ++ simpl. rewrite take_length. rewrite H0. rewrite E2. destruct (ith_zer n k').
            reflexivity. reflexivity.
    (* k is inserted below the current top-level branch *)
    + unfold equal_content. intros k' H. unfold insert_map. unfold content_aug.
      inversion H2. specialize (IHaut1 H1 H5 k' H) as IH1. specialize (IHaut2 H1 H7 k' H) as IH2.
      clear IHaut1 IHaut2 H3 l H4 r p0 H0.
      unfold content_aug in *. unfold insert_map in *. destruct (ith_zer (length p) k) eqn:E2.
      * simpl. destruct (ith_zer (length p) k') eqn:E3.
       -- exact IH2.
       -- destruct (key_eqb k' k) eqn:E4. apply key_eqb_iff in E4. rewrite E4 in E3. rewrite E3 in E2.
          discriminate. reflexivity.
      * simpl. destruct (ith_zer (length p) k') eqn:E3.
       -- destruct (key_eqb k' k) eqn:E4. apply key_eqb_iff in E4. rewrite E4 in E3. rewrite E3 in E2.
          discriminate. reflexivity.
       -- exact IH1.
Qed.

Lemma insert_aug_match_com : forall (X : Type) (k : list bool) (v : X) (aut : augCBT),
  (OneTerminated k) -> (augCBT_valid aut) ->
  (strip_augCBT (insert_aug k v aut) = insert k v (strip_augCBT aut)).
Proof.
  intros X k v aut H1 H2. unfold insert. pose proof (insert_aug_match X k v aut [] H1 H2).
  specialize (H (ipfz1 _) (is_prefix_nil _)). destruct H as [_ [H _]].
  rewrite (critical_bit_aug_match _ _ _ H2) in H. exact H.
Qed.

Lemma insert_aug_valid : forall (X : Type) (k : list bool) (v : X) (aut : augCBT),
  (OneTerminated k) -> (augCBT_valid aut) -> (augCBT_valid (insert_aug k v aut)).
Proof.
  intros X k v aut H1 H2. unfold insert. pose proof (insert_aug_match X k v aut [] H1 H2).
  specialize (H (ipfz1 _) (is_prefix_nil _)). destruct H as [H _]. exact H.
Qed.

Theorem insert_valid : forall (X : Type) (k : list bool) (v : X) (t : CBT),
  (OneTerminated k) -> (CBT_valid t) -> CBT_valid (insert k v t).
Proof.
  intros X k v t H1 H2. inversion H2. rewrite <- H0. clear H0 H t0 H2.
  rewrite <- (insert_aug_match_com _ _ _ _ H1 H3). apply (cv _ (insert_aug k v aut)).
  reflexivity. apply (insert_aug_valid _ _ _ _ H1 H3).
Qed.

Theorem insert_content : forall (X : Type) (k : list bool) (v : X) (t : CBT),
  (OneTerminated k) -> (CBT_valid t) ->
  (equal_content (content (insert k v t)) (insert_map k v (content t))).
Proof.
  intros X k v t H1 H2. inversion H2. rewrite <- H0 in *. clear t0 H H0 H2 t.
  rewrite <- (insert_aug_match_com _ _ _ _ H1 H3). apply (insert_content_aug _ _ _ _ H1 H3).
Qed.