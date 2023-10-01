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
*)

Require Import List.
Require Import Nat.
Require Import Bool.
Require Import Arith.
Require Import Arith.Compare.
Require Import Logic.FunctionalExtensionality.
Import ListNotations.

From CritBit Require Import Front.
From CritBit Require Import GenerUtil.
From CritBit Require Import KeyUtil.
From CritBit Require Import PrefixCritical.
From CritBit Require Import SeqAccess.

Definition content_map (X : Type) : Type := list bool -> option X.

Definition singleton {X : Type} (k : list bool) (v : X) : content_map X
  := fun k' => if key_eqb k k' then Some v else None.

Definition cbit_union {X : Type} (cbit : nat) (m0 m1 : content_map X) : content_map X
  := fun k' => if ith_zer cbit k' then m1 k' else m0 k'.

Inductive pmCBT_valid {X : Type} : prefix -> content_map X -> @CBT X -> Prop :=
| pcv_leaf (k : list bool) (v : X) (H : OneTerminated k)
  : pmCBT_valid (ZeroExt k) (singleton k v) (Leaf k v)
| pcv_branch (p : list bool) (pl pr : prefix) (ml mr : content_map X) (l r : CBT)
    (Hl : pmCBT_valid pl ml l) (Hr : pmCBT_valid pr mr r)
    (Hpl : is_prefix (p ++ [false]) pl) (Hpr : is_prefix (p ++ [true]) pr)
  : pmCBT_valid (Finite p) (cbit_union (length p) ml mr) (Branch (length p) l r).

Definition pCBT_valid {X : Type} (p : prefix) (t : @CBT X) : Prop :=
  exists m, pmCBT_valid p m t.

Lemma pmCBT_valid_forget_m : forall (X : Type)
                                    (p : prefix) (m : content_map X) (t : CBT),
    pmCBT_valid p m t -> pCBT_valid p t.
Proof.
  intros X p m t H. exists m. assumption.
Qed.

Definition mCBT_valid {X : Type} (m : content_map X) (t : @CBT X) : Prop :=
  exists p, pmCBT_valid p m t.

Lemma pmCBT_valid_forget_p : forall (X : Type)
                                    (p : prefix) (m : content_map X) (t : CBT),
    pmCBT_valid p m t -> mCBT_valid m t.
Proof.
  intros. exists p. assumption.
Qed.

Definition CBT_valid {X : Type} (t : @CBT X) : Prop :=
  exists p m, pmCBT_valid p m t.

(* ROOM FOR IMPROVEMENT: prove this lemma using the one one below and
   a lemma that the best key is in the content map *)
Lemma best_key_has_prefix : forall (X : Type) (k p : list bool)
                                   (t : @CBT X),
    pCBT_valid (Finite p) t ->
    is_prefix_zer p (find_best_key k t).
Proof.
  intros X k p t. generalize dependent p. induction t.
  - intros p H. destruct H. inversion H.
  - intros p H. simpl. destruct H as [m H]. inversion H. rewrite <- H3 in H.
    clear l r H3 H4 H5 p0 H1 i H0.
    destruct (ith_zer (length p) k) eqn:E.
    + clear IHt1 t1 Hpl pl Hl H. destruct pr eqn:E2.
      * inversion Hr. simpl in *. apply app_is_prefix_zer in Hpr. assumption.
      * apply pmCBT_valid_forget_m in Hr. specialize (IHt2 p0 Hr).
        apply app_is_prefix in Hpr. simpl in Hpr.
        apply (prefix_zer_trans p p0 _ Hpr IHt2).
    + clear IHt2 t2 Hpr pr Hr H. destruct pl eqn:E2.
      * inversion Hl. simpl in *. apply app_is_prefix_zer in Hpl. assumption.
      * apply pmCBT_valid_forget_m in Hl. specialize (IHt1 p0 Hl).
        apply app_is_prefix in Hpl. simpl in Hpl.
        apply (prefix_zer_trans p p0 _ Hpl IHt1).
Qed.

Lemma key_has_prefix : forall (X : Type) (k p : list bool) (m : content_map X)
                                (t : CBT),
    pmCBT_valid (Finite p) m t -> (exists v, m k = Some v) -> is_prefix_zer p k.
Proof.
  intros. remember (Finite p) as pi. generalize dependent p.
  induction H; intros p1 H2.
  - discriminate.
  - destruct H0 as [v H0]. unfold cbit_union in H0. injection H2 as H2. subst p1.
    destruct (ith_zer (length p) k).
    + clear IHpmCBT_valid1 Hpl H l. apply app_is_prefix in Hpr.
      destruct pr eqn:E; simpl in Hpr.
      * inversion H1. subst. unfold singleton in H0. destruct (key_eqb p0 k) eqn:E.
        apply key_eqb_iff in E. subst p0. assumption. discriminate.
      * assert (exists v : X, mr k = Some v). exists v. assumption.
        specialize (IHpmCBT_valid2 H p0 (eq_refl (Finite p0))).
        eapply prefix_zer_trans. eassumption. assumption.
    + clear IHpmCBT_valid2 Hpr H1 r. apply app_is_prefix in Hpl.
      destruct pl eqn:E; simpl in Hpl.
      * inversion H. subst. unfold singleton in H0. destruct (key_eqb p0 k) eqn:E;
          try discriminate. apply key_eqb_iff in E. subst p0. assumption.
      * assert (exists v, ml k = Some v). exists v. assumption.
        specialize (IHpmCBT_valid1 H1 p0 (eq_refl (Finite p0))).
        eapply prefix_zer_trans. eassumption. assumption.
Qed.

Lemma best_key_one_terminated : forall (X : Type) (k : list bool) (t : @CBT X),
    CBT_valid t -> OneTerminated (find_best_key k t).
Proof.
  induction t.
  - intro H. unfold CBT_valid in H. destruct H as [m [p H]]. inversion H. simpl.
    assumption.
  - intro H. simpl. unfold CBT_valid in *. destruct H as [m [p0 H]]. inversion H. rewrite <- H3 in *.
    destruct (ith_zer (length p) k).
    + apply IHt2. exists pr. exists mr. assumption.
    + apply IHt1. exists pl. exists ml. assumption.
Qed.

Lemma is_beforeb_true_exists : forall (o : option nat) (m : nat),
    is_beforeb o m = true -> exists n, o = Some n /\ S n <= m.
Proof.
  intros o m H. destruct o.
  - simpl in H. exists n. split. reflexivity. apply Nat.ltb_lt in H.
    unfold "<" in H. assumption.
  - discriminate.
Qed.

Lemma is_beforeb_false_high_none : forall (o : option nat) (m : nat),
    is_beforeb o m = false -> (o = None \/ exists n, o = Some n /\ m <= n).
Proof.
  intros o m H. destruct o.
  - simpl in H. right. exists n. split. reflexivity. apply Nat.ltb_ge. assumption.
  - left. reflexivity.
Qed.

Lemma high_critbit_is_prefix : forall (X : Type) (k p : list bool) (t : @CBT X),
    pCBT_valid (Finite p) t ->
    is_beforeb (critical_bit_CBT k t) (length p) = false ->
    is_prefix_zer p k.
Proof.
  intros X k p t H1 H2. destruct H1 as [m H1]. inversion H1. rewrite <- H4 in *.
  clear t H4 p0 H0 H3. apply is_beforeb_false_high_none in H2.
  apply pmCBT_valid_forget_m in H1. apply best_key_has_prefix with (k:=k) in H1.
  apply prefix_iff_take_eq in H1. unfold critical_bit_CBT in H2.
  remember (find_best_key k (Branch (length p) l r)) as k'.
  assert (take_zer (length p) k = take_zer (length p) k').
  { destruct H2.
    - rewrite critical_bit_zer_none_eqv in H. specialize (H (length p)). assumption.
    - destruct H as [n [H2 H3]]. apply critical_bit_zer_take_eq in H2.
      rewrite <- (take_take _ n _). rewrite H2. rewrite take_take. reflexivity.
      assumption. assumption. }
  apply prefix_iff_take_eq. rewrite H. assumption.
Qed.

Lemma low_critbit_on_prefix : forall (X : Type) (k p : list bool) (t : @CBT X),
    pCBT_valid (Finite p) t ->
    is_beforeb (critical_bit_CBT k t) (length p) = true ->
    critical_bit_CBT k t = critical_bit_fin k p.
Proof.
  intros X k p t. generalize dependent p. induction t.
  - intros p H. destruct H. inversion H.
  - intros p H1 H2. unfold critical_bit_CBT in *. simpl in *. destruct H1 as [m H1].
    inversion H1. rewrite <- H in *. clear H5 l H6 r H0 p0 H i.
    apply app_is_prefix in Hpl. apply app_is_prefix in Hpr.
    assert (forall (ps : prefix) (t : @CBT X),
               (forall (p : list bool), pCBT_valid (Finite p) t ->
                                      is_beforeb (critical_bit_zer k (find_best_key k t)) (length p) = true ->
                                      critical_bit_zer k (find_best_key k t) = critical_bit_fin k p) ->
               is_beforeb (critical_bit_zer k (find_best_key k t)) (length p) = true ->
               is_prefix p ps ->
               pCBT_valid ps t ->
               critical_bit_zer k (find_best_key k t) = critical_bit_fin k p). {
      clear. intros ps t H1 H2 H3 H4. apply is_beforeb_true_exists in H2.
      destruct H2 as [n [H5 H6]]. destruct ps.
      - destruct H4 as [m H4]. inversion H4. rewrite <- H7 in *. clear H k0 H4 H7 t H2.
        simpl in *. rewrite H5.
        symmetry. apply critical_bit_zer_fin. assumption.
        apply prefix_iff_take_eq in H3. rewrite <- H3. apply critical_bit_zer_from_parts.
        apply critical_bit_zer_take_eq in H5. rewrite take_take.
        assumption. apply Le.le_Sn_le_stt. assumption. rewrite ith_from_take.
        apply critical_bit_zer_ith_neq in H5. assumption. assumption.
      - specialize (H1 p0 H4).
        pose proof (best_key_has_prefix X k p0 t H4).
        remember (find_best_key k t) as k'. clear Heqk' H4. simpl in H3.
        rewrite H5 in *. clear H5. simpl in H1. rewrite Nat.ltb_lt in H1.
        unfold "<" in H1. assert (S n <= length p0). transitivity (length p).
        assumption. apply is_prefix_fin_length. assumption. specialize (H1 H0).
        symmetry. symmetry in H1. apply critical_bit_fin_zer in H1.
        apply critical_bit_zer_fin. assumption. apply is_prefix_fin_zer in H3.
        apply prefix_iff_take_eq in H3. rewrite <- H3.
        apply critical_bit_zer_from_parts. rewrite take_take.
        apply critical_bit_zer_take_eq in H1. assumption. apply Le.le_Sn_le_stt.
        assumption. rewrite ith_from_take. apply critical_bit_zer_ith_neq in H1.
        assumption. assumption.
    } destruct (ith_zer (length p) k).
    + apply pmCBT_valid_forget_m in Hr. apply (H pr t2 IHt2 H2 Hpr Hr).
    + apply pmCBT_valid_forget_m in Hl. apply (H pl t1 IHt1 H2 Hpl Hl).
Qed.

Lemma pcv_finite_len_num : forall (X : Type) (p : list bool) (plen : nat)
                                  (pl pr : prefix) (l r : CBT),
    length p = plen -> is_prefix (p ++ [false]) pl -> is_prefix (p ++ [true]) pr ->
    pCBT_valid pl l -> pCBT_valid pr r -> @pCBT_valid X (Finite p) (Branch plen l r).
Proof.
  intros *. intros H1 H2 H3 H4 H5. rewrite <- H1.
  destruct H4 as [ml H4]. destruct H5 as [mr H5].
  exists (fun k' => if ith_zer (length p) k' then mr k' else ml k').
  apply pcv_branch with (pl:=pl) (pr:=pr).
  assumption. assumption. assumption. assumption.
Qed.

Lemma pmcv_finite_len_num : forall (X : Type) (p : list bool) (plen : nat)
                                   (pl pr : prefix) (ml mr : content_map X) (l r : CBT),
    length p = plen -> is_prefix (p ++ [false]) pl -> is_prefix (p ++ [true]) pr ->
    pmCBT_valid pl ml l -> pmCBT_valid pr mr r ->
    pmCBT_valid (Finite p) (cbit_union plen ml mr) (Branch plen l r).
Proof.
  intros. rewrite <- H. econstructor; eassumption.
Qed.

Definition cmap_insert {X : Type} (k : list bool) (v : X) (m : content_map X)
  : content_map X := (fun k' => if key_eqb k k' then Some v else m k').

Lemma cmap_insert_cbit_singleton : forall (X : Type) (k0 k : list bool) (v0 v : X)
                                          (n : nat),
    critical_bit_zer k k0 = Some n ->
    cmap_insert k v (singleton k0 v0) = if ith_zer n k then
                                          cbit_union n (singleton k0 v0) (singleton k v)
                                        else
                                          cbit_union n (singleton k v) (singleton k0 v0).
Proof.
  intros X k0 k v0 v n H1. unfold cmap_insert. unfold cbit_union.
  apply critical_bit_zer_ith_neq in H1. extensionality k''. unfold singleton.
  destruct (key_eqb k k'') eqn:E.
  - apply key_eqb_iff in E. subst k''.
    destruct (ith_zer n k) eqn:E2; apply not_eq_sym in H1; rewrite E2;
    rewrite (key_eqb_reflx k); reflexivity.
  - destruct (ith_zer n k) eqn:E2; apply bneq_eq_neg in H1; symmetry in H1; simpl in H1;
    rewrite E; destruct (key_eqb k0 k'') eqn:E3; try (apply key_eqb_iff in E3; subst;
    rewrite H1; reflexivity); destruct (ith_zer n k''); reflexivity.
Qed.

Lemma cmap_insert_eqk_singleton : forall (X : Type) (k : list bool) (v0 v : X),
  cmap_insert k v (singleton k v0) = singleton k v.
Proof.
  intros. extensionality k'. unfold cmap_insert. unfold singleton.
  destruct (key_eqb k k'); reflexivity.
Qed.

Lemma cmap_insert_low_cb_branch : forall (X : Type) (k : list bool) (v : X)
                                         (p : list bool) (m : content_map X)
                                         (l r : @CBT X) (n : nat),
    pmCBT_valid (Finite p) m (Branch (length p) l r) ->
    critical_bit_CBT k (Branch (length p) l r) = Some n -> n < length p ->
    cmap_insert k v m = if ith_zer n k then
                          cbit_union n m (singleton k v)
                        else
                          cbit_union n (singleton k v) m.
Proof.
  intros. unfold cmap_insert. extensionality k0. unfold cbit_union.
  destruct (key_eqb k k0) eqn:E.
  - apply key_eqb_iff in E. subst k0. destruct (ith_zer n k) eqn:E;
      rewrite E; unfold singleton; rewrite key_eqb_reflx; reflexivity.
  - destruct (m k0) eqn:E2.
    + assert (exists v, m k0 = Some v). exists x. assumption.
      eapply key_has_prefix in H2; try eassumption.
      assert (ith_zer n k <> ith_zer n p).
      { apply pmCBT_valid_forget_m in H. eapply low_critbit_on_prefix in H.
        rewrite H0 in H. symmetry in H. apply critical_bit_fin_zer in H.
        apply critical_bit_zer_ith_neq in H. assumption.
        rewrite H0. simpl. apply Nat.ltb_lt. assumption. }
      destruct (ith_zer n k); apply bneq_eq_neg in H3; destruct (ith_zer n k0) eqn:E4;
        try (symmetry; assumption); unfold singleton; rewrite E;
        apply prefix_iff_take_eq in H2; eapply ith_from_take in H1; rewrite H2 in H1;
        rewrite E4 in H1; rewrite <- H3 in H1; discriminate.
    + unfold singleton. destruct (ith_zer n k); rewrite E2; rewrite E;
        destruct (ith_zer n k0); reflexivity.
Qed.

Lemma cmap_insert_high_cb_branch : forall (X : Type) (k : list bool) (v : X)
                                          (p : list bool) (ml mr : content_map X)
                                          (l r : @CBT X),
    pmCBT_valid (Finite p) (cbit_union (length p) ml mr) (Branch (length p) l r) ->
    is_beforeb (critical_bit_CBT k (Branch (length p) l r)) (length p) = false ->
    cmap_insert k v (cbit_union (length p) ml mr)
    = if ith_zer (length p) k then
        cbit_union (length p) ml (cmap_insert k v mr)
      else
        cbit_union (length p) (cmap_insert k v ml) mr.
Proof.
  intros.
  apply high_critbit_is_prefix in H0; try (eapply pmCBT_valid_forget_m; eassumption).
  unfold cmap_insert. unfold cbit_union. extensionality k0.
  destruct (ith_zer (length p) k) eqn:E2; destruct (key_eqb k k0) eqn:E;
    try (apply key_eqb_iff in E; subst k0); try rewrite E2; try reflexivity.
Qed.

Theorem insert_correct {X : Type} :
  forall (p : prefix) (m : content_map X) (t : CBT) (k : list bool) (v : X)
         (p' : list bool),
    pmCBT_valid p m t -> is_prefix p' p -> is_prefix_zer p' k -> OneTerminated k ->
    exists pi, is_prefix p' pi /\ pmCBT_valid pi (cmap_insert k v m) (insert k v t).
Proof.
  intros p m t k v p' H. generalize dependent p'. induction H.
  - intros p' H1 H2 H3. unfold insert. unfold critical_bit_CBT. simpl.
    destruct (critical_bit_zer k k0) eqn:E.
    + exists (Finite (take_zer n k)). simpl in *. split.
      * assert (length p' <= n). pose proof (Nat.le_gt_cases (length p') n).
        destruct H0. assumption. unfold "<" in H0. apply critical_bit_zer_ith_neq in E.
        apply (ith_from_prefix _ _ n) in H1. apply (ith_from_prefix _ _ n) in H2.
        rewrite <- H2 in E. apply E in H1. destruct H1. assumption. assumption.
        apply is_prefix_zer_fin. split. apply prefix_iff_take_eq.
        apply prefix_iff_take_eq in H2. rewrite take_take. assumption. assumption.
        rewrite take_length. assumption.
      * unfold insert_as_branch. pose proof (critical_bit_zer_ith_neq _ _ _ E).
        pose proof E as Hcb.
        apply critical_bit_zer_prefix in E.
        assert (pmCBT_valid (ZeroExt k0) (singleton k0 v0) (Leaf k0 v0)).
        { constructor. assumption. }
        assert (pmCBT_valid (ZeroExt k) (singleton k v) (Leaf k v)).
        { apply pcv_leaf. assumption. }
        assert (is_prefix (take_zer n k ++ [negb (ith_zer n k)]) (ZeroExt k0)).
        { simpl. assumption. }
        assert (is_prefix (take_zer n k ++ [ith_zer n k]) (ZeroExt k)).
        { simpl. pose proof (is_prefix_zer_with_ith (take_zer n k) k).
          pose proof (take_is_prefix k n). apply H7 in H8. rewrite take_length in H8.
          assumption. }
        rewrite cmap_insert_cbit_singleton with (n := n).
        -- destruct (ith_zer n k); rewrite <- (take_length n k) at 2;
           rewrite <- (take_length n k) at 3; econstructor; eassumption.
        -- assumption.
    + exists (ZeroExt k). apply (critical_bit_zer_none_eq k k0) in E. subst k0. split.
      * assumption.
      * rewrite cmap_insert_eqk_singleton. constructor. assumption.
      * assumption.
      * assumption.
  - intros p' H1 H2 H3. unfold insert. simpl. 
    destruct ((is_beforeb (critical_bit_CBT k (Branch (length p) l r))) (length p)) eqn:E.
    + pose proof (low_critbit_on_prefix X k p (Branch (length p) l r)).
      Print pcv_branch.
      specialize (H4 (pmCBT_valid_forget_m _ _ _ _ (pcv_branch p pl pr ml mr l r H H0 Hpl Hpr)) E). rewrite H4 in *. apply is_beforeb_true_exists in E. destruct E as [n [H5 H6]].
      rewrite H5. exists (Finite (take_zer n p)). split.
      * simpl. simpl in H1. assert (length p' <= n).
        destruct (le_le_S_dec (length p') n).
        assumption. apply critical_bit_fin_zer in H5.
        apply critical_bit_zer_ith_neq in H5. apply prefix_iff_take_eq in H2.
        apply is_prefix_fin_zer in H1. apply prefix_iff_take_eq in H1.
        assert (ith_zer n p' = ith_zer n p'). reflexivity. rewrite <- H1 in H7 at 2.
        rewrite <- H2 in H7 at 1. rewrite ith_from_take in H7.
        rewrite ith_from_take in H7. apply H5 in H7. destruct H7. assumption.
        assumption. apply is_prefix_zer_fin. split. apply prefix_iff_take_eq.
        apply is_prefix_fin_zer in H1. apply prefix_iff_take_eq in H1.
        rewrite take_take. assumption. assumption. rewrite take_length. assumption.
      * unfold insert_as_branch.
        assert (take_zer n k = take_zer n p).
        { apply critical_bit_fin_zer in H5. apply (critical_bit_zer_take_eq _ _ _ H5). }
        assert (is_prefix (take_zer n p ++ [negb (ith_zer n k)]) (Finite p)).
        { simpl. pose proof (critical_bit_fin_prefix _ _ _ H5).          
          rewrite H7 in H8. assumption. }
        assert (is_prefix (take_zer n p ++ [ith_zer n k]) (ZeroExt k)).
        { simpl. rewrite <- H7. rewrite take_with_ith. apply take_is_prefix. }
        Print pcv_branch.
        assert (pmCBT_valid (Finite p) (cbit_union (length p) ml mr)
                  (Branch (length p) l r)).
        { eapply pcv_branch; eassumption. }
        destruct (ith_zer n k) eqn:E; erewrite cmap_insert_low_cb_branch;
          try erewrite E; try eapply pmcv_finite_len_num; try apply take_length;
          try rewrite H4; try eassumption; try reflexivity; constructor; assumption.
    + exists (Finite p). split; try assumption. unfold critical_bit_CBT.
      erewrite cmap_insert_high_cb_branch; try eapply pcv_branch; try eassumption.
      simpl. apply high_critbit_is_prefix in E;
        try (eapply pmCBT_valid_forget_m; eapply pcv_branch; eassumption).
      unfold insert in *.
      destruct (ith_zer (length p) k) eqn:E2;
        [edestruct IHpmCBT_valid2 as [pi ?] | edestruct IHpmCBT_valid1 as [pi ?]];
        try eassumption; try rewrite <- E2; try apply is_prefix_zer_with_ith;
        try assumption; destruct H4;
        [eapply pcv_branch with (pr := pi) | eapply pcv_branch with (pl := pi)];
        try eassumption.
Qed.

Theorem lookup_correct : forall (X : Type) (p : prefix) (m : content_map X) (t : CBT)
                                (k : list bool),
    OneTerminated k -> pmCBT_valid p m t -> lookup k t = m k.
Proof.
  intros. induction H0.
  - unfold singleton. rewrite key_eqb_sym. reflexivity.
  - unfold cbit_union. simpl. destruct (ith_zer (length p) k); assumption.
Qed.
