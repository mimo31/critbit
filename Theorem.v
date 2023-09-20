From CritBit Require Import Front.
From CritBit Require Import KeyUtil.
From CritBit Require Import Main.

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