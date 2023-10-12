From CritBit Require Import Front.
From CritBit Require Import KeyUtil.
From CritBit Require Import Main.
From CritBit Require Import PrefixCritical.

Require Import List.
Import ListNotations.

Theorem seed_spec : forall (X : Type) (k : list bool) (v : X),
    OneTerminated k -> mCBT_valid X (singleton X k v) (seed X k v).
Proof.
  intros. exists (ZeroExt k). constructor. assumption.
Qed.

Theorem insert_spec : forall (X : Type) (k : list bool) (v : X) (m : content_map X)
                             (t : CBT X),
    OneTerminated k -> mCBT_valid X m t -> mCBT_valid X (cmap_insert X k v m) (insert X k v t).
Proof.
  intros. destruct H0 as [p H0].
  edestruct insert_correct with (p' := [] : list bool); try eassumption.
  - apply is_prefix_nil.
  - constructor.
  - eapply pmCBT_valid_forget_p. eapply proj2. eassumption.
Qed.

Theorem lookup_spec : forall (X : Type) (k : list bool) (v : X) (m : content_map X)
                             (t : CBT X),
    OneTerminated k -> mCBT_valid X m t -> lookup X k t = m k.
Proof.
  intros. destruct H0 as [p H0]. eapply lookup_correct; eassumption.
Qed.
