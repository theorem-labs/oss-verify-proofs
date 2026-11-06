From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Spec Require Import StrFun.
Import ListNotations.
Local Open Scope Z_scope.

Definition slot_nn (pl : list byte) : Z :=
  match find_byte 0 pl with Some i => Z.of_nat i | None => Z.of_nat (length pl) end.

Definition slot_db (pl : list byte) : list byte := firstn (Z.to_nat (slot_nn pl)) pl.

Lemma slot_nn_range : forall pl, 0 <= slot_nn pl <= Z.of_nat (length pl).
Proof.
  intros pl. unfold slot_nn. destruct (find_byte 0 pl) as [i|] eqn:E; [|lia].
  destruct (find_byte_Some _ _ _ E) as (H & _). lia.
Qed.

Lemma slot_db_length : forall pl, Z.of_nat (length (slot_db pl)) = slot_nn pl.
Proof.
  intros pl. unfold slot_db. pose proof (slot_nn_range pl). rewrite firstn_length. lia.
Qed.

Lemma slot_db_nozero : forall pl, ~ In (Z_to_bv 8 0) (slot_db pl).
Proof.
  intros pl Hin. unfold slot_db, slot_nn in Hin. apply In_nth_error in Hin as (k & Hk).
  rewrite nth_error_firstn in Hk. destruct (k <? _)%nat eqn:Lt; [|discriminate].
  apply Nat.ltb_lt in Lt.
  destruct (find_byte 0 pl) as [i|] eqn:E.
  - destruct (find_byte_Some _ _ _ E) as (_ & _ & Hmin).
    rewrite Nat2Z.id in Lt. exact (Hmin k _ Lt Hk eq_refl).
  - exact (find_byte_None _ _ E k _ Hk eq_refl).
Qed.
