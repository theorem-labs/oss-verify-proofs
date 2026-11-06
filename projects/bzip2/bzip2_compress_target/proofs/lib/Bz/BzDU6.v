(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock BzDK BzDU5.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDK OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDU5.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition K_L6W (F : nat) (L : dsv) (d : dst) (s : dstrm) : dres := dgo F (coding_check L d s).
Definition K_HHB (F : nat) (L : dsv) (d : dst) (s : dstrm) : dres := dgo F (after_tables L d s).

(* [comment removed for export] *)
Lemma edge_33 : forall F v L d s, dgo F (gb_after 33 v L d s) = K_L6W F (sv_set_i (sv_set_curr L v) 0) d s.
Proof. intros. rewrite gb_after_33. reflexivity. Qed.

(* [comment removed for export] *)
Lemma K_L6W_ret : forall F L d s, (sv_curr L < 1 \/ 20 < sv_curr L) -> K_L6W F L d s = DRet BZ_DATA_ERROR L d s.
Proof.
  intros F L d s H. unfold K_L6W, coding_check.
  replace ((sv_curr L <? 1) || (20 <? sv_curr L)) with true; [apply dgo_DRet|].
  symmetry. apply Bool.orb_true_iff. destruct H; [left|right]; apply Z.ltb_lt; lia.
Qed.
Lemma K_L6W_go : forall F L d s, 1 <= sv_curr L <= 20 -> K_L6W F L d s = drun F 34 L d s.
Proof.
  intros F L d s H. unfold K_L6W, coding_check.
  replace ((sv_curr L <? 1) || (20 <? sv_curr L)) with false; [apply dgo_DGo|].
  symmetry. apply Bool.orb_false_iff. split; apply Z.ltb_ge; lia.
Qed.

(* [comment removed for export] *)
Lemma edge_34_1 : forall F v L d s, v <> 0 -> dgo F (gb_after 34 v L d s) = drun F 35 L d s.
Proof.
  intros F v L d s Hv. rewrite gb_after_34.
  replace (v =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hv). apply dgo_DGo.
Qed.
(* [comment removed for export] *)
Lemma edge_34_0 : forall F v L d s, v = 0 ->
  dgo F (gb_after 34 v L d s) =
  if sv_i L + 1 <? sv_alphaSize L
  then K_L6W F (sv_set_i L (sv_i L + 1)) (d_set_len d (zset (d_len d) (258 * sv_t L + sv_i L) (sv_curr L))) s
  else K_HCOD F (sv_set_t (sv_set_i L (sv_i L + 1)) (sv_t L + 1))
              (d_set_len d (zset (d_len d) (258 * sv_t L + sv_i L) (sv_curr L))) s.
Proof.
  intros F v L d s ->. rewrite gb_after_34. change (0 =? 0) with true. cbv iota. cbv zeta.
  unfold K_L6W, K_HCOD. rewrite !dgo_if, dgo_DGo.
  destruct (sv_i L + 1 <? sv_alphaSize L); [reflexivity|].
  Lsplit L. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma edge_35 : forall F v L d s,
  dgo F (gb_after 35 v L d s) = K_L6W F (sv_set_curr L (if v =? 0 then sv_curr L + 1 else sv_curr L - 1)) d s.
Proof. intros. rewrite gb_after_35. reflexivity. Qed.

(* [comment removed for export] *)
Lemma K_HCOD_exit : forall F L d s, sv_nGroups L <= sv_t L -> K_HCOD F L d s = K_HHB F L d s.
Proof.
  intros F L d s H. unfold K_HCOD, K_HHB.
  replace (sv_t L <? sv_nGroups L) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.
Lemma K_HCOD_go : forall F L d s, sv_t L < sv_nGroups L -> K_HCOD F L d s = drun F 33 L d s.
Proof.
  intros F L d s H. unfold K_HCOD.
  replace (sv_t L <? sv_nGroups L) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition lenp_ok (len : zarr) (alpha t i : Z) : Prop :=
  forall t' i', 0 <= t' -> 0 <= i' < alpha -> (t' < t \/ (t' = t /\ i' < i)) -> 1 <= zget len (258 * t' + i') <= 20.

Lemma lenp_ok_of_rows : forall len alpha t,
  (forall t' i', 0 <= t' < t -> 0 <= i' < alpha -> 1 <= zget len (258 * t' + i') <= 20) -> lenp_ok len alpha t 0.
Proof. intros len alpha t H t' i' Ht' Hi' C. apply H; lia. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma lenp_ok_upd : forall len alpha t i curr, 0 <= t -> 0 <= i < alpha -> alpha <= 258 -> 1 <= curr <= 20 ->
  lenp_ok len alpha t i -> lenp_ok (zset len (258 * t + i) curr) alpha t (i + 1).
Proof.
  intros len alpha t i curr Ht Hi Ha Hc H t' i' Ht' Hi' C. rewrite zget_zset.
  destruct (Z.eqb_spec (258 * t' + i') (258 * t + i)) as [E|NE]; [lia|].
  apply H; [lia|lia|]. destruct C as [C|[-> C]]; [left; exact C|right]. split; [reflexivity|].
  assert (i' <> i) by (intros ->; apply NE; reflexivity). lia.
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sel_okF (L : dsv) (d : dst) : Prop :=
  alpha_ok L d /\ 2 <= sv_nGroups L <= 6 /\ 1 <= sv_nSelectors L <= 18002 /\
  belown (d_sel d) (sv_nSelectors L) (sv_nGroups L).

(* [comment removed for export] *)
Definition dinv_L6W (L : dsv) (d : dst) : Prop :=
  sel_okF L d /\ 0 <= sv_t L < sv_nGroups L /\ 0 <= sv_i L < sv_alphaSize L /\ 0 <= sv_curr L <= 32 /\
  lenp_ok (d_len d) (sv_alphaSize L) (sv_t L) (sv_i L).

(* [comment removed for export] *)
Definition dinv_HHB (L : dsv) (d : dst) : Prop :=
  sel_okF L d /\ sv_t L = sv_nGroups L /\
  (forall t i, 0 <= t < sv_nGroups L -> 0 <= i < sv_alphaSize L -> 1 <= zget (d_len d) (258 * t + i) <= 20).

(* [comment removed for export] *)
