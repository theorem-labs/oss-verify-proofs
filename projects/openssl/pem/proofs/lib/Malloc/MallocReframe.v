(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.openssl.pem.lib.Spec Require Import STree Malloc MallocCtrl Prog KInv MI_Inv MI_Ext MI_WGroup MI_WEnframe MI_WEnframe2 MI_Reframe.
From OSSVerify.Proofs.openssl.pem.lib.Malloc Require Import MallocRep MallocTree MallocBlocks.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition rf_full_st (st : mstate) (c : cptr) (off' n' : Z) (l : list (aptr * Z)) : mstate :=
  havoc (aadd c (UNIT * off')) n' (wrs l (rf_tick st)).
Definition rf_setsize_st (st : mstate) (c : cptr) (g bg : aptr) (idx off n' : Z) : mstate :=
  rf_full_st st c off n'
    (ss_list (fst bg) (sstart (MR st g) idx + UNIT * off) (sstart (MR st g) idx + get_stride (MR st g) - IB) n' idx).

(* [comment removed for export] *)
Definition rf_move_st (st : mstate) (c : cptr) (g bg : aptr) (idx off' n' : Z) : mstate :=
  rf_full_st st c off' n'
    (mv_list (fst bg) (sstart (MR st g) idx) (sstart (MR st g) idx + UNIT * off') (sstart (MR st g) idx + get_stride (MR st g) - IB) n' idx
             ((sstart (MR st g) idx + UNIT * off' - snd (gbase (MR st g)) - UNIT) / UNIT) off').

Lemma rf_full_ctrl st c off' n' l : ctrl_eq st (rf_full_st st c off' n' l).
Proof.
  unfold rf_full_st. eapply ctrl_eq_trans; [| exact (proj1 (havoc_ctrl _ _ _))].
  eapply ctrl_eq_trans; [| exact (proj1 (wrs_ctrl _ _))]. constructor; reflexivity.
Qed.

Section WithCeiling0. Context {CE__ : Ceiling}.
Lemma reframe_ok_full : forall st c g bg idx off0 n0 off' n' l,
  s_slots st !! c = Some (g, idx) -> hosts st bg g ->
  0 <= off' <= 291 -> 0 <= n' -> UNIT * off' + n' <= get_stride (MR st g) - IB -> get_stride (MR st g) - IB - n' < 2 ^ 32 ->
  (forall q, lastw l q None = lastw (EL (rf_tick st) g bg idx n' off') q None) ->
  (forall a, In a (map fst l) -> In a (map fst (EL (rf_tick st) g bg idx n' off'))) ->
  reframe_ok st c off0 n0 off' n' (rf_full_st st c off' n' l).
Proof.
  intros st c g bg idx off0 n0 off' n' l Hs Hg Ho Hn Hf Hres HLW HIN.
  pose proof (rf_full_ctrl st c off' n' l) as CE.
  split; [exact (ce_regions _ _ CE)|]. split; [exact (ce_secret _ _ CE)|].
  intros L BL LS INV Hk.
  exact (INVL_reframe_full st L BL LS ((c, off0), n0) g bg idx INV Hk Hs Hg off' n' l Ho Hn Hf Hres HLW HIN).
Qed.

Lemma reframe_ok_setsize : forall st c g bg idx off0 n0 n',
  s_slots st !! c = Some (g, idx) -> hosts st bg g ->
  0 <= n' -> UNIT * off0 + n' <= get_stride (MR st g) - IB -> get_stride (MR st g) - IB - n' < 2 ^ 32 ->
  reframe_ok st c off0 n0 off0 n' (rf_setsize_st st c g bg idx off0 n').
Proof.
  intros st c g bg idx off0 n0 n' Hs Hg Hn Hf Hres.
  pose proof (rf_full_ctrl st c off0 n' (ss_list (fst bg) (sstart (MR st g) idx + UNIT * off0) (sstart (MR st g) idx + get_stride (MR st g) - IB) n' idx)) as CE.
  split; [exact (ce_regions _ _ CE)|]. split; [exact (ce_secret _ _ CE)|].
  intros L BL LS INV Hk.
  exact (INVL_reframe_setsize st L BL LS ((c, off0), n0) g bg idx INV Hk Hs Hg n' Hn Hf Hres).
Qed.
Lemma reframe_ok_move : forall st c g bg idx off0 n0 off' n',
  s_slots st !! c = Some (g, idx) -> hosts st bg g ->
  1 <= off' <= 291 -> 0 <= n' -> UNIT * off' + n' <= get_stride (MR st g) - IB -> get_stride (MR st g) - IB - n' < 2 ^ 32 ->
  0 <= (sstart (MR st g) idx + UNIT * off' - snd (gbase (MR st g)) - UNIT) / UNIT < 2 ^ 16 ->
  reframe_ok st c off0 n0 off' n' (rf_move_st st c g bg idx off' n').
Proof.
  intros st c g bg idx off0 n0 off' n' Hs Hg Ho Hn Hf Hres QR.
  pose proof (rf_full_ctrl st c off' n' (mv_list (fst bg) (sstart (MR st g) idx) (sstart (MR st g) idx + UNIT * off') (sstart (MR st g) idx + get_stride (MR st g) - IB) n' idx
             ((sstart (MR st g) idx + UNIT * off' - snd (gbase (MR st g)) - UNIT) / UNIT) off')) as CE.
  split; [exact (ce_regions _ _ CE)|]. split; [exact (ce_secret _ _ CE)|].
  intros L BL LS INV Hk.
  exact (INVL_reframe_move st L BL LS ((c, off0), n0) g bg idx INV Hk Hs Hg off' n' Ho Hn Hf Hres QR).
Qed.
End WithCeiling0.
