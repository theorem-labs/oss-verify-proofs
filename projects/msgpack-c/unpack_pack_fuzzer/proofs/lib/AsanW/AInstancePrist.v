(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Mem Cells Step Frame Arr ITree Nodes Decode.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import ExecF ITreeA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto ABase ABytes AMalloc_iface ARep ARepFrame ALayout AHeapP AInstance AInstanceM AInstanceU AMalloc_iface2 AInstanceU2 APristLaw.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.

Section CANSEC1. Context {rc : runConstT}.

Lemma c8_det : forall (m m' : amem) A (x y : word),
  rw_cells asegs m A [C8 x] -> rw_cells asegs m' A [C8 y] -> (forall i, 0 <= i < 8 -> m' (wa (A + i)) = m (wa (A + i))) -> x = y.
Proof.
  intros m m' A x y [[_ (B0 & B1 & BX)] _] [[_ (_ & _ & BY)] _] AG.
  cbn [cells_bytes cbytes] in BX, BY. rewrite app_nil_r in BX, BY.
  rewrite <- (le_bytes_to_word_le8 x), <- (le_bytes_to_word_le8 y). f_equal.
  apply nth_error_ext. intros i. destruct (Nat.lt_ge_cases i 8) as [LT|GE].
  - rewrite <- (BX i ltac:(rewrite length_le8; exact LT)), <- (BY i ltac:(rewrite length_le8; exact LT)).
    unfold mrd. rewrite (AG (Z.of_nat i) ltac:(lia)). reflexivity.
  - rewrite (proj2 (nth_error_None _ _)) by (rewrite length_le8; exact GE). symmetry. apply nth_error_None. rewrite length_le8. exact GE.
Qed.

Theorem AHU2_prist : prist_det_law AHEAPu2.
Proof.
  intros L RNG st LB m L' RNG' st' LB' m' (ov & [g AH] & _) (ov' & [g' AH'] & _) AG PR c Hc NC.
  pose proof AH as (ALO & _ & [X [AR BL]] & _). pose proof AH' as (ALO' & _ & [X' [AR' BL']] & _).
  destruct AR as (WF & _ & INST & _ & CLS & _). destruct AR' as (WF' & _ & INST' & _ & CLS' & _).
  destruct INST as (I32 & _). destruct INST' as (I32' & _).
  pose proof (alayout_space L ALO) as (SP1 & SP2 & _ & SP4). pose proof (alayout_space L' ALO') as (SP1' & SP2' & _ & SP4').
  pose proof atop_range as AT.

  assert (SB : al_space_beg L' = al_space_beg L).
  { pose proof (c8_det m m' _ _ _ I32 I32' ltac:(intros i Hi; apply AG; left; unfold AINSTANCE, AIMG_HI; lia)) as E.
    apply (f_equal bv_unsigned) in E. rewrite !unsigned_lit in E by lia. symmetry. exact E. }
  assert (HCK : 1 <= c < K_NUM_CLASSES) by (unfold K_NUM_CLASSES; lia).
  destruct (CLS c HCK) as ((_ & REG & _) & _). destruct (CLS' c HCK) as ((_ & REG' & _) & _).
  assert (RIE : aregion_info L' c = aregion_info L c) by (unfold aregion_info; rewrite SB; reflexivity). rewrite RIE in REG'.
  destruct WF as (_ & _ & _ & _ & _ & PERC & _). destruct WF' as (_ & _ & _ & _ & _ & PERC' & _).
  destruct (PERC c HCK) as (A1 & A2 & _). destruct (PERC' c HCK) as (A1' & A2' & _). cbv zeta in A1, A2, A1', A2'.
  destruct (PR c Hc NC) as [AU0 MU0].
  assert (RIB : 0x10007fff8000 <= aregion_info L c /\ aregion_info L c + 128 <= 2^47).
  { unfold aregion_info, K_SPACE_SIZE, K_SPACE_EXTRA, ARI_STRIDE in *. change (2^37) with 137438953472 in *. lia. }

  rw_split REG 2%nat Ra Rb. rw_split Rb 1%nat Rau Rc. rw_split Rc 1%nat Rd Re. rw_split Re 1%nat Rmu Rf.
  rw_split REG' 2%nat Ra' Rb'. rw_split Rb' 1%nat Rau' Rc'. rw_split Rc' 1%nat Rd' Re'. rw_split Re' 1%nat Rmu' Rf'.
  pose proof (c8_det m m' _ _ _ Rau Rau' ltac:(intros i Hi; apply AG; right; lia)) as EA.
  pose proof (c8_det m m' _ _ _ Rmu Rmu' ltac:(intros i Hi; apply AG; right; lia)) as EM.
  apply (f_equal bv_unsigned) in EA, EM. unfold K_FREEARR_OFF in *.
  rewrite !unsigned_lit in EA, EM by lia. lia.
Qed.
End CANSEC1.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import AProto.TwinB ABase.TwinB ABytes.TwinB AMalloc_iface.TwinB ARep.TwinB ARepFrame.TwinB ALayout.TwinB AHeapP.TwinB AInstance.TwinB AInstanceM.TwinB AInstanceU.TwinB AMalloc_iface2.TwinB AInstanceU2.TwinB APristLaw.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.

Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.

Section CANSEC1. Context {rc : runConstT}.

Lemma c8_det : forall (m m' : amem) A (x y : word),
  rw_cells bsegs m A [C8 x] -> rw_cells bsegs m' A [C8 y] -> (forall i, 0 <= i < 8 -> m' (wa (A + i)) = m (wa (A + i))) -> x = y.
Proof.
  intros m m' A x y [[_ (B0 & B1 & BX)] _] [[_ (_ & _ & BY)] _] AG.
  cbn [cells_bytes cbytes] in BX, BY. rewrite app_nil_r in BX, BY.
  rewrite <- (le_bytes_to_word_le8 x), <- (le_bytes_to_word_le8 y). f_equal.
  apply nth_error_ext. intros i. destruct (Nat.lt_ge_cases i 8) as [LT|GE].
  - rewrite <- (BX i ltac:(rewrite length_le8; exact LT)), <- (BY i ltac:(rewrite length_le8; exact LT)).
    unfold mrd. rewrite (AG (Z.of_nat i) ltac:(lia)). reflexivity.
  - rewrite (proj2 (nth_error_None _ _)) by (rewrite length_le8; exact GE). symmetry. apply nth_error_None. rewrite length_le8. exact GE.
Qed.

Theorem AHU2_prist : prist_det_law AHEAPu2.
Proof.
  intros L RNG st LB m L' RNG' st' LB' m' (ov & [g AH] & _) (ov' & [g' AH'] & _) AG PR c Hc NC.
  pose proof AH as (ALO & _ & [X [AR BL]] & _). pose proof AH' as (ALO' & _ & [X' [AR' BL']] & _).
  destruct AR as (WF & _ & INST & _ & CLS & _). destruct AR' as (WF' & _ & INST' & _ & CLS' & _).
  destruct INST as (I32 & _). destruct INST' as (I32' & _).
  pose proof (alayout_space L ALO) as (SP1 & SP2 & _ & SP4). pose proof (alayout_space L' ALO') as (SP1' & SP2' & _ & SP4').
  pose proof atop_range as AT.

  assert (SB : al_space_beg L' = al_space_beg L).
  { pose proof (c8_det m m' _ _ _ I32 I32' ltac:(intros i Hi; apply AG; left; unfold AINSTANCE, AIMG_HI; lia)) as E.
    apply (f_equal bv_unsigned) in E. rewrite !unsigned_lit in E by lia. symmetry. exact E. }
  assert (HCK : 1 <= c < K_NUM_CLASSES) by (unfold K_NUM_CLASSES; lia).
  destruct (CLS c HCK) as ((_ & REG & _) & _). destruct (CLS' c HCK) as ((_ & REG' & _) & _).
  assert (RIE : aregion_info L' c = aregion_info L c) by (unfold aregion_info; rewrite SB; reflexivity). rewrite RIE in REG'.
  destruct WF as (_ & _ & _ & _ & _ & PERC & _). destruct WF' as (_ & _ & _ & _ & _ & PERC' & _).
  destruct (PERC c HCK) as (A1 & A2 & _). destruct (PERC' c HCK) as (A1' & A2' & _). cbv zeta in A1, A2, A1', A2'.
  destruct (PR c Hc NC) as [AU0 MU0].
  assert (RIB : 0x10007fff8000 <= aregion_info L c /\ aregion_info L c + 128 <= 2^47).
  { unfold aregion_info, K_SPACE_SIZE, K_SPACE_EXTRA, ARI_STRIDE in *. change (2^37) with 137438953472 in *. lia. }

  rw_split REG 2%nat Ra Rb. rw_split Rb 1%nat Rau Rc. rw_split Rc 1%nat Rd Re. rw_split Re 1%nat Rmu Rf.
  rw_split REG' 2%nat Ra' Rb'. rw_split Rb' 1%nat Rau' Rc'. rw_split Rc' 1%nat Rd' Re'. rw_split Re' 1%nat Rmu' Rf'.
  pose proof (c8_det m m' _ _ _ Rau Rau' ltac:(intros i Hi; apply AG; right; lia)) as EA.
  pose proof (c8_det m m' _ _ _ Rmu Rmu' ltac:(intros i Hi; apply AG; right; lia)) as EM.
  apply (f_equal bv_unsigned) in EA, EM. unfold K_FREEARR_OFF in *.
  rewrite !unsigned_lit in EA, EM by lia. lia.
Qed.
End CANSEC1.
End TwinB.
