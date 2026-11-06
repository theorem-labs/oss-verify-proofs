(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec MmapSim LibIface U1Layout.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Module Ly := U1Layout.

Lemma in_ranges_1 : forall lo hi a, in_ranges [(lo, hi)] a <-> lo <= a < hi.
Proof.
  intros lo hi a. split.
  - intros (l & h & Hin & Hr). destruct Hin as [E|[]]. injection E as <- <-. exact Hr.
  - intros Hr. exists lo, hi. split; [left; reflexivity | exact Hr].
Qed.

Lemma ly_img_low {AC : AllocCeiling} : forall a, in_ranges (ly_img Ly.L) a -> a < alloc_ceiling.
Proof. intros a H. apply in_ranges_1 in H. pose proof ac_bounds_lit. cbn in H. lia. Qed.
Lemma ly_rw_img : forall a, in_ranges (ly_rw Ly.L) a -> in_ranges (ly_img Ly.L) a.
Proof. intros a H. apply in_ranges_1 in H. apply in_ranges_1. cbn in *. lia. Qed.
Lemma ly_relro_img : forall a, in_ranges (ly_relro Ly.L) a -> in_ranges (ly_img Ly.L) a.
Proof. intros a H. apply in_ranges_1 in H. apply in_ranges_1. cbn in *. lia. Qed.
Lemma ly_errno_img : forall a, errno_win Ly.L a -> in_ranges (ly_img Ly.L) a.
Proof. intros a H. unfold errno_win, zwin in H. apply in_ranges_1. cbn in *. lia. Qed.
Lemma ly_img_iff : forall a, in_ranges (ly_img Ly.L) a <-> 0x10000 <= a < 0x124000.
Proof. intros a. apply in_ranges_1. Qed.
Lemma ly_errno_rw : forall a, errno_win Ly.L a -> in_ranges (ly_rw Ly.L) a.
Proof. intros a H. unfold errno_win, zwin in H. apply in_ranges_1. cbn in *. lia. Qed.

Lemma ly_noseg : forall x, 0x124000 <= x -> find_segment Ubsan.M.loaded_segments x 1 = None.
Proof.
  intros x Hx. unfold Ubsan.M.loaded_segments, Ubsan.Ubsan_loaded_segments,
    Ubsan.Ubsan_segment_000, Ubsan.Ubsan_segment_001, Ubsan.Ubsan_segment_002, Ubsan.Ubsan_segment_003, find_segment.
  cbn [seg_base seg_size].
  repeat match goal with
  | |- (if ?c then _ else _) = None =>
      let e := fresh in destruct c eqn:e;
      [apply andb_prop in e; destruct e as [_ e]; apply Z.leb_le in e; cbn in e; lia|clear e]
  end.
  reflexivity.
Qed.

Lemma ly_rw_not_relro : forall a, in_ranges (ly_rw Ly.L) a -> ~ in_ranges (ly_relro Ly.L) a.
Proof. intros a H H'. apply in_ranges_1 in H. apply in_ranges_1 in H'. cbn in *. lia. Qed.
