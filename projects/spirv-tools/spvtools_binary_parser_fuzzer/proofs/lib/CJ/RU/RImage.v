(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Lib Require Import Tac Mem.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.RU Require Import RMallocRep.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import AllocCeil RunRandom.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Lib Require Import AcLia.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Open Scope Z_scope.
Section AC_1. Context {ACEIL : AllocCeiling} {RRND : RunRandom}.

Definition RIMG_LO : Z := 0x10000.
Definition RIMG_HI : Z := 0x124000.
Definition RRO_HI  : Z := 0xe8000.
Definition RRW_LO  : Z := 0xef000.

Lemma seg0w : seg_writable Ubsan_segment_000 = false. Proof. cbv [seg_writable Ubsan_segment_000 seg_perms]; reflexivity. Qed.
Lemma seg1w : seg_writable Ubsan_segment_001 = false. Proof. cbv [seg_writable Ubsan_segment_001 seg_perms]; reflexivity. Qed.
Lemma seg2w : seg_writable Ubsan_segment_002 = true. Proof. cbv [seg_writable Ubsan_segment_002 seg_perms]; reflexivity. Qed.
Lemma seg3w : seg_writable Ubsan_segment_003 = true. Proof. cbv [seg_writable Ubsan_segment_003 seg_perms]; reflexivity. Qed.

Lemma ref_ro_addr_true_range : forall x : word, ro_addr rsegs x = true -> RIMG_LO <= bv_unsigned x < RRO_HI.
Proof.
  intros x H. unfold ro_addr, RIMG_LO, RRO_HI in *.
  unfold rsegs, Ubsan.M.loaded_segments, Ubsan.Ubsan_loaded_segments in H. cbn [find_segment] in H.
  replace (Z.of_N (seg_base Ubsan_segment_000)) with 65536%Z in H by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size Ubsan_segment_000)) with 348160%Z in H by (vm_compute; reflexivity).
  replace (Z.of_N (seg_base Ubsan_segment_001)) with 413696%Z in H by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size Ubsan_segment_001)) with 536576%Z in H by (vm_compute; reflexivity).
  replace (Z.of_N (seg_base Ubsan_segment_002)) with 950272%Z in H by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size Ubsan_segment_002)) with 28672%Z in H by (vm_compute; reflexivity).
  replace (Z.of_N (seg_base Ubsan_segment_003)) with 978944%Z in H by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size Ubsan_segment_003)) with 217088%Z in H by (vm_compute; reflexivity).
  set (z := bv_unsigned x) in *.
  destruct (Z.leb_spec0 65536 z); destruct (Z.leb_spec0 (z + 1) (65536 + 348160)); cbn [andb] in H; try lia.
  all: destruct (Z.leb_spec0 413696 z); destruct (Z.leb_spec0 (z + 1) (413696 + 536576)); cbn [andb] in H; try lia.
  all: destruct (Z.leb_spec0 950272 z); destruct (Z.leb_spec0 (z + 1) (950272 + 28672)); cbn [andb] in H; try lia.
  all: destruct (Z.leb_spec0 978944 z); destruct (Z.leb_spec0 (z + 1) (978944 + 217088)); cbn [andb] in H; try lia.
  all: rewrite ?seg0w, ?seg1w, ?seg2w, ?seg3w in H; try discriminate H; lia.
Qed.

End AC_1.
