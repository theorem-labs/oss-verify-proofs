(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Lib Require Import Tac Mem.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.R Require Import RMallocRep.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import AllocCeil RunRandom.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Lib Require Import AcLia.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Open Scope Z_scope.
Section AC_1. Context {ACEIL : AllocCeiling} {RRND : RunRandom}.

Definition RIMG_LO : Z := 0x10000.
Definition RIMG_HI : Z := 0x122000.
Definition RRO_HI  : Z := 0xe6000.
Definition RRW_LO  : Z := 0xee000.

Lemma seg0w : seg_writable Plain_segment_000 = false. Proof. cbv [seg_writable Plain_segment_000 seg_perms]; reflexivity. Qed.
Lemma seg1w : seg_writable Plain_segment_001 = false. Proof. cbv [seg_writable Plain_segment_001 seg_perms]; reflexivity. Qed.
Lemma seg2w : seg_writable Plain_segment_002 = true. Proof. cbv [seg_writable Plain_segment_002 seg_perms]; reflexivity. Qed.
Lemma seg3w : seg_writable Plain_segment_003 = true. Proof. cbv [seg_writable Plain_segment_003 seg_perms]; reflexivity. Qed.

Lemma ref_ro_addr_true_range : forall x : word, ro_addr rsegs x = true -> RIMG_LO <= bv_unsigned x < RRO_HI.
Proof.
  intros x H. unfold ro_addr, RIMG_LO, RRO_HI in *.
  unfold rsegs, Plain.M.loaded_segments, Plain.Plain_loaded_segments in H. cbn [find_segment] in H.
  replace (Z.of_N (seg_base Plain_segment_000)) with 65536%Z in H by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size Plain_segment_000)) with 348160%Z in H by (vm_compute; reflexivity).
  replace (Z.of_N (seg_base Plain_segment_001)) with 413696%Z in H by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size Plain_segment_001)) with 528384%Z in H by (vm_compute; reflexivity).
  replace (Z.of_N (seg_base Plain_segment_002)) with 942080%Z in H by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size Plain_segment_002)) with 32768%Z in H by (vm_compute; reflexivity).
  replace (Z.of_N (seg_base Plain_segment_003)) with 974848%Z in H by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size Plain_segment_003)) with 212992%Z in H by (vm_compute; reflexivity).
  set (z := bv_unsigned x) in *.
  destruct (Z.leb_spec0 65536 z); destruct (Z.leb_spec0 (z + 1) (65536 + 348160)); cbn [andb] in H; try lia.
  all: destruct (Z.leb_spec0 413696 z); destruct (Z.leb_spec0 (z + 1) (413696 + 528384)); cbn [andb] in H; try lia.
  all: destruct (Z.leb_spec0 942080 z); destruct (Z.leb_spec0 (z + 1) (942080 + 32768)); cbn [andb] in H; try lia.
  all: destruct (Z.leb_spec0 974848 z); destruct (Z.leb_spec0 (z + 1) (974848 + 212992)); cbn [andb] in H; try lia.
  all: rewrite ?seg0w, ?seg1w, ?seg2w, ?seg3w in H; try discriminate H; lia.
Qed.

End AC_1.
