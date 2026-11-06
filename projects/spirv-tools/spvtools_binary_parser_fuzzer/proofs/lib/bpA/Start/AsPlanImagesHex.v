(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import AsanHexScan AsanHexTree.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.

Definition asan_hex2_blocks : list (positive * nat) :=
  [(1%positive, 0%nat); (1%positive, 1%nat); (1%positive, 2%nat); (1%positive, 3%nat); (1%positive, 4%nat); (1%positive, 5%nat); (1%positive, 6%nat); (1%positive, 7%nat); (1%positive, 8%nat); (1%positive, 9%nat); (1%positive, 10%nat); (1%positive, 11%nat); (1%positive, 12%nat); (1%positive, 13%nat); (1%positive, 14%nat); (8%positive, 12%nat)].
Lemma asan_hex2_gallv : gallv Asan_seg_bytes_002 asan_hex2_blocks.
Proof. unfold asan_hex2_blocks. gallv_vm. Qed.
Lemma asan_hex2_0 : scanN Asan_seg_bytes_002 64 0 1 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma asan_hex2 : vpt Asan_seg_bytes_002 0 36864.
Proof.
  change 36864%N with (1 + 36863)%N. apply vpt_app; [exact (scanN_sound _ _ 0 1 asan_hex2_0)|].
  apply (vtree_scan_sound _ asan_hex2_blocks); [exact asan_hex2_gallv| vm_compute; reflexivity].
Qed.

Lemma asan_len2 : Z.to_N (Uint63.to_Z (PrimString.length Asan_seg_bytes_002) / 2) = 36864%N.
Proof. vm_compute. reflexivity. Qed.
Lemma asan_len3 : Z.to_N (Uint63.to_Z (PrimString.length Asan_seg_bytes_003) / 2) = 5640192%N.
Proof. vm_compute. reflexivity. Qed.

Definition asan_hex3a_blocks : list (positive * nat) :=
  [(1%positive, 0%nat); (1%positive, 1%nat); (1%positive, 2%nat); (1%positive, 3%nat); (1%positive, 4%nat); (1%positive, 5%nat); (1%positive, 6%nat); (1%positive, 7%nat); (1%positive, 8%nat); (1%positive, 9%nat); (1%positive, 10%nat); (1%positive, 11%nat); (1%positive, 12%nat); (1%positive, 13%nat); (1%positive, 14%nat); (4%positive, 13%nat); (10%positive, 12%nat); (22%positive, 11%nat); (184%positive, 8%nat)].
Lemma asan_hex3a_gallv : gallv Asan_seg_bytes_003 asan_hex3a_blocks.
Proof. unfold asan_hex3a_blocks. gallv_vm. Qed.
Lemma asan_hex3a_0 : scanN Asan_seg_bytes_003 64 0 1 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma asan_hex3a : vpt Asan_seg_bytes_003 0 47360.
Proof.
  change 47360%N with (1 + 47359)%N. apply vpt_app; [exact (scanN_sound _ _ 0 1 asan_hex3a_0)|].
  apply (vtree_scan_sound _ asan_hex3a_blocks); [exact asan_hex3a_gallv| vm_compute; reflexivity].
Qed.

Definition asan_hex3b_blocks : list (positive * nat) :=
  [(35987%positive, 4%nat); (8997%positive, 6%nat); (4499%positive, 7%nat); (1125%positive, 9%nat); (563%positive, 10%nat); (141%positive, 12%nat); (71%positive, 13%nat); (9%positive, 16%nat); (5%positive, 17%nat); (6%positive, 17%nat); (28%positive, 15%nat); (58%positive, 14%nat); (944%positive, 10%nat); (3780%positive, 8%nat); (7562%positive, 7%nat); (15126%positive, 6%nat); (60508%positive, 4%nat); (121018%positive, 3%nat)].
Lemma asan_hex3b_gallv : gallv Asan_seg_bytes_003 asan_hex3b_blocks.
Proof. unfold asan_hex3b_blocks. gallv_vm. Qed.
Lemma asan_hex3b : vpt Asan_seg_bytes_003 575792 392360.
Proof. apply (vtree_scan_sound _ asan_hex3b_blocks); [exact asan_hex3b_gallv| vm_compute; reflexivity]. Qed.
