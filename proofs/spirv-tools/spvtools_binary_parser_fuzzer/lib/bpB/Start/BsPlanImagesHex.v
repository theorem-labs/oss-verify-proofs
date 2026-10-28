(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BothHexScan BothHexTree.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.

Definition asan_hex2_blocks : list (positive * nat) :=
  [(1%positive, 0%nat); (1%positive, 1%nat); (1%positive, 2%nat); (1%positive, 3%nat); (1%positive, 4%nat); (1%positive, 5%nat); (1%positive, 6%nat); (1%positive, 7%nat); (1%positive, 8%nat); (1%positive, 9%nat); (1%positive, 10%nat); (1%positive, 11%nat); (1%positive, 12%nat); (1%positive, 13%nat); (1%positive, 14%nat)].
Lemma asan_hex2_gallv : gallv AsanUbsan_seg_bytes_002 asan_hex2_blocks.
Proof. unfold asan_hex2_blocks. gallv_vm. Qed.
Lemma asan_hex2_0 : scanN AsanUbsan_seg_bytes_002 64 0 1 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma asan_hex2 : vpt AsanUbsan_seg_bytes_002 0 32768.
Proof.
  change 32768%N with (1 + 32767)%N. apply vpt_app; [exact (scanN_sound _ _ 0 1 asan_hex2_0)|].
  apply (vtree_scan_sound _ asan_hex2_blocks); [exact asan_hex2_gallv| vm_compute; reflexivity].
Qed.

Lemma asan_len2 : Z.to_N (Uint63.to_Z (PrimString.length AsanUbsan_seg_bytes_002) / 2) = 32768%N.
Proof. vm_compute. reflexivity. Qed.
Lemma asan_len3 : Z.to_N (Uint63.to_Z (PrimString.length AsanUbsan_seg_bytes_003) / 2) = 5644288%N.
Proof. vm_compute. reflexivity. Qed.

Definition asan_hex3a_blocks : list (positive * nat) :=
  [(1%positive, 0%nat); (1%positive, 1%nat); (1%positive, 2%nat); (1%positive, 3%nat); (1%positive, 4%nat); (1%positive, 5%nat); (1%positive, 6%nat); (1%positive, 7%nat); (1%positive, 8%nat); (1%positive, 9%nat); (1%positive, 10%nat); (1%positive, 11%nat); (1%positive, 12%nat); (1%positive, 13%nat); (1%positive, 14%nat); (2%positive, 14%nat); (96%positive, 9%nat); (776%positive, 6%nat)].
Lemma asan_hex3a_gallv : gallv AsanUbsan_seg_bytes_003 asan_hex3a_blocks.
Proof. unfold asan_hex3a_blocks. gallv_vm. Qed.
Lemma asan_hex3a_0 : scanN AsanUbsan_seg_bytes_003 64 0 1 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma asan_hex3a : vpt AsanUbsan_seg_bytes_003 0 49728.
Proof.
  change 49728%N with (1 + 49727)%N. apply vpt_app; [exact (scanN_sound _ _ 0 1 asan_hex3a_0)|].
  apply (vtree_scan_sound _ asan_hex3a_blocks); [exact asan_hex3a_gallv| vm_compute; reflexivity].
Qed.

Definition asan_hex3b_blocks : list (positive * nat) :=
  [(36135%positive, 4%nat); (4517%positive, 7%nat); (2259%positive, 8%nat); (565%positive, 10%nat); (283%positive, 11%nat); (71%positive, 13%nat); (9%positive, 16%nat); (5%positive, 17%nat); (6%positive, 17%nat); (28%positive, 15%nat); (58%positive, 14%nat); (472%positive, 11%nat); (946%positive, 10%nat); (1894%positive, 9%nat); (3790%positive, 8%nat); (60656%positive, 4%nat); (121314%positive, 3%nat)].
Lemma asan_hex3b_gallv : gallv AsanUbsan_seg_bytes_003 asan_hex3b_blocks.
Proof. unfold asan_hex3b_blocks. gallv_vm. Qed.
Lemma asan_hex3b : vpt AsanUbsan_seg_bytes_003 578160 392360.
Proof. apply (vtree_scan_sound _ asan_hex3b_blocks); [exact asan_hex3b_gallv| vm_compute; reflexivity]. Qed.
