(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics.
From OssFuzzTheorems.openssl.echconfiglist_parser.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import AsanHexScan AsanHexTree.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

(* [comment removed for export] *)
Definition asan_hex2_blocks : list (positive * nat) :=
  [(1%positive, 0%nat); (1%positive, 1%nat); (1%positive, 2%nat); (1%positive, 3%nat); (1%positive, 4%nat); (1%positive, 5%nat); (1%positive, 6%nat); (1%positive, 7%nat); (1%positive, 8%nat); (1%positive, 9%nat); (1%positive, 10%nat); (1%positive, 11%nat); (1%positive, 12%nat); (1%positive, 13%nat); (1%positive, 14%nat); (1%positive, 15%nat); (1%positive, 16%nat); (1%positive, 17%nat); (2%positive, 17%nat); (6%positive, 16%nat); (14%positive, 15%nat); (120%positive, 12%nat)].
Lemma asan_hex2_gallv : gallv AsanUbsan_seg_bytes_002 asan_hex2_blocks.
Proof. unfold asan_hex2_blocks. gallv_vm. Qed.
Lemma asan_hex2_0 : scanN AsanUbsan_seg_bytes_002 64 0 1 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma asan_hex2 : vpt AsanUbsan_seg_bytes_002 0 495616.
Proof.
  change 495616%N with (1 + 495615)%N. apply vpt_app; [exact (scanN_sound _ _ 0 1 asan_hex2_0)|].
  apply (vtree_scan_sound _ asan_hex2_blocks); [exact asan_hex2_gallv| vm_compute; reflexivity].
Qed.

Lemma asan_len2 : Z.to_N (Uint63.to_Z (PrimString.length AsanUbsan_seg_bytes_002) / 2) = 495616%N.
Proof. vm_compute. reflexivity. Qed.
Lemma asan_len3 : Z.to_N (Uint63.to_Z (PrimString.length AsanUbsan_seg_bytes_003) / 2) = 6397952%N.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition asan_hex3a_blocks : list (positive * nat) :=
  [(1%positive, 0%nat); (1%positive, 1%nat); (1%positive, 2%nat); (1%positive, 3%nat); (1%positive, 4%nat); (1%positive, 5%nat); (1%positive, 6%nat); (1%positive, 7%nat); (1%positive, 8%nat); (1%positive, 9%nat); (1%positive, 10%nat); (1%positive, 11%nat); (1%positive, 12%nat); (1%positive, 13%nat); (1%positive, 14%nat); (1%positive, 15%nat); (1%positive, 16%nat); (1%positive, 17%nat); (1%positive, 18%nat); (2%positive, 18%nat); (192%positive, 12%nat); (386%positive, 11%nat); (1548%positive, 9%nat); (3098%positive, 8%nat)].
Lemma asan_hex3a_gallv : gallv AsanUbsan_seg_bytes_003 asan_hex3a_blocks.
Proof. unfold asan_hex3a_blocks. gallv_vm. Qed.
Lemma asan_hex3a_0 : scanN AsanUbsan_seg_bytes_003 64 0 1 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma asan_hex3a : vpt AsanUbsan_seg_bytes_003 0 793344.
Proof.
  change 793344%N with (1 + 793343)%N. apply vpt_app; [exact (scanN_sound _ _ 0 1 asan_hex3a_0)|].
  apply (vtree_scan_sound _ asan_hex3a_blocks); [exact asan_hex3a_gallv| vm_compute; reflexivity].
Qed.

(* [comment removed for export] *)
Definition asan_hex3b_blocks : list (positive * nat) :=
  [(82611%positive, 4%nat); (20653%positive, 6%nat); (10327%positive, 7%nat); (1291%positive, 10%nat); (323%positive, 12%nat); (81%positive, 14%nat); (41%positive, 15%nat); (21%positive, 16%nat); (11%positive, 17%nat); (12%positive, 17%nat); (208%positive, 13%nat); (1672%positive, 10%nat); (3346%positive, 9%nat); (6694%positive, 8%nat); (13390%positive, 7%nat); (26782%positive, 6%nat); (107132%positive, 4%nat); (214266%positive, 3%nat)].
Lemma asan_hex3b_gallv : gallv AsanUbsan_seg_bytes_003 asan_hex3b_blocks.
Proof. unfold asan_hex3b_blocks. gallv_vm. Qed.
Lemma asan_hex3b : vpt AsanUbsan_seg_bytes_003 1321776 392360.
Proof. apply (vtree_scan_sound _ asan_hex3b_blocks); [exact asan_hex3b_gallv| vm_compute; reflexivity]. Qed.
