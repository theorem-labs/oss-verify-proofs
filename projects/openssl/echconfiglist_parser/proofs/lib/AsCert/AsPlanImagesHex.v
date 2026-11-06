(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics.
From OSSVerify.openssl.echconfiglist_parser.images Require Import Asan.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import AsanHexScan AsanHexTree.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

(* [comment removed for export] *)
Definition asan_hex2_blocks : list (positive * nat) :=
  [(1%positive, 0%nat); (1%positive, 1%nat); (1%positive, 2%nat); (1%positive, 3%nat); (1%positive, 4%nat); (1%positive, 5%nat); (1%positive, 6%nat); (1%positive, 7%nat); (1%positive, 8%nat); (1%positive, 9%nat); (1%positive, 10%nat); (1%positive, 11%nat); (1%positive, 12%nat); (1%positive, 13%nat); (1%positive, 14%nat); (1%positive, 15%nat); (1%positive, 16%nat); (1%positive, 17%nat); (2%positive, 17%nat); (6%positive, 16%nat); (14%positive, 15%nat); (120%positive, 12%nat)].
Lemma asan_hex2_gallv : gallv Asan_seg_bytes_002 asan_hex2_blocks.
Proof. unfold asan_hex2_blocks. gallv_vm. Qed.
Lemma asan_hex2_0 : scanN Asan_seg_bytes_002 64 0 1 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma asan_hex2 : vpt Asan_seg_bytes_002 0 495616.
Proof.
  change 495616%N with (1 + 495615)%N. apply vpt_app; [exact (scanN_sound _ _ 0 1 asan_hex2_0)|].
  apply (vtree_scan_sound _ asan_hex2_blocks); [exact asan_hex2_gallv| vm_compute; reflexivity].
Qed.

Lemma asan_len2 : Z.to_N (Uint63.to_Z (PrimString.length Asan_seg_bytes_002) / 2) = 495616%N.
Proof. vm_compute. reflexivity. Qed.
Lemma asan_len3 : Z.to_N (Uint63.to_Z (PrimString.length Asan_seg_bytes_003) / 2) = 6418432%N.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition asan_hex3a_blocks : list (positive * nat) :=
  [(1%positive, 0%nat); (1%positive, 1%nat); (1%positive, 2%nat); (1%positive, 3%nat); (1%positive, 4%nat); (1%positive, 5%nat); (1%positive, 6%nat); (1%positive, 7%nat); (1%positive, 8%nat); (1%positive, 9%nat); (1%positive, 10%nat); (1%positive, 11%nat); (1%positive, 12%nat); (1%positive, 13%nat); (1%positive, 14%nat); (1%positive, 15%nat); (1%positive, 16%nat); (1%positive, 17%nat); (1%positive, 18%nat); (2%positive, 18%nat); (48%positive, 14%nat); (98%positive, 13%nat); (198%positive, 12%nat); (796%positive, 10%nat); (6376%positive, 7%nat); (12754%positive, 6%nat)].
Lemma asan_hex3a_gallv : gallv Asan_seg_bytes_003 asan_hex3a_blocks.
Proof. unfold asan_hex3a_blocks. gallv_vm. Qed.
Lemma asan_hex3a_0 : scanN Asan_seg_bytes_003 64 0 1 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma asan_hex3a : vpt Asan_seg_bytes_003 0 816320.
Proof.
  change 816320%N with (1 + 816319)%N. apply vpt_app; [exact (scanN_sound _ _ 0 1 asan_hex3a_0)|].
  apply (vtree_scan_sound _ asan_hex3a_blocks); [exact asan_hex3a_gallv| vm_compute; reflexivity].
Qed.

(* [comment removed for export] *)
Definition asan_hex3b_blocks : list (positive * nat) :=
  [(84047%positive, 4%nat); (5253%positive, 8%nat); (2627%positive, 9%nat); (657%positive, 11%nat); (329%positive, 12%nat); (165%positive, 13%nat); (83%positive, 14%nat); (21%positive, 16%nat); (11%positive, 17%nat); (12%positive, 17%nat); (52%positive, 15%nat); (6784%positive, 8%nat); (13570%positive, 7%nat); (108568%positive, 4%nat); (217138%positive, 3%nat)].
Lemma asan_hex3b_gallv : gallv Asan_seg_bytes_003 asan_hex3b_blocks.
Proof. unfold asan_hex3b_blocks. gallv_vm. Qed.
Lemma asan_hex3b : vpt Asan_seg_bytes_003 1344752 392360.
Proof. apply (vtree_scan_sound _ asan_hex3b_blocks); [exact asan_hex3b_gallv| vm_compute; reflexivity]. Qed.
