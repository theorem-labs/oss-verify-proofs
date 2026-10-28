(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics.
From OssFuzzTheorems.openssl.echconfiglist_parser.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import AsanHexTree.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

(* [comment removed for export] *)
Definition asan_hex3c_blocks : list (positive * nat) :=
  [(738555%positive, 3%nat); (184639%positive, 5%nat); (2885%positive, 11%nat); (1443%positive, 12%nat); (361%positive, 14%nat); (181%positive, 15%nat); (91%positive, 16%nat); (23%positive, 18%nat); (96%positive, 16%nat); (194%positive, 15%nat); (780%positive, 13%nat)].
Lemma asan_hex3c_gallv : gallv AsanUbsan_seg_bytes_003 asan_hex3c_blocks.
Proof. unfold asan_hex3c_blocks. gallv_vm. Qed.
Lemma asan_hex3c : vpt AsanUbsan_seg_bytes_003 5908440 489512.
Proof. apply (vtree_scan_sound _ asan_hex3c_blocks); [exact asan_hex3c_gallv| vm_compute; reflexivity]. Qed.
