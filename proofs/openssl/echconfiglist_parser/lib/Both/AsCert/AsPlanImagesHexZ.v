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
Definition asan_ia_blocks : list (positive * nat) :=
  [(3099%positive, 8%nat); (775%positive, 10%nat); (97%positive, 13%nat); (49%positive, 14%nat); (25%positive, 15%nat); (13%positive, 16%nat); (7%positive, 17%nat); (4%positive, 18%nat); (160%positive, 13%nat); (644%positive, 11%nat); (2580%positive, 9%nat); (5162%positive, 8%nat); (41304%positive, 5%nat); (82610%positive, 4%nat)].
Lemma asan_ia_gall : gall AsanUbsan_seg_bytes_003 asan_ia_blocks.
Proof. unfold asan_ia_blocks. gall_vm. Qed.   (* [comment removed for export] *)
Lemma asan_ia_zero : zpt AsanUbsan_seg_bytes_003 793344 528432.
Proof. apply (ztree_scan_sound _ asan_ia_blocks); [exact asan_ia_gall| vm_compute; reflexivity]. Qed.

(* [comment removed for export] *)
Definition asan_tab_blocks : list (positive * nat) :=
  [(214267%positive, 3%nat); (53567%positive, 5%nat); (837%positive, 11%nat); (419%positive, 12%nat); (105%positive, 14%nat); (53%positive, 15%nat); (27%positive, 16%nat); (7%positive, 18%nat); (1%positive, 21%nat); (4%positive, 20%nat); (10%positive, 19%nat); (44%positive, 17%nat); (720%positive, 13%nat); (5768%positive, 10%nat); (11538%positive, 9%nat); (23078%positive, 8%nat); (46158%positive, 7%nat); (92318%positive, 6%nat); (369276%positive, 4%nat); (738554%positive, 3%nat)].
Lemma asan_tab_gall : gall AsanUbsan_seg_bytes_003 asan_tab_blocks.
Proof. unfold asan_tab_blocks. gall_vm. Qed.   (* [comment removed for export] *)
Lemma asan_tab_zero : zpt AsanUbsan_seg_bytes_003 1714136 4194304.
Proof. apply (ztree_scan_sound _ asan_tab_blocks); [exact asan_tab_gall| vm_compute; reflexivity]. Qed.
