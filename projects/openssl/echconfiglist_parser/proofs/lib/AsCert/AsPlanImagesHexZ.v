(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics.
From OSSVerify.openssl.echconfiglist_parser.images Require Import Asan.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import AsanHexTree.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

(* [comment removed for export] *)
Definition asan_ia_blocks : list (positive * nat) :=
  [(12755%positive, 6%nat); (3189%positive, 8%nat); (1595%positive, 9%nat); (399%positive, 11%nat); (25%positive, 15%nat); (13%positive, 16%nat); (7%positive, 17%nat); (4%positive, 18%nat); (40%positive, 15%nat); (1312%positive, 10%nat); (10504%positive, 7%nat); (21010%positive, 6%nat); (42022%positive, 5%nat); (84046%positive, 4%nat)].
Lemma asan_ia_gall : gall Asan_seg_bytes_003 asan_ia_blocks.
Proof. unfold asan_ia_blocks. gall_vm. Qed.   (* [comment removed for export] *)
Lemma asan_ia_zero : zpt Asan_seg_bytes_003 816320 528432.
Proof. apply (ztree_scan_sound _ asan_ia_blocks); [exact asan_ia_gall| vm_compute; reflexivity]. Qed.

(* [comment removed for export] *)
Definition asan_tab_blocks : list (positive * nat) :=
  [(217139%positive, 3%nat); (54285%positive, 5%nat); (27143%positive, 6%nat); (3393%positive, 9%nat); (1697%positive, 10%nat); (849%positive, 11%nat); (425%positive, 12%nat); (213%positive, 13%nat); (107%positive, 14%nat); (27%positive, 16%nat); (7%positive, 18%nat); (1%positive, 21%nat); (4%positive, 20%nat); (10%positive, 19%nat); (44%positive, 17%nat); (180%positive, 15%nat); (23168%positive, 8%nat); (46338%positive, 7%nat); (370712%positive, 4%nat); (741426%positive, 3%nat)].
Lemma asan_tab_gall : gall Asan_seg_bytes_003 asan_tab_blocks.
Proof. unfold asan_tab_blocks. gall_vm. Qed.   (* [comment removed for export] *)
Lemma asan_tab_zero : zpt Asan_seg_bytes_003 1737112 4194304.
Proof. apply (ztree_scan_sound _ asan_tab_blocks); [exact asan_tab_gall| vm_compute; reflexivity]. Qed.
