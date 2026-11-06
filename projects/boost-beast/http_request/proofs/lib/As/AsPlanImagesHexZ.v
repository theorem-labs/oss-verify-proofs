(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics.
From OSSVerify.boost_beast.http_request.images Require Import Asan.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import AsanHexTree.
Unset Lia Cache.
Import ListNotations.

(* [comment removed for export] *)
Definition asan_ia_blocks : list (positive * nat) :=
  [(429%positive, 7%nat); (215%positive, 8%nat); (27%positive, 11%nat); (7%positive, 13%nat); (1%positive, 16%nat); (1%positive, 17%nat); (1%positive, 18%nat); (16%positive, 15%nat); (34%positive, 14%nat); (70%positive, 13%nat); (568%positive, 10%nat); (1138%positive, 9%nat); (4556%positive, 7%nat); (18228%positive, 5%nat); (36458%positive, 4%nat)].
Lemma asan_ia_gall : gall Asan_seg_bytes_003 asan_ia_blocks.
Proof. unfold asan_ia_blocks. gall_vm. Qed.   (* [comment removed for export] *)
Lemma asan_ia_zero : zpt Asan_seg_bytes_003 54912 528432.
Proof. apply (ztree_scan_sound _ asan_ia_blocks); [exact asan_ia_gall| vm_compute; reflexivity]. Qed.

(* [comment removed for export] *)
Definition asan_tab_blocks : list (positive * nat) :=
  [(121963%positive, 3%nat); (30491%positive, 5%nat); (7623%positive, 7%nat); (953%positive, 10%nat); (477%positive, 11%nat); (239%positive, 12%nat); (15%positive, 16%nat); (1%positive, 20%nat); (1%positive, 21%nat); (8%positive, 19%nat); (18%positive, 18%nat); (38%positive, 17%nat); (156%positive, 15%nat); (314%positive, 14%nat); (630%positive, 13%nat); (10096%positive, 9%nat); (20194%positive, 8%nat); (80780%positive, 6%nat); (323124%positive, 4%nat); (646250%positive, 3%nat)].
Lemma asan_tab_gall : gall Asan_seg_bytes_003 asan_tab_blocks.
Proof. unfold asan_tab_blocks. gall_vm. Qed.   (* [comment removed for export] *)
Lemma asan_tab_zero : zpt Asan_seg_bytes_003 975704 4194304.
Proof. apply (ztree_scan_sound _ asan_tab_blocks); [exact asan_tab_gall| vm_compute; reflexivity]. Qed.
