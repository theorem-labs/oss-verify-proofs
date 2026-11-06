(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics.
From OSSVerify.boost_beast.http_request.images Require Import AsanUbsan.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import AsanHexTree.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

(* [comment removed for export] *)
Definition both_ia_blocks : list (positive * nat) :=
  [(871%positive, 6%nat); (109%positive, 9%nat); (55%positive, 10%nat); (7%positive, 13%nat); (1%positive, 16%nat); (1%positive, 17%nat); (1%positive, 18%nat); (16%positive, 15%nat); (34%positive, 14%nat); (70%positive, 13%nat); (284%positive, 11%nat); (2280%positive, 8%nat); (4562%positive, 7%nat); (9126%positive, 6%nat); (18254%positive, 5%nat); (36510%positive, 4%nat)].
Lemma both_ia_gall : gall AsanUbsan_seg_bytes_003 both_ia_blocks.
Proof. unfold both_ia_blocks. gall_vm. Qed.   (* [comment removed for export] *)
Lemma both_ia_zero : zpt AsanUbsan_seg_bytes_003 55744 528432.
Proof. apply (ztree_scan_sound _ both_ia_blocks); [exact both_ia_gall| vm_compute; reflexivity]. Qed.

(* [comment removed for export] *)
Definition both_tab_blocks : list (positive * nat) :=
  [(122067%positive, 3%nat); (30517%positive, 5%nat); (15259%positive, 6%nat); (3815%positive, 8%nat); (477%positive, 11%nat); (239%positive, 12%nat); (15%positive, 16%nat); (1%positive, 20%nat); (1%positive, 21%nat); (8%positive, 19%nat); (18%positive, 18%nat); (38%positive, 17%nat); (156%positive, 15%nat); (314%positive, 14%nat); (630%positive, 13%nat); (5048%positive, 10%nat); (10098%positive, 9%nat); (40396%positive, 7%nat); (323176%positive, 4%nat); (646354%positive, 3%nat)].
Lemma both_tab_gall : gall AsanUbsan_seg_bytes_003 both_tab_blocks.
Proof. unfold both_tab_blocks. gall_vm. Qed.   (* [comment removed for export] *)
Lemma both_tab_zero : zpt AsanUbsan_seg_bytes_003 976536 4194304.
Proof. apply (ztree_scan_sound _ both_tab_blocks); [exact both_tab_gall| vm_compute; reflexivity]. Qed.
