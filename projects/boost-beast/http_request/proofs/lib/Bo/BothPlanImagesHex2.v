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
Definition both_hex3c_blocks : list (positive * nat) :=
  [(646355%positive, 3%nat); (161589%positive, 5%nat); (80795%positive, 6%nat); (20199%positive, 8%nat); (2525%positive, 11%nat); (1263%positive, 12%nat); (79%positive, 16%nat); (20%positive, 18%nat); (42%positive, 17%nat); (688%positive, 13%nat); (1378%positive, 12%nat)].
Lemma both_hex3c_gallv : gallv AsanUbsan_seg_bytes_003 both_hex3c_blocks.
Proof. unfold both_hex3c_blocks. gallv_vm. Qed.
Lemma both_hex3c : vpt AsanUbsan_seg_bytes_003 5170840 477544.
Proof. apply (vtree_scan_sound _ both_hex3c_blocks); [exact both_hex3c_gallv| vm_compute; reflexivity]. Qed.
