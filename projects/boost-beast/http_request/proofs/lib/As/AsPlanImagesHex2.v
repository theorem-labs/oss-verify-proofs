(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics.
From OSSVerify.boost_beast.http_request.images Require Import Asan.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import AsanHexTree.
Unset Lia Cache.
Import ListNotations.

(* [comment removed for export] *)
Definition asan_hex3c_blocks : list (positive * nat) :=
  [(646251%positive, 3%nat); (161563%positive, 5%nat); (40391%positive, 7%nat); (5049%positive, 10%nat); (2525%positive, 11%nat); (1263%positive, 12%nat); (79%positive, 16%nat); (20%positive, 18%nat); (42%positive, 17%nat); (688%positive, 13%nat)].
Lemma asan_hex3c_gallv : gallv Asan_seg_bytes_003 asan_hex3c_blocks.
Proof. unfold asan_hex3c_blocks. gallv_vm. Qed.
Lemma asan_hex3c : vpt Asan_seg_bytes_003 5170008 474280.
Proof. apply (vtree_scan_sound _ asan_hex3c_blocks); [exact asan_hex3c_gallv| vm_compute; reflexivity]. Qed.
