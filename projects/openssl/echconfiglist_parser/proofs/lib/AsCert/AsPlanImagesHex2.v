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
Definition asan_hex3c_blocks : list (positive * nat) :=
  [(741427%positive, 3%nat); (185357%positive, 5%nat); (92679%positive, 6%nat); (11585%positive, 9%nat); (5793%positive, 10%nat); (2897%positive, 11%nat); (1449%positive, 12%nat); (725%positive, 13%nat); (363%positive, 14%nat); (91%positive, 16%nat); (23%positive, 18%nat); (96%positive, 16%nat); (194%positive, 15%nat); (390%positive, 14%nat); (782%positive, 13%nat); (1566%positive, 12%nat)].
Lemma asan_hex3c_gallv : gallv Asan_seg_bytes_003 asan_hex3c_blocks.
Proof. unfold asan_hex3c_blocks. gallv_vm. Qed.
Lemma asan_hex3c : vpt Asan_seg_bytes_003 5931416 487016.
Proof. apply (vtree_scan_sound _ asan_hex3c_blocks); [exact asan_hex3c_gallv| vm_compute; reflexivity]. Qed.
