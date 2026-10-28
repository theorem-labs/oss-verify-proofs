(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BothHexTree.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.

Definition asan_ia_blocks : list (positive * nat) :=
  [(777%positive, 6%nat); (389%positive, 7%nat); (195%positive, 8%nat); (49%positive, 10%nat); (25%positive, 11%nat); (13%positive, 12%nat); (7%positive, 13%nat); (1%positive, 16%nat); (1%positive, 17%nat); (1%positive, 18%nat); (16%positive, 15%nat); (34%positive, 14%nat); (140%positive, 12%nat); (1128%positive, 9%nat); (9032%positive, 6%nat); (18066%positive, 5%nat); (36134%positive, 4%nat)].
Lemma asan_ia_gall : gall AsanUbsan_seg_bytes_003 asan_ia_blocks.
Proof.
unfold asan_ia_blocks. gall_vm. Qed.
Lemma asan_ia_zero : zpt AsanUbsan_seg_bytes_003 49728 528432.
Proof.
apply (ztree_scan_sound _ asan_ia_blocks); [exact asan_ia_gall| vm_compute; reflexivity]. Qed.

Definition asan_tab_blocks : list (positive * nat) :=
  [(121315%positive, 3%nat); (30329%positive, 5%nat); (15165%positive, 6%nat); (7583%positive, 7%nat); (237%positive, 12%nat); (119%positive, 13%nat); (15%positive, 16%nat); (1%positive, 20%nat); (1%positive, 21%nat); (8%positive, 19%nat); (18%positive, 18%nat); (38%positive, 17%nat); (156%positive, 15%nat); (314%positive, 14%nat); (2520%positive, 11%nat); (5042%positive, 10%nat); (10086%positive, 9%nat); (20174%positive, 8%nat); (322800%positive, 4%nat); (645602%positive, 3%nat)].
Lemma asan_tab_gall : gall AsanUbsan_seg_bytes_003 asan_tab_blocks.
Proof.
unfold asan_tab_blocks. gall_vm. Qed.
Lemma asan_tab_zero : zpt AsanUbsan_seg_bytes_003 970520 4194304.
Proof.
apply (ztree_scan_sound _ asan_tab_blocks); [exact asan_tab_gall| vm_compute; reflexivity]. Qed.
