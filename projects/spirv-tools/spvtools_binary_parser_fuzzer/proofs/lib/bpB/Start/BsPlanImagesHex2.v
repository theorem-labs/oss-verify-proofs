(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BothHexTree.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_BsPlanImagesHex2 () := "K47Corelib4Init9Datatypes3nat02C47Corelib4Init3Nat3subK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01C67Corelib7Numbers6Cyclic5Int63<Uint63Axioms:of_pos_recI47Corelib4Init5Logic3and00K47Corelib4Init5Logic3and01I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4list01C69OSSVerify5KrLib3bpB5Start;BothHexTree5gallvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB5Start;BothHexTree5vtreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB5Start;BothHexTree5gtreeC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes4list02C49OSSVerify5KrImgVTgt_spvtools_binary_parser_fuzzer_bothdTgt_spvtools_binary_parser_fuzzer_both_seg_bytes_003C1@~~~~~~~~~~~~~~~~I69OSSVerify5KrLib3bpB5Start;BothHexTree3ztr00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums8positive00I47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01c69OSSVerify5KrLib3bpB5Start@BsPlanImagesHex2Aasan_hex3c_blocksC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N02C56Stdlib6NArith6BinNat1N3addC69OSSVerify5KrLib3bpB5Start;BothHexTree6coversC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB5Start;BothHexTree@vtree_scan_soundC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB5Start@BsPlanImagesHex2@asan_hex3c_gallvC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.

Definition asan_hex3c_blocks : list (positive * nat) :=
  [(645603%positive, 3%nat); (161401%positive, 5%nat); (80701%positive, 6%nat); (40351%positive, 7%nat); (1261%positive, 12%nat); (631%positive, 13%nat); (79%positive, 16%nat); (20%positive, 18%nat); (42%positive, 17%nat); (688%positive, 13%nat)].
Lemma asan_hex3c_gallv : gallv AsanUbsan_seg_bytes_003 asan_hex3c_blocks.
Proof.
unfold asan_hex3c_blocks. gallv_vm. Qed.
Lemma asan_hex3c : vpt AsanUbsan_seg_bytes_003 5164824 479464.
Proof.
apply (vtree_scan_sound _ asan_hex3c_blocks); [exact asan_hex3c_gallv| vm_compute; reflexivity]. Qed.
