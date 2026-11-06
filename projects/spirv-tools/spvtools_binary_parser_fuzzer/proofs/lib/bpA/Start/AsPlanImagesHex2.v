(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import AsanHexTree.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_AsPlanImagesHex2 () := "K47Corelib4Init9Datatypes3nat02C47Corelib4Init3Nat3subK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01C67Corelib7Numbers6Cyclic5Int63<Uint63Axioms:of_pos_recI47Corelib4Init5Logic3and00K47Corelib4Init5Logic3and01I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4list01C69OSSVerify5KrLib3bpA5Start;AsanHexTree5gallvC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA5Start;AsanHexTree5vtreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA5Start;AsanHexTree5gtreeC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes4list02C49OSSVerify5KrImgVTgt_spvtools_binary_parser_fuzzer_asandTgt_spvtools_binary_parser_fuzzer_asan_seg_bytes_003C1@~~~~~~~~~~~~~~~~I69OSSVerify5KrLib3bpA5Start;AsanHexTree3ztr00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums8positive00I47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01c69OSSVerify5KrLib3bpA5Start@AsPlanImagesHex2Aasan_hex3c_blocksC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N02C56Stdlib6NArith6BinNat1N3addC69OSSVerify5KrLib3bpA5Start;AsanHexTree6coversC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA5Start;AsanHexTree@vtree_scan_soundC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpA5Start@AsPlanImagesHex2@asan_hex3c_gallvC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.

Definition asan_hex3c_blocks : list (positive * nat) :=
  [(645307%positive, 3%nat); (161327%positive, 5%nat); (10083%positive, 9%nat); (2521%positive, 11%nat); (1261%positive, 12%nat); (631%positive, 13%nat); (79%positive, 16%nat); (20%positive, 18%nat); (42%positive, 17%nat); (1376%positive, 12%nat)].
Lemma asan_hex3c_gallv : gallv Asan_seg_bytes_003 asan_hex3c_blocks.
Proof.
unfold asan_hex3c_blocks. gallv_vm. Qed.
Lemma asan_hex3c : vpt Asan_seg_bytes_003 5162456 477736.
Proof.
apply (vtree_scan_sound _ asan_hex3c_blocks); [exact asan_hex3c_gallv| vm_compute; reflexivity]. Qed.
