(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Bool.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BsPlanImagesHexZ BsMainIface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_BsMainIfaceDepotScan () := "C6ARocqVerifyHarness?AgentSubmission3bpB5Start@BsPlanImagesHexZ=asan_tab_zero".
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Lemma tab_zero_scan : BothHexTree.zpt AsanUbsan_seg_bytes_003 (Z.to_N (0x272f18 - 0x186000)) (Z.to_N 0x400000).
Proof.
ltac2:(KReplay.run1 (kr_t_BsMainIfaceDepotScan ()) [] "g0000o"). Qed.
