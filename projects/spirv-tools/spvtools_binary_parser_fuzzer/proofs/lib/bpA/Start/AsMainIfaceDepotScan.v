(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Bool.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import AsPlanImagesHexZ AsMainIface.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_AsMainIfaceDepotScan () := "C69OSSVerify5KrLib3bpA5Start@AsPlanImagesHexZ=asan_tab_zeroC1?~~~~~~~~~~~~~~~".
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Lemma tab_zero_scan : AsanHexTree.zpt Asan_seg_bytes_003 (Z.to_N (0x2715d8 - 0x185000)) (Z.to_N 0x400000).
Proof.
ltac2:(KReplay.run1 (kr_t_AsMainIfaceDepotScan ()) [] "g0000o"). Qed.
