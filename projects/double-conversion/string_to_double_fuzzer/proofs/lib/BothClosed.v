(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgP ImgB ImgSame LibIface LibIfaceB LxLib LbLibBClosed RefMain RefMainClosed
  BothTop BothObls RefLim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma plain_closed_B : plain_stmt_B.
Proof. exact (ref_realizes_spec_closed (AL:=SanLim) lib_P). Qed.

(* [comment removed for export] *)
Definition both_closed_abort (C : both_certs) :
  strong_universal_error_free_T_budgets_abort SanitizerBudgets.lim_source SanitizerBudgets.lim_target image_P image_B :=
  both_top_abort_of plain_closed_B lib_B C.
