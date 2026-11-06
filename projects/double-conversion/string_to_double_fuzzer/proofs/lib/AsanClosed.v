(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgP ImgA ImgSame LibIface LibIfaceA LxLib LaLibAClosed RefMain RefMainClosed
  AsanTop AsanObls RefLim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma plain_closed : plain_stmt.
Proof. exact (ref_realizes_spec_closed (AL:=SanLim) lib_P). Qed.

(* [comment removed for export] *)
Definition asan_closed_abort (C : asan_certs) :
  strong_universal_error_free_T_budgets_abort SanitizerBudgets.lim_source SanitizerBudgets.lim_target image_P image_A :=
  asan_top_abort_of plain_closed lib_A C.
