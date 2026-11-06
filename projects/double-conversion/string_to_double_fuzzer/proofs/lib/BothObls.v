(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgSame PropExec LibIface.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound LibIfaceB BothTableL BothStartup BothMainClosed BothTop
  AsanStartupXBoth AsanArgCloseBoth BothRPClose BothLibClose.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition both_obls_of (HL : lib_stmt_B) : both_obls :=
  BOTH_OBLS LINV_B LINV_B_stmt (xall_sound_B LINV_B LINV_B_stmt) (xlib_sound_B HL) (xarg_sound_B LINV_B LINV_B_stmt) (xrp_sound_B LINV_B LINV_B_stmt).

(* [comment removed for export] *)
Definition both_top_abort_of (HP : plain_stmt_B) (HL : lib_stmt_B) (C : both_certs) :
  strong_universal_error_free_T_budgets_abort SanitizerBudgets.lim_source SanitizerBudgets.lim_target image_P image_B :=
  both_top_abort HP (both_obls_of HL) C.
(* [comment removed for export] *)
