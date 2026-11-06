(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgSame PropExec LibIface.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound LibIfaceA AsanStartup AsanMainClosed AsanTop
  AsanStartupX AsanArgClose AsanRPClose AsanLibClose.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition asan_obls_of (HL : lib_stmt_A) : asan_obls :=
  ASAN_OBLS LINV_A LINV_A_stmt (xall_sound LINV_A LINV_A_stmt) (xlib_sound HL) (xarg_sound LINV_A LINV_A_stmt) (xrp_sound LINV_A LINV_A_stmt).

(* [comment removed for export] *)
Definition asan_top_abort_of (HP : plain_stmt) (HL : lib_stmt_A) (C : asan_certs) :
  strong_universal_error_free_T_budgets_abort SanitizerBudgets.lim_source SanitizerBudgets.lim_target image_P image_A :=
  asan_top_abort HP (asan_obls_of HL) C.
(* [comment removed for export] *)
