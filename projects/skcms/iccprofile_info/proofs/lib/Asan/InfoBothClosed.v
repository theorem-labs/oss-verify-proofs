(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require AsFuzzContract.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AxSymExec3 AsanPlanCore AsanPlan AsanMainLib AsanMainHooksBoth AsanMainDefsBoth AsanMainTreeBoth
  AsanMainCertLibBoth AsanMainItabBoth StartupHSBoth AsanMainForestBoth AsanMainCertKWTreeBoth AsanMainCertKWClosedBoth.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import InfoBothFinal.

Definition info_both_closed := info_both_final (AsanMainForestBoth.TREE KWT) (AsanMainForestBoth.TREES KWT KW_ok).
Definition info_both_closed_ca_iff := info_both_final_ca_iff (AsanMainForestBoth.TREE KWT) (AsanMainForestBoth.TREES KWT KW_ok).
Definition info_both_closed_cb_iff := info_both_final_cb_iff (AsanMainForestBoth.TREE KWT) (AsanMainForestBoth.TREES KWT KW_ok).
Check info_both_closed.
