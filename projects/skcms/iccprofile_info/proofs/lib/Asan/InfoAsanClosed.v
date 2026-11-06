(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require AsFuzzContract.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AxSymExec3 AsanPlanCore AsanPlan AsanMainLib AsanMainDefs AsanMainTree
  AsanMainCertLib AsanMainItab StartupHSAsan AsanMainForest AsanMainCertKWTree AsanMainCertKWClosed.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import InfoAsanFinal.

Definition info_asan_closed := info_asan_final (AsanMainForest.TREE KWT) (AsanMainForest.TREES KWT KW_ok).
Definition info_asan_closed_ca_iff := info_asan_final_ca_iff (AsanMainForest.TREE KWT) (AsanMainForest.TREES KWT KW_ok).
Definition info_asan_closed_cb_iff := info_asan_final_cb_iff (AsanMainForest.TREE KWT) (AsanMainForest.TREES KWT KW_ok).
Check info_asan_closed.
