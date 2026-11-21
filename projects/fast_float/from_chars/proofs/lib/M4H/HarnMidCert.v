(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (MID_FINS computed in the build by the walk itself, in place of the recorded final state HPMF). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxFacts FxPlan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxChDen FxChain FxChMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require Import AcAst AcSubst.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4H Require HarnChain HarnSubCh HarnMain HarnPM2 HarnCertLib HarnCrlsCert_G HPT_G.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require AsanCallTP.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require AsanCallTP.
Import OSSVerify.Proofs.fast_float.from_chars.lib.M4H.HarnChain OSSVerify.Proofs.fast_float.from_chars.lib.M4H.HarnSubCh OSSVerify.Proofs.fast_float.from_chars.lib.M4H.HarnMain OSSVerify.Proofs.fast_float.from_chars.lib.M4H.HarnPM2 OSSVerify.Proofs.fast_float.from_chars.lib.M4H.HarnCertLib OSSVerify.Proofs.fast_float.from_chars.lib.M4H.HarnCrlsCert_G OSSVerify.Proofs.fast_float.from_chars.lib.M4H.HPT_G OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanCallTP.HPMT OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanCallTP.HPMF.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Definition MID_SUBS : SUBSC := [(HPT_G_S, HPT_G_M, HPT_G_A, CRLS_FINS_G)].
Definition NBM : positive := Eval vm_compute in Pos.pred (s_next HPMT_S).      (* [comment removed for export] *)
(* the walk's own final states, computed in the build: at 727298f3 its hull bounds near 2^47 are tighter than
   the recorded HPMF's, so the certificate's expected output is made by its producer *)
Definition MID_CH : MCH := MIDCH 0 NBM.
Definition MID_RES : option (list (sst * smodel * ast)) := Eval vm_compute in PCHK MID_SUBS MID_CH HPMT_S HPMT_M HPMT_A.
Definition MID_FINS : list (sst * smodel * ast) := match MID_RES with Some l => l | None => [] end.
Lemma mid_cert : PCHK MID_SUBS MID_CH HPMT_S HPMT_M HPMT_A = Some MID_FINS.
Proof. vm_cast_no_check (eq_refl (Some MID_FINS)). Qed.
