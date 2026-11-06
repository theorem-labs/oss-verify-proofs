(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxFacts FxPlan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxChDen FxChain FxChMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require Import AcAst AcSubst.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require Import AsanCallTE.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4HB Require HarnChain HarnEnt HarnMain HarnMainE HarnCertLib.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanCallTE.
Import OSSVerify.Proofs.fast_float.from_chars.lib.M4HB.HarnChain OSSVerify.Proofs.fast_float.from_chars.lib.M4HB.HarnEnt OSSVerify.Proofs.fast_float.from_chars.lib.M4HB.HarnMain OSSVerify.Proofs.fast_float.from_chars.lib.M4HB.HarnMainE OSSVerify.Proofs.fast_float.from_chars.lib.M4HB.HarnCertLib OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanCallTE.HEFP.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition PREP_FINS : list (sst * smodel * ast) := [(HEFP_S, HEFP_M, HEFP_A)].
Definition prep_res : option (list (sst * smodel * ast)) := PCHK [] HARN_PREP_E TCE_S TCE_M TCE_A.
(* [comment removed for export] *)
Lemma prep_cert : PCHK [] HARN_PREP_E TCE_S TCE_M TCE_A = Some PREP_FINS.
Proof. vm_cast_no_check (eq_refl (Some PREP_FINS)). Qed.
(* [comment removed for export] *)
