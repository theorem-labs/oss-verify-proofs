(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxFacts FxPlan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxChDen FxChain FxChMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require Import AcAst AcSubst.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4HL Require Import HarnChain HarnSubCh HarnMain HarnPM2 HarnCertLib HPTH HPFHARN HarnMidCert HPMT.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Definition HARN_SUBS : SUBSC := [(HPMT_S, HPMT_M, HPMT_A, MID_FINS)].
Definition HARN_FINS : list (sst * smodel * ast) := [(HPFHARN_S, HPFHARN_M, HPFHARN_A)].
Definition STK_IDX : nat := Eval vm_compute in stk_idx_of HPTH_S.      (* [comment removed for export] *)
Definition HARN_CH : MCH := HARN_ALL_W (genK HPFHARN_S HPFHARN_M (alins_a HPFHARN_A)) STK_IDX 0 NBM.
Lemma harn_cert : PCHK HARN_SUBS HARN_CH HPTH_S HPTH_M HPTH_A = Some HARN_FINS.
Proof. vm_cast_no_check (eq_refl (Some HARN_FINS)). Qed.
