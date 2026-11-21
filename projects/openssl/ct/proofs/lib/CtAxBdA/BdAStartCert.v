(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the start-up over the run's entry stack). *)
From OSSVerify.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
From Stdlib Require Import ZArith Bool List.
From LinuxProcessSemantics.LinuxProcessSem Require Import State.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import AxState AxSys AxRun AxSumCk AxStart.
From OSSVerify.Proofs.openssl.ct.lib.CtAxBdA Require Import BdAParams BdAHints BdAStart.
From OSSVerify.Proofs.openssl.ct.lib.CtAxA Require Import ArtA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma bda_cert_main : bda_cert true fin_mainA = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
