(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: added for LPS 727298f3 from this unit's CtAxBdA/BdAStartCert.v: the same start-up certificate for the auxv layout without the CONFIG_RSEQ entry. *)
From OSSVerify.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
From Stdlib Require Import ZArith Bool List.
From LinuxProcessSemantics.LinuxProcessSem Require Import State.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import AxState AxSys AxRun AxSumCk AxStart.
From OSSVerify.Proofs.openssl.ct.lib.CtAxBdA Require Import BdAParams BdAHints BdAStart.
From OSSVerify.Proofs.openssl.ct.lib.CtAxA Require Import ArtA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(** the 27-pair layout: the same analysis from the entry state without rseq *)
Lemma bda_cert_main_norseq : bda_cert false fin_mainA = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
