(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Bool List.
From LinuxProcessSemantics.LinuxProcessSem Require Import State.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import AxState AxSys AxRun AxSumCk AxStart.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.AxBdB Require Import BdAParams BdAHints BdAStart.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.AxB Require Import ArtA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma bda_cert_main : bda_cert fin_mainA = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
