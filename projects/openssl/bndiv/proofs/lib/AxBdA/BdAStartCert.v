(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Bool List.
From LinuxProcessSemantics.LinuxProcessSem Require Import State.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import AxState AxSys AxRun AxSumCk AxStart.
From OSSVerify.Proofs.openssl.bndiv.lib.AxBdA Require Import BdAParams BdAHints BdAStart.
From OSSVerify.Proofs.openssl.bndiv.lib.AxA Require Import ArtA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma bda_cert_main : bda_cert fin_mainA = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
