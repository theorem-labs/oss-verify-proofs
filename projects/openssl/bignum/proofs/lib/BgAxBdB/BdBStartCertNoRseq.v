(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from this unit's BgAxBdB/BdBStartCert.v for LPS 727298f3: the same start-up certificate, computed in the build, for the start state with the CONFIG_RSEQ flag off. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.

From Stdlib Require Import ZArith Bool List.
From LinuxProcessSemantics.LinuxProcessSem Require Import State.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import AxState AxSys AxRun AxSumCk AxStart.
From OSSVerify.Proofs.openssl.bignum.lib.BgAxBdB Require Import BdBParams BdBHints BdBStart.
From OSSVerify.Proofs.openssl.bignum.lib.BgAxB Require Import ArtB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(** the 27-pair layout: the same analysis from the entry state without rseq *)
Lemma bdb_cert_main_norseq : bdb_cert false fin_mainB = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
