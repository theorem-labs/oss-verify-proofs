(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ubsan_base and asan_base, which Trevor Hansen made from pinned_both of projects/openssl/pem/proofs/lib/Top/PunyFinal.v at commit 59c0f6933a6b, with PemTop.pinned_ubsan and PemTop.pinned_asan in place of PemTop.pinned_both and u_realizes and a_realizes in place of b_realizes, moved here from lib/ConstAccept.v. *)
From Stdlib Require Import ZArith NArith List QArith String PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run OmniRun.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import Examples Omni SpuriousCfg.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit FinInput Classifier Measure.
From OSSVerify.Core Require Import Images Shapes.
Require OSSVerify.openssl.pem.Images.
Require OSSVerify.Proofs.openssl.pem.lib.Top.PunyFinal.
Require OSSVerify.Proofs.openssl.pem.lib.Top.PemTop.

Lemma ubsan_base :
  strong_universal_error_free_T_scfg Env.alloc_forced_only
    OSSVerify.openssl.pem.Images.plain
    OSSVerify.openssl.pem.Images.ubsan.
Proof. exact (OSSVerify.Proofs.openssl.pem.lib.Top.PemTop.pinned_ubsan OSSVerify.Proofs.openssl.pem.lib.Top.PunyFinal.p_realizes OSSVerify.Proofs.openssl.pem.lib.Top.PunyFinal.u_realizes). Qed.

Lemma asan_base :
  strong_universal_error_free_T_scfg Env.alloc_forced_only
    OSSVerify.openssl.pem.Images.plain
    OSSVerify.openssl.pem.Images.asan.
Proof. exact (OSSVerify.Proofs.openssl.pem.lib.Top.PemTop.pinned_asan OSSVerify.Proofs.openssl.pem.lib.Top.PunyFinal.p_realizes OSSVerify.Proofs.openssl.pem.lib.Top.PunyFinal.a_realizes). Qed.
