(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ubsan_base, which Trevor Hansen made from top_ubsan_shipped of projects/mbedtls/fuzz_pkcs7/proofs/lib/U/TopUbsan.v and ubsan_assembled_shipped of projects/mbedtls/fuzz_pkcs7/proofs/lib/U/FinalU.v at source_alloc_limit, and asan_ubsan_base, which he made from top_both of projects/mbedtls/fuzz_pkcs7/proofs/lib/B/TopBoth.v and both_boot and both_main of projects/mbedtls/fuzz_pkcs7/proofs/lib/B/FinalBoth.v, all at commit 59c0f6933a6b, moved here from lib/ConstAccept.v. *)
From Stdlib Require Import ZArith NArith List QArith String PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run OmniRun.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import Examples Omni SpuriousCfg.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit FinInput Classifier Measure.
From OSSVerify.Core Require Import Images Shapes.
Require OSSVerify.mbedtls.fuzz_pkcs7.Images.
Require OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.FinalP.
Require OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_top.
Require OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.TopUbsan.
Require OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.FinalU.
Require OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.B.TopBoth.
Require OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.B.FinalBoth.

Lemma ubsan_base :
  strong_universal_error_free_T OSSVerify.mbedtls.fuzz_pkcs7.Images.plain OSSVerify.mbedtls.fuzz_pkcs7.Images.ubsan.
Proof.
  intros en_s en_t inp Hs Ht Hv.
  exact (OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.TopUbsan.top_ubsan_lim
           (@OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.U_top.U_realizes_spec_lim OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.FinalU.SIU OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.FinalU.SIU_fp OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.U.FinalU.PF_U)
           OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.FinalP.SIP OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.FinalP.SIP_fp OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.FinalP.PF_P
           source_alloc_limit ltac:(apply Z.leb_le; vm_compute; reflexivity) en_s en_t inp Hs Ht Hv).
Qed.

Lemma asan_ubsan_base :
  strong_universal_error_free_T OSSVerify.mbedtls.fuzz_pkcs7.Images.plain OSSVerify.mbedtls.fuzz_pkcs7.Images.asan_ubsan.
Proof.
  exact (OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.B.TopBoth.top_both OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.FinalP.SIP OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.FinalP.SIP_fp OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.FinalP.PF_P
           (OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.B.TopBoth.both_side_of_parts _ OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.B.FinalBoth.both_boot OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.B.FinalBoth.both_main)).
Qed.
