(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan Require Import ZTopC BothMain.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.Plain Require Import PImg.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.BothW Require Import BImg AMalloc_iface AFake_iface AHarness_iface ADriver_iface AInstance AInstanceM AInstanceF
     AMain_closed AMain_closedI AFreeAll AMain_final AClient_inst.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.U3B Require Import U2BIface InfBIface BHarnessIface InitB EndB InfB_closed HarnB.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT}.
  Notation AIF := (AI_of (@AHI_free rc)).

  Theorem inflate_closed_u3 : forall haswin, inflate_stmtA AIF afake_rng haswin.
  Proof.
    exact (inflate_closed AIF fflag afake_rng (inst_fake_flag AHI_free) (inst_fake_release AHI_free) (inst_SM0 AHI_free) (inst_SM2 AHI_free)).
  Qed.

  Theorem harness_closed_u3 : fuzz_oneA_stmt AIF afake_rng.
  Proof.
    apply (harness_closed AIF fflag afake_rng);
      first [ exact (inst_fake_flag AHI_free) | exact (inst_fake_release AHI_free) | exact inst_rng_fs_mono
            | exact (inst_SM1 AHI_free) | exact (inst_SM2 AHI_free)
            | exact (inflateInit_proofA AIF) | exact (inflate_closed_u3 true) | exact (inflate_closed_u3 false) | exact (inflateEnd_proofA AIF)
            | exact (inst_OBC AHI_free) | exact (inst_VCL AHI_free) | exact (inst_TABC1 AHI_free) | exact (inst_TABC2 AHI_free) | exact (inst_CI_LO AHI_free) ].
  Qed.
End CANSEC1.

Theorem both_implC_u3 : both_implC_stmt ASTAGE.
Proof. apply both_implC_final. intros rc. exact (@harness_closed_u3 rc). Qed.
