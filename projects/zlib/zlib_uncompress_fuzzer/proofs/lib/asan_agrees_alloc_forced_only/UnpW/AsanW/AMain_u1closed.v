(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW Require Import ZTopC AsanMain.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.Plain Require Import PImg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AsanW Require Import AImg AMalloc_iface AFake_iface AHarness_iface ADriver_iface AInstance AInstanceM AInstanceF AMain_closed AMain_closedI AFreeAll AMain_final AClient_inst.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.U1A Require Import U2AIface InfAIface AHarnessIface InitA EndA InfA_closed HarnA.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT}.
  Notation AIF := (AI_of (@AHI_free rc)).

  (* [comment removed for export] *)
  Theorem inflate_closed_u1 : forall haswin, inflate_stmtA AIF afake_rng haswin.
  Proof.
    exact (inflate_closed AIF fflag afake_rng (inst_fake_flag AHI_free) (inst_fake_release AHI_free) (inst_SM0 AHI_free) (inst_SM2 AHI_free)).
  Qed.

  Theorem harness_closed_u1 : fuzz_oneA_stmt AIF afake_rng.
  Proof.
    apply (harness_closed AIF fflag afake_rng);
      first [ exact (inst_fake_flag AHI_free) | exact (inst_fake_release AHI_free) | exact inst_rng_fs_mono
            | exact (inst_SM0 AHI_free) | exact (inst_SM2 AHI_free)
            | exact (inflateInit_proofA AIF) | exact (inflate_closed_u1 true) | exact (inflate_closed_u1 false) | exact (inflateEnd_proofA AIF)
            | exact (inst_OBC AHI_free) | exact (inst_VCL AHI_free) | exact (inst_TABC1 AHI_free) | exact (inst_TABC2 AHI_free) | exact (inst_CI_LO AHI_free) ].
  Qed.
End CANSEC1.

(* [comment removed for export] *)
Theorem asan_implC_u1 : asan_implC_stmt ASTAGE.
Proof. apply asan_implC_final. intros rc. exact (@harness_closed_u1 rc). Qed.
