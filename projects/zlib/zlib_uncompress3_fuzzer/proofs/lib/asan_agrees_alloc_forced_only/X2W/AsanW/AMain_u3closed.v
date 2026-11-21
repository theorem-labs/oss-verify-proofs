(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
Require Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.ZTopC OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.X2W.AsanMain.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Plain Require Import PImg.
Require Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AsanW.AImg OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AsanW.AMalloc_iface OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AsanW.AFake_iface OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AsanW.AHarness_iface OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AsanW.ADriver_iface OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AsanW.AInstance OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AsanW.AInstanceM OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AsanW.AInstanceF OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.X2W.AsanW.AMain_closed OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.X2W.AsanW.AMain_closedI OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AsanW.AFreeAll OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.X2W.AsanW.AMain_final OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AsanW.AClient_inst.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.U3A Require Import U2AIface InfAIface AHarnessIface InitA EndA InfA_closed HarnA.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT}.
  Notation AIF := (AI_of (@AHI_free rc)).

  (* [comment removed for export] *)
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

(* [comment removed for export] *)
Theorem asan_implC_u3 : asan_implC_stmt ASTAGE.
Proof. apply asan_implC_final. intros rc. exact (@harness_closed_u3 rc). Qed.
