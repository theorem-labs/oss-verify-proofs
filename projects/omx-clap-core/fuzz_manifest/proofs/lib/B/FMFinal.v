(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/FMFinal.v. *)
(* fuzz_manifest's Statements.asan_ubsan_agrees and Statements.asan_ubsan_halts from the program part: FMTopB.v (the two
   statements from the image-B ASan side TFIB_TB) and FMTfibTop.v (TFIB_TB from the walk of LLVMFuzzerTestOneInput,
   fm_llvmf_walk).
   This is the one image-B file that loads both the plain side (FMPlain.v through FMTopB.v: lib/Reusable/YI5b.v and
   YI5c.v declare the plain build's sink instances as global hints) and the ASan side. The plain instances are removed as
   hints here (fuzz_state's guard, A/FSH_Gen.v), and the ASan instance ReusableB/YE2k.v tfib_sink_head is an #[export]
   hint that this file does not import, so in this context a bare sink_head or sink_syms argument of the classes the ASan
   side uses (lib/Reusable/YI16.v, YI14.v) resolves to no instance: the two Fail lines below are that test.
   Every name is written with its full path: this context also loads the UBSan twins lib/U/Reusable/YI5b.v, YI5c.v,
   YI14.v, YI16.v, and image A's FMTfibT, FMTop beside image B's files, so a short qualifier can bind the other twin. *)
From Stdlib Require Import ZArith List.
From OSSVerify.omx_clap_core.fuzz_manifest Require Statements.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YI14 YI16 YI5b YI5c.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require FMTfibTB FMTopB FMTfibTop.

#[global] Remove Hints OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

Fail Definition fm_bare_sink_head : Z :=
  @OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable.YI16.sk_ofl_head _.
Fail Definition fm_bare_sink_syms : Z :=
  @OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable.YI14.sk_ofl_lock _.

Theorem fm_asan_ubsan_agrees_of_walk :
  OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.FMTfibTop.fm_llvmf_walk ->
  OSSVerify.omx_clap_core.fuzz_manifest.Statements.asan_ubsan_agrees.
Proof.
  intros W.
  exact (OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.FMTopB.fm_asan_ubsan_agrees_of_tfib
    (OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.FMTfibTop.fm_TFIB_TB_of_walk W)).
Qed.

Theorem fm_asan_ubsan_halts_of_walk :
  OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.FMTfibTop.fm_llvmf_walk ->
  OSSVerify.omx_clap_core.fuzz_manifest.Statements.asan_ubsan_halts.
Proof.
  intros W.
  exact (OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.FMTopB.fm_asan_ubsan_halts_of_tfib
    (OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.FMTfibTop.fm_TFIB_TB_of_walk W)).
Qed.
