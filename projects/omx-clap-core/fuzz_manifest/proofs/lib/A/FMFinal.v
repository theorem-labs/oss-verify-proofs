(* fuzz_manifest's Statements.asan_agrees and Statements.asan_halts from the program part: FMTop.v (the two statements
   from the ASan side TFIB_T) and FMTfibTop.v (TFIB_T at fm's symbols, fm_TFIB_T).
   This is the one file that loads both the plain side (FMPlain.v through FMTop.v: lib/Reusable/YI5b.v and YI5c.v declare
   the plain build's sink instances as global hints) and the ASan side. The plain instances are removed as hints here
   (fuzz_state's guard, A/FSH_Gen.v), and the ASan instance A/AE2k.v tfib_sink_head is an #[export] hint that this
   file does not import, so in this context a bare sink_head or sink_syms argument of the classes the ASan side uses
   (lib/Reusable/YI16.v, YI14.v) resolves to no instance: the two Fail lines below are that test.
   Every name is written with its full path: this context also loads the UBSan twins lib/U/Reusable/YI5b.v, YI5c.v,
   YI14.v, YI16.v, and a short qualifier such as `YI16.sk_ofl_head` binds the U twin here (Locate, 2026-10-29). *)
From Stdlib Require Import ZArith List.
From OSSVerify.omx_clap_core.fuzz_manifest Require Statements.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YI14 YI16 YI5b YI5c.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require FMTfibT FMTop FMTfibTop.

#[global] Remove Hints OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

Fail Definition fm_bare_sink_head : Z :=
  @OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable.YI16.sk_ofl_head _.
Fail Definition fm_bare_sink_syms : Z :=
  @OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable.YI14.sk_ofl_lock _.

Theorem fm_asan_agrees : Statements.asan_agrees.
Proof. exact (FMTop.fm_asan_agrees_of_tfib FMTfibTop.fm_TFIB_T). Qed.

Theorem fm_asan_halts : Statements.asan_halts.
Proof. exact (FMTop.fm_asan_halts_of_tfib FMTfibTop.fm_TFIB_T). Qed.
