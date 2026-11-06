(* fuzz_manifest's ASan side TFIB_T (FMTfibT.v) from the relocated core (FMTfibParts.TFIB_T_of_lib) and the program
   part: fm's library invariant fm_LI (FMH_Harness.v) with its stability and initial facts (FMW_bridge.v), and the
   harness contract at fm's symbols fm_lib_x_TfibB (FMAsm.v: FMW_harness.v's fm_lib_x with every callee contract and
   image fact instantiated). No premise is left.
   This file does not load the plain build's proof (FMPlain.v and its closure): the plain side declares the global
   instance lib/Reusable/YI5b.v src0_sink_head, and no ASan-side statement here may resolve a sink_head against it. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK15 YK18 YK04 YA0n YG00 YG0d YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest Require Import lib.ZTraceSpec.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v AF0m AD2l.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMTfibT FMTfibParts.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMH_Harness FMW_bridge FMAsm.
Import ListNotations.
Local Open Scope Z_scope.

Theorem fm_TFIB_T : TFIB_T.
Proof.
  apply (TFIB_T_of_lib fm_LI).
  - intros rc fx. exact (@fm_lib_x_TfibB fx rc).
  - exact fm_LI_stable_holds.
  - exact fm_LI_init_holds.
Qed.
