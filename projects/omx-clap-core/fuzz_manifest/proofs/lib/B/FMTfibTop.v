(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/FMTfibTop.v, relocated by b_reloc.py (b7comp): every image
   numeral re-derived by symbol / section / string content, revcheck report (internal path). *)
(* fuzz_manifest's image-B ASan side TFIB_TB (FMTfibTB.v) from the relocated core (FMTfibParts.TFIB_TB_of_lib) and the
   program part: fm's library invariant fm_LI (FMH_Harness.v) with its stability and initial facts (FMW_bridge.v), and
   the harness contract fm_lib_x (FMW_harness.v) over the walk of LLVMFuzzerTestOneInput (fm_llvmf_walk, the statement
   of FMW_harness.v's WALK at TfibB).
   This file does not load the plain build's proof (FMPlain.v and its closure): the plain side declares the global
   instance Reusable/YI5b.v src0_sink_head, and no ASan-side statement here may resolve a sink_head against it. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK15 YK18 YK04 YA0n YG00 YG0d YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest Require Import lib.ZTraceSpec.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YB1v YF0m YD2l YCfn YD1u YE2k.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMTfibTB FMTfibParts.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMH_Harness FMW_llvmf0 FMW_bridge FMW_harness.
Import ListNotations.
Local Open Scope Z_scope.

(* the walk of LLVMFuzzerTestOneInput (A_LLVMF = 0x8097c, ReusableB/YCfn.v; FMH_Base.v FM_LLVMF) at fm's symbols TfibB:
   what FMW_harness.v's WALK assumes *)
Definition fm_llvmf_walk : Prop :=
  forall (fx : YK11.FPState) (rc : YM05.RunCeil) regs ly S (W : world tfibsegs) mem md p n pl M live cnt,
  llvmf_pre TfibB regs ly S W mem md p n pl M live cnt ->
  SRr tfibsegs W (cfg_at tfibsegs A_LLVMF regs mem md) (llvmf_post TfibB regs ly S W mem md p n live cnt).

Theorem fm_TFIB_TB_of_walk : fm_llvmf_walk -> TFIB_TB.
Proof.
  intros WALK.
  apply (TFIB_TB_of_lib fm_LI).
  - intros rc fx.
    apply (@fm_lib_x fx rc TfibB).
    + eapply tfib_AIL; first [exact TfibB_syms | apply AR_laws_ok].
    + exact (WALK fx rc).
  - exact fm_LI_stable_holds.
  - exact fm_LI_init_holds.
Qed.
