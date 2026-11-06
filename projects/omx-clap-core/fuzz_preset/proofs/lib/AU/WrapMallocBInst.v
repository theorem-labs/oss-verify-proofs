(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/AU/WrapMallocBInst.v, with its module paths and addresses changed; 16 of its 34 lines of code are new or changed and 9 lines of the source are left out. *)
(* Theorem Labs, 2026-10: omx-clap-core/fuzz_preset image B (asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43; relocated from pin f8f98a95bc52 by alreloc c4338d099cfb8025): the
   malloc interceptor walk at the real image, closed.
   - wrap_malloc_walk_keep_cf_B: the keep record wrap_malloc_walk_keep_cf (lib/Reusable/YGcfMallocComposeKeep.v:74-102)
     at segs := tfibsegs, B := YD2l.TfibB, every nmax, al := 8, atp := 1 (FROM_MALLOC), acf := 1 (can_fill),
     ARX := YGcfInstBase.ARXq_cf YD2l.TfibB (fun i => i = as_inst YD2l.TfibB) (lib/Reusable/YGcfInstBase.v:480) at
     IM := AU/AGif2cgif.AImg_cgif and ci := AU/CfImgB.CfImg_B, K := WrapMallocBM1.K_B. Field wmk_call is
     WrapMallocBM1.wm_call_B, field wmk_ret is WrapMallocBM2.wm_ret_B.
   - wrap_malloc_walk_cf_B: the plain record wrap_malloc_walk_cf (lib/Reusable/YGcfMallocCompose.v:168-201) at the same
     arguments, by YGcfMallocComposeKeep.wrap_malloc_walk_cf_of_keep (YGcfMallocComposeKeep.v:104).
   The fields' image premises and their witnesses:
   - TfibSyms B (WrapBKit, WrapMallocBSeed, WrapBEntry, WrapMallocBCall, WrapMallocBM1, WrapMallocBM2): at
     YD2l.TfibB, YD2l.TfibB_syms (lib/Reusable/YD2l.v:71, its decidable parts closed by vm_compute).
   - cf_pc_allocate = 0x326a4 (WrapMallocBM1's Hpc): at AU/CfImgB.v's CfImg_B, cf_pc_allocate_B below (vm_compute).
   - tfib_unwind_spec (U1, UnwindImpl's contract over the image's code; the donors' named premise, YFl0.v:24): not a
     table fact but a callee contract; discharged by YFl4.tfib_unwind_ok (lib/Reusable/YFl4.v:1208), a walk.
   Not image facts: the Section hypotheses of WrapMallocBRetRun.v (registers and memory at asan_malloc's return;
   WrapMallocBM2 discharges them at the call); acall_pre_cf (the caller's state), whose conjunct
   ly_bot ly + ACALL_PREFIX < spZ regs (YG0dcf.v:225) is the stack room at Allocate's entry. No premise remains. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YI04 YA0n YG00 YG0f YG0n YB1v YF0m YFl0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG0ncf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YD2l YFl4.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfMallocCompose YGcfMallocComposeKeep YGcfInstBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require CfImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGif2cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import WrapMallocBStmt WrapMallocBM1 WrapMallocBM2.
Local Open Scope Z_scope.

(* The image's Allocate entry at image B's CfImg instance. *)
Lemma cf_pc_allocate_B : @cf_pc_allocate CfImgB.CfImg_B = 0x326a4.
Proof. vm_compute. reflexivity. Qed.

(* The symbol-table premise at the real image (the cited witness, restated here so the report names one lemma). *)
Lemma TfibSyms_B : TfibSyms YD2l.TfibB.
Proof. exact YD2l.TfibB_syms. Qed.

Section I. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {cp : CfParams}.
Local Existing Instance CfImgB.CfImg_B.

(* The keep record at image B, closed. *)
Theorem wrap_malloc_walk_keep_cf_B : forall nmax,
  YGcfMallocComposeKeep.wrap_malloc_walk_keep_cf tfibsegs YD2l.TfibB nmax 8 1 1
    (YGcfInstBase.ARXq_cf YD2l.TfibB (fun i => i = as_inst YD2l.TfibB)) K_B.
Proof.
intros nmax. split.
- exact (wm_call_B YD2l.TfibB TfibSyms_B YFl4.tfib_unwind_ok cf_pc_allocate_B nmax).
- exact (wm_ret_B YD2l.TfibB TfibSyms_B nmax).
Qed.

(* The plain record at image B, from the keep record. *)
Corollary wrap_malloc_walk_cf_B : forall nmax,
  YGcfMallocCompose.wrap_malloc_walk_cf tfibsegs YD2l.TfibB nmax 8 1 1
    (YGcfInstBase.ARXq_cf YD2l.TfibB (fun i => i = as_inst YD2l.TfibB)) K_B.
Proof.
intros nmax. exact (YGcfMallocComposeKeep.wrap_malloc_walk_cf_of_keep tfibsegs YD2l.TfibB nmax 8 1 1 _ K_B
  (wrap_malloc_walk_keep_cf_B nmax)).
Qed.
End I.
