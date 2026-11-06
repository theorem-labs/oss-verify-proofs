(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/AU/WrapFreeBWit.v, with its module paths and module names changed; 13 of its 29 lines of code are new or changed and 7 lines of the source are left out. *)
(* Theorem Labs, 2026-10: omx-clap-core/fuzz_preset image B (asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43; relocated from pin f8f98a95bc52 by alreloc c4338d099cfb8025): the
   free interceptor walk as the primed keep record, CLOSED, at the real symbol table YD2l.TfibB
   (lib/Reusable/YD2l.v:13, generated from the unstripped twin) and the real image record AU/CfImgB.CfImg_B
   (lib/AU/CfImgB.v):
   - wf_TB_wit: TfibSyms YD2l.TfibB (the premise TB of WrapFreeBF1.wf_call_B and WrapFreeBF2.wf_ret_B), which is
     YD2l.TfibB_syms (YD2l.v:71; its conjuncts close by reflexivity, lia and vm_compute).
   - wf_HpcD_wit: CfImg_B's cf_pc_deallocate is Deallocate's symbol entry (the premise HpcD of wf_call_B; lib/AU/CfImgB.v
     and YB1w's tfib_A__ZN6__asan9Allocator10Deallocate... (lib/Reusable/YB1w.v) both give 0x32390), closed by vm_compute.
   - wrap_free_walk_keep_cf_rh_B: YGcfMallocComposeKeep.wrap_free_walk_keep_cf_rh (YGcfMallocComposeKeep.v:398-423) at
     segs := tfibsegs, atpD := 1, ARX := YGcfInstBase.ARXq_cf (YGcfInstBase.v:480; IM := AGif2cgif.AImg_cgif by
     instance) with IOK := (fun i => i = as_inst YD2l.TfibB), K := WrapFreeBF2.K_F, built by WrapFreeBStmt.wf_record_of
     from the two fields wf_call_B and wf_ret_B with the two witnesses. No premise: the stack room is acall_pre_cf's
     own conjunct (YG0dcf.v:225), internal_allocator and UnwindImpl are YFfg.tfib_ialloc_ok and YFl4.tfib_unwind_ok.
   - wrap_free_walk_cf_rh_B: the primed record YGcfMallocComposeRh.wrap_free_walk_cf_rh (YGcfMallocComposeRh.v:87) at
     the same arguments, by YGcfMallocComposeKeep.wrap_free_walk_cf_rh_of_keep (YGcfMallocComposeKeep.v:425).
   Reads no listing; proves no function (rule 24). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK04 YA0i YA0n YG00 YG0f YB1v YB1w YF0m YM05 YGcfNames YG0ncf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YD2l.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfMallocComposeRh YGcfMallocComposeKeep YGcfInstBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGif2cgif CfImgB WrapFreeBStmt WrapFreeBF2 WrapFreeBF1.
Local Open Scope Z_scope.

Lemma wf_TB_wit : TfibSyms YD2l.TfibB.
Proof. exact YD2l.TfibB_syms. Qed.

Lemma wf_HpcD_wit : @cf_pc_deallocate CfImg_B =
  tfib_A__ZN6__asan9Allocator10DeallocateEPvmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeE.
Proof. vm_compute. reflexivity. Qed.

Section i. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {cp : CfParams}.
Local Existing Instance CfImg_B.

(* The primed keep record at image B, closed. *)
Theorem wrap_free_walk_keep_cf_rh_B :
  YGcfMallocComposeKeep.wrap_free_walk_keep_cf_rh tfibsegs YD2l.TfibB 1
    (YGcfInstBase.ARXq_cf YD2l.TfibB (fun i => i = as_inst YD2l.TfibB)) K_F.
Proof.
exact (wf_record_of tfibsegs YD2l.TfibB 1 _ K_F (wf_call_B YD2l.TfibB wf_TB_wit wf_HpcD_wit) (wf_ret_B YD2l.TfibB wf_TB_wit)).
Qed.

(* The primed record without the keep, by the keep record's projection. *)
Corollary wrap_free_walk_cf_rh_B :
  YGcfMallocComposeRh.wrap_free_walk_cf_rh tfibsegs YD2l.TfibB 1
    (YGcfInstBase.ARXq_cf YD2l.TfibB (fun i => i = as_inst YD2l.TfibB)) K_F.
Proof.
exact (YGcfMallocComposeKeep.wrap_free_walk_cf_rh_of_keep tfibsegs YD2l.TfibB 1 _ K_F wrap_free_walk_keep_cf_rh_B).
Qed.
End i.
