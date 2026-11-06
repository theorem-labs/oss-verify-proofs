(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-30 (a Theorem Labs lane, for lane W of a Theorem Labs lane's cf layer at plugin-hostd/fuzz_reply; first draft by
   ReplyEnqReloc): reply's MALLOC INSTANCE at image A (fuzz_reply.asan, pin 42c58610e125), its Allocate part.
   rule 24: no function proved (kind: statement text; the cf layer's Allocate top at reply's image over reply's Allocate
   walk tops and its unit facts; no named premise is left).

   Export: Allocate's bridge premise aalloc_realizes_cf_em at can_fill 1 and the call-site relation
   ARXq_cf TfibB IOK_reply (IOK_reply := fun i => i = as_inst TfibB), at every FPState and RunCeil: the premise of WalkB2's
   malloc body top (YGcfMallocCompose.amalloc_realizes_cf_of_body route, ReplyMallocBodyUnitA), which gives
   ReplyAllocTargets.amalloc_target_reply.  Route: YGcfMallocComposeE.aalloc_realizes_cf_em_of_m (YGcfMallocComposeE.v:130)
   over YGcfInstWalkSigreply.aalloc_realizes_cf_reply (YGcfInstAllocTop.aalloc_realizes_cf_em_m_cf with WS :=
   walksig_cf_reply: reply's Allocate arms + the interface instances, the image premises from reply's unit facts, HDEP
   from the depot rows).
   No premise is left: the refill walk is B3LeafCf's YGcfRefillTopreply.refill_walk_cf_reply_closed and the secondary
   interface (IFS / IFSE) is CfInstSec's YGcfInstSecreply.ifaceSw_A / ifaceSE_A, both inside YGcfInstWalkSigreply.
   Field round 3 part 3c: aalloc_realizes_cf_em takes the call state's arodata_ok_cf at Allocate's entry (the bridge that
   consumes it derives it from acall_pre_cf); the text of the export is unchanged.
   This file does not Require ReplyAllocTargets (its realloc bridges reach Reusable/YGcallcf.v). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AGif2reply ImgBaseAG AGif0reply ImgBaseAGS AGif4reply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AF0m AF0x CfImgA CfParamsReply AD2l.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import YGcfMallocCompose YGcfMallocComposeE.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import YGcfInstBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require YGcfInstWalkSigreply.
Import ListNotations.
Local Open Scope Z_scope.

(* reply's allocator parameters and image constants are this file's CfParams / CfImg instances *)
#[local] Existing Instance CfParams_reply.
#[local] Existing Instance CfImg_A.

(* The instance predicate on the allocator instance: reply's one instance object. *)
Definition IOK_reply : Z -> Prop := fun i => i = as_inst TfibB.

Lemma IOK_reply_ok : IOK_ok TfibB IOK_reply.
Proof. intros i H. exact H. Qed.

Section r. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* Allocate's bridge premise at can_fill 1, at this FPState / RunCeil. *)
Theorem aalloc_realizes_cf_em_reply_rc :
  aalloc_realizes_cf_em im_segs TfibB cf_malloc_max 8 1 1 (ARXq_cf TfibB IOK_reply).
Proof.
apply aalloc_realizes_cf_em_of_m.
exact (YGcfInstWalkSigreply.aalloc_realizes_cf_reply IOK_reply IOK_reply_ok 1 (or_intror eq_refl)).
Qed.

End r.

(* At every FPState and RunCeil: the premise WalkB2's malloc body top takes, in its text (ReplyMallocA.v:113 at commit
   805bb3b51c39); IOK_reply's body and tfibsegs = im_segs at AImg_reply. *)
Theorem aalloc_realizes_cf_em_reply_all :
  forall (fx : YK11.FPState) (rc : YM05.RunCeil),
    aalloc_realizes_cf_em (fx := fx) tfibsegs TfibB cf_malloc_max 8 1 1
      (ARXq_cf (rc := rc) TfibB (fun i => i = as_inst TfibB)).
Proof.
intros fx rc. exact (@aalloc_realizes_cf_em_reply_rc fx rc).
Qed.
