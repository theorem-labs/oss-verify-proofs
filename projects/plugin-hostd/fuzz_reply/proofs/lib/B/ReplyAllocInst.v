(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-30 (a Theorem Labs lane; 2026-10-31 part 3c and premise-free, a Theorem Labs lane, for a Theorem Labs lane's cf layer at
   plugin-hostd/fuzz_reply): reply's MALLOC INSTANCE at image B (fuzz_reply.asan-ubsan, pin 10ffb5f9202a), its Allocate
   part: the image B twin of lib/A/ReplyAllocInst.v.
   rule 24: no function proved (kind: statement text; the cf layer's Allocate top at reply's image B over reply's Allocate
   walk tops and its unit facts; no named premise is left).
   Changes against the A text: module paths lib.A -> lib.B, image twins A<r> -> Y<r>, CfImg_B; the CfParams instance stays
   A's CfParams_reply, as image B's target and its consumers name it; the miss arms come from the B miss chain
   (CfInstMiss) inside B/YGcfInstWalkSigreply.v. The refill walk and the secondary interface are discharged there by
   a Theorem Labs lane's B refill closer and CfInstSec's B closers.
   Field round 3 part 3c: aalloc_realizes_cf_em takes the call state's arodata_ok_cf at Allocate's entry (the bridge that
   consumes it derives it from acall_pre_cf); the text of the export is unchanged.
   This file does not Require ReplyAllocTargets. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import AGif2reply ImgBaseAG AGif0reply ImgBaseAGS AGif4reply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YF0m YF0x CfImgB YD2l.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require AGif4 ErrnoGS.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YGcfMallocCompose YGcfMallocComposeE.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YGcfInstBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YGcfInstHit YGcfInstWalkSigreply.
Import ListNotations.
Local Open Scope Z_scope.

(* reply's allocator parameters and image constants are this file's CfParams / CfImg instances *)
#[local] Existing Instance CfParams_reply.
#[local] Existing Instance CfImg_B.

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

(* At every FPState and RunCeil: the premise a Theorem Labs lane's image-B malloc closure (ReplyClosedB) takes, the A text's form
   at image B; IOK_reply's body and tfibsegs = im_segs at AImg_reply. *)
Theorem aalloc_realizes_cf_em_reply_all :
  forall (fx : YK11.FPState) (rc : YM05.RunCeil),
    aalloc_realizes_cf_em (fx := fx) tfibsegs TfibB cf_malloc_max 8 1 1
      (ARXq_cf (rc := rc) TfibB (fun i => i = as_inst TfibB)).
Proof.
intros fx rc. exact (@aalloc_realizes_cf_em_reply_rc fx rc).
Qed.
