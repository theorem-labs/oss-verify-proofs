(* Reply A's malloc target and strndup contract with no premise: Allocate's contract at the call-site relation of every
   reply instance is ReplyAllocInst.aalloc_realizes_cf_em_reply_all (premise-free on the part-3c line), the one premise
   of ReplyMallocA.amalloc_target_reply_of_allocate and of Rt/RtDStrndupClosed.reply_astrndup_cf_closed.  Stated at
   image A's CfImg and reply's CfParams, as those files state their theorems. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YM05 YG0f YGcfNames YG0dcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AD2l W_syms W_kit W_listing W_img.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require CfImgA CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ReplyAllocInst ReplyMallocA ReplyAllocTargets.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Rt Require RtDStrndupClosed.
Open Scope Z_scope.

#[local] Existing Instance CfImgA.CfImg_A.
#[local] Existing Instance CfParamsReply.CfParams_reply.

(* reply A's malloc target (ReplyAllocTargets.amalloc_target_reply, the text top_x's AMALLOC_CF takes) *)
Theorem amalloc_target_reply_A : ReplyAllocTargets.amalloc_target_reply.
Proof. exact (ReplyMallocA.amalloc_target_reply_of_allocate ReplyAllocInst.aalloc_realizes_cf_em_reply_all). Qed.

(* reply A's strndup interceptor at its entry, at every FP state and RunCeil *)
Theorem reply_astrndup_cf_all : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  astrndup_realizes_cf (fx := fx) (rc := rc) tfibsegs AD2l.TfibB (@pa_sigma _ fr_prog_listing PB_fr WS_strndup) 0x427b8.
Proof.
intros fx rc.
exact (RtDStrndupClosed.reply_astrndup_cf_closed fx rc (ReplyAllocInst.aalloc_realizes_cf_em_reply_all fx rc)).
Qed.

Print Assumptions amalloc_target_reply_A.
Print Assumptions reply_astrndup_cf_all.
