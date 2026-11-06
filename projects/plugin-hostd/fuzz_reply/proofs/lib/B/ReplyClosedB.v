(* Reply B's malloc target and strndup contract with no premise: Allocate's contract at the call-site relation of every
   reply instance is ReplyAllocInst.aalloc_realizes_cf_em_reply_all (lib/B, premise-free on the part-3c line), the one
   premise of ReplyMallocB.amalloc_target_replyB_of_allocate and of Rt/RtDStrndupClosed.reply_astrndup_cf_B_closed.
   Stated at image B's CfImg and reply's one CfParams record, as those files state their theorems. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YM05 YG0f YGcfNames YG0dcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YD2l W_syms W_kit W_listing W_img.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require CfImgB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyAllocInst ReplyMallocB ReplyAllocTargetsB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Rt Require RtDStrndupClosed.
Open Scope Z_scope.

#[local] Existing Instance CfImgB.CfImg_B.
#[local] Existing Instance CfParamsReply.CfParams_reply.

(* reply B's malloc target (ReplyAllocTargetsB.amalloc_target_replyB, every FP state and RunCeil) *)
Theorem reply_amalloc_target_B : ReplyAllocTargetsB.amalloc_target_replyB.
Proof. exact (ReplyMallocB.amalloc_target_replyB_of_allocate ReplyAllocInst.aalloc_realizes_cf_em_reply_all). Qed.

(* reply B's strndup interceptor at its entry, at every FP state and RunCeil *)
Theorem reply_astrndup_cf_B_all : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  astrndup_realizes_cf (fx := fx) (rc := rc) tfibsegs YD2l.TfibB (@pa_sigma _ fr_prog_listing PB_fr WS_strndup) 0x42810.
Proof.
intros fx rc.
exact (RtDStrndupClosed.reply_astrndup_cf_B_closed fx rc (ReplyAllocInst.aalloc_realizes_cf_em_reply_all fx rc)).
Qed.

Print Assumptions reply_amalloc_target_B.
Print Assumptions reply_astrndup_cf_B_all.
