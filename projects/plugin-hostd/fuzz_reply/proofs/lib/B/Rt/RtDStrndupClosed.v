(* The strndup wrapper contract at fuzz_reply image B with its premises discharged except Allocate's contract:
   reply_astrndup_cf_B (RtDStrndup.v) takes the malloc interceptor body's contract amalloc_body_realizes_cf and the
   image row relro_seg_t; ReplyMallocBodyB.amalloc_body_reply_B proves the first from Allocate's contract at the
   call-site relation of every reply instance, ReplyRelroGeoB.relro_seg_reply_B the second.  Stated at image B's CfImg
   and reply's one CfParams record, as ReplyMallocBodyB states its theorem. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YM05 YG0f YGcfNames YG0dcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YD2l W_syms W_kit W_listing W_img.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YGcfInstBase CfImgB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YGcfMallocCompose AGif2reply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyMallocBodyB ReplyRelroGeoB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Rt Require RtDStrndup.
Open Scope Z_scope.

#[local] Existing Instance CfImgB.CfImg_B.
#[local] Existing Instance CfParamsReply.CfParams_reply.

Theorem reply_astrndup_cf_B_closed : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  YGcfMallocCompose.aalloc_realizes_cf_em (fx := fx) tfibsegs YD2l.TfibB cf_malloc_max 8 1 1
    (YGcfInstBase.ARXq_cf (rc := rc) YD2l.TfibB (fun i => i = as_inst YD2l.TfibB)) ->
  astrndup_realizes_cf (fx := fx) (rc := rc) tfibsegs YD2l.TfibB (@pa_sigma _ fr_prog_listing PB_fr WS_strndup) 0x42810.
Proof.
intros fx rc HAL.
exact (RtDStrndup.reply_astrndup_cf_B (ReplyMallocBodyB.amalloc_body_reply_B fx rc HAL) ReplyRelroGeoB.relro_seg_reply_B).
Qed.

Print Assumptions reply_astrndup_cf_B_closed.
About reply_astrndup_cf_B_closed.
