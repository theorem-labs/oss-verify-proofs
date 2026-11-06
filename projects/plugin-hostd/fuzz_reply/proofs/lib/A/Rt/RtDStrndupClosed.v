(* The strndup wrapper contract at fuzz_reply image A with its premises discharged except Allocate's contract:
   reply_astrndup_cf (RtDStrndup.v) takes the malloc interceptor body's contract amalloc_body_realizes_cf and the image
   row relro_seg_t; ReplyMallocBodyA.amalloc_body_reply_A proves the first from Allocate's contract at the call-site
   relation of every reply instance, ReplyRelroGeoA.relro_seg_reply_A the second.  Stated at image A's CfImg and
   reply's CfParams, as ReplyMallocBodyA states its theorem. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YM05 YG0f YGcfNames YG0dcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AD2l W_syms W_kit W_listing W_img.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require YGcfInstBase CfImgA CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import YGcfMallocCompose AGif2reply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ReplyMallocBodyA ReplyRelroGeoA.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Rt Require RtDStrndup.
Open Scope Z_scope.

#[local] Existing Instance CfImgA.CfImg_A.
#[local] Existing Instance CfParamsReply.CfParams_reply.

Theorem reply_astrndup_cf_closed : forall (fx : YK11.FPState) (rc : YM05.RunCeil),
  YGcfMallocCompose.aalloc_realizes_cf_em (fx := fx) tfibsegs AD2l.TfibB cf_malloc_max 8 1 1
    (YGcfInstBase.ARXq_cf (rc := rc) AD2l.TfibB (fun i => i = as_inst AD2l.TfibB)) ->
  astrndup_realizes_cf (fx := fx) (rc := rc) tfibsegs AD2l.TfibB (@pa_sigma _ fr_prog_listing PB_fr WS_strndup) 0x427b8.
Proof.
intros fx rc HAL.
exact (RtDStrndup.reply_astrndup_cf (ReplyMallocBodyA.amalloc_body_reply_A fx rc HAL) ReplyRelroGeoA.relro_seg_reply_A).
Qed.

Print Assumptions reply_astrndup_cf_closed.
About reply_astrndup_cf_closed.
