(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-31 (a Theorem Labs lane, for a Theorem Labs lane's reply-B realloc row and a Theorem Labs lane's reply-B top): reply's two
   realloc targets at image B (fuzz_reply.asan-ubsan, pin 10ffb5f9202a), the image-B twin of a Theorem Labs lane's
   lib/A/ReplyAreallocTargetA.v,
     ReplyAllocTargetsB.arealloc_target_replyB      (lib/B/ReplyAllocTargetsB.v, the PRIMED text:
       `forall fx rc k, YGcfInstReallocK.arealloc_realizes_cf_k tfibsegs TfibB [] (pa_sigma WS_realloc) k`)
     ReplyAllocTargetsB.arealloc_null_target_replyB (`forall fx rc, YGcfRealloc.arealloc_null_realizes_cf tfibsegs
       TfibB [] (pa_sigma WS_realloc)`),
   from the layer's instance theorems YGcfInstReallocK.arealloc_realizes_cf_k_inst (lib/B/YGcfInstReallocK.v) and
   YGcfInstRealloc.arealloc_null_realizes_cf_inst (lib/B/YGcfInstRealloc.v) at the image (IM := lib/B AImg_reply, so
   im_segs is image B's tfibsegs; ci := CfImg_B, cp := CfParams_reply), B := TfibB, IOK := ReplyAllocInst.IOK_reply,
   can_fill acf := 1, whose named premises are closed here by reply B's instances:
     Allocate (em_m)               : YGcfInstWalkSigreply.aalloc_realizes_cf_reply (a Theorem Labs lane's image-B Allocate
                                     instance on part 3c);
     Deallocate (primed raw, em_m_rh): ReplyDeallocInstB.adealloc_realizes_raw_cf_em_m_rh_reply (premise-free);
     errno_word_cf                 : ReplyImg_errnoword.errno_word_cf_B at TfibB;
     relro_seg_t / errno_relro_t   : ReplyRelroGeoB.relro_seg_reply_B / errno_relro_reply_B (a Theorem Labs lane's rows).
   The walk records (the instance theorems' last premises) are a Theorem Labs lane's lib/B/RGcfWalkB.v wrap_realloc_walk_cf_rh_B
   (PRIMED: the return segment is lib/B RGcfSegs3Rh.rw_ret_rh_A) and wrap_realloc_null_walk_cf_B, at
   nmax := cf_malloc_max, (al, atp, acf, atpD) := (8, 1, 1, 1), ARX := RGcfLaws.ARXqA TfibB (= YGcfInstBase.ARXq_cf
   TfibB IOK_reply).
   rule 24: proves no function (kind: statement text; instance plumbing over proved contracts and walk records).
   The file runs no Print Assumptions (as its A twin: the allocator's whole closure takes minutes); the report has it.
   A Theorem Labs lane's reply-B top (lib/B/ReplyBTop.v) binds its AR / AR0 to the two theorems below. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase YK11 YK04 YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import AGif2reply YF0m YD2l CfImgB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YGcfMallocCompose YGcfMallocComposeE YGcfInstBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YGcfRealloc.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require
  ReplyAllocTargetsB ReplyAllocInst ReplyDeallocInstB YGcfInstWalkSigreply ReplyImg_errnoword ReplyRelroGeoB
  YGcfMallocComposeERh YGcfReallocCompose YGcfReallocComposeRh YGcfInstReallocK YGcfInstRealloc RGcfK RGcfSegs2a RGcfWalkB.
Local Open Scope Z_scope.

(* the ASan-UBSan image's sink instance, as the B listing's pa_sigma takes it *)
#[local] Existing Instance YE2k.tfib_sink_head.

#[local] Existing Instance CfParams_reply.
#[local] Existing Instance CfImg_B.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* Allocate's contract at reply B's call-site relation, can_fill 1 (im_segs at AImg_reply is tfibsegs) *)
Local Lemma AL : aalloc_realizes_cf_em_m (@im_segs AImg_reply) TfibB cf_malloc_max al_cf atp_cf 1
  (ARXq_cf (IM := AImg_reply) TfibB ReplyAllocInst.IOK_reply).
Proof. exact (YGcfInstWalkSigreply.aalloc_realizes_cf_reply ReplyAllocInst.IOK_reply ReplyAllocInst.IOK_reply_ok 1
                (or_intror eq_refl)). Qed.

(* Each instance premise at its stated type (the instance theorems' arguments, typed once here). *)
Local Lemma DE : YGcfMallocComposeERh.adealloc_realizes_raw_cf_em_m_rh (@im_segs AImg_reply) TfibB atp_cf
  (ARXq_cf (IM := AImg_reply) TfibB ReplyAllocInst.IOK_reply).
Proof. exact ReplyDeallocInstB.adealloc_realizes_raw_cf_em_m_rh_reply. Qed.

Local Lemma EW : YGcfReallocCompose.errno_word_cf TfibB.
Proof. exact (ReplyImg_errnoword.errno_word_cf_B TfibB TfibB_syms). Qed.

Local Lemma WK : YGcfReallocComposeRh.wrap_realloc_walk_cf_rh (@im_segs AImg_reply) TfibB cf_malloc_max al_cf atp_cf 1
  atp_cf (ARXq_cf (IM := AImg_reply) TfibB ReplyAllocInst.IOK_reply) (RGcfK.K1A TfibB) (RGcfSegs2a.K2A TfibB)
  (RGcfSegs2a.K3A TfibB).
Proof. exact (RGcfWalkB.wrap_realloc_walk_cf_rh_B TfibB TfibB_syms cf_malloc_max). Qed.

Local Lemma WN : YGcfReallocCompose.wrap_realloc_null_walk_cf (@im_segs AImg_reply) TfibB cf_malloc_max al_cf atp_cf 1
  (ARXq_cf (IM := AImg_reply) TfibB ReplyAllocInst.IOK_reply) RGcfK.KnA.
Proof. exact (RGcfWalkB.wrap_realloc_null_walk_cf_B TfibB TfibB_syms cf_malloc_max). Qed.

(* realloc(p, n), primed, at every headroom k: the instance at the image's interceptor entry *)
Local Lemma INST : forall k, YGcfInstReallocK.arealloc_realizes_cf_k (@im_segs AImg_reply) TfibB [] cf_pc_wrap_realloc k.
Proof.
exact (YGcfInstReallocK.arealloc_realizes_cf_k_inst (IM := AImg_reply) TfibB ReplyAllocInst.IOK_reply 1 AL DE EW
  ReplyRelroGeoB.relro_seg_reply_B (ReplyRelroGeoB.errno_relro_reply_B TfibB TfibB_syms) _ _ _ WK []).
Qed.

(* ... at image B's tfibsegs and SIGMA WS_realloc (im_segs AImg_reply = tfibsegs; CfImg_B's cf_pc_wrap_realloc is the
   B listing's WS_realloc address) *)
Theorem arealloc_realizes_cf_k_replyB_rc : forall k,
  YGcfInstReallocK.arealloc_realizes_cf_k tfibsegs TfibB [] (@pa_sigma _ fr_prog_listing PB_fr WS_realloc) k.
Proof. exact INST. Qed.

(* realloc(NULL, n) *)
Local Lemma INSTN : YGcfRealloc.arealloc_null_realizes_cf (@im_segs AImg_reply) TfibB [] cf_pc_wrap_realloc.
Proof.
exact (YGcfInstRealloc.arealloc_null_realizes_cf_inst (IM := AImg_reply) TfibB ReplyAllocInst.IOK_reply 1 AL
  ReplyRelroGeoB.relro_seg_reply_B (ReplyRelroGeoB.errno_relro_reply_B TfibB TfibB_syms) _ WN []).
Qed.

Theorem arealloc_null_realizes_cf_replyB_rc :
  YGcfRealloc.arealloc_null_realizes_cf tfibsegs TfibB [] (@pa_sigma _ fr_prog_listing PB_fr WS_realloc).
Proof. exact INSTN. Qed.

End a.

Theorem arealloc_target_reply_B : ReplyAllocTargetsB.arealloc_target_replyB.
Proof. intros fx rc k. exact (@arealloc_realizes_cf_k_replyB_rc fx rc k). Qed.

Theorem arealloc_null_target_reply_B : ReplyAllocTargetsB.arealloc_null_target_replyB.
Proof. intros fx rc. exact (@arealloc_null_realizes_cf_replyB_rc fx rc). Qed.
