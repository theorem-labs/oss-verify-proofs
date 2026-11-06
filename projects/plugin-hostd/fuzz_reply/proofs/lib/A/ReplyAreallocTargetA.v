(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-31 (a Theorem Labs lane, for a Theorem Labs lane's reply-A realloc row and a Theorem Labs lane's reply top): reply's two
   realloc targets at image A,
     ReplyAllocTargets.arealloc_target_reply      (lib/A/ReplyAllocTargets.v, CfF1's PRIMED text:
       `forall fx rc k, YGcfInstReallocK.arealloc_realizes_cf_k tfibsegs TfibB [] (pa_sigma WS_realloc) k`)
     ReplyAllocTargets.arealloc_null_target_reply (`forall fx rc, YGcfRealloc.arealloc_null_realizes_cf tfibsegs TfibB []
       (pa_sigma WS_realloc)`),
   from the layer's instance theorems YGcfInstReallocK.arealloc_realizes_cf_k_inst (lib/A/YGcfInstReallocK.v:244) and
   YGcfInstRealloc.arealloc_null_realizes_cf_inst (lib/A/YGcfInstRealloc.v:94) at the image (IM := AImg_reply, so
   im_segs is tfibsegs; ci := CfImg_A, cp := CfParams_reply), B := TfibB, IOK := ReplyAllocInst.IOK_reply, can_fill
   acf := 1, whose named premises are closed here by reply's existing instances:
     Allocate (memnorm-kept, em_m) : YGcfInstWalkSigreply.aalloc_realizes_cf_reply (a Theorem Labs lane's Allocate instance);
     Deallocate (primed raw, em_m_rh): ReplyDeallocInst.adealloc_realizes_raw_cf_em_m_rh_reply (dealloc-rh-a eb934de95d1,
                                      premise-free);
     errno_word_cf                 : ReplyImg_errnoword.errno_word_cf_A_TfibB;
     relro_seg_t / errno_relro_t   : ReplyRelroGeoA.relro_seg_reply_A / errno_relro_reply_A (a Theorem Labs lane's rows).
   The walk records (the instance theorems' last premises) are A/RGcfWalkA.v's wrap_realloc_walk_cf_rh_A (PRIMED: the
   return segment is RGcfSegs3Rh.rw_ret_rh_A) and wrap_realloc_null_walk_cf_A, at nmax := cf_malloc_max,
   (al, atp, acf, atpD) := (8, 1, 1, 1), ARX := RGcfLaws.ARXqA TfibB (= YGcfInstBase.ARXq_cf TfibB IOK_reply).
   rule 24: proves no function (kind: statement text; instance plumbing over proved contracts and walk records).
   A Theorem Labs lane's generated top (lib/A/gen_ReplyATopX.py) binds AREALLOC_CF / AREALLOC0_CF to the two theorems below. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase YK11 YK04 YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AGif2reply AF0m AD2l CfImgA CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import YGcfMallocCompose YGcfMallocComposeE YGcfInstBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YGcfRealloc.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require
  ReplyAllocTargets ReplyAllocInst ReplyDeallocInst YGcfInstWalkSigreply ReplyImg_errnoword ReplyRelroGeoA
  YGcfMallocComposeERh YGcfReallocCompose YGcfReallocComposeRh YGcfInstReallocK YGcfInstRealloc RGcfK RGcfSegs2a RGcfWalkA.
Local Open Scope Z_scope.

(* the ASan image's sink instance, as ReplyAllocTargets.v / ReplyATopX.v take it *)
#[local] Existing Instance AE2k.tfib_sink_head.

#[local] Existing Instance CfParams_reply.
#[local] Existing Instance CfImg_A.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* Allocate's memnorm-kept contract at reply's call-site relation, can_fill 1 (im_segs at AImg_reply is tfibsegs) *)
Local Lemma AL : aalloc_realizes_cf_em_m (@im_segs AImg_reply) TfibB cf_malloc_max al_cf atp_cf 1
  (ARXq_cf (IM := AImg_reply) TfibB ReplyAllocInst.IOK_reply).
Proof. exact (YGcfInstWalkSigreply.aalloc_realizes_cf_reply ReplyAllocInst.IOK_reply ReplyAllocInst.IOK_reply_ok 1
                (or_intror eq_refl)). Qed.

(* Each instance premise at its stated type (the instance theorems' arguments, typed once here). *)
Local Lemma DE : YGcfMallocComposeERh.adealloc_realizes_raw_cf_em_m_rh (@im_segs AImg_reply) TfibB atp_cf
  (ARXq_cf (IM := AImg_reply) TfibB ReplyAllocInst.IOK_reply).
Proof. exact ReplyDeallocInst.adealloc_realizes_raw_cf_em_m_rh_reply. Qed.

Local Lemma WK : YGcfReallocComposeRh.wrap_realloc_walk_cf_rh (@im_segs AImg_reply) TfibB cf_malloc_max al_cf atp_cf 1
  atp_cf (ARXq_cf (IM := AImg_reply) TfibB ReplyAllocInst.IOK_reply) (RGcfK.K1A TfibB) (RGcfSegs2a.K2A TfibB)
  (RGcfSegs2a.K3A TfibB).
Proof. exact (RGcfWalkA.wrap_realloc_walk_cf_rh_A TfibB TfibB_syms cf_malloc_max). Qed.

Local Lemma WN : YGcfReallocCompose.wrap_realloc_null_walk_cf (@im_segs AImg_reply) TfibB cf_malloc_max al_cf atp_cf 1
  (ARXq_cf (IM := AImg_reply) TfibB ReplyAllocInst.IOK_reply) RGcfK.KnA.
Proof. exact (RGcfWalkA.wrap_realloc_null_walk_cf_A TfibB TfibB_syms cf_malloc_max). Qed.

(* realloc(p, n), primed, at every headroom k: the instance at the image's interceptor entry *)
Local Lemma INST : forall k, YGcfInstReallocK.arealloc_realizes_cf_k (@im_segs AImg_reply) TfibB [] cf_pc_wrap_realloc k.
Proof.
exact (YGcfInstReallocK.arealloc_realizes_cf_k_inst (IM := AImg_reply) TfibB ReplyAllocInst.IOK_reply 1 AL DE
  ReplyImg_errnoword.errno_word_cf_A_TfibB ReplyRelroGeoA.relro_seg_reply_A
  (ReplyRelroGeoA.errno_relro_reply_A TfibB TfibB_syms) _ _ _ WK []).
Qed.

(* ... at tfibsegs and SIGMA WS_realloc (im_segs AImg_reply = tfibsegs, cf_pc_wrap_realloc = 0x53df0 = SIGMA WS_realloc) *)
Theorem arealloc_realizes_cf_k_reply_rc : forall k,
  YGcfInstReallocK.arealloc_realizes_cf_k tfibsegs TfibB [] (@pa_sigma _ fr_prog_listing PB_fr WS_realloc) k.
Proof. exact INST. Qed.

(* realloc(NULL, n) *)
Local Lemma INSTN : YGcfRealloc.arealloc_null_realizes_cf (@im_segs AImg_reply) TfibB [] cf_pc_wrap_realloc.
Proof.
exact (YGcfInstRealloc.arealloc_null_realizes_cf_inst (IM := AImg_reply) TfibB ReplyAllocInst.IOK_reply 1 AL
  ReplyRelroGeoA.relro_seg_reply_A (ReplyRelroGeoA.errno_relro_reply_A TfibB TfibB_syms) _ WN []).
Qed.

Theorem arealloc_null_realizes_cf_reply_rc :
  YGcfRealloc.arealloc_null_realizes_cf tfibsegs TfibB [] (@pa_sigma _ fr_prog_listing PB_fr WS_realloc).
Proof. exact INSTN. Qed.

End a.

Theorem arealloc_target_reply_A : ReplyAllocTargets.arealloc_target_reply.
Proof. intros fx rc k. exact (@arealloc_realizes_cf_k_reply_rc fx rc k). Qed.

Theorem arealloc_null_target_reply_A : ReplyAllocTargets.arealloc_null_target_reply.
Proof. intros fx rc. exact (@arealloc_null_realizes_cf_reply_rc fx rc). Qed.

(* Print Assumptions of the two theorems is not run here: it takes 199 s and 106 s (the allocator's whole closure); its
   result, read in a throwaway build of this file, is Prim*, functional_extensionality_dep, Classical_Prop.classic and
   IndefiniteDescription.constructive_indefinite_description, all on the allow-list. *)
