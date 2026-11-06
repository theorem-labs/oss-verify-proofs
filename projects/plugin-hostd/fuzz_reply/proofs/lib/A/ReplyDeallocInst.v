(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-30 (a Theorem Labs lane, for lane W of a Theorem Labs lane's cf layer at plugin-hostd/fuzz_reply): reply's
   DEALLOCATE INSTANCE at image A (fuzz_reply.asan, pin 42c58610e125), in the PRIMED form (row (a) of the primed-free
   plan: a secondary free re-hides the dead map's shadow, so reply's free contract is the primed
   YG0dcfR.afree_realizes_cf_rh).
   rule 24: no function proved (kind: statement text; the composition of the cf layer's primed free instance at reply's
   image, its unit facts and rows, and the other lanes' closers).

   Export: afree_realizes_cf_rh_reply_all : forall fx rc,
   @YG0dcfR.afree_realizes_cf_rh fx rc CfImg_A CfParams_reply tfibsegs TfibB (the conclusion is YG0dcfR.v:61-69; free(NULL)
   is the same contract, p = PNull).  Route:
   - YGcfMallocComposeRh.afree_realizes_cf_rh_of_parts_m (row (b), RealSegA) at B := TfibB, atpD := atp_cf,
     ARX := ARXq_cf TfibB IOK_reply, with YGcfInstBase.ARXq_cf_ARcf, a Theorem Labs lane's rows ReplyRelroGeoA.relro_seg_reply_A /
     errno_relro_reply_A, and a Theorem Labs lane's primed free walk WrapFreeReplyA.wrap_free_walk_rh_reply_A at its K_reply;
   - its Deallocate premise from the layer's primed top YGcfInstFreeTopRh.adealloc_realizes_raw_cf_em_m_rh_cf (row (c),
     lane F2a) at the choices ARXr := YGcfInstDrainR.ARXr_cf TfibB IOK_reply, L24 := L24MAX_cf,
     QB := YGcfInstDrainR.QB_cf kQuarantineMax, DRq := YGcfInstDrainR.DRq_cf TfibB kQuarantineMax (lane F2b's,
     agreed with a Theorem Labs lane); its image premises: reply's unit facts (ReplyUnitFactsA.reply_unit_facts_A TfibB
     AD2l.TfibB_syms: FM_INST_OK uf_dg_inst_ok, IMG_COVER uf_IMG_COVER, FV_TSD uf_HTSD, FV_IAL uf_FV_IAL, FQ_CONST
     uf_FQ_CONST, DZONE_OWNED / IZONE_OWNED / FV_ZONE3 uf_DZONE_OWNED / uf_IZONE_OWNED / uf_FV_ZONE3, ERRB_APART
     uf_ERRB_APART), QB_BYTES at QB_cf (a Theorem Labs lane's ReplyQBBytes.qb_bytes_reply_A), a Theorem Labs lane's FP_IZONE_ROM / FP_DSTAT /
     FP_DZONE_FP / FP_CONST rows (YGcfInstFreeImgreply.FP_*_TfibB), and PF_APART (ReplyPfApartA.pf_apart_reply_A);
     IOK_ok holds by the instance's choice IOK_reply := (fun i => i = as_inst TfibB).
   - its DIfaceExtRh premise (YGcfInstFree.DIfaceExtRh at the choices, every ghost set): a Theorem Labs lane's
     YGcfInstFreeExtA.diface_ext_rh_reply_A at IOK_reply.
   - its WalkSigDrh premise (reply's Deallocate arms under the re-hide): a Theorem Labs lane's ReplyWalkSigDrh.walksigdrh_reply
     (walksigdrh_reply_A below), its hypotheses plugged with the rows above and CfF1's Enqueue arms
     YGcfInstEnqMissreply.enq_arms_cf_reply (ENQA_reply, over B3LeafCf's refill spec).
   - its big arm's DIfaceExtRh premise (EXTB, at DRq_cf TfibB NMAXD_big_cf): a Theorem Labs lane's
     YGcfInstFreeExtA.diface_ext_rh_reply_A_big at IOK_reply.
   No premise is left: the export is closed.
   This file no longer proves the released (unprimed) free contract (plan row X). ReplyATopX's AFREE_CF and
   ReplyAllocTargets.afree_target_reply still state it; they move to the primed form in plan rows 3 / 3D. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase YGcfBatch.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AF0m AF0x CfImgA CfParamsReply AD2l.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import DeallocG ImgBaseDG DMspec DMiface DGif0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AGif2reply DGif0reply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import YGcfMallocCompose YGcfMallocComposeE.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import YGcfMallocComposeERh YGcfMallocComposeRh.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import YGcfInstBase YGcfInstFreeSig.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import YGcfInstFreeView YGcfInstFreeQ YGcfInstFreeModel YGcfInstFree.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import YGcfInstFreePost YGcfInstFreeTopRh.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require YGcfDIface YGcfInstDrainR YG0dcfR DGmpcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ReplyUnitFactsA ReplyRelroGeoA ReplyPfApartA YGcfInstFreeImgreply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require WrapFreeReplyA YGcfInstFreeExtA.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ReplyWalkSigDrh ReplyQBBytes YGcfInstEnq YGcfInstEnqMissreply
  YGcfRefillTopreply RepArmTcf.
Import ListNotations.
Local Open Scope Z_scope.

(* reply's allocator parameters (A/CfParamsReply.v) are the instance of the layer's CfParams in this file *)
#[local] Existing Instance CfParams_reply.
(* reply's image constants (A/CfImgA.v) are the instance of the layer's CfImg *)
#[local] Existing Instance CfImg_A.

(* The instance predicate on the allocator instance: reply's one instance object. *)
Definition IOK_reply : Z -> Prop := fun i => i = as_inst TfibB.

Lemma IOK_reply_ok : IOK_ok TfibB IOK_reply.
Proof. intros i H. exact H. Qed.

Section r. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* The unit's three Enqueue arms at the cf relation: CfF1's closed form at reply A (YGcfInstEnqMissreply.v:367 over
   B3LeafCf's refill spec, the class-full arm by the relocated report). *)
Lemma ENQA_reply : forall Hp, YGcfInstEnq.EnqArmsCf TfibB (ARX_cf TfibB IOK_reply Hp).
Proof.
intros Hp.
exact (YGcfInstEnqMissreply.enq_arms_cf_reply TfibB TfibB_syms IOK_reply Hp IOK_reply_ok ReplyRelroGeoA.relro_seg_reply_A
  (YGcfRefillTopreply.refill_spec_cf_reply_inst TfibB IOK_reply TfibB_syms IOK_reply_ok
    (@RepArmTcf.classfull_cf_of_hyps fx rc CfParams_reply))).
Qed.

(* reply's Deallocate arms under the re-hide: a Theorem Labs lane's walksigdrh_reply (lib/A/ReplyWalkSigDrh.v) with its
   hypotheses plugged. *)
Lemma walksigdrh_reply_A : forall Hp,
  WalkSigDrh TfibB (U_cf TfibB) free_cf (ARX_cf TfibB IOK_reply Hp) (aowned TfibB)
    (rpreD_small_cf TfibB) qtight (fpre_hp_cf im_segs TfibB Hp) atp_cf (rpreD_big_cf TfibB)
    (YGcfInstDrainR.ARXr_cf TfibB IOK_reply Hp) (YGcfInstDrainR.DRq_cf TfibB YGcfInstDrainR.NMAXD_big_cf) (DGmpcf.MPcf TfibB).
Proof.
intros Hp.
exact (ReplyWalkSigDrh.walksigdrh_reply IOK_reply (YGcfInstDrainR.DRq_cf TfibB kQuarantineMax) IOK_reply_ok
  ReplyQBBytes.qb_bytes_reply_A
  YGcfInstFreeImgreply.FP_IZONE_ROM_TfibB YGcfInstFreeImgreply.FP_DSTAT_TfibB YGcfInstFreeImgreply.FP_DZONE_FP_TfibB
  YGcfInstFreeImgreply.FP_CONST_TfibB ReplyPfApartA.pf_apart_reply_A
  (YGcfInstFreeExtA.diface_ext_rh_reply_A IOK_reply IOK_reply_ok) ENQA_reply
  (YGcfInstFreeExtA.diface_ext_rh_reply_A_big IOK_reply IOK_reply_ok) Hp).
Qed.

(* Deallocate's primed raw contract at reply's call-site relation, from the layer's primed free top. *)
Theorem adealloc_realizes_raw_cf_em_m_rh_reply :
  adealloc_realizes_raw_cf_em_m_rh im_segs TfibB atp_cf (ARXq_cf TfibB IOK_reply).
Proof.
pose proof (ReplyUnitFactsA.reply_unit_facts_A TfibB TfibB_syms) as UF.
refine (adealloc_realizes_raw_cf_em_m_rh_cf TfibB IOK_reply (YGcfInstDrainR.ARXr_cf TfibB IOK_reply) L24MAX_cf
  (YGcfInstDrainR.QB_cf kQuarantineMax) (YGcfInstDrainR.DRq_cf TfibB kQuarantineMax)
  IOK_reply_ok _ _ _ _ _ ReplyQBBytes.qb_bytes_reply_A _ _ _
  YGcfInstFreeImgreply.FP_IZONE_ROM_TfibB YGcfInstFreeImgreply.FP_DSTAT_TfibB YGcfInstFreeImgreply.FP_DZONE_FP_TfibB
  YGcfInstFreeImgreply.FP_CONST_TfibB _ ReplyPfApartA.pf_apart_reply_A (YGcfInstFreeExtA.diface_ext_rh_reply_A IOK_reply IOK_reply_ok) walksigdrh_reply_A).

- exact (ReplyUnitFactsA.uf_dg_inst_ok _ UF).
- exact (ReplyUnitFactsA.uf_IMG_COVER _ UF).
- exact (ReplyUnitFactsA.uf_HTSD _ UF).
- exact (ReplyUnitFactsA.uf_FV_IAL _ UF).
- exact (ReplyUnitFactsA.uf_FQ_CONST _ UF).
- exact (ReplyUnitFactsA.uf_DZONE_OWNED _ UF).
- exact (ReplyUnitFactsA.uf_IZONE_OWNED _ UF).
- exact (ReplyUnitFactsA.uf_FV_ZONE3 _ UF).
- exact (ReplyUnitFactsA.uf_ERRB_APART _ UF).
Qed.

(* The primed free contract at reply's image and this FPState / RunCeil. *)
Theorem afree_realizes_cf_rh_reply_rc :
  YG0dcfR.afree_realizes_cf_rh tfibsegs TfibB.
Proof.
exact (afree_realizes_cf_rh_of_parts_m im_segs TfibB atp_cf (ARXq_cf TfibB IOK_reply) _
  (ARXq_cf_ARcf TfibB IOK_reply) ReplyRelroGeoA.relro_seg_reply_A (ReplyRelroGeoA.errno_relro_reply_A TfibB TfibB_syms)
  adealloc_realizes_raw_cf_em_m_rh_reply WrapFreeReplyA.wrap_free_walk_rh_reply_A).
Qed.

End r.

(* AFREE_CF in the primed form, at every FPState and RunCeil: the form reply's primed top takes (plan rows 3 / 3D / T). *)
Theorem afree_realizes_cf_rh_reply_all :
  forall (fx : YK11.FPState) (rc : YM05.RunCeil),
    @YG0dcfR.afree_realizes_cf_rh fx rc CfImg_A CfParams_reply tfibsegs TfibB.
Proof.
intros fx rc. exact (@afree_realizes_cf_rh_reply_rc fx rc).
Qed.
