(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/YGcfInstDrainTop.v, with its module paths and module names changed; 32 of its 68 lines of code are new or changed and 27 lines of the source are left out. *)
(* Theorem Labs, 2026-10-30 (lane F2b, CfF2b; drain-rh split row (c), route P): the seam's PRIMED drain field at reply's
   image A - DIfaceRh.de_drain_m_rh_t at the cf instance (ARX := ARX_cf, ARXr := ARXr_cf, AOX := aowned,
   L24 := L24MAX_cf, QB := QB_cf kQuarantineMax, DRq := DRq_cf kQuarantineMax, RMAXD := RMAXD_cf), as ONE application
   of the primed drain top DMdrainTopRh.drain_m_cf_rh.  The field is over amreal' (= amrealG tfibsegs (wle' tfibsegs
   RZ_cf)), a route-P instance of the generic engine at R := wle'.  It replaces the deleted unprimed ds_drain_cf.
   This file is about ONE image by design: the walk top is typed over image A's segments (tfibsegs), so the image is
   AGif2reply's exported AImg_reply (and DGif0reply's DImg), not a generic binder; the layer facts it takes
   (YGcfInstDrainTop.drain_reads_cf / QBB_of_QB_cf / L24MAX_lt_cf) are image-generic and meet the walk's types by
   conversion.  Discharged here: DoRecycle's primed contract (a Theorem Labs lane's DMrecFRh.dorecycle_ok_rh), the three image
   rows SB_CONST / IMG_QAPART / CONST_APART at A (CfInstMiss's YGcfInstDrainImgreply), the Recycle twin (H4's
   DMrcCf.rchunk_ok_rh_cf_closed, with H3's DMcdF.cdealloc_g_of_reads at YGcfInstCdReads.cd_reads_cf) and CacheDealloc
   (a Theorem Labs lane's YGcfInstCdealloc.de_cdealloc_m_cf).  The Recycle twin's drop bound DMrcSecCf.REC_LE is a CfParams
   fact: the field keeps it as a premise (it is generic in CfParams), and [rec_le_reply] discharges it at reply's
   CfParams_reply (YGcfRehideAR.reply_rec_drop_le_rh).
   rule 24: no function proved (kind: interface-instance discharge, one application of the primed walk top). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require YGcfRehidePost.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0s YK0i YP0m YP0e YP09 YP0l YP06 YO0d YK08.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI04 YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0k YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YGcfTok YG03cf YG03dcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ImgBaseDG AGif2reply DGif0reply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import DMspec DMiface MnRecycle DMwalkIF.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfBatch YGcfImgRows.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import YGcfInstBase YGcfInstDrainR YGcfInstDrainX YGcfInstDrainQ.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require DIfaceRh DMwalkIFRh DMdrainTopRh DMrecFRh.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require YGcfInstDrainTop YGcfInstDrainImgreply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require DMrcSecCf DMrcCf DMcdF YGcfInstCdReads YGcfInstCdealloc.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require YGcfRehideAR CfParamsReply.
From Stdlib Require Import List.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section U. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Section T.
Variable B : asyms.
Variable IOK : Z -> Prop.
Variable Hp : list Z.
Local Notation ARX := (ARX_cf B IOK Hp).
Local Notation ARXr := (ARXr_cf B IOK Hp).
Local Notation AOX := (aowned B).
Local Notation QB := (QB_cf kQuarantineMax).
Local Notation DRq := (DRq_cf B kQuarantineMax).

(* the unit choice, the symbol table and the one image row not discharged here (CfInstHit's ERRB_QAPART at A) *)
Hypothesis IOK_inst : IOK_ok B IOK.
Hypothesis TS : im_syms B.
Hypothesis TB : TfibSyms B.
Hypothesis EAP : ERRB_QAPART.
(* lane F2a's four fields at ARX *)
Hypothesis QV : di_qview_t B ARX L24MAX_cf QB.
Hypothesis QO : di_qowned_t ARX AOX L24MAX_cf QB.
Hypothesis STK : di_stack_t ARX AOX.
Hypothesis FRX : di_frame_t ARX AOX.
(* H4's one open premise of the Recycle twin (DMrcCf.rchunk_ok_rh_cf_closed): the re-hide's drop bound *)
Hypothesis RLE : DMrcSecCf.REC_LE.

Theorem ds_drain_rh_cf : DIfaceRh.de_drain_m_rh_t B ARX AOX drain_body_cf L24MAX_cf QB.
Proof.
pose proof (YGcfInstDrainTop.drain_reads_cf B IOK Hp IOK_inst TS YGcfInstDrainImgreply.SB_CONST_reply_A
  YGcfInstDrainImgreply.IMG_QAPART_reply_A EAP YGcfInstDrainImgreply.CONST_APART_reply_A QV QO STK FRX) as DR.
eapply (DMdrainTopRh.drain_m_cf_rh B ARX ARXr AOX L24MAX_cf QB DRq RMAXD_cf).
- exact YGcfInstDrainTop.QBB_of_QB_cf.
- exact YGcfInstDrainTop.L24MAX_lt_cf.
- exact rmaxd_ok_cf.
- exact (DMrecFRh.dorecycle_ok_rh B ARXr AOX DRq RMAXD_cf).
- exact TB.
- exact DR.
- destruct DR as (_ & _ & _ & _ & FRr & _ & _ & _ & RVx).
  exact (DMrcCf.rchunk_ok_rh_cf_closed B TB IOK Hp IOK_inst EAP RLE FRr RVx
    (DMcdF.cdealloc_g_of_reads B ARXr AOX DRq RMAXD_cf TB rmaxd_ok_cf (YGcfInstCdReads.cd_reads_cf B IOK Hp TB IOK_inst))).
- exact (YGcfInstCdealloc.de_cdealloc_m_cf B IOK Hp TB IOK_inst).
Qed.

End T.
End U.

(* The drop bound at reply's CfParams: cf_rec_drop is reply_rec_drop_cf there, under the re-hidden interior by
   YGcfRehideAR.reply_rec_drop_le_rh.  So ds_drain_rh_cf (cp := CfParamsReply.CfParams_reply) ... rec_le_reply is the
   field at reply's instance. *)
Section R. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma rec_le_reply : DMrcSecCf.REC_LE (cp := CfParamsReply.CfParams_reply).
Proof.
unfold DMrcSecCf.REC_LE. intros MAP LEN H0 HL.
exact (YGcfRehideAR.reply_rec_drop_le_rh MAP LEN H0 ltac:(unfold kMaxSize, kPage in HL; lia)).
Qed.
End R.
