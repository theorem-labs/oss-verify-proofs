(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the generic cf instance layer, lane F2b (a working branch): the three facts the cf
   instance's drain field takes from this lane, stated image-generically (over the Section's {IM : AImg} /
   {DI : DImg}, like the other YGcfInstDrain* files), so the file carries to a unit's tree as one text.  The drain
   field itself is the PRIMED one at reply (ds_drain_rh_cf, one application of the primed drain top
   DMdrainTopRh.drain_m_cf_rh at reply A's image); the earlier unprimed ds_drain_cf of this file is deleted.

   The three facts:
   - drain_reads_cf: the drain walk's nine read fields (DMwalkIF.drain_reads, its last field di_rview_x_t unfolded)
     as an explicit conjunction over DMiface's generic types; DMwalkIF is typed over one image's segments, so a
     consumer at a concrete image gets DMwalkIF.drain_reads from it by conversion.  Lane F2b supplies five fields:
     di_frame_t ARXr (YGcfInstDrainQ.di_frame_r_cf), di_requar_x_t (YGcfInstDrainX.di_requar_x_cf), di_requar_r_t
     (YGcfInstDrainX.di_requar_r_cf), di_requar_e_t (YGcfInstDrainQ.di_requar_e_cf) and the rview pair
     (YGcfInstDrainQ.di_rview_cf, di_rview_alloc_cf); lane F2a's four (di_qview_t, di_qowned_t, di_stack_t,
     di_frame_t ARX) are NAMED Section hypotheses, supplied by lane F2a's free-top assembly;
   - QBB_of_QB_cf: QB_cf's split bounds, the walk top's byte premise;
   - L24MAX_lt_cf: the batch-count bound below 2 ^ 40.
   Image rows taken as Section hypotheses: IOK_ok, im_syms, SB_CONST, IMG_QAPART, ERRB_QAPART, CONST_APART;
   errb_obj_owned_t and EXH_OFF_t are not premises, the relation carries them (ARmcf.amc_cells_owned, field round 2).
   rule 24: no function proved (kind: interface-instance facts for the drain field). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0s YK0i YP0m YP0e YP09 YP0l YP06 YO0d YK08.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YI04 YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0k YG0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YGcfTok YG03cf YG03dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase ImgBaseDG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import DMspec DMiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfBatch YGcfImgRows YGcfInstBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfInstDrainR YGcfInstDrainX YGcfInstDrainQ.
From Stdlib Require Import List.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* Image-generic: the image is the Context's {IM} / {DI}, and no image module is Required (DMwalkIF is not: it is
   typed over one image's segments). *)
Section U. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {IM : AImg} {DI : DImg}.
Section T.
Variable B : asyms.
Variable IOK : Z -> Prop.
Variable Hp : list Z.
Local Notation ARX := (ARX_cf B IOK Hp).
Local Notation ARXr := (ARXr_cf B IOK Hp).
Local Notation AOX := (aowned B).
Local Notation QB := (QB_cf kQuarantineMax).
Local Notation DRq := (DRq_cf B kQuarantineMax).

(* the image rows lane F2b's fields take *)
Hypothesis IOK_inst : IOK_ok B IOK.
Hypothesis TS : im_syms B.
Hypothesis SBC : SB_CONST.
Hypothesis IQA : IMG_QAPART.
Hypothesis EAP : ERRB_QAPART.
Hypothesis CA : CONST_APART.
(* lane F2a's fields at ARX (lane F2a's free-top assembly supplies them) *)
Hypothesis QV : di_qview_t B ARX L24MAX_cf QB.
Hypothesis QO : di_qowned_t ARX AOX L24MAX_cf QB.
Hypothesis STK : di_stack_t ARX AOX.
Hypothesis FRX : di_frame_t ARX AOX.

(* The drain's byte premise as the walk reads it (DMwalkIF.drain_ok_t's third premise): QB_cf's split bounds. *)
Lemma QBB_of_QB_cf : forall X, QB X -> qc_bytes (st_qglobal X) <= 2 ^ 30 /\ qc_bytes (st_qthread X) <= 2 ^ 29.
Proof.
intros X (_ & _ & T & G & _). unfold kQuarantineCacheMax, kBatchBytes, kQuarantineMax in *. split; lia.
Qed.

Lemma L24MAX_lt_cf : L24MAX_cf < 2 ^ 40.
Proof. rewrite L24MAX_cf_value. lia. Qed.

(* The drain walk's read fields (DMwalkIF.drain_reads, with its last field di_rview_x_t unfolded), stated over the
   image-generic types: DMwalkIF itself is typed over one image's segments (world tfibsegs), so a consumer at a
   concrete image gets DMwalkIF.drain_reads ... RMAXD_cf from this by conversion (`exact`). *)
Lemma drain_reads_cf :
  di_qview_t B ARX L24MAX_cf QB /\ di_qowned_t ARX AOX L24MAX_cf QB /\ di_stack_t ARX AOX /\
  di_frame_t ARX AOX /\ di_frame_t ARXr AOX /\
  di_requar_x_t B ARX AOX L24MAX_cf QB /\ di_requar_r_t B ARX ARXr AOX L24MAX_cf QB DRq /\
  di_requar_e_t ARX ARXr DRq /\
  (di_rview_t B ARXr DRq /\
   (forall inst ly X W mem md its zs, ARXr inst ly X W mem md -> DRq X its zs ->
    rg_alloc_user (reg X kBatchClass) <= RMAXD_cf)).
Proof.
split; [exact QV|]. split; [exact QO|]. split; [exact STK|]. split; [exact FRX|].
split; [exact (di_frame_r_cf B IOK Hp)|].
split; [exact (di_requar_x_cf B IOK Hp IOK_inst TS IQA EAP CA L24MAX_cf kQuarantineMax)|].
split; [exact (di_requar_r_cf B IOK Hp IOK_inst TS IQA EAP CA kQuarantineMax L24MAX_cf)|].
split; [exact (di_requar_e_cf B IOK Hp)|].
split; [exact (di_rview_cf B IOK Hp IOK_inst SBC TS) | exact (di_rview_alloc_cf B IOK Hp)].
Qed.

(* The unprimed drain field ds_drain_cf (one application of DMdrainTop.drain_ok) and its cgif corollary are DELETED
   (Main, 2026-10-30): its Recycle premise, the unprimed rchunk_ok_cf_closed, is false at a real recycle, so the
   field was vacuous.  The drain field is now the PRIMED one, at reply (ds_drain_rh_cf over DMdrainTopRh.drain_m_cf_rh,
   reply lib/A), which takes this file's drain_reads_cf, QBB_of_QB_cf and L24MAX_lt_cf. *)
End T.

End U.
