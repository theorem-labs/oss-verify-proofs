(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31: from proofs/plugin-hostd/fuzz_reply/lib/B/ReplyWalkSigDrh.v (commit 4d286b2e618d, file sha256 0fdae9655fab) onto omx-clap-core/fuzz_preset's ASan+UBSan image B' (fuzz_preset.asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43); module paths changed; reply's image-instance names mapped to preset's B' instance (AGif2reply / AImg_reply -> AGif2cgif / AImg_cgif) and its row names to preset's (Reply* -> Preset*, *reply -> *preset); its 0 image numerals moved by symbol from fuzz_reply.asan-ubsan (pin 10ffb5f9202a) to B' (port_addr_check 3d2eee813cce predictions; object addresses written in decimal, jump-table offsets and list indices by the same stage map), 0 list indices re-picked, and 1 addresses named in comments; facts preset already states are cited, not restated; comment references to people and refs dropped; no other numeral changed. *)
(* Reply's Deallocate walk under the re-hide at image B, at the cf layer's round 3 part 3: an instance of CfF2a's record
   YGcfInstFreeSig.WalkSigDrh (lib/B) at the free top's instance, in the form image B's primed top
   YGcfInstFreeTopRh.adealloc_realizes_raw_cf_em_m_rh_cf takes it (lib/B/YGcfInstFreeTopRh.v:251-256, B row (c)
   02b40b5bc30b): the lib/B mirror of lib/A/ReplyWalkSigDrh.v (AFREE_CF premise #12), with image B's module names.
   rule 24: no function proved (kind: instance of a record of walk tops from the unit's arm theorems).

   The instance: B := TfibB, U := U_cf TfibB, ft := free_cf, ARX := ARX_cf TfibB IOK Hp, AOX := aowned TfibB,
   rpre := rpreD_small_cf TfibB, lpost := qtight, fpre := fpre_hp_cf im_segs TfibB Hp, atpD := atp_cf,
   rpreB := rpreD_big_cf TfibB, ARXr := YGcfInstDrainR.ARXr_cf TfibB IOK Hp, DRq := YGcfInstDrainR.DRq_cf TfibB YGcfInstDrainR.NMAXD_big_cf,
   MP := DGmpcf.MPcf TfibB (the memory predicate of the cf instance, at reply B's image constants); the free interface's
   L24 / QB are lane F2b's L24MAX_cf / QB_cf kQuarantineMax.
   The fields, from reply's arm theorems:
   - wsr_null: MemnormDnullRh.dealloc_null_arm_em (MemnormDnull's, over DIfaceRh.DIface_rh);
   - wsr_common: MemnormDcommonRh.dealloc_common_em (MemnormDcommon's, over DIface_rh), its seed by DGfu.FH_c;
   - wsr_mid: MemnormDmidRh.dealloc_mid_em (MemnormDmid's, over DIface_rh);
   - wsr_drn: MemnormDdrnRh.dealloc_drn_em_rh (the drain arm under the re-hide, over the drain DRNrh_preset := CfF2b's
     YGcfInstDrainTopRh.ds_drain_rh_cf);
   - wsr_big_rh: DGbig.dealloc_big_em_rh;
   - wsr_rcs_rh: SEC_preset := a prior worker's YGcfInstFreeSecRhpreset.SEC_rh_preset.
   The arms' keep law of MP is DGmpcf.MP_keep_cf_preset_B; TfibSyms is YD2l.TfibB_syms; ErrnoApart's four rows are
   ErrnoApartreply's.  The arms' remaining premises at this instance are this file's Section hypotheses, each at the text
   its owner states: [EXT] [HIOK] [HQB] [HIZR] [HDS] [HDZF] [HCO] [HPFA] (YGcfInstFree.DIfaceExtRh and the open premises
   of CfF2a's YGcfInstFree.diface_rh_cf, which gives the arms' interface DIfaceRh.DIface_rh .. MP: IF_preset), [ENQA]
   (YGcfInstEnq.EnqArmsCf, from which with YGcfInstFreeMidE's enq_bridge_holds_cf / enq_qb_QB_cf YGcfInstEnq.enq_m_cf
   gives the arms' Enqueue at Put's call, MnEnq.de_enqueue_m_t .. MP: ENQm_preset), [EXTB] (YGcfInstFree.DIfaceExtRh at the big
   arm's recycle invariant, from which with SEC YGcfInstFreeBig.diface_big_rh_cf_at gives the big arm's DIfaceBig:
   IFB_preset, its SEC premise being SEC_preset).  The image constants are definitional: AGif2cgif.AImg_reply's im_segs is tfibsegs,
   CfImgB.CfImg_B's cf_pc_deallocate is 0x32390, atp_cf is 1. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YF0m YF0x. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import CfImgB. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YD2l.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import DeallocG ImgBaseDG DMspec DMiface DGif0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGif2cgif DGif0cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfMallocCompose YGcfInstBase YGcfInstFreeModel.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfInstFreeSig.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require CLdepot MnEnq DIfaceRh DGbigIF YGcfInstDrainR. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require DGmpcf DGfu.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require MemnormDnullRh MemnormDcommonRh MemnormDmidRh MemnormDdrnRh DGbig.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require ErrnoApart. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require ErrnoApartcgif. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfInstErrno YGcfInstEnq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require PresetImg_errnoseg PresetImg_errnonst YGcfInstF1Wpreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfInstFree YGcfInstFreeQ YGcfInstFreePost YGcfInstFreeBig.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require YGcfInstDrainTopRh PresetImg_errbqapart. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfInstFreeMidE.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require YGcfInstFreeSecRhpreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfBatch.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require PresetImg_instok PresetImg_fvzones PresetImg_fqconst PresetImg_errbapart.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseAG. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGif0cgif.
Import ListNotations.
Local Open Scope Z_scope.

(* reply's allocator parameters (A/CfParamsPreset.v, shared by both images) and image B's constants (B/CfImgB.v) are this
   file's instances of the layer's CfParams / CfImg. *)
#[local] Existing Instance CfParams_preset.
#[local] Existing Instance CfImg_B.

Section r. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable IOK : Z -> Prop.
(* the consumer's choice: the drain's recycle invariant of the free interface; the drain's cut relation is row (c)'s YGcfInstDrainR.ARXr_cf TfibB IOK (ARXr below), the one
   YGcfInstFreeBig.diface_big_rh_cf_at is stated at *)
Local Notation ARXr := (YGcfInstDrainR.ARXr_cf TfibB IOK).
(* the drain's batch-count bound and drain-entry premise are lane F2b's (L24MAX_cf, QB_cf kQuarantineMax), the ones
   YGcfInstDrainTopRh.ds_drain_rh_cf is stated at *)
Local Notation L24 := YGcfBatch.L24MAX_cf.
Local Notation QB := (YGcfInstDrainR.QB_cf kQuarantineMax).
Variable DRq : astate -> list chunk -> list Z -> Prop.

(* The arms' interface IF (DIfaceRh.DIface_rh .. MPcf) is CfF2a's YGcfInstFree.diface_rh_cf (IF_preset below), over the
   primed callee record YGcfInstFree.DIfaceExtRh [EXT], the instance predicate's law [HIOK], the drain-entry bound's
   byte form [HQB] and the image rows reply has not proved yet [HIZR] [HDS] [HDZF] [HCO] [HPFA]; its other image premises
   are reply's closed rows. *)
Hypothesis HIOK : IOK_ok TfibB IOK.
Hypothesis HQB : YGcfInstFreeQ.QB_BYTES QB.
Hypothesis HIZR : YGcfInstFreePost.FP_IZONE_ROM TfibB.
Hypothesis HDS : YGcfInstFreePost.FP_DSTAT TfibB.
Hypothesis HDZF : YGcfInstFreePost.FP_DZONE_FP TfibB.
Hypothesis HCO : YGcfInstFreePost.FP_CONST TfibB.
Hypothesis HPFA : YGcfInstFreePost.PF_APART TfibB.
Hypothesis EXT : forall Hp, YGcfInstFree.DIfaceExtRh TfibB IOK Hp (ARXr Hp) L24 QB DRq.
(* The mid and drain arms' Enqueue at Put's call (MemnormDmid's ENQm, MnEnq.de_enqueue_m_t .. MPcf) is
   YGcfInstEnq.enq_m_cf (ENQm_preset below) over: the unit's three Enqueue arms at the cf relation (YGcfInstEnq.EnqArmsCf,
   ENQA), the instance's call-site bridge (YGcfInstFreeMidE.enq_bridge_holds_cf) and the drain-entry bound at QB
   (YGcfInstFreeMidE.enq_qb_QB_cf) *)
Hypothesis ENQA : forall Hp, YGcfInstEnq.EnqArmsCf TfibB (ARX_cf TfibB IOK Hp).
(* The big arm's interface IFB (DGbigIF.DIfaceBig) is YGcfInstFreeBig.diface_big_rh_cf_at (IFB_preset below), over the
   primed callee record at the big arm's recycle invariant [EXTB] and SEC (and the image premises IF_preset takes) *)
Hypothesis EXTB : forall Hp, YGcfInstFree.DIfaceExtRh TfibB IOK Hp (ARXr Hp) L24 QB
  (YGcfInstDrainR.DRq_cf TfibB YGcfInstDrainR.NMAXD_big_cf).

(* reply's malloc limit reaches kQuarantineMax (CfParams_reply's cf_malloc_max = 2 ^ 30 - 2 ^ 20): the big arm exists. *)
Lemma NBIG_preset : kQuarantineMax <= cf_malloc_max + 1.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.

(* YGcfInstFreeSig.SEC_rh_t, the big arm's secondary Recycle walk under the re-hide (the record's wsr_rcs_rh, and
   diface_big_rh_cf_at's second premise), by a prior worker's YGcfInstFreeSecRhpreset.SEC_rh_preset: ERRB_QAPART is
   PresetImg_errbqapart.ERRB_QAPART_B, REC_LE is YGcfInstDrainTopRh.rec_le_preset, NBIG is NBIG_preset. *)
Lemma SEC_preset : forall Hp, SEC_rh_t TfibB (aowned TfibB) (ARXr Hp) (YGcfInstDrainR.DRq_cf TfibB YGcfInstDrainR.NMAXD_big_cf).
Proof.
intros Hp.
exact (YGcfInstFreeSecRhpreset.SEC_rh_preset TfibB TfibB_syms IOK Hp HIOK PresetImg_errbqapart.ERRB_QAPART_B
  YGcfInstDrainTopRh.rec_le_preset NBIG_preset).
Qed.

(* MnEnq.de_enqueue_m_t at the instance, by YGcfInstEnq.enq_m_cf (its MP_enq_cf TfibB is DGmpcf.MPcf TfibB, the same
   body at im_segs = tfibsegs); its image premises are reply's closed rows: ErrnoApartreply's nine ErrnoApart lemmas
   (YGcfInstErrno.ErrnoImgCf), PresetImg_errnoseg.errno_seg_B, PresetImg_errnonst.errno_nstatic_B,
   YGcfInstF1Wpreset.IMG_COVER_preset, YD2l.TfibB_syms and YGcfInstBase.ARX_cf_ARcf. *)
Lemma ENQm_preset : forall Hp, MnEnq.de_enqueue_m_t TfibB (U_cf TfibB) (ARX_cf TfibB IOK Hp) (aowned TfibB)
  (rpreD_small_cf TfibB) qtight (fpre_hp_cf im_segs TfibB Hp) (CLdepot.dpost_x im_segs TfibB) L24 QB (DGmpcf.MPcf TfibB).
Proof.
intros Hp.
assert (EI : YGcfInstErrno.ErrnoImgCf).
{ constructor.
  - exact ErrnoApartcgif.errno_in_img_cgif.
  - exact ErrnoApartcgif.errno_unhidden_cgif.
  - exact ErrnoApartcgif.errno_apart_dzone_ag_cgif.
  - exact ErrnoApartcgif.errno_apart_shadow_ag_cgif.
  - exact ErrnoApartcgif.errno_apart_inst_ag_cgif.
  - exact ErrnoApartcgif.errno_apart_dzone_d_cgif.
  - exact ErrnoApartcgif.errno_apart_izone_cgif.
  - exact ErrnoApartcgif.errno_apart_zone3_d_cgif.
  - exact ErrnoApartcgif.errno_apart_inst_d_cgif. }
exact (YGcfInstEnq.enq_m_cf TfibB TfibB_syms Hp (ARX_cf TfibB IOK Hp) (ARX_cf_ARcf TfibB IOK Hp)
  (rpreD_small_cf TfibB) (fpre_hp_cf im_segs TfibB Hp) (CLdepot.dpost_x im_segs TfibB) L24 QB EI
  (PresetImg_errnoseg.errno_seg_B TfibB TfibB_syms) PresetImg_errnonst.errno_nstatic_B YGcfInstF1Wpreset.IMG_COVER_preset
  (ENQA Hp)
  (YGcfInstFreeMidE.enq_bridge_holds_cf TfibB IOK Hp (PresetImg_fvzones.izone_owned_img TfibB TfibB_syms) HIZR HDS
     (PresetImg_fvzones.dzone_owned_img TfibB TfibB_syms) HDZF HCO (PresetImg_fvzones.fv_ial_img TfibB TfibB_syms)
     YGcfInstF1Wpreset.IMG_COVER_preset PresetImg_errbapart.ERRB_APART_B HPFA)
  (YGcfInstFreeMidE.enq_qb_QB_cf TfibB IOK Hp)).
Qed.

(* DIfaceRh.DIface_rh at the instance, by YGcfInstFree.diface_rh_cf (its MP is DGmpcf.MPcf TfibB's body); the image
   premises reply has proved: PresetImg_instok.fm_inst_ok_B (FM_INST_OK), YGcfInstF1Wpreset.IMG_COVER_preset,
   YF0m.ts_tsd (FV_TSD), PresetImg_fvzones.fv_ial_img / dzone_owned_img / izone_owned_img / fv_zone3_img (FV_IAL,
   DZONE_OWNED, IZONE_OWNED, FV_ZONE3), PresetImg_fqconst.FQ_CONST_B, PresetImg_errbapart.ERRB_APART_B. *)
Lemma IF_preset : forall Hp, DIfaceRh.DIface_rh TfibB (U_cf TfibB) free_cf (ARX_cf TfibB IOK Hp) (ARXr Hp) (aowned TfibB)
  (rpreD_small_cf TfibB) qtight (fpre_hp_cf im_segs TfibB Hp) (CLdepot.dpost_x im_segs TfibB) drain_body_cf L24 QB DRq
  (DGmpcf.MPcf TfibB).
Proof.
intros Hp.
exact (YGcfInstFree.diface_rh_cf TfibB IOK Hp (ARXr Hp) L24 QB DRq HIOK (PresetImg_instok.fm_inst_ok_B TfibB TfibB_syms)
  YGcfInstF1Wpreset.IMG_COVER_preset (YF0m.ts_tsd TfibB TfibB_syms) (PresetImg_fvzones.fv_ial_img TfibB TfibB_syms)
  (PresetImg_fqconst.FQ_CONST_B TfibB TfibB_syms) HQB (PresetImg_fvzones.dzone_owned_img TfibB TfibB_syms)
  (PresetImg_fvzones.izone_owned_img TfibB TfibB_syms) PresetImg_fvzones.fv_zone3_img HIZR HDS HDZF HCO
  PresetImg_errbapart.ERRB_APART_B HPFA (EXT Hp)).
Qed.

(* DGbigIF.DIfaceBig at the recycle side, by YGcfInstFreeBig.diface_big_rh_cf_at, with the image premises of IF_preset. *)
Lemma IFB_preset : forall Hp, DGbigIF.DIfaceBig TfibB (U_cf TfibB) free_cf (ARX_cf TfibB IOK Hp) (ARXr Hp) (aowned TfibB)
  (rpreD_big_cf TfibB) qtight (fpre_hp_cf im_segs TfibB Hp) (CLdepot.dpost_x im_segs TfibB) drain_body_cf
  (YGcfInstDrainR.DRq_cf TfibB YGcfInstDrainR.NMAXD_big_cf).
Proof.
intros Hp.
exact (YGcfInstFreeBig.diface_big_rh_cf_at TfibB IOK Hp L24 QB HIOK (PresetImg_instok.fm_inst_ok_B TfibB TfibB_syms)
  YGcfInstF1Wpreset.IMG_COVER_preset (YF0m.ts_tsd TfibB TfibB_syms) (PresetImg_fvzones.fv_ial_img TfibB TfibB_syms)
  (PresetImg_fqconst.FQ_CONST_B TfibB TfibB_syms) (PresetImg_fvzones.dzone_owned_img TfibB TfibB_syms)
  (PresetImg_fvzones.izone_owned_img TfibB TfibB_syms) PresetImg_fvzones.fv_zone3_img HIZR HDS HDZF HCO
  PresetImg_errbapart.ERRB_APART_B HPFA (EXTB Hp) (SEC_preset Hp)).
Qed.

(* DIfaceRh.de_drain_m_rh_t, the drain under the re-hide (MemnormDdrnRh's DRNrh), by CfF2b's
   YGcfInstDrainTopRh.ds_drain_rh_cf: its four lane-F2a fields at ARX (di_qview_t / di_qowned_t / di_stack_t / di_frame_t)
   are IF_reply's, ERRB_QAPART is PresetImg_errbqapart.ERRB_QAPART_B, REC_LE is YGcfInstDrainTopRh.rec_le_preset. *)
Lemma DRNrh_preset : forall Hp, DIfaceRh.de_drain_m_rh_t TfibB (ARX_cf TfibB IOK Hp) (aowned TfibB) drain_body_cf L24 QB.
Proof.
intros Hp.
exact (YGcfInstDrainTopRh.ds_drain_rh_cf TfibB IOK Hp HIOK TfibB_syms TfibB_syms PresetImg_errbqapart.ERRB_QAPART_B
  (DIfaceRh.dih_qview _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (IF_preset Hp))
  (DIfaceRh.dih_qowned _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (IF_preset Hp))
  (DIfaceRh.dih_stack _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (IF_preset Hp))
  (DIfaceRh.dih_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (IF_preset Hp))
  YGcfInstDrainTopRh.rec_le_preset).
Qed.

Theorem walksigdrh_preset : forall Hp,
  WalkSigDrh TfibB (U_cf TfibB) free_cf (ARX_cf TfibB IOK Hp) (aowned TfibB) (rpreD_small_cf TfibB) qtight
    (fpre_hp_cf im_segs TfibB Hp) atp_cf (rpreD_big_cf TfibB) (ARXr Hp)
    (YGcfInstDrainR.DRq_cf TfibB YGcfInstDrainR.NMAXD_big_cf) (DGmpcf.MPcf TfibB).
Proof.
intros Hp. constructor.
- intros inst so bp ly S W regs mem md p n tr PRE HN.
  exact (MemnormDnullRh.dealloc_null_arm_em TfibB TfibB_syms (U_cf TfibB) free_cf (ARX_cf TfibB IOK Hp) (ARXr Hp)
    (aowned TfibB) (rpreD_small_cf TfibB) qtight (fpre_hp_cf im_segs TfibB Hp) (CLdepot.dpost_x im_segs TfibB)
    drain_body_cf L24 QB DRq (DGmpcf.MPcf TfibB) (IF_preset Hp) inst so bp ly S W regs mem md p n tr PRE HN).
- intros inst so bp ly S W regs mem md p n tr lastb initr PRE HBLK HR HL HC.
  exact (MemnormDcommonRh.dealloc_common_em TfibB (U_cf TfibB) free_cf (ARX_cf TfibB IOK Hp) (ARXr Hp)
    (aowned TfibB) (rpreD_small_cf TfibB) qtight (fpre_hp_cf im_segs TfibB Hp) (CLdepot.dpost_x im_segs TfibB)
    drain_body_cf L24 QB DRq (DGmpcf.MPcf TfibB) (IF_preset Hp) TfibB_syms (DGfu.FH_c TfibB TfibB_syms)
    inst so bp ly S W regs mem md p n tr lastb initr PRE HBLK HR HL HC).
- intros inst so bp ly S W regs mem md p n tr PRE HMP HBLK HNB HC.
  exact (MemnormDmidRh.dealloc_mid_em TfibB TfibB_syms (U_cf TfibB) free_cf (ARX_cf TfibB IOK Hp) (ARXr Hp)
    (aowned TfibB) (rpreD_small_cf TfibB) qtight (fpre_hp_cf im_segs TfibB Hp) (CLdepot.dpost_x im_segs TfibB)
    drain_body_cf L24 QB DRq (DGmpcf.MPcf TfibB) (IF_preset Hp) (ENQm_preset Hp) (DGmpcf.MP_keep_cf_preset_B TfibB)
    ErrnoApartcgif.errno_in_img_cgif ErrnoApartcgif.errno_apart_zone3_d_cgif
    ErrnoApartcgif.errno_apart_dzone_d_cgif ErrnoApartcgif.errno_apart_izone_cgif
    inst so bp ly S W regs mem md p n tr PRE HMP HBLK HNB HC).
- intros inst so bp ly S W regs mem md p n tr PRE HMP HBLK HD.
  exact (MemnormDdrnRh.dealloc_drn_em_rh TfibB TfibB_syms (U_cf TfibB) free_cf (ARX_cf TfibB IOK Hp) (ARXr Hp)
    (aowned TfibB) (rpreD_small_cf TfibB) qtight (fpre_hp_cf im_segs TfibB Hp) (CLdepot.dpost_x im_segs TfibB)
    drain_body_cf L24 QB DRq (DGmpcf.MPcf TfibB) (IF_preset Hp) (DGmpcf.MP_keep_cf_preset_B TfibB) (ENQm_preset Hp) (DRNrh_preset Hp)
    ErrnoApartcgif.errno_in_img_cgif ErrnoApartcgif.errno_apart_zone3_d_cgif
    ErrnoApartcgif.errno_apart_dzone_d_cgif ErrnoApartcgif.errno_apart_izone_cgif
    inst so bp ly S W regs mem md p n tr PRE HMP HBLK HD).
- intros inst so bp ly S W regs mem md p n tr PRE HBLK.
  exact (DGbig.dealloc_big_em_rh TfibB TfibB_syms (U_cf TfibB) free_cf (ARX_cf TfibB IOK Hp) (ARXr Hp)
    (aowned TfibB) (rpreD_big_cf TfibB) qtight (fpre_hp_cf im_segs TfibB Hp) (CLdepot.dpost_x im_segs TfibB)
    drain_body_cf (YGcfInstDrainR.DRq_cf TfibB YGcfInstDrainR.NMAXD_big_cf) (IFB_preset Hp)
    ErrnoApartcgif.errno_in_img_cgif ErrnoApartcgif.errno_apart_zone3_d_cgif
    ErrnoApartcgif.errno_apart_dzone_d_cgif ErrnoApartcgif.errno_apart_izone_cgif
    inst so bp ly S W regs mem md p n tr PRE HBLK).
- exact (SEC_preset Hp).
Qed.
End r.
