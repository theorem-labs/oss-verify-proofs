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
   - wsr_drn: MemnormDdrnRh.dealloc_drn_em_rh (the drain arm under the re-hide, over the drain DRNrh_reply := CfF2b's
     YGcfInstDrainTopRh.ds_drain_rh_cf);
   - wsr_big_rh: DGbig.dealloc_big_em_rh;
   - wsr_rcs_rh: SEC_reply := a Theorem Labs lane's YGcfInstFreeSecRhreply.SEC_rh_reply.
   The arms' keep law of MP is DGmpcf.MP_keep_cf_reply_B; TfibSyms is YD2l.TfibB_syms; ErrnoApart's four rows are
   ErrnoApartreply's.  The arms' remaining premises at this instance are this file's Section hypotheses, each at the text
   its owner states: [EXT] [HIOK] [HQB] [HIZR] [HDS] [HDZF] [HCO] [HPFA] (YGcfInstFree.DIfaceExtRh and the open premises
   of CfF2a's YGcfInstFree.diface_rh_cf, which gives the arms' interface DIfaceRh.DIface_rh .. MP: IF_reply), [ENQA]
   (YGcfInstEnq.EnqArmsCf, from which with YGcfInstFreeMidE's enq_bridge_holds_cf / enq_qb_QB_cf YGcfInstEnq.enq_m_cf
   gives the arms' Enqueue at Put's call, MnEnq.de_enqueue_m_t .. MP: ENQm_reply), [EXTB] (YGcfInstFree.DIfaceExtRh at the big
   arm's recycle invariant, from which with SEC YGcfInstFreeBig.diface_big_rh_cf_at gives the big arm's DIfaceBig:
   IFB_reply, its SEC premise being SEC_reply).  The image constants are definitional: AGif2reply.AImg_reply's im_segs is tfibsegs,
   CfImgB.CfImg_B's cf_pc_deallocate is 0x3191c, atp_cf is 1. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YF0m YF0x CfImgB YD2l.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import DeallocG ImgBaseDG DMspec DMiface DGif0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import AGif2reply DGif0reply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YGcfMallocCompose YGcfInstBase YGcfInstFreeModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YGcfInstFreeSig.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require CLdepot MnEnq DIfaceRh DGbigIF YGcfInstDrainR DGmpcf DGfu.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require MemnormDnullRh MemnormDcommonRh MemnormDmidRh MemnormDdrnRh DGbig.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ErrnoApart ErrnoApartreply YGcfInstErrno YGcfInstEnq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyImg_errnoseg ReplyImg_errnonst YGcfInstF1Wreply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YGcfInstFree YGcfInstFreeQ YGcfInstFreePost YGcfInstFreeBig.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YGcfInstDrainTopRh ReplyImg_errbqapart YGcfInstFreeMidE.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YGcfInstFreeSecRhreply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YGcfBatch.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyImg_instok ReplyImg_fvzones ReplyImg_fqconst ReplyImg_errbapart.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ImgBaseAG AGif0reply.
Import ListNotations.
Local Open Scope Z_scope.

(* reply's allocator parameters (A/CfParamsReply.v, shared by both images) and image B's constants (B/CfImgB.v) are this
   file's instances of the layer's CfParams / CfImg. *)
#[local] Existing Instance CfParams_reply.
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

(* The arms' interface IF (DIfaceRh.DIface_rh .. MPcf) is CfF2a's YGcfInstFree.diface_rh_cf (IF_reply below), over the
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
   YGcfInstEnq.enq_m_cf (ENQm_reply below) over: the unit's three Enqueue arms at the cf relation (YGcfInstEnq.EnqArmsCf,
   ENQA), the instance's call-site bridge (YGcfInstFreeMidE.enq_bridge_holds_cf) and the drain-entry bound at QB
   (YGcfInstFreeMidE.enq_qb_QB_cf) *)
Hypothesis ENQA : forall Hp, YGcfInstEnq.EnqArmsCf TfibB (ARX_cf TfibB IOK Hp).
(* The big arm's interface IFB (DGbigIF.DIfaceBig) is YGcfInstFreeBig.diface_big_rh_cf_at (IFB_reply below), over the
   primed callee record at the big arm's recycle invariant [EXTB] and SEC (and the image premises IF_reply takes) *)
Hypothesis EXTB : forall Hp, YGcfInstFree.DIfaceExtRh TfibB IOK Hp (ARXr Hp) L24 QB
  (YGcfInstDrainR.DRq_cf TfibB YGcfInstDrainR.NMAXD_big_cf).

(* reply's malloc limit reaches kQuarantineMax (CfParams_reply's cf_malloc_max = 2 ^ 30 - 2 ^ 20): the big arm exists. *)
Lemma NBIG_reply : kQuarantineMax <= cf_malloc_max + 1.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.

(* YGcfInstFreeSig.SEC_rh_t, the big arm's secondary Recycle walk under the re-hide (the record's wsr_rcs_rh, and
   diface_big_rh_cf_at's second premise), by a Theorem Labs lane's YGcfInstFreeSecRhreply.SEC_rh_reply: ERRB_QAPART is
   ReplyImg_errbqapart.ERRB_QAPART_B, REC_LE is YGcfInstDrainTopRh.rec_le_reply, NBIG is NBIG_reply. *)
Lemma SEC_reply : forall Hp, SEC_rh_t TfibB (aowned TfibB) (ARXr Hp) (YGcfInstDrainR.DRq_cf TfibB YGcfInstDrainR.NMAXD_big_cf).
Proof.
intros Hp.
exact (YGcfInstFreeSecRhreply.SEC_rh_reply TfibB TfibB_syms IOK Hp HIOK ReplyImg_errbqapart.ERRB_QAPART_B
  YGcfInstDrainTopRh.rec_le_reply NBIG_reply).
Qed.

(* MnEnq.de_enqueue_m_t at the instance, by YGcfInstEnq.enq_m_cf (its MP_enq_cf TfibB is DGmpcf.MPcf TfibB, the same
   body at im_segs = tfibsegs); its image premises are reply's closed rows: ErrnoApartreply's nine ErrnoApart lemmas
   (YGcfInstErrno.ErrnoImgCf), ReplyImg_errnoseg.errno_seg_B, ReplyImg_errnonst.errno_nstatic_B,
   YGcfInstF1Wreply.IMG_COVER_reply, YD2l.TfibB_syms and YGcfInstBase.ARX_cf_ARcf. *)
Lemma ENQm_reply : forall Hp, MnEnq.de_enqueue_m_t TfibB (U_cf TfibB) (ARX_cf TfibB IOK Hp) (aowned TfibB)
  (rpreD_small_cf TfibB) qtight (fpre_hp_cf im_segs TfibB Hp) (CLdepot.dpost_x im_segs TfibB) L24 QB (DGmpcf.MPcf TfibB).
Proof.
intros Hp.
assert (EI : YGcfInstErrno.ErrnoImgCf).
{ constructor.
  - exact ErrnoApartreply.errno_in_img_reply.
  - exact ErrnoApartreply.errno_unhidden_reply.
  - exact ErrnoApartreply.errno_apart_dzone_ag_reply.
  - exact ErrnoApartreply.errno_apart_shadow_ag_reply.
  - exact ErrnoApartreply.errno_apart_inst_ag_reply.
  - exact ErrnoApartreply.errno_apart_dzone_d_reply.
  - exact ErrnoApartreply.errno_apart_izone_reply.
  - exact ErrnoApartreply.errno_apart_zone3_d_reply.
  - exact ErrnoApartreply.errno_apart_inst_d_reply. }
exact (YGcfInstEnq.enq_m_cf TfibB TfibB_syms Hp (ARX_cf TfibB IOK Hp) (ARX_cf_ARcf TfibB IOK Hp)
  (rpreD_small_cf TfibB) (fpre_hp_cf im_segs TfibB Hp) (CLdepot.dpost_x im_segs TfibB) L24 QB EI
  (ReplyImg_errnoseg.errno_seg_B TfibB TfibB_syms) ReplyImg_errnonst.errno_nstatic_B YGcfInstF1Wreply.IMG_COVER_reply
  (ENQA Hp)
  (YGcfInstFreeMidE.enq_bridge_holds_cf TfibB IOK Hp (ReplyImg_fvzones.izone_owned_img TfibB TfibB_syms) HIZR HDS
     (ReplyImg_fvzones.dzone_owned_img TfibB TfibB_syms) HDZF HCO (ReplyImg_fvzones.fv_ial_img TfibB TfibB_syms)
     YGcfInstF1Wreply.IMG_COVER_reply ReplyImg_errbapart.ERRB_APART_B HPFA)
  (YGcfInstFreeMidE.enq_qb_QB_cf TfibB IOK Hp)).
Qed.

(* DIfaceRh.DIface_rh at the instance, by YGcfInstFree.diface_rh_cf (its MP is DGmpcf.MPcf TfibB's body); the image
   premises reply has proved: ReplyImg_instok.fm_inst_ok_B (FM_INST_OK), YGcfInstF1Wreply.IMG_COVER_reply,
   YF0m.ts_tsd (FV_TSD), ReplyImg_fvzones.fv_ial_img / dzone_owned_img / izone_owned_img / fv_zone3_img (FV_IAL,
   DZONE_OWNED, IZONE_OWNED, FV_ZONE3), ReplyImg_fqconst.FQ_CONST_B, ReplyImg_errbapart.ERRB_APART_B. *)
Lemma IF_reply : forall Hp, DIfaceRh.DIface_rh TfibB (U_cf TfibB) free_cf (ARX_cf TfibB IOK Hp) (ARXr Hp) (aowned TfibB)
  (rpreD_small_cf TfibB) qtight (fpre_hp_cf im_segs TfibB Hp) (CLdepot.dpost_x im_segs TfibB) drain_body_cf L24 QB DRq
  (DGmpcf.MPcf TfibB).
Proof.
intros Hp.
exact (YGcfInstFree.diface_rh_cf TfibB IOK Hp (ARXr Hp) L24 QB DRq HIOK (ReplyImg_instok.fm_inst_ok_B TfibB TfibB_syms)
  YGcfInstF1Wreply.IMG_COVER_reply (YF0m.ts_tsd TfibB TfibB_syms) (ReplyImg_fvzones.fv_ial_img TfibB TfibB_syms)
  (ReplyImg_fqconst.FQ_CONST_B TfibB TfibB_syms) HQB (ReplyImg_fvzones.dzone_owned_img TfibB TfibB_syms)
  (ReplyImg_fvzones.izone_owned_img TfibB TfibB_syms) ReplyImg_fvzones.fv_zone3_img HIZR HDS HDZF HCO
  ReplyImg_errbapart.ERRB_APART_B HPFA (EXT Hp)).
Qed.

(* DGbigIF.DIfaceBig at the recycle side, by YGcfInstFreeBig.diface_big_rh_cf_at, with the image premises of IF_reply. *)
Lemma IFB_reply : forall Hp, DGbigIF.DIfaceBig TfibB (U_cf TfibB) free_cf (ARX_cf TfibB IOK Hp) (ARXr Hp) (aowned TfibB)
  (rpreD_big_cf TfibB) qtight (fpre_hp_cf im_segs TfibB Hp) (CLdepot.dpost_x im_segs TfibB) drain_body_cf
  (YGcfInstDrainR.DRq_cf TfibB YGcfInstDrainR.NMAXD_big_cf).
Proof.
intros Hp.
exact (YGcfInstFreeBig.diface_big_rh_cf_at TfibB IOK Hp L24 QB HIOK (ReplyImg_instok.fm_inst_ok_B TfibB TfibB_syms)
  YGcfInstF1Wreply.IMG_COVER_reply (YF0m.ts_tsd TfibB TfibB_syms) (ReplyImg_fvzones.fv_ial_img TfibB TfibB_syms)
  (ReplyImg_fqconst.FQ_CONST_B TfibB TfibB_syms) (ReplyImg_fvzones.dzone_owned_img TfibB TfibB_syms)
  (ReplyImg_fvzones.izone_owned_img TfibB TfibB_syms) ReplyImg_fvzones.fv_zone3_img HIZR HDS HDZF HCO
  ReplyImg_errbapart.ERRB_APART_B HPFA (EXTB Hp) (SEC_reply Hp)).
Qed.

(* DIfaceRh.de_drain_m_rh_t, the drain under the re-hide (MemnormDdrnRh's DRNrh), by CfF2b's
   YGcfInstDrainTopRh.ds_drain_rh_cf: its four lane-F2a fields at ARX (di_qview_t / di_qowned_t / di_stack_t / di_frame_t)
   are IF_reply's, ERRB_QAPART is ReplyImg_errbqapart.ERRB_QAPART_B, REC_LE is YGcfInstDrainTopRh.rec_le_reply. *)
Lemma DRNrh_reply : forall Hp, DIfaceRh.de_drain_m_rh_t TfibB (ARX_cf TfibB IOK Hp) (aowned TfibB) drain_body_cf L24 QB.
Proof.
intros Hp.
exact (YGcfInstDrainTopRh.ds_drain_rh_cf TfibB IOK Hp HIOK TfibB_syms TfibB_syms ReplyImg_errbqapart.ERRB_QAPART_B
  (DIfaceRh.dih_qview _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (IF_reply Hp))
  (DIfaceRh.dih_qowned _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (IF_reply Hp))
  (DIfaceRh.dih_stack _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (IF_reply Hp))
  (DIfaceRh.dih_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (IF_reply Hp))
  YGcfInstDrainTopRh.rec_le_reply).
Qed.

Theorem walksigdrh_reply : forall Hp,
  WalkSigDrh TfibB (U_cf TfibB) free_cf (ARX_cf TfibB IOK Hp) (aowned TfibB) (rpreD_small_cf TfibB) qtight
    (fpre_hp_cf im_segs TfibB Hp) atp_cf (rpreD_big_cf TfibB) (ARXr Hp)
    (YGcfInstDrainR.DRq_cf TfibB YGcfInstDrainR.NMAXD_big_cf) (DGmpcf.MPcf TfibB).
Proof.
intros Hp. constructor.
- intros inst so bp ly S W regs mem md p n tr PRE HN.
  exact (MemnormDnullRh.dealloc_null_arm_em TfibB TfibB_syms (U_cf TfibB) free_cf (ARX_cf TfibB IOK Hp) (ARXr Hp)
    (aowned TfibB) (rpreD_small_cf TfibB) qtight (fpre_hp_cf im_segs TfibB Hp) (CLdepot.dpost_x im_segs TfibB)
    drain_body_cf L24 QB DRq (DGmpcf.MPcf TfibB) (IF_reply Hp) inst so bp ly S W regs mem md p n tr PRE HN).
- intros inst so bp ly S W regs mem md p n tr lastb initr PRE HBLK HR HL HC.
  exact (MemnormDcommonRh.dealloc_common_em TfibB (U_cf TfibB) free_cf (ARX_cf TfibB IOK Hp) (ARXr Hp)
    (aowned TfibB) (rpreD_small_cf TfibB) qtight (fpre_hp_cf im_segs TfibB Hp) (CLdepot.dpost_x im_segs TfibB)
    drain_body_cf L24 QB DRq (DGmpcf.MPcf TfibB) (IF_reply Hp) TfibB_syms (DGfu.FH_c TfibB TfibB_syms)
    inst so bp ly S W regs mem md p n tr lastb initr PRE HBLK HR HL HC).
- intros inst so bp ly S W regs mem md p n tr PRE HMP HBLK HNB HC.
  exact (MemnormDmidRh.dealloc_mid_em TfibB TfibB_syms (U_cf TfibB) free_cf (ARX_cf TfibB IOK Hp) (ARXr Hp)
    (aowned TfibB) (rpreD_small_cf TfibB) qtight (fpre_hp_cf im_segs TfibB Hp) (CLdepot.dpost_x im_segs TfibB)
    drain_body_cf L24 QB DRq (DGmpcf.MPcf TfibB) (IF_reply Hp) (ENQm_reply Hp) (DGmpcf.MP_keep_cf_reply_B TfibB)
    ErrnoApartreply.errno_in_img_reply ErrnoApartreply.errno_apart_zone3_d_reply
    ErrnoApartreply.errno_apart_dzone_d_reply ErrnoApartreply.errno_apart_izone_reply
    inst so bp ly S W regs mem md p n tr PRE HMP HBLK HNB HC).
- intros inst so bp ly S W regs mem md p n tr PRE HMP HBLK HD.
  exact (MemnormDdrnRh.dealloc_drn_em_rh TfibB TfibB_syms (U_cf TfibB) free_cf (ARX_cf TfibB IOK Hp) (ARXr Hp)
    (aowned TfibB) (rpreD_small_cf TfibB) qtight (fpre_hp_cf im_segs TfibB Hp) (CLdepot.dpost_x im_segs TfibB)
    drain_body_cf L24 QB DRq (DGmpcf.MPcf TfibB) (IF_reply Hp) (DGmpcf.MP_keep_cf_reply_B TfibB) (ENQm_reply Hp) (DRNrh_reply Hp)
    ErrnoApartreply.errno_in_img_reply ErrnoApartreply.errno_apart_zone3_d_reply
    ErrnoApartreply.errno_apart_dzone_d_reply ErrnoApartreply.errno_apart_izone_reply
    inst so bp ly S W regs mem md p n tr PRE HMP HBLK HD).
- intros inst so bp ly S W regs mem md p n tr PRE HBLK.
  exact (DGbig.dealloc_big_em_rh TfibB TfibB_syms (U_cf TfibB) free_cf (ARX_cf TfibB IOK Hp) (ARXr Hp)
    (aowned TfibB) (rpreD_big_cf TfibB) qtight (fpre_hp_cf im_segs TfibB Hp) (CLdepot.dpost_x im_segs TfibB)
    drain_body_cf (YGcfInstDrainR.DRq_cf TfibB YGcfInstDrainR.NMAXD_big_cf) (IFB_reply Hp)
    ErrnoApartreply.errno_in_img_reply ErrnoApartreply.errno_apart_zone3_d_reply
    ErrnoApartreply.errno_apart_dzone_d_reply ErrnoApartreply.errno_apart_izone_reply
    inst so bp ly S W regs mem md p n tr PRE HBLK).
- exact (SEC_reply Hp).
Qed.
End r.
