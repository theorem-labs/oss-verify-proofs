(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/ReplyWalkSigDrh.v (commit eb934de95d13, blob 474fc8465c2f) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb), from reply A d751b179ea49 (pin 42c58610e125); module paths changed; 0 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AF0m AF0x CfImgA CfParamsPreset AD2l.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import DeallocG ImgBaseDG DMspec DMiface DGif0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AImgA ADIfaceA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfMallocCompose YGcfInstBase YGcfInstFreeModel.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfInstFreeSig.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require CLdepot MnEnq DIfaceRh DGbigIF YGcfInstDrainR.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require DGmpcf DGfu.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require MemnormDnullRh MemnormDcommonRh MemnormDmidRh MemnormDdrnRh DGbig.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require ErrnoApart.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require ErrnoApartpreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfInstErrno YGcfInstEnq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PresetImg_errnoseg PresetImg_errnonst YGcfInstF1Wpreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfInstFree YGcfInstFreeQ YGcfInstFreePost YGcfInstFreeBig.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require YGcfInstDrainTopRh CfInstImgA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfInstFreeMidE.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require YGcfInstFreeSecRhpreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfBatch.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PresetImg_instok PresetImg_fvzones PresetImg_fqconst PresetImg_errbapart.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseAG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AGImgA.
Import ListNotations.
Local Open Scope Z_scope.

#[local] Existing Instance CfParams_preset.
#[local] Existing Instance CfImg_A.

Section r. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable IOK : Z -> Prop.

Local Notation ARXr := (YGcfInstDrainR.ARXr_cf TfibB IOK).

Local Notation L24 := YGcfBatch.L24MAX_cf.
Local Notation QB := (YGcfInstDrainR.QB_cf kQuarantineMax).
Variable DRq : astate -> list chunk -> list Z -> Prop.

Hypothesis HIOK : IOK_ok TfibB IOK.
Hypothesis HQB : YGcfInstFreeQ.QB_BYTES QB.
Hypothesis HIZR : YGcfInstFreePost.FP_IZONE_ROM TfibB.
Hypothesis HDS : YGcfInstFreePost.FP_DSTAT TfibB.
Hypothesis HDZF : YGcfInstFreePost.FP_DZONE_FP TfibB.
Hypothesis HCO : YGcfInstFreePost.FP_CONST TfibB.
Hypothesis HPFA : YGcfInstFreePost.PF_APART TfibB.
Hypothesis EXT : forall Hp, YGcfInstFree.DIfaceExtRh TfibB IOK Hp (ARXr Hp) L24 QB DRq.

Hypothesis ENQA : forall Hp, YGcfInstEnq.EnqArmsCf TfibB (ARX_cf TfibB IOK Hp).

Hypothesis EXTB : forall Hp, YGcfInstFree.DIfaceExtRh TfibB IOK Hp (ARXr Hp) L24 QB
  (YGcfInstDrainR.DRq_cf TfibB YGcfInstDrainR.NMAXD_big_cf).

Lemma NBIG_preset : kQuarantineMax <= cf_malloc_max + 1.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.

Lemma SEC_preset : forall Hp, SEC_rh_t TfibB (aowned TfibB) (ARXr Hp) (YGcfInstDrainR.DRq_cf TfibB YGcfInstDrainR.NMAXD_big_cf).
Proof.
intros Hp.
exact (YGcfInstFreeSecRhpreset.SEC_rh_preset TfibB TfibB_syms IOK Hp HIOK CfInstImgA.ERRB_QAPART_A
  YGcfInstDrainTopRh.rec_le_preset NBIG_preset).
Qed.

Lemma ENQm_preset : forall Hp, MnEnq.de_enqueue_m_t TfibB (U_cf TfibB) (ARX_cf TfibB IOK Hp) (aowned TfibB)
  (rpreD_small_cf TfibB) qtight (fpre_hp_cf im_segs TfibB Hp) (CLdepot.dpost_x im_segs TfibB) L24 QB (DGmpcf.MPcf TfibB).
Proof.
intros Hp.
assert (EI : YGcfInstErrno.ErrnoImgCf).
{ constructor.
  - exact ErrnoApartpreset.errno_in_img_preset.
  - exact ErrnoApartpreset.errno_unhidden_preset.
  - exact ErrnoApartpreset.errno_apart_dzone_ag_preset.
  - exact ErrnoApartpreset.errno_apart_shadow_ag_preset.
  - exact ErrnoApartpreset.errno_apart_inst_ag_preset.
  - exact ErrnoApartpreset.errno_apart_dzone_d_preset.
  - exact ErrnoApartpreset.errno_apart_izone_preset.
  - exact ErrnoApartpreset.errno_apart_zone3_d_preset.
  - exact ErrnoApartpreset.errno_apart_inst_d_preset. }
exact (YGcfInstEnq.enq_m_cf TfibB TfibB_syms Hp (ARX_cf TfibB IOK Hp) (ARX_cf_ARcf TfibB IOK Hp)
  (rpreD_small_cf TfibB) (fpre_hp_cf im_segs TfibB Hp) (CLdepot.dpost_x im_segs TfibB) L24 QB EI
  (PresetImg_errnoseg.errno_seg_A TfibB TfibB_syms) PresetImg_errnonst.errno_nstatic_A YGcfInstF1Wpreset.IMG_COVER_preset
  (ENQA Hp)
  (YGcfInstFreeMidE.enq_bridge_holds_cf TfibB IOK Hp (PresetImg_fvzones.izone_owned_img TfibB TfibB_syms) HIZR HDS
     (PresetImg_fvzones.dzone_owned_img TfibB TfibB_syms) HDZF HCO (PresetImg_fvzones.fv_ial_img TfibB TfibB_syms)
     YGcfInstF1Wpreset.IMG_COVER_preset PresetImg_errbapart.ERRB_APART_A HPFA)
  (YGcfInstFreeMidE.enq_qb_QB_cf TfibB IOK Hp)).
Qed.

Lemma IF_preset : forall Hp, DIfaceRh.DIface_rh TfibB (U_cf TfibB) free_cf (ARX_cf TfibB IOK Hp) (ARXr Hp) (aowned TfibB)
  (rpreD_small_cf TfibB) qtight (fpre_hp_cf im_segs TfibB Hp) (CLdepot.dpost_x im_segs TfibB) drain_body_cf L24 QB DRq
  (DGmpcf.MPcf TfibB).
Proof.
intros Hp.
exact (YGcfInstFree.diface_rh_cf TfibB IOK Hp (ARXr Hp) L24 QB DRq HIOK (PresetImg_instok.fm_inst_ok_A TfibB TfibB_syms)
  YGcfInstF1Wpreset.IMG_COVER_preset (AF0m.ts_tsd TfibB TfibB_syms) (PresetImg_fvzones.fv_ial_img TfibB TfibB_syms)
  (PresetImg_fqconst.FQ_CONST_A TfibB TfibB_syms) HQB (PresetImg_fvzones.dzone_owned_img TfibB TfibB_syms)
  (PresetImg_fvzones.izone_owned_img TfibB TfibB_syms) PresetImg_fvzones.fv_zone3_img HIZR HDS HDZF HCO
  PresetImg_errbapart.ERRB_APART_A HPFA (EXT Hp)).
Qed.

Lemma IFB_preset : forall Hp, DGbigIF.DIfaceBig TfibB (U_cf TfibB) free_cf (ARX_cf TfibB IOK Hp) (ARXr Hp) (aowned TfibB)
  (rpreD_big_cf TfibB) qtight (fpre_hp_cf im_segs TfibB Hp) (CLdepot.dpost_x im_segs TfibB) drain_body_cf
  (YGcfInstDrainR.DRq_cf TfibB YGcfInstDrainR.NMAXD_big_cf).
Proof.
intros Hp.
exact (YGcfInstFreeBig.diface_big_rh_cf_at TfibB IOK Hp L24 QB HIOK (PresetImg_instok.fm_inst_ok_A TfibB TfibB_syms)
  YGcfInstF1Wpreset.IMG_COVER_preset (AF0m.ts_tsd TfibB TfibB_syms) (PresetImg_fvzones.fv_ial_img TfibB TfibB_syms)
  (PresetImg_fqconst.FQ_CONST_A TfibB TfibB_syms) (PresetImg_fvzones.dzone_owned_img TfibB TfibB_syms)
  (PresetImg_fvzones.izone_owned_img TfibB TfibB_syms) PresetImg_fvzones.fv_zone3_img HIZR HDS HDZF HCO
  PresetImg_errbapart.ERRB_APART_A HPFA (EXTB Hp) (SEC_preset Hp)).
Qed.

Lemma DRNrh_preset : forall Hp, DIfaceRh.de_drain_m_rh_t TfibB (ARX_cf TfibB IOK Hp) (aowned TfibB) drain_body_cf L24 QB.
Proof.
intros Hp.
exact (YGcfInstDrainTopRh.ds_drain_rh_cf TfibB IOK Hp HIOK TfibB_syms TfibB_syms CfInstImgA.ERRB_QAPART_A
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
    drain_body_cf L24 QB DRq (DGmpcf.MPcf TfibB) (IF_preset Hp) (ENQm_preset Hp) (DGmpcf.MP_keep_cf_preset TfibB)
    ErrnoApartpreset.errno_in_img_preset ErrnoApartpreset.errno_apart_zone3_d_preset
    ErrnoApartpreset.errno_apart_dzone_d_preset ErrnoApartpreset.errno_apart_izone_preset
    inst so bp ly S W regs mem md p n tr PRE HMP HBLK HNB HC).
- intros inst so bp ly S W regs mem md p n tr PRE HMP HBLK HD.
  exact (MemnormDdrnRh.dealloc_drn_em_rh TfibB TfibB_syms (U_cf TfibB) free_cf (ARX_cf TfibB IOK Hp) (ARXr Hp)
    (aowned TfibB) (rpreD_small_cf TfibB) qtight (fpre_hp_cf im_segs TfibB Hp) (CLdepot.dpost_x im_segs TfibB)
    drain_body_cf L24 QB DRq (DGmpcf.MPcf TfibB) (IF_preset Hp) (DGmpcf.MP_keep_cf_preset TfibB) (ENQm_preset Hp) (DRNrh_preset Hp)
    ErrnoApartpreset.errno_in_img_preset ErrnoApartpreset.errno_apart_zone3_d_preset
    ErrnoApartpreset.errno_apart_dzone_d_preset ErrnoApartpreset.errno_apart_izone_preset
    inst so bp ly S W regs mem md p n tr PRE HMP HBLK HD).
- intros inst so bp ly S W regs mem md p n tr PRE HBLK.
  exact (DGbig.dealloc_big_em_rh TfibB TfibB_syms (U_cf TfibB) free_cf (ARX_cf TfibB IOK Hp) (ARXr Hp)
    (aowned TfibB) (rpreD_big_cf TfibB) qtight (fpre_hp_cf im_segs TfibB Hp) (CLdepot.dpost_x im_segs TfibB)
    drain_body_cf (YGcfInstDrainR.DRq_cf TfibB YGcfInstDrainR.NMAXD_big_cf) (IFB_preset Hp)
    ErrnoApartpreset.errno_in_img_preset ErrnoApartpreset.errno_apart_zone3_d_preset
    ErrnoApartpreset.errno_apart_dzone_d_preset ErrnoApartpreset.errno_apart_izone_preset
    inst so bp ly S W regs mem md p n tr PRE HBLK).
- exact (SEC_preset Hp).
Qed.
End r.
