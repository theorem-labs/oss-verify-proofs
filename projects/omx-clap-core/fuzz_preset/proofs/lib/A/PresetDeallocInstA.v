(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/PresetDeallocInstA.v, with its module paths changed; 2 of its 85 lines of code are new or changed and 1 line of the source is left out. *)
(* Theorem Labs, 2026-10: fuzz_preset's DEALLOCATE contract at image A', in the primed form, closed.
   It is the A' twin of fuzz_reply's ReplyDeallocInst.adealloc_realizes_raw_cf_em_m_rh_reply (lib/A at
   eb934de95d13), at B := AD2l.TfibB, IOK := the binary's own allocator object, CfImg_A and CfParams_preset.
   Route: the layer's primed free top (YGcfInstFreeTopRh.adealloc_realizes_raw_cf_em_m_rh_cf) at the choices
   ARXr := YGcfInstDrainR.ARXr_cf, L24 := L24MAX_cf, QB := QB_cf kQuarantineMax, DRq := DRq_cf kQuarantineMax,
   with: this image's unit facts (PresetUnitFactsA.preset_unit_facts_A), its QB byte bound
   (PresetQBBytes.qb_bytes_preset_A), its four Printf rows (YGcfInstFreeImgpreset.FP_*_TfibB), PF_APART
   (PresetPfApartA.pf_apart_preset_A), the primed callee record (YGcfInstFreeExtA.diface_ext_rh_preset_A and
   its big-arm twin _big) and the Deallocate arms under the re-hide (PresetWalkSigDrh.walksigdrh_preset) over
   the Enqueue arms (YGcfInstEnqMisspreset.enq_arms_cf_preset at the unit's Refill contract).
   The free contract itself (YG0dcfR.afree_realizes_cf_rh) also needs the wrap-free walk, which is another
   row at preset (A/WrapFreeATop.v); this file ends at the Deallocate contract. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase YGcfBatch.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AF0m AF0x CfImgA CfParamsPreset AD2l.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import DeallocG ImgBaseDG DMspec DMiface DGif0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AImgA ADIfaceA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfMallocCompose YGcfMallocComposeE.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfMallocComposeERh.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfInstBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfInstFreeSig.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfInstFreeView YGcfInstFreeQ YGcfInstFreeModel YGcfInstFree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfInstFreePost YGcfInstFreeTopRh.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfDIface YGcfInstDrainR YGcfInstEnq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require DGmpcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0dcfR.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PresetUnitFactsA PresetPfApartA YGcfInstFreeImgpreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require YGcfInstFreeExtA PresetWalkSigDrh PresetQBBytes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require YGcfInstEnqMisspreset YGcfRefillToppreset RepArmTcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfAroPresetA YGcfInstDrainTopRhA.
From Stdlib Require Import List.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* preset's allocator parameters and image constants are the instances of the layer's classes in this file *)
#[local] Existing Instance CfParams_preset.
#[local] Existing Instance CfImg_A.

(* The instance predicate on the allocator instance: preset's one instance object. It is the drain field's own
   choice (A/YGcfInstDrainTopRhA.v), so both A' tops stand at one IOK. *)
Notation IOK_A := YGcfInstDrainTopRhA.IOK_A.

Section r. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* The unit's three Enqueue arms at the cf relation, over the unit's Refill contract. *)
Lemma ENQA_A : forall Hp, YGcfInstEnq.EnqArmsCf TfibB (ARX_cf TfibB IOK_A Hp).
Proof.
intros Hp.
exact (YGcfInstEnqMisspreset.enq_arms_cf_preset TfibB TfibB_syms IOK_A Hp YGcfInstDrainTopRhA.IOK_ok_A
  CfAroPresetA.relro_seg_preset_A
  (YGcfRefillToppreset.refill_spec_cf_preset_inst TfibB IOK_A TfibB_syms YGcfInstDrainTopRhA.IOK_ok_A
    (@RepArmTcf.classfull_cf_of_hyps fx rc CfParams_preset))).
Qed.

(* preset's Deallocate arms under the re-hide, with the rows plugged. *)
Lemma walksigdrh_A : forall Hp,
  WalkSigDrh TfibB (U_cf TfibB) free_cf (ARX_cf TfibB IOK_A Hp) (aowned TfibB)
    (rpreD_small_cf TfibB) qtight (fpre_hp_cf im_segs TfibB Hp) atp_cf (rpreD_big_cf TfibB)
    (YGcfInstDrainR.ARXr_cf TfibB IOK_A Hp) (YGcfInstDrainR.DRq_cf TfibB YGcfInstDrainR.NMAXD_big_cf)
    (DGmpcf.MPcf TfibB).
Proof.
intros Hp.
exact (PresetWalkSigDrh.walksigdrh_preset IOK_A (YGcfInstDrainR.DRq_cf TfibB kQuarantineMax)
  YGcfInstDrainTopRhA.IOK_ok_A PresetQBBytes.qb_bytes_preset_A
  YGcfInstFreeImgpreset.FP_IZONE_ROM_TfibB YGcfInstFreeImgpreset.FP_DSTAT_TfibB
  YGcfInstFreeImgpreset.FP_DZONE_FP_TfibB YGcfInstFreeImgpreset.FP_CONST_TfibB
  PresetPfApartA.pf_apart_preset_A
  (YGcfInstFreeExtA.diface_ext_rh_preset_A IOK_A YGcfInstDrainTopRhA.IOK_ok_A) ENQA_A
  (YGcfInstFreeExtA.diface_ext_rh_preset_A_big IOK_A YGcfInstDrainTopRhA.IOK_ok_A) Hp).
Qed.

(* Deallocate's primed raw contract at preset's call-site relation, from the layer's primed free top. *)
Theorem adealloc_realizes_raw_cf_em_m_rh_preset_A :
  adealloc_realizes_raw_cf_em_m_rh im_segs TfibB atp_cf (ARXq_cf TfibB IOK_A).
Proof.
pose proof (PresetUnitFactsA.preset_unit_facts_A TfibB TfibB_syms) as UF.
refine (adealloc_realizes_raw_cf_em_m_rh_cf TfibB IOK_A (YGcfInstDrainR.ARXr_cf TfibB IOK_A) L24MAX_cf
  (YGcfInstDrainR.QB_cf kQuarantineMax) (YGcfInstDrainR.DRq_cf TfibB kQuarantineMax)
  YGcfInstDrainTopRhA.IOK_ok_A _ _ _ _ _ PresetQBBytes.qb_bytes_preset_A _ _ _
  YGcfInstFreeImgpreset.FP_IZONE_ROM_TfibB YGcfInstFreeImgpreset.FP_DSTAT_TfibB
  YGcfInstFreeImgpreset.FP_DZONE_FP_TfibB YGcfInstFreeImgpreset.FP_CONST_TfibB _
  PresetPfApartA.pf_apart_preset_A
  (YGcfInstFreeExtA.diface_ext_rh_preset_A IOK_A YGcfInstDrainTopRhA.IOK_ok_A) walksigdrh_A).

- exact (PresetUnitFactsA.uf_dg_inst_ok _ UF).
- exact (PresetUnitFactsA.uf_IMG_COVER _ UF).
- exact (PresetUnitFactsA.uf_HTSD _ UF).
- exact (PresetUnitFactsA.uf_FV_IAL _ UF).
- exact (PresetUnitFactsA.uf_FQ_CONST _ UF).
- exact (PresetUnitFactsA.uf_DZONE_OWNED _ UF).
- exact (PresetUnitFactsA.uf_IZONE_OWNED _ UF).
- exact (PresetUnitFactsA.uf_FV_ZONE3 _ UF).
- exact (PresetUnitFactsA.uf_ERRB_APART _ UF).
Qed.

End r.
Print Assumptions adealloc_realizes_raw_cf_em_m_rh_preset_A.
