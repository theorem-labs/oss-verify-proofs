(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31: from proofs/plugin-hostd/fuzz_reply/lib/B/ReplyDeallocInstB.v (commit b104d24056b5, file sha256 c0f8eddb3dbe) onto omx-clap-core/fuzz_preset's ASan+UBSan image B' (fuzz_preset.asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43); module paths changed; reply's instance and row names mapped to preset's (a reply suffix -> preset, Reply* -> Preset* where preset's file has that name); the header comment rewritten and the two free-contract theorems (afree_realizes_cf_rh_replyB_rc / _all, which compose with the WrapFree walk) left out; facts preset already states are cited (relro_seg); no image numeral in the file. *)
(* omx-clap-core/fuzz_preset's DEALLOCATE INSTANCE at image B' (fuzz_preset.asan-ubsan, pin d663f82d7f48), in the
   PRIMED form: a secondary free re-hides the dead map's shadow.
   rule 24: no function proved (kind: statement text; the composition of the cf layer's primed free instance at
   preset's image B', its unit facts and rows, and the relocated arms).
   Export: adealloc_realizes_raw_cf_em_m_rh_preset : Deallocate's primed raw contract at the call-site relation
   ARXq_cf TfibB IOK_preset, from the layer's primed top YGcfInstFreeTopRh.adealloc_realizes_raw_cf_em_m_rh_cf at
   ARXr := YGcfInstDrainR.ARXr_cf TfibB IOK_preset, L24 := L24MAX_cf, QB := YGcfInstDrainR.QB_cf kQuarantineMax,
   DRq := YGcfInstDrainR.DRq_cf TfibB kQuarantineMax; its image premises from PresetUnitFactsB (FM_INST_OK, IMG_COVER,
   FV_TSD, FV_IAL, FQ_CONST, DZONE_OWNED, IZONE_OWNED, FV_ZONE3, ERRB_APART), ReplyQBBytes (QB_BYTES),
   YGcfInstFreeImgpresetB (FP_IZONE_ROM, FP_DSTAT, FP_DZONE_FP, FP_CONST) and PresetPfApartB (PF_APART); its
   DIfaceExtRh premises from YGcfInstFreeExtB (at kQuarantineMax and at NMAXD_big_cf); its WalkSigDrh premise from
   ReplyWalkSigDrh.walksigdrh_preset with the Enqueue arms YGcfInstEnqMisspreset.enq_arms_cf_preset. No premise is left.
   The free contract (afree_realizes_cf_rh) composes this with the WrapFree walk, which is not relocated here. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase YGcfBatch.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YF0m YF0x. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import CfImgB. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YD2l.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import DeallocG ImgBaseDG DMspec DMiface DGif0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGif2cgif DGif0cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfMallocCompose YGcfMallocComposeE.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfMallocComposeERh YGcfMallocComposeRh.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfInstBase YGcfInstFreeSig.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfInstFreeView YGcfInstFreeQ YGcfInstFreeModel YGcfInstFree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfInstFreePost YGcfInstFreeTopRh.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfDIface YGcfInstDrainR YG0dcfR. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require DGmpcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require PresetUnitFactsB PresetRelroGeoB PresetPfApartB YGcfInstFreeImgpresetB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require YGcfInstFreeExtB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require ReplyWalkSigDrh ReplyQBBytes. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfInstEnq. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require YGcfInstEnqMisspreset YGcfRefillToppreset RepArmTcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require CfAroPresetB.
Import ListNotations.
Local Open Scope Z_scope.

(* reply's allocator parameters (A/CfParamsPreset.v) are the instance of the layer's CfParams in this file *)
#[local] Existing Instance CfParams_preset.
(* reply's image-B constants (B/CfImgB.v) are the instance of the layer's CfImg *)
#[local] Existing Instance CfImg_B.

(* The instance predicate on the allocator instance: reply's one instance object. *)
Definition IOK_preset : Z -> Prop := fun i => i = as_inst TfibB.

Lemma IOK_preset_ok : IOK_ok TfibB IOK_preset.
Proof. intros i H. exact H. Qed.

Section r. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* The unit's three Enqueue arms at the cf relation: CfF1's closed form at reply B (lib/B/YGcfInstEnqMisspreset.v:371 over
   B3LeafCf's refill spec, the class-full arm by the relocated report). *)
Lemma ENQA_preset : forall Hp, YGcfInstEnq.EnqArmsCf TfibB (ARX_cf TfibB IOK_preset Hp).
Proof.
intros Hp.
exact (YGcfInstEnqMisspreset.enq_arms_cf_preset TfibB TfibB_syms IOK_preset Hp IOK_preset_ok CfAroPresetB.relro_seg_preset_AU
  (YGcfRefillToppreset.refill_spec_cf_preset_inst TfibB IOK_preset TfibB_syms IOK_preset_ok
    (@RepArmTcf.classfull_cf_of_hyps fx rc CfParams_preset))).
Qed.

(* reply's Deallocate arms under the re-hide: a prior worker's walksigdrh_preset (lib/B/ReplyWalkSigDrh.v) with its
   hypotheses plugged. *)
Lemma walksigdrh_preset_B : forall Hp,
  WalkSigDrh TfibB (U_cf TfibB) free_cf (ARX_cf TfibB IOK_preset Hp) (aowned TfibB)
    (rpreD_small_cf TfibB) qtight (fpre_hp_cf im_segs TfibB Hp) atp_cf (rpreD_big_cf TfibB)
    (YGcfInstDrainR.ARXr_cf TfibB IOK_preset Hp) (YGcfInstDrainR.DRq_cf TfibB YGcfInstDrainR.NMAXD_big_cf) (DGmpcf.MPcf TfibB).
Proof.
intros Hp.
exact (ReplyWalkSigDrh.walksigdrh_preset IOK_preset (YGcfInstDrainR.DRq_cf TfibB kQuarantineMax) IOK_preset_ok
  ReplyQBBytes.qb_bytes_preset_B
  YGcfInstFreeImgpresetB.FP_IZONE_ROM_TfibB YGcfInstFreeImgpresetB.FP_DSTAT_TfibB YGcfInstFreeImgpresetB.FP_DZONE_FP_TfibB
  YGcfInstFreeImgpresetB.FP_CONST_TfibB PresetPfApartB.pf_apart_preset_B
  (YGcfInstFreeExtB.diface_ext_rh_preset_B IOK_preset IOK_preset_ok) ENQA_preset
  (YGcfInstFreeExtB.diface_ext_rh_preset_B_big IOK_preset IOK_preset_ok) Hp).
Qed.

(* Deallocate's primed raw contract at reply's call-site relation, from the layer's primed free top. *)
Theorem adealloc_realizes_raw_cf_em_m_rh_preset :
  adealloc_realizes_raw_cf_em_m_rh im_segs TfibB atp_cf (ARXq_cf TfibB IOK_preset).
Proof.
pose proof (PresetUnitFactsB.preset_unit_facts_B TfibB TfibB_syms) as UF.
refine (adealloc_realizes_raw_cf_em_m_rh_cf TfibB IOK_preset (YGcfInstDrainR.ARXr_cf TfibB IOK_preset) L24MAX_cf
  (YGcfInstDrainR.QB_cf kQuarantineMax) (YGcfInstDrainR.DRq_cf TfibB kQuarantineMax)
  IOK_preset_ok _ _ _ _ _ ReplyQBBytes.qb_bytes_preset_B _ _ _
  YGcfInstFreeImgpresetB.FP_IZONE_ROM_TfibB YGcfInstFreeImgpresetB.FP_DSTAT_TfibB YGcfInstFreeImgpresetB.FP_DZONE_FP_TfibB
  YGcfInstFreeImgpresetB.FP_CONST_TfibB _ PresetPfApartB.pf_apart_preset_B (YGcfInstFreeExtB.diface_ext_rh_preset_B IOK_preset IOK_preset_ok) walksigdrh_preset_B).

- exact (PresetUnitFactsB.uf_dg_inst_ok _ UF).
- exact (PresetUnitFactsB.uf_IMG_COVER _ UF).
- exact (PresetUnitFactsB.uf_HTSD _ UF).
- exact (PresetUnitFactsB.uf_FV_IAL _ UF).
- exact (PresetUnitFactsB.uf_FQ_CONST _ UF).
- exact (PresetUnitFactsB.uf_DZONE_OWNED _ UF).
- exact (PresetUnitFactsB.uf_IZONE_OWNED _ UF).
- exact (PresetUnitFactsB.uf_FV_ZONE3 _ UF).
- exact (PresetUnitFactsB.uf_ERRB_APART _ UF).
Qed.

End r.
Print Assumptions adealloc_realizes_raw_cf_em_m_rh_preset.
