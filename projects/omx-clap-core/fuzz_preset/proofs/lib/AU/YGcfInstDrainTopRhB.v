(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the primed drain field at fuzz_preset image B' (fuzz_preset.asan-ubsan, pin d663f82d7f48), closed.
   YGcfInstDrainTopRh.ds_drain_rh_cf at preset's instance: B := YD2l.TfibB, IOK := the binary's own allocator object,
   CfImgB.CfImg_B, CfParamsPreset.CfParams_preset, and AImg_cgif / DImg_cgif (preset's B' image instance, lib/AU) by
   instance search.  Each of its named premises is discharged by a B' fact:
   - IOK_ok: by its definition;
   - im_syms and TfibSyms: YD2l.TfibB_syms (AImg_cgif's im_syms is TfibSyms);
   - ERRB_QAPART: PresetImg_errbqapart.ERRB_QAPART_B;
   - the four drain-view fields: YGcfInstFreeQ.di_qview_cf / di_qowned_cf and YGcfInstFreeModel.di_frame_cf /
     di_stack_cf, with their premises DMrcCf.img_cover_preset, YF0m.ts_tsd, PresetImg_fqconst.FQ_CONST_B and [QB_BYTES_B];
   - REC_LE: YGcfInstDrainTopRh.rec_le_preset.
   rule 24: no function proved (kind: interface-instance discharge at one image). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0s YK0i YP0m YP0e YP09 YP0l YP06 YO0d YK08.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YI04 YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0k YG0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YGcfTok YG03cf YG03dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YF0m YD2l.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase ImgBaseDG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGif2cgif DGif0cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require CfImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import DMspec DMiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfBatch YGcfImgRows.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfInstBase YGcfInstDrainR.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfDIface YGcfInstFreeView YGcfInstFreeQ YGcfInstFreeModel.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require DIfaceRh YGcfInstDrainTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require PresetImg_errbqapart PresetImg_fqconst DMrcCf YGcfInstDrainTopRh.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section B. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Existing Instance CfImgB.CfImg_B.
#[local] Existing Instance CfParamsPreset.CfParams_preset.

(* The unit's instance object: the binary's own allocator object. *)
Definition IOK_B : Z -> Prop := fun i => i = as_inst YD2l.TfibB.

Lemma IOK_ok_B : IOK_ok YD2l.TfibB IOK_B.
Proof. intros i H. exact H. Qed.

(* The drain's byte premise in the form the queue view takes, from the two byte bounds of QB_cf at kQuarantineMax. *)
Lemma QB_BYTES_B : YGcfInstFreeQ.QB_BYTES (YGcfInstDrainR.QB_cf kQuarantineMax).
Proof.
intros X H. destruct (YGcfInstDrainTop.QBB_of_QB_cf X H) as [H1 H2]. lia.
Qed.

Theorem ds_drain_rh_cf_B : forall Hp : list Z,
  DIfaceRh.de_drain_m_rh_t YD2l.TfibB (ARX_cf YD2l.TfibB IOK_B Hp) (aowned YD2l.TfibB) drain_body_cf L24MAX_cf
    (YGcfInstDrainR.QB_cf kQuarantineMax).
Proof.
intros Hp.
apply (YGcfInstDrainTopRh.ds_drain_rh_cf YD2l.TfibB IOK_B Hp).
- exact IOK_ok_B.
- exact YD2l.TfibB_syms.
- exact YD2l.TfibB_syms.
- exact PresetImg_errbqapart.ERRB_QAPART_B.
- exact (YGcfInstFreeQ.di_qview_cf YD2l.TfibB IOK_B Hp L24MAX_cf (YGcfInstDrainR.QB_cf kQuarantineMax) IOK_ok_B
    DMrcCf.img_cover_preset (YF0m.ts_tsd _ YD2l.TfibB_syms) (PresetImg_fqconst.FQ_CONST_B YD2l.TfibB YD2l.TfibB_syms)
    QB_BYTES_B).
- exact (YGcfInstFreeQ.di_qowned_cf YD2l.TfibB IOK_B Hp L24MAX_cf (YGcfInstDrainR.QB_cf kQuarantineMax) IOK_ok_B).
- exact (YGcfInstFreeModel.di_stack_cf YD2l.TfibB IOK_B Hp).
- exact (YGcfInstFreeModel.di_frame_cf YD2l.TfibB IOK_B Hp).
- exact YGcfInstDrainTopRh.rec_le_preset.
Qed.

End B.
Print Assumptions ds_drain_rh_cf_B.
