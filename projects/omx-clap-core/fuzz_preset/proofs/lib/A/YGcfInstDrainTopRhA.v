(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: copied from proofs/omx-clap-core/fuzz_preset/lib/A/YGcfInstDrainTopRhA.v, with its module paths and module names changed. *)
(* Theorem Labs, 2026-10: the primed drain field at fuzz_preset image A', closed.  YGcfInstDrainTopRh.ds_drain_rh_cf
   at preset's instance: B := AD2l.TfibB, IOK := the binary's own allocator object, CfImg_A, CfParams_preset, and
   AImg_A / DImg_A by instance search.  Each of its named premises is discharged by an A' fact:
   - IOK_ok: by its definition;
   - im_syms and TfibSyms: AD2l.TfibB_syms (AImg_A's im_syms is TfibSyms);
   - ERRB_QAPART: CfInstImgA.ERRB_QAPART_A;
   - the four drain-view fields: YGcfInstFreeQ.di_qview_cf / di_qowned_cf and YGcfInstFreeModel.di_frame_cf /
     di_stack_cf, with their premises ADIfaceA.img_cover_A, AF0m.ts_tsd, PresetImg_fqconst.FQ_CONST_A and [QB_BYTES_A];
   - REC_LE: YGcfInstDrainTopRh.rec_le_preset. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0s YK0i YP0m YP0e YP09 YP0l YP06 YO0d YK08.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YI04 YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0k YG0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YGcfTok YG03cf YG03dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AF0m AD2l.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase ImgBaseDG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AImgA ADIfaceA CfImgA CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import DMspec DMiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfBatch YGcfImgRows.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfInstBase YGcfInstDrainR.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfDIface YGcfInstFreeView YGcfInstFreeQ YGcfInstFreeModel.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require DIfaceRh YGcfInstDrainTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfInstImgA PresetImg_fqconst YGcfInstDrainTopRh.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section A. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Existing Instance CfImgA.CfImg_A.
#[local] Existing Instance CfParamsPreset.CfParams_preset.

(* The unit's instance object: the binary's own allocator object. *)
Definition IOK_A : Z -> Prop := fun i => i = as_inst TfibB.

Lemma IOK_ok_A : IOK_ok TfibB IOK_A.
Proof. intros i H. exact H. Qed.

(* The drain's byte premise in the form the queue view takes, from the two byte bounds of QB_cf at kQuarantineMax. *)
Lemma QB_BYTES_A : YGcfInstFreeQ.QB_BYTES (YGcfInstDrainR.QB_cf kQuarantineMax).
Proof.
intros X H. destruct (YGcfInstDrainTop.QBB_of_QB_cf X H) as [H1 H2]. lia.
Qed.

Theorem ds_drain_rh_cf_A : forall Hp : list Z,
  DIfaceRh.de_drain_m_rh_t TfibB (ARX_cf TfibB IOK_A Hp) (aowned TfibB) drain_body_cf L24MAX_cf
    (YGcfInstDrainR.QB_cf kQuarantineMax).
Proof.
intros Hp.
apply (YGcfInstDrainTopRh.ds_drain_rh_cf TfibB IOK_A Hp).
- exact IOK_ok_A.
- exact TfibB_syms.
- exact TfibB_syms.
- exact CfInstImgA.ERRB_QAPART_A.
- exact (YGcfInstFreeQ.di_qview_cf TfibB IOK_A Hp L24MAX_cf (YGcfInstDrainR.QB_cf kQuarantineMax) IOK_ok_A
    img_cover_A (ts_tsd _ TfibB_syms) (PresetImg_fqconst.FQ_CONST_A TfibB TfibB_syms) QB_BYTES_A).
- exact (YGcfInstFreeQ.di_qowned_cf TfibB IOK_A Hp L24MAX_cf (YGcfInstDrainR.QB_cf kQuarantineMax) IOK_ok_A).
- exact (YGcfInstFreeModel.di_stack_cf TfibB IOK_A Hp).
- exact (YGcfInstFreeModel.di_frame_cf TfibB IOK_A Hp).
- exact YGcfInstDrainTopRh.rec_le_preset.
Qed.

End A.
