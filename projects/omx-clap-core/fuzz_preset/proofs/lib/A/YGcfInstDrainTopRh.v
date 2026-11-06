(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/YGcfInstDrainTopRh.v (commit 67deba317dfb, blob 5ab08e81a647) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb); module paths changed; 0 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them); the drop bound REC_LE at preset's CfParams (cf_rec_drop = 0, CfParamsPreset.v:165) by YGcfRehideAR.preset_rec_drop_le_rh in place of reply's drop law. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0s YK0i YP0m YP0e YP09 YP0l YP06 YO0d YK08.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YI04 YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0k YG0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YGcfTok YG03cf YG03dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AF0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseDG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AImgA ADIfaceA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import DMspec DMiface MnRecycle.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import DMwalkIFA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfBatch YGcfImgRows.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfInstBase YGcfInstDrainR YGcfInstDrainX YGcfInstDrainQ.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require DIfaceRh.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require DMwalkIFRhA DMdrainTopRh DMrecFRh.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfInstDrainTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require YGcfInstDrainImgpreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require DMrcSecCf DMrcCf DMcdF YGcfInstCdReads YGcfInstCdealloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehideAR.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfParamsPreset.
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

Hypothesis IOK_inst : IOK_ok B IOK.
Hypothesis TS : im_syms B.
Hypothesis TB : TfibSyms B.
Hypothesis EAP : ERRB_QAPART.

Hypothesis QV : di_qview_t B ARX L24MAX_cf QB.
Hypothesis QO : di_qowned_t ARX AOX L24MAX_cf QB.
Hypothesis STK : di_stack_t ARX AOX.
Hypothesis FRX : di_frame_t ARX AOX.

Hypothesis RLE : DMrcSecCf.REC_LE.

Theorem ds_drain_rh_cf : DIfaceRh.de_drain_m_rh_t B ARX AOX drain_body_cf L24MAX_cf QB.
Proof.
pose proof (YGcfInstDrainTop.drain_reads_cf B IOK Hp IOK_inst TS YGcfInstDrainImgpreset.SB_CONST_preset_A
  YGcfInstDrainImgpreset.IMG_QAPART_preset_A EAP YGcfInstDrainImgpreset.CONST_APART_preset_A QV QO STK FRX) as DR.
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

Section R. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma rec_le_preset : DMrcSecCf.REC_LE (cp := CfParamsPreset.CfParams_preset).
Proof.
unfold DMrcSecCf.REC_LE. intros MAP LEN H0 HL.
exact (YGcfRehideAR.preset_rec_drop_le_rh MAP LEN H0 HL).
Qed.
End R.
