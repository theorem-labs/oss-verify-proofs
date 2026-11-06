(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/DMdrainTopRh.v (commit 67deba317dfb, blob 0af3e35da866) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb); module paths changed; 0 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1w AFeq AFew AFeu AFey AFgj AFhf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG00cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseDG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AImgA ADIfaceA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import DMspec DMiface DIfaceR MnEnq MnRecycle MnDrain.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import DMwalkIFA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require DMdrainM DMdrainTF DMdrainV0 DMdrainV1 DMsegDA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require MemnormT.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YG0dH YG0dHc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost DIfaceRh.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require DMwalkIFRhA DMdrainTFRh DMdrainUARh DMrecFRh.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section g.
Variable B : asyms.
Variable ARX ARXr : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable L24 : Z.
Variable QB : astate -> Prop.
Variable DRq : astate -> list chunk -> list Z -> Prop.
Variable RMAXD : Z.

Hypothesis QBB : forall X, QB X -> qc_bytes (st_qglobal X) <= 2 ^ 30 /\ qc_bytes (st_qthread X) <= 2 ^ 29.
Hypothesis HL24 : L24 < 2 ^ 40.
Hypothesis HRM : rmaxd_ok RMAXD.

Hypothesis DOK : DMwalkIFRhA.dorecycle_ok_rh_t B ARXr AOX DRq RMAXD.

Theorem drain_m_cf_rh : DMwalkIFRhA.drain_m_cf_rh_t B ARX ARXr AOX L24 QB DRq RMAXD.
Proof.
intros TB DR RCH CDH.
destruct DR as (QV & QO & STK & FRX & FRr & RQX & RQR & RQE & RV).
unfold DIfaceRh.de_drain_m_rh_t, DIfaceRh.drain_spec_g_rh. intros inst ly X W regs mem md PRE.
destruct (Z_le_gt_dec (qc_bytes (DMdrainM.gxf X)) kQuarantineMax) as [HLE|HGT].
-
  eapply DMdrainTFRh.ret_arm_rh; eassumption.
-
  assert (HGT' : kQuarantineMax < AFgj.LBv (st_qglobal X) (st_qthread X)) by (rewrite DMdrainTF.lb_eq; lia).
  unfold cfg_at. rewrite <- (AFhf.wvb_self md) at 1.
  destruct (DMsegDA.merge_test (st_qglobal X) (st_qthread X)) eqn:HMT.
  + eapply amreal'_SRr_pre.
    * apply SRr_SRr'.
      exact (DMdrainV1.merge_to_call B ARX L24 QB TB QV QBB inst ly X W regs mem md (m_vm_materialized md) PRE HGT' HMT).
    * intros W' c' _ (F1 & regs1 & mem1 & gk & P & HIN).
      eapply DMdrainUARh.recyc_tail_rh; eassumption.
  + eapply amreal'_SRr_pre.
    * apply SRr_SRr'.
      exact (DMdrainV0.nomerge_to_call B ARX L24 QB TB QV QBB inst ly X W regs mem md (m_vm_materialized md) PRE HGT' HMT).
    * intros W' c' _ (F1 & regs1 & mem1 & gk & P & HIN).
      eapply DMdrainUARh.recyc_tail_rh; eassumption.
Qed.
End g.

Theorem drain_ok_rh : forall B ARX ARXr AOX L24 QB DRq RMAXD,
DMwalkIFRhA.dorecycle_ok_rh_t B ARXr AOX DRq RMAXD -> DMwalkIFRhA.drain_ok_rh_t B ARX ARXr AOX L24 QB DRq RMAXD.
Proof. intros B ARX ARXr AOX L24 QB DRq RMAXD DOK HRM HL24 QBB. eapply drain_m_cf_rh; eassumption. Qed.

Theorem drain_ok_rh_closed : forall B ARX ARXr AOX L24 QB DRq RMAXD, DMwalkIFRhA.drain_ok_rh_t B ARX ARXr AOX L24 QB DRq RMAXD.
Proof. intros B ARX ARXr AOX L24 QB DRq RMAXD. exact (drain_ok_rh B ARX ARXr AOX L24 QB DRq RMAXD (DMrecFRh.dorecycle_ok_rh B ARXr AOX DRq RMAXD)). Qed.
End f.
