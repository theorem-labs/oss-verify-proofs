(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31: from proofs/plugin-hostd/fuzz_reply/lib/B/DMdrainTopRh.v (commit ce1a656b52b7, file sha256 ea11f65b9986) onto omx-clap-core/fuzz_preset's ASan+UBSan image B' (fuzz_preset.asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43); module paths changed; reply's image-instance names mapped to preset's B' instance (AGif2reply / AImg_reply -> AGif2cgif / AImg_cgif) and its image-row names to preset's (ReplyImg_* -> PresetImg_*, *reply -> *preset); its 0 image numerals moved by symbol from fuzz_reply.asan-ubsan (pin 10ffb5f9202a) to B' (port_addr_check 3d2eee813cce predictions; object addresses written in decimal by the same symbol map), and 0 addresses named in comments; comment references to people and refs dropped; no other numeral changed. *)
(* Theorem Labs, 2026-10-30 (lane F2b, CfF2b): the lib/B twin of lib/A/DMdrainTopRh.v by path (67deba317dfb), with lib.A -> lib.B in the Require lines and image B's names (the rows _reply_B, YGcfInstCdeallocB; CfParams_preset stays lib/A/CfParamsReply's, the one record the B files use). *)
(* Theorem Labs, 2026-10-30 (lane F2b, CfF2b; drain-rh split row (b2), route P): the drain walk's top at the re-hide
   relation - DMwalkIFRh.drain_m_cf_rh_t / drain_ok_rh_t, the twins of DMdrainTop.drain_m_cf / drain_ok, over
   amreal' (= amrealG tfibsegs (wle' tfibsegs RZ_cf): a route-P instance of the generic engine at R := wle').  The
   same case split: the return arm is DMdrainTFRh.ret_arm_rh (it recycles nothing); each recycle arm reaches the
   shared tail's input by DMdrainV1.merge_to_call / DMdrainV0.nomerge_to_call (machine segments, lifted by
   YA0nH.SRr_SRr'), then DMdrainUARh.recyc_tail_rh.  DoRecycle's primed contract DMwalkIFRh.dorecycle_ok_rh_t is a
   named premise of drain_m_cf_rh / drain_ok_rh, discharged in drain_ok_rh_closed by row (a)'s
   DMrecFRh.dorecycle_ok_rh (a prior worker).  A new file: DMdrainTop.v stays byte-unchanged.
   rule 24: no function proved (kind: one composition of walked segments at the primed contracts). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB1q YB1t YF0l YF0m YF0x YFl0 YFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1w YFeq YFew YFeu YFey YFgj YFhf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG00cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseDG. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGif2cgif DGif0cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import DMspec DMiface DIfaceR MnEnq MnRecycle MnDrain. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import DMwalkIF.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require DMdrainM DMdrainTF DMdrainV0 DMdrainV1 DMsegD. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require MemnormT.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YG0dH YG0dHc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost DIfaceRh. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require DMwalkIFRh DMdrainTFRh DMdrainUARh DMrecFRh.
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
(* the instance-side premises *)
Hypothesis QBB : forall X, QB X -> qc_bytes (st_qglobal X) <= 2 ^ 30 /\ qc_bytes (st_qthread X) <= 2 ^ 29.
Hypothesis HL24 : L24 < 2 ^ 40.
Hypothesis HRM : rmaxd_ok RMAXD.
(* DoRecycle's primed contract (row (a)) *)
Hypothesis DOK : DMwalkIFRh.dorecycle_ok_rh_t B ARXr AOX DRq RMAXD.

Theorem drain_m_cf_rh : DMwalkIFRh.drain_m_cf_rh_t B ARX ARXr AOX L24 QB DRq RMAXD.
Proof.
intros TB DR RCH CDH.
destruct DR as (QV & QO & STK & FRX & FRr & RQX & RQR & RQE & RV).
unfold DIfaceRh.de_drain_m_rh_t, DIfaceRh.drain_spec_g_rh. intros inst ly X W regs mem md PRE.
destruct (Z_le_gt_dec (qc_bytes (DMdrainM.gxf X)) kQuarantineMax) as [HLE|HGT].
- (* the return arm *)
  eapply DMdrainTFRh.ret_arm_rh; eassumption.
- (* the recycle arms: each reaches the shared tail's input, then the tail *)
  assert (HGT' : kQuarantineMax < YFgj.LBv (st_qglobal X) (st_qthread X)) by (rewrite DMdrainTF.lb_eq; lia).
  unfold cfg_at. rewrite <- (YFhf.wvb_self md) at 1.
  destruct (DMsegD.merge_test (st_qglobal X) (st_qthread X)) eqn:HMT.
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

(* The same with the instance premises inside the contract (DMwalkIFRh.drain_ok_rh_t), the form a seam takes. *)
Theorem drain_ok_rh : forall B ARX ARXr AOX L24 QB DRq RMAXD,
DMwalkIFRh.dorecycle_ok_rh_t B ARXr AOX DRq RMAXD -> DMwalkIFRh.drain_ok_rh_t B ARX ARXr AOX L24 QB DRq RMAXD.
Proof. intros B ARX ARXr AOX L24 QB DRq RMAXD DOK HRM HL24 QBB. eapply drain_m_cf_rh; eassumption. Qed.

(* With DoRecycle's primed contract discharged by row (a) (a prior worker's DMrecFRh.dorecycle_ok_rh), the form of record:
   exactly DMwalkIFRh.drain_ok_rh_t. *)
Theorem drain_ok_rh_closed : forall B ARX ARXr AOX L24 QB DRq RMAXD, DMwalkIFRh.drain_ok_rh_t B ARX ARXr AOX L24 QB DRq RMAXD.
Proof. intros B ARX ARXr AOX L24 QB DRq RMAXD. exact (drain_ok_rh B ARX ARXr AOX L24 QB DRq RMAXD (DMrecFRh.dorecycle_ok_rh B ARXr AOX DRq RMAXD)). Qed.
End f.
Print Assumptions drain_m_cf_rh.
Print Assumptions drain_ok_rh_closed.
