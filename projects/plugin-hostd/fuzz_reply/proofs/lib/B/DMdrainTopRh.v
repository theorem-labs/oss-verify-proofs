(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMdrainTop.v (commit 67fc7ef5787c2195464dbe4d4f7905278328dc0c, drain recycle tail and top; file sha256 9a622ff4a1a9) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 0 image addresses moved by code-verified function pairs (0 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py), and 1 pcs named in comments; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/DMdrainTop.v, with its module paths and module names changed; 20 of its 67 lines of code are new or changed and 15 lines of the source are left out. *)
(* Theorem Labs, 2026-10-30 (lane F2b, CfF2b): the lib/B twin of lib/A/DMdrainTopRh.v by path (a working branch 67deba317dfb), with lib.A -> lib.B in the Require lines and image B's names (the rows _reply_B, YGcfInstCdeallocB; CfParams_reply stays lib/A/CfParamsReply's, the one record the B files use). *)
(* Theorem Labs, 2026-10-30 (lane F2b, CfF2b; drain-rh split row (b2), route P): the drain walk's top at the re-hide
   relation - DMwalkIFRh.drain_m_cf_rh_t / drain_ok_rh_t, the twins of DMdrainTop.drain_m_cf / drain_ok, over
   amreal' (= amrealG tfibsegs (wle' tfibsegs RZ_cf): a route-P instance of the generic engine at R := wle').  The
   same case split: the return arm is DMdrainTFRh.ret_arm_rh (it recycles nothing); each recycle arm reaches the
   shared tail's input by DMdrainV1.merge_to_call / DMdrainV0.nomerge_to_call (machine segments, lifted by
   YA0nH.SRr_SRr'), then DMdrainUARh.recyc_tail_rh.  DoRecycle's primed contract DMwalkIFRh.dorecycle_ok_rh_t is a
   named premise of drain_m_cf_rh / drain_ok_rh, discharged in drain_ok_rh_closed by row (a)'s
   DMrecFRh.dorecycle_ok_rh (a Theorem Labs lane).  A new file: DMdrainTop.v stays byte-unchanged.
   rule 24: no function proved (kind: one composition of walked segments at the primed contracts). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0o.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YB1q YB1t YF0l YF0m YF0x YFl0 YFl1.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1w YFeq YFew YFeu YFey YFgj YFhf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames YG00cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ImgBaseDG AGif2reply DGif0reply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import DMspec DMiface DIfaceR MnEnq MnRecycle MnDrain DMwalkIF.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require DMdrainM DMdrainTF DMdrainV0 DMdrainV1 DMsegD MemnormT.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH YG0dH YG0dHc.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YGcfRehidePost DIfaceRh DMwalkIFRh DMdrainTFRh DMdrainUARh DMrecFRh.
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

(* With DoRecycle's primed contract discharged by row (a) (a Theorem Labs lane's DMrecFRh.dorecycle_ok_rh), the form of record:
   exactly DMwalkIFRh.drain_ok_rh_t. *)
Theorem drain_ok_rh_closed : forall B ARX ARXr AOX L24 QB DRq RMAXD, DMwalkIFRh.drain_ok_rh_t B ARX ARXr AOX L24 QB DRq RMAXD.
Proof. intros B ARX ARXr AOX L24 QB DRq RMAXD. exact (drain_ok_rh B ARX ARXr AOX L24 QB DRq RMAXD (DMrecFRh.dorecycle_ok_rh B ARXr AOX DRq RMAXD)). Qed.
End f.
