(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMdrainTop.v (commit 67fc7ef5787c2195464dbe4d4f7905278328dc0c, drain recycle tail and top; file sha256 9a622ff4a1a9) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 0 image addresses moved by code-verified function pairs (0 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py), and 1 pcs named in comments; no other numeral changed. *)
(* Theorem Labs, 2026-10-30 (lane B1, WalkB1): the lane's TOP - DMwalkIF.drain_m_cf_t (DMwalkIF.v:530-533),
   Quarantine::Drain (0x337ec) with the REAL MergeBatches over the shared model's drain tree drain_body_cf, in
   MnDrain.de_drain_m_t's form (DIfaceR.drain_spec_g with MnEnq.acall_raw_em_x), frame-generic over the
   opaque relations ARX / ARXr / AOX / DRq.  The model's first cut (DMdrainM.drain_body_cf_unfold) splits the
   drain into three arms, each already proved:
   - the RETURN arm, the transferred quarantine within kQuarantineMax: DMdrainTF.ret_arm;
   - the NO-MERGE recycle arm (Recycle's merge test false): DMdrainV0.nomerge_to_call to the shared tail's
     input DMdrainU9.recyc_cut_in, then DMdrainUA.recyc_tail;
   - the MERGE recycle arm (merge test true): a Theorem Labs lane's DMdrainV1.merge_to_call to the same input, then
     the same tail.
   The premises beyond drain_m_cf_t's own are instance-side and named: QB's two byte bounds [QBB] (at the
   shared instance DMdrainG4.QBB_of_QB_cf with NMAXD = kQuarantineMax = 2 ^ 28), the batch bound L24 < 2 ^ 40,
   and rmaxd_ok RMAXD (H2's DoRecycle walk takes it); [drain_ok] states them inside the contract
   (DMwalkIF.drain_ok_t).  No memnorm instance fact: every word the drain writes is mn_safe at the image
   (DMdrainMN); the earlier MemnormT.mn_owned_wr premise was false at the shared instance (MemnormT.v:28-31).
   rule 24: proves function __sanitizer::Quarantine::Drain with __sanitizer::QuarantineCache::MergeBatches /
   Recycle / DoRecycle and __asan::QuarantineCallback::Recycle on the real-merge path, frame-generic; the
   lane's reuse search is LOOKUP-B1-drain.txt (sha256 c6e48b676fd5; internal record), `proof-index MergeBatches Recycle
   QuarantineCallback_Recycle Drain` 2026-10-29T23:07:48Z exit 0, rule-24 check B1LookupCheck CONFIRM.
   Additive: no existing file is touched. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1w AFeq AFew AFeu AFey AFgj AFhf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames YG00cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ImgBaseDG AGif2reply DGif0reply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import DMspec DMiface DIfaceR MnEnq MnRecycle MnDrain DMwalkIF.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require DMdrainM DMdrainTF DMdrainV0 DMdrainV1 DMdrainUA DMsegD MemnormT.
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

Theorem drain_m_cf : DMwalkIF.drain_m_cf_t B ARX ARXr AOX L24 QB DRq RMAXD.
Proof.
intros TB DR RCH CDH.
destruct DR as (QV & QO & STK & FRX & FRr & RQX & RQR & RQE & RV).
unfold MnDrain.de_drain_m_t. intros inst ly X W regs mem md PRE.
destruct (Z_le_gt_dec (qc_bytes (DMdrainM.gxf X)) kQuarantineMax) as [HLE|HGT].
- (* the return arm *)
  eapply DMdrainTF.ret_arm; eassumption.
- (* the recycle arms: each reaches the shared tail's input, then the tail *)
  assert (HGT' : kQuarantineMax < AFgj.LBv (st_qglobal X) (st_qthread X)) by (rewrite DMdrainTF.lb_eq; lia).
  unfold cfg_at. rewrite <- (AFhf.wvb_self md) at 1.
  destruct (DMsegD.merge_test (st_qglobal X) (st_qthread X)) eqn:HMT.
  + eapply YG0d.amreal_SRr_pre.
    * exact (DMdrainV1.merge_to_call B ARX L24 QB TB QV QBB inst ly X W regs mem md (m_vm_materialized md) PRE HGT' HMT).
    * intros W' c' _ (F1 & regs1 & mem1 & gk & P & HIN).
      eapply DMdrainUA.recyc_tail; eassumption.
  + eapply YG0d.amreal_SRr_pre.
    * exact (DMdrainV0.nomerge_to_call B ARX L24 QB TB QV QBB inst ly X W regs mem md (m_vm_materialized md) PRE HGT' HMT).
    * intros W' c' _ (F1 & regs1 & mem1 & gk & P & HIN).
      eapply DMdrainUA.recyc_tail; eassumption.
Qed.
End g.

(* The same with the instance premises inside the contract (DMwalkIF.drain_ok_t), the form a seam takes. *)
Theorem drain_ok : forall B ARX ARXr AOX L24 QB DRq RMAXD, DMwalkIF.drain_ok_t B ARX ARXr AOX L24 QB DRq RMAXD.
Proof. intros B ARX ARXr AOX L24 QB DRq RMAXD HRM HL24 QBB. eapply drain_m_cf; eassumption. Qed.
End f.
Print Assumptions drain_m_cf.
Print Assumptions drain_ok.
Print Assumptions DMdrainUA.recyc_tail.
