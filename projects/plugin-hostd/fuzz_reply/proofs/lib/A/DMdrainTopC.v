(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DMdrainTopC.v (commit 2a6a4e688066bfacd01258860b3c510ab6da38ad, drain top, CacheDealloc closed; file sha256 03c228236fc2) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* Theorem Labs, 2026-10-30 (lane B1, WalkB1): the lane's top with CacheDealloc CLOSED - DMdrainTop.drain_ok with
   its MnRecycle.de_cdealloc_m_t premise discharged by H3's walk, DMcdF.cdealloc_m_of_reads,
   from H3's read fields DMcdR.cd_reads and the recycle invariant's bookkeeping DMwalkIF.drq_cd, both of which the
   instance discharges (CfF2bRChunk's cd_reads at cf; CfF2b's DRq_cf).  What remains are the instance's facts:
   TfibSyms, the three bounds of DMwalkIF.drain_ok_t, the nine read fields, H4's de_rchunk_m_t (H4's
   rchunk_ok_cf_closed at cf), cd_reads and drq_cd.
   rule 24: proves function __sanitizer::Quarantine::Drain with __sanitizer::QuarantineCache::MergeBatches /
   Recycle / DoRecycle, __asan::QuarantineCallback::Recycle and SizeClassAllocator64LocalCache::Deallocate on the
   real-merge path, frame-generic; the lane's reuse search is LOOKUP-B1-drain.txt (sha256 c6e48b676fd5; internal record), `proof-index
   MergeBatches Recycle QuarantineCallback_Recycle Drain` 2026-10-29T23:07:48Z exit 0, rule-24 check B1LookupCheck
   CONFIRM.
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require DMdrainTop DMcdR DMcdF.
Import ListNotations.
Open Scope Z_scope.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Theorem drain_ok_cd : forall B ARX ARXr AOX L24 QB DRq RMAXD,
rmaxd_ok RMAXD -> L24 < 2 ^ 40 ->
(forall X, QB X -> qc_bytes (st_qglobal X) <= 2 ^ 30 /\ qc_bytes (st_qthread X) <= 2 ^ 29) ->
TfibSyms B -> drain_reads B ARX ARXr AOX L24 QB DRq RMAXD ->
MnRecycle.de_rchunk_m_t B ARXr AOX DRq ->
DMcdR.cd_reads B ARXr AOX DRq RMAXD -> drq_cd DRq RMAXD ->
MnDrain.de_drain_m_t B ARX AOX drain_body_cf L24 QB.
Proof.
intros B ARX ARXr AOX L24 QB DRq RMAXD HRM HL24 QBB TB DR RCH CR DQ.
exact (DMdrainTop.drain_ok B ARX ARXr AOX L24 QB DRq RMAXD HRM HL24 QBB TB DR RCH
  (DMcdF.cdealloc_m_of_reads B ARXr AOX DRq RMAXD TB HRM CR DQ)).
Qed.
End f.
Print Assumptions drain_ok_cd.
