(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_up.v, with its module paths and module names changed; 264 of its 309 lines of code are new or changed and 2644 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/fuzz_recv_cp.v; 57 of its 96 lines of code are new or changed and 270 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/check_refused.v, with its module names changed; 11 of its 39 lines of code are new or changed and 68 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/check_mark.v, with its module names changed; 55 of its 79 lines of code are new or changed and 15 lines of the source are left out. *)
(* model_read (fuzz_link.asan 0x8642c, listing offset AF_model_read = 0x4260) on image A against its contract
   lib/A/Prog/model_read_c.v `model_read_acontract` (aleaf_rd over the caller's journal), by the walk of
   lib/A/Prog/model_read*.v:
     model_readHead.v  entry .. +0x120 (frame_alloc_1, the frame header and shadow): mr_head
     model_readChk.v   +0x120 .. +0x15c (the guarded NUL stores to kind and alias, the name test): mr_chk
     model_readTail.v  +0x15c .. +0x180 (index_of) and the -ENODEV exit: mr_tail
     model_readRq.v    +0x180 .. +0x208 (checked_memset, the request, talk): mr_rq
     model_readExit.v  +0x208 .. ret (the frame retired): mr_exit_d
   (cut states model_readDefs.v; helpers model_readKit/Str/Call/Wr/Req.v), and the corollary on the image, with the
   runtime callees discharged by their closed lemmas; the two own callees stay hypotheses: index_of (index_of_c.v)
   and talk (talk_c.v).

   Section hypotheses and their discharges on the image:
     ASM1    frame_alloc_1 (0x3da88)      lib/A/AF0s.v stack_malloc1_contract
     HSM1    frame_alloc_1's code entry   AF0m.ts_code, lv_sigma
     AMSET   checked_memset (0x53214)     lib/A/AE2r.v asan_memset_realizes
     IDX     index_of (0x86784)           not proved here (index_of_c.v)
     TALK    talk (0x8763c)               not proved here (talk_c.v)
   and the image instance: LAWS (AR_laws), TL (PALib), LV (LinkVals), TB (AF0m.PcapSyms), HSEGS (pa_segs =
   tfibsegs).

   Proves model_read (kind: function proof). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20 SetShadowDef.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem LinkWalk link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkPi LinkWalkSide.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
index_of_c talk_c model_read_c model_readDefs model_readHead model_readChk.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AB1v AF0m AF0s AE2r.
Import ListNotations.
Open Scope Z_scope.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis LV : LinkVals.
Hypothesis TB : AF0m.PcapSyms B.
Hypothesis HSEGS : SEGS = AB1v.tfibsegs.
Hypothesis ASM1 : astack_malloc_realizes SEGS B 1.
Hypothesis HSM1 : pc_stack_malloc (as_code B) 1 = pa_sigma LS___asan_stack_malloc_1.
Hypothesis AMSET : aintrin_realizes SEGS B OSet (pa_sigma LS___asan_memset).
Hypothesis IDX : forall rlo rhi, index_of_acontract SK SEGS rlo rhi B.
Hypothesis TALK : forall rlo rhi, talk_acontract SK SEGS rlo rhi B.

Theorem model_read_aproof : forall rlo rhi, model_read_acontract SK SEGS rlo rhi B.
Proof using LAWS TL LV TB HSEGS ASM1 HSM1 AMSET IDX TALK.
  intros rlo rhi. unfold model_read_acontract, aleaf_rd.
  intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HPRE HRD HP.
  assert (HENT : MR_ENTRY SK B rlo rhi G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs)
    by (split; [exact HPRE | split; [exact HRD | exact HP]]).
  apply (mr_head SK B LAWS TL LV ASM1 HSM1 rlo rhi G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs
    HENT).
  intros E ms md1 S1 pos HAT.
  exact (mr_chk SK B LAWS TL LV HSEGS TB AMSET IDX TALK rlo rhi G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W
    memc mdc k regs E ms md1 S1 pos HENT HAT).
Qed.

End w.

Section img. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
Context {PI : PAImg link_listing}.
Theorem model_read_aproof_img : forall B, AR_laws pa_segs B -> PALib B -> LinkVals -> AF0m.PcapSyms B ->
  pa_segs = AB1v.tfibsegs ->
  (forall rlo rhi, index_of_acontract SK pa_segs rlo rhi B) ->
  (forall rlo rhi, talk_acontract SK pa_segs rlo rhi B) ->
  forall rlo rhi, model_read_acontract SK pa_segs rlo rhi B.
Proof.
  intros B LAWS TL LV TS Hsegs IDX TALK.
  pose proof LAWS as LAWS'. rewrite Hsegs in LAWS'.
  apply (model_read_aproof SK B LAWS TL LV TS Hsegs).
  - rewrite Hsegs. exact (AF0s.stack_malloc1_contract B LAWS' TS).
  - rewrite (AF0m.ts_code B TS), (lv_sigma LV). reflexivity.
  - (* AE2r.v's statement asks no amem_range of the destination: drop that premise (as model_write.v) *)
    rewrite (lv_sigma LV). cbn [link_sigma]. rewrite Hsegs.
    intros ly S W regs mem md d x n HPRE H10 H11 H12 Hn Hd Hdn HD HAM HRA HHV HOP.
    eapply (AE2r.asan_memset_realizes B LAWS' TS); eassumption.
  - exact IDX.
  - exact TALK.
Qed.
End img.

Print Assumptions model_read_aproof.
Print Assumptions model_read_aproof_img.
