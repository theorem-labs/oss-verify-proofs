(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Conv LbB_SR LbB_FKit LbB_MILB LbB_PrsStmt LbB_PmBase LbB_FSlots LbB_PmOwn LbB_PmCut LbB_PmTac LbB_PmHdr.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require TablRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_SR LbB_Conv LbB_MILB LbB_PrsStmt LbB_HKit LbB_HStKit LbB_PmExit LbB_PiStmt LbB_PiInit LbB_PmTac.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_ContStmt LbB_RwStm LbB_PmHTK LbB_PmMagRS.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_WoGen LbB_WoDefs LbB_WoKit LbB_WoBP LbB_PmMagK LbB_Own LbB_RwStm LbB_PmMagRS LbB_PmMagW LbB_PmHTK.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BakeStackRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_PmHdr2 LbB_DStat LbB_DiagStmt LbB_PmBMRS.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_PmBMT LbB_PmBMT1.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_PmBMCK.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Section BMC2.
  #[local] Set Default Proof Using "All".
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable ds_repA : list block -> mem -> Z -> Z -> Z -> list block -> Prop.
  Hypothesis DSL : ds_rep_lawsA LINV_P5 ds_repA.
  Hypothesis HCTOR : ds_ctor_stmtA H LINV_P5 ds_repA.
  Hypothesis HCSEQ : put_cseq_stmtA H LINV_P5 ds_repA.
  Hypothesis HDTOR : ds_dtor_stmtA H LINV_P5 ds_repA.
  Hypothesis HU32 : put_u32_stmtA H LINV_P5 ds_repA.
  Hypothesis HTR : pm_tr_ok H.

  Lemma HHbmc2 : asan_rt_hyps H. Proof. exact (proj1 HHbp). Qed.

  Lemma pm_bm_10 : forall e ff fp Q mo0 (b0 b1 b2 b3 : byte), bv_unsigned b0 = 3 -> bv_unsigned b1 <> 2 ->
    bp_kmagf H e ff fp Q mo0 -> bp_mag_at H e ff fp (fun m => mag_bytes H e m b0 b1 b2 b3) Q mo0.
  Proof.
    intros e ff fp Q mo0 b0 b1 b2 b3 E0 E1 KF.
    pose proof (pm_bm_tail H HHbp ds_repA DSL HCTOR HCSEQ HDTOR HU32 HTR e ff fp Q mo0 KF) as KT.
    unfold bp_mag_at, bp_hdr0.
    intros s LB LBs m mo msF R F fc XSc w c VIS RF FZ KR MP HP HI SL SH RC RM WL (PF & HW & HN & R0 & R1 & R2 & R3).
    pose proof (bytes4_x b0 b1 b2 b3) as (XR & X0 & X1 & X2 & X3).
    pose proof (bm_pre_proj _ _ _ _ _ _ _ (mag_pre_of H HHbmc2 e ff fp XSc s LB m R b0 b1 b2 b3 HP HI SH RC RM HW HN R0 R1 R2 R3)) as PRE.
    destruct (bmR_x10_bp R F fc m (ff / 32) (wS1 e) (w_words e) (w_n e) _ PRE ltac:(lia) ltac:(lia)) as (R' & M' & MS & MU & WM & _ & _ & _ & _ & G2 & _ & _ & _ & _ & _ & G18 & G19 & G20 & _ & _ & KEEP).
    eapply (sr_msteps H HHbmc2 s msF mo R F (wz (0xea7c4 + 4784)) fc m R' (wz (0xea7c4 + 4812)) M' Q KR); [rewrite VIS; reflexivity | exact RF | exact MS |].
    intros msF1 mo1 KR1 MP1 VIS1 RF1.
    exact (tail_of_post H HHbmc2 e ff fp Q mo0 s LB LBs m mo R F fc XSc w c msF1 mo1 R' M' FZ MP HP HI SL SH RC RM WL PF HW HN
             KR1 MP1 VIS1 RF1 MS MU WM G2 G18 G19 G20 KEEP KT).
  Qed.

  Lemma pm_bm_20 : forall e ff fp Q mo0 (b0 b1 b2 b3 : byte), bv_unsigned b0 = 3 -> bv_unsigned b1 = 2 -> bv_unsigned b2 <> 35 ->
    bp_kmagf H e ff fp Q mo0 -> bp_mag_at H e ff fp (fun m => mag_bytes H e m b0 b1 b2 b3) Q mo0.
  Proof.
    intros e ff fp Q mo0 b0 b1 b2 b3 E0 E1 E2 KF.
    pose proof (pm_bm_tail H HHbp ds_repA DSL HCTOR HCSEQ HDTOR HU32 HTR e ff fp Q mo0 KF) as KT.
    unfold bp_mag_at, bp_hdr0.
    intros s LB LBs m mo msF R F fc XSc w c VIS RF FZ KR MP HP HI SL SH RC RM WL (PF & HW & HN & R0 & R1 & R2 & R3).
    pose proof (bytes4_x b0 b1 b2 b3) as (XR & X0 & X1 & X2 & X3).
    pose proof (bm_pre_proj _ _ _ _ _ _ _ (mag_pre_of H HHbmc2 e ff fp XSc s LB m R b0 b1 b2 b3 HP HI SH RC RM HW HN R0 R1 R2 R3)) as PRE.
    destruct (bmR_x20_bp R F fc m (ff / 32) (wS1 e) (w_words e) (w_n e) _ PRE ltac:(lia) ltac:(lia) ltac:(lia)) as (R' & M' & MS & MU & WM & _ & _ & _ & _ & G2 & _ & _ & _ & _ & _ & _ & G18 & G19 & G20 & _ & _ & KEEP).
    eapply (sr_msteps H HHbmc2 s msF mo R F (wz (0xea7c4 + 4784)) fc m R' (wz (0xea7c4 + 4812)) M' Q KR); [rewrite VIS; reflexivity | exact RF | exact MS |].
    intros msF1 mo1 KR1 MP1 VIS1 RF1.
    exact (tail_of_post H HHbmc2 e ff fp Q mo0 s LB LBs m mo R F fc XSc w c msF1 mo1 R' M' FZ MP HP HI SL SH RC RM WL PF HW HN
             KR1 MP1 VIS1 RF1 MS MU WM G2 G18 G19 G20 KEEP KT).
  Qed.

  Lemma pm_bm_30 : forall e ff fp Q mo0 (b0 b1 b2 b3 : byte), bv_unsigned b0 = 3 -> bv_unsigned b1 = 2 -> bv_unsigned b2 = 35 -> bv_unsigned b3 <> 7 ->
    bp_kmagf H e ff fp Q mo0 -> bp_mag_at H e ff fp (fun m => mag_bytes H e m b0 b1 b2 b3) Q mo0.
  Proof.
    intros e ff fp Q mo0 b0 b1 b2 b3 E0 E1 E2 E3 KF.
    pose proof (pm_bm_tail H HHbp ds_repA DSL HCTOR HCSEQ HDTOR HU32 HTR e ff fp Q mo0 KF) as KT.
    unfold bp_mag_at, bp_hdr0.
    intros s LB LBs m mo msF R F fc XSc w c VIS RF FZ KR MP HP HI SL SH RC RM WL (PF & HW & HN & R0 & R1 & R2 & R3).
    pose proof (bytes4_x b0 b1 b2 b3) as (XR & X0 & X1 & X2 & X3).
    pose proof (bm_pre_proj _ _ _ _ _ _ _ (mag_pre_of H HHbmc2 e ff fp XSc s LB m R b0 b1 b2 b3 HP HI SH RC RM HW HN R0 R1 R2 R3)) as PRE.
    destruct (bmR_x30_bp R F fc m (ff / 32) (wS1 e) (w_words e) (w_n e) _ PRE ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (R' & M' & MS & MU & WM & _ & _ & _ & _ & G2 & _ & _ & _ & _ & _ & _ & _ & G18 & G19 & G20 & _ & _ & KEEP).
    eapply (sr_msteps H HHbmc2 s msF mo R F (wz (0xea7c4 + 4784)) fc m R' (wz (0xea7c4 + 4812)) M' Q KR); [rewrite VIS; reflexivity | exact RF | exact MS |].
    intros msF1 mo1 KR1 MP1 VIS1 RF1.
    exact (tail_of_post H HHbmc2 e ff fp Q mo0 s LB LBs m mo R F fc XSc w c msF1 mo1 R' M' FZ MP HP HI SL SH RC RM WL PF HW HN
             KR1 MP1 VIS1 RF1 MS MU WM G2 G18 G19 G20 KEEP KT).
  Qed.
End BMC2.
