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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BArr BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BakeStackRep FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_FKit LbB_Own.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_MILB LbB_DiagStmt LbB_DStat LbB_DRep LbB_DKit LbB_DKitN.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_DCtorK LbB_DCtor LbB_DPdK LbB_DPd.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_PrsStmt LbB_TablStmt LbB_SnStmt LbB_SnV.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_SnK LbB_SnW LbB_SnFind LbB_SnTA LbB_SnTB LbB_SnA LbB_SnF LbB_SnAb LbB_SnFb LbB_SnQ LbB_Sn.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_SnXD LbB_SnXK LbB_SnXI.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_SnXT LbB_SnB LbB_SnD.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_PqS LbB_DtS LbB_NPut.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_SnXO1 LbB_SnXO2 LbB_SnXQ1 LbB_SnXQ2 LbB_SnXC1 LbB_SnXC2 LbB_SnXS1 LbB_SnXS2.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_SnXP1 LbB_SnXP2 LbB_SnXR1 LbB_SnXR2 LbB_SnXE1 LbB_SnXE2.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Theorem setnum_okA {HCEIL : HeapCeil} : forall (H : asr), asan_rt_hyps_bp H -> RtB_Td.td_law H -> setnum_stmtA H LINV_P5.
Proof.
  intros H HHbp HTD ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc msF m mo s LB LF CH
         lo B shi errv this po tid pcons icount bl bc ents
         PRE LOs LFs BS3 BC3 BL3 PFs Ha0 Ha1 Ha2 TIDR THob THI THC1 THC2 HIC PCob PCI PCC PC16 UM USH KINDS POob POin POW DISJ.
  destruct PRE as (VIS & FZ & RH & KR & OWN & LBS & LBC & LBL & RAUX & SPB & BB & SP16 & STK & CEIL & LO & ERRN & MI & TP & RA2 & LV
                   & AC & RFS & LFn & S0 & SPS & CHN & PF & CHsp & TRok & COST).
  pose proof THob as (THA & TH8 & THfs & TH0 & TH47 & THsp & THO).
  pose proof PCob as (PCA & PC8 & PCfs & PC0 & PC47 & PCsp & PCO).
  pose proof POob as (DSA & DS8 & DSfs & DS0 & DS47 & DSsp & DSO).
  pose proof (rt_bp_base H HHbp) as HHb.
  destruct (LbB_DCtor.inframe_facts H HHb LF m po 20 RFS POin ltac:(clear; lia) (proj1 DSO)) as (DSH & DSV & _ & _).
  assert (SPHI : bv_unsigned sp <= AAPP_HI) by (pose proof (stack0_bounds m lo shi S0); lia).
  assert (SPOBJ : forall O n, O = po /\ n = 20 \/ O = pcons /\ n = 48 \/ O = this /\ n = 288 ->
                  O + n <= bv_unsigned sp - ADS_STACK \/ bv_unsigned sp <= O).
  { intros O n [[-> ->] | [[-> ->] | [-> ->]]]; assumption. }
  assert (LFn' : (length LF < AFS_MAXLIVE_BP)%nat) by (unfold DS_FRAMES in LFn; lia).
  pose proof (ah_thr H HHb s LB m RH) as THR.
  assert (UBL : forall A n, In (A, n) (lbl LB) -> ablock_range H A n).
  { intros A n Hin. destruct (lbl_in_inv LB A n Hin) as [p Hp]. exact (ah_blocks H HHb s LB m (p, A, n) RH Hp). }
  assert (XP : xpre H (LbB_SnB.sn_e H ra sp gp tp s0 s1 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m this po tid pcons icount lo LF bl bc LB
                                    s mo CH B shi)).
  { unfold xpre, LbB_SnB.sn_e, xSP. cbn [x_ra x_sp x_gp x_tp x_s0 x_s1 x_s2 x_s3 x_s4 x_s5 x_s6 x_s7 x_s8 x_s9 x_s10 x_s11 x_F x_fc x_m
                                           x_mo x_s x_LB x_LF x_CH x_this x_pcons x_icount x_po x_tid x_aw x_bl x_bc x_lo x_B x_shi].
    unfold ASX_STACK, SX_FRAMES, SX_COST.
    exact (conj FZ (conj RH (conj BS3 (conj BC3 (conj BL3 (conj RAUX (conj SPB (conj BB (conj SP16 (conj STK (conj CEIL (conj LOs (conj (ex_intro _ errv ERRN) (conj MI (conj TP (conj RA2 (conj LV (conj AC (conj RFS (conj LFs (conj S0 (conj SPS (conj CHN (conj PFs (conj CHsp (conj TRok (conj COST (conj TIDR (conj THob (conj THC1 (conj THC2 (conj HIC (conj PCob (conj PCC (conj PC16 (conj POob (conj POin POW))))))))))))))))))))))))))))))))))))). }
  exact (LbB_SnD.sn_all H HHbp ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
           this po tid pcons icount lo LF bl bc LB ents Ha0 Ha1 Ha2 TIDR DSA POW DSO DS8 DSV POin PCA PCO PC8 PCC PCfs DISJ HIC
           THA THO TH8 THfs THC1 THC2 UM USH UBL KINDS STK CEIL LO SP16 SPHI SPOBJ MI AC LV TP RFS LFn' THR s mo CH B shi XP THI PCI
           (LbB_PqS.put_cseq_okA H HHbp) (LbB_NPut.put_u32_ok H HHbp HTD) (LbB_DtS.dtor_okA H HHbp) (LbB_DPd.pdiag0_okA H HHbp) msF errv
           VIS FZ RH KR RAUX ERRN S0).
Qed.
