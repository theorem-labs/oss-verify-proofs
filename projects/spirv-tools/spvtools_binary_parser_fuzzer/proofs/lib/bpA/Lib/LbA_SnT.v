(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HeapCeil.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HMState HMem HCells HArr HExec HLFrame HStep HSysStep TacX CellsX.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import ASegs AsShadow AsConst AsIface AsCXXHeap CXXRep AsStack0 RtA_Iface.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require FakeStackRep FPSteps.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require Import LbA_Kit LbA_Bridge LbA_Call LbA_Conv LbA_SR LbA_FKit LbA_Own.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require Import LbA_MILB LbA_DiagStmt LbA_DStat LbA_DRep LbA_DKit LbA_DKitN.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require LbA_DCtorK LbA_DCtor LbA_DPdK.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require Import LbA_PrsStmt LbA_TablStmt LbA_SnStmt LbA_SnV.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require LbA_SnK LbA_SnW LbA_SnFind LbA_SnTA LbA_SnTB LbA_SnA LbA_SnF LbA_SnAb LbA_SnFb LbA_SnQ LbA_Sn.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require Import LbA_SnXD LbA_SnXK LbA_SnXI.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require LbA_SnXT LbA_SnB LbA_SnD.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require LbA_PqS LbA_DtS LbA_NPut.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require LbA_SnXO1 LbA_SnXO2 LbA_SnXQ1 LbA_SnXQ2 LbA_SnXC1 LbA_SnXC2 LbA_SnXS1 LbA_SnXS2.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require LbA_SnXP1 LbA_SnXP2 LbA_SnXR1 LbA_SnXR2 LbA_SnXE1 LbA_SnXE2.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Theorem setnum_okA {HCEIL : HeapCeil} : forall (H : asr), asan_rt_hyps_bp H -> RtA_Td.td_law H -> setnum_stmtA H LINV_P5.
Proof.
  intros H HHbp HTD ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc msF m mo s LB LF CH
         lo B shi errv this po tid pcons icount bl bc ents
         PRE LOs LFs BS3 BC3 BL3 PFs Ha0 Ha1 Ha2 TIDR THob THI THC1 THC2 HIC PCob PCI PCC UM USH POob POin POW DISJ.
  destruct PRE as (VIS & FZ & RH & KR & OWN & LBS & LBC & LBL & RAUX & SPB & BB & SP16 & STK & CEIL & LO & ERRN & MI & TP & RA2 & LV
                   & AC & RFS & LFn & S0 & SPS & CHN & PF & CHsp & TRok & COST).
  pose proof THob as (THA & TH8 & THfs & TH0 & TH47 & THsp & THO).
  pose proof PCob as (PCA & PC8 & PCfs & PC0 & PC47 & PCsp & PCO).
  pose proof POob as (DSA & DS8 & DSfs & DS0 & DS47 & DSsp & DSO).
  pose proof (rt_bp_base H HHbp) as HHb.
  destruct (LbA_DCtor.inframe_facts H HHb LF m po 20 RFS POin ltac:(clear; lia) (proj1 DSO)) as (DSH & DSV & _ & _).
  assert (SPHI : bv_unsigned sp <= AAPP_HI) by (pose proof (stack0_bounds m lo shi S0); lia).
  assert (SPOBJ : forall O n, O = po /\ n = 20 \/ O = pcons /\ n = 48 \/ O = this /\ n = 288 ->
                  O + n <= bv_unsigned sp - ADS_STACK \/ bv_unsigned sp <= O).
  { intros O n [[-> ->] | [[-> ->] | [-> ->]]]; assumption. }
  assert (LFn' : (length LF < AFS_MAXLIVE_BP)%nat) by (unfold DS_FRAMES in LFn; lia).
  pose proof (ah_thr H HHb s LB m RH) as THR.
  assert (UBL : forall A n, In (A, n) (lbl LB) -> ablock_range H A n).
  { intros A n Hin. destruct (lbl_in_inv LB A n Hin) as [p Hp]. exact (ah_blocks H HHb s LB m (p, A, n) RH Hp). }
  assert (XP : xpre H (LbA_SnB.sn_e H ra sp gp tp s0 s1 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m this po tid pcons icount lo LF bl bc LB
                                    s mo CH B shi)).
  { unfold xpre, LbA_SnB.sn_e, xSP. cbn [x_ra x_sp x_gp x_tp x_s0 x_s1 x_s2 x_s3 x_s4 x_s5 x_s6 x_s7 x_s8 x_s9 x_s10 x_s11 x_F x_fc x_m
                                           x_mo x_s x_LB x_LF x_CH x_this x_pcons x_icount x_po x_tid x_aw x_bl x_bc x_lo x_B x_shi].
    unfold ASX_STACK, SX_FRAMES, SX_COST.
    exact (conj FZ (conj RH (conj BS3 (conj BC3 (conj BL3 (conj RAUX (conj SPB (conj BB (conj SP16 (conj STK (conj CEIL (conj LOs (conj (ex_intro _ errv ERRN) (conj MI (conj TP (conj RA2 (conj LV (conj AC (conj RFS (conj LFs (conj S0 (conj SPS (conj CHN (conj PFs (conj CHsp (conj TRok (conj COST (conj TIDR (conj THob (conj THC1 (conj THC2 (conj HIC (conj PCob (conj PCC (conj POob (conj POin POW)))))))))))))))))))))))))))))))))))). }
  exact (LbA_SnD.sn_all H HHbp ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
           this po tid pcons icount lo LF bl bc LB ents Ha0 Ha1 Ha2 TIDR DSA POW DSO DS8 DSV POin PCA PCO PC8 PCC PCfs DISJ HIC
           THA THO TH8 THfs THC1 THC2 UM USH UBL STK CEIL LO SP16 SPHI SPOBJ MI AC LV TP RFS LFn' THR s mo CH B shi XP THI PCI
           (LbA_PqS.put_cseq_okA H HHbp) (LbA_NPut.put_u32_ok H HHbp HTD) (LbA_DtS.dtor_okA H HHbp) msF errv
           VIS FZ RH KR RAUX ERRN S0).
Qed.
