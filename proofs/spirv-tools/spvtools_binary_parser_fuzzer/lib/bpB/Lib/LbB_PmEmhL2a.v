From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib HRep HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_ContStmt.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_RwImg LbB_RwKit LbB_RwSem LbB_RwStm.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_MILB LbB_PrsStmt LbB_Own LbB_HEmpStmt LbB_DStat.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_PmEmhW.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_PmEmh LbB_PmEmhF LbB_PmEmhI LbB_HEmpStmt.

Section EmhL2a.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.

  Lemma emh_sq_facts : forall spz, spz mod 16 = 0 -> 80 <= spz ->
    spz - 80 <= emh_sq spz /\ emh_sq spz <= spz - 64 /\ emh_sq spz mod 32 = 0.
  Proof. intros spz A B. unfold emh_sq. Z.div_mod_to_equations. lia. Qed.

  Lemma acr_sp : forall LBx SP SP' A n, SP' <= SP -> aclient_range H LBx SP A n -> aclient_range H LBx SP' A n.
  Proof. intros LBx SP SP' A n L [K|K]; [left; lia | right; exact K]. Qed.

  Lemma emp_post_mo : forall ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB0 LF obj bl bc key ents lo B shi m mo mo1 cf,
    as_MPRES H mo mo1 ->
    emp_post H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB0 LF obj bl bc key ents lo B shi m mo1 cf ->
    emp_post H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB0 LF obj bl bc key ents lo B shi m mo cf.
  Proof using HHbp.
    intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB0 LF obj bl bc key ents lo B shi m mo mo1 cf MP0 P.
    destruct P as (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18 & x19 & x20
                   & x21 & x22 & x23 & x24 & x25 & x26 & x27 & VIS & FZ & KR & MP & REST).
    exists x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27.
    split; [exact VIS|]. split; [exact FZ|]. split; [exact KR|].
    split; [exact (ah_mpres_trans H (rt_bp_base H HHbp) _ _ _ MP0 MP) | exact REST].
  Qed.

  Lemma emh_B_to_C : forall I, bv_unsigned (Z_to_bv 64 (emh_entry I + 296)) mod 2 = 0 ->
    emp_stmt H (emh_emp I) -> emh_BC_stmt H I.
  Proof using HHbp.
    intros I EV EMP. unfold emh_BC_stmt.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           F fc msF m mo s LB LB0 LBm LF obj bl bc keyp key ents lo B shi errv.
    intros VIS0 FZ0 HA0 HA1 UM0 US0 PLB PLBm AD0 WR0 MLF OC OD KF0 KA0 SRC0 KLF KM KR ZL BCL
           RH0 KREL0 AL0 SM CNT LG ICMf TR RX0 SPB BB SP16 STK0 CEIL LO ERR0 MI0 TP RA0 AC0 RFS0 LFN RL0 S00 SPH OWN0.
    intros cf SB. destruct cf as [msF1 mo1]. unfold emh_SB in SB.
    destruct SB as (t0' & t1' & t2' & a2' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & errv1 & ff & fp
      & VIS1 & FZ1 & KR1 & MP1 & FR1 & RFS1 & UM1 & US1 & AD1 & WR1 & KF1 & KA1 & TF1 & TA1 & RH1 & OWN1 & RX1
      & STK1 & ERR1 & MI1 & AC1 & S01 & R1 & R2 & R3 & R4 & R5 & R6 & FP1 & WFP1 & WFF1 & WSH1 & XP1).
    cbn [cfg_ms cfg_model] in VIS1, MP1.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2 ^ 64) in SPR.
    assert (LO0 : 0 <= lo) by (destruct STK0 as (K & _); exact K).
    assert (SPL : 80 <= bv_unsigned sp) by (unfold AEMH_STACK, AEMP_STACK, AOPNEW_STACK, AMALLOC_STACK in LO; lia).
    pose proof (emh_sq_facts (bv_unsigned sp) SP16 SPL) as (Q1 & Q2 & Q3).
    assert (SQ : bv_unsigned (Z_to_bv 64 (emh_sq (bv_unsigned sp))) = emh_sq (bv_unsigned sp)) by (apply wz_unsigned; lia).
    pose proof S00 as (g & G1 & G2 & G3 & G4).
    assert (A128 : aceil + 128 <= bv_unsigned sp) by (unfold AEMH_STACK, AEMP_STACK, AOPNEW_STACK, AMALLOC_STACK in LO; lia).
    assert (S47 : bv_unsigned sp <= 2 ^ 47) by (unfold AAPP_HI in G2; lia).
    destruct (emh_place H HHbp LF m LB0 obj (bv_unsigned sp) ff fp RFS0 FR1 MLF A128 S47 SP16)
      as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & PSRC).
    assert (MLF1 : map_live_frame ((1, ff, fp) :: LF) obj).
    { destruct MLF as (f & Hf & Hf1 & Hf2). exists f. split; [right; exact Hf | split; assumption]. }
    assert (SRCk : emp_src H LB0 (bv_unsigned (Z_to_bv 64 (emh_sq (bv_unsigned sp)))) obj keyp 4).
    { rewrite SQ. destruct SRC0 as (C1 & C2 & C3). split; [apply (acr_sp LB0 (bv_unsigned sp)); [lia | exact C1]|].
      split; [apply (acr_sp LB0 (bv_unsigned sp)); [lia | exact C2] | exact C3]. }
    assert (SRCt : emp_src H LB0 (bv_unsigned (Z_to_bv 64 (emh_sq (bv_unsigned sp)))) obj (ff + 32) 8) by (rewrite SQ; exact PSRC).
    assert (TM : (ff + 32) mod 8 = 0) by (clear - P3; Z.div_mod_to_equations; lia).
    assert (SQ16 : bv_unsigned (Z_to_bv 64 (emh_sq (bv_unsigned sp))) mod 16 = 0)
      by (rewrite SQ; clear - Q3; Z.div_mod_to_equations; lia).
    assert (SQB : bv_unsigned (Z_to_bv 64 (emh_sq (bv_unsigned sp))) <= B) by (rewrite SQ; lia).
    assert (SQS : bv_unsigned (Z_to_bv 64 (emh_sq (bv_unsigned sp))) <= shi) by (rewrite SQ; lia).
    assert (SQL : lo <= bv_unsigned (Z_to_bv 64 (emh_sq (bv_unsigned sp))) - AEMP_STACK)
      by (rewrite SQ; unfold AEMH_STACK in LO; lia).
    assert (STKq : stk asegs m1 lo (bv_unsigned (Z_to_bv 64 (emh_sq (bv_unsigned sp))))).
    { rewrite SQ. destruct STK1 as (K1 & K2 & K3). split; [exact K1|]. split; [lia|]. intros x Hx. apply K3. lia. }
    pose proof (rt_bp_base H HHbp) as HHb.
    eapply (ah_mono H HHb).
    - apply (EMP (Z_to_bv 64 (emh_entry I + 296)) (Z_to_bv 64 (emh_sq (bv_unsigned sp))) gp tp t0' t1' t2' sp
                 (Z_to_bv 64 (emh_sq (bv_unsigned sp))) (Z_to_bv 64 obj) (Z_to_bv 64 keyp) a2' (Z_to_bv 64 (ff + 32))
                 a4' a5' a6' a7' (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6'
                 F fc msF1 m1 mo1 s LB LB0 LBm ((1, ff, fp) :: LF) obj bl bc keyp (ff + 32) keyp key ents lo B shi errv1);
        first [assumption | reflexivity].
    - intros c' P. unfold emh_SC. exists m1, ff, fp.
      split; [exact FR1|]. split; [exact STK1|]. split; [exact R1|]. split; [exact R2|]. split; [exact R3|].
      split; [exact R4|]. split; [exact R5|]. split; [exact R6|]. split; [exact FP1|]. split; [exact WFP1|].
      split; [exact WFF1|]. split; [exact WSH1|]. split; [exact XP1|].
      eapply emp_post_mo; [exact MP1 | exact P].
  Qed.
End EmhL2a.
