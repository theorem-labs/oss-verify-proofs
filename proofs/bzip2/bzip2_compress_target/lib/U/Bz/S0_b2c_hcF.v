(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac WalkLib.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require ZBridge.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require SegsS0.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge.Bytes OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib.SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTables. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCStream BzCState. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCBlock BzCDriver. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArrD BzCLemmas1 CmpMem.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut CmpCut0. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpArith. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpSess CmpSessB S0_cmp_ap.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import U0_cmp_prep.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require GlueTac. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpArith2 BzInv S0_b2c_hcA S0_b2c_hcB S0_b2c_hcC.

From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require ZBridge.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require GlueTac. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpArith2 BzInv S0_b2c_hcA S0_b2c_hcB S0_b2c_hcC.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeilTac.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpCut6.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaP.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpSessFast.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpStEq.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require CpsOpen.
Module S0_b2c_hcD.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.PropExec.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge.Bytes OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib.SegsS0.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTables OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCBlock OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCDriver OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmas1 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCut OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCut0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpArith OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpSess OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpSessB OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_cmp_ap.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.U0_cmp_prep.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.GlueTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpArith2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzInv OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_b2c_hcA OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_b2c_hcB OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_b2c_hcC.
 Unset Lia Cache.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeilTac.
Import ListNotations. Local Open Scope bv_scope.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeil.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCut6.   (* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzParams.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpLiaP.   (* [comment removed for export] *)
(* [comment removed for export] *)

Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
   (* [comment removed for export] *)
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
(* [comment removed for export] *)

#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
   (* [comment removed for export] *)
Local Ltac lia ::= CmpLiaC.lia_c.   (* [comment removed for export] *)
   (* [comment removed for export] *)
   (* [comment removed for export] *)
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.   (* [comment removed for export] *)
Local Ltac slia ::= CmpSessFast.slia_sep_fast.   (* [comment removed for export] *)
Local Ltac simpl_arr_sizes ::= CmpFast.sas7_all.   (* [comment removed for export] *)
(* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Section HC.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte).
  Variables (cx : cctx) (g0 : eg) (e0 : est) (z0 : zstrm) (nin : Z) (pl OB : list byte) (p1 p2 sv : word) (lo : Z) (ob on dbza dbzfr : Z).
  Variables (HCXB : cctx -> Z -> eg -> est -> zstrm -> Prop) (CBFACTS : est -> Prop).
  Notation usp := (bv_unsigned sp). Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation A2 := (c_A2 cx). Notation FT := (c_FT cx).
  Notation bz := (c_bz cx). Notation J := (c_J cx).
  Variables (qsp : Z) (j8 : list byte).
  (* [comment removed for export] *)
  Definition hc_sec : Prop :=
    cctx_ok cx /\ cctx_sep cx /\ cctx_img S0C cx /\ hc_lawsB HCXB CBFACTS /\ compressBlock_spec CBFACTS S0C /\
    Z.of_nat (length OB) = on /\ z_in z0 = map bv_unsigned pl /\ pay_condB cx ob on nin pl /\
    z_outr z0 = [] /\ z_avail_out z0 = on /\ (lo + HC_STACK <= usp)%Z /\ (CEIL <= lo)%Z /\ (usp = 16 * qsp)%Z /\ u8ro s0segs m0 nin pl /\
    out_okB S0C cx ob on /\ strm_okB cx usp.
  Hypothesis HS : hc_sec.

  Notation W := (handle_compress_WB cx ob on usp).
  Notation POST := (handle_compress_postB HCXB s0segs S0C cx ob on dbza dbzfr g0 e0 z0 nin pl OB p1 p2 sv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo W m0).
  Definition FRAME : list cell := [CB 8 j8; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  (* [comment removed for export] *)
  Definition kin (z : zstrm) : Z := (z_avail_in z0 - z_avail_in z)%Z.
  (* [comment removed for export] *)
  Definition MEMh (g : eg) (e : est) (z : zstrm) (mc m : word -> option byte) : Prop :=
    rw_cells s0segs m E (EHEAD1 cx g e) /\ rw_cells s0segs m (E + 640) (EHEAD2 cx g e) /\
    u8arr s0segs m (E + 128) (ovb (e_inUse e) (jseg J 128 256) 256) /\
    u8arr s0segs m A2 (zb8 (e_arr2 e) ARR2_SIZE) /\
    rw_cells s0segs m (bz + 5016) (STRMB cx ob on dbza dbzfr z (nin + kin z) p1 p2) /\
    u8arr s0segs m ob (outb (z_outr z) OB) /\ length (outb (z_outr z) OB) = Z.to_nat on /\
    u32arr s0segs m 209272 crc_words /\
    hid (erest S0C cx e sv mc) /\ munch (hc_WlocB cx ob on usp) mc m /\ wmono s0segs mc m /\
    mem_inv s0segs m /\ munch W m0 m /\ wmono s0segs m0 m /\ stk s0segs m lo (usp - 112) /\ rw_cells s0segs m (usp - 112) FRAME.
  (* [comment removed for export] *)
  Definition PUREh (g : eg) (e : est) (z : zstrm) : Prop :=
    HCXB cx on g e z /\ z_in z = map bv_unsigned (skipn (Z.to_nat (kin z)) pl) /\ (0 <= kin z)%Z.

  Ltac prep :=
    let CX := ident:(CX) in let SEP := ident:(SEP) in let IMG := ident:(IMG) in let PLM0 := ident:(PLM0) in let OOK := ident:(OOK) in let SOK := ident:(SOK) in let ALE := ident:(ALE) in let AL1 := ident:(AL1) in let AL2 := ident:(AL2) in let ALF := ident:(ALF) in let ALB := ident:(ALB) in let ALFb := ident:(ALFb) in pose proof HS as HS'; unfold hc_sec in HS';
    cps_destruct HS' as (CX & SEP & IMG & LAWS & CBS & LOB & ZIN & PAY & OUT0 & AOUT0 & STK16 & LO & ALQ & PLM0 & OOK & SOK); apply hid_i in PLM0;
    pose proof OOK as OOK'; unfold out_okB, apart, img_apart in OOK'; cbn [ci_hi S0C] in OOK'; cps_destruct OOK' as (RO1 & RO2 & RO3 & RO4 & SO1 & SO2 & SO3 & SO4 & IO);
    pose proof SOK as SOK'; unfold strm_okB in SOK'; cps_destruct SOK' as (SA1 & SA2 & SA8);
    pose proof CX as CX'; unfold cctx_ok in CX'; cbv zeta in CX';
    bz_ceil; bz_params; unfold ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, IMG_HI3, CEIL in CX';
    cps_destruct CX' as (RE1 & RE2 & RA1 & RA1' & RA2 & RA2' & RFT & RFT' & RBZ & RBZ' & RFB & RFB' & ALE & AL1 & AL2 & ALF & ALB & ALFb & LJ & LJB);
    pose proof SEP as SEP'; unfold cctx_sep, apart in SEP'; cbv zeta in SEP';
    cps_destruct SEP' as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13 & S14 & S15);
    pose proof IMG as IMG'; unfold cctx_img, img_apart in IMG'; cbn [ci_hi S0C] in IMG'; cps_destruct IMG' as (I1 & I2 & I3 & I4 & I5 & I6);
    bz_ceil; bz_params; unfold FTAB_WORDS, ESTATE_SIZE, BZFILE_SIZE, CEIL, HC_STACK, BZF_STRM, BZ_MAX_UNUSED, IMG_LO3, IMG_HI3 in *;
    hide_disj; pose proof crc_words_length as CWL; clear ALE AL1 AL2 ALF ALB ALFb.
  Ltac cbn_est := cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos
         e_nInUse e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf
         e_len e_code e_rfreq e_len_pack est_set_outpos est_set_modes est_set_rl est_rl rl_nblock rl_block rl_inUse rl_crc rl_ch rl_len
         z_in z_avail_in z_outr z_avail_out z_tin_lo z_tin_hi z_tout_lo z_tout_hi fst snd
         BZ_S_OUTPUT BZ_S_INPUT BZ_M_IDLE BZ_M_RUNNING BZ_M_FLUSHING BZ_M_FINISHING].
  Ltac cbn_est_in H := cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos
         e_nInUse e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf
         e_len e_code e_rfreq e_len_pack est_set_outpos est_set_modes est_set_rl est_rl rl_nblock rl_block rl_inUse rl_crc rl_ch rl_len
         z_in z_avail_in z_outr z_avail_out z_tin_lo z_tin_hi z_tout_lo z_tout_hi fst snd
         BZ_S_OUTPUT BZ_S_INPUT BZ_M_IDLE BZ_M_RUNNING BZ_M_FLUSHING BZ_M_FINISHING] in H.
  Ltac openh MEM :=
    let EH1 := ident:(EH1) in let EH2 := ident:(EH2) in let INU := ident:(INU) in let AR2 := ident:(AR2) in let SM := ident:(SM) in let OBM := ident:(OBM) in let LOBn := ident:(LOBn) in let MUL := ident:(MUL) in let MU := ident:(MU) in let ST := ident:(ST) in let FR := ident:(FR) in cps_destruct MEM as (EH1 & EH2 & INU & AR2 & SM & OBM & LOBn & CRC & HID & MUL & WML & MI & MU & WM & ST & FR);
    unfold EHEAD1, EHEAD2 in EH1, EH2; bz_params; unfold STRMB in SM; unfold FRAME in FR;
    cbn_est_in EH1; cbn_est_in EH2; cbn_est_in INU; cbn_est_in AR2; cbn_est_in SM; cbn_est_in OBM; cbn_est_in LOBn;
    unfold handle_compress_WB in MU; unfold hc_WlocB in MUL;
    pose proof (rw_cells_bound _ _ _ _ FR) as FRB; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FRB;
    pose proof (stk_lo_nonneg _ _ _ _ ST) as LONN.
  (* [comment removed for export] *)
  Ltac closeh EH1 EH2 INU AR2 SM OBM LOBn CRC HID MUL WML MI MU WM ST FR :=
    unfold MEMh;
    split; [first [exact EH1 | unfold EHEAD1; cbn_est; try match goal with GA : g_aie _ = true |- _ => rewrite ?GA in EH1; rewrite ?GA end; first [exact EH1 | cells_eq_by EH1]]|];
    split; [first [exact EH2 | unfold EHEAD2; cbn_est; first [exact EH2 | cells_eq_by EH2]]|];
    split; [cbn_est; exact INU|]; split; [cbn_est; exact AR2|];
    split; [first [exact SM | unfold STRMB, kin in *; cbn_est; first [exact SM | cells_eq_by SM]]|];
    split; [cbn_est; exact OBM|]; split; [cbn_est; exact LOBn|]; split; [exact CRC|];
    split; [exact HID|]; split; [exact MUL|]; split; [exact WML|]; split; [exact MI|]; split; [exact MU|]; split; [exact WM|];
    split; [exact ST| exact FR].
  (* [comment removed for export] *)
  Ltac hci_facts HI :=
    let MD := ident:(MD) in let MODES := ident:(MODES) in let STATES := ident:(STATES) in pose proof (HCIB_est_ok _ _ _ _ _ HI) as EOK;
    pose proof (HCIB_avail_out _ _ _ _ _ HI) as (AOR & OLEN); pose proof (HCIB_avail_in _ _ _ _ _ HI) as (AIL & AIR);
    cps_pose (HCIB_mode _ _ _ _ _ HI) as (MD & GA & AIE); pose proof (HCIB_rl _ _ _ _ _ HI) as RLD; pose proof (HCIB_inUse _ _ _ _ _ HI) as DEFI;
    unfold est_ok in EOK; cps_destruct EOK as (BOK1 & BOK2 & FTR & NBR & NZ0 & POSR & MODES & STATES & CHR & LENR & CRCR & CCR & BNO);
    unfold BZ_M_IDLE, BZ_M_RUNNING, BZ_M_FLUSHING, BZ_M_FINISHING, BZ_S_OUTPUT, BZ_S_INPUT in MODES, STATES, MD;
    unfold BZ_MAX_UNUSED in *.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Notation co_loopL := (co_loop ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 cx z0 nin pl OB p1 p2 sv lo ob on dbza dbzfr HCXB CBFACTS qsp j8 HS).

  (* [comment removed for export] *)
  Definition hc_aft (e : est) (z : zstrm) (pout : bool) : est * zstrm * bool * bool :=
    if (e_state_out_pos e <? bw_numZ (e_bw e))%Z then (e, z, pout, true) else
    if ((e_mode e =? BZ_M_FINISHING)%Z && (e_avail_in_expect e =? 0)%Z && isempty_RL_e e)%bool then (e, z, pout, true) else
    let e := hc_prep e in
    if ((e_mode e =? BZ_M_FLUSHING)%Z && (e_avail_in_expect e =? 0)%Z && isempty_RL_e e)%bool then (e, z, pout, true)
    else (e, z, pout, false).
  Lemma hc_out_aft : forall e z pout,
    hc_out e z pout = let '(e1, z1, q1) := copy_output (Z.to_nat (z_avail_out z) + 1)%nat e z pout in hc_aft e1 z1 q1.
  Proof. intros. unfold hc_out, hc_aft. destruct (copy_output _ e z pout) as [[e1 z1] q1]. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma seg_prep : forall (Q : machine_state -> Prop) g e z (pin pout : bool) mc m
      (x1 xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs8 xt3 xt4 xt5 xt6 : word),
    e_state e = BZ_S_OUTPUT -> (bw_numZ (e_bw e) <= e_state_out_pos e)%Z ->
    ((e_mode e =? BZ_M_FINISHING)%Z && (e_avail_in_expect e =? 0)%Z && isempty_RL_e e)%bool = false ->
    PUREh g e z -> MEMh g e z mc m ->
    (forall m' (x1' xt0' xt1' xt2' xa0' xa1' xa3' xa4' xa5' xa6' xa7' xs8' xt3' xt4' xt5' xt6' : word),
        PUREh g (hc_prep e) z -> MEMh g (hc_prep e) z mc m' ->
        evt s0segs Q (MS (mkR x1' (Z_to_bv 64 (usp - 112)) gp tp xt0' xt1' xt2' (Z_to_bv 64 E) (Z_to_bv 64 (Z.b2z pin))
                             xa0' xa1' (Z_to_bv 64 (e_mode e)) xa3' xa4' xa5' xa6' xa7'
                             (Z_to_bv 64 (Z.b2z pout)) (Z_to_bv 64 (E + 128)) (Z_to_bv 64 2) (Z_to_bv 64 255) (Z_to_bv 64 1) (Z_to_bv 64 209272)
                             xs8' (Z_to_bv 64 4) (Z_to_bv 64 (18446744073709551615 - (E + 128))) (Z_to_bv 64 (18446744073709551615 - 209272)) xt3' xt4' xt5' xt6')
                        F (Z_to_bv 64 0x141c0) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR x1 (Z_to_bv 64 (usp - 112)) gp tp xt0 xt1 xt2 (Z_to_bv 64 E) (Z_to_bv 64 (Z.b2z pin))
                         xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                         (Z_to_bv 64 (Z.b2z pout)) (Z_to_bv 64 (E + 128)) (Z_to_bv 64 2) (Z_to_bv 64 255) (Z_to_bv 64 1) (Z_to_bv 64 209272)
                         xs8 (Z_to_bv 64 4) (Z_to_bv 64 (18446744073709551615 - (E + 128))) (Z_to_bv 64 (18446744073709551615 - 209272)) xt3 xt4 xt5 xt6)
                    F (Z_to_bv 64 0x1418c) fc None m (seg_rom s0segs)).
  Proof.
    intros Q g e z pin pout mc m x1 xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs8 xt3 xt4 xt5 xt6 STO NP NF PU MEM KI.
    pose proof (proj1 MEM) as EH1f. pose proof (proj1 (proj2 MEM)) as EH2f. pose proof (proj1 (proj2 (proj2 MEM))) as INUf.
    openh MEM. prep.
    cps_destruct PU as (HX & ZI & KNN). pose proof (hlB_hci _ _ LAWS _ _ _ _ _ HX) as HI. hci_facts HI.
    pose proof (hlB_prep _ _ LAWS cx on g e z HX STO NP NF) as HX'.
    pose proof (b2z_range pout) as BP.
    (* [comment removed for export] *)
    wstep. wstep.
    (* [comment removed for export] *)
    eapply (U0_prep Q cx gp tp F fc CX I1 g e m); [lia | exact EH1f | exact EH2f | exact INUf | exact MI |].
    intros m' a1' a2' a3' a4' EH1' EH2' INU' MI' MUp WMp.
    clear EH1f EH2f INUf EH1 EH2 INU MI.
    transport_after_call s0segs m m' MUp WMp. clear MUp WMp.
    rename EH1' into EH1. rename EH2' into EH2. rename INU' into INU. rename MI' into MI.
    replace (ret_pc (Z_to_bv 64 0x14194)) with (Z_to_bv 64 0x14194) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    unfold EHEAD1, EHEAD2 in EH1, EH2. bz_params.
    unfold prepare_new_block, prepare_new_block_rl in EH1, EH2, INU. cbn_est_in EH1. cbn_est_in EH2. cbn_est_in INU.
    unfold est_set_rl in EH1, EH2, INU. cbn_est_in EH1. cbn_est_in EH2. cbn_est_in INU.
    (* [comment removed for export] *)
    wstep. wstep. wstep.
    (* [comment removed for export] *)
    wstep; if_cases K3; zify_cond_z K3; [|exfalso; clear -K3 MD; lia].
    eapply KI; [unfold PUREh; split; [exact HX'| split; [exact ZI| exact KNN]]
               | unfold hc_prep, prepare_new_block, prepare_new_block_rl; cbn_est; unfold est_set_rl; cbn_est; closeh EH1 EH2 INU AR2 SM OBM LOBn CRC HID MUL WML MI MU WM ST FR].
  Qed.

  (* [comment removed for export] *)
  Lemma seg_aft : forall (Q : machine_state -> Prop) g e z (pin pout itb : bool) mc m
      (x1 xt0 xt1 xt2 xa0 xa4 xa5 xa6 xa7 xs8 xt3 xt4 xt5 xt6 : word),
    e_state e = BZ_S_OUTPUT -> (z_avail_out z = 0 \/ bw_numZ (e_bw e) <= e_state_out_pos e)%Z ->
    PUREh g e z -> MEMh g e z mc m ->
    (forall e1 z1 pout1 m' (x1' xt0' xt1' xt2' xa0' xa1' xa2' xa3' xa4' xa5' xa6' xa7' xs8' xt3' xt4' xt5' xt6' : word),
        hc_aft e z (pout || itb) = (e1, z1, pout1, true) -> PUREh g e1 z1 -> MEMh g e1 z1 mc m' ->
        evt s0segs Q (MS (mkR x1' (Z_to_bv 64 (usp - 112)) gp tp xt0' xt1' xt2' (Z_to_bv 64 E) (Z_to_bv 64 (Z.b2z pin))
                             xa0' xa1' xa2' xa3' xa4' xa5' xa6' xa7'
                             (Z_to_bv 64 (Z.b2z pout1)) (Z_to_bv 64 (E + 128)) (Z_to_bv 64 2) (Z_to_bv 64 255) (Z_to_bv 64 1) (Z_to_bv 64 209272)
                             xs8' (Z_to_bv 64 4) (Z_to_bv 64 (18446744073709551615 - (E + 128))) (Z_to_bv 64 (18446744073709551615 - 209272)) xt3' xt4' xt5' xt6')
                        F (Z_to_bv 64 0x144e0) fc None m' (seg_rom s0segs))) ->
    (forall e1 z1 pout1 m' (x1' xt0' xt1' xt2' xa0' xa1' xa3' xa4' xa5' xa6' xa7' xs8' xt3' xt4' xt5' xt6' : word),
        hc_aft e z (pout || itb) = (e1, z1, pout1, false) -> e_state e1 = BZ_S_INPUT -> PUREh g e1 z1 -> MEMh g e1 z1 mc m' ->
        evt s0segs Q (MS (mkR x1' (Z_to_bv 64 (usp - 112)) gp tp xt0' xt1' xt2' (Z_to_bv 64 E) (Z_to_bv 64 (Z.b2z pin))
                             xa0' xa1' (Z_to_bv 64 (e_mode e1)) xa3' xa4' xa5' xa6' xa7'
                             (Z_to_bv 64 (Z.b2z pout1)) (Z_to_bv 64 (E + 128)) (Z_to_bv 64 2) (Z_to_bv 64 255) (Z_to_bv 64 1) (Z_to_bv 64 209272)
                             xs8' (Z_to_bv 64 4) (Z_to_bv 64 (18446744073709551615 - (E + 128))) (Z_to_bv 64 (18446744073709551615 - 209272)) xt3' xt4' xt5' xt6')
                        F (Z_to_bv 64 0x141c0) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR x1 (Z_to_bv 64 (usp - 112)) gp tp xt0 xt1 xt2 (Z_to_bv 64 E) (Z_to_bv 64 (Z.b2z pin))
                         xa0 (Z_to_bv 64 (Z.b2z itb)) (Z_to_bv 64 (e_state_out_pos e)) (Z_to_bv 64 (bw_numZ (e_bw e))) xa4 xa5 xa6 xa7
                         (Z_to_bv 64 (Z.b2z pout)) (Z_to_bv 64 (E + 128)) (Z_to_bv 64 2) (Z_to_bv 64 255) (Z_to_bv 64 1) (Z_to_bv 64 209272)
                         xs8 (Z_to_bv 64 4) (Z_to_bv 64 (18446744073709551615 - (E + 128))) (Z_to_bv 64 (18446744073709551615 - 209272)) xt3 xt4 xt5 xt6)
                    F (Z_to_bv 64 0x14164) fc None m (seg_rom s0segs)).
  Proof.
    intros Q g e z pin pout itb mc m x1 xt0 xt1 xt2 xa0 xa4 xa5 xa6 xa7 xs8 xt3 xt4 xt5 xt6 STO EXO PU MEM KR KI.
    openh MEM. prep.
    cps_destruct PU as (HX & ZI & KNN). pose proof (hlB_hci _ _ LAWS _ _ _ _ _ HX) as HI. hci_facts HI.
    cps_pose (HCIB_output _ _ _ _ _ HI STO) as (GZ & NZR & ZREL). bz_params.
    pose proof (b2z_range pout) as BP. pose proof (b2z_range itb) as BI.
    (* [comment removed for export] *)
    wstep. rewrite (lor_b2z itb pout), (Bool.orb_comm itb pout).
    (* [comment removed for export] *)
    wstep; if_cases KP; zify_cond_z KP.
    { enter_with (KR e z (pout || itb)); [st_eq| unfold hc_aft; replace (e_state_out_pos e <? bw_numZ (e_bw e))%Z with true by (symmetry; apply Z.ltb_lt; lia); reflexivity
        | unfold PUREh; first [ solve [ split; [ assumption | split; assumption ] ] | tauto ] | closeh EH1 EH2 INU AR2 SM OBM LOBn CRC HID MUL WML MI MU WM ST FR]. }
    assert (T1 : (e_state_out_pos e <? bw_numZ (e_bw e))%Z = false) by (apply Z.ltb_ge; lia).
    (* [comment removed for export] *)
    wstep. rewrite MD. wstep; if_cases KM; zify_cond_z KM; [exfalso; clear -KM; lia|].
    (* [comment removed for export] *)
    wstep. rewrite GA, AIE. bz32. wstep; if_cases KE; zify_cond_z KE.
    { assert (NF : ((e_mode e =? BZ_M_FINISHING)%Z && (e_avail_in_expect e =? 0)%Z && isempty_RL_e e)%bool = false).
      { rewrite AIE. replace (z_avail_in z =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia). rewrite Bool.andb_false_r. reflexivity. }
      enter_with (seg_prep Q g e z pin (pout || itb) mc);
        [ st_eq | exact STO | lia | exact NF | unfold PUREh; first [ solve [ split; [ assumption | split; assumption ] ] | tauto ] | closeh EH1 EH2 INU AR2 SM OBM LOBn CRC HID MUL WML MI MU WM ST FR
        | intros m' x1' xt0' xt1' xt2' xa0' xa1' xa2' xa3' xa4' xa5' xa6' xa7' xt3' xt4' xt5' xt6' PU' MEM';
          enter_with (KI (hc_prep e) z (pout || itb) m');
          [ st_eq
          | unfold hc_aft; rewrite T1; rewrite NF; unfold hc_prep, prepare_new_block; cbn_est; cbn_est;
            rewrite MD; cbn [Z.eqb Pos.eqb BZ_M_FLUSHING andb]; reflexivity
          | reflexivity | exact PU' | exact MEM' ] ]. }
    (* [comment removed for export] *)
    wstep. wstep; if_cases KC; zify_cond_z KC.
    { enter_with (KR e z (pout || itb)); [st_eq| unfold hc_aft; rewrite T1; unfold isempty_RL_e, isempty_RL, est_rl; cbn_est; rewrite MD, AIE, KE;
          cbn [Z.eqb Pos.eqb BZ_M_FINISHING andb]; replace (e_state_in_ch e <? 256)%Z with false by (symmetry; apply Z.ltb_ge; lia); reflexivity
        | unfold PUREh; first [ solve [ split; [ assumption | split; assumption ] ] | tauto ] | closeh EH1 EH2 INU AR2 SM OBM LOBn CRC HID MUL WML MI MU WM ST FR]. }
    (* [comment removed for export] *)
    wstep. wstep; if_cases KL; zify_cond_z KL.
    { enter_with (KR e z (pout || itb)); [st_eq| unfold hc_aft; rewrite T1; unfold isempty_RL_e, isempty_RL, est_rl; cbn_est; rewrite MD, AIE, KE;
          cbn [Z.eqb Pos.eqb BZ_M_FINISHING andb]; replace (e_state_in_ch e <? 256)%Z with true by (symmetry; apply Z.ltb_lt; lia);
          replace (0 <? e_state_in_len e)%Z with false by (symmetry; apply Z.ltb_ge; lia); reflexivity
        | unfold PUREh; first [ solve [ split; [ assumption | split; assumption ] ] | tauto ] | closeh EH1 EH2 INU AR2 SM OBM LOBn CRC HID MUL WML MI MU WM ST FR]. }
    assert (NF : ((e_mode e =? BZ_M_FINISHING)%Z && (e_avail_in_expect e =? 0)%Z && isempty_RL_e e)%bool = false).
    { unfold isempty_RL_e, isempty_RL, est_rl. cbn_est.
      replace (e_state_in_ch e <? 256)%Z with true by (symmetry; apply Z.ltb_lt; lia).
      replace (0 <? e_state_in_len e)%Z with true by (symmetry; apply Z.ltb_lt; lia). cbn [negb andb]. apply Bool.andb_false_r. }
    enter_with (seg_prep Q g e z pin (pout || itb) mc);
      [ st_eq | exact STO | lia | exact NF | unfold PUREh; first [ solve [ split; [ assumption | split; assumption ] ] | tauto ] | closeh EH1 EH2 INU AR2 SM OBM LOBn CRC HID MUL WML MI MU WM ST FR
      | intros m' x1' xt0' xt1' xt2' xa0' xa1' xa2' xa3' xa4' xa5' xa6' xa7' xt3' xt4' xt5' xt6' PU' MEM';
        enter_with (KI (hc_prep e) z (pout || itb) m');
        [ st_eq
        | unfold hc_aft; rewrite T1; rewrite NF; unfold hc_prep, prepare_new_block; cbn_est; cbn_est;
          rewrite MD; cbn [Z.eqb Pos.eqb BZ_M_FLUSHING andb]; reflexivity
        | reflexivity | exact PU' | exact MEM' ] ].
  Qed.

  (* [comment removed for export] *)
  Lemma seg_out : forall (Q : machine_state -> Prop) g e z (pin pout : bool) mc m
      (x1 xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs8 xt3 xt4 xt5 xt6 : word),
    e_state e = BZ_S_OUTPUT -> PUREh g e z -> MEMh g e z mc m ->
    (forall e1 z1 pout1 m' (x1' xt0' xt1' xt2' xa0' xa1' xa2' xa3' xa4' xa5' xa6' xa7' xs8' xt3' xt4' xt5' xt6' : word),
        hc_out e z pout = (e1, z1, pout1, true) -> PUREh g e1 z1 -> MEMh g e1 z1 mc m' ->
        evt s0segs Q (MS (mkR x1' (Z_to_bv 64 (usp - 112)) gp tp xt0' xt1' xt2' (Z_to_bv 64 E) (Z_to_bv 64 (Z.b2z pin))
                             xa0' xa1' xa2' xa3' xa4' xa5' xa6' xa7'
                             (Z_to_bv 64 (Z.b2z pout1)) (Z_to_bv 64 (E + 128)) (Z_to_bv 64 2) (Z_to_bv 64 255) (Z_to_bv 64 1) (Z_to_bv 64 209272)
                             xs8' (Z_to_bv 64 4) (Z_to_bv 64 (18446744073709551615 - (E + 128))) (Z_to_bv 64 (18446744073709551615 - 209272)) xt3' xt4' xt5' xt6')
                        F (Z_to_bv 64 0x144e0) fc None m' (seg_rom s0segs))) ->
    (forall e1 z1 pout1 m' (x1' xt0' xt1' xt2' xa0' xa1' xa3' xa4' xa5' xa6' xa7' xs8' xt3' xt4' xt5' xt6' : word),
        hc_out e z pout = (e1, z1, pout1, false) -> e_state e1 = BZ_S_INPUT -> PUREh g e1 z1 -> MEMh g e1 z1 mc m' ->
        evt s0segs Q (MS (mkR x1' (Z_to_bv 64 (usp - 112)) gp tp xt0' xt1' xt2' (Z_to_bv 64 E) (Z_to_bv 64 (Z.b2z pin))
                             xa0' xa1' (Z_to_bv 64 (e_mode e1)) xa3' xa4' xa5' xa6' xa7'
                             (Z_to_bv 64 (Z.b2z pout1)) (Z_to_bv 64 (E + 128)) (Z_to_bv 64 2) (Z_to_bv 64 255) (Z_to_bv 64 1) (Z_to_bv 64 209272)
                             xs8' (Z_to_bv 64 4) (Z_to_bv 64 (18446744073709551615 - (E + 128))) (Z_to_bv 64 (18446744073709551615 - 209272)) xt3' xt4' xt5' xt6')
                        F (Z_to_bv 64 0x141c0) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR x1 (Z_to_bv 64 (usp - 112)) gp tp xt0 xt1 xt2 (Z_to_bv 64 E) (Z_to_bv 64 (Z.b2z pin))
                         xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                         (Z_to_bv 64 (Z.b2z pout)) (Z_to_bv 64 (E + 128)) (Z_to_bv 64 2) (Z_to_bv 64 255) (Z_to_bv 64 1) (Z_to_bv 64 209272)
                         xs8 (Z_to_bv 64 4) (Z_to_bv 64 (18446744073709551615 - (E + 128))) (Z_to_bv 64 (18446744073709551615 - 209272)) xt3 xt4 xt5 xt6)
                    F (Z_to_bv 64 0x14098) fc None m (seg_rom s0segs)).
  Proof.
    intros Q g e z pin pout mc m x1 xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs8 xt3 xt4 xt5 xt6 STO PU MEM KR KI.
    pose proof MEM as MEM0. pose proof PU as PU0.
    openh MEM. prep.
    cps_destruct PU as (HX & ZI & KNN). pose proof (hlB_hci _ _ LAWS _ _ _ _ _ HX) as HI. hci_facts HI.
    cps_pose (HCIB_output _ _ _ _ _ HI STO) as (GZ & NZR & ZREL). bz_params.
    pose proof (b2z_range pout) as BP.
    assert (LS7 : Z.land (bz + 5016) 7 = 0%Z) by (change 7%Z with (Z.ones 3); rewrite Z.land_ones by lia; exact SA8).
    rewrite hc_out_aft in KR, KI.
    replace (Z.to_nat (z_avail_out z) + 1)%nat with (S (Z.to_nat (z_avail_out z))) in KR, KI by lia.
    (* [comment removed for export] *)
    wstep. rewrite STO. unfold BZ_S_OUTPUT. wstep; if_cases K2; zify_cond_z K2; [exfalso; clear -K2; lia|].
    wstep; if_cases K1; zify_cond_z K1; [exfalso; clear -K1; lia|].
    (* [comment removed for export] *)
    wstep. wstep; notrap. wstep. rewrite LS7. wstep; notrap.
    wstep. wstep. wstep.
    (* [comment removed for export] *)
    wstep; if_cases KA; zify_cond_z KA.
    { rewrite copy_output_S in KR, KI. replace (z_avail_out z =? 0)%Z with true in KR, KI by (symmetry; apply Z.eqb_eq; lia).
      eapply (seg_aft Q g e z pin pout false mc); [exact STO | lia | exact PU0 | closeh EH1 EH2 INU AR2 SM OBM LOBn CRC HID MUL WML MI MU WM ST FR | | ];
        rewrite Bool.orb_false_r; [exact KR | exact KI]. }
    (* [comment removed for export] *)
    wstep; if_cases KG; zify_cond_z KG.
    { rewrite copy_output_S in KR, KI. replace (z_avail_out z =? 0)%Z with false in KR, KI by (symmetry; apply Z.eqb_neq; lia).
      replace (bw_numZ (e_bw e) <=? e_state_out_pos e)%Z with true in KR, KI by (symmetry; apply Z.leb_le; lia).
      eapply (seg_aft Q g e z pin pout false mc); [exact STO | lia | exact PU0 | closeh EH1 EH2 INU AR2 SM OBM LOBn CRC HID MUL WML MI MU WM ST FR | | ];
        rewrite Bool.orb_false_r; [exact KR | exact KI]. }
    (* [comment removed for export] *)
    assert (CT : copy_output (S (Z.to_nat (z_avail_out z))) e z pout = copy_output (S (Z.to_nat (z_avail_out z))) e z true).
    { rewrite !copy_output_S. replace (z_avail_out z =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
      replace (bw_numZ (e_bw e) <=? e_state_out_pos e)%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity. }
    rewrite CT in KR, KI.
    eapply (co_loopL (S (Z.to_nat (z_avail_out z))) Q g e z pout pin mc); [lia | exact STO | lia | lia | exact PU0 | closeh EH1 EH2 INU AR2 SM OBM LOBn CRC HID MUL WML MI MU WM ST FR |].
    intros e' z' m' x1' xt0' xt1' xt2' xa3' xa4' xa5' xa6' xa7' xs7' xt3' xt4' xt5' xt6' CO' ST' EX' PU' MEM'.
    rewrite CO' in KR, KI.
    eapply (seg_aft Q g e' z' pin pout true mc); [exact ST' | exact EX' | exact PU' | exact MEM' | | ].
    - intros e1 z1 pout1 m'' x1'' xt0'' xt1'' xt2'' xa0'' xa1'' xa2'' xa3'' xa4'' xa5'' xa6'' xa7'' xs7'' xt3'' xt4'' xt5'' xt6'' HA PU'' MEM''.
      rewrite Bool.orb_true_r in HA. eapply KR; [exact HA | exact PU'' | exact MEM''].
    - intros e1 z1 pout1 m'' x1'' xt0'' xt1'' xt2'' xa0'' xa1'' xa2'' xa3'' xa4'' xa5'' xa6'' xa7'' xt3'' xt4'' xt5'' xt6'' HA ST'' PU'' MEM''.
      rewrite Bool.orb_true_r in HA. eapply KI; [exact HA | exact ST'' | exact PU'' | exact MEM''].
  Qed.
End HC.

End ACeilS1.
End S0_b2c_hcD.


From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require ZBridge.
Module S0_b2c_hcE.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.PropExec.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge.Bytes OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib.SegsS0.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTables OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCBlock OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCDriver OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmas1 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCut OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCut0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpArith OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpSess OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpSessB OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_cmp_ap.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.GlueTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpArith2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzInv OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_b2c_hcA OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_b2c_hcB OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_b2c_hcC OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_b2c_hcF.S0_b2c_hcD.
 Unset Lia Cache.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeilTac.
Import ListNotations. Local Open Scope bv_scope.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeil.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCut6.   (* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzParams.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpLiaP.   (* [comment removed for export] *)
(* [comment removed for export] *)

Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
   (* [comment removed for export] *)
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
(* [comment removed for export] *)

#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
   (* [comment removed for export] *)
Local Ltac lia ::= CmpLiaC.lia_c.   (* [comment removed for export] *)
   (* [comment removed for export] *)
Local Ltac slia ::= CmpSessFast.slia_sep_fast.   (* [comment removed for export] *)
Local Ltac simpl_arr_sizes ::= CmpFast.sas7_all.   (* [comment removed for export] *)
(* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Section HC.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte).
  Variables (cx : cctx) (g0 : eg) (e0 : est) (z0 : zstrm) (nin : Z) (pl OB : list byte) (p1 p2 sv : word) (lo : Z) (ob on dbza dbzfr : Z).
  Variables (HCXB : cctx -> Z -> eg -> est -> zstrm -> Prop) (CBFACTS : est -> Prop).
  Notation usp := (bv_unsigned sp). Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation A2 := (c_A2 cx). Notation FT := (c_FT cx).
  Notation bz := (c_bz cx). Notation J := (c_J cx).
  Variables (qsp : Z) (j8 : list byte).
  (* [comment removed for export] *)
  Definition hc_sec : Prop :=
    cctx_ok cx /\ cctx_sep cx /\ cctx_img S0C cx /\ hc_lawsB HCXB CBFACTS /\ compressBlock_spec CBFACTS S0C /\
    Z.of_nat (length OB) = on /\ z_in z0 = map bv_unsigned pl /\ pay_condB cx ob on nin pl /\
    z_outr z0 = [] /\ z_avail_out z0 = on /\ (lo + HC_STACK <= usp)%Z /\ (CEIL <= lo)%Z /\ (usp = 16 * qsp)%Z /\ u8ro s0segs m0 nin pl /\
    out_okB S0C cx ob on /\ strm_okB cx usp.
  Hypothesis HS : hc_sec.

  Notation W := (handle_compress_WB cx ob on usp).
  Notation POST := (handle_compress_postB HCXB s0segs S0C cx ob on dbza dbzfr g0 e0 z0 nin pl OB p1 p2 sv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo W m0).
  Definition FRAME : list cell := [CB 8 j8; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  (* [comment removed for export] *)
  Definition kin (z : zstrm) : Z := (z_avail_in z0 - z_avail_in z)%Z.
  (* [comment removed for export] *)
  Definition MEMh (g : eg) (e : est) (z : zstrm) (mc m : word -> option byte) : Prop :=
    rw_cells s0segs m E (EHEAD1 cx g e) /\ rw_cells s0segs m (E + 640) (EHEAD2 cx g e) /\
    u8arr s0segs m (E + 128) (ovb (e_inUse e) (jseg J 128 256) 256) /\
    u8arr s0segs m A2 (zb8 (e_arr2 e) ARR2_SIZE) /\
    rw_cells s0segs m (bz + 5016) (STRMB cx ob on dbza dbzfr z (nin + kin z) p1 p2) /\
    u8arr s0segs m ob (outb (z_outr z) OB) /\ length (outb (z_outr z) OB) = Z.to_nat on /\
    u32arr s0segs m 209272 crc_words /\
    hid (erest S0C cx e sv mc) /\ munch (hc_WlocB cx ob on usp) mc m /\ wmono s0segs mc m /\
    mem_inv s0segs m /\ munch W m0 m /\ wmono s0segs m0 m /\ stk s0segs m lo (usp - 112) /\ rw_cells s0segs m (usp - 112) FRAME.
  (* [comment removed for export] *)
  Definition PUREh (g : eg) (e : est) (z : zstrm) : Prop :=
    HCXB cx on g e z /\ z_in z = map bv_unsigned (skipn (Z.to_nat (kin z)) pl) /\ (0 <= kin z)%Z.

  Ltac prep :=
    let CX := ident:(CX) in let SEP := ident:(SEP) in let IMG := ident:(IMG) in let PLM0 := ident:(PLM0) in let OOK := ident:(OOK) in let SOK := ident:(SOK) in let ALE := ident:(ALE) in let AL1 := ident:(AL1) in let AL2 := ident:(AL2) in let ALF := ident:(ALF) in let ALB := ident:(ALB) in let ALFb := ident:(ALFb) in pose proof HS as HS'; unfold hc_sec in HS';
    cps_destruct HS' as (CX & SEP & IMG & LAWS & CBS & LOB & ZIN & PAY & OUT0 & AOUT0 & STK16 & LO & ALQ & PLM0 & OOK & SOK); apply hid_i in PLM0;
    pose proof OOK as OOK'; unfold out_okB, apart, img_apart in OOK'; cbn [ci_hi S0C] in OOK'; cps_destruct OOK' as (RO1 & RO2 & RO3 & RO4 & SO1 & SO2 & SO3 & SO4 & IO);
    pose proof SOK as SOK'; unfold strm_okB in SOK'; cps_destruct SOK' as (SA1 & SA2 & SA8);
    pose proof CX as CX'; unfold cctx_ok in CX'; cbv zeta in CX';
    bz_ceil; bz_params; unfold ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, IMG_HI3, CEIL in CX';
    cps_destruct CX' as (RE1 & RE2 & RA1 & RA1' & RA2 & RA2' & RFT & RFT' & RBZ & RBZ' & RFB & RFB' & ALE & AL1 & AL2 & ALF & ALB & ALFb & LJ & LJB);
    pose proof SEP as SEP'; unfold cctx_sep, apart in SEP'; cbv zeta in SEP';
    cps_destruct SEP' as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13 & S14 & S15);
    pose proof IMG as IMG'; unfold cctx_img, img_apart in IMG'; cbn [ci_hi S0C] in IMG'; cps_destruct IMG' as (I1 & I2 & I3 & I4 & I5 & I6);
    bz_ceil; bz_params; unfold FTAB_WORDS, ESTATE_SIZE, BZFILE_SIZE, CEIL, HC_STACK, BZF_STRM, BZ_MAX_UNUSED, IMG_LO3, IMG_HI3 in *;
    hide_disj; pose proof crc_words_length as CWL; clear ALE AL1 AL2 ALF ALB ALFb.
  Ltac cbn_est := cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos
         e_nInUse e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf
         e_len e_code e_rfreq e_len_pack est_set_outpos est_set_modes est_set_rl est_rl rl_nblock rl_block rl_inUse rl_crc rl_ch rl_len
         z_in z_avail_in z_outr z_avail_out z_tin_lo z_tin_hi z_tout_lo z_tout_hi fst snd
         BZ_S_OUTPUT BZ_S_INPUT BZ_M_IDLE BZ_M_RUNNING BZ_M_FLUSHING BZ_M_FINISHING].
  Ltac cbn_est_in H := cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos
         e_nInUse e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf
         e_len e_code e_rfreq e_len_pack est_set_outpos est_set_modes est_set_rl est_rl rl_nblock rl_block rl_inUse rl_crc rl_ch rl_len
         z_in z_avail_in z_outr z_avail_out z_tin_lo z_tin_hi z_tout_lo z_tout_hi fst snd
         BZ_S_OUTPUT BZ_S_INPUT BZ_M_IDLE BZ_M_RUNNING BZ_M_FLUSHING BZ_M_FINISHING] in H.
  Ltac openh MEM :=
    let EH1 := ident:(EH1) in let EH2 := ident:(EH2) in let INU := ident:(INU) in let AR2 := ident:(AR2) in let SM := ident:(SM) in let OBM := ident:(OBM) in let LOBn := ident:(LOBn) in let MUL := ident:(MUL) in let MU := ident:(MU) in let ST := ident:(ST) in let FR := ident:(FR) in cps_destruct MEM as (EH1 & EH2 & INU & AR2 & SM & OBM & LOBn & CRC & HID & MUL & WML & MI & MU & WM & ST & FR);
    unfold EHEAD1, EHEAD2 in EH1, EH2; bz_params; unfold STRMB in SM; unfold FRAME in FR;
    cbn_est_in EH1; cbn_est_in EH2; cbn_est_in INU; cbn_est_in AR2; cbn_est_in SM; cbn_est_in OBM; cbn_est_in LOBn;
    unfold handle_compress_WB in MU; unfold hc_WlocB in MUL;
    pose proof (rw_cells_bound _ _ _ _ FR) as FRB; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FRB;
    pose proof (stk_lo_nonneg _ _ _ _ ST) as LONN.
  (* [comment removed for export] *)
  Ltac closeh EH1 EH2 INU AR2 SM OBM LOBn CRC HID MUL WML MI MU WM ST FR :=
    unfold MEMh;
    split; [first [exact EH1 | unfold EHEAD1; cbn_est; try match goal with GA : g_aie _ = true |- _ => rewrite ?GA in EH1; rewrite ?GA end; first [exact EH1 | cells_eq_by EH1]]|];
    split; [first [exact EH2 | unfold EHEAD2; cbn_est; first [exact EH2 | cells_eq_by EH2]]|];
    split; [cbn_est; exact INU|]; split; [cbn_est; exact AR2|];
    split; [first [exact SM | unfold STRMB, kin in *; cbn_est; first [exact SM | cells_eq_by SM]]|];
    split; [cbn_est; exact OBM|]; split; [cbn_est; exact LOBn|]; split; [exact CRC|];
    split; [exact HID|]; split; [exact MUL|]; split; [exact WML|]; split; [exact MI|]; split; [exact MU|]; split; [exact WM|];
    split; [exact ST| exact FR].
  (* [comment removed for export] *)
  Ltac hci_facts HI :=
    let MD := ident:(MD) in let MODES := ident:(MODES) in let STATES := ident:(STATES) in pose proof (HCIB_est_ok _ _ _ _ _ HI) as EOK;
    pose proof (HCIB_avail_out _ _ _ _ _ HI) as (AOR & OLEN); pose proof (HCIB_avail_in _ _ _ _ _ HI) as (AIL & AIR);
    cps_pose (HCIB_mode _ _ _ _ _ HI) as (MD & GA & AIE); pose proof (HCIB_rl _ _ _ _ _ HI) as RLD; pose proof (HCIB_inUse _ _ _ _ _ HI) as DEFI;
    unfold est_ok in EOK; cps_destruct EOK as (BOK1 & BOK2 & FTR & NBR & NZ0 & POSR & MODES & STATES & CHR & LENR & CRCR & CCR & BNO);
    unfold BZ_M_IDLE, BZ_M_RUNNING, BZ_M_FLUSHING, BZ_M_FINISHING, BZ_S_OUTPUT, BZ_S_INPUT in MODES, STATES, MD;
    unfold BZ_MAX_UNUSED in *.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma cb_call : forall (Q : machine_state -> Prop) g e z (is_last : bool) mc m (ret : Z)
      (xt0 xt1 xt2 ws1 xa2 xa3 xa4 xa5 xa6 xa7 ws2 xs8 xt3 xt4 xt5 xt6 : word),
    (0 <= ret < 18446744073709551616)%Z -> (ret mod 2 = 0)%Z ->
    cb_pre g e -> CBFACTS e ->
    MEMh g e z mc m ->
    (forall m' (xt0' xt1' xt2' xa0' xa1' xa2' xa3' xa4' xa5' xa6' xa7' xt3' xt4' xt5' xt6' : word),
        MEMh (eg_after_cb cx g e) (fst (compressBlock e is_last znew)) z m' m' ->
        evt s0segs Q (MS (mkR (Z_to_bv 64 ret) (Z_to_bv 64 (usp - 112)) gp tp xt0' xt1' xt2' (Z_to_bv 64 E) ws1
                             xa0' xa1' xa2' xa3' xa4' xa5' xa6' xa7' ws2 (Z_to_bv 64 (E + 128)) (Z_to_bv 64 2) (Z_to_bv 64 255) (Z_to_bv 64 1) (Z_to_bv 64 209272)
                             xs8 (Z_to_bv 64 4) (Z_to_bv 64 (18446744073709551615 - (E + 128))) (Z_to_bv 64 (18446744073709551615 - 209272)) xt3' xt4' xt5' xt6')
                        F (Z_to_bv 64 ret) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR (Z_to_bv 64 ret) (Z_to_bv 64 (usp - 112)) gp tp xt0 xt1 xt2 (Z_to_bv 64 E) ws1
                         (Z_to_bv 64 E) (Z_to_bv 64 (if is_last then 1 else 0)) xa2 xa3 xa4 xa5 xa6 xa7 ws2 (Z_to_bv 64 (E + 128)) (Z_to_bv 64 2) (Z_to_bv 64 255) (Z_to_bv 64 1) (Z_to_bv 64 209272)
                         xs8 (Z_to_bv 64 4) (Z_to_bv 64 (18446744073709551615 - (E + 128))) (Z_to_bv 64 (18446744073709551615 - 209272)) xt3 xt4 xt5 xt6)
                    F (Z_to_bv 64 0x16344) fc None m (seg_rom s0segs)).
  Proof.
    intros Q g e z is_last mc m ret xt0 xt1 xt2 ws1 xa2 xa3 xa4 xa5 xa6 xa7 ws2 xs8 xt3 xt4 xt5 xt6 RET RET2 PRE FACTS MEM K.
    openh MEM. prep.
    pose proof (erest_transportB S0C cx ob on e sv mc m usp HID MUL WML CX SEP IMG OOK ltac:(bz_ceil; bz_params; unfold CEIL, HC_STACK; lia) SA1 eq_refl) as HIDm.
    pose proof (hid_e _ HIDm) as ER. cps_destruct ER as (UNS & MTF & SEL & SLM & LEN & COD & RFQ & LNP & AR1 & FTB & CM). clear HIDm HID MUL WML.
    pose proof (emem_intro cx s0segs g e m EH1 INU UNS EH2 MTF SEL SLM LEN COD RFQ LNP) as EM.
    pose proof (amem_intro cx s0segs e m AR1 AR2 FTB) as AM.
    clear EH1 INU UNS EH2 MTF SEL SLM LEN COD RFQ LNP AR1 AR2 FTB CRC.
    assert (AL16 : ((usp - 112) mod 16 = 0)%Z).
    { rewrite ALQ. replace (16 * qsp - 112)%Z with (16 * qsp + 16 * (-7))%Z by lia. apply mod16_of_lin. }
    eapply evt_cut.
    { eapply (CBS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m cx g e is_last lo sv);
        [ reflexivity | reflexivity | exact EM | exact AM | exact CM | exact MI
        | cbn [ci_segs S0C]; rewrite unsigned_lit by lia; exact ST
        | rewrite unsigned_lit by lia; unfold CB_STACK; lia | bz_ceil; bz_params; unfold CEIL; lia | rewrite unsigned_lit by lia; exact AL16
        | exact CX | exact SEP | exact IMG | exact PRE | exact FACTS ]. }
    cbn [ci_segs ci_compressBlock S0C]. clear EM AM CM.
    post_callW s0segs m.
    rewrite (ret_pc_even ret) by lia.
    cbv zeta in POST. cps_destruct POST as (EM' & AM' & CM').
    match goal with H : stk _ ?mm _ (bv_unsigned _) |- _ => rename H into ST'; rewrite unsigned_lit in ST' by lia end.
    match goal with H : mem_inv _ ?mm |- _ => rename H into MI' end.
    lazymatch type of MI' with mem_inv _ ?m' =>
      open_emem EM'; open_amem AM';
      pose proof (cimg_crc_u32arr S0C m' sv CM') as CRC; cbn [ci_segs ci_crc S0C] in CRC;
      pose proof (erest_intro S0C cx _ sv m' UNS MTF SEL SLM LEN COD RFQ LNP AR1 FTB CM') as HID';
      pose proof (munch_refl (hc_WlocB cx ob on usp) m') as MUL'; pose proof (wmono_refl s0segs m') as WML'
    end.
    eapply K. closeh EH1 EH2 INU AR2 SM OBM LOBn CRC HID' MUL' WML' MI' MU WM ST' FR.
  Qed.

  (* [comment removed for export] *)
  Lemma fin_tail : forall (Q : machine_state -> Prop) g e z (pin pout : bool) (r1 : rlst) mc m
      (x1 xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs8 xt3 xt4 xt5 xt6 : word),
    e_state e = BZ_S_INPUT -> e_mode e = BZ_M_FINISHING -> e_avail_in_expect e = 0%Z ->
    r1 = (if (e_state_in_ch e <? 256)%Z then add_pair_to_block (est_rl e) else est_rl e) ->
    PUREh g e z -> MEMh g (est_set_rl e r1) z mc m ->
    (forall mc' m' (x1' xt0' xt1' xt2' xa0' xa1' xa2' xa3' xa4' xa5' xa6' xa7' xs8' xt3' xt4' xt5' xt6' : word),
        PUREh (eg_after_cb cx g (hc_flush e)) (hc_cbF e) z -> MEMh (eg_after_cb cx g (hc_flush e)) (hc_cbF e) z mc' m' ->
        evt s0segs Q (MS (mkR x1' (Z_to_bv 64 (usp - 112)) gp tp xt0' xt1' xt2' (Z_to_bv 64 E) (Z_to_bv 64 (Z.b2z pin))
                             xa0' xa1' xa2' xa3' xa4' xa5' xa6' xa7'
                             (Z_to_bv 64 (Z.b2z pout)) (Z_to_bv 64 (E + 128)) (Z_to_bv 64 2) (Z_to_bv 64 255) (Z_to_bv 64 1) (Z_to_bv 64 209272)
                             xs8' (Z_to_bv 64 4) (Z_to_bv 64 (18446744073709551615 - (E + 128))) (Z_to_bv 64 (18446744073709551615 - 209272)) xt3' xt4' xt5' xt6')
                        F (Z_to_bv 64 0x14098) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR x1 (Z_to_bv 64 (usp - 112)) gp tp xt0 xt1 xt2 (Z_to_bv 64 E) (Z_to_bv 64 (Z.b2z pin))
                         xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                         (Z_to_bv 64 (Z.b2z pout)) (Z_to_bv 64 (E + 128)) (Z_to_bv 64 2) (Z_to_bv 64 255) (Z_to_bv 64 1) (Z_to_bv 64 209272)
                         xs8 (Z_to_bv 64 4) (Z_to_bv 64 (18446744073709551615 - (E + 128))) (Z_to_bv 64 (18446744073709551615 - 209272)) xt3 xt4 xt5 xt6)
                    F (Z_to_bv 64 0x144b8) fc None m (seg_rom s0segs)).
  Proof.
    intros Q g e z pin pout r1 mc m x1 xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs8 xt3 xt4 xt5 xt6 STI MF E0 R1 PU MEM KT.
    openh MEM. prep.
    cps_destruct PU as (HX & ZI & KNN). pose proof (hlB_hci _ _ LAWS _ _ _ _ _ HX) as HI. hci_facts HI.
    cps_pose (hlB_cbF _ _ LAWS cx on g e z HX STI E0) as (PRE & FACTS & HX').
    pose proof (b2z_range pout) as BP. pose proof (b2z_range pin) as BI.
    assert (FL : hc_flush e = est_set_rl e (RL (rl_nblock r1) (rl_block r1) (rl_inUse r1) (rl_crc r1) 256 0)).
    { cbn_est_in R1. unfold hc_flush, flush_RL, init_RL. cbn_est. rewrite <- R1. reflexivity. }
    (* [comment removed for export] *)
    wstep. rewrite MF. unfold BZ_M_FINISHING. wstep. wstep. wstep. wstep. wstep; flags.
    (* [comment removed for export] *)
    wstep. wstep.
    change (Z_to_bv 64 1) with (Z_to_bv 64 (if true then 1 else 0)%Z) at 1.
    eapply (cb_call Q g (hc_flush e) z true mc); [lia | reflexivity | exact PRE | exact FACTS | rewrite FL; closeh EH1 EH2 INU AR2 SM OBM LOBn CRC HID MUL WML MI MU WM ST FR |].
    intros m' xt0' xt1' xt2' xa0' xa1' xa2' xa3' xa4' xa5' xa6' xa7' xt3' xt4' xt5' xt6' MEM'.
    clear EH1 EH2 INU AR2 SM OBM LOBn CRC HID MUL WML MI MU WM ST FR FRB LONN.
    openh MEM'. bz_ceil; bz_params; unfold FTAB_WORDS, ESTATE_SIZE, BZFILE_SIZE, CEIL, HC_STACK, BZF_STRM, BZ_MAX_UNUSED in *.
    (* [comment removed for export] *)
    wstep. wstep.
    eapply KT.
    - unfold PUREh. split; [exact HX'|]. split; [exact ZI| exact KNN].
    - unfold hc_cbF. rewrite (surjective_pairing (compressBlock (hc_flush e) _ znew)).
      replace (e_mode (hc_flush e) =? BZ_M_FINISHING)%Z with true by (symmetry; apply Z.eqb_eq; rewrite FL; cbn_est; exact MF).
      closeh EH1 EH2 INU AR2 SM OBM LOBn CRC HID MUL WML MI MU WM ST FR.
  Qed.

End HC.

End ACeilS1.
End S0_b2c_hcE.

Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.GlueTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpArith2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzInv OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_b2c_hcA OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_b2c_hcB OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_b2c_hcC OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_b2c_hcF.S0_b2c_hcD OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_b2c_hcF.S0_b2c_hcE.
From Stdlib Require Lia. Unset Lia Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilTac.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut6.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.   (* [comment removed for export] *)
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.   (* [comment removed for export] *)
Local Ltac lia ::= CmpLiaC.lia_c.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpSessFast.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpStEq.   (* [comment removed for export] *)
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.   (* [comment removed for export] *)
Local Ltac slia ::= CmpSessFast.slia_sep_fast.   (* [comment removed for export] *)
Local Ltac simpl_arr_sizes ::= CmpFast.sas7_all.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Section HC.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte).
  Variables (cx : cctx) (g0 : eg) (e0 : est) (z0 : zstrm) (nin : Z) (pl OB : list byte) (p1 p2 sv : word) (lo : Z) (ob on dbza dbzfr : Z).
  Variables (HCXB : cctx -> Z -> eg -> est -> zstrm -> Prop) (CBFACTS : est -> Prop).
  Notation usp := (bv_unsigned sp). Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation A2 := (c_A2 cx). Notation FT := (c_FT cx).
  Notation bz := (c_bz cx). Notation J := (c_J cx).
  Variables (qsp : Z) (j8 : list byte).
  (* [comment removed for export] *)
  Definition hc_sec : Prop :=
    cctx_ok cx /\ cctx_sep cx /\ cctx_img S0C cx /\ hc_lawsB HCXB CBFACTS /\ compressBlock_spec CBFACTS S0C /\
    Z.of_nat (length OB) = on /\ z_in z0 = map bv_unsigned pl /\ pay_condB cx ob on nin pl /\
    z_outr z0 = [] /\ z_avail_out z0 = on /\ (lo + HC_STACK <= usp)%Z /\ (CEIL <= lo)%Z /\ (usp = 16 * qsp)%Z /\ u8ro s0segs m0 nin pl /\
    out_okB S0C cx ob on /\ strm_okB cx usp.
  Hypothesis HS : hc_sec.

  Notation W := (handle_compress_WB cx ob on usp).
  Notation POST := (handle_compress_postB HCXB s0segs S0C cx ob on dbza dbzfr g0 e0 z0 nin pl OB p1 p2 sv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo W m0).
  Definition FRAME : list cell := [CB 8 j8; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  (* [comment removed for export] *)
  Definition kin (z : zstrm) : Z := (z_avail_in z0 - z_avail_in z)%Z.
  (* [comment removed for export] *)
  Definition MEMh (g : eg) (e : est) (z : zstrm) (mc m : word -> option byte) : Prop :=
    rw_cells s0segs m E (EHEAD1 cx g e) /\ rw_cells s0segs m (E + 640) (EHEAD2 cx g e) /\
    u8arr s0segs m (E + 128) (ovb (e_inUse e) (jseg J 128 256) 256) /\
    u8arr s0segs m A2 (zb8 (e_arr2 e) ARR2_SIZE) /\
    rw_cells s0segs m (bz + 5016) (STRMB cx ob on dbza dbzfr z (nin + kin z) p1 p2) /\
    u8arr s0segs m ob (outb (z_outr z) OB) /\ length (outb (z_outr z) OB) = Z.to_nat on /\
    u32arr s0segs m 209272 crc_words /\
    hid (erest S0C cx e sv mc) /\ munch (hc_WlocB cx ob on usp) mc m /\ wmono s0segs mc m /\
    mem_inv s0segs m /\ munch W m0 m /\ wmono s0segs m0 m /\ stk s0segs m lo (usp - 112) /\ rw_cells s0segs m (usp - 112) FRAME.
  (* [comment removed for export] *)
  Definition PUREh (g : eg) (e : est) (z : zstrm) : Prop :=
    HCXB cx on g e z /\ z_in z = map bv_unsigned (skipn (Z.to_nat (kin z)) pl) /\ (0 <= kin z)%Z.

  Ltac prep :=
    let CX := ident:(CX) in let SEP := ident:(SEP) in let IMG := ident:(IMG) in let PLM0 := ident:(PLM0) in let OOK := ident:(OOK) in let SOK := ident:(SOK) in let ALE := ident:(ALE) in let AL1 := ident:(AL1) in let AL2 := ident:(AL2) in let ALF := ident:(ALF) in let ALB := ident:(ALB) in let ALFb := ident:(ALFb) in pose proof HS as HS'; unfold hc_sec in HS';
    cps_destruct HS' as (CX & SEP & IMG & LAWS & CBS & LOB & ZIN & PAY & OUT0 & AOUT0 & STK16 & LO & ALQ & PLM0 & OOK & SOK); apply hid_i in PLM0;
    pose proof OOK as OOK'; unfold out_okB, apart, img_apart in OOK'; cbn [ci_hi S0C] in OOK'; cps_destruct OOK' as (RO1 & RO2 & RO3 & RO4 & SO1 & SO2 & SO3 & SO4 & IO);
    pose proof SOK as SOK'; unfold strm_okB in SOK'; cps_destruct SOK' as (SA1 & SA2 & SA8);
    pose proof CX as CX'; unfold cctx_ok in CX'; cbv zeta in CX';
    bz_ceil; bz_params; unfold ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, IMG_HI3, CEIL in CX';
    cps_destruct CX' as (RE1 & RE2 & RA1 & RA1' & RA2 & RA2' & RFT & RFT' & RBZ & RBZ' & RFB & RFB' & ALE & AL1 & AL2 & ALF & ALB & ALFb & LJ & LJB);
    pose proof SEP as SEP'; unfold cctx_sep, apart in SEP'; cbv zeta in SEP';
    cps_destruct SEP' as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13 & S14 & S15);
    pose proof IMG as IMG'; unfold cctx_img, img_apart in IMG'; cbn [ci_hi S0C] in IMG'; cps_destruct IMG' as (I1 & I2 & I3 & I4 & I5 & I6);
    bz_ceil; bz_params; unfold FTAB_WORDS, ESTATE_SIZE, BZFILE_SIZE, CEIL, HC_STACK, BZF_STRM, BZ_MAX_UNUSED, IMG_LO3, IMG_HI3 in *;
    hide_disj; pose proof crc_words_length as CWL; clear ALE AL1 AL2 ALF ALB ALFb.
  Ltac cbn_est := cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos
         e_nInUse e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf
         e_len e_code e_rfreq e_len_pack est_set_outpos est_set_modes est_set_rl est_rl rl_nblock rl_block rl_inUse rl_crc rl_ch rl_len
         z_in z_avail_in z_outr z_avail_out z_tin_lo z_tin_hi z_tout_lo z_tout_hi fst snd
         BZ_S_OUTPUT BZ_S_INPUT BZ_M_IDLE BZ_M_RUNNING BZ_M_FLUSHING BZ_M_FINISHING].
  Ltac cbn_est_in H := cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos
         e_nInUse e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf
         e_len e_code e_rfreq e_len_pack est_set_outpos est_set_modes est_set_rl est_rl rl_nblock rl_block rl_inUse rl_crc rl_ch rl_len
         z_in z_avail_in z_outr z_avail_out z_tin_lo z_tin_hi z_tout_lo z_tout_hi fst snd
         BZ_S_OUTPUT BZ_S_INPUT BZ_M_IDLE BZ_M_RUNNING BZ_M_FLUSHING BZ_M_FINISHING] in H.
  Ltac openh MEM :=
    let EH1 := ident:(EH1) in let EH2 := ident:(EH2) in let INU := ident:(INU) in let AR2 := ident:(AR2) in let SM := ident:(SM) in let OBM := ident:(OBM) in let LOBn := ident:(LOBn) in let MUL := ident:(MUL) in let MU := ident:(MU) in let ST := ident:(ST) in let FR := ident:(FR) in cps_destruct MEM as (EH1 & EH2 & INU & AR2 & SM & OBM & LOBn & CRC & HID & MUL & WML & MI & MU & WM & ST & FR);
    unfold EHEAD1, EHEAD2 in EH1, EH2; bz_params; unfold STRMB in SM; unfold FRAME in FR;
    cbn_est_in EH1; cbn_est_in EH2; cbn_est_in INU; cbn_est_in AR2; cbn_est_in SM; cbn_est_in OBM; cbn_est_in LOBn;
    unfold handle_compress_WB in MU; unfold hc_WlocB in MUL;
    pose proof (rw_cells_bound _ _ _ _ FR) as FRB; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FRB;
    pose proof (stk_lo_nonneg _ _ _ _ ST) as LONN.
  (* [comment removed for export] *)
  Ltac closeh EH1 EH2 INU AR2 SM OBM LOBn CRC HID MUL WML MI MU WM ST FR :=
    unfold MEMh;
    split; [first [exact EH1 | unfold EHEAD1; cbn_est; try match goal with GA : g_aie _ = true |- _ => rewrite ?GA in EH1; rewrite ?GA end; first [exact EH1 | cells_eq_by EH1]]|];
    split; [first [exact EH2 | unfold EHEAD2; cbn_est; first [exact EH2 | cells_eq_by EH2]]|];
    split; [cbn_est; exact INU|]; split; [cbn_est; exact AR2|];
    split; [first [exact SM | unfold STRMB, kin in *; cbn_est; first [exact SM | cells_eq_by SM]]|];
    split; [cbn_est; exact OBM|]; split; [cbn_est; exact LOBn|]; split; [exact CRC|];
    split; [exact HID|]; split; [exact MUL|]; split; [exact WML|]; split; [exact MI|]; split; [exact MU|]; split; [exact WM|];
    split; [exact ST| exact FR].
  (* [comment removed for export] *)
  Ltac hci_facts HI :=
    let MD := ident:(MD) in let MODES := ident:(MODES) in let STATES := ident:(STATES) in pose proof (HCIB_est_ok _ _ _ _ _ HI) as EOK;
    pose proof (HCIB_avail_out _ _ _ _ _ HI) as (AOR & OLEN); pose proof (HCIB_avail_in _ _ _ _ _ HI) as (AIL & AIR);
    cps_pose (HCIB_mode _ _ _ _ _ HI) as (MD & GA & AIE); pose proof (HCIB_rl _ _ _ _ _ HI) as RLD; pose proof (HCIB_inUse _ _ _ _ _ HI) as DEFI;
    unfold est_ok in EOK; cps_destruct EOK as (BOK1 & BOK2 & FTR & NBR & NZ0 & POSR & MODES & STATES & CHR & LENR & CRCR & CCR & BNO);
    unfold BZ_M_IDLE, BZ_M_RUNNING, BZ_M_FLUSHING, BZ_M_FINISHING, BZ_S_OUTPUT, BZ_S_INPUT in MODES, STATES, MD;
    unfold BZ_MAX_UNUSED in *.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Notation ci_loopL := (ci_loopF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 cx z0 nin pl OB p1 p2 sv lo ob on dbza dbzfr HCXB CBFACTS qsp j8 HS).
  Local Notation cb_callL := (cb_call ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 cx z0 nin pl OB p1 p2 sv lo ob on dbza dbzfr HCXB CBFACTS qsp j8 HS).
  Local Notation fin_tailL := (fin_tail ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 cx z0 nin pl OB p1 p2 sv lo ob on dbza dbzfr HCXB CBFACTS qsp j8 HS).
  Local Notation ap_callL := (ap_call ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 cx z0 nin pl OB p1 p2 sv lo ob on dbza dbzfr HCXB CBFACTS qsp j8 HS).

  (* [comment removed for export] *)
  Lemma in_tail : forall (Q : machine_state -> Prop) g e z (pin pout itb : bool) mc m
      (x1 xt0 xt1 xt2 xa3 xa4 xa5 xa6 xa7 xs8 xt3 xt4 xt5 xt6 : word),
    e_state e = BZ_S_INPUT -> (NBLOCKMAX <= e_nblock e \/ z_avail_in z = 0)%Z ->
    PUREh g e z -> MEMh g e z mc m ->
    (* [comment removed for export] *)
    (forall mc' m' (x1' xt0' xt1' xt2' xa0' xa1' xa2' xa3' xa4' xa5' xa6' xa7' xs8' xt3' xt4' xt5' xt6' : word),
        e_avail_in_expect e = 0%Z ->
        PUREh (eg_after_cb cx g (hc_flush e)) (hc_cbF e) z -> MEMh (eg_after_cb cx g (hc_flush e)) (hc_cbF e) z mc' m' ->
        evt s0segs Q (MS (mkR x1' (Z_to_bv 64 (usp - 112)) gp tp xt0' xt1' xt2' (Z_to_bv 64 E) (Z_to_bv 64 (Z.b2z (pin || itb)))
                             xa0' xa1' xa2' xa3' xa4' xa5' xa6' xa7'
                             (Z_to_bv 64 (Z.b2z pout)) (Z_to_bv 64 (E + 128)) (Z_to_bv 64 2) (Z_to_bv 64 255) (Z_to_bv 64 1) (Z_to_bv 64 209272)
                             xs8' (Z_to_bv 64 4) (Z_to_bv 64 (18446744073709551615 - (E + 128))) (Z_to_bv 64 (18446744073709551615 - 209272)) xt3' xt4' xt5' xt6')
                        F (Z_to_bv 64 0x14098) fc None m' (seg_rom s0segs))) ->
    (* [comment removed for export] *)
    (forall mc' m' (x1' xt0' xt1' xt2' xa0' xa1' xa2' xa3' xa4' xa5' xa6' xa7' xs8' xt3' xt4' xt5' xt6' : word),
        e_avail_in_expect e <> 0%Z -> (NBLOCKMAX <= e_nblock e)%Z ->
        PUREh (eg_after_cb cx g e) (hc_cbR e) z -> MEMh (eg_after_cb cx g e) (hc_cbR e) z mc' m' ->
        evt s0segs Q (MS (mkR x1' (Z_to_bv 64 (usp - 112)) gp tp xt0' xt1' xt2' (Z_to_bv 64 E) (Z_to_bv 64 (Z.b2z (pin || itb)))
                             xa0' xa1' xa2' xa3' xa4' xa5' xa6' xa7'
                             (Z_to_bv 64 (Z.b2z pout)) (Z_to_bv 64 (E + 128)) (Z_to_bv 64 2) (Z_to_bv 64 255) (Z_to_bv 64 1) (Z_to_bv 64 209272)
                             xs8' (Z_to_bv 64 4) (Z_to_bv 64 (18446744073709551615 - (E + 128))) (Z_to_bv 64 (18446744073709551615 - 209272)) xt3' xt4' xt5' xt6')
                        F (Z_to_bv 64 0x14098) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR x1 (Z_to_bv 64 (usp - 112)) gp tp xt0 xt1 xt2 (Z_to_bv 64 E) (Z_to_bv 64 (Z.b2z pin))
                         (Z_to_bv 64 (e_nblock e)) (Z_to_bv 64 NBLOCKMAX) (Z_to_bv 64 (Z.b2z itb)) xa3 xa4 xa5 xa6 xa7
                         (Z_to_bv 64 (Z.b2z pout)) (Z_to_bv 64 (E + 128)) (Z_to_bv 64 2) (Z_to_bv 64 255) (Z_to_bv 64 1) (Z_to_bv 64 209272)
                         xs8 (Z_to_bv 64 4) (Z_to_bv 64 (18446744073709551615 - (E + 128))) (Z_to_bv 64 (18446744073709551615 - 209272)) xt3 xt4 xt5 xt6)
                    F (Z_to_bv 64 0x1446c) fc None m (seg_rom s0segs)).
  Proof.
    intros Q g e z pin pout itb mc m x1 xt0 xt1 xt2 xa3 xa4 xa5 xa6 xa7 xs8 xt3 xt4 xt5 xt6 STI EXI PU MEM KF KM.
    pose proof PU as PU0. openh MEM. prep.
    cps_destruct PU as (HX & ZI & KNN). pose proof (hlB_hci _ _ LAWS _ _ _ _ _ HX) as HI. hci_facts HI.
    pose proof (b2z_range pout) as BP. pose proof (b2z_range pin) as BI. pose proof (b2z_range itb) as BT.
    (* [comment removed for export] *)
    wstep. rewrite MD. wstep. rewrite (lor_b2z itb pin), (Bool.orb_comm itb pin).
    wstep; if_cases K2; zify_cond_z K2; [exfalso; clear -K2; lia|].
    (* [comment removed for export] *)
    wstep. rewrite GA, AIE. bz32. wstep; if_cases KE; zify_cond_z KE.
    - (* [comment removed for export] *)
      assert (E0 : e_avail_in_expect e = 0%Z) by lia.
      wstep. wstep; if_cases KC; zify_cond_z KC.
      + (* [comment removed for export] *)
        enter_with (fin_tailL Q g e z (pin || itb) pout (est_rl e) mc);
          [st_eq | exact STI | exact MD | exact E0 | replace (e_state_in_ch e <? 256)%Z with false by (symmetry; apply Z.ltb_ge; lia); reflexivity
          | exact PU0 | closeh EH1 EH2 INU AR2 SM OBM LOBn CRC HID MUL WML MI MU WM ST FR |].
        intros mc' m' x1' xt0' xt1' xt2' xa0' xa1' xa2' xa3' xa4' xa5' xa6' xa7' xs7' xt3' xt4' xt5' xt6' PU' MEM'. eapply KF; [exact E0 | exact PU' | exact MEM'].
      + (* [comment removed for export] *)
        wstep. wstep.
        eapply (ap_callL Q g e z mc); [lia | lia | lia | lia | exact DEFI | exact BOK2 | lia | reflexivity
          | closeh EH1 EH2 INU AR2 SM OBM LOBn CRC HID MUL WML MI MU WM ST FR |].
        intros m' xt0' xt1' xt2' xa0' xa1' xa2' xa3' xa4' xa5' xa6' xa7' xt3' xt4' xt5' xt6' MEM'.
        clear EH1 EH2 INU AR2 SM OBM LOBn CRC HID MUL WML MI MU WM ST FR FRB LONN.
        openh MEM'. bz_ceil; bz_params; unfold FTAB_WORDS, ESTATE_SIZE, BZFILE_SIZE, CEIL, HC_STACK, BZF_STRM, BZ_MAX_UNUSED in *.
        (* [comment removed for export] *)
        enter_with (fin_tailL Q g e z (pin || itb) pout (add_pair_to_block (est_rl e)) mc);
          [st_eq | exact STI | exact MD | exact E0 | replace (e_state_in_ch e <? 256)%Z with true by (symmetry; apply Z.ltb_lt; lia); reflexivity
          | exact PU0 | closeh EH1 EH2 INU AR2 SM OBM LOBn CRC HID MUL WML MI MU WM ST FR |].
        intros mc' m'' x1' xt0'' xt1'' xt2'' xa0'' xa1'' xa2'' xa3'' xa4'' xa5'' xa6'' xa7'' xs7' xt3'' xt4'' xt5'' xt6'' PU' MEM''. eapply KF; [exact E0 | exact PU' | exact MEM''].
    - (* [comment removed for export] *)
      assert (NE0 : e_avail_in_expect e <> 0%Z) by lia.
      wstep; if_cases KN; zify_cond_z KN; [| exfalso; destruct EXI as [EXI|EXI]; clear - KN EXI AIE NE0; bz_params; lia].
      (* [comment removed for export] *)
      cps_pose (hlB_cbM _ _ LAWS cx on g e z HX STI NE0 ltac:(bz_params; lia)) as (PRE & FACTS & HX').
      wstep. wstep. wstep. wstep.
      enter_with (cb_callL Q g e z false mc);
        [ st_eq | lia | reflexivity | exact PRE | exact FACTS | closeh EH1 EH2 INU AR2 SM OBM LOBn CRC HID MUL WML MI MU WM ST FR |].
      intros m' xt0' xt1' xt2' xa0' xa1' xa2' xa3' xa4' xa5' xa6' xa7' xt3' xt4' xt5' xt6' MEM'.
      clear EH1 EH2 INU AR2 SM OBM LOBn CRC HID MUL WML MI MU WM ST FR FRB LONN.
      openh MEM'. bz_ceil; bz_params; unfold FTAB_WORDS, ESTATE_SIZE, BZFILE_SIZE, CEIL, HC_STACK, BZF_STRM, BZ_MAX_UNUSED in *.
      (* [comment removed for export] *)
      wstep. wstep.
      eapply KM.
      + exact NE0.
      + bz_params; lia.
      + unfold PUREh. split; [exact HX'|]. split; [exact ZI| exact KNN].
      + unfold hc_cbR. rewrite (surjective_pairing (compressBlock e false znew)).
        closeh EH1 EH2 INU AR2 SM OBM LOBn CRC HID MUL WML MI MU WM ST FR.
  Qed.

  (* [comment removed for export] *)
  Lemma seg_finB : forall (Q : machine_state -> Prop) g e z (pin pout : bool) mc m
      (x1 xt0 xt1 xt2 xa0 xa1 xa3 xa4 xa5 xa6 xa7 xs8 xt3 xt4 xt5 xt6 : word),
    e_state e = BZ_S_INPUT ->
    PUREh g e z -> MEMh g e z mc m ->
    (* [comment removed for export] *)
    (forall g1 e1 z1 pin1 mc' m' (x1' xt0' xt1' xt2' xa0' xa1' xa2' xa3' xa4' xa5' xa6' xa7' xs8' xt3' xt4' xt5' xt6' : word),
        hc_in znew e z pin pout = (e1, z1, pin1, pout, false) -> PUREh g1 e1 z1 -> MEMh g1 e1 z1 mc' m' ->
        evt s0segs Q (MS (mkR x1' (Z_to_bv 64 (usp - 112)) gp tp xt0' xt1' xt2' (Z_to_bv 64 E) (Z_to_bv 64 (Z.b2z pin1))
                             xa0' xa1' xa2' xa3' xa4' xa5' xa6' xa7'
                             (Z_to_bv 64 (Z.b2z pout)) (Z_to_bv 64 (E + 128)) (Z_to_bv 64 2) (Z_to_bv 64 255) (Z_to_bv 64 1) (Z_to_bv 64 209272)
                             xs8' (Z_to_bv 64 4) (Z_to_bv 64 (18446744073709551615 - (E + 128))) (Z_to_bv 64 (18446744073709551615 - 209272)) xt3' xt4' xt5' xt6')
                        F (Z_to_bv 64 0x14098) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR x1 (Z_to_bv 64 (usp - 112)) gp tp xt0 xt1 xt2 (Z_to_bv 64 E) (Z_to_bv 64 (Z.b2z pin))
                         xa0 xa1 (Z_to_bv 64 (e_mode e)) xa3 xa4 xa5 xa6 xa7
                         (Z_to_bv 64 (Z.b2z pout)) (Z_to_bv 64 (E + 128)) (Z_to_bv 64 2) (Z_to_bv 64 255) (Z_to_bv 64 1) (Z_to_bv 64 209272)
                         xs8 (Z_to_bv 64 4) (Z_to_bv 64 (18446744073709551615 - (E + 128))) (Z_to_bv 64 (18446744073709551615 - 209272)) xt3 xt4 xt5 xt6)
                    F (Z_to_bv 64 0x141c0) fc None m (seg_rom s0segs)).
  Proof.
    intros Q g e z pin pout mc m x1 xt0 xt1 xt2 xa0 xa1 xa3 xa4 xa5 xa6 xa7 xs8 xt3 xt4 xt5 xt6 STI PU MEM KT.
    pose proof PU as PU0. openh MEM. prep.
    cps_destruct PU as (HX & ZI & KNN). pose proof (hlB_hci _ _ LAWS _ _ _ _ _ HX) as HI. hci_facts HI.
    pose proof (b2z_range pout) as BP. pose proof (b2z_range pin) as BI.
    (* [comment removed for export] *)
    assert (HIN : forall e1 z1 pin1, copy_input (S (Z.to_nat (z_avail_in z))) e z pin = (e1, z1, pin1) ->
              hc_in znew e z pin pout =
              if (e_avail_in_expect e1 =? 0)%Z then (hc_cbF e1, z1, pin1, pout, false)
              else if (NBLOCKMAX <=? e_nblock e1)%Z then (hc_cbR e1, z1, pin1, pout, false)
              else if (z_avail_in z1 =? 0)%Z then (e1, z1, pin1, pout, true) else (e1, z1, pin1, pout, false)).
    { intros e1 z1 pin1 CI. unfold hc_in. replace (Z.to_nat (z_avail_in z) + 1)%nat with (S (Z.to_nat (z_avail_in z))) by lia.
      rewrite CI. pose proof (proj1 (copy_input_modes (S (Z.to_nat (z_avail_in z))) e z pin)) as CM. rewrite CI in CM. cbn [fst] in CM.
      rewrite CM, MD. cbn [Z.eqb Pos.eqb negb andb BZ_M_RUNNING BZ_M_FINISHING].
      unfold hc_cbF, hc_flush, hc_cbR. rewrite (surjective_pairing (compressBlock e1 false znew)).
      rewrite (surjective_pairing (compressBlock (est_set_rl e1 (flush_RL (est_rl e1))) _ znew)).
      replace (e_mode (est_set_rl e1 (flush_RL (est_rl e1))) =? BZ_M_FINISHING)%Z with true by (symmetry; cbn_est; rewrite CM, MD; reflexivity).
      reflexivity. }
    assert (CI0 : (NBLOCKMAX <= e_nblock e \/ z_avail_in z = 0)%Z -> copy_input (S (Z.to_nat (z_avail_in z))) e z pin = (e, z, pin)).
    { intros HX0. rewrite (copy_input_S_finF _ e z pin MD). bz_params.
      destruct (Z.leb_spec NBLOCKMAX (e_nblock e)); [reflexivity|].
      replace (z_avail_in z =? 0)%Z with true by (symmetry; apply Z.eqb_eq; lia). reflexivity. }
    assert (TAILK : forall e1 z1 (itb : bool) mcx mx (y1 yt0 yt1 yt2 ya3 ya4 ya5 ya6 ya7 ys8 yt3 yt4 yt5 yt6 : word),
              copy_input (S (Z.to_nat (z_avail_in z))) e z pin = (e1, z1, pin || itb) -> e_state e1 = BZ_S_INPUT ->
              (NBLOCKMAX <= e_nblock e1 \/ z_avail_in z1 = 0)%Z -> PUREh g e1 z1 -> MEMh g e1 z1 mcx mx ->
              evt s0segs Q (MS (mkR y1 (Z_to_bv 64 (usp - 112)) gp tp yt0 yt1 yt2 (Z_to_bv 64 E) (Z_to_bv 64 (Z.b2z pin))
                         (Z_to_bv 64 (e_nblock e1)) (Z_to_bv 64 NBLOCKMAX) (Z_to_bv 64 (Z.b2z itb)) ya3 ya4 ya5 ya6 ya7
                         (Z_to_bv 64 (Z.b2z pout)) (Z_to_bv 64 (E + 128)) (Z_to_bv 64 2) (Z_to_bv 64 255) (Z_to_bv 64 1) (Z_to_bv 64 209272)
                         ys8 (Z_to_bv 64 4) (Z_to_bv 64 (18446744073709551615 - (E + 128))) (Z_to_bv 64 (18446744073709551615 - 209272)) yt3 yt4 yt5 yt6)
                    F (Z_to_bv 64 0x1446c) fc None mx (seg_rom s0segs))).
    { intros e1 z1 itb mcx mx y1 yt0 yt1 yt2 ya3 ya4 ya5 ya6 ya7 ys8 yt3 yt4 yt5 yt6 CI ST1 EX1 PU1 MEM1.
      pose proof (HIN e1 z1 (pin || itb) CI) as HIN1.
      eapply (in_tail Q g e1 z1 pin pout itb mcx mx); [exact ST1 | exact EX1 | exact PU1 | exact MEM1 | |].
      - intros mc' m' x1' xt0' xt1' xt2' xa0' xa1' xa2' xa3' xa4' xa5' xa6' xa7' xs7' xt3' xt4' xt5' xt6' E0 PU' MEM'.
        eapply KT; [| exact PU' | exact MEM']. rewrite HIN1, E0. reflexivity.
      - intros mc' m' x1' xt0' xt1' xt2' xa0' xa1' xa2' xa3' xa4' xa5' xa6' xa7' xs7' xt3' xt4' xt5' xt6' NE0 NB' PU' MEM'.
        eapply KT; [| exact PU' | exact MEM']. rewrite HIN1. replace (e_avail_in_expect e1 =? 0)%Z with false by (symmetry; apply Z.eqb_neq; exact NE0).
        replace (NBLOCKMAX <=? e_nblock e1)%Z with true by (symmetry; apply Z.leb_le; exact NB'). reflexivity. }
    (* [comment removed for export] *)
    wstep. wstep. rewrite MD. wstep; if_cases KM; zify_cond_z KM; [|exfalso; clear -KM; lia].
    (* [comment removed for export] *)
    wstep; if_cases KN; zify_cond_z KN.
    - (* [comment removed for export] *)
      wstep.
      enter_with (TAILK e z false mc); [bz_params; st_eq | rewrite Bool.orb_false_r; apply CI0; bz_params; lia | exact STI | bz_params; lia | exact PU0 | closeh EH1 EH2 INU AR2 SM OBM LOBn CRC HID MUL WML MI MU WM ST FR].
    - (* [comment removed for export] *)
      assert (LS7 : Z.land (bz + 5016) 7 = 0%Z) by (change 7%Z with (Z.ones 3); rewrite Z.land_ones by lia; exact SA8).
      wstep. wstep. wstep; notrap. wstep. rewrite LS7. wstep; notrap.
      wstep. wstep; if_cases KA; zify_cond_z KA.
      + (* [comment removed for export] *)
        enter_with (TAILK e z false mc); [bz_params; cbn [Z.b2z]; st_eq | rewrite Bool.orb_false_r; apply CI0; lia | exact STI | lia | exact PU0 | closeh EH1 EH2 INU AR2 SM OBM LOBn CRC HID MUL WML MI MU WM ST FR].
      + (* [comment removed for export] *)
        wstep. rewrite GA, AIE. bz32. wstep; if_cases KE; zify_cond_z KE; [exfalso; clear -KE KA; lia|].
        assert (CT : copy_input (S (Z.to_nat (z_avail_in z))) e z pin = copy_input (S (Z.to_nat (z_avail_in z))) e z true).
        { rewrite !(copy_input_S_finF _ e z _ MD). bz_params.
          replace (NBLOCKMAX <=? e_nblock e)%Z with false by (symmetry; apply Z.leb_gt; lia).
          replace (z_avail_in z =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
          replace (e_avail_in_expect e =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
        eapply (ci_loopL (S (Z.to_nat (z_avail_in z))) Q g e z pin pout mc);
          [lia | exact STI | bz_params; lia | lia | exact PU0 | closeh EH1 EH2 INU AR2 SM OBM LOBn CRC HID MUL WML MI MU WM ST FR |].
        intros e' z' m' x1' xt0' xt1' xt2' xa2' xa4' xa5' xa6' xa7' xs7' xt3' xt4' xt5' xt6' CO' ST' EX' PU' MEM'.
        eapply (TAILK e' z' true mc m'); [rewrite CT, Bool.orb_true_r; exact CO' | exact ST' | exact EX' | exact PU' | exact MEM'].
  Qed.
End HC.

End ACeilS1.
