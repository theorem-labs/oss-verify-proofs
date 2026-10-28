(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
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
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require GlueTac. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpArith2 BzInv S0_b2c_hcA S0_b2c_hcB S0_b2c_hcC.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require S0_b2c_hcF.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require S0_b2c_hcF.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require S0_b2c_hcF.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.GlueTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpArith2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzInv OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_b2c_hcA OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_b2c_hcB OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_b2c_hcC OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_b2c_hcF.S0_b2c_hcD OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_b2c_hcF.S0_b2c_hcE OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_b2c_hcF.
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
  (* [comment removed for export] *)
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
  Local Notation seg_outL := (seg_out ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 cx z0 nin pl OB p1 p2 sv lo ob on dbza dbzfr HCXB CBFACTS qsp j8 HS).
  Local Notation seg_finL := (seg_finB ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 cx z0 nin pl OB p1 p2 sv lo ob on dbza dbzfr HCXB CBFACTS qsp j8 HS).

  (* [comment removed for export] *)
  Lemma seg_in : forall (Q : machine_state -> Prop) g e z (pin pout : bool) mc m
      (x1 xt0 xt1 xt2 xa0 xa1 xa3 xa4 xa5 xa6 xa7 xs8 xt3 xt4 xt5 xt6 : word),
    e_state e = BZ_S_INPUT -> PUREh g e z -> MEMh g e z mc m ->
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
    eapply (seg_finL Q g e z pin pout mc); [exact STI | exact PU | exact MEM | exact KT].
  Qed.

  (* [comment removed for export] *)
  Lemma hc_ret : forall g e z (pin pout : bool) mc m
      (x1 xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs8 xt3 xt4 xt5 xt6 : word),
    handle_compress znew e0 z0 = (e, z, pin || pout) ->
    PUREh g e z -> MEMh g e z mc m ->
    evt s0segs POST (MS (mkR x1 (Z_to_bv 64 (usp - 112)) gp tp xt0 xt1 xt2 (Z_to_bv 64 E) (Z_to_bv 64 (Z.b2z pin))
                            xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                            (Z_to_bv 64 (Z.b2z pout)) (Z_to_bv 64 (E + 128)) (Z_to_bv 64 2) (Z_to_bv 64 255) (Z_to_bv 64 1) (Z_to_bv 64 209272)
                            xs8 (Z_to_bv 64 4) (Z_to_bv 64 (18446744073709551615 - (E + 128))) (Z_to_bv 64 (18446744073709551615 - 209272)) xt3 xt4 xt5 xt6)
                       F (Z_to_bv 64 0x144e0) fc None m (seg_rom s0segs)).
  Proof.
    intros g e z pin pout mc m x1 xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs8 xt3 xt4 xt5 xt6 RES PU MEM.
    openh MEM. prep.
    cps_destruct PU as (HX & ZI & KNN). pose proof (b2z_range pout) as BP. pose proof (b2z_range pin) as BI.
    (* [comment removed for export] *)
    wstep. rewrite (lor_b2z pin pout).
    destruct (pin || pout) eqn:PR; cbn [Z.b2z]; (wstep; flags);
      (* [comment removed for export] *)
      do 15 wstep;
      pose proof (erest_transportB S0C cx ob on e sv mc _ usp HID MUL WML CX SEP IMG OOK ltac:(bz_ceil; bz_params; unfold CEIL, HC_STACK; lia) SA1 eq_refl) as HIDm;
      pose proof (hid_e _ HIDm) as ER; cps_destruct ER as (UNS & MTF & SEL & SLM & LEN & COD & RFQ & LNP & AR1 & FTB & CM);
      release_frame FR ST (bv_unsigned sp);
      replace (Z_to_bv 64 (usp - 112 + 112)) with sp by (rewrite <- (Z_to_bv_bv_unsigned sp) at 1; f_equal; lia);
      unfold handle_compress_postB; rewrite RES; cbn [Z.b2z];
      finish.
    all: first [ eapply emem_intro; [exact EH1 | exact INU | exact UNS | exact EH2 | exact MTF | exact SEL | exact SLM | exact LEN | exact COD | exact RFQ | exact LNP]
               | eapply amem_intro; [exact AR1 | exact AR2 | exact FTB]
               | exact CM
               | unfold kin in SM; exact SM
               | exact OBM
               | (eapply u8ro_keep; [exact (hid_e _ PLM0) | exact MU | intros NE; exact (pay_disj_hcB cx ob on nin _ usp lo (PAY NE) LO STK16 SA1)])
               | rewrite ZI, ZIN, skipn_map; unfold kin; reflexivity
               | exact HX
               | match goal with |- ?gg => idtac "LEFT:" gg end ].
  Qed.

  (* [comment removed for export] *)
  Lemma hc_top : forall (fuel : nat) g e z (pin pout : bool) mc m
      (x1 xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs8 xt3 xt4 xt5 xt6 : word),
    hc_breaks fuel znew e z pin pout ->
    hc_loop fuel znew e z pin pout = handle_compress znew e0 z0 ->
    PUREh g e z -> MEMh g e z mc m ->
    evt s0segs POST (MS (mkR x1 (Z_to_bv 64 (usp - 112)) gp tp xt0 xt1 xt2 (Z_to_bv 64 E) (Z_to_bv 64 (Z.b2z pin))
                            xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                            (Z_to_bv 64 (Z.b2z pout)) (Z_to_bv 64 (E + 128)) (Z_to_bv 64 2) (Z_to_bv 64 255) (Z_to_bv 64 1) (Z_to_bv 64 209272)
                            xs8 (Z_to_bv 64 4) (Z_to_bv 64 (18446744073709551615 - (E + 128))) (Z_to_bv 64 (18446744073709551615 - 209272)) xt3 xt4 xt5 xt6)
                       F (Z_to_bv 64 0x14098) fc None m (seg_rom s0segs)).
  Proof.
    induction fuel as [|fuel IH]; intros g e z pin pout mc m x1 xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs8 xt3 xt4 xt5 xt6 BRK RES PU MEM;
      [destruct BRK|].
    rewrite hc_breaks_S in BRK. rewrite hc_loop_S in RES.
    pose proof HS as HS'. cps_destruct HS' as (_ & _ & _ & LAWS0 & _).
    pose proof (hlB_hci _ _ LAWS0 _ _ _ _ _ (proj1 PU)) as HI0. clear LAWS0.
    destruct (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (HCIB_est_ok _ _ _ _ _ HI0))))))))) as [STO|STI].
    - (* [comment removed for export] *)
      rewrite (hc_iter_output znew e z pin pout STO) in BRK, RES.
      eapply (seg_outL POST g e z pin pout mc); [exact STO | exact PU | exact MEM | |].
      + intros e1 z1 pout1 m' x1' xt0' xt1' xt2' xa0' xa1' xa2' xa3' xa4' xa5' xa6' xa7' xs7' xt3' xt4' xt5' xt6' HO PU1 MEM1.
        rewrite HO in RES. cbn iota in RES.
        eapply (hc_ret g e1 z1 pin pout1 mc); [symmetry; exact RES | exact PU1 | exact MEM1].
      + intros e1 z1 pout1 m' x1' xt0' xt1' xt2' xa0' xa1' xa2' xa3' xa4' xa5' xa6' xa7' xt3' xt4' xt5' xt6' HO ST1 PU1 MEM1.
        rewrite HO in BRK, RES. cbn iota in BRK, RES.
        eapply (seg_in POST g e1 z1 pin pout1 mc); [exact ST1 | exact PU1 | exact MEM1 |].
        intros g1 e2 z2 pin2 mc'' m'' x1'' xt0'' xt1'' xt2'' xa0'' xa1'' xa2'' xa3'' xa4'' xa5'' xa6'' xa7'' xs7'' xt3'' xt4'' xt5'' xt6'' HIN PU2 MEM2.
        rewrite HIN in BRK, RES. cbn iota in BRK, RES.
        eapply (IH g1 e2 z2 pin2 pout1 mc''); [exact BRK | exact RES | exact PU2 | exact MEM2].
    - (* [comment removed for export] *)
      rewrite (hc_iter_input znew e z pin pout STI) in BRK, RES.
      pose proof MEM as MEM0. openh MEM. prep. hci_facts HI0. pose proof (b2z_range pout) as BP. pose proof (b2z_range pin) as BI.
      wstep. rewrite STI. unfold BZ_S_INPUT. wstep; if_cases K2; zify_cond_z K2; [|exfalso; clear -K2; lia].
      wstep.
      eapply (seg_in POST g e z pin pout mc); [exact STI | exact PU | exact MEM0 |].
      intros g1 e2 z2 pin2 mc'' m'' x1'' xt0'' xt1'' xt2'' xa0'' xa1'' xa2'' xa3'' xa4'' xa5'' xa6'' xa7'' xs7'' xt3'' xt4'' xt5'' xt6'' HIN PU2 MEM2.
      rewrite HIN in BRK, RES. cbn iota in BRK, RES.
      eapply (IH g1 e2 z2 pin2 pout mc''); [exact BRK | exact RES | exact PU2 | exact MEM2].
  Qed.

  (* [comment removed for export] *)
  Lemma hc_entry : forall m (xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
    HCXB cx on g0 e0 z0 ->
    emem cx s0segs g0 e0 m -> amem cx s0segs e0 m -> cimg_mem S0C m sv ->
    rw_cells s0segs m (bz + 5016) (STRMB cx ob on dbza dbzfr z0 nin p1 p2) ->
    u8arr s0segs m ob OB ->
    mem_inv s0segs m -> munch W m0 m -> wmono s0segs m0 m -> stk s0segs m lo (usp - 112) -> rw_cells s0segs m (usp - 112) FRAME ->
    evt s0segs POST (MS (mkR ra (Z_to_bv 64 (usp - 112)) gp tp xt0 xt1 xt2 s0 s1
                            (Z_to_bv 64 (bz + 5016)) xa1 xa2 xa3 xa4 xa5 xa6 xa7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
                       F (Z_to_bv 64 0x14054) fc None m (seg_rom s0segs)).
  Proof.
    intros m xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 HX EM AM CM SM OBM MI MU WM ST FR.
    prep.
    assert (LE7 : Z.land E 7 = 0%Z).
    { pose proof CX as CXa. unfold cctx_ok in CXa. cbv zeta in CXa. destruct CXa as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ALE0 & _).
      change 7%Z with (Z.ones 3). rewrite Z.land_ones by lia. apply (proj2 (Z.mod_divide E 8 ltac:(lia))).
      exists (2 * (E / 16))%Z. pose proof (Z.div_mod E 16 ltac:(lia)) as DM. lia. }
    assert (LS7 : Z.land (bz + 5016) 7 = 0%Z) by (change 7%Z with (Z.ones 3); rewrite Z.land_ones by lia; exact SA8).
    open_emem EM. open_amem AM. pose proof (cimg_crc_u32arr S0C m sv CM) as CRC. pose proof CM as CM0. cps_destruct CM as (CM1 & GOTC & CM3 & CM4).
    cbn [ci_segs ci_got ci_crc ci_crcx ci_stderrp S0C] in CM1, GOTC, CM3, CM4, CRC. change (205032 + 24)%Z with 205056%Z in GOTC.
    cbn_est_in EH1. cbn_est_in EH2. unfold EHEAD1, EHEAD2 in EH1, EH2. bz_params.
    unfold STRMB in SM. unfold FRAME in FR. unfold handle_compress_WB in MU.
    bz_ceil; bz_params; unfold FTAB_WORDS, ESTATE_SIZE, BZFILE_SIZE, CEIL, HC_STACK, BZF_STRM, BZ_MAX_UNUSED in *.
    pose proof (rw_cells_bound _ _ _ _ FR) as FRB; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FRB.
    pose proof (stk_lo_nonneg _ _ _ _ ST) as LONN.
    (* [comment removed for export] *)
    wstep. rewrite LS7. wstep; notrap. wstep. wstep; notrap. wstep. rewrite LE7. wstep; notrap.
    wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep.
    pose proof (hlB_term _ _ LAWS cx on g0 e0 z0 HX) as BRK.
    change (Z_to_bv 64 0) with (Z_to_bv 64 (Z.b2z false)).
    eapply (hc_top (hc_fuel z0) g0 e0 z0 false false m m); [exact BRK | reflexivity | |].
    - unfold PUREh, kin. split; [exact HX|]. rewrite Z.sub_diag. cbn [Z.to_nat skipn]. split; [exact ZIN| lia].
    - unfold MEMh. 
      split; [unfold EHEAD1; bz_params; cbn_est; exact EH1|].
      split; [unfold EHEAD2; bz_params; cbn_est; exact EH2|].
      split; [exact INU|]. split; [exact AR2|].
      split; [unfold STRMB, kin in *; cbn_est; cells_eq_by SM|].
      split; [rewrite OUT0, outb_nil; exact OBM|].
      split; [rewrite OUT0, outb_nil; lia|].
      split; [exact CRC|].
      split; [exact (erest_intro S0C cx e0 sv m UNS MTF SEL SLM LEN COD RFQ LNP AR1 FTB CM0)|].
      split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI|]. split; [exact MU|]. split; [exact WM|].
      split; [exact ST| exact FR].
  Qed.
End HC.

(* [comment removed for export] *)
Theorem S0_handle_compressB : forall HCXB CBFACTS, compressBlock_spec CBFACTS S0C -> handle_compress_specB HCXB CBFACTS S0C.
Proof.
  intros HCXB CBFACTS CBS. unfold handle_compress_specB. cbn [ci_segs ci_handle_compress S0C]. intros until lo.
  intros A0 EM AM CM SM SOK OBM LOB OOK PLM ZIN PAY OUT0 AOUT0 MI ST STK LO AL CX SEP IMG LAWS HX. subst a0.
  destruct (mod16_lin _ AL) as [qsp ALQ].
  assert (HS : hc_sec sp m cx z nin pl OB lo ob on HCXB CBFACTS qsp).
  { unfold hc_sec. repeat (split; [assumption|]). assumption. }
  clear PLM.
  pose proof CX as CX'. unfold cctx_ok in CX'. cbv zeta in CX'.
  cps_destruct CX' as (RE1 & RE2 & RA1 & RA1' & RA2 & RA2' & RFT & RFT' & RBZ & RBZ' & RFB & RFB' & _).
  open_emem EM. open_amem AM. cps_destruct CM as (CM1 & CM2 & CM3 & CM4). cbn [ci_segs ci_got ci_crc ci_crcx ci_stderrp S0C] in CM1, CM2, CM3, CM4.
  unfold STRMB in SM. pose proof SOK as SOK'. unfold strm_okB in SOK'. cps_destruct SOK' as (SA1 & SA2 & SA8).
  pose proof OOK as OOK'; unfold out_okB, apart, img_apart in OOK'; cbn [ci_hi S0C] in OOK'; cps_destruct OOK' as (RO1 & RO2 & RO3 & RO4 & SO1 & SO2 & SO3 & SO4 & IO).
  bz_ceil; bz_params; unfold ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, CEIL, HC_STACK, BZ_MAX_UNUSED, BZF_STRM in *.
  pose proof (munch_refl (handle_compress_WB cx ob on (bv_unsigned sp)) m) as MU. unfold handle_compress_WB, ESTATE_SIZE, FTAB_WORDS, HC_STACK, BZF_STRM in MU.
  pose proof (wmono_refl s0segs m) as WM.
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)]%Z m) as MUf. pose proof WM as WMf.
  (* [comment removed for export] *)
  shelve_mem EH1. shelve_mem EH2. shelve_mem INU. shelve_mem UNS. shelve_mem MTF. shelve_mem SEL. shelve_mem SLM. shelve_mem LEN.
  shelve_mem COD. shelve_mem RFQ. shelve_mem LNP. shelve_mem AR1. shelve_mem AR2. shelve_mem FTB.
  shelve_mem CM1. shelve_mem CM2. shelve_mem CM3. shelve_mem CM4. shelve_mem SM. shelve_mem OBM.
  carve_frame 112%nat ST.
  wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep.
  replace (bv_unsigned sp + -112)%Z with (bv_unsigned sp - 112)%Z in * by lia.
  unshelve_mems.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m' _) => transport_after_call s0segs m m' MUf WMf end.
  clear MUf WMf.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m' _) =>
    eapply (hc_entry ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m cx g e z nin pl OB p1 p2 sv lo ob on dbza dbzfr HCXB CBFACTS qsp _ HS m');
    [ exact HX
    | eapply emem_intro; [exact EH1 | exact INU | exact UNS | exact EH2 | exact MTF | exact SEL | exact SLM | exact LEN | exact COD | exact RFQ | exact LNP]
    | eapply amem_intro; [exact AR1 | exact AR2 | exact FTB]
    | split; [exact CM1|]; split; [exact CM2|]; split; [exact CM3| exact CM4]
    | exact SM | exact OBM | assumption | exact MU | exact WM | exact ST | unfold FRAME; exact FR ] end.
Qed.

End ACeilS1.
