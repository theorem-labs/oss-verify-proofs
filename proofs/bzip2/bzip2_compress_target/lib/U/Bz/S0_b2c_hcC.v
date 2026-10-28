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
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Musl Require Import S0_memset.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import GlueTac. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpArith2 BzInv S0_b2c_hcA S0_b2c_hcB.
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
    let MODES := ident:(MODES) in let STATES := ident:(STATES) in pose proof (HCIB_est_ok _ _ _ _ _ HI) as EOK;
    pose proof (HCIB_avail_out _ _ _ _ _ HI) as (AOR & OLEN); pose proof (HCIB_avail_in _ _ _ _ _ HI) as (AIL & AIR);
    pose proof (HCIB_mode _ _ _ _ _ HI) as MD; pose proof (HCIB_rl _ _ _ _ _ HI) as RLD; pose proof (HCIB_inUse _ _ _ _ _ HI) as DEFI;
    unfold est_ok in EOK; cps_destruct EOK as (BOK1 & BOK2 & FTR & NBR & NZ0 & POSR & MODES & STATES & CHR & LENR & CRCR & CCR & BNO);
    unfold BZ_M_IDLE, BZ_M_RUNNING, BZ_M_FLUSHING, BZ_M_FINISHING, BZ_S_OUTPUT, BZ_S_INPUT in MODES, STATES, MD;
    unfold BZ_MAX_UNUSED in *.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac hide1 H := lazymatch type of H with ?A \/ ?B => change (A \/ B) with (id (A \/ B)) in H end.
  Ltac pay_open PAY NE :=
    let P4 := ident:(P4) in let P5 := ident:(P5) in let P6 := ident:(P6) in let P7 := ident:(P7) in let P8 := ident:(P8) in let PAY' := fresh "PAY'" in
    pose proof (PAY NE) as PAY'; unfold pay_okB, apart in PAY';
    bz_ceil; bz_params; unfold FTAB_WORDS, ESTATE_SIZE, BZFILE_SIZE, CEIL in PAY';
    cps_destruct PAY' as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8); hide1 P4; hide1 P5; hide1 P6; hide1 P7; hide1 P8.
  (* [comment removed for export] *)
  Ltac plm_here PLM0 MU PAY NE LO STK16 SA1 :=
    pose proof (u8ro_transport s0segs _ _ _ _ _ (hid_e _ PLM0) MU (pay_disj_hcB cx ob on nin _ usp lo (PAY NE) LO STK16 SA1)) as PLM.
  Local Notation ci_advL := (ci_advF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 cx z0 nin pl OB p1 p2 sv lo ob on dbza dbzfr HCXB CBFACTS qsp j8 HS).
  Local Notation ci_callGL := (ci_callGF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 cx z0 nin pl OB p1 p2 sv lo ob on dbza dbzfr HCXB CBFACTS qsp j8 HS).
  (* [comment removed for export] *)
  Lemma ci_loopF : forall (fuel : nat) (Q : machine_state -> Prop) g e z (pin pout : bool) mc m
      (x1 xt0 xt1 xt2 xa1 xa2 xa4 xa5 xa6 xa7 xs8 xt3 xt4 xt5 xt6 : word),
    (Z.of_nat fuel > z_avail_in z)%Z -> e_state e = BZ_S_INPUT -> (e_nblock e < NBLOCKMAX)%Z -> z_avail_in z <> 0%Z ->
    PUREh g e z -> MEMh g e z mc m ->
    (forall e' z' m' (x1' xt0' xt1' xt2' xa3' xa4' xa5' xa6' xa7' xs8' xt3' xt4' xt5' xt6' : word),
        copy_input fuel e z true = (e', z', true) -> e_state e' = BZ_S_INPUT ->
        (NBLOCKMAX <= e_nblock e' \/ z_avail_in z' = 0)%Z ->
        PUREh g e' z' -> MEMh g e' z' mc m' ->
        evt s0segs Q (MS (mkR x1' (Z_to_bv 64 (usp - 112)) gp tp xt0' xt1' xt2' (Z_to_bv 64 E) (Z_to_bv 64 (Z.b2z pin))
                             (Z_to_bv 64 (e_nblock e')) (Z_to_bv 64 NBLOCKMAX) (Z_to_bv 64 1) xa3' xa4' xa5' xa6' xa7'
                             (Z_to_bv 64 (Z.b2z pout)) (Z_to_bv 64 (E + 128)) (Z_to_bv 64 2) (Z_to_bv 64 255) (Z_to_bv 64 1) (Z_to_bv 64 209272)
                             xs8' (Z_to_bv 64 4) (Z_to_bv 64 (18446744073709551615 - (E + 128))) (Z_to_bv 64 (18446744073709551615 - 209272)) xt3' xt4' xt5' xt6')
                        F (Z_to_bv 64 0x1446c) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR x1 (Z_to_bv 64 (usp - 112)) gp tp xt0 xt1 xt2 (Z_to_bv 64 E) (Z_to_bv 64 (Z.b2z pin))
                         (Z_to_bv 64 (e_nblock e)) xa1 xa2 (Z_to_bv 64 (bz + 5016)) xa4 xa5 xa6 xa7
                         (Z_to_bv 64 (Z.b2z pout)) (Z_to_bv 64 (E + 128)) (Z_to_bv 64 2) (Z_to_bv 64 255) (Z_to_bv 64 1) (Z_to_bv 64 209272)
                         xs8 (Z_to_bv 64 4) (Z_to_bv 64 (18446744073709551615 - (E + 128))) (Z_to_bv 64 (18446744073709551615 - 209272)) xt3 xt4 xt5 xt6)
                    F (Z_to_bv 64 0x14338) fc None m (seg_rom s0segs)).
  Proof.
    induction fuel as [|fuel IH]; intros Q g e z pin pout mc m x1 xt0 xt1 xt2 xa1 xa2 xa4 xa5 xa6 xa7 xs8 xt3 xt4 xt5 xt6 FUEL STI NBM AIN PU MEM K;
    openh MEM; prep;
    cps_destruct PU as (HX & ZI & KNN); pose proof (hlB_hci _ _ LAWS _ _ _ _ _ HX) as HI;
    pose proof (HCIB_est_ok _ _ _ _ _ HI) as EOK; pose proof (HCIB_avail_in _ _ _ _ _ HI) as (AIL & AIR); pose proof (HCIB_rl _ _ _ _ _ HI) as RLD;
    pose proof (HCIB_inUse _ _ _ _ _ HI) as DEFI; cps_pose (HCIB_mode _ _ _ _ _ HI) as (MF & GA & AIE);
    unfold est_ok in EOK; cps_destruct EOK as (BOK1 & BOK2 & FTR & NBR & NZ0 & POSR & MODES & STATES & CHR & LENR & CRCR & CCR & BNO);
    [exfalso; lia|].
    (* [comment removed for export] *)
    destruct (skipn (Z.to_nat (kin z)) pl) as [|b plrest] eqn:SK.
    { exfalso. rewrite ZI in AIL. cbn [map length] in AIL. lia. }
    assert (NTH : nth_error pl (Z.to_nat (kin z)) = Some b).
    { rewrite <- (Nat.add_0_r (Z.to_nat (kin z))), <- nth_error_skipn, SK. reflexivity. }
    pose proof (nth_error_lt _ _ _ NTH) as KLT.
    set (ch := bv_unsigned b). assert (Hch : (0 <= ch < 256)%Z) by (subst ch; apply byte_range).
    assert (ZI' : z_in z = ch :: map bv_unsigned plrest) by (rewrite ZI; reflexivity).
    pose proof (ci_stepF_eq e z ch (map bv_unsigned plrest) ZI') as CIE.
    assert (CIS : copy_input (S fuel) e z true = copy_input fuel (fst (ci_stepF e z)) (snd (ci_stepF e z)) true).
    { rewrite (copy_input_S_finF fuel e z true MF). bz_params. replace (NBLOCKMAX <=? e_nblock e)%Z with false by (symmetry; apply Z.leb_gt; lia).
      replace (z_avail_in z =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
      replace (e_avail_in_expect e =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
    pose proof (hlB_ci _ _ LAWS cx on g e z HX STI ltac:(bz_params; lia) AIN) as HX'.
    rewrite CIE in CIS, HX'. cbv zeta in CIS. cbv zeta in HX'. cbn [fst snd] in CIS, HX'. clear CIE.
    assert (ZIn : map bv_unsigned plrest = map bv_unsigned (skipn (Z.to_nat (kin z + 1)) pl)).
    { f_equal. replace (Z.to_nat (kin z + 1)) with (1 + Z.to_nat (kin z))%nat by lia. rewrite <- skipn_skipn, SK. reflexivity. }
    assert (AI1 : (1 <= z_avail_in z < 2147483648)%Z) by lia.
    assert (NE : pl <> []) by (intros ->; rewrite skipn_nil in SK; discriminate SK).
    pay_open PAY NE. plm_here PLM0 MU PAY NE LO STK16 SA1.
    assert (NINK : (0 < nin + kin z < CEIL)%Z) by (bz_ceil; unfold CEIL; lia).
    (* [comment removed for export] *)
    wstep. wstep; notrap.
    match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u8ro_read s0segs mm nin pl (kin z) b _ PLM NTH ltac:(lia) eq_refl) as RD end.
    wstep. clear RD PLM. cbv beta. fold ch. wstep. wstep.
    (* [comment removed for export] *)
    wstep; if_cases Kne; zify_cond_z Kne.
    - (* [comment removed for export] *)
      wstep; if_cases K1; zify_cond_z K1.
      + (* [comment removed for export] *)
        wstep; if_cases K256; zify_cond_z K256.
        * (* [comment removed for export] *)
          wstep. wstep.
        rewrite (acb_gen256 (est_rl e) ch) in CIS, HX' by (cbn_est; lia). cbn_est_in CIS. cbn_est_in HX'.
        enter_with (ci_advL Q g (est_set_rl e (RL (e_nblock e) (e_arr2 e) (e_inUse e) (e_blockCRC e) ch 1)) z (map bv_unsigned plrest) ch mc);
          [ cbn_est; st_eq | exact AI1 | cbn_est; exact AIE | exact GA | exact HX' | exact Hch | exact NINK
          | closeh EH1 EH2 INU AR2 SM OBM LOBn CRC HID MUL WML MI MU WM ST FR
          | (* [comment removed for export] *)
            intros m' x1' xt0' xt1' xt2' xa3' xa4' xa5' xa6' xa7' xt3' xt4' xt5' xt6' EXIT MEM';
            eapply (K (est_set_modes (est_set_rl e (RL (e_nblock e) (e_arr2 e) (e_inUse e) (e_blockCRC e) ch 1)) (e_mode e) (e_state e) (e_avail_in_expect e - 1)));
            [ rewrite CIS; destruct fuel as [|fuel']; [reflexivity|];
              rewrite copy_input_S_finF by (cbn_est; exact MF); cbn_est; cbn_est_in EXIT; bz_params;
              match goal with |- context [(NBLOCKMAX <=? ?x)%Z] => destruct (Z.leb_spec NBLOCKMAX x); [reflexivity|] end;
              destruct EXIT as [EX|EX]; [exfalso; bz_params; lia|]; unfold z_adv; cbn_est; unfold z_adv in EX; cbn_est_in EX;
              rewrite (proj2 (Z.eqb_eq _ _) EX); reflexivity
            | cbn_est; exact STI | exact EXIT
            | unfold PUREh; split; [exact HX'|]; unfold kin in *; unfold z_adv; cbn_est; rewrite ZIn; split; [f_equal; f_equal; f_equal; lia| lia]
            | exact MEM' ]
          | (* [comment removed for export] *)
            intros m' x1' xt0' xt1' xt2' xa1' xa2' xa4' xa5' xa6' xa7' xt3' xt4' xt5' xt6' NB' AI' MEM';
            enter_with (IH Q g (est_set_modes (est_set_rl e (RL (e_nblock e) (e_arr2 e) (e_inUse e) (e_blockCRC e) ch 1)) (e_mode e) (e_state e) (e_avail_in_expect e - 1)) (z_adv z (map bv_unsigned plrest)) pin pout mc m');
            [ cbn_est; st_eq | unfold z_adv; cbn_est; lia | cbn_est; exact STI | exact NB' | exact AI'
            | unfold PUREh; split; [exact HX'|]; unfold kin in *; unfold z_adv; cbn_est; rewrite ZIn; split; [f_equal; f_equal; f_equal; lia| lia]
            | exact MEM'
            | intros e'' z'' m'' x1'' xt0'' xt1'' xt2'' xa3'' xa4'' xa5'' xa6'' xa7'' xs8'' xt3'' xt4'' xt5'' xt6'' CO'' ST'' EX'' PU'' MEM'';
              eapply K; [rewrite CIS; exact CO''| exact ST'' | exact EX'' | exact PU'' | exact MEM''] ] ].
        * (* [comment removed for export] *)
          assert (IC : (e_state_in_ch e < 256)%Z) by lia.
          eapply (ci_callGL Q g e z ch mc); [cbn_est; lia | cbn_est; lia | exact CRCR | bz_params; lia | exact DEFI | exact BOK2 | exact Hch
                           | closeh EH1 EH2 INU AR2 SM OBM LOBn CRC HID MUL WML MI MU WM ST FR |].
          intros mG x1G xt0G xt1G xt2G xa0G xa1G xa2G xa3G xa4G xa5G xa6G xa7G xt3G xt4G xt5G xt6G MEMG.
        rewrite (acb_gen (est_rl e) ch) in CIS, HX' by (cbn_est; lia). cbn_est_in CIS. cbn_est_in HX'.
        enter_with (ci_advL Q g (est_set_rl e (let r1 := add_pair_to_block (est_rl e) in RL (rl_nblock r1) (rl_block r1) (rl_inUse r1) (rl_crc r1) ch 1)) z (map bv_unsigned plrest) ch mc);
          [ cbn_est; st_eq | exact AI1 | cbn_est; exact AIE | exact GA | exact HX' | exact Hch | exact NINK
          | exact MEMG
          | (* [comment removed for export] *)
            intros m' x1' xt0' xt1' xt2' xa3' xa4' xa5' xa6' xa7' xt3' xt4' xt5' xt6' EXIT MEM';
            eapply (K (est_set_modes (est_set_rl e (let r1 := add_pair_to_block (est_rl e) in RL (rl_nblock r1) (rl_block r1) (rl_inUse r1) (rl_crc r1) ch 1)) (e_mode e) (e_state e) (e_avail_in_expect e - 1)));
            [ rewrite CIS; destruct fuel as [|fuel']; [reflexivity|];
              rewrite copy_input_S_finF by (cbn_est; exact MF); cbn_est; cbn_est_in EXIT; bz_params;
              match goal with |- context [(NBLOCKMAX <=? ?x)%Z] => destruct (Z.leb_spec NBLOCKMAX x); [reflexivity|] end;
              destruct EXIT as [EX|EX]; [exfalso; bz_params; lia|]; unfold z_adv; cbn_est; unfold z_adv in EX; cbn_est_in EX;
              rewrite (proj2 (Z.eqb_eq _ _) EX); reflexivity
            | cbn_est; exact STI | exact EXIT
            | unfold PUREh; split; [exact HX'|]; unfold kin in *; unfold z_adv; cbn_est; rewrite ZIn; split; [f_equal; f_equal; f_equal; lia| lia]
            | exact MEM' ]
          | (* [comment removed for export] *)
            intros m' x1' xt0' xt1' xt2' xa1' xa2' xa4' xa5' xa6' xa7' xt3' xt4' xt5' xt6' NB' AI' MEM';
            enter_with (IH Q g (est_set_modes (est_set_rl e (let r1 := add_pair_to_block (est_rl e) in RL (rl_nblock r1) (rl_block r1) (rl_inUse r1) (rl_crc r1) ch 1)) (e_mode e) (e_state e) (e_avail_in_expect e - 1)) (z_adv z (map bv_unsigned plrest)) pin pout mc m');
            [ cbn_est; st_eq | unfold z_adv; cbn_est; lia | cbn_est; exact STI | exact NB' | exact AI'
            | unfold PUREh; split; [exact HX'|]; unfold kin in *; unfold z_adv; cbn_est; rewrite ZIn; split; [f_equal; f_equal; f_equal; lia| lia]
            | exact MEM'
            | intros e'' z'' m'' x1'' xt0'' xt1'' xt2'' xa3'' xa4'' xa5'' xa6'' xa7'' xs8'' xt3'' xt4'' xt5'' xt6'' CO'' ST'' EX'' PU'' MEM'';
              eapply K; [rewrite CIS; exact CO''| exact ST'' | exact EX'' | exact PU'' | exact MEM''] ] ].
      + (* [comment removed for export] *)
        assert (IC : (e_state_in_ch e < 256)%Z) by lia.
        (* [comment removed for export] *)
        wstep. wstep. wstep. wstep. wstep.
        rewrite !land255_mod, !(Z.mod_small (e_state_in_ch e) 256) by lia.
        set (idx := Z.lxor (e_blockCRC e / 16777216) (e_state_in_ch e)).
        assert (Hidx : (0 <= idx < 256)%Z).
        { subst idx. apply lxor_byte; [|lia]. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
        (* [comment removed for export] *)
        wstep; notrap. wstep.
        u32_read CRC CWL idx tw NTHt RDt. replace (209272 + idx * 4)%Z with (209272 + 4 * idx)%Z by lia.
        wstep. clear RDt.
        assert (Etw : tw = Z_to_bv 64 (crc32_tbl idx)).
        { pose proof (nth_error_wnth crc_words idx ltac:(lia) ltac:(rewrite CWL; lia)) as N2.
          rewrite NTHt in N2. injection N2 as N3. rewrite N3. apply wnth_crc_words. lia. }
        subst tw. clear NTHt. pose proof (crc32_tbl_range idx Hidx) as TR.
        (* [comment removed for export] *)
        wstep. wstep. wstep.
        reword_C4 EH2 2%nat (crc_update (e_blockCRC e) (Z.land (e_state_in_ch e) 255)).
        { pose proof (crc_update_range (e_blockCRC e) (Z.land (e_state_in_ch e) 255) ltac:(lia)) as CR'.
          replace (crc_update (e_blockCRC e) (Z.land (e_state_in_ch e) 255) mod 4294967296)%Z with (crc_update (e_blockCRC e) (Z.land (e_state_in_ch e) 255))
            by (symmetry; apply Z.mod_small; exact CR').
          unfold crc_update. rewrite !land255_mod, !(Z.mod_small (e_state_in_ch e) 256), shiftr_div24 by lia. subst idx.
          pose proof (low32_crc_step' (Z_to_bv 64 (e_blockCRC e)) (e_blockCRC e) (crc32_tbl (Z.lxor (e_blockCRC e / 16777216) (e_state_in_ch e))) ltac:(rewrite low32_lit; apply Z.mod_small; lia) TR) as CS.
          rewrite (unsigned_lit (e_blockCRC e)), (Z.mod_small (e_blockCRC e * 256)), (Z.lxor_comm (e_blockCRC e * 256)) in CS by lia. exact CS. }
        wstep; notrap. wstep; notrap. wstep. wstep. wstep. fstep. fstep.
        (* [comment removed for export] *)
        match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          pose proof (u8arr_store_ok s0segs mm (E + 128) _ (e_state_in_ch e) _ INU ltac:(rewrite ovb_length_nat; lia) eq_refl) as SO end.
        wstep.
        match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm _ (le1 ?w)) _) =>
          pose proof (ovb_write1 s0segs mm (E + 128) (e_inUse e) (jseg J 128 256) 256 (e_state_in_ch e) w INU ltac:(lia)) as INU' end.
        clear INU. store_done. rename INU' into INU.
        replace (wr8 (e_inUse e) (e_state_in_ch e) (bv_unsigned (Z_to_bv 64 1))) with (zset (e_inUse e) (e_state_in_ch e) 1) in INU by reflexivity.
        wstep; notrap. fstep. fstep. wstep. wstep. wstep; notrap. wstep; notrap.
        (* [comment removed for export] *)
        match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          pose proof (u8arr_store_ok s0segs mm A2 _ (e_nblock e) _ AR2 ltac:(rewrite zb8_length_nat; lia) eq_refl) as SO end.
        wstep.
        match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm _ (le1 ?w)) _) =>
          pose proof (zb8_write1 s0segs mm A2 (e_arr2 e) ARR2_SIZE (e_nblock e) w AR2 ltac:(lia)) as AR2' end.
        clear AR2. store_done. rename AR2' into AR2.
        rewrite unsigned_lit in AR2 by lia. rewrite (wr8_zset_land (e_arr2 e) (e_nblock e) (e_state_in_ch e)) in AR2 by lia.
        (* [comment removed for export] *)
        wstep. wstep. wstep; notrap. wstep. wstep. wstep.
        rewrite (acb_fast (est_rl e) ch) in CIS, HX' by (cbn_est; lia). cbn_est_in CIS. cbn_est_in HX'.
        enter_with (ci_advL Q g (est_set_rl e (RL (e_nblock e + 1) (zset (e_arr2 e) (e_nblock e) (Z.land (e_state_in_ch e) 255)) (zset (e_inUse e) (e_state_in_ch e) 1) (crc_update (e_blockCRC e) (Z.land (e_state_in_ch e) 255)) ch 1)) z (map bv_unsigned plrest) ch mc);
          [ cbn_est; st_eq | exact AI1 | cbn_est; exact AIE | exact GA | exact HX' | exact Hch | exact NINK
          | closeh EH1 EH2 INU AR2 SM OBM LOBn CRC HID MUL WML MI MU WM ST FR
          | (* [comment removed for export] *)
            intros m' x1' xt0' xt1' xt2' xa3' xa4' xa5' xa6' xa7' xt3' xt4' xt5' xt6' EXIT MEM';
            eapply (K (est_set_modes (est_set_rl e (RL (e_nblock e + 1) (zset (e_arr2 e) (e_nblock e) (Z.land (e_state_in_ch e) 255)) (zset (e_inUse e) (e_state_in_ch e) 1) (crc_update (e_blockCRC e) (Z.land (e_state_in_ch e) 255)) ch 1)) (e_mode e) (e_state e) (e_avail_in_expect e - 1)));
            [ rewrite CIS; destruct fuel as [|fuel']; [reflexivity|];
              rewrite copy_input_S_finF by (cbn_est; exact MF); cbn_est; cbn_est_in EXIT; bz_params;
              match goal with |- context [(NBLOCKMAX <=? ?x)%Z] => destruct (Z.leb_spec NBLOCKMAX x); [reflexivity|] end;
              destruct EXIT as [EX|EX]; [exfalso; bz_params; lia|]; unfold z_adv; cbn_est; unfold z_adv in EX; cbn_est_in EX;
              rewrite (proj2 (Z.eqb_eq _ _) EX); reflexivity
            | cbn_est; exact STI | exact EXIT
            | unfold PUREh; split; [exact HX'|]; unfold kin in *; unfold z_adv; cbn_est; rewrite ZIn; split; [f_equal; f_equal; f_equal; lia| lia]
            | exact MEM' ]
          | (* [comment removed for export] *)
            intros m' x1' xt0' xt1' xt2' xa1' xa2' xa4' xa5' xa6' xa7' xt3' xt4' xt5' xt6' NB' AI' MEM';
            enter_with (IH Q g (est_set_modes (est_set_rl e (RL (e_nblock e + 1) (zset (e_arr2 e) (e_nblock e) (Z.land (e_state_in_ch e) 255)) (zset (e_inUse e) (e_state_in_ch e) 1) (crc_update (e_blockCRC e) (Z.land (e_state_in_ch e) 255)) ch 1)) (e_mode e) (e_state e) (e_avail_in_expect e - 1)) (z_adv z (map bv_unsigned plrest)) pin pout mc m');
            [ cbn_est; st_eq | unfold z_adv; cbn_est; lia | cbn_est; exact STI | exact NB' | exact AI'
            | unfold PUREh; split; [exact HX'|]; unfold kin in *; unfold z_adv; cbn_est; rewrite ZIn; split; [f_equal; f_equal; f_equal; lia| lia]
            | exact MEM'
            | intros e'' z'' m'' x1'' xt0'' xt1'' xt2'' xa3'' xa4'' xa5'' xa6'' xa7'' xs8'' xt3'' xt4'' xt5'' xt6'' CO'' ST'' EX'' PU'' MEM'';
              eapply K; [rewrite CIS; exact CO''| exact ST'' | exact EX'' | exact PU'' | exact MEM''] ] ].
    - (* [comment removed for export] *)
      wstep; if_cases K255; zify_cond_z K255.
      + (* [comment removed for export] *)
        assert (IC : (e_state_in_ch e < 256)%Z) by lia.
        eapply (ci_callGL Q g e z ch mc); [cbn_est; lia | cbn_est; lia | exact CRCR | bz_params; lia | exact DEFI | exact BOK2 | exact Hch
                         | closeh EH1 EH2 INU AR2 SM OBM LOBn CRC HID MUL WML MI MU WM ST FR |].
        intros mG x1G xt0G xt1G xt2G xa0G xa1G xa2G xa3G xa4G xa5G xa6G xa7G xt3G xt4G xt5G xt6G MEMG.
        rewrite (acb_same255 (est_rl e) ch) in CIS, HX' by (cbn_est; lia). cbn_est_in CIS. cbn_est_in HX'.
        enter_with (ci_advL Q g (est_set_rl e (let r1 := add_pair_to_block (est_rl e) in RL (rl_nblock r1) (rl_block r1) (rl_inUse r1) (rl_crc r1) ch 1)) z (map bv_unsigned plrest) ch mc);
          [ cbn_est; st_eq | exact AI1 | cbn_est; exact AIE | exact GA | exact HX' | exact Hch | exact NINK
          | exact MEMG
          | (* [comment removed for export] *)
            intros m' x1' xt0' xt1' xt2' xa3' xa4' xa5' xa6' xa7' xt3' xt4' xt5' xt6' EXIT MEM';
            eapply (K (est_set_modes (est_set_rl e (let r1 := add_pair_to_block (est_rl e) in RL (rl_nblock r1) (rl_block r1) (rl_inUse r1) (rl_crc r1) ch 1)) (e_mode e) (e_state e) (e_avail_in_expect e - 1)));
            [ rewrite CIS; destruct fuel as [|fuel']; [reflexivity|];
              rewrite copy_input_S_finF by (cbn_est; exact MF); cbn_est; cbn_est_in EXIT; bz_params;
              match goal with |- context [(NBLOCKMAX <=? ?x)%Z] => destruct (Z.leb_spec NBLOCKMAX x); [reflexivity|] end;
              destruct EXIT as [EX|EX]; [exfalso; bz_params; lia|]; unfold z_adv; cbn_est; unfold z_adv in EX; cbn_est_in EX;
              rewrite (proj2 (Z.eqb_eq _ _) EX); reflexivity
            | cbn_est; exact STI | exact EXIT
            | unfold PUREh; split; [exact HX'|]; unfold kin in *; unfold z_adv; cbn_est; rewrite ZIn; split; [f_equal; f_equal; f_equal; lia| lia]
            | exact MEM' ]
          | (* [comment removed for export] *)
            intros m' x1' xt0' xt1' xt2' xa1' xa2' xa4' xa5' xa6' xa7' xt3' xt4' xt5' xt6' NB' AI' MEM';
            enter_with (IH Q g (est_set_modes (est_set_rl e (let r1 := add_pair_to_block (est_rl e) in RL (rl_nblock r1) (rl_block r1) (rl_inUse r1) (rl_crc r1) ch 1)) (e_mode e) (e_state e) (e_avail_in_expect e - 1)) (z_adv z (map bv_unsigned plrest)) pin pout mc m');
            [ cbn_est; st_eq | unfold z_adv; cbn_est; lia | cbn_est; exact STI | exact NB' | exact AI'
            | unfold PUREh; split; [exact HX'|]; unfold kin in *; unfold z_adv; cbn_est; rewrite ZIn; split; [f_equal; f_equal; f_equal; lia| lia]
            | exact MEM'
            | intros e'' z'' m'' x1'' xt0'' xt1'' xt2'' xa3'' xa4'' xa5'' xa6'' xa7'' xs8'' xt3'' xt4'' xt5'' xt6'' CO'' ST'' EX'' PU'' MEM'';
              eapply K; [rewrite CIS; exact CO''| exact ST'' | exact EX'' | exact PU'' | exact MEM''] ] ].
      + (* [comment removed for export] *)
        wstep. wstep; notrap. wstep. wstep.
        rewrite (acb_same (est_rl e) ch) in CIS, HX' by (cbn_est; lia). cbn_est_in CIS. cbn_est_in HX'.
        enter_with (ci_advL Q g (est_set_rl e (RL (e_nblock e) (e_arr2 e) (e_inUse e) (e_blockCRC e) (e_state_in_ch e) (e_state_in_len e + 1))) z (map bv_unsigned plrest) ch mc);
          [ cbn_est; st_eq | exact AI1 | cbn_est; exact AIE | exact GA | exact HX' | exact Hch | exact NINK
          | closeh EH1 EH2 INU AR2 SM OBM LOBn CRC HID MUL WML MI MU WM ST FR
          | (* [comment removed for export] *)
            intros m' x1' xt0' xt1' xt2' xa3' xa4' xa5' xa6' xa7' xt3' xt4' xt5' xt6' EXIT MEM';
            eapply (K (est_set_modes (est_set_rl e (RL (e_nblock e) (e_arr2 e) (e_inUse e) (e_blockCRC e) (e_state_in_ch e) (e_state_in_len e + 1))) (e_mode e) (e_state e) (e_avail_in_expect e - 1)));
            [ rewrite CIS; destruct fuel as [|fuel']; [reflexivity|];
              rewrite copy_input_S_finF by (cbn_est; exact MF); cbn_est; cbn_est_in EXIT; bz_params;
              match goal with |- context [(NBLOCKMAX <=? ?x)%Z] => destruct (Z.leb_spec NBLOCKMAX x); [reflexivity|] end;
              destruct EXIT as [EX|EX]; [exfalso; bz_params; lia|]; unfold z_adv; cbn_est; unfold z_adv in EX; cbn_est_in EX;
              rewrite (proj2 (Z.eqb_eq _ _) EX); reflexivity
            | cbn_est; exact STI | exact EXIT
            | unfold PUREh; split; [exact HX'|]; unfold kin in *; unfold z_adv; cbn_est; rewrite ZIn; split; [f_equal; f_equal; f_equal; lia| lia]
            | exact MEM' ]
          | (* [comment removed for export] *)
            intros m' x1' xt0' xt1' xt2' xa1' xa2' xa4' xa5' xa6' xa7' xt3' xt4' xt5' xt6' NB' AI' MEM';
            enter_with (IH Q g (est_set_modes (est_set_rl e (RL (e_nblock e) (e_arr2 e) (e_inUse e) (e_blockCRC e) (e_state_in_ch e) (e_state_in_len e + 1))) (e_mode e) (e_state e) (e_avail_in_expect e - 1)) (z_adv z (map bv_unsigned plrest)) pin pout mc m');
            [ cbn_est; st_eq | unfold z_adv; cbn_est; lia | cbn_est; exact STI | exact NB' | exact AI'
            | unfold PUREh; split; [exact HX'|]; unfold kin in *; unfold z_adv; cbn_est; rewrite ZIn; split; [f_equal; f_equal; f_equal; lia| lia]
            | exact MEM'
            | intros e'' z'' m'' x1'' xt0'' xt1'' xt2'' xa3'' xa4'' xa5'' xa6'' xa7'' xs8'' xt3'' xt4'' xt5'' xt6'' CO'' ST'' EX'' PU'' MEM'';
              eapply K; [rewrite CIS; exact CO''| exact ST'' | exact EX'' | exact PU'' | exact MEM''] ] ].
  Qed.
End HC.

End ACeilS1.
