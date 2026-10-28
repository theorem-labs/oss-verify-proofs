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
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import GlueTac. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpArith2 BzInv S0_b2c_hcA.
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
  (* [comment removed for export] *)
  Lemma ap_call : forall (Q : machine_state -> Prop) g e z mc m (ret : Z)
      (xt0 xt1 xt2 ws1 xa1 xa2 xa3 xa4 xa5 xa6 xa7 ws2 xs8 xt3 xt4 xt5 xt6 : word),
    (0 <= e_state_in_ch e < 256)%Z -> (1 <= e_state_in_len e <= 255)%Z -> (0 <= e_blockCRC e < 4294967296)%Z ->
    (0 <= e_nblock e /\ e_nblock e + 5 <= ARR2_SIZE)%Z -> zdefr (e_inUse e) 0 256 -> zbok (e_arr2 e) ->
    (0 <= ret < 18446744073709551616)%Z -> (ret mod 2 = 0)%Z ->
    MEMh g e z mc m ->
    (forall m' (xt0' xt1' xt2' xa0' xa1' xa2' xa3' xa4' xa5' xa6' xa7' xt3' xt4' xt5' xt6' : word),
        MEMh g (est_set_rl e (add_pair_to_block (est_rl e))) z mc m' ->
        evt s0segs Q (MS (mkR (Z_to_bv 64 ret) (Z_to_bv 64 (usp - 112)) gp tp xt0' xt1' xt2' (Z_to_bv 64 E) ws1
                             xa0' xa1' xa2' xa3' xa4' xa5' xa6' xa7' ws2 (Z_to_bv 64 (E + 128)) (Z_to_bv 64 2) (Z_to_bv 64 255) (Z_to_bv 64 1) (Z_to_bv 64 209272)
                             xs8 (Z_to_bv 64 4) (Z_to_bv 64 (18446744073709551615 - (E + 128))) (Z_to_bv 64 (18446744073709551615 - 209272)) xt3' xt4' xt5' xt6')
                        F (Z_to_bv 64 ret) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR (Z_to_bv 64 ret) (Z_to_bv 64 (usp - 112)) gp tp xt0 xt1 xt2 (Z_to_bv 64 E) ws1
                         (Z_to_bv 64 E) xa1 xa2 xa3 xa4 xa5 xa6 xa7 ws2 (Z_to_bv 64 (E + 128)) (Z_to_bv 64 2) (Z_to_bv 64 255) (Z_to_bv 64 1) (Z_to_bv 64 209272)
                         xs8 (Z_to_bv 64 4) (Z_to_bv 64 (18446744073709551615 - (E + 128))) (Z_to_bv 64 (18446744073709551615 - 209272)) xt3 xt4 xt5 xt6)
                    F (Z_to_bv 64 0x1603c) fc None m (seg_rom s0segs)).
  Proof.
    intros Q g e z mc m ret xt0 xt1 xt2 ws1 xa1 xa2 xa3 xa4 xa5 xa6 xa7 ws2 xs8 xt3 xt4 xt5 xt6 CH LEN CRCR NB DEFI BOK RET RET2 MEM K.
    openh MEM. prep. bz_params.
    (* [comment removed for export] *)
    pose proof (erest_transportB S0C cx ob on e sv mc m usp HID MUL WML CX SEP IMG OOK ltac:(bz_ceil; bz_params; unfold CEIL, HC_STACK; lia) SA1 eq_refl) as HIDm.
    pose proof (hid_e _ HIDm) as ER. cps_destruct ER as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CM). clear HIDm.
    eapply evt_cut.
    { eapply (S0_add_pair _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m cx g e lo sv);
        [ reflexivity | exact EH1 | exact EH2 | exact INU | exact AR2 | exact CM | exact MI | cbn [ci_segs S0C]; rewrite unsigned_lit by lia; exact ST
        | rewrite unsigned_lit by lia; lia | bz_ceil; bz_params; unfold CEIL; lia | exact CX | exact SEP | exact IMG | lia | lia | lia | lia | bz_params; lia | exact DEFI | exact BOK ]. }
    cbn [ci_segs S0C]. clear CM EH1 EH2 INU AR2.
    post_callW s0segs m.
    rewrite (ret_pc_even ret) by lia.
    cbv zeta in POST. cps_destruct POST as (EH1 & EH2 & INU & AR2).
    eapply K. closeh EH1 EH2 INU AR2 SM OBM LOBn CRC HID MUL WML MI0 MU WM ST FR.
  Qed.

  (* [comment removed for export] *)
  Lemma ci_advF : forall (Q : machine_state -> Prop) g e1 z (rest : list Z) (ch : Z) mc m
      (x1 xt0 xt1 xt2 ws1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 ws2 xt3 xt4 xt5 xt6 : word),
    (1 <= z_avail_in z < 2147483648)%Z -> e_avail_in_expect e1 = z_avail_in z -> g_aie g = true ->
    HCXB cx on g (est_set_modes e1 (e_mode e1) (e_state e1) (e_avail_in_expect e1 - 1)) (z_adv z rest) -> (0 <= ch < 256)%Z ->
    (0 < nin + kin z < CEIL)%Z ->
    MEMh g e1 z mc m ->
    (forall m' (x1' xt0' xt1' xt2' xa3' xa4' xa5' xa6' xa7' xt3' xt4' xt5' xt6' : word),
        (NBLOCKMAX <= e_nblock e1 \/ z_avail_in (z_adv z rest) = 0)%Z ->
        MEMh g (est_set_modes e1 (e_mode e1) (e_state e1) (e_avail_in_expect e1 - 1)) (z_adv z rest) mc m' ->
        evt s0segs Q (MS (mkR x1' (Z_to_bv 64 (usp - 112)) gp tp xt0' xt1' xt2' (Z_to_bv 64 E) ws1
                             (Z_to_bv 64 (e_nblock e1)) (Z_to_bv 64 NBLOCKMAX) (Z_to_bv 64 1) xa3' xa4' xa5' xa6' xa7'
                             ws2 (Z_to_bv 64 (E + 128)) (Z_to_bv 64 2) (Z_to_bv 64 255) (Z_to_bv 64 1) (Z_to_bv 64 209272)
                             (Z_to_bv 64 ch) (Z_to_bv 64 4) (Z_to_bv 64 (18446744073709551615 - (E + 128))) (Z_to_bv 64 (18446744073709551615 - 209272)) xt3' xt4' xt5' xt6')
                        F (Z_to_bv 64 0x1446c) fc None m' (seg_rom s0segs))) ->
    (forall m' (x1' xt0' xt1' xt2' xa1' xa2' xa4' xa5' xa6' xa7' xt3' xt4' xt5' xt6' : word),
        (e_nblock e1 < NBLOCKMAX)%Z -> (z_avail_in (z_adv z rest) <> 0)%Z ->
        MEMh g (est_set_modes e1 (e_mode e1) (e_state e1) (e_avail_in_expect e1 - 1)) (z_adv z rest) mc m' ->
        evt s0segs Q (MS (mkR x1' (Z_to_bv 64 (usp - 112)) gp tp xt0' xt1' xt2' (Z_to_bv 64 E) ws1
                             (Z_to_bv 64 (e_nblock e1)) xa1' xa2' (Z_to_bv 64 (bz + 5016)) xa4' xa5' xa6' xa7'
                             ws2 (Z_to_bv 64 (E + 128)) (Z_to_bv 64 2) (Z_to_bv 64 255) (Z_to_bv 64 1) (Z_to_bv 64 209272)
                             (Z_to_bv 64 ch) (Z_to_bv 64 4) (Z_to_bv 64 (18446744073709551615 - (E + 128))) (Z_to_bv 64 (18446744073709551615 - 209272)) xt3' xt4' xt5' xt6')
                        F (Z_to_bv 64 0x14338) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR x1 (Z_to_bv 64 (usp - 112)) gp tp xt0 xt1 xt2 (Z_to_bv 64 E) ws1
                         xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                         ws2 (Z_to_bv 64 (E + 128)) (Z_to_bv 64 2) (Z_to_bv 64 255) (Z_to_bv 64 1) (Z_to_bv 64 209272)
                         (Z_to_bv 64 ch) (Z_to_bv 64 4) (Z_to_bv 64 (18446744073709551615 - (E + 128))) (Z_to_bv 64 (18446744073709551615 - 209272)) xt3 xt4 xt5 xt6)
                    F (Z_to_bv 64 0x14400) fc None m (seg_rom s0segs)).
  Proof.
    intros Q g e1 z rest ch mc m x1 xt0 xt1 xt2 ws1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 ws2 xt3 xt4 xt5 xt6 AIN EXP GA HX Hch NIN MEM KX KL.
    openh MEM. prep. rewrite GA in EH1.
    pose proof (hlB_hci _ _ LAWS _ _ _ _ _ HX) as HI. pose proof (HCIB_est_ok _ _ _ _ _ HI) as EOK.
    unfold est_ok in EOK; cbn_est_in EOK. cps_destruct EOK as (BOK1 & BOK2 & FTR & NBR & NZ0 & POSR & MODES & STATES & CHR & LENR & CRCR & CCR & BNO).
    bz_params.
    (* [comment removed for export] *)
    wstep. wstep; notrap. wstep. wstep; notrap. wstep. wstep. wstep; notrap.
    wstep. wstep. wstep. wstep. wstep. wstep. wstep.
    reword_C4 SM 2%nat (m32 (z_tin_lo z + 1))%Z. { rewrite low32_inc_sx32, m32_eq. symmetry. apply low32_mod. }
    unfold z_adv in *. set (hi' := if (m32 (z_tin_lo z + 1) =? 0)%Z then (z_tin_hi z + 1)%Z else z_tin_hi z) in *.
    (* [comment removed for export] *)
    wstep; if_cases Kc; zify_cond_z Kc.
    - assert (NC : (m32 (z_tin_lo z + 1) <> 0)%Z).
      { intros Hz. apply Kc. apply (proj2 (swrap32_mod64_zero_iff _)). rewrite inc_sx32_mod. exact Hz. }
      (* [comment removed for export] *)
      wstep. rewrite EXP. bz32. wstep. wstep. wstep. wstep. wstep.
      reword_C4 EH1 3%nat (e_avail_in_expect e1 - 1)%Z. { rewrite EXP. now low32. }
      (* [comment removed for export] *)
      wstep; if_cases Kf; zify_cond_z Kf.
      { enter_with KX; [unfold kin; cbn_est; st_eq| cbn_est; lia | subst hi'; rewrite (proj2 (Z.eqb_neq _ _) NC) in *; closeh EH1 EH2 INU AR2 SM OBM LOBn CRC HID MUL WML MI MU WM ST FR]. }
      (* [comment removed for export] *)
      wstep. wstep; notrap. wstep. wstep; notrap. wstep. wstep; if_cases Ka; zify_cond_z Ka.
      { enter_with KX; [unfold kin; cbn_est; st_eq| cbn_est; lia | subst hi'; rewrite (proj2 (Z.eqb_neq _ _) NC) in *; closeh EH1 EH2 INU AR2 SM OBM LOBn CRC HID MUL WML MI MU WM ST FR]. }
      (* [comment removed for export] *)
      wstep. wstep; if_cases Ke; zify_cond_z Ke; [exfalso; clear - Ke Ka AIN EXP; lia |].
      enter_with KL; [unfold kin; cbn_est; st_eq| cbn_est; lia | cbn_est; lia | subst hi'; rewrite (proj2 (Z.eqb_neq _ _) NC) in *; closeh EH1 EH2 INU AR2 SM OBM LOBn CRC HID MUL WML MI MU WM ST FR].
    - assert (CA : (m32 (z_tin_lo z + 1) = 0)%Z).
      { apply (proj1 (swrap32_mod64_zero_iff _)) in Kc. rewrite inc_sx32_mod in Kc. exact Kc. }
      (* [comment removed for export] *)
      wstep. wstep. wstep.
      reword_C4 SM 3%nat (z_tin_hi z + 1)%Z. { first [rewrite low32_inc64_sx32 | rewrite low32_inc64_sx32_mod]. reflexivity. }
      (* [comment removed for export] *)
      wstep. rewrite EXP. bz32. wstep. wstep. wstep. wstep. wstep.
      reword_C4 EH1 3%nat (e_avail_in_expect e1 - 1)%Z. { rewrite EXP. now low32. }
      (* [comment removed for export] *)
      wstep; if_cases Kf; zify_cond_z Kf.
      { enter_with KX; [unfold kin; cbn_est; st_eq| cbn_est; lia | subst hi'; rewrite (proj2 (Z.eqb_eq _ _) CA) in *; closeh EH1 EH2 INU AR2 SM OBM LOBn CRC HID MUL WML MI MU WM ST FR]. }
      (* [comment removed for export] *)
      wstep. wstep; notrap. wstep. wstep; notrap. wstep. wstep; if_cases Ka; zify_cond_z Ka.
      { enter_with KX; [unfold kin; cbn_est; st_eq| cbn_est; lia | subst hi'; rewrite (proj2 (Z.eqb_eq _ _) CA) in *; closeh EH1 EH2 INU AR2 SM OBM LOBn CRC HID MUL WML MI MU WM ST FR]. }
      (* [comment removed for export] *)
      wstep. wstep; if_cases Ke; zify_cond_z Ke; [exfalso; clear - Ke Ka AIN EXP; lia |].
      enter_with KL; [unfold kin; cbn_est; st_eq| cbn_est; lia | cbn_est; lia | subst hi'; rewrite (proj2 (Z.eqb_eq _ _) CA) in *; closeh EH1 EH2 INU AR2 SM OBM LOBn CRC HID MUL WML MI MU WM ST FR].
  Qed.

  (* [comment removed for export] *)
  Lemma ci_callGF : forall (Q : machine_state -> Prop) g e z (ch : Z) mc m
      (x1 xt0 xt1 xt2 ws1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 ws2 xt3 xt4 xt5 xt6 : word),
    (0 <= e_state_in_ch e < 256)%Z -> (1 <= e_state_in_len e <= 255)%Z -> (0 <= e_blockCRC e < 4294967296)%Z ->
    (0 <= e_nblock e < NBLOCKMAX)%Z -> zdefr (e_inUse e) 0 256 -> zbok (e_arr2 e) -> (0 <= ch < 256)%Z ->
    MEMh g e z mc m ->
    (forall m' (x1' xt0' xt1' xt2' xa0' xa1' xa2' xa3' xa4' xa5' xa6' xa7' xt3' xt4' xt5' xt6' : word),
        MEMh g (est_set_rl e (let r1 := add_pair_to_block (est_rl e) in RL (rl_nblock r1) (rl_block r1) (rl_inUse r1) (rl_crc r1) ch 1)) z mc m' ->
        evt s0segs Q (MS (mkR x1' (Z_to_bv 64 (usp - 112)) gp tp xt0' xt1' xt2' (Z_to_bv 64 E) ws1
                             xa0' xa1' xa2' xa3' xa4' xa5' xa6' xa7' ws2 (Z_to_bv 64 (E + 128)) (Z_to_bv 64 2) (Z_to_bv 64 255) (Z_to_bv 64 1) (Z_to_bv 64 209272)
                             (Z_to_bv 64 ch) (Z_to_bv 64 4) (Z_to_bv 64 (18446744073709551615 - (E + 128))) (Z_to_bv 64 (18446744073709551615 - 209272)) xt3' xt4' xt5' xt6')
                        F (Z_to_bv 64 0x14400) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR x1 (Z_to_bv 64 (usp - 112)) gp tp xt0 xt1 xt2 (Z_to_bv 64 E) ws1
                         xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 ws2 (Z_to_bv 64 (E + 128)) (Z_to_bv 64 2) (Z_to_bv 64 255) (Z_to_bv 64 1) (Z_to_bv 64 209272)
                         (Z_to_bv 64 ch) (Z_to_bv 64 4) (Z_to_bv 64 (18446744073709551615 - (E + 128))) (Z_to_bv 64 (18446744073709551615 - 209272)) xt3 xt4 xt5 xt6)
                    F (Z_to_bv 64 0x143f0) fc None m (seg_rom s0segs)).
  Proof.
    intros Q g e z ch mc m x1 xt0 xt1 xt2 ws1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 ws2 xt3 xt4 xt5 xt6 CH LEN CRCR NB DEFI BOK Hch MEM KG.
    (* [comment removed for export] *)
    wstep. wstep.
    eapply ap_call; [exact CH | exact LEN | exact CRCR | bz_params; lia | exact DEFI | exact BOK | lia | reflexivity | exact MEM |].
    intros m' xt0' xt1' xt2' xa0' xa1' xa2' xa3' xa4' xa5' xa6' xa7' xt3' xt4' xt5' xt6' MEM'.
    openh MEM'. prep. bz_params.
    (* [comment removed for export] *)
    wstep. wstep.
    eapply KG. closeh EH1 EH2 INU AR2 SM OBM LOBn CRC HID MUL WML MI MU WM ST FR.
  Qed.

End HC.

End ACeilS1.
