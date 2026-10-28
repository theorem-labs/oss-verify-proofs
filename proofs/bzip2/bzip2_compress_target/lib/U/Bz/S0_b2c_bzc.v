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
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut CmpCut0. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpArith. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpArith2 CmpSess CmpSess2 CmpSessB. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import GlueTac. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzInv S0_b2c_hcG.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import ZBridge.
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
(* [comment removed for export] *)
Ltac post_callWB segs m :=
  let ms' := fresh "ms'" in let PO := fresh "POST" in
  intros ms' PO;
  destruct_exs PO;
  let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MI" in
  destruct PO as [E [MUc [WMc PO]]];
  first [ destruct PO as [MIc PO] | rename PO into MIc ];
  subst ms';
  unfold add_pair_W, compressBlock_W, handle_compress_W, handle_compress_WB, bzCompress_WB, bsW8_W, bsPutUInt32_W, blockSort_W, fallbackSort_W, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, CB_STACK, HC_STACK, BZF_STRM in MUc;
  cbn [e_nblock e_mode e_state est_set_rl est_set_modes rl_nblock c_E c_A1 c_A2 c_FT c_bz] in MUc;
  repeat (rewrite unsigned_lit in MUc by lia);
  lazymatch type of MUc with
  | munch _ m ?m' =>
      transport_after_call segs m m' MUc WMc;
      clear MUc WMc;
      try match goal with H : mem_inv segs m |- _ => clear H end;
      try clear m
  end;
  try destruct_ands PO;
  try (lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end).
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Lemma land7_8 : forall x, (x mod 8 = 0)%Z -> Z.land x 7 = 0%Z.
Proof. intros x Hx. change 7%Z with (Z.ones 3). rewrite Z.land_ones by lia. exact Hx. Qed.
Lemma cctx_al8 : forall cx, cctx_ok cx -> (c_E cx mod 16 = 0)%Z.
Proof. intros cx H. unfold cctx_ok in H. cbv zeta in H. decompose [and] H. assumption. Qed.

Section BZC.
  Variables (HCXB : cctx -> Z -> eg -> est -> zstrm -> Prop) (CBFACTS : est -> Prop).
  Hypothesis CBS : compressBlock_spec CBFACTS S0C.
  Let HC : handle_compress_specB HCXB CBFACTS S0C := S0_handle_compressB HCXB CBFACTS CBS.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte).
  Variables (cx : cctx) (g0 : eg) (e0 : est) (z0 : zstrm) (nin : Z) (pl OB : list byte) (p1 p2 sv : word) (lo : Z) (qsp : Z) (ob on dbza dbzfr : Z).
  Notation usp := (bv_unsigned sp). Notation E := (c_E cx). Notation bz := (c_bz cx). Notation J := (c_J cx).
  Definition bzc_sec : Prop :=
    cctx_ok cx /\ cctx_sep cx /\ cctx_img S0C cx /\ hc_lawsB HCXB CBFACTS /\
    Z.of_nat (length OB) = on /\ z_in z0 = map bv_unsigned pl /\ pay_condB cx ob on nin pl /\
    z_outr z0 = [] /\ z_avail_out z0 = on /\ (lo + BZC_STACKB <= usp)%Z /\ (CEIL <= lo)%Z /\ (usp = 16 * qsp)%Z /\ u8ro s0segs m0 nin pl /\
    out_okB S0C cx ob on /\ strm_okB cx usp.
  Hypothesis HS : bzc_sec.
  Notation W := (bzCompress_WB cx ob on usp).
  Notation POST := (bzCompress_postB s0segs S0C cx ob on dbza dbzfr g0 e0 z0 nin pl OB p1 p2 sv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo W m0).
  Definition FRAME (j8 : list byte) : list cell := [CB 8 j8; C8 s1; C8 s0; C8 ra].

  Ltac prep :=
    let CX := ident:(CX) in let SEP := ident:(SEP) in let IMG := ident:(IMG) in let PLM0 := ident:(PLM0) in let OOK := ident:(OOK) in let SOK := ident:(SOK) in let ALE := ident:(ALE) in let AL1 := ident:(AL1) in let AL2 := ident:(AL2) in let ALF := ident:(ALF) in let ALB := ident:(ALB) in let ALFb := ident:(ALFb) in pose proof HS as HS'; unfold bzc_sec in HS';
    cps_destruct HS' as (CX & SEP & IMG & LAWS & LOB & ZIN & PAY & OUT0 & AOUT0 & STK & LO & ALQ & PLM0 & OOK & SOK); apply hid_i in PLM0;
    pose proof OOK as OOK'; unfold out_okB, apart, img_apart in OOK'; cbn [ci_hi S0C] in OOK'; cps_destruct OOK' as (RO1 & RO2 & RO3 & RO4 & SO1 & SO2 & SO3 & SO4 & IO);
    pose proof SOK as SOK'; unfold strm_okB in SOK'; cps_destruct SOK' as (SA1 & SA2 & SA8);
    pose proof CX as CX'; unfold cctx_ok in CX'; cbv zeta in CX';
    cps_destruct CX' as (RE1 & RE2 & RA1 & RA1' & RA2 & RA2' & RFT & RFT' & RBZ & RBZ' & RFB & RFB' & ALE & AL1 & AL2 & ALF & ALB & ALFb & LJ & LJB);
    clear ALE AL1 AL2 ALF ALB ALFb;
    pose proof SEP as SEP'; unfold cctx_sep, apart in SEP'; cbv zeta in SEP';
    cps_destruct SEP' as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13 & S14 & S15);
    pose proof IMG as IMG'; unfold cctx_img, img_apart in IMG'; cbn [ci_hi S0C] in IMG'; cps_destruct IMG' as (I1 & I2 & I3 & I4 & I5 & I6);
    bz_ceil; bz_params; unfold ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, CEIL, BZC_STACKB, HC_STACK, BZ_MAX_UNUSED, BZF_STRM, IMG_LO3, IMG_HI3 in *;
    hide_disj.
  Ltac hci_facts HI :=
    let MD := ident:(MD) in let MODES := ident:(MODES) in let STATES := ident:(STATES) in pose proof (HCIB_est_ok _ _ _ _ _ HI) as EOK;
    pose proof (HCIB_avail_out _ _ _ _ _ HI) as (AOR & OLEN); pose proof (HCIB_avail_in _ _ _ _ _ HI) as (AIL & AIR);
    cps_pose (HCIB_mode _ _ _ _ _ HI) as (MD & GA & AIE); pose proof (HCIB_rl _ _ _ _ _ HI) as RLD; pose proof (HCIB_inUse _ _ _ _ _ HI) as DEFI;
    pose proof (HCIB_numZ _ _ _ _ _ HI) as NUMZ; bz_params;
    unfold est_ok in EOK; cps_destruct EOK as (BOK1 & BOK2 & FTR & NBR & NZ0 & POSR & MODES & STATES & CHR & LENR & CRCR & CCR & BNO);
    unfold BZ_M_IDLE, BZ_M_RUNNING, BZ_M_FLUSHING, BZ_M_FINISHING, BZ_S_OUTPUT, BZ_S_INPUT in MODES, STATES, MD;
    unfold BZ_MAX_UNUSED in *.

  (* [comment removed for export] *)
  Lemma call_hc : forall (Q : machine_state -> Prop) g e z m (ret : Z) j8 xs0
      (xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
    (0 <= ret < 18446744073709551616)%Z -> (ret mod 2 = 0)%Z ->
    HCXB cx on g e z -> z_in z = z_in z0 -> z_avail_in z = z_avail_in z0 -> z_outr z = [] -> z_avail_out z = on ->
    emem cx s0segs g e m -> amem cx s0segs e m -> cimg_mem S0C m sv ->
    rw_cells s0segs m (bz + 5016) (STRMB cx ob on dbza dbzfr z nin p1 p2) -> u8arr s0segs m ob OB ->
    mem_inv s0segs m -> munch W m0 m -> wmono s0segs m0 m -> stk s0segs m lo (usp - 32) -> rw_cells s0segs m (usp - 32) (FRAME j8) ->
    (forall m' g' (xt0' xt1' xt2' xa1' xa2' xa3' xa4' xa5' xa6' xa7' xt3' xt4' xt5' xt6' : word),
        let '(e', z', pr) := handle_compress znew e z in
        HCXB cx on g' e' z' ->
        emem cx s0segs g' e' m' -> amem cx s0segs e' m' -> cimg_mem S0C m' sv ->
        rw_cells s0segs m' (bz + 5016) (STRMB cx ob on dbza dbzfr z' (nin + (z_avail_in z - z_avail_in z')) p1 p2) ->
        u8arr s0segs m' ob (outb (z_outr z') OB) ->
        z_in z' = skipn (Z.to_nat (z_avail_in z - z_avail_in z')) (z_in z) ->
        mem_inv s0segs m' -> munch W m0 m' -> wmono s0segs m0 m' -> stk s0segs m' lo (usp - 32) -> rw_cells s0segs m' (usp - 32) (FRAME j8) ->
        evt s0segs Q (MS (mkR (Z_to_bv 64 ret) (Z_to_bv 64 (usp - 32)) gp tp xt0' xt1' xt2' xs0 (Z_to_bv 64 E)
                             (Z_to_bv 64 (Z.b2z pr)) xa1' xa2' xa3' xa4' xa5' xa6' xa7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3' xt4' xt5' xt6')
                        F (Z_to_bv 64 ret) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR (Z_to_bv 64 ret) (Z_to_bv 64 (usp - 32)) gp tp xt0 xt1 xt2 xs0 (Z_to_bv 64 E)
                         (Z_to_bv 64 (bz + 5016)) xa1 xa2 xa3 xa4 xa5 xa6 xa7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
                    F (Z_to_bv 64 0x1401c) fc None m (seg_rom s0segs)).
  Proof.
    intros Q g e z m ret j8 xs0 xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 RET RET2 HX ZI AI OUT AOUT EM AM CM SM OBM MI MU WM ST FR K.
    prep. unfold bzCompress_WB, ESTATE_SIZE, FTAB_WORDS, BZC_STACKB, BZF_STRM in MU.
    assert (AL16 : ((usp - 32) mod 16 = 0)%Z).
    { rewrite ALQ. replace (16 * qsp - 32)%Z with (16 * qsp + 16 * (-2))%Z by lia. apply mod16_of_lin. }
    unfold FRAME in FR. pose proof (rw_cells_bound _ _ _ _ FR) as FRB. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FRB.
    pose proof (stk_lo_nonneg _ _ _ _ ST) as LONN.
    assert (PLM : u8ro s0segs m nin pl).
    { eapply u8ro_keep; [exact (hid_e _ PLM0) | exact MU | intros NE; exact (pay_disj_bzcB cx ob on nin _ usp lo (PAY NE) LO STK SA1)]. }
    eapply evt_cut.
    { eapply (HC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m cx ob on dbza dbzfr g e z nin pl OB p1 p2 sv lo);
        [ reflexivity | exact EM | exact AM | exact CM | exact SM
        | rewrite unsigned_lit by lia; apply (strm_okB_frame cx usp 32 SOK); lia
        | exact OBM | exact LOB | exact OOK | exact PLM | rewrite ZI; exact ZIN | exact PAY
        | exact OUT | exact AOUT | exact MI
        | cbn [ci_segs S0C]; rewrite unsigned_lit by lia; exact ST
        | rewrite unsigned_lit by lia; unfold HC_STACK; lia | bz_ceil; bz_params; unfold CEIL; lia | rewrite unsigned_lit by lia; exact AL16
        | exact CX | exact SEP | exact IMG | exact LAWS | exact HX ]. }
    cbn [ci_segs ci_handle_compress S0C]. clear EM AM CM SM OBM.
    destruct (handle_compress znew e z) as [[e' z'] pr] eqn:HCE.
    intros ms' PO. unfold handle_compress_postB in PO. rewrite HCE in PO. cbv beta iota in PO. revert ms' PO.
    post_callWB s0segs m.
    rewrite (ret_pc_even ret) by lia.
    match goal with H : emem _ _ _ _ _ |- _ => rename H into EM' end.
    match goal with H : amem _ _ _ _ |- _ => rename H into AM' end.
    match goal with H : cimg_mem _ _ _ |- _ => rename H into CM' end.
    match goal with H : rw_cells _ _ _ (STRMB _ _ _ _ _ _ _ _ _) |- _ => rename H into SM' end.
    match goal with H : u8arr _ _ _ (outb _ _) |- _ => rename H into OBM' end.
    match goal with H : u8ro _ _ _ _ |- _ => clear H end.
    match goal with H : z_in _ = _ |- _ => rename H into ZI' end.
    match goal with H : HCXB _ _ ?gg e' _ |- _ => rename H into HX'; rename gg into g' end.
    match goal with H : stk _ _ _ (bv_unsigned _) |- _ => rename H into ST'; rewrite unsigned_lit in ST' by lia end.
    match goal with H : mem_inv _ _ |- _ => rename H into MI' end.
    lazymatch type of MI' with mem_inv _ ?mm => specialize (K mm g') end. cbn [Z.b2z] in K |- *.
    destruct pr; (eapply K; [exact HX' | exact EM' | exact AM' | exact CM' | exact SM' | exact OBM' | exact ZI' | exact MI' | exact MU | exact WM | exact ST' | unfold FRAME; exact FR]).
  Qed.

  (* [comment removed for export] *)
  Lemma bzc_ret : forall (ret : Z) g' e' z' m j8
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
    bzCompress znew e0 z0 BZ_FINISH = (ret, e', z') ->
    est_ok e' ->
    (0 <= z_avail_out z' <= on /\ Z.of_nat (length (z_outr z')) = on - z_avail_out z')%Z ->
    emem cx s0segs g' e' m -> amem cx s0segs e' m -> cimg_mem S0C m sv ->
    rw_cells s0segs m (bz + 5016) (STRMB cx ob on dbza dbzfr z' (nin + (z_avail_in z0 - z_avail_in z')) p1 p2) ->
    u8arr s0segs m ob (outb (z_outr z') OB) ->
    mem_inv s0segs m -> munch W m0 m -> wmono s0segs m0 m -> stk s0segs m lo (usp - 32) -> rw_cells s0segs m (usp - 32) (FRAME j8) ->
    evt s0segs POST (MS (mkR xra (Z_to_bv 64 (usp - 32)) gp tp xt0 xt1 xt2 (Z_to_bv 64 ret) (Z_to_bv 64 E)
                            xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
                       F (Z_to_bv 64 0x13ed8) fc None m (seg_rom s0segs)).
  Proof.
    intros ret g' e' z' m j8 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 RES EOK' ZF EM AM CM SM OBM MI MU WM ST FR.
    prep. unfold FRAME in FR. pose proof (rw_cells_bound _ _ _ _ FR) as FRB. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FRB.
    pose proof (stk_lo_nonneg _ _ _ _ ST) as LONN.
    shelve_mem EM. shelve_mem AM. shelve_mem CM. shelve_mem SM. shelve_mem OBM.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. wstep. wstep.
    unshelve_mems.
    release_frame FR ST (bv_unsigned sp).
    replace (Z_to_bv 64 (usp - 32 + 32)) with sp by (rewrite <- (Z_to_bv_bv_unsigned sp) at 1; f_equal; lia).
    unfold bzCompress_postB. rewrite RES. finish.
    all: first [ exact EM | exact AM | exact CM | exact SM | exact OBM | exact EOK' | exact ZF | exact (proj1 ZF) | exact (proj2 ZF) | exact (proj1 (proj1 ZF)) | exact (proj2 (proj1 ZF))
               | (eapply u8ro_keep; [exact (hid_e _ PLM0) | exact MU | intros NE; exact (pay_disj_bzcB cx ob on nin _ usp lo (PAY NE) LO STK SA1)])
               | match goal with |- ?gg => idtac "LEFT:" gg end ].
  Qed.

  (* [comment removed for export] *)
  Lemma fin_epi : forall g' e' z' (pr : bool) (z1 : zstrm) m j8
      (xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
    bzCompress znew e0 z0 BZ_FINISH = bzc_finish_tail e' z' pr ->
    HCXB cx on g' e' z' -> z_avail_in z1 = z_avail_in z0 -> z_in z1 = z_in z0 ->
    emem cx s0segs g' e' m -> amem cx s0segs e' m -> cimg_mem S0C m sv ->
    rw_cells s0segs m (bz + 5016) (STRMB cx ob on dbza dbzfr z' (nin + (z_avail_in z1 - z_avail_in z')) p1 p2) ->
    u8arr s0segs m ob (outb (z_outr z') OB) ->
    z_in z' = skipn (Z.to_nat (z_avail_in z1 - z_avail_in z')) (z_in z1) ->
    mem_inv s0segs m -> munch W m0 m -> wmono s0segs m0 m -> stk s0segs m lo (usp - 32) -> rw_cells s0segs m (usp - 32) (FRAME j8) ->
    evt s0segs POST (MS (mkR (Z_to_bv 64 0x13f5c) (Z_to_bv 64 (usp - 32)) gp tp xt0 xt1 xt2 (Z_to_bv 64 (-1)) (Z_to_bv 64 E)
                            (Z_to_bv 64 (Z.b2z pr)) xa1 xa2 xa3 xa4 xa5 xa6 xa7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
                       F (Z_to_bv 64 0x13f5c) fc None m (seg_rom s0segs)).
  Proof.
    intros g' e' z' pr z1 m j8 xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 RES HX AI1 ZI1 EM AM CM SM OBM ZI MI MU WM ST FR.
    rewrite AI1 in SM, ZI. rewrite ZI1 in ZI.
    prep. pose proof (hlB_hci _ _ LAWS _ _ _ _ _ HX) as HI. hci_facts HI.
    assert (EOK' : est_ok e') by exact (HCIB_est_ok _ _ _ _ _ HI).
    unfold bzCompress_WB, ESTATE_SIZE, FTAB_WORDS, BZC_STACKB, BZF_STRM in MU.
    unfold FRAME in FR. pose proof (rw_cells_bound _ _ _ _ FR) as FRB. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FRB.
    pose proof (stk_lo_nonneg _ _ _ _ ST) as LONN.
    pose proof (outb_length_nat (z_outr z') OB ltac:(lia)) as LOBn. replace (length OB) with (Z.to_nat on) in LOBn by lia.
    destruct pr; cbn [Z.b2z].
    2:{ (* [comment removed for export] *)
        wstep; if_cases KP; zify_cond_z KP; [|exfalso; clear -KP; lia].
        unfold bzc_finish_tail in RES. cbn [negb] in RES.
        eapply (bzc_ret BZ_SEQUENCE_ERROR g' e' z' m j8); [exact RES | exact EOK' | split; [exact AOR | exact OLEN] | exact EM | exact AM | exact CM | exact SM | exact OBM | exact MI | exact MU | exact WM | exact ST | exact FR]. }
    wstep; if_cases KP; zify_cond_z KP; [exfalso; clear -KP; lia|].
    open_emem EM. unfold EHEAD1, EHEAD2 in EH1, EH2. unfold BZF_STRM in EH1, EH2. cbn_est_in EH1. cbn_est_in EH2.
    open_amem AM. unfold FTAB_WORDS in AR1, AR2, FTB. unfold STRMB in SM. cps_destruct CM as (CM1 & CM2 & CM3 & CM4). cbn [ci_segs ci_got ci_crc ci_crcx ci_stderrp S0C] in CM1, CM2, CM3, CM4.
    unfold bzc_finish_tail in RES. cbn [negb] in RES. unfold isempty_RL_e, isempty_RL, est_rl in RES. cbn_est_in RES.
    (* [comment removed for export] *)
    wstep. rewrite GA, AIE. bz32. wstep. wstep; if_cases KA; zify_cond_z KA.
    { (* [comment removed for export] *)
      rewrite AIE in RES. replace (0 <? z_avail_in z')%Z with true in RES by (symmetry; apply Z.ltb_lt; lia). cbn [orb] in RES.
      eapply (bzc_ret BZ_FINISH_OK g' e' z' _ j8); [exact RES | exact EOK' | split; [exact AOR | exact OLEN] | | eapply amem_intro; [exact AR1 | exact AR2 | exact FTB] | split; [exact CM1|]; split; [exact CM2|]; split; [exact CM3| exact CM4] | exact SM | exact OBM | exact MI | exact MU | exact WM | exact ST | exact FR].
      eapply emem_intro; [unfold EHEAD1; cbn_est; exact EH1 | exact INU | exact UNS
                           | unfold EHEAD2; cbn_est; exact EH2 | exact MTF | exact SEL | exact SLM | exact LEN | exact COD | exact RFQ | exact LNP]. }
    rewrite AIE in RES. replace (0 <? z_avail_in z')%Z with false in RES by (symmetry; apply Z.ltb_ge; lia). cbn [orb] in RES.
    (* [comment removed for export] *)
    wstep. wstep. wstep; if_cases KC; zify_cond_z KC.
    2:{ (* [comment removed for export] *)
        wstep. wstep; if_cases KL; zify_cond_z KL; [|exfalso; lia].
        replace (e_state_in_ch e' <? 256)%Z with true in RES by (symmetry; apply Z.ltb_lt; lia).
        replace (0 <? e_state_in_len e')%Z with true in RES by (symmetry; apply Z.ltb_lt; lia). cbn [negb andb orb] in RES.
        eapply (bzc_ret BZ_FINISH_OK g' e' z' _ j8); [exact RES | exact EOK' | split; [exact AOR | exact OLEN] | | eapply amem_intro; [exact AR1 | exact AR2 | exact FTB] | split; [exact CM1|]; split; [exact CM2|]; split; [exact CM3| exact CM4] | exact SM | exact OBM | exact MI | exact MU | exact WM | exact ST | exact FR].
        eapply emem_intro; [unfold EHEAD1; cbn_est; exact EH1 | exact INU | exact UNS
                           | unfold EHEAD2; cbn_est; exact EH2 | exact MTF | exact SEL | exact SLM | exact LEN | exact COD | exact RFQ | exact LNP]. }
    replace (e_state_in_ch e' <? 256)%Z with false in RES by (symmetry; apply Z.ltb_ge; lia). cbn [negb andb orb] in RES.
    (* [comment removed for export] *)
    wstep. wstep. wstep; if_cases KN; zify_cond_z KN.
    { replace (e_state_out_pos e' <? bw_numZ (e_bw e'))%Z with true in RES by (symmetry; apply Z.ltb_lt; lia).
      eapply (bzc_ret BZ_FINISH_OK g' e' z' _ j8); [exact RES | exact EOK' | split; [exact AOR | exact OLEN] | | eapply amem_intro; [exact AR1 | exact AR2 | exact FTB] | split; [exact CM1|]; split; [exact CM2|]; split; [exact CM3| exact CM4] | exact SM | exact OBM | exact MI | exact MU | exact WM | exact ST | exact FR].
      eapply emem_intro; [unfold EHEAD1; cbn_est; exact EH1 | exact INU | exact UNS
                           | unfold EHEAD2; cbn_est; exact EH2 | exact MTF | exact SEL | exact SLM | exact LEN | exact COD | exact RFQ | exact LNP]. }
    replace (e_state_out_pos e' <? bw_numZ (e_bw e'))%Z with false in RES by (symmetry; apply Z.ltb_ge; lia).
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. rewrite AIE in EH1.
    eapply (bzc_ret BZ_STREAM_END g' _ z' _ j8); [exact RES | | split; [exact AOR | exact OLEN] | | eapply amem_intro; [exact AR1 | exact AR2 | exact FTB] | split; [exact CM1|]; split; [exact CM2|]; split; [exact CM3| exact CM4] | exact SM | exact OBM | exact MI | exact MU | exact WM | exact ST | exact FR].
    { revert EOK'. unfold est_ok. cbn_est. unfold BZ_M_IDLE. clear. intros EOK'. decompose [and] EOK'; repeat apply conj; try assumption. left; reflexivity. }
    eapply emem_intro; [unfold EHEAD1; cbn_est; exact EH1 | exact INU | exact UNS
                           | unfold EHEAD2; cbn_est; exact EH2 | exact MTF | exact SEL | exact SLM | exact LEN | exact COD | exact RFQ | exact LNP].
  Qed.

  (* [comment removed for export] *)
  Lemma bzc_body : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    e_mode e0 = BZ_M_RUNNING -> e_state e0 = BZ_S_INPUT -> z_avail_in z0 = Z.of_nat (length pl) ->
    HCXB cx on (eg_set_aie g0) (e_finish e0 z0) z0 ->
    emem cx s0segs g0 e0 m0 -> amem cx s0segs e0 m0 -> cimg_mem S0C m0 sv ->
    rw_cells s0segs m0 (bz + 5016) (STRMB cx ob on dbza dbzfr z0 nin p1 p2) -> u8arr s0segs m0 ob OB ->
    mem_inv s0segs m0 -> stk s0segs m0 lo usp ->
    evt s0segs POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (bz + 5016)) (Z_to_bv 64 BZ_FINISH) a2 a3 a4 a5 a6 a7
                            s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x13ea0) fc None m0 (seg_rom s0segs)).
  Proof.
    intros t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 MR STI0 AVL HX EM AM CM SM OBM MI ST.
    prep. pose proof (hlB_hci _ _ LAWS _ _ _ _ _ HX) as HI. hci_facts HI.
    unfold e_finish in *. cbn_est_in AIL. cbn_est_in AIR. cbn_est_in BOK1. cbn_est_in BOK2. cbn_est_in NBR. cbn_est_in CHR. cbn_est_in LENR. cbn_est_in CRCR. cbn_est_in CCR. cbn_est_in BNO. cbn_est_in NZ0. cbn_est_in POSR.
    pose proof (munch_refl W m0) as MU. unfold bzCompress_WB, ESTATE_SIZE, FTAB_WORDS, BZC_STACKB, BZF_STRM in MU.
    pose proof (wmono_refl s0segs m0) as WM.
    pose proof (munch_refl [(usp - 32, usp); (E, E + 128)]%Z m0) as MUf. pose proof WM as WMf.
    open_emem EM. unfold EHEAD1 in EH1. unfold BZF_STRM in EH1. cbn_est_in EH1. unfold STRMB in SM.
    open_amem AM. unfold FTAB_WORDS in AR1, AR2, FTB.
    cps_destruct CM as (CM1 & CM2 & CM3 & CM4). cbn [ci_segs ci_got ci_crc ci_crcx ci_stderrp S0C] in CM1, CM2, CM3, CM4.
    shelve_mem INU. shelve_mem UNS. shelve_mem EH2. shelve_mem MTF. shelve_mem SEL. shelve_mem SLM. shelve_mem LEN. shelve_mem COD. shelve_mem RFQ. shelve_mem LNP.
    shelve_mem AR1. shelve_mem AR2. shelve_mem FTB. shelve_mem CM1. shelve_mem CM2. shelve_mem CM3. shelve_mem CM4. shelve_mem OBM.
    (* [comment removed for export] *)
    carve_frame 32%nat ST.
    wstep. wstep. wstep. wstep.
    replace (usp + -32)%Z with (usp - 32)%Z in * by lia.
    (* [comment removed for export] *)
    wstep. wstep; if_cases KZ; zify_cond_z KZ; [exfalso; lia|].
    pose proof (cctx_al8 cx CX) as ALe.
    assert (LA0 : Z.land (bz + 5016) 7 = 0%Z) by (apply land7_8; lia).
    assert (LA1 : Z.land E 7 = 0%Z) by (apply land7_8; lia).
    wstep. try rewrite LA0. wstep; notrap.
    (* [comment removed for export] *)
    wstep. wstep; if_cases KS; zify_cond_z KS; [exfalso; clear -KS RE1; lia|].
    wstep. try rewrite LA1. wstep; notrap.
    (* [comment removed for export] *)
    wstep. wstep; if_cases KE; zify_cond_z KE; [|exfalso; clear -KE; lia].
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep.
    (* [comment removed for export] *)
    unfold BZ_M_RUNNING in MR. rewrite MR. unfold BZ_FINISH.
    wstep; if_cases K1; zify_cond_z K1; [exfalso; clear -K1; lia|].
    wstep; if_cases K2; zify_cond_z K2; [exfalso; clear -K2; lia|].
    wstep; if_cases K3; zify_cond_z K3; [exfalso; clear -K3; lia|].
    wstep. wstep. wstep. rewrite AVL. bz32. rewrite <- AVL. wstep. wstep.
    (* [comment removed for export] *)
    wstep; if_cases K4; zify_cond_z K4; [exfalso; clear -K4; lia|].
    wstep. wstep; if_cases K5; zify_cond_z K5; [exfalso; clear -K5; lia|].
    wstep. wstep; if_cases K6; zify_cond_z K6; [exfalso; clear -K6; lia|].
    wstep. wstep; if_cases K7; zify_cond_z K7; [exfalso; clear -K7; lia|].
    (* [comment removed for export] *)
    wstep. wstep. wstep; if_cases K8; zify_cond_z K8; [exfalso; clear -K8; lia|].
    wstep. rewrite AVL. bz32. rewrite <- AVL. wstep. rewrite AVL. bz32. rewrite <- AVL. wstep; if_cases K9; zify_cond_z K9; [exfalso; clear -K9; lia|].
    wstep.
    unshelve_mems. lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m' _) => transport_after_call s0segs m0 m' MUf WMf end. clear MUf WMf.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m' _) =>
    eapply (call_hc POST (eg_set_aie g0) (e_finish e0 z0) z0 m' 0x13f5c);
      [ lia | reflexivity | exact HX | reflexivity | reflexivity | exact OUT0 | exact AOUT0
      | eapply emem_intro; [unfold EHEAD1, e_finish; cbn_est; cbn [g_aie g_sort g_mtf g_zbits eg_set_aie]; first [exact EH1 | cells_eq_by EH1] | exact INU | exact UNS
                           | unfold EHEAD2, e_finish; cbn_est; cbn [g_bs g_mtf eg_set_aie]; exact EH2 | exact MTF | exact SEL | exact SLM | exact LEN | exact COD | exact RFQ | exact LNP]
      | eapply amem_intro; [exact AR1 | exact AR2 | exact FTB] | split; [exact CM1|]; split; [exact CM2|]; split; [exact CM3| exact CM4]
      | exact SM | exact OBM | exact MI | exact MU | exact WM | exact ST | unfold FRAME; exact FR | ] end.
    intros m' g' xt0' xt1' xt2' xa1' xa2' xa3' xa4' xa5' xa6' xa7' xt3' xt4' xt5' xt6'.
    destruct (handle_compress znew (e_finish e0 z0) z0) as [[e' z'] pr] eqn:HCE.
    intros HX' EM' AM' CM' SM' OBM' ZI' MI' MU' WM' ST' FR'.
    clear EH1 INU UNS EH2 MTF SEL SLM LEN COD RFQ LNP AR1 AR2 FTB CM1 CM2 CM3 CM4 SM OBM MI MU WM ST FR.
    eapply (fin_epi g' e' z' pr z0 m'); [rewrite (bzCompress_finish_runningB znew e0 z0 ltac:(exact MR)), HCE; reflexivity
      | exact HX' | reflexivity | reflexivity | exact EM' | exact AM' | exact CM' | exact SM' | exact OBM' | exact ZI' | exact MI' | exact MU' | exact WM' | exact ST' | exact FR'].
  Qed.

End BZC.

Theorem S0_bzCompressB : forall HCXB CBFACTS, compressBlock_spec CBFACTS S0C -> bzCompress_specB HCXB CBFACTS S0C.
Proof.
  intros HCXB CBFACTS CBS. unfold bzCompress_specB. cbn [ci_segs ci_bzCompress S0C]. intros until lo.
  intros A0 A1 MR STI AVL OUT0 AOUT0 EM AM CM SM SOK OBM LOB OOK PLM ZIN PAY MI ST STK LO AL CX SEP IMG LAWS HX. subst a0 a1.
  destruct (mod16_lin _ AL) as [qsp ALQ].
  eapply (bzc_body HCXB CBFACTS CBS ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m cx g e z nin pl OB p1 p2 sv lo qsp ob on dbza dbzfr);
    [ unfold bzc_sec; repeat (split; [assumption|]); assumption
    | exact MR | exact STI | exact AVL | exact HX | exact EM | exact AM | exact CM | exact SM | exact OBM | exact MI | exact ST ].
Qed.

End ACeilS1.
