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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_FKit LbB_MILB LbB_PrsStmt LbB_Own LbB_PmBase LbB_FSlots LbB_PmOwn LbB_PmCut LbB_PmTac LbB_PmHdr LbB_PmCall LbB_PmXp LbB_PmExit LbB_PmInit LbB_PmFin LbB_PmExit2 LbB_DiagStmt LbB_PmDS LbB_PmGlue.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_PmHdr2.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require TablRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_SR LbB_Conv LbB_MILB LbB_PrsStmt LbB_HKit LbB_HStKit LbB_PmExit LbB_PiStmt LbB_PiInit LbB_PmTac.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_ContStmt LbB_RwStm LbB_PmHTK LbB_PmMagRS.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_WoGen LbB_WoDefs LbB_WoKit LbB_WoBP LbB_PmMagK LbB_Own LbB_RwStm LbB_PmMagRS LbB_PmMagW LbB_PmHTK LbB_FSlots LbB_PmHdr2.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_TablImg.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BakeStackRep.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Lemma rdn1_of_mdef : forall m a, mdef m a 1 -> 0 <= a -> a + 1 < 2 ^ 64 ->
  exists b, PropExec.rdn asegs m (Z_to_bv 64 a) 1 = Some [b].
Proof.
  intros m a MD H0 H1. pose proof (MD 0 ltac:(lia)) as D. rewrite Z.add_0_r in D.
  destruct (m (Z_to_bv 64 a)) as [b|] eqn:E; [| contradiction].
  exists b. cbn [PropExec.rdn]. rewrite E. reflexivity.
Qed.

Section Mag.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.

  Lemma HHmg : asan_rt_hyps H. Proof. exact (proj1 HHbp). Qed.

  Lemma nth_error_map_b8 : forall (l : list Z) i, (i < length l)%nat ->
    nth_error (map (Z_to_bv 8) l) i = Some (Z_to_bv 8 (nth i l 1)).
  Proof.
    induction l as [|z l IH]; intros i Hi; [cbn in Hi; lia|].
    destruct i as [|i]; cbn; [reflexivity | apply IH; cbn in Hi; lia].
  Qed.

  Lemma shad_upd14 : forall ff m M', 0 <= ff -> ff <= 2 ^ 47 -> bp_shad ff [20; 21]%nat m ->
    munch [(sh ff + 216, sh ff + 218)] m M' -> wmono asegs m M' ->
    fldA M' (sh ff + 216) 1 0 -> fldA M' (sh ff + 217) 1 0 -> bp_shad ff [14; 20; 21]%nat M'.
  Proof.
    intros ff m M' H0 H47 SH MU WM F6 F7. unfold bp_shad in *.
    destruct SH as [(B0 & B1 & B) WR].
    assert (L1 : length (wo_sh [20; 21]%nat) = 476%nat) by (vm_compute; reflexivity).
    assert (L2 : length (wo_sh [14; 20; 21]%nat) = 476%nat) by (vm_compute; reflexivity).
    assert (CHK : forallb (fun i => orb (orb (Nat.eqb i 216) (Nat.eqb i 217))
                    (Z.eqb (nth i (wo_sh [14; 20; 21]%nat) 1) (nth i (wo_sh [20; 21]%nat) 1))) (seq 0 476) = true)
      by (vm_compute; reflexivity).
    rewrite forallb_forall in CHK.
    split.
    - split; [exact B0 |]. split; [rewrite length_map, L2; rewrite length_map, L1 in B1; exact B1 |].
      intros i Hi. rewrite length_map, L2 in Hi.
      rewrite (nth_error_map_b8 _ i ltac:(rewrite L2; lia)).
      destruct (Nat.eq_dec i 216) as [->|N1].
      { replace (nth 216 (wo_sh [14; 20; 21]%nat) 1) with 0 by (vm_compute; reflexivity).
        unfold fldA, fld in F6. change (word_to_le_bytes 1 (Z_to_bv 64 0)) with [Z_to_bv 8 0] in F6.
        apply LbB_TablImg.mrd_of_rdn1. unfold wa. change (Z.of_nat 216) with 216. exact F6. }
      destruct (Nat.eq_dec i 217) as [->|N2].
      { replace (nth 217 (wo_sh [14; 20; 21]%nat) 1) with 0 by (vm_compute; reflexivity).
        unfold fldA, fld in F7. change (word_to_le_bytes 1 (Z_to_bv 64 0)) with [Z_to_bv 8 0] in F7.
        apply LbB_TablImg.mrd_of_rdn1. unfold wa. change (Z.of_nat 217) with 217. exact F7. }
      pose proof (CHK i ltac:(apply in_seq; lia)) as Ci.
      apply Bool.orb_prop in Ci as [Ci|Ci]; [apply Bool.orb_prop in Ci as [Ci|Ci]; apply Nat.eqb_eq in Ci; contradiction |].
      apply Z.eqb_eq in Ci. rewrite Ci, <- (nth_error_map_b8 _ i ltac:(rewrite L1; lia)).
      rewrite <- (B i ltac:(rewrite length_map, L1; lia)). unfold mrd, wa.
      rewrite (munch_at [(sh ff + 216, sh ff + 218)] m M' (sh ff + Z.of_nat i) MU).
      + reflexivity.
      + unfold sh in *. rewrite ASHADOW_BASE_val in *. pose proof (Z.div_pos ff 8 ltac:(lia) ltac:(lia)).
        assert (ff / 8 <= ff) by (apply Z.div_le_upper_bound; lia). lia.
      + intros iv Hiv. cbn in Hiv. destruct Hiv as [<-|[]]. cbn [fst snd]. lia.
    - rewrite length_map, L2. rewrite length_map, L1 in WR. exact (wr_at_wmono _ _ _ _ WR WM).
  Qed.
  Lemma pm_hdr_a2 : forall e ff fp Q mo0, w_words e <> 0 -> 5 <= w_n e ->
    bp_kmag H e ff fp Q mo0 -> bp_khdr H e ff fp Q mo0.
  Proof.
    intros e ff fp Q mo0 HW HN K.
    unfold bp_khdr, bp_hdr0. intros s LB LBs m mo msF R F fc XSc w c VIS RF FZ KR MP HP HI SL SH RC RR WL PF.
    pose proof (hdr_geo H e ff fp XSc s LB m HP HI) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16).
    pose proof HI as (RFS & FF & RH & AC & MI & S0 & RA & ER & ST & SV & SF & WF & WFP & XP & FS & LVI).
    destruct (hdr_words H HHmg e ff fp XSc s LB m HP HI HW HN) as (W16le & W16 & WHI & SHw & _).
    pose proof HP as (_ & _ & N24 & _).
    set (q := ff / 32).
    assert (Hq : ff = 32 * q) by (subst q; clear - G1; Z.div_mod_to_equations; lia).
    assert (SHq : sh ff = 4 * q + 2147450880).
    { unfold sh. rewrite ASHADOW_BASE_val, Hq. replace (32 * q) with ((4 * q) * 8) by ring. rewrite Z.div_mul by lia. lia. }
    pose proof WL as (Wp & Wc & Ww & Wn & WLB & Ws0 & Wlo & WB & Wshi).
    pose proof PF as (PP & FR & AL & CC).
    pose proof PP as (PR & PSH & HC & HU & HD & SOWN & LBOWN & CWR).
    pose proof PR as [_ _ _ _ _ Pst _ _ _ _ _ _]. destruct Pst as [W0 W1 _ _ _ _ _ _ _ _ _ _ _ _ _ _].
    pose proof FR as (PH & _). unfold pi_hdr in PH. cbn [bp_ste st_words st_nwords] in PH. destruct PH as (PW0 & PW1 & _).
    destruct RC as (Rc2 & Rc3 & Rc4 & Rc8 & Rc9 & Rc19 & Rc20).
    destruct RR as (M18 & M21 & M22 & M23 & M24 & M25 & M26 & M27).
    destruct SL as (SL1 & SL2 & SL3).
    pose proof (proj1 (rw_cells_app asegs m (wS1 e + 24) [C8 (wz (w_words e)); C8 (wz (w_n e))]
                  [C8 (wz ASHADOW_BASE); C8 (wz (ff + 2224)); C8 (wz (ff + 3376))]) SL2) as (_ & SL2b).
    pose proof (proj1 (rw_cells_app asegs m _ [C8 (wz ASHADOW_BASE)] [C8 (wz (ff + 2224)); C8 (wz (ff + 3376))]) SL2b) as (SL2c & _).
    pose proof (rdn_of_rw_C8 m _ _ SL2c) as RDS.
    pose proof SH as [_ SHW]. rewrite length_map in SHW.
    replace (Z.of_nat (length (wo_sh [20; 21]%nat))) with 476 in SHW by (vm_compute; reflexivity).
    destruct ST as (T0 & T1 & T).
    assert (PRE : hdrR_a2_pre R m q (wS1 e) (w_words e) (w_n e) (wS1 e)).
    { unfold hdrR_a2_pre.
      split; [exact Rc2 |]. split; [exact Rc9 |].
      split; [rewrite M18, Hq; reflexivity |].
      split; [rewrite Rc19, SHq, ASHADOW_BASE_val; reflexivity |].
      split; [rewrite Rc20, Hq; reflexivity |].
      split; [rewrite M22, Hq; reflexivity |].
      split; [unfold fldA, fld; replace (32 * q + 3504) with (pw_p H w + ST_OFF) by (rewrite Wp; unfold ST_OFF; lia);
              rewrite <- Ww, <- PW0; exact (proj2 W0) |].
      split; [unfold fldA, fld; replace (32 * q + 3512) with (pw_p H w + ST_OFF + 8) by (rewrite Wp; unfold ST_OFF; lia);
              rewrite <- Wn, <- PW1; exact (proj2 W1) |].
      split; [unfold fldA, fld; replace (wS1 e + 40) with (wS1 e + 24 + Z.of_nat (cells_size [C8 (wz (w_words e)); C8 (wz (w_n e))])) by (cbn; lia);
              exact RDS |].
      split; [replace (4 * q + 2147451096) with (sh ff + 216) by (rewrite SHq; lia); apply (wr_at_sub m (sh ff) 476); [exact SHW | lia | lia | lia] |].
      split; [lia |]. split; [lia |]. split; [lia |]. split; [lia |]. split; [lia |].
      split; [lia |]. split; [lia |]. split; [lia |]. split; [lia |].
      destruct G6 as [G6|G6]; unfold aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in G6; lia. }
    eapply (hdr_a2_sr H HHmg s msF mo R F fc m q (wS1 e) (w_words e) (w_n e) (wS1 e) Q KR); [rewrite VIS; reflexivity | exact RF | exact PRE |].
    intros msF1 mo1 R' M' KR1 MP1 VIS1 RF1 PST. unfold hdrR_a2_post in PST.
    destruct PST as (MS & MU & WM & F217 & F216 & G2' & G9' & G10' & G11' & _ & G18' & G19' & G20' & G22' & G25' & G27' & KEEP).
    replace (4 * q + 2147451096) with (sh ff + 216) in MU, F216 by (rewrite SHq; lia).
    replace (4 * q + 2147451098) with (sh ff + 218) in MU by (rewrite SHq; lia).
    replace (4 * q + 2147451097) with (sh ff + 217) in F217 by (rewrite SHq; lia).
    rewrite <- Hq in G18', G20', G22', G25'. rewrite SHq in Rc19.
    set (W := [(sh ff + 216, sh ff + 218)]) in MU.
    assert (MI' : mem_inv asegs M') by exact (msteps_mem_inv asegs _ _ MS MI).
    assert (ST' : stk asegs M' (w_lo e) (wSP e)) by (apply (stk_keepW W m M'); [split; [exact T0 | split; [exact T1 | exact T]] | exact MU | exact WM | unfold AIMG_TOP; lia]).
    assert (FW : Forall (wwin H e ff) W) by (subst W; repeat constructor; unfold wwin; cbn [fst snd]; lia).
    assert (HI' : winv H e ff fp XSc s LB M') by exact (winv_munch H HHmg e ff fp XSc s LB m M' W HP HI MU WM MI' ST' FW).
    assert (FL : Forall (bp_flw H e ff) W).
    { subst W. constructor; [| constructor]. unfold bp_flw; cbn [fst snd]. split; [right; left; lia | unfold sh in *; lia]. }
    unfold bp_kmag, bp_hdr0 in K.
    apply (K s LB LBs M' mo1 msF1 R' F fc XSc w c).
    - rewrite VIS1. reflexivity.
    - exact RF1.
    - exact FZ.
    - exact KR1.
    - exact (ah_mpres_trans H HHmg mo0 mo mo1 MP MP1).
    - exact HP.
    - exact HI'.
    - split; [| split].
      + eapply rw_cells_transport; [exact SL1 | exact MU | exact WM |]. subst W. cbn. unfold sh in *. lia.
      + eapply rw_cells_transport; [exact SL2 | exact MU | exact WM |]. subst W. cbn. unfold sh in *. lia.
      + eapply rw_cells_transport; [exact SL3 | exact MU | exact WM |]. subst W. cbn. unfold sh in *. lia.
    - apply (shad_upd14 ff m M'); [lia | lia | exact SH | exact MU | exact WM | exact F216 | exact F217].
    - split; [exact G2' |].
      split; [etransitivity; [exact (KEEP 3%bv ltac:(repeat (first [left; reflexivity | right]))) | exact Rc3] |].
      split; [etransitivity; [exact (KEEP 4%bv ltac:(repeat (first [left; reflexivity | right]))) | exact Rc4] |].
      split; [etransitivity; [exact (KEEP 8%bv ltac:(repeat (first [left; reflexivity | right]))) | exact Rc8] |].
      split; [exact G9' |].
      split; [rewrite SHq; exact G19' | exact G20'].
    - split; [exact G10' |]. split; [exact G11' |]. split; [exact G18' |].
      split; [etransitivity; [exact (KEEP 21%bv ltac:(repeat (first [left; reflexivity | right]))) | exact M21] |].
      split; [exact G22' |].
      split; [etransitivity; [exact (KEEP 23%bv ltac:(repeat (first [left; reflexivity | right]))) | exact M23] |].
      split; [etransitivity; [exact (KEEP 24%bv ltac:(repeat (first [left; reflexivity | right]))) | exact M24] |].
      split; [exact G25' |].
      split; [etransitivity; [exact (KEEP 26%bv ltac:(repeat (first [left; reflexivity | right]))) | exact M26] |].
      exact G27'.
    - exact WL.
    - split; [| split; [exact HW | exact HN]].
      split; [exact (bp_pp_keepW H HHmg e ff fp XSc w s LB LBs m M' c W HP HI WL PP MU WM FL) |].
      split; [exact FR |]. split; [exact AL |].
      eapply rw_cells_transport; [exact CC | exact MU | exact WM |]. rewrite Wc. subst W. cbn. unfold sh in *. lia.
  Qed.
End Mag.

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_PmBMC1.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_PmBMC2.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_PmIH.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_PmMM.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_DStat LbB_DiagStmt.

Section MagB.
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
  Hypothesis HU64 : put_u64_stmtA H LINV_P5 ds_repA.
  Hypothesis HTR : pm_tr_ok H.

  Lemma HHmb : asan_rt_hyps H. Proof. exact (proj1 HHbp). Qed.

  Lemma pm_magic : forall e ff fp Q mo0, hdr_good_K H e ff fp Q mo0 -> bp_kmagf H e ff fp Q mo0 -> bp_kmag H e ff fp Q mo0.
  Proof.
    intros e ff fp Q mo0 KG KF. unfold bp_kmag, bp_hdr0.
    intros s LB LBs m mo msF R F fc XSc w c VIS RF FZ KR MP HP HI SL SH RC RM WL (PF & HW & HN).
    destruct (hdr_words H HHmb e ff fp XSc s LB m HP HI HW HN) as (_ & _ & _ & _ & b0 & b1 & b2 & b3 & R0 & R1 & R2 & R3).
    pose proof (conj PF (conj HW (conj HN (conj R0 (conj R1 (conj R2 R3)))))) as ST.
    destruct (Z.eq_dec (bv_unsigned b0) 3) as [E0|E0].
    - destruct (Z.eq_dec (bv_unsigned b1) 2) as [E1|E1].
      + destruct (Z.eq_dec (bv_unsigned b2) 35) as [E2|E2].
        * destruct (Z.eq_dec (bv_unsigned b3) 7) as [E3|E3].
          -- exact (pm_hdr_b_le H HHmb e ff fp Q mo0 b0 b1 b2 b3 E0 E1 E2 E3 KG s LB LBs m mo msF R F fc XSc w c VIS RF FZ KR MP HP HI SL SH RC RM WL ST).
          -- exact ((LbB_PmBMC2.pm_bm_30 H HHbp ds_repA DSL HCTOR HCSEQ HDTOR HU32 HTR) e ff fp Q mo0 b0 b1 b2 b3 E0 E1 E2 E3 KF s LB LBs m mo msF R F fc XSc w c VIS RF FZ KR MP HP HI SL SH RC RM WL ST).
        * exact ((LbB_PmBMC2.pm_bm_20 H HHbp ds_repA DSL HCTOR HCSEQ HDTOR HU32 HTR) e ff fp Q mo0 b0 b1 b2 b3 E0 E1 E2 KF s LB LBs m mo msF R F fc XSc w c VIS RF FZ KR MP HP HI SL SH RC RM WL ST).
      + exact ((LbB_PmBMC2.pm_bm_10 H HHbp ds_repA DSL HCTOR HCSEQ HDTOR HU32 HTR) e ff fp Q mo0 b0 b1 b2 b3 E0 E1 KF s LB LBs m mo msF R F fc XSc w c VIS RF FZ KR MP HP HI SL SH RC RM WL ST).
    - destruct (Z.eq_dec (bv_unsigned b0) 7) as [F0|F0].
      + destruct (Z.eq_dec (bv_unsigned b1) 35) as [F1|F1].
        * destruct (Z.eq_dec (bv_unsigned b2) 2) as [F2|F2].
          -- destruct (Z.eq_dec (bv_unsigned b3) 3) as [F3|F3].
             ++ exact (pm_hdr_b_be H HHmb e ff fp Q mo0 b0 b1 b2 b3 F0 F1 F2 F3 KG s LB LBs m mo msF R F fc XSc w c VIS RF FZ KR MP HP HI SL SH RC RM WL ST).
             ++ exact ((LbB_PmBMC1.pm_bm_03 H HHbp ds_repA DSL HCTOR HCSEQ HDTOR HU32 HTR) e ff fp Q mo0 b0 b1 b2 b3 E0 F0 F1 F2 F3 KF s LB LBs m mo msF R F fc XSc w c VIS RF FZ KR MP HP HI SL SH RC RM WL ST).
          -- exact ((LbB_PmBMC1.pm_bm_02 H HHbp ds_repA DSL HCTOR HCSEQ HDTOR HU32 HTR) e ff fp Q mo0 b0 b1 b2 b3 E0 F0 F1 F2 KF s LB LBs m mo msF R F fc XSc w c VIS RF FZ KR MP HP HI SL SH RC RM WL ST).
        * exact ((LbB_PmBMC1.pm_bm_01 H HHbp ds_repA DSL HCTOR HCSEQ HDTOR HU32 HTR) e ff fp Q mo0 b0 b1 b2 b3 E0 F0 F1 KF s LB LBs m mo msF R F fc XSc w c VIS RF FZ KR MP HP HI SL SH RC RM WL ST).
      + exact ((LbB_PmBMC1.pm_bm_00 H HHbp ds_repA DSL HCTOR HCSEQ HDTOR HU32 HTR) e ff fp Q mo0 b0 b1 b2 b3 E0 F0 KF s LB LBs m mo msF R F fc XSc w c VIS RF FZ KR MP HP HI SL SH RC RM WL ST).
  Qed.

  Lemma pm_hdr : forall e ff fp Q mo0, hdr_good_K H e ff fp Q mo0 -> bp_kmagf H e ff fp Q mo0 -> bp_kwcf H e ff fp Q mo0 ->
    bp_khdr H e ff fp Q mo0.
  Proof.
    intros e ff fp Q mo0 KG KF KW.
    destruct (Z.eq_dec (w_words e) 0) as [HW0|HW0].
    { exact (LbB_PmMM.pm_mm H HHbp ds_repA DSL HCTOR HCSEQ HDTOR HU32 HU64 HTR e ff fp Q mo0 HW0 KW). }
    destruct (Z_le_gt_dec (w_n e) 4) as [HN4|HN4].
    { exact (LbB_PmIH.pm_ih H HHbp ds_repA DSL HCTOR HCSEQ HDTOR HU32 HU64 HTR e ff fp Q mo0 HW0 HN4 KW). }
    exact (pm_hdr_a2 H HHbp e ff fp Q mo0 HW0 ltac:(lia) (pm_magic e ff fp Q mo0 KG KF)).
  Qed.
End MagB.
