(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame BCells BStep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 BsWalk RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_SR LbB_Conv.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_MILB LbB_PrsStmt LbB_StateStmt LbB_Own LbB_RtOwn LbB_HKit LbB_HStKit.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_WoGen LbB_WoDefs LbB_WoKit LbB_WoKit2 LbB_WoKit3 LbB_WoSt LbB_WoSt2 LbB_WoMs LbB_WoCall LbB_WoCut LbB_WoZ.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_WoR2 LbB_WoR3 LbB_WoR4 LbB_WoR5 LbB_WoE0 LbB_WoE0b LbB_WoQ LbB_WoS1 LbB_WoF LbB_WoVec.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_WoBP LbB_WoBPsh.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Lemma perm_wo6 : forall (A : Type) (a1 a2 a3 a4 a5 a6 : A) (L : list A),
  Permutation (a6 :: a5 :: a4 :: a3 :: a2 :: a1 :: L) (L ++ [a1; a2; a3] ++ [a4; a5; a6]).
Proof.
  intros A a1 a2 a3 a4 a5 a6 L. change (a6 :: a5 :: a4 :: a3 :: a2 :: a1 :: L) with (rev ([a1; a2; a3] ++ [a4; a5; a6]) ++ L).
  etransitivity; [apply Permutation_app_comm|]. apply Permutation_app_head. apply Permutation_sym. apply Permutation_rev.
Qed.
Lemma perm_wo3 : forall (A : Type) (a1 a2 a3 : A) (L : list A), Permutation (a3 :: a2 :: a1 :: L) ([a1; a2; a3] ++ L).
Proof.
  intros A a1 a2 a3 L. change (a3 :: a2 :: a1 :: L) with (rev [a1; a2; a3] ++ L). apply Permutation_app_tail.
  apply Permutation_sym. apply Permutation_rev.
Qed.

Section WoS3.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHb : asan_rt_hyps_bp H.
  Hypothesis HOWN : rt_own H.
  Hypothesis MVA : st_mva_stmt H.
  Hypothesis DTOR : st_dtor_stmt H.
  Hypothesis WTR : po_tr_ok H.
  Let HB := rt_bp_base H HHb.

  Ltac mpres_chain :=
    repeat match goal with
    | |- as_MPRES H ?a ?a => apply (ah_mpres_refl H HB)
    | K : as_MPRES H ?a ?b |- as_MPRES H ?a ?c => apply (ah_mpres_trans H HB a b c K)
    end.

  Lemma wtr_mva : st_mva_tr_ok H.
  Proof. destruct WTR as [_ F]. apply Forall_app in F as [F _]. exact F. Qed.
  Lemma wtr_dtor : st_dtor_tr_ok H.
  Proof. destruct WTR as [_ F]. apply Forall_app in F as [_ F]. apply Forall_app in F as [F _]. exact F. Qed.

  Lemma wscr_ff : forall (e : went H) ff fp mr XS a, wpre H e -> as_RFS H ((6, ff, fp) :: w_LF e) mr ->
    fresh_frame H (w_LF e) 6 ff fp -> Forall (fs_scratch H ((6, ff, fp) :: w_LF e)) XS -> ff <= a < ff + WO_FLAGP ->
    ~ rin_ivs XS a.
  Proof.
    intros e ff fp mr XS a HP RF FF FS Ha. pose proof (wpre_geo H e HP) as (CE & _).
    apply rin_ivs_none. eapply Forall_impl; [| exact FS]. intros iv FSi.
    destruct (wfsw_ok H HB e ff fp mr iv RF FF CE FSi) as (_ & _ & _ & _ & B5 & _). unfold WO_FLAGP in *. lia.
  Qed.

  Lemma wscr_blkA : forall (e : went H) ff fp mr XS s LB m p A n a, as_RFS H ((6, ff, fp) :: w_LF e) mr ->
    as_RHEAP H s LB m -> In (p, A, n) LB -> Forall (fs_scratch H ((6, ff, fp) :: w_LF e)) XS ->
    (A <= a < A + n \/ sh A <= a < sh A + nsh n) -> ~ rin_ivs XS a.
  Proof.
    intros e ff fp mr XS s LB m p A n a RF RH IN FS Ha.
    apply rin_ivs_none. eapply Forall_impl; [| exact FS]. intros iv FSi.
    destruct (wscr_blk H HB _ s LB mr m p A n iv RF RH IN FSi) as [K1 K2]. lia.
  Qed.

  Lemma wS1cell_xp : forall (e : went H) ff fp LB XO XS mr m m' a cs,
    wpre H e -> as_RFS H ((6, ff, fp) :: w_LF e) mr -> fresh_frame H (w_LF e) 6 ff fp ->
    xpres H LB (wS1 e) (XO ++ XS) m m' -> Forall (fs_scratch H ((6, ff, fp) :: w_LF e)) XS ->
    Forall (fun iv : Z * Z => a + Z.of_nat (cells_size cs) <= fst iv \/ snd iv <= a) XO ->
    wS1 e <= a -> rw_cells asegs m a cs -> rw_cells asegs m' a cs.
  Proof.
    intros e ff fp LB XO XS mr m m' a cs HP RF FF XP FS FXO Ha C.
    pose proof (wpre_geo H e HP) as (CE & _). pose proof (wS1_facts H e HP) as (_ & _ & _ & _ & LOS1 & _).
    eapply xpres_rw_cells; [exact XP | exact C |]. split; [left; exact Ha|].
    apply Forall_app. split; [exact FXO|]. eapply Forall_impl; [| exact FS]. intros iv FSi.
    destruct (wfsw_ok H HB e ff fp mr iv RF FF CE FSi) as (_ & _ & _ & _ & _ & _ & B7 & _). right. lia.
  Qed.

  Lemma wstate_xp : forall (e : went H) ff fp s LB LB' XO XS mr m m' c st,
    wpre H e -> as_RFS H ((6, ff, fp) :: w_LF e) mr -> fresh_frame H (w_LF e) 6 ff fp -> as_RHEAP H s LB m ->
    xpres H LB (wS1 e) (XO ++ XS) m m' -> Forall (fs_scratch H ((6, ff, fp) :: w_LF e)) XS ->
    ff <= st -> st + ST_SIZE <= ff + WO_FLAGP ->
    Forall (fun iv : Z * Z => aceil <= fst iv \/ (ff <= fst iv /\ snd iv <= ff + WO_FLAGP /\ (snd iv <= st \/ st + ST_SIZE <= fst iv))) XO ->
    (forall p n, In (p, n) (state_blocks c) -> In (p, n) (lbl LB) /\ In (p, n) (lbl LB')) ->
    state_repA LB m st c -> state_sh m c -> state_repA LB' m' st c /\ state_sh m' c.
  Proof.
    intros e ff fp s LB LB' XO XS mr m m' c st HP RF FF RH XP FS ST1 ST2 FXO BL R S.
    pose proof (wframe_facts H _ _ _ FF) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16).
    pose proof (wS1_facts H e HP) as (S32 & S1SP & S1L & SPH & LOS1 & CEL).
    pose proof aceil_facts as ACF.
    assert (SHC : sh aceil < aceil) by (unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (SHL : ALOWSH_LO <= sh AIMG_TOP) by (unfold sh, ALOWSH_LO, AIMG_TOP; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (BLO : forall p n, In (p, n) (state_blocks c) -> 0 < p /\ p mod 16 = 0 /\ 0 <= n /\ p + n <= aceil /\ sh p + nsh n <= sh aceil
                                                           /\ (p + n + 16 <= as_FSB H \/ as_FSB H + AFS_SIZE <= p - 16)
                                                           /\ sh AIMG_TOP <= sh p /\ sh aceil < AHI_LO /\ exists q, In (q, p, n) LB).
    { intros p n Hin. destruct (BL p n Hin) as [L1 _]. destruct (lbl_in_inv _ _ _ L1) as (q & Hq).
      pose proof (ah_blocks H HB _ _ _ _ RH Hq) as (B0 & B16 & Bn & BI & BC & BF & BAPP). cbn in B0, B16, Bn, BI, BC, BF, BAPP.
      destruct (sh_aapp_range _ _ BAPP Bn) as (X1 & X2 & X3).
      split; [exact B0|]. split; [exact B16|]. split; [exact Bn|]. split; [exact BC|]. split; [exact X2|]. split; [exact BF|].
      split; [exact X1|]. split; [exact X3|]. exists q. exact Hq. }
    assert (NXO1 : forall a, st <= a < st + ST_SIZE -> ~ rin_ivs XO a).
    { intros a Ha. apply rin_ivs_none. eapply Forall_impl; [| exact FXO]. intros iv K. cbn in K. unfold ST_SIZE, WO_FLAGP in *. lia. }
    assert (NXO2 : forall a, (a < ff \/ ff + WO_FLAGP <= a) -> a < aceil -> ~ rin_ivs XO a).
    { intros a Ha Hb. apply rin_ivs_none. eapply Forall_impl; [| exact FXO]. intros iv K. cbn in K. unfold WO_FLAGP in *. lia. }
    assert (FAP : as_FSB H + AFS_SIZE <= ALOWSH_LO \/ AHI_LO <= as_FSB H) by (unfold aapp, aapp_lo, aapp_hi in F10; lia).
    split.
    - eapply (rep_keep H LB LB' LB (wS1 e) (XO ++ XS) m m' st c R XP).
      + apply (objx_intro H). { left. unfold ST_SIZE, WO_FLAGP in *. lia. }
        intros a Ha _ R0. apply rin_ivs_app in R0. destruct R0 as [R0|R0]; [exact (NXO1 a ltac:(unfold ST_SIZE in *; lia) R0)|].
        exact (wscr_ff e ff fp mr XS a HP RF FF FS ltac:(unfold ST_SIZE, WO_FLAGP in *; lia) R0).
      + apply (blkx_intro H). intros p n Hin. destruct (BL p n Hin) as [L1 L2]. split; [exact L1|]. split; [exact L2|].
        intros a Ha R0. destruct (BLO p n Hin) as (B0 & B16 & Bn & BC & BS & BF & BX1 & BX3 & q & Hq).
        apply rin_ivs_app in R0. destruct R0 as [R0|R0]; [exact (NXO2 a ltac:(unfold WO_FLAGP in *; lia) ltac:(lia) R0)|].
        exact (wscr_blkA e ff fp mr XS s LB m q p n a RF RH Hq FS (or_introl Ha) R0).
      + unfold AIMG_TOP, ST_SIZE, WO_FLAGP in *. lia.
      + destruct ACF as ((ACe1 & ACe2) & ACe3 & ACe4). unfold ST_SIZE, WO_FLAGP in *. lia.
    - eapply (sh_keep H LB LB (wS1 e) (XO ++ XS) m m' st c R S XP).
      apply (blksh_intro H). intros p n Hin. destruct (BL p n Hin) as [L1 L2]. split; [exact L1|].
      intros a Ha R0. destruct (BLO p n Hin) as (B0 & B16 & Bn & BC & BS & BF & BX1 & BX3 & q & Hq).
      apply rin_ivs_app in R0. destruct R0 as [R0|R0]; [exact (NXO2 a ltac:(unfold WO_FLAGP in *; lia) ltac:(lia) R0)|].
      exact (wscr_blkA e ff fp mr XS s LB m q p n a RF RH Hq FS (or_intror Ha) R0).
  Qed.

  Lemma wmva : forall (e : went H) ff fp XSc s LB (LBs1 LBs2 : list block) (c1 c2 : stateC) m msF mo (Q : config -> Prop) (d sr : Z)
      (ra t0 t1 t2 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
    wpre H e -> winv H e ff fp XSc s LB m ->
    ff + 8 <= d -> d + ST_SIZE <= ff + WO_FLAGP -> ff + 8 <= sr -> sr + ST_SIZE <= ff + WO_FLAGP -> d + ST_SIZE <= sr \/ sr + ST_SIZE <= d ->
    addressable m d ST_SIZE -> addressable m sr ST_SIZE ->
    as_VIS H s msF = MS (mkR ra (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) t0 t1 t2 (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
                           (Z_to_bv 64 d) (Z_to_bv 64 sr) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 AST_MVA) fc None m (seg_rom asegs) ->
    frm_zero fc -> bv_unsigned ra mod 2 = 0 ->
    as_AKREL H s (mkCfg msF mo) -> 0 <= as_AL H s ->
    state_repA LB m d c1 -> state_sh m c1 -> state_repA LB m sr c2 -> state_sh m c2 ->
    Permutation LB (w_LB e ++ LBs1 ++ LBs2) -> Permutation (lbl LBs1) (state_blocks c1) -> Permutation (lbl LBs2) (state_blocks c2) ->
    (forall p n, In (p, n) (state_blocks c1) -> n <= 2 ^ 40) ->
    (forall msF' mo' s' LB' m' XS (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32),
       as_VIS H s' msF' = MS (mkR ra (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) t0' t1' t2' (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
                                (Z_to_bv 64 d) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                          F' (ret_pc ra) fc' None m' (seg_rom asegs) ->
       frm_zero fc' -> as_AKREL H s' (mkCfg msF' mo') -> as_MPRES H mo mo' ->
       winv H e ff fp (XSc ++ XS) s' LB' m' ->
       xpres H (w_LB e) (wS1 e) ((d, d + ST_SIZE) :: (sr, sr + ST_SIZE) :: XS) m m' ->
       Forall (fs_scratch H ((6, ff, fp) :: w_LF e)) XS ->
       Permutation LB' (w_LB e ++ LBs2) ->
       state_repA LB' m' d (state_moved c1 c2) -> state_sh m' (state_moved c1 c2) ->
       state_repA LB' m' sr (state_emptied c2) ->
       as_AL H s' >= as_AL H s ->
       as_SR H Q (mkCfg msF' mo')) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros e ff fp XSc s LB LBs1 LBs2 c1 c2 m msF mo Q d sr ra t0 t1 t2 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
      HP HI D1 D2 R1b R2b DJ AD1 AD2 VIS FZ RA2 KR AL0 R1 SH1 R2 SH2 PLB P1 P2 CAP K.
    pose proof (wpre_geo H e HP) as (CE & LO & SSHI & SHIH & SP16 & TP).
    pose proof (wS1_facts H e HP) as (S32 & S1SP & S1L & SPH & LOS1 & _).
    pose proof (wframe_facts H _ _ _ (winv_ff H _ _ _ _ _ _ _ HI)) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16).
    pose proof aceil_facts as ACF.
    pose proof (winv_rh H _ _ _ _ _ _ _ HI) as RH.
    destruct (winv_er H _ _ _ _ _ _ _ HI) as (errv & ER).
    pose proof (winv_rf H _ _ _ _ _ _ _ HI) as RF.
    eapply (ah_seq H HB).
    { eapply (MVA ra (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) t0 t1 t2 (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
                (Z_to_bv 64 d) (Z_to_bv 64 sr) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc msF m mo s LB (w_LB e) LBs1 LBs2 ((6, ff, fp) :: w_LF e) d sr c1 c2 (w_lo e) (w_B e) (w_shi e) errv);
        rewrite ?HLib.u64_of_Z by lia.
      - exact VIS.
      - exact FZ.
      - reflexivity.
      - reflexivity.
      - exact R1.
      - exact SH1.
      - exact R2.
      - exact SH2.
      - exact PLB.
      - exact P1.
      - exact P2.
      - exact CAP.
      - exact AD1.
      - exact AD2.
      - exact DJ.
      - intros b Hb. pose proof (ah_blocks H HB _ _ _ _ RH Hb) as (B0 & B16 & Bn & BI & BC & BF & BAPP). unfold ST_SIZE, WO_FLAGP in *. unfold AFS_SIZE in *. lia.
      - intros b Hb. pose proof (ah_blocks H HB _ _ _ _ RH Hb) as (B0 & B16 & Bn & BI & BC & BF & BAPP). unfold ST_SIZE, WO_FLAGP in *. unfold AFS_SIZE in *. lia.
      - exists (6, ff, fp). split; [left; reflexivity|]. unfold ff_addr, ff_class. cbn [fst snd]. change (fsz 6) with 4096. unfold ST_SIZE, WO_FLAGP in *. lia.
      - left. exists (6, ff, fp). split; [left; reflexivity|]. unfold ff_addr, ff_class. cbn [fst snd]. change (fsz 6) with 4096. unfold ST_SIZE, WO_FLAGP in *. lia.
      - unfold ST_SIZE, WO_FLAGP in *. lia.
      - exact RH.
      - exact KR.
      - exact AL0.
      - exact (winv_ra H _ _ _ _ _ _ _ HI).
      - pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & X & _). lia.
      - pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _). lia.
      - clear - S32. Z.div_mod_to_equations. lia.
      - exact (proj1 (stk_split asegs m (w_lo e) (wS1 e) (wSP e) (winv_stk H _ _ _ _ _ _ _ HI) ltac:(lia))).
      - exact CE.
      - unfold AST_MVA_STACK, AFREE_STACK. lia.
      - exact ER.
      - exact (winv_mi H _ _ _ _ _ _ _ HI).
      - exact TP.
      - exact RA2.
      - exact (winv_ac H _ _ _ _ _ _ _ HI).
      - exact RF.
      - exact (winv_s0 H _ _ _ _ _ _ _ HI).
      - lia.
      - exact (HOWN _ _ _ RH).
      - exact wtr_mva. }
    intros [msF' mo'] POST.
    destruct POST as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & errv' & s' & LB' & XS & F' & fc'
                      & VIS' & FZ' & KR' & MP' & MI' & ST' & ER' & RA' & RH' & PERM & R1' & SH1' & R2' & FS & XP & RF' & AC' & S0' & AL' & OWN').
    cbn [cfg_ms cfg_model] in VIS', KR', MP'.
    rewrite ?HLib.u64_of_Z in ST', XP by lia.
    eapply (K msF' mo' s' LB' m' XS); [exact VIS' | exact FZ' | exact KR' | exact MP' | | exact XP | exact FS | exact PERM
                                        | exact R1' | exact SH1' | exact R2' | lia].
    change ((d, d + ST_SIZE) :: (sr, sr + ST_SIZE) :: XS)
      with ([(d, d + ST_SIZE); (sr, sr + ST_SIZE)] ++ XS) in XP.
    eapply (winv_sr H HB e ff fp XSc XS _ s LB (w_LB e) s' LB' m m' HP HI (fun b Hb => Hb) XP FS).
    - apply Forall_cons; [right; left; cbn [fst snd]; unfold ST_SIZE, WO_FLAGP in *; lia|].
      apply Forall_cons; [right; left; cbn [fst snd]; unfold ST_SIZE, WO_FLAGP in *; lia|].
      apply Forall_forall. intros iv Hiv. left. exact Hiv.
    - exact RF'.
    - exact RH'.
    - exact AC'.
    - exact MI'.
    - exact ST'.
    - exists errv'. exact ER'.
    - exact RA'.
    - apply Forall_cons; [cbn [fst snd]; intros _; replace (d + ST_SIZE - d) with ST_SIZE by lia;
                          unfold ST_SIZE; apply (state_repA_wr LB' m' d (state_moved c1 c2) R1'); unfold ST_SIZE, WO_FLAGP in *; lia|].
      apply Forall_cons; [cbn [fst snd]; intros _; replace (sr + ST_SIZE - sr) with ST_SIZE by lia;
                          unfold ST_SIZE; apply (state_repA_wr LB' m' sr (state_emptied c2) R2'); unfold ST_SIZE, WO_FLAGP in *; lia|].
      eapply Forall_impl; [| exact FS]. intros iv FSi Hiv. cbn [fst snd] in Hiv |- *.
      destruct (wfsw_ok H HB e ff fp m' iv RF' (winv_ff H _ _ _ _ _ _ _ HI) CE FSi) as (W1 & _ & _ & B4 & B5 & _ & B7 & _).
      destruct (W1 LB') as [A1|[A1|[A1|[A1|[A1|[A1|A1]]]]]]; cbn in A1;
        (split; [unfold WO_FLAGP in *; unfold sh in *; rewrite ?ASHADOW_BASE_val in *; lia|]; split; [unfold AAPP_HI, AHI_LO, AFS_SIZE in *; lia|]; intros i Hi; exfalso; unfold WO_FLAGP in *; lia).
  Qed.

  Lemma wdtT : forall (e : went H) ff fp XSc s LB (c : stateC) m msF mo (Q : config -> Prop) (r o : Z)
      (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
    wpre H e -> winv H e ff fp XSc s LB m -> (forall b, In b (w_LB e) -> In b LB) ->
    ff + 8 <= o -> o + ST_SIZE <= ff + WO_FLAGP -> addressable m o ST_SIZE ->
    as_VIS H s msF = MS (mkR (Z_to_bv 64 r) (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) t0 t1 t2 (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
                           (Z_to_bv 64 o) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 AST_DTOR) fc None m (seg_rom asegs) ->
    frm_zero fc -> 0 <= r < 2 ^ 64 -> r mod 2 = 0 -> In (APC0_FREE, [r]) PO_PF ->
    as_AKREL H s (mkCfg msF mo) -> 0 <= as_AL H s ->
    state_repA LB m o c -> state_sh m c -> state_blocks c = [] ->
    (forall msF' mo' s' LB' m' XS (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32),
       as_VIS H s' msF' = MS (mkR (Z_to_bv 64 r) (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) t0' t1' t2' (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
                                a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                          F' (Z_to_bv 64 r) fc' None m' (seg_rom asegs) ->
       frm_zero fc' -> as_AKREL H s' (mkCfg msF' mo') -> as_MPRES H mo mo' ->
       winv H e ff fp (XSc ++ XS) s' LB' m' ->
       xpres H LB (wS1 e) ((o, o + ST_SIZE) :: XS) m m' ->
       Forall (fs_scratch H ((6, ff, fp) :: w_LF e)) XS ->
       Permutation LB' LB -> wr_at asegs m' o ST_SIZE ->
       as_AL H s' >= as_AL H s ->
       as_SR H Q (mkCfg msF' mo')) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros e ff fp XSc s LB c m msF mo Q r o t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
      HP HI INC O1 O2 AD2 VIS FZ Hr RE INPF KR AL0 R SH SB K.
    pose proof (wpre_geo H e HP) as (CE & LO & SSHI & SHIH & SP16 & TP).
    pose proof (wS1_facts H e HP) as (S32 & S1SP & S1L & SPH & LOS1 & _).
    pose proof (wframe_facts H _ _ _ (winv_ff H _ _ _ _ _ _ _ HI)) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16).
    pose proof aceil_facts as ACF.
    pose proof (winv_rh H _ _ _ _ _ _ _ HI) as RH.
    destruct (winv_er H _ _ _ _ _ _ _ HI) as (errv & ER).
    pose proof (winv_rf H _ _ _ _ _ _ _ HI) as RF.
    destruct (wchain_call H HB e ff fp XSc s LB m HP HI) as [CH CHU].
    eapply (ah_seq H HB).
    { eapply (DTOR (Z_to_bv 64 r) (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) t0 t1 t2 (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
                (Z_to_bv 64 o) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc msF m mo s LB LB [] ((6, ff, fp) :: w_LF e) o c (w_lo e) (w_B e) (w_shi e) errv
                ((wSP e, bv_unsigned (w_ra e)) :: w_CH e));
        rewrite ?HLib.u64_of_Z by lia.
      - exact VIS.
      - exact FZ.
      - reflexivity.
      - exact R.
      - exact SH.
      - rewrite app_nil_r. apply Permutation_refl.
      - rewrite SB. apply Permutation_refl.
      - rewrite SB. intros p n [].
      - exact AD2.
      - intros b Hb. pose proof (ah_blocks H HB _ _ _ _ RH Hb) as (B0 & B16 & Bn & BI & BC & BF & BAPP). unfold ST_SIZE, WO_FLAGP in *. unfold AFS_SIZE in *. lia.
      - left. exists (6, ff, fp). split; [left; reflexivity|]. unfold ff_addr, ff_class. cbn [fst snd]. change (fsz 6) with 4096. unfold ST_SIZE, WO_FLAGP in *. lia.
      - left. exact SB.
      - exact RH.
      - exact KR.
      - exact AL0.
      - exact (winv_ra H _ _ _ _ _ _ _ HI).
      - pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & X & _). lia.
      - pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _). lia.
      - clear - S32. Z.div_mod_to_equations. lia.
      - exact (proj1 (stk_split asegs m (w_lo e) (wS1 e) (wSP e) (winv_stk H _ _ _ _ _ _ _ HI) ltac:(lia))).
      - exact CE.
      - unfold AST_DTOR_STACK, AFREE_STACK. lia.
      - exact ER.
      - exact (winv_mi H _ _ _ _ _ _ _ HI).
      - exact TP.
      - exact RE.
      - exact (winv_ac H _ _ _ _ _ _ _ HI).
      - exact RF.
      - exact (winv_s0 H _ _ _ _ _ _ _ HI).
      - lia.
      - exact (HOWN _ _ _ RH).
      - exact wtr_dtor.
      - exact CH.
      - exact (wtrace_dtor H e r HP INPF).
      - exact CHU. }
    intros [msF' mo'] POST.
    destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & errv' & s' & LB' & XS & F' & fc'
                      & VIS' & FZ' & KR' & MP' & MI' & ST' & ER' & RA' & RH' & PERM & FS & XP & RF' & AC' & S0' & AL' & OWN' & WR').
    cbn [cfg_ms cfg_model] in VIS', KR', MP'.
    rewrite ?HLib.u64_of_Z in ST', XP by lia.
    rewrite (ret_pc_even r Hr RE) in VIS'.
    eapply (K msF' mo' s' LB' m' XS); [exact VIS' | exact FZ' | exact KR' | exact MP' | | exact XP | exact FS | exact PERM | exact WR' | lia].
    change ((o, o + ST_SIZE) :: XS) with ([(o, o + ST_SIZE)] ++ XS) in XP.
    eapply (winv_sr H HB e ff fp XSc XS _ s LB LB s' LB' m m' HP HI INC XP FS).
    - apply Forall_cons; [right; left; cbn [fst snd]; unfold ST_SIZE, WO_FLAGP in *; lia|].
      apply Forall_forall. intros iv Hiv. left. exact Hiv.
    - exact RF'.
    - exact RH'.
    - exact AC'.
    - exact MI'.
    - exact ST'.
    - exists errv'. exact ER'.
    - exact RA'.
    - apply Forall_cons; [cbn [fst snd]; intros _; replace (o + ST_SIZE - o) with ST_SIZE by lia; exact WR'|].
      eapply Forall_impl; [| exact FS]. intros iv FSi Hiv. cbn [fst snd] in Hiv |- *.
      destruct (wfsw_ok H HB e ff fp m' iv RF' (winv_ff H _ _ _ _ _ _ _ HI) CE FSi) as (W1 & _ & _ & B4 & B5 & _ & B7 & _).
      destruct (W1 LB') as [A1|[A1|[A1|[A1|[A1|[A1|A1]]]]]]; cbn in A1;
        (split; [unfold WO_FLAGP in *; unfold sh in *; rewrite ?ASHADOW_BASE_val in *; lia|]; split; [unfold AAPP_HI, AHI_LO, AFS_SIZE in *; lia|]; intros i Hi; exfalso; unfold WO_FLAGP in *; lia).
  Qed.

  Definition wm3_post (e : went H) (ff fp : Z) (XS : list (Z * Z)) (sk : as_St H) (LBk : list block) (p4 p5 p6 : bptr)
      (b1 b2 b3 g h k : Z) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m',
      ms' = MS (mkR (Z_to_bv 64 WO_MVA1_RA) (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) x5 x6 x7 (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
                    (Z_to_bv 64 (ff + 3504)) (Z_to_bv 64 (ff + 2752)) x12 x13 x14 x15 x16 x17
                    (Z_to_bv 64 (ff + 3456)) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) (Z_to_bv 64 (ff + 2920)) (Z_to_bv 64 (ff + 3504))
                    (Z_to_bv 64 0x3f800000) (Z_to_bv 64 (ff + 2944)) (Z_to_bv 64 (ff + 2968)) (Z_to_bv 64 (ff + 3696))
                    (Z_to_bv 64 (ff + 2752)) x28 x29 x30 x31)
               (w_F e) (Z_to_bv 64 AST_MVA) (w_fc e) None m' (seg_rom asegs)
      /\ winv H e ff fp XS sk LBk m' /\ wpcells H e ff m' /\ bp_slots H e ff m' /\ bp_shad ff [18; 20; 21]%nat m'
      /\ wps3 ff m' b1 b2 b3 /\ wtst ff m' (w_words e) (w_n e) (vtrip g 500) (vtrip h 100) (vtrip k 100)
      /\ wblk m' g 500 /\ wblk m' h 100 /\ wblk m' k 100
      /\ lb_own [(p4, g, 500); (p5, h, 100); (p6, k, 100)] m'
      /\ addressable m' (ff + 3504) ST_SIZE /\ addressable m' (ff + 2752) ST_SIZE.

  Definition wv1_post (e : went H) (ff fp : Z) (XS : list (Z * Z)) (sk : as_St H) (LBk : list block) (p4 p5 p6 : bptr) (g h k : Z)
      : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32) m',
      ms' = MS (mkR (Z_to_bv 64 WO_DT1_RA) (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) x5 x6 x7 (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
                    (Z_to_bv 64 (ff + 2752)) x11 x12 x13 x14 x15 x16 x17
                    (Z_to_bv 64 (ff + 3456)) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) (Z_to_bv 64 (ff + 2920)) (Z_to_bv 64 (ff + 3504))
                    (Z_to_bv 64 0x3f800000) (Z_to_bv 64 (ff + 2944)) (Z_to_bv 64 (ff + 2968)) (Z_to_bv 64 (ff + 3696))
                    (Z_to_bv 64 (ff + 2752)) x28 x29 x30 x31)
               F (Z_to_bv 64 AST_DTOR) fc None m' (seg_rom asegs)
      /\ frm_zero fc
      /\ winv H e ff fp XS sk LBk m' /\ wpcells H e ff m' /\ bp_slots H e ff m' /\ bp_shad ff [18; 20; 21]%nat m'
      /\ state_repA LBk m' (ff + 3504) (mkfreshA (w_words e) (w_n e) g h k) /\ state_sh m' (mkfreshA (w_words e) (w_n e) g h k)
      /\ state_repA LBk m' (ff + 2752) (state_emptied (mkfreshA (w_words e) (w_n e) g h k))
      /\ lb_own [(p4, g, 500); (p5, h, 100); (p6, k, 100)] m'
      /\ addressable m' (ff + 2752) ST_SIZE
      /\ 0 < g /\ 0 < h /\ 0 < k.

  Lemma munch_nil_eq : forall (m m' : mem), munch [] m m' -> m' = m.
  Proof. intros m m' MU. apply functional_extensionality. intros x. apply MU. exact I. Qed.

  Lemma pm_phi3 : forall a b c, LbB_PmBase.pm_phi_blocks [(a, 500); (b, 100); (c, 100)] = 0.
  Proof. intros. reflexivity. Qed.

  Lemma wFcell_xp : forall (e : went H) ff fp LB XO XS mr m m' a cs,
    wpre H e -> as_RFS H ((6, ff, fp) :: w_LF e) mr -> fresh_frame H (w_LF e) 6 ff fp ->
    xpres H LB (wS1 e) (XO ++ XS) m m' -> Forall (fs_scratch H ((6, ff, fp) :: w_LF e)) XS ->
    Forall (fun iv : Z * Z => a + Z.of_nat (cells_size cs) <= fst iv \/ snd iv <= a) XO ->
    ff <= a -> a + Z.of_nat (cells_size cs) <= ff + 4096 -> rw_cells asegs m a cs -> rw_cells asegs m' a cs.
  Proof.
    intros e ff fp LB XO XS mr m m' a cs HP RF FF XP FS FXO Ha1 Ha2 C.
    pose proof (wpre_geo H e HP) as (CE & _).
    pose proof (wframe_facts H _ _ _ FF) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & _).
    eapply xpres_rw_cells; [exact XP | exact C |]. split; [right; right; right; right; left; lia|].
    apply Forall_app. split; [exact FXO|]. eapply Forall_impl; [| exact FS]. intros iv FSi.
    destruct (wfsw_ok H HB e ff fp mr iv RF FF CE FSi) as (_ & _ & _ & _ & B5 & _). lia.
  Qed.

  Lemma wFsh_xp : forall (e : went H) ff fp LB XO XS mr m m' bs,
    wpre H e -> as_RFS H ((6, ff, fp) :: w_LF e) mr -> fresh_frame H (w_LF e) 6 ff fp ->
    xpres H LB (wS1 e) (XO ++ XS) m m' -> Forall (fs_scratch H ((6, ff, fp) :: w_LF e)) XS ->
    Forall (fun iv : Z * Z => ff <= fst iv /\ snd iv <= ff + 4096) XO ->
    (length bs <= 512)%nat -> u8arr asegs m (sh ff) bs -> u8arr asegs m' (sh ff) bs.
  Proof.
    intros e ff fp LB XO XS mr m m' bs HP RF FF XP FS FXO LEN U.
    pose proof (wpre_geo H e HP) as (CE & _).
    pose proof (wframe_facts H _ _ _ FF) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16).
    eapply xpres_u8arr; [exact XP | exact U |]. split; [right; right; right; right; right; left; lia|].
    apply Forall_app. split.
    - eapply Forall_impl; [| exact FXO]. intros iv K. cbn beta in K. lia.
    - eapply Forall_impl; [| exact FS]. intros iv FSi.
      destruct (wfsw_ok H HB e ff fp mr iv RF FF CE FSi) as (_ & _ & _ & _ & _ & B6 & _). lia.
  Qed.

  Lemma wFaddr_xp : forall (e : went H) ff fp LB XO XS mr m m' A n,
    wpre H e -> as_RFS H ((6, ff, fp) :: w_LF e) mr -> fresh_frame H (w_LF e) 6 ff fp ->
    xpres H LB (wS1 e) (XO ++ XS) m m' -> Forall (fs_scratch H ((6, ff, fp) :: w_LF e)) XS ->
    Forall (fun iv : Z * Z => ff <= fst iv /\ snd iv <= ff + 4096) XO ->
    ff <= A -> A + n <= ff + 4096 -> A mod 8 = 0 -> addressable m A n -> addressable m' A n.
  Proof.
    intros e ff fp LB XO XS mr m m' A n HP RF FF XP FS FXO HA1 HA2 HA8 AD.
    pose proof (wpre_geo H e HP) as (CE & _).
    pose proof (wframe_facts H _ _ _ FF) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16).
    pose proof AD as (Hn & _).
    assert (SA : sh ff <= sh A /\ sh A + nsh n <= sh ff + 512) by (clear - F3 HA1 HA2 HA8 Hn; unfold sh, nsh; Z.div_mod_to_equations; lia).
    eapply addressable_xp; [exact XP | exact AD |]. intros a Ha.
    apply (xclient_range_addr H LB (wS1 e) (XO ++ XS) (sh A) (nsh n) a); [| exact Ha].
    split; [right; right; right; right; right; left; lia|].
    apply Forall_app. split.
    - eapply Forall_impl; [| exact FXO]. intros iv K. cbn beta in K. lia.
    - eapply Forall_impl; [| exact FS]. intros iv FSi.
      destruct (wfsw_ok H HB e ff fp mr iv RF FF CE FSi) as (_ & _ & _ & _ & _ & B6 & _). lia.
  Qed.

  Lemma wpcells_xp : forall (e : went H) ff fp LB XO XS mr m m',
    wpre H e -> as_RFS H ((6, ff, fp) :: w_LF e) mr -> fresh_frame H (w_LF e) 6 ff fp ->
    xpres H LB (wS1 e) (XO ++ XS) m m' -> Forall (fs_scratch H ((6, ff, fp) :: w_LF e)) XS ->
    Forall (fun iv : Z * Z => ff <= fst iv /\ snd iv <= ff + 4096 /\ (snd iv <= ff + 3408 \/ ff + 3504 <= fst iv)) XO ->
    wpcells H e ff m -> wpcells H e ff m'.
  Proof.
    intros e ff fp LB XO XS mr m m' HP RF FF XP FS FXO (W1 & W2 & W3 & W4 & W5).
    pose proof (wframe_facts H _ _ _ FF) as (F1 & F2 & F3 & _).
    assert (FX1 : forall a k, ff + 3408 <= a -> a + k <= ff + 3504 -> Forall (fun iv : Z * Z => a + k <= fst iv \/ snd iv <= a) XO).
    { intros a k K1 K2. eapply Forall_impl; [| exact FXO]. intros iv K. cbn beta in K. lia. }
    assert (FX2 : Forall (fun iv : Z * Z => ff <= fst iv /\ snd iv <= ff + 4096) XO).
    { eapply Forall_impl; [| exact FXO]. intros iv K. cbn beta in K. lia. }
    assert (M8 : forall o, o mod 8 = 0 -> (ff + o) mod 8 = 0) by (intros o Ho; clear - F3 Ho; Z.div_mod_to_equations; lia).
    unfold wpcells. split; [|split; [|split; [|split]]].
    - eapply (wFcell_xp e ff fp LB XO XS mr m m'); [exact HP | exact RF | exact FF | exact XP | exact FS
      | apply FX1; cbn [cells_size csize]; lia | lia | cbn [cells_size csize]; lia | exact W1].
    - eapply (wFcell_xp e ff fp LB XO XS mr m m'); [exact HP | exact RF | exact FF | exact XP | exact FS
      | apply FX1; cbn [cells_size csize]; lia | lia | cbn [cells_size csize]; lia | exact W2].
    - eapply (wFcell_xp e ff fp LB XO XS mr m m'); [exact HP | exact RF | exact FF | exact XP | exact FS
      | apply FX1; cbn [cells_size csize]; lia | lia | cbn [cells_size csize]; lia | exact W3].
    - eapply (wFaddr_xp e ff fp LB XO XS mr m m'); [exact HP | exact RF | exact FF | exact XP | exact FS | exact FX2
      | lia | lia | apply M8; reflexivity | exact W4].
    - eapply (wFaddr_xp e ff fp LB XO XS mr m m'); [exact HP | exact RF | exact FF | exact XP | exact FS | exact FX2
      | lia | lia | apply M8; reflexivity | exact W5].
  Qed.

  Lemma bp_slots_xp : forall (e : went H) ff fp LB XO XS mr m m',
    wpre H e -> as_RFS H ((6, ff, fp) :: w_LF e) mr -> fresh_frame H (w_LF e) 6 ff fp ->
    xpres H LB (wS1 e) (XO ++ XS) m m' -> Forall (fs_scratch H ((6, ff, fp) :: w_LF e)) XS ->
    Forall (fun iv : Z * Z => snd iv <= wS1 e) XO -> bp_slots H e ff m -> bp_slots H e ff m'.
  Proof.
    intros e ff fp LB XO XS mr m m' HP RF FF XP FS FXO (C1 & C2 & C3).
    assert (FX : forall a k, wS1 e <= a -> Forall (fun iv : Z * Z => a + k <= fst iv \/ snd iv <= a) XO).
    { intros a k K. eapply Forall_impl; [| exact FXO]. intros iv K'. cbn beta in K'. lia. }
    unfold bp_slots. split; [|split].
    - eapply wS1cell_xp; [exact HP | exact RF | exact FF | exact XP | exact FS | apply FX; lia | lia | exact C1].
    - eapply wS1cell_xp; [exact HP | exact RF | exact FF | exact XP | exact FS | apply FX; lia | lia | exact C2].
    - eapply wS1cell_xp; [exact HP | exact RF | exact FF | exact XP | exact FS | apply FX; lia | lia | exact C3].
  Qed.
  Lemma seg_mva1 : forall (Q : config -> Prop) (e : went H) ff fp msF mo mo0 s6 XS6 (p1 p2 p3 p4 p5 p6 : bptr) b1 b2 b3 g h k,
    let LB6 := (p6, k, 100) :: (p5, h, 100) :: (p4, g, 500) :: (p3, b3, 100) :: (p2, b2, 100) :: (p1, b1, 500) :: w_LB e in
    wpre H e -> as_AKREL H s6 (mkCfg msF mo) -> as_MPRES H mo0 mo -> as_AL H s6 >= as_AL H (w_s e) ->
    List.NoDup (map blk_id LB6) ->
    wm3_post e ff fp XS6 s6 LB6 p4 p5 p6 b1 b2 b3 g h k (as_VIS H s6 msF) ->
    (forall msF' mo' s7 LB7 XS, as_AKREL H s7 (mkCfg msF' mo') -> as_MPRES H mo0 mo' -> as_AL H s7 >= as_AL H (w_s e) ->
       Permutation LB7 (w_LB e ++ [(p4, g, 500); (p5, h, 100); (p6, k, 100)]) ->
       wv1_post e ff fp XS s7 LB7 p4 p5 p6 g h k (as_VIS H s7 msF') -> as_SR H Q (mkCfg msF' mo')) ->
    as_SR H Q (mkCfg msF mo).
  Proof using HHb HOWN MVA DTOR WTR.
    intros Q e ff fp msF mo mo0 s6 XS6 p1 p2 p3 p4 p5 p6 b1 b2 b3 g h k LB6 HP KR MP AL6 ND P7 K.
    destruct P7 as (x5 & x6 & x7 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m0 & VIS & HI & WC & SL & SD
                    & PS & TS & WG & WH & WK & OWN & AD1 & AD2).
    pose proof (wS1_facts H e HP) as (S32 & S1SP & S1L & SPH & LOS1 & CEL).
    pose proof (wpre_geo H e HP) as (CE & LO & SSHI & SHIH & SP16 & TP).
    pose proof (wpre_budget H e HP) as (HN & BS & BC & BL & AL0).
    pose proof HP as (FZ0 & _).
    pose proof (wframe_facts H _ _ _ (winv_ff H _ _ _ _ _ _ _ HI)) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16).
    assert (PA : Permutation LB6 ([(p1, b1, 500); (p2, b2, 100); (p3, b3, 100)] ++ ((p6, k, 100) :: (p5, h, 100) :: (p4, g, 500) :: w_LB e))).
    { unfold LB6. etransitivity; [| apply Permutation_app_comm]. cbn [app].
      apply Permutation_cons; [reflexivity|]. apply Permutation_cons; [reflexivity|]. apply Permutation_cons; [reflexivity|].
      etransitivity; [apply perm_wo3 | apply Permutation_app_comm]. }
    assert (PB : Permutation LB6 ([(p4, g, 500); (p5, h, 100); (p6, k, 100)] ++ ((p3, b3, 100) :: (p2, b2, 100) :: (p1, b1, 500) :: w_LB e)))
      by (unfold LB6; apply perm_wo3).
    destruct (wst_P_rep H HB e ff fp XS6 s6 LB6 m0 p1 p2 p3 b1 b2 b3 _ HP HI PS
                ltac:(unfold LB6; cbn; tauto) ltac:(unfold LB6; cbn; tauto) ltac:(unfold LB6; cbn; tauto) PA) as (R1 & SH1 & B1 & B2 & B3).
    destruct (wst_T_rep H HB e ff fp XS6 s6 LB6 m0 p4 p5 p6 g h k _ HP HI TS WG WH WK
                ltac:(unfold LB6; cbn; tauto) ltac:(unfold LB6; cbn; tauto) ltac:(unfold LB6; cbn; tauto) PB) as (R2 & SH2 & G1 & G2 & G3).
    eapply (wmva e ff fp XS6 s6 LB6 [(p1, b1, 500); (p2, b2, 100); (p3, b3, 100)] [(p4, g, 500); (p5, h, 100); (p6, k, 100)]
              (mkfreshA 0 0 b1 b2 b3) (mkfreshA (w_words e) (w_n e) g h k) m0 msF mo Q (ff + 3504) (ff + 2752));
      [exact HP | exact HI | unfold ST_SIZE, WO_FLAGP; lia | unfold ST_SIZE, WO_FLAGP; lia | unfold ST_SIZE, WO_FLAGP; lia
      | unfold ST_SIZE, WO_FLAGP; lia | unfold ST_SIZE; lia | exact AD1 | exact AD2 | exact VIS | exact FZ0 | reflexivity | exact KR
      | unfold po_cost in AL0; lia | exact R1 | exact SH1 | exact R2 | exact SH2
      | unfold LB6; apply perm_wo6
      | rewrite mkfreshA_blocks by lia; apply Permutation_refl
      | rewrite mkfreshA_blocks by lia; apply Permutation_refl
      | rewrite mkfreshA_blocks by lia; intros p n Hin; destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; lia |].
    intros msF' mo' s' LB' m' XS t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' VIS' FZ' KR' MP' HI' XP FS PERM R1' SH1' R2' AL'.
    rewrite (ret_pc_even WO_MVA1_RA ltac:(unfold WO_MVA1_RA; lia) eq_refl) in VIS'.
    rewrite state_moved_mkfreshA in R1', SH1'.
    pose proof (winv_rf H _ _ _ _ _ _ _ HI') as RF'.
    pose proof (winv_ff H _ _ _ _ _ _ _ HI) as FF.
    change ((ff + 3504, ff + 3504 + ST_SIZE) :: (ff + 2752, ff + 2752 + ST_SIZE) :: XS)
      with ([(ff + 3504, ff + 3504 + ST_SIZE); (ff + 2752, ff + 2752 + ST_SIZE)] ++ XS) in XP.
    assert (FXW : Forall (fun iv : Z * Z => ff <= fst iv /\ snd iv <= ff + 4096 /\ (snd iv <= ff + 3408 \/ ff + 3504 <= fst iv))
                    [(ff + 3504, ff + 3504 + ST_SIZE); (ff + 2752, ff + 2752 + ST_SIZE)]).
    { apply Forall_cons; [cbn [fst snd]; unfold ST_SIZE; lia|]. apply Forall_cons; [cbn [fst snd]; unfold ST_SIZE; lia | apply Forall_nil]. }
    assert (FXF : Forall (fun iv : Z * Z => ff <= fst iv /\ snd iv <= ff + 4096)
                    [(ff + 3504, ff + 3504 + ST_SIZE); (ff + 2752, ff + 2752 + ST_SIZE)]).
    { apply Forall_cons; [cbn [fst snd]; unfold ST_SIZE; lia|]. apply Forall_cons; [cbn [fst snd]; unfold ST_SIZE; lia | apply Forall_nil]. }
    assert (FXS : Forall (fun iv : Z * Z => snd iv <= wS1 e) [(ff + 3504, ff + 3504 + ST_SIZE); (ff + 2752, ff + 2752 + ST_SIZE)]).
    { apply Forall_cons; [cbn [fst snd]; unfold ST_SIZE; lia|]. apply Forall_cons; [cbn [fst snd]; unfold ST_SIZE; lia | apply Forall_nil]. }
    pose proof (wpcells_xp e ff fp (w_LB e) _ XS m' m0 m' HP RF' FF XP FS FXW WC) as WC'.
    pose proof (bp_slots_xp e ff fp (w_LB e) _ XS m' m0 m' HP RF' FF XP FS FXS SL) as SL'.
    assert (SD' : bp_shad ff [18; 20; 21]%nat m').
    { unfold bp_shad in *. eapply (wFsh_xp e ff fp (w_LB e) _ XS m' m0 m'); [exact HP | exact RF' | exact FF | exact XP | exact FS | exact FXF | | exact SD].
      rewrite length_map. apply Nat.leb_le. vm_compute. reflexivity. }
    assert (AD2' : addressable m' (ff + 2752) ST_SIZE).
    { eapply (wFaddr_xp e ff fp (w_LB e) _ XS m' m0 m'); [exact HP | exact RF' | exact FF | exact XP | exact FS | exact FXF
      | lia | unfold ST_SIZE; lia | clear - F3; Z.div_mod_to_equations; lia | exact AD2]. }
    assert (OWN' : lb_own [(p4, g, 500); (p5, h, 100); (p6, k, 100)] m').
    { eapply lb_own_incl; [| exact (HOWN s' LB' m' (winv_rh H _ _ _ _ _ _ _ HI'))]. intros b Hb.
      eapply Permutation_in; [apply Permutation_sym; exact PERM|]. apply in_or_app. right. exact Hb. }
    eapply (ahh_evt_then H HB _ Q s' msF' _ mo'); [exact KR' | exact VIS' | |].
    { eapply wd1; [lia | lia | exact (winv_stk H _ _ _ _ _ _ _ HI') | exact (winv_mi H _ _ _ _ _ _ _ HI')]. }
    intros msF2 mo2 KR2 MP2 (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m1 & EQ & MU & WM & MI1 & ST1).
    pose proof (munch_nil_eq m' m1 MU) as EM. subst m1.
    eapply (K msF2 mo2 s' LB' (XS6 ++ XS)); [exact KR2 | mpres_chain | lia | exact PERM |].
    unfold wv1_post. rewrite EQ.
    do 14 eexists. exists F', fc', m'. split; [reflexivity|].
    split; [exact FZ'|]. split; [exact HI'|]. split; [exact WC'|]. split; [exact SL'|]. split; [exact SD'|].
    split; [exact R1'|]. split; [exact SH1'|]. split; [exact R2'|]. split; [exact OWN'|]. split; [exact AD2'|]. lia.
  Qed.

  Lemma seg_dt1 : forall (Q : config -> Prop) (e : went H) ff fp msF mo mo0 s7 LB7 XS7 (p4 p5 p6 : bptr) g h k,
    wpre H e -> as_AKREL H s7 (mkCfg msF mo) -> as_MPRES H mo0 mo -> as_AL H s7 >= as_AL H (w_s e) ->
    Permutation LB7 (w_LB e ++ [(p4, g, 500); (p5, h, 100); (p6, k, 100)]) ->
    wv1_post e ff fp XS7 s7 LB7 p4 p5 p6 g h k (as_VIS H s7 msF) ->
    bp_k480 H e ff fp Q mo0 ->
    as_SR H Q (mkCfg msF mo).
  Proof using HHb HOWN MVA DTOR WTR.
    intros Q e ff fp msF mo mo0 s7 LB7 XS7 p4 p5 p6 g h k HP KR MP AL7 PERM7 P8 K.
    destruct P8 as (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & F & fc & m0
                    & VIS & FZ & HI & WC & SL & SD & R1 & SH1 & R2 & OWN & AD2 & G1 & G2 & G3).
    pose proof (wS1_facts H e HP) as (S32 & S1SP & S1L & SPH & LOS1 & CEL).
    pose proof (wpre_geo H e HP) as (CE & LO & SSHI & SHIH & SP16 & TP).
    pose proof (wpre_budget H e HP) as (HN & BS & BC & BL & AL0).
    pose proof (wframe_facts H _ _ _ (winv_ff H _ _ _ _ _ _ _ HI)) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16).
    assert (INC : forall b, In b (w_LB e) -> In b LB7).
    { intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact PERM7|]. apply in_or_app. left. exact Hb. }
    eapply (wdtT e ff fp XS7 s7 LB7 (state_emptied (mkfreshA (w_words e) (w_n e) g h k)) m0 msF mo Q WO_DT1_RA (ff + 2752));
      [exact HP | exact HI | exact INC | unfold ST_SIZE, WO_FLAGP; lia | unfold ST_SIZE, WO_FLAGP; lia | exact AD2 | exact VIS | exact FZ
      | unfold WO_DT1_RA; lia | reflexivity | unfold PO_PF, WO_DT1_RA; apply in_or_app; left; left; reflexivity
      | exact KR | unfold po_cost in AL0; lia | exact R2 | apply state_sh_emptied | reflexivity |].
    intros msF' mo' s' LB' m' XS t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' VIS' FZ' KR' MP' HI' XP FS PERM WR' AL'.
    pose proof (winv_rf H _ _ _ _ _ _ _ HI') as RF'.
    pose proof (winv_ff H _ _ _ _ _ _ _ HI) as FF.
    pose proof (winv_rh H _ _ _ _ _ _ _ HI) as RH7.
    assert (PERM' : Permutation LB' (w_LB e ++ [(p4, g, 500); (p5, h, 100); (p6, k, 100)])) by (etransitivity; [exact PERM | exact PERM7]).
    change ((ff + 2752, ff + 2752 + ST_SIZE) :: XS) with ([(ff + 2752, ff + 2752 + ST_SIZE)] ++ XS) in XP.
    assert (WC' : wpcells H e ff m').
    { eapply (wpcells_xp e ff fp LB7 _ XS m' m0 m'); [exact HP | exact RF' | exact FF | exact XP | exact FS | | exact WC].
      apply Forall_cons; [cbn [fst snd]; unfold ST_SIZE; lia | apply Forall_nil]. }
    assert (SL' : bp_slots H e ff m').
    { eapply (bp_slots_xp e ff fp LB7 _ XS m' m0 m'); [exact HP | exact RF' | exact FF | exact XP | exact FS | | exact SL].
      apply Forall_cons; [cbn [fst snd]; unfold ST_SIZE; lia | apply Forall_nil]. }
    assert (SD' : bp_shad ff [18; 20; 21]%nat m').
    { unfold bp_shad in *. eapply (wFsh_xp e ff fp LB7 _ XS m' m0 m'); [exact HP | exact RF' | exact FF | exact XP | exact FS | | | exact SD].
      - apply Forall_cons; [cbn [fst snd]; unfold ST_SIZE; lia | apply Forall_nil].
      - rewrite length_map. apply Nat.leb_le. vm_compute. reflexivity. }
    assert (BLK : forall p n, In (p, n) (state_blocks (mkfreshA (w_words e) (w_n e) g h k)) -> In (p, n) (lbl LB7) /\ In (p, n) (lbl LB')).
    { rewrite mkfreshA_blocks by lia. intros p n Hin.
      assert (IN7 : In (p, n) (lbl [(p4, g, 500); (p5, h, 100); (p6, k, 100)])) by (cbn; destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; tauto).
      destruct (lbl_in_inv _ _ _ IN7) as (q & Hq). split.
      - apply (lbl_in _ q). eapply Permutation_in; [apply Permutation_sym; exact PERM7|]. apply in_or_app. right. exact Hq.
      - apply (lbl_in _ q). eapply Permutation_in; [apply Permutation_sym; exact PERM'|]. apply in_or_app. right. exact Hq. }
    destruct (wstate_xp e ff fp s7 LB7 LB' [(ff + 2752, ff + 2752 + ST_SIZE)] XS m' m0 m' (mkfreshA (w_words e) (w_n e) g h k) (ff + 3504)
                HP RF' FF RH7 XP FS ltac:(lia) ltac:(unfold ST_SIZE, WO_FLAGP; lia)
                ltac:(apply Forall_cons; [cbn [fst snd]; unfold ST_SIZE, WO_FLAGP; lia | apply Forall_nil]) BLK R1 SH1) as [R1' SH1'].
    destruct (wparser_mk H e ff fp (XS7 ++ XS) s' LB' m' (mkfreshA (w_words e) (w_n e) g h k) HP HI' WC' R1') as (PR & PSH & FS1 & FS2 & C16 & WRC).
    assert (OWN' : lb_own [(p4, g, 500); (p5, h, 100); (p6, k, 100)] m').
    { eapply lb_own_incl; [| exact (HOWN s' LB' m' (winv_rh H _ _ _ _ _ _ _ HI'))]. intros b Hb.
      eapply Permutation_in; [apply Permutation_sym; exact PERM'|]. apply in_or_app. right. exact Hb. }
    assert (PH : LbB_PiInit.pi_hdr (bp_ste (mkfreshA (w_words e) (w_n e) g h k) 0) (w_words e) (w_n e) 0).
    { unfold LbB_PiInit.pi_hdr, bp_ste, mkfreshA. cbn. repeat split; lia. }
    destruct (LbB_PiInit.pi_blocks _ _ _ _ PH) as [_ CB].
    unfold bp_k480, bp_hdr0 in K.
    eapply (K s' LB' [(p4, g, 500); (p5, h, 100); (p6, k, 100)] m' mo' msF' _ F' fc' (XS7 ++ XS)
              (LbB_PiStmt.PIW H (ff + 3456) (ff + 3376) 0 0 (w_words e) (w_n e) (w_LB e) (w_s e) (w_lo e) (w_B e) (w_shi e))
              (wparser ff (mkfreshA (w_words e) (w_n e) g h k)));
      [exact VIS' | apply LbB_Bridge.rfull_mkR | exact FZ' | exact KR' | mpres_chain | exact HP | exact HI' | exact SL' | exact SD' | | | |].
    - unfold bp_rc. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [transitivity (Z_to_bv 64 (wSP e)); [reflexivity | unfold wSP; apply Z_to_bv_bv_unsigned]|].
      split; [reflexivity|]. split; reflexivity.
    - unfold bp_r480. repeat split.
    - unfold bp_wl. repeat split.
    - unfold bp_pfresh, bp_pp, bp_fresh, wparser. cbn [pc_state pc_cons pc_user]. split; [|split; [|split]].
      + split; [exact PR|]. split; [exact (PSH SH1')|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        split; [split; [exact PERM' | rewrite mkfreshA_blocks by lia; apply Permutation_refl]|].
        split; [exact OWN' | exact WRC].
      + split; [exact PH | left; reflexivity].
      + unfold bp_al. cbn [LbB_PiStmt.pw_s0 LbB_PiStmt.pw_n].
        rewrite LbB_PmBase.pm_phi_eq, LbB_PmBase.pm_cap_eq, CB, pm_phi3.
        pose proof (LbB_PmBase.pm_prog_bounds (LbB_PiInit.pi_c0 (bp_ste (mkfreshA (w_words e) (w_n e) g h k) 0))) as PG.
        unfold LbB_PmBase.PM_RESERVE, po_cost in *. lia.
      + cbn [LbB_PiStmt.pw_cons]. replace (ff + 3376 + 32) with (ff + 3408) by lia. exact (proj1 WC').
  Qed.
End WoS3.
