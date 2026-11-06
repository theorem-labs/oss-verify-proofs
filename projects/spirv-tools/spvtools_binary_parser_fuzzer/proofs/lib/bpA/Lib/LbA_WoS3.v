(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HeapCeil.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HTac HArr HSysStep HExec CellsX TacX HMem HMState HLFrame HCells HStep.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HPrelim.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import ASegs AsShadow AsConst AsIface AsCXXHeap CXXRep AsStack0 AsWalk RtA_Iface.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec LibIface FPSteps.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require HLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbA_SR LbA_Conv.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require Import LbA_MILB LbA_PrsStmt LbA_StateStmt LbA_Own LbA_RtOwn LbA_HKit LbA_HStKit.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbA_WoGen LbA_WoDefs LbA_WoKit LbA_WoKit2 LbA_WoKit3 LbA_WoSt LbA_WoSt2 LbA_WoMs LbA_WoCall LbA_WoCut LbA_WoZ.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbA_WoR2 LbA_WoR3 LbA_WoR4 LbA_WoR5 LbA_WoE0 LbA_WoE0b LbA_WoP LbA_WoQ LbA_WoF LbA_WoS1 LbA_WoS2.
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
  Proof. destruct WTR as [_ F]. apply Forall_app in F as [_ F]. exact F. Qed.

  Lemma wscr_ff : forall (e : went H) ff fp mr XS a, wpre H e -> as_RFS H ((3, ff, fp) :: w_LF e) mr ->
    fresh_frame H (w_LF e) 3 ff fp -> Forall (fs_scratch H ((3, ff, fp) :: w_LF e)) XS -> ff <= a < ff + WO_FLAGP ->
    ~ rin_ivs XS a.
  Proof.
    intros e ff fp mr XS a HP RF FF FS Ha. pose proof (wpre_geo H e HP) as (CE & _).
    apply rin_ivs_none. eapply Forall_impl; [| exact FS]. intros iv FSi.
    destruct (wfsw_ok H HB e ff fp mr iv RF FF CE FSi) as (_ & _ & _ & _ & B5 & _). unfold WO_FLAGP in *. lia.
  Qed.

  Lemma wscr_blkA : forall (e : went H) ff fp mr XS s LB m p A n a, as_RFS H ((3, ff, fp) :: w_LF e) mr ->
    as_RHEAP H s LB m -> In (p, A, n) LB -> Forall (fs_scratch H ((3, ff, fp) :: w_LF e)) XS ->
    (A <= a < A + n \/ sh A <= a < sh A + nsh n) -> ~ rin_ivs XS a.
  Proof.
    intros e ff fp mr XS s LB m p A n a RF RH IN FS Ha.
    apply rin_ivs_none. eapply Forall_impl; [| exact FS]. intros iv FSi.
    destruct (wscr_blk H HB _ s LB mr m p A n iv RF RH IN FSi) as [K1 K2]. lia.
  Qed.

  Lemma wS1cell_xp : forall (e : went H) ff fp LB XO XS mr m m' a cs,
    wpre H e -> as_RFS H ((3, ff, fp) :: w_LF e) mr -> fresh_frame H (w_LF e) 3 ff fp ->
    xpres H LB (wS1 e) (XO ++ XS) m m' -> Forall (fs_scratch H ((3, ff, fp) :: w_LF e)) XS ->
    Forall (fun iv : Z * Z => a + Z.of_nat (cells_size cs) <= fst iv \/ snd iv <= a) XO ->
    wS1 e <= a -> rw_cells asegs m a cs -> rw_cells asegs m' a cs.
  Proof.
    intros e ff fp LB XO XS mr m m' a cs HP RF FF XP FS FXO Ha C.
    pose proof (wpre_geo H e HP) as (CE & _). pose proof (wS1_facts H e HP) as (_ & _ & _ & _ & LOS1 & _).
    eapply xpres_rw_cells; [exact XP | exact C |]. split; [left; exact Ha|].
    apply Forall_app. split; [exact FXO|]. eapply Forall_impl; [| exact FS]. intros iv FSi.
    destruct (wfsw_ok H HB e ff fp mr iv RF FF CE FSi) as (_ & _ & _ & _ & _ & _ & B7 & _). right. lia.
  Qed.

  Lemma wstate_xp : forall (e : went H) ff fp s LB LB' XO XS mr m m' c,
    wpre H e -> as_RFS H ((3, ff, fp) :: w_LF e) mr -> fresh_frame H (w_LF e) 3 ff fp -> as_RHEAP H s LB m ->
    xpres H LB (wS1 e) (XO ++ XS) m m' -> Forall (fs_scratch H ((3, ff, fp) :: w_LF e)) XS ->
    Forall (fun iv : Z * Z => aceil <= fst iv) XO ->
    (forall p n, In (p, n) (state_blocks c) -> In (p, n) (lbl LB) /\ In (p, n) (lbl LB')) ->
    state_repA LB m (ff + 176) c -> state_sh m c -> state_repA LB' m' (ff + 176) c /\ state_sh m' c.
  Proof.
    intros e ff fp s LB LB' XO XS mr m m' c HP RF FF RH XP FS FXO BL R S.
    pose proof (wframe_facts H _ _ _ FF) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16).
    pose proof (wS1_facts H e HP) as (S32 & S1SP & S1L & SPH & LOS1 & CEL).
    pose proof aceil_facts as ACF.
    assert (SHC : sh aceil < aceil) by (unfold sh; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
    assert (BLO : forall p n, In (p, n) (state_blocks c) -> 0 < p /\ p mod 16 = 0 /\ 0 <= n /\ p + n <= aceil /\ sh p + nsh n <= sh aceil
                                                           /\ exists q, In (q, p, n) LB).
    { intros p n Hin. destruct (BL p n Hin) as [L1 _]. destruct (lbl_in_inv _ _ _ L1) as (q & Hq).
      pose proof (ah_blocks H HB _ _ _ _ RH Hq) as (B0 & B16 & Bn & BI & BC & BF & BAPP). cbn in B0, B16, Bn, BI, BC, BF, BAPP.
      destruct (sh_aapp_range _ _ BAPP Bn) as (_ & X2 & _).
      split; [exact B0|]. split; [exact B16|]. split; [exact Bn|]. split; [exact BC|]. split; [exact X2|]. exists q. exact Hq. }
    assert (NXO : forall a, a < aceil \/ (ff + 176 <= a < ff + 416) -> ~ rin_ivs XO a).
    { intros a Ha. apply rin_ivs_none. eapply Forall_impl; [| exact FXO]. intros iv K. cbn in K. lia. }
    split.
    - eapply (rep_keep H LB LB' LB (wS1 e) (XO ++ XS) m m' (ff + 176) c R XP).
      + apply (objx_intro H). { left. lia. }
        intros a Ha _ R0. apply rin_ivs_app in R0. destruct R0 as [R0|R0]; [exact (NXO a ltac:(right; lia) R0)|].
        exact (wscr_ff e ff fp mr XS a HP RF FF FS ltac:(unfold WO_FLAGP; lia) R0).
      + apply (blkx_intro H). intros p n Hin. destruct (BL p n Hin) as [L1 L2]. split; [exact L1|]. split; [exact L2|].
        intros a Ha R0. destruct (BLO p n Hin) as (B0 & B16 & Bn & BC & BS & q & Hq).
        apply rin_ivs_app in R0. destruct R0 as [R0|R0]; [exact (NXO a ltac:(left; lia) R0)|].
        exact (wscr_blkA e ff fp mr XS s LB m q p n a RF RH Hq FS (or_introl Ha) R0).
      + unfold AIMG_TOP. lia.
      + lia.
    - eapply (sh_keep H LB LB (wS1 e) (XO ++ XS) m m' (ff + 176) c R S XP).
      apply (blksh_intro H). intros p n Hin. destruct (BL p n Hin) as [L1 L2]. split; [exact L1|].
      intros a Ha R0. destruct (BLO p n Hin) as (B0 & B16 & Bn & BC & BS & q & Hq).
      apply rin_ivs_app in R0. destruct R0 as [R0|R0]; [exact (NXO a ltac:(left; lia) R0)|].
      exact (wscr_blkA e ff fp mr XS s LB m q p n a RF RH Hq FS (or_intror Ha) R0).
  Qed.

  Lemma wmva : forall (e : went H) ff fp XSc s LB (LBs1 LBs2 : list block) (c1 c2 : stateC) m msF mo (Q : config -> Prop)
      (ra t0 t1 t2 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
    wpre H e -> winv H e ff fp XSc s LB m -> addressable m (ff + 176) ST_SIZE ->
    as_VIS H s msF = MS (mkR ra (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) t0 t1 t2 (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
                           (Z_to_bv 64 (ff + 176)) (Z_to_bv 64 (wS1 e + 72)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 AST_MVA) fc None m (seg_rom asegs) ->
    frm_zero fc -> bv_unsigned ra mod 2 = 0 ->
    as_AKREL H s (mkCfg msF mo) -> 0 <= as_AL H s ->
    state_repA LB m (ff + 176) c1 -> state_sh m c1 -> state_repA LB m (wS1 e + 72) c2 -> state_sh m c2 ->
    Permutation LB (w_LB e ++ LBs1 ++ LBs2) -> Permutation (lbl LBs1) (state_blocks c1) -> Permutation (lbl LBs2) (state_blocks c2) ->
    (forall p n, In (p, n) (state_blocks c1) -> n <= 2 ^ 40) ->
    (forall msF' mo' s' LB' m' XS (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32),
       as_VIS H s' msF' = MS (mkR ra (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) t0' t1' t2' (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
                                (Z_to_bv 64 (ff + 176)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                          F' (ret_pc ra) fc' None m' (seg_rom asegs) ->
       frm_zero fc' -> as_AKREL H s' (mkCfg msF' mo') -> as_MPRES H mo mo' ->
       winv H e ff fp (XSc ++ XS) s' LB' m' ->
       xpres H (w_LB e) (wS1 e) ((ff + 176, ff + 176 + ST_SIZE) :: (wS1 e + 72, wS1 e + 72 + ST_SIZE) :: XS) m m' ->
       Forall (fs_scratch H ((3, ff, fp) :: w_LF e)) XS ->
       Permutation LB' (w_LB e ++ LBs2) ->
       state_repA LB' m' (ff + 176) (state_moved c1 c2) -> state_sh m' (state_moved c1 c2) ->
       state_repA LB' m' (wS1 e + 72) (state_emptied c2) ->
       as_AL H s' >= as_AL H s ->
       as_SR H Q (mkCfg msF' mo')) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros e ff fp XSc s LB LBs1 LBs2 c1 c2 m msF mo Q ra t0 t1 t2 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
      HP HI AD1 VIS FZ RA2 KR AL0 R1 SH1 R2 SH2 PLB P1 P2 CAP K.
    pose proof (wpre_geo H e HP) as (CE & LO & SSHI & SHIH & SP16 & TP).
    pose proof (wS1_facts H e HP) as (S32 & S1SP & S1L & SPH & LOS1 & _).
    pose proof (wframe_facts H _ _ _ (winv_ff H _ _ _ _ _ _ _ HI)) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16).
    pose proof aceil_facts as ACF.
    pose proof (winv_rh H _ _ _ _ _ _ _ HI) as RH.
    destruct (winv_er H _ _ _ _ _ _ _ HI) as (errv & ER).
    pose proof (winv_rf H _ _ _ _ _ _ _ HI) as RF.
    assert (AD2 : addressable m (wS1 e + 72) ST_SIZE).
    { unfold ST_SIZE. eapply (stack0_addr m (w_lo e) (w_shi e)); [exact (winv_s0 H _ _ _ _ _ _ _ HI) | lia | lia | clear - S32; Z.div_mod_to_equations; lia | reflexivity | lia]. }
    eapply (ah_seq H HB).
    { eapply (MVA ra (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) t0 t1 t2 (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
                (Z_to_bv 64 (ff + 176)) (Z_to_bv 64 (wS1 e + 72)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc msF m mo s LB (w_LB e) LBs1 LBs2 ((3, ff, fp) :: w_LF e) (ff + 176) (wS1 e + 72) c1 c2 (w_lo e) (w_B e) (w_shi e) errv);
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
      - left. unfold ST_SIZE. lia.
      - intros b Hb. pose proof (ah_blocks H HB _ _ _ _ RH Hb) as (B0 & B16 & Bn & BI & BC & BF & BAPP). unfold ST_SIZE. unfold AFS_SIZE in *. lia.
      - intros b Hb. pose proof (ah_blocks H HB _ _ _ _ RH Hb) as (B0 & B16 & Bn & BI & BC & BF & BAPP). unfold ST_SIZE. lia.
      - exists (3, ff, fp). split; [left; reflexivity|]. unfold ff_addr, ff_class. cbn [fst snd]. change (fsz 3) with 512. unfold ST_SIZE. lia.
      - right. unfold ST_SIZE. lia.
      - unfold ST_SIZE. lia.
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
    change ((ff + 176, ff + 176 + ST_SIZE) :: (wS1 e + 72, wS1 e + 72 + ST_SIZE) :: XS)
      with ([(ff + 176, ff + 176 + ST_SIZE); (wS1 e + 72, wS1 e + 72 + ST_SIZE)] ++ XS) in XP.
    eapply (winv_sr H HB e ff fp XSc XS _ s LB (w_LB e) s' LB' m m' HP HI (fun b Hb => Hb) XP FS).
    - apply Forall_cons; [right; left; cbn [fst snd]; unfold ST_SIZE, WO_FLAGP; lia|].
      apply Forall_cons; [right; right; right; cbn [fst snd]; unfold ST_SIZE, WO_SAVED; lia|].
      apply Forall_forall. intros iv Hiv. left. exact Hiv.
    - exact RF'.
    - exact RH'.
    - exact AC'.
    - exact MI'.
    - exact ST'.
    - exists errv'. exact ER'.
    - exact RA'.
    - apply Forall_cons; [cbn [fst snd]; intros _; replace (ff + 176 + ST_SIZE - (ff + 176)) with ST_SIZE by lia;
                          unfold ST_SIZE; apply (state_repA_wr LB' m' (ff + 176) (state_moved c1 c2) R1'); lia|].
      apply Forall_cons; [cbn [fst snd]; intros _; replace (wS1 e + 72 + ST_SIZE - (wS1 e + 72)) with ST_SIZE by lia;
                          unfold ST_SIZE; apply (state_repA_wr LB' m' (wS1 e + 72) (state_emptied c2) R2'); lia|].
      eapply Forall_impl; [| exact FS]. intros iv FSi Hiv. cbn [fst snd] in Hiv |- *.
      destruct (wfsw_ok H HB e ff fp m' iv RF' (winv_ff H _ _ _ _ _ _ _ HI) CE FSi) as (W1 & _ & _ & B4 & B5 & _ & B7 & _).
      destruct (W1 LB') as [A1|[A1|[A1|[A1|[A1|[A1|A1]]]]]]; cbn in A1;
        (split; [unfold WO_FLAGP in *; unfold sh in *; rewrite ?ASHADOW_BASE_val in *; lia|]; split; [unfold AAPP_HI, AHI_LO, AFS_SIZE in *; lia|]; intros i Hi; exfalso; unfold WO_FLAGP in *; lia).
  Qed.

  Lemma wdtT : forall (e : went H) ff fp XSc s LB (c : stateC) m msF mo (Q : config -> Prop) (r : Z)
      (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
    wpre H e -> winv H e ff fp XSc s LB m -> (forall b, In b (w_LB e) -> In b LB) ->
    as_VIS H s msF = MS (mkR (Z_to_bv 64 r) (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) t0 t1 t2 (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
                           (Z_to_bv 64 (wS1 e + 72)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 AST_DTOR) fc None m (seg_rom asegs) ->
    frm_zero fc -> 0 <= r < 2 ^ 64 -> r mod 2 = 0 -> In (APC0_FREE, [r]) PO_PF ->
    as_AKREL H s (mkCfg msF mo) -> 0 <= as_AL H s ->
    state_repA LB m (wS1 e + 72) c -> state_sh m c -> state_blocks c = [] ->
    (forall msF' mo' s' LB' m' XS (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32),
       as_VIS H s' msF' = MS (mkR (Z_to_bv 64 r) (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) t0' t1' t2' (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
                                a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                          F' (Z_to_bv 64 r) fc' None m' (seg_rom asegs) ->
       frm_zero fc' -> as_AKREL H s' (mkCfg msF' mo') -> as_MPRES H mo mo' ->
       winv H e ff fp (XSc ++ XS) s' LB' m' ->
       xpres H LB (wS1 e) ((wS1 e + 72, wS1 e + 72 + ST_SIZE) :: XS) m m' ->
       Forall (fs_scratch H ((3, ff, fp) :: w_LF e)) XS ->
       Permutation LB' LB -> wr_at asegs m' (wS1 e + 72) ST_SIZE ->
       as_AL H s' >= as_AL H s ->
       as_SR H Q (mkCfg msF' mo')) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros e ff fp XSc s LB c m msF mo Q r t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
      HP HI INC VIS FZ Hr RE INPF KR AL0 R SH SB K.
    pose proof (wpre_geo H e HP) as (CE & LO & SSHI & SHIH & SP16 & TP).
    pose proof (wS1_facts H e HP) as (S32 & S1SP & S1L & SPH & LOS1 & _).
    pose proof (wframe_facts H _ _ _ (winv_ff H _ _ _ _ _ _ _ HI)) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16).
    pose proof aceil_facts as ACF.
    pose proof (winv_rh H _ _ _ _ _ _ _ HI) as RH.
    destruct (winv_er H _ _ _ _ _ _ _ HI) as (errv & ER).
    pose proof (winv_rf H _ _ _ _ _ _ _ HI) as RF.
    destruct (wchain_call H HB e ff fp XSc s LB m HP HI) as [CH CHU].
    assert (AD2 : addressable m (wS1 e + 72) ST_SIZE).
    { unfold ST_SIZE. eapply (stack0_addr m (w_lo e) (w_shi e)); [exact (winv_s0 H _ _ _ _ _ _ _ HI) | lia | lia | clear - S32; Z.div_mod_to_equations; lia | reflexivity | lia]. }
    eapply (ah_seq H HB).
    { eapply (DTOR (Z_to_bv 64 r) (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) t0 t1 t2 (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
                (Z_to_bv 64 (wS1 e + 72)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                F fc msF m mo s LB LB [] ((3, ff, fp) :: w_LF e) (wS1 e + 72) c (w_lo e) (w_B e) (w_shi e) errv
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
      - intros b Hb. pose proof (ah_blocks H HB _ _ _ _ RH Hb) as (B0 & B16 & Bn & BI & BC & BF & BAPP). unfold ST_SIZE. lia.
      - right. unfold ST_SIZE. lia.
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
    change ((wS1 e + 72, wS1 e + 72 + ST_SIZE) :: XS) with ([(wS1 e + 72, wS1 e + 72 + ST_SIZE)] ++ XS) in XP.
    eapply (winv_sr H HB e ff fp XSc XS _ s LB LB s' LB' m m' HP HI INC XP FS).
    - apply Forall_cons; [right; right; right; cbn [fst snd]; unfold ST_SIZE, WO_SAVED; lia|].
      apply Forall_forall. intros iv Hiv. left. exact Hiv.
    - exact RF'.
    - exact RH'.
    - exact AC'.
    - exact MI'.
    - exact ST'.
    - exists errv'. exact ER'.
    - exact RA'.
    - apply Forall_cons; [cbn [fst snd]; intros _; replace (wS1 e + 72 + ST_SIZE - (wS1 e + 72)) with ST_SIZE by lia; exact WR'|].
      eapply Forall_impl; [| exact FS]. intros iv FSi Hiv. cbn [fst snd] in Hiv |- *.
      destruct (wfsw_ok H HB e ff fp m' iv RF' (winv_ff H _ _ _ _ _ _ _ HI) CE FSi) as (W1 & _ & _ & B4 & B5 & _ & B7 & _).
      destruct (W1 LB') as [A1|[A1|[A1|[A1|[A1|[A1|A1]]]]]]; cbn in A1;
        (split; [unfold WO_FLAGP in *; unfold sh in *; rewrite ?ASHADOW_BASE_val in *; lia|]; split; [unfold AAPP_HI, AHI_LO, AFS_SIZE in *; lia|]; intros i Hi; exfalso; unfold WO_FLAGP in *; lia).
  Qed.

  Definition wv1_post (e : went H) (ff fp : Z) (XS : list (Z * Z)) (sk : as_St H) (LBk : list block) (g h k : Z)
      : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32) m',
      ms' = MS (mkR (Z_to_bv 64 WO_DT1_RA) (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) x5 x6 x7 (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
                    (Z_to_bv 64 (wS1 e + 72)) x11 x12 x13 x14 x15 x16 x17
                    (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) (Z_to_bv 64 0) (Z_to_bv 64 k) (Z_to_bv 64 99)
                    (Z_to_bv 64 k) (Z_to_bv 64 (k + 100)) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31)
               F (Z_to_bv 64 AST_DTOR) fc None m' (seg_rom asegs)
      /\ frm_zero fc
      /\ winv H e ff fp XS sk LBk m' /\ wfc H e ff m' /\ rw_cells asegs m' (wS1 e + 48) [C8 (Z_to_bv 64 (ff + 176))]
      /\ state_repA LBk m' (ff + 176) (mkfreshA (w_words e) (w_n e) g h k) /\ state_sh m' (mkfreshA (w_words e) (w_n e) g h k)
      /\ state_repA LBk m' (wS1 e + 72) (state_emptied (mkfreshA (w_words e) (w_n e) g h k))
      /\ 0 < g /\ 0 < h /\ 0 < k.

  Definition wx1_post (e : went H) (ff fp : Z) (XS : list (Z * Z)) (sk : as_St H) (LBk : list block) (g h k : Z)
      : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 (F : bvmap 5 word) (fc : bv 32) m',
      ms' = MS (mkR (Z_to_bv 64 AWO_PM_RA) (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) x5 x6 x7 (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
                    (Z_to_bv 64 (ff + 128)) x11 x12 x13 x14 x15 x16 x17
                    (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) (Z_to_bv 64 0) (Z_to_bv 64 k) (Z_to_bv 64 99)
                    (Z_to_bv 64 k) (Z_to_bv 64 (k + 100)) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31)
               F (Z_to_bv 64 APM_ENTRY) fc None m' (seg_rom asegs)
      /\ frm_zero fc
      /\ winv H e ff fp XS sk LBk m' /\ wfc H e ff m' /\ rw_cells asegs m' (wS1 e + 48) [C8 (Z_to_bv 64 (ff + 176))]
      /\ state_repA LBk m' (ff + 176) (mkfreshA (w_words e) (w_n e) g h k) /\ state_sh m' (mkfreshA (w_words e) (w_n e) g h k)
      /\ 0 < g /\ 0 < h /\ 0 < k
      /\ wr_at asegs m' (wS1 e + 72) ST_SIZE.

  Lemma munch_nil_eq : forall (m m' : mem), munch [] m m' -> m' = m.
  Proof. intros m m' MU. apply functional_extensionality. intros x. apply MU. exact I. Qed.

  Lemma seg_mva1 : forall (Q : config -> Prop) (e : went H) ff fp msF mo s6 (p1 p2 p3 p4 p5 p6 : bptr) b1 b2 b3 g h k,
    let LB6 := (p6, k, 100) :: (p5, h, 100) :: (p4, g, 500) :: (p3, b3, 100) :: (p2, b2, 100) :: (p1, b1, 500) :: w_LB e in
    wpre H e -> as_AKREL H s6 (mkCfg msF mo) -> as_MPRES H (w_mo e) mo -> as_AL H s6 >= as_AL H (w_s e) ->
    wq3_post H e ff fp s6 LB6 b1 b2 b3 g h k (as_VIS H s6 msF) ->
    (forall msF' mo' s7 LB7 XS, as_AKREL H s7 (mkCfg msF' mo') -> as_MPRES H (w_mo e) mo' -> as_AL H s7 >= as_AL H (w_s e) ->
       Permutation LB7 (w_LB e ++ [(p4, g, 500); (p5, h, 100); (p6, k, 100)]) ->
       wv1_post e ff fp XS s7 LB7 g h k (as_VIS H s7 msF') -> as_SR H Q (mkCfg msF' mo')) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros Q e ff fp msF mo s6 p1 p2 p3 p4 p5 p6 b1 b2 b3 g h k LB6 HP KR MP AL6 P7 K.
    destruct P7 as (x5 & x6 & x7 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m0 & VIS & HI & WC & C48 & PS & TS & WG & WH & WK).
    pose proof (wS1_facts H e HP) as (S32 & S1SP & S1L & SPH & LOS1 & CEL).
    pose proof (wpre_geo H e HP) as (CE & LO & SSHI & SHIH & SP16 & TP).
    pose proof (wpre_budget H e HP) as (HN & BS & BC & BL & AL0).
    pose proof (po_budget_facts (w_n e) ltac:(lia)) as (PB1 & PB2 & PB3 & PB4).
    pose proof HP as (FZ0 & _).
    assert (PA : Permutation LB6 ([(p1, b1, 500); (p2, b2, 100); (p3, b3, 100)] ++ ((p6, k, 100) :: (p5, h, 100) :: (p4, g, 500) :: w_LB e))).
    { unfold LB6. etransitivity; [| apply Permutation_app_comm]. cbn [app].
      apply Permutation_cons; [reflexivity|]. apply Permutation_cons; [reflexivity|]. apply Permutation_cons; [reflexivity|].
      etransitivity; [apply perm_wo3 | apply Permutation_app_comm]. }
    assert (PB : Permutation LB6 ([(p4, g, 500); (p5, h, 100); (p6, k, 100)] ++ ((p3, b3, 100) :: (p2, b2, 100) :: (p1, b1, 500) :: w_LB e)))
      by (unfold LB6; apply perm_wo3).
    destruct (wst_P_rep H HB e ff fp [] s6 LB6 m0 p1 p2 p3 b1 b2 b3 _ HP HI PS
                ltac:(unfold LB6; cbn; tauto) ltac:(unfold LB6; cbn; tauto) ltac:(unfold LB6; cbn; tauto) PA) as (R1 & SH1 & B1 & B2 & B3).
    destruct (wst_T_rep H HB e ff fp [] s6 LB6 m0 p4 p5 p6 g h k _ HP HI TS WG WH WK
                ltac:(unfold LB6; cbn; tauto) ltac:(unfold LB6; cbn; tauto) ltac:(unfold LB6; cbn; tauto) PB) as (R2 & SH2 & G1 & G2 & G3).
    pose proof (wframe_facts H _ _ _ (winv_ff H _ _ _ _ _ _ _ HI)) as (Fa1 & Fa2 & Fa3 & _).
    assert (AD1 : addressable m0 (ff + 176) ST_SIZE).
    { destruct WC as (_ & _ & _ & _ & _ & U & _). unfold ST_SIZE. replace (ff + 176) with (ff + 128 + 48) by lia.
      eapply (addressable_sub8 m0 (ff + 128) 288 48 240); [exact (wo_pad m0 ff U Fa3 ltac:(lia)) | reflexivity | reflexivity | reflexivity | lia | lia | lia]. }
    eapply (wmva e ff fp [] s6 LB6 [(p1, b1, 500); (p2, b2, 100); (p3, b3, 100)] [(p4, g, 500); (p5, h, 100); (p6, k, 100)]
              (mkfreshA 0 0 b1 b2 b3) (mkfreshA (w_words e) (w_n e) g h k) m0 msF mo Q);
      [exact HP | exact HI | exact AD1 | exact VIS | exact FZ0 | reflexivity | exact KR | lia | exact R1 | exact SH1 | exact R2 | exact SH2
      | unfold LB6; apply perm_wo6
      | rewrite mkfreshA_blocks by lia; apply Permutation_refl
      | rewrite mkfreshA_blocks by lia; apply Permutation_refl
      | rewrite mkfreshA_blocks by lia; intros p n Hin; destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; lia |].
    intros msF' mo' s' LB' m' XS t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' VIS' FZ' KR' MP' HI' XP FS PERM R1' SH1' R2' AL'.
    rewrite (ret_pc_even WO_MVA1_RA ltac:(unfold WO_MVA1_RA; lia) eq_refl) in VIS'.
    rewrite state_moved_mkfreshA in R1', SH1'.
    pose proof (winv_rf H _ _ _ _ _ _ _ HI') as RF'.
    assert (WC' : wfc H e ff m').
    { eapply (wfc_xpres H e ff fp (w_LB e) _ m0 m' HP (winv_ff H _ _ _ _ _ _ _ HI) WC XP).
      pose proof (wframe_facts H _ _ _ (winv_ff H _ _ _ _ _ _ _ HI)) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16).
      apply Forall_cons; [unfold wfc_apart, ST_SIZE; cbn [fst snd]; unfold AFS_SIZE in *; lia|].
      apply Forall_cons; [unfold wfc_apart, ST_SIZE; cbn [fst snd]; lia|].
      eapply Forall_impl; [| exact FS]. intros iv FSi. exact (wscr_apart H HB e ff fp m' iv HP RF' (winv_ff H _ _ _ _ _ _ _ HI) FSi). }
    assert (C48' : rw_cells asegs m' (wS1 e + 48) [C8 (Z_to_bv 64 (ff + 176))]).
    { change ((ff + 176, ff + 176 + ST_SIZE) :: (wS1 e + 72, wS1 e + 72 + ST_SIZE) :: XS)
        with ([(ff + 176, ff + 176 + ST_SIZE); (wS1 e + 72, wS1 e + 72 + ST_SIZE)] ++ XS) in XP.
      eapply (wS1cell_xp e ff fp (w_LB e) _ XS m' m0 m'); [exact HP | exact RF' | exact (winv_ff H _ _ _ _ _ _ _ HI) | exact XP | exact FS | | lia | exact C48].
      pose proof (wframe_facts H _ _ _ (winv_ff H _ _ _ _ _ _ _ HI)) as (F1 & F2 & _).
      apply Forall_cons; [cbn [fst snd cells_size csize]; unfold ST_SIZE; lia|]. apply Forall_cons; [cbn [fst snd cells_size csize]; unfold ST_SIZE; lia | apply Forall_nil]. }

    pose proof (wframe_z H _ _ _ (winv_ff H _ _ _ _ _ _ _ HI')) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & FAPP & FSH).
    eapply (ahh_evt_then H HB (wd1_post (w_gp e) (w_tp e) F' fc' (wSP e) (wS1 e) ff (w_lo e) k m') Q s' msF' _ mo'); [exact KR' | exact VIS' | |].
    { exact (wd1 (w_gp e) (w_tp e) t0' t1' t2' (Z_to_bv 64 (ff + 176)) a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' (wSP e) (wS1 e) ff (w_lo e) k
                 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) F3 ltac:(lia) ltac:(lia) FSH FAPP (winv_stk H _ _ _ _ _ _ _ HI') (winv_mi H _ _ _ _ _ _ _ HI')). }
    intros msF2 mo2 KR2 MP2 (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m1 & EQ & MU & WM & MI1 & ST1).
    pose proof (munch_nil_eq m' m1 MU) as EM. subst m1.
    eapply (K msF2 mo2 s' LB' XS); [exact KR2 | mpres_chain | lia | exact PERM |].
    unfold wv1_post. rewrite EQ.
    do 14 eexists. exists F', fc', m'. split; [reflexivity|].
    split; [exact FZ'|]. split; [exact HI'|]. split; [exact WC'|]. split; [exact C48'|].
    split; [exact R1'|]. split; [exact SH1'|]. split; [exact R2'|]. lia.
  Qed.

  Lemma seg_dt1 : forall (Q : config -> Prop) (e : went H) ff fp msF mo s7 LB7 XS7 (p4 p5 p6 : bptr) g h k,
    wpre H e -> as_AKREL H s7 (mkCfg msF mo) -> as_MPRES H (w_mo e) mo -> as_AL H s7 >= as_AL H (w_s e) ->
    Permutation LB7 (w_LB e ++ [(p4, g, 500); (p5, h, 100); (p6, k, 100)]) ->
    wv1_post e ff fp XS7 s7 LB7 g h k (as_VIS H s7 msF) ->
    (forall msF' mo' s8 LB8 XS, as_AKREL H s8 (mkCfg msF' mo') -> as_MPRES H (w_mo e) mo' -> as_AL H s8 >= as_AL H (w_s e) ->
       Permutation LB8 (w_LB e ++ [(p4, g, 500); (p5, h, 100); (p6, k, 100)]) ->
       wx1_post e ff fp XS s8 LB8 g h k (as_VIS H s8 msF') -> as_SR H Q (mkCfg msF' mo')) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros Q e ff fp msF mo s7 LB7 XS7 p4 p5 p6 g h k HP KR MP AL7 PERM7 P8 K.
    destruct P8 as (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & F & fc & m0
                    & VIS & FZ & HI & WC & C48 & R1 & SH1 & R2 & G1 & G2 & G3).
    pose proof (wS1_facts H e HP) as (S32 & S1SP & S1L & SPH & LOS1 & CEL).
    pose proof (wpre_geo H e HP) as (CE & LO & SSHI & SHIH & SP16 & TP).
    pose proof (wpre_budget H e HP) as (HN & BS & BC & BL & AL0).
    pose proof (po_budget_facts (w_n e) ltac:(lia)) as (PB1 & PB2 & PB3 & PB4).
    assert (INC : forall b, In b (w_LB e) -> In b LB7).
    { intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact PERM7|]. apply in_or_app. left. exact Hb. }
    eapply (wdtT e ff fp XS7 s7 LB7 (state_emptied (mkfreshA (w_words e) (w_n e) g h k)) m0 msF mo Q WO_DT1_RA);
      [exact HP | exact HI | exact INC | exact VIS | exact FZ | unfold WO_DT1_RA; lia | reflexivity
      | unfold PO_PF, WO_DT1_RA; cbn; tauto | exact KR | lia | exact R2 | apply state_sh_emptied | reflexivity |].
    intros msF' mo' s' LB' m' XS t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' VIS' FZ' KR' MP' HI' XP FS PERM WR' AL'.
    pose proof (winv_rf H _ _ _ _ _ _ _ HI') as RF'.
    assert (WC' : wfc H e ff m').
    { eapply (wfc_xpres H e ff fp LB7 _ m0 m' HP (winv_ff H _ _ _ _ _ _ _ HI) WC XP).
      pose proof (wframe_facts H _ _ _ (winv_ff H _ _ _ _ _ _ _ HI)) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16).
      apply Forall_cons; [unfold wfc_apart, ST_SIZE; cbn [fst snd]; lia|].
      eapply Forall_impl; [| exact FS]. intros iv FSi. exact (wscr_apart H HB e ff fp m' iv HP RF' (winv_ff H _ _ _ _ _ _ _ HI) FSi). }
    pose proof (winv_rh H _ _ _ _ _ _ _ HI) as RH7.
    assert (PERM' : Permutation LB' (w_LB e ++ [(p4, g, 500); (p5, h, 100); (p6, k, 100)])) by (etransitivity; [exact PERM | exact PERM7]).
    change ((wS1 e + 72, wS1 e + 72 + ST_SIZE) :: XS) with ([(wS1 e + 72, wS1 e + 72 + ST_SIZE)] ++ XS) in XP.
    assert (C48' : rw_cells asegs m' (wS1 e + 48) [C8 (Z_to_bv 64 (ff + 176))]).
    { eapply (wS1cell_xp e ff fp LB7 _ XS m' m0 m'); [exact HP | exact RF' | exact (winv_ff H _ _ _ _ _ _ _ HI) | exact XP | exact FS | | lia | exact C48].
      apply Forall_cons; [cbn [fst snd cells_size csize]; unfold ST_SIZE; lia | apply Forall_nil]. }
    assert (BLK : forall p n, In (p, n) (state_blocks (mkfreshA (w_words e) (w_n e) g h k)) -> In (p, n) (lbl LB7) /\ In (p, n) (lbl LB')).
    { rewrite mkfreshA_blocks by lia. intros p n Hin.
      assert (IN7 : In (p, n) (lbl [(p4, g, 500); (p5, h, 100); (p6, k, 100)])) by (cbn; destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; tauto).
      destruct (lbl_in_inv _ _ _ IN7) as (q & Hq).
      split; [apply (lbl_in _ q) | apply (lbl_in _ q)]; (eapply Permutation_in; [apply Permutation_sym; eassumption|]; apply in_or_app; right; exact Hq). }
    destruct (wstate_xp e ff fp s7 LB7 LB' _ XS m' m0 m' (mkfreshA (w_words e) (w_n e) g h k) HP RF' (winv_ff H _ _ _ _ _ _ _ HI) RH7 XP FS
                ltac:(apply Forall_cons; [cbn [fst snd]; lia | apply Forall_nil]) BLK R1 SH1) as [R1' SH1'].

    pose proof (wframe_z H _ _ _ (winv_ff H _ _ _ _ _ _ _ HI')) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & FAPP & FSH).
    eapply (ahh_evt_then H HB (wd2_post (w_gp e) (w_tp e) F' fc' (wSP e) (wS1 e) ff (w_lo e) k m') Q s' msF' _ mo'); [exact KR' | exact VIS' | |].
    { exact (wd2 (w_gp e) (w_tp e) t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' (wSP e) (wS1 e) ff (w_lo e) k
                 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) F3 ltac:(lia) ltac:(lia) FSH FAPP (winv_stk H _ _ _ _ _ _ _ HI') (winv_mi H _ _ _ _ _ _ _ HI')). }
    intros msF2 mo2 KR2 MP2 (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m1 & EQ & MU & WM & MI1 & ST1).
    pose proof (munch_nil_eq m' m1 MU) as EM. subst m1.
    eapply (K msF2 mo2 s' LB' (XS7 ++ XS)); [exact KR2 | mpres_chain | lia | exact PERM' |].
    unfold wx1_post. rewrite EQ.
    do 14 eexists. exists F', fc', m'. split; [reflexivity|].
    split; [exact FZ'|]. split; [exact HI'|]. split; [exact WC'|]. split; [exact C48'|].
    split; [exact R1'|]. split; [exact SH1'|]. split; [lia|]. split; [lia|]. split; [lia|]. exact WR'.
  Qed.
End WoS3.
