(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import FunctionalExtensionality.
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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_WoR2 LbB_WoR3 LbB_WoR4 LbB_WoR5 LbB_WoE0 LbB_WoE0b LbB_WoQ LbB_WoF LbB_WoVec.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_WoBP LbB_WoBPsh LbB_WoS3 LbB_WoT2 LbB_WoR6 LbB_WoRv LbB_WoS4.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section WoS5.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHb : asan_rt_hyps_bp H.
  Hypothesis HOWN : rt_own H.
  Hypothesis MVA : st_mva_stmt H.
  Hypothesis DTOR : st_dtor_stmt H.
  Hypothesis WTR : po_tr_ok H.
  Let HB := rt_bp_base H HHb.

  Lemma wdtP : forall (e : went H) ff fp XSc s LB (LBs : list block) (c : stateC) m msF mo (Q : config -> Prop) (r o : Z)
      (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
    wpre H e -> winv H e ff fp XSc s LB m ->
    ff + 8 <= o -> o + ST_SIZE <= ff + WO_FLAGP -> addressable m o ST_SIZE ->
    as_VIS H s msF = MS (mkR (Z_to_bv 64 r) (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) t0 t1 t2 (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
                           (Z_to_bv 64 o) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 AST_DTOR) fc None m (seg_rom asegs) ->
    frm_zero fc -> 0 <= r < 2 ^ 64 -> r mod 2 = 0 -> In (APC0_FREE, [r]) PO_PF ->
    as_AKREL H s (mkCfg msF mo) -> 0 <= as_AL H s ->
    state_repA LB m o c -> state_sh m c ->
    Permutation LB (w_LB e ++ LBs) -> Permutation (lbl LBs) (state_blocks c) ->
    (forall p n, In (p, n) (state_blocks c) -> n <= 2 ^ 40) ->
    (forall msF' mo' s' LB' m' XS (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32),
       as_VIS H s' msF' = MS (mkR (Z_to_bv 64 r) (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) t0' t1' t2' (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
                                a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                          F' (Z_to_bv 64 r) fc' None m' (seg_rom asegs) ->
       frm_zero fc' -> as_AKREL H s' (mkCfg msF' mo') -> as_MPRES H mo mo' ->
       winv H e ff fp (XSc ++ XS) s' LB' m' ->
       xpres H (w_LB e) (wS1 e) ((o, o + ST_SIZE) :: XS) m m' ->
       Forall (fs_scratch H ((6, ff, fp) :: w_LF e)) XS ->
       Permutation LB' (w_LB e) -> wr_at asegs m' o ST_SIZE ->
       as_AL H s' >= as_AL H s ->
       as_SR H Q (mkCfg msF' mo')) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros e ff fp XSc s LB LBs c m msF mo Q r o t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
      HP HI O1 O2 AD2 VIS FZ Hr RE INPF KR AL0 R SH PLB PBL CAP K.
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
                F fc msF m mo s LB (w_LB e) LBs ((6, ff, fp) :: w_LF e) o c (w_lo e) (w_B e) (w_shi e) errv
                ((wSP e, bv_unsigned (w_ra e)) :: w_CH e));
        rewrite ?HLib.u64_of_Z by lia.
      - exact VIS.
      - exact FZ.
      - reflexivity.
      - exact R.
      - exact SH.
      - exact PLB.
      - exact PBL.
      - exact CAP.
      - exact AD2.
      - intros b Hb. pose proof (ah_blocks H HB _ _ _ _ RH Hb) as (B0 & B16 & Bn & BI & BC & BF & BAPP). unfold ST_SIZE, WO_FLAGP in *. unfold AFS_SIZE in *. lia.
      - left. exists (6, ff, fp). split; [left; reflexivity|]. unfold ff_addr, ff_class. cbn [fst snd]. change (fsz 6) with 4096. unfold ST_SIZE, WO_FLAGP in *. lia.
      - right. unfold ST_SIZE, WO_FLAGP in *. lia.
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
      - exact (wtr_dtor H WTR).
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
    eapply (winv_sr H HB e ff fp XSc XS _ s LB (w_LB e) s' LB' m m' HP HI (fun b Hb => Hb) XP FS).
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

  Lemma munch_nil_eq5 : forall (m m' : mem), munch [] m m' -> m' = m.
  Proof. intros m m' MU. apply functional_extensionality. intros x. apply MU. exact I. Qed.

  Lemma wtx_apart : forall (e : went H) ff fp XSc s LB m XO XS (P : Z * Z -> Prop),
    wpre H e -> winv H e ff fp XSc s LB m -> Forall (fs_scratch H ((6, ff, fp) :: w_LF e)) XS ->
    (forall iv, wfc_apart H e ff iv -> P iv) -> Forall P XO -> Forall P (XO ++ XS).
  Proof.
    intros e ff fp XSc s LB m XO XS P HP HI FS IMP FO. apply Forall_app. split; [exact FO|].
    eapply Forall_impl; [| exact FS]. intros iv Hiv. apply IMP.
    exact (wscr_apart H HB e ff fp m iv HP (winv_rf H _ _ _ _ _ _ _ HI) (winv_ff H _ _ _ _ _ _ _ HI) Hiv).
  Qed.

  Lemma wsx_wr : forall (e : went H) ff fp XSc sk LBk LB m m' X o k,
    wpre H e -> winv H e ff fp XSc sk LBk m -> xpres H LB (wS1 e) X m m' -> wr_at asegs m (sh ff + o) k ->
    0 <= o -> 0 <= k -> o + k <= 476 ->
    Forall (fun iv : Z * Z => sh ff + 476 <= fst iv \/ snd iv <= sh ff) X -> wr_at asegs m' (sh ff + o) k.
  Proof.
    intros e ff fp XSc sk LBk LB m m' X o k HP HI XP W O0 K0 OK FX.
    destruct (wrv_fsb H e ff fp XSc sk LBk m HP HI) as (B1 & B2 & F64 & FC & FAPP).
    eapply (xpres_wr_at H); [exact XP | exact W |]. split.
    - unfold aclient_range. right; right; right; right; right; left.
      clear - B1 B2 F64 O0 K0 OK. unfold sh. Z.div_mod_to_equations. lia.
    - eapply Forall_impl; [| exact FX]. intros iv Kv. cbn in Kv. lia.
  Qed.

  Lemma wsx_ad : forall (e : went H) ff fp XSc sk LBk LB m m' X A n,
    wpre H e -> winv H e ff fp XSc sk LBk m -> xpres H LB (wS1 e) X m m' -> addressable m A n ->
    ff <= A -> A + n <= ff + 3808 ->
    Forall (fun iv : Z * Z => sh ff + 476 <= fst iv \/ snd iv <= sh ff) X -> addressable m' A n.
  Proof.
    intros e ff fp XSc sk LBk LB m m' X A n HP HI XP AD A1 A2 FX.
    destruct (wrv_fsb H e ff fp XSc sk LBk m HP HI) as (B1 & B2 & F64 & FC & FAPP).
    destruct AD as (N0 & A0 & A8 & U). split; [exact N0|]. split; [exact A0|]. split; [exact A8|].
    eapply (xpres_u8arr H); [exact XP | exact U |].
    rewrite (shadow_of_length n N0).
    split.
    - unfold aclient_range. right; right; right; right; right; left.
      clear - B1 B2 A1 A2 A8 N0. unfold sh, nsh. Z.div_mod_to_equations. lia.
    - eapply Forall_impl; [| exact FX]. intros iv K. cbn in K.
      clear - K F64 A1 A2 A8 N0. unfold sh, nsh in *. Z.div_mod_to_equations. lia.
  Qed.

  Lemma wfw_sh : forall (e : went H) ff fp XSc s LB m (iv : Z * Z), wpre H e -> winv H e ff fp XSc s LB m ->
    ff <= fst iv -> snd iv <= ff + 4096 -> sh ff + 476 <= fst iv \/ snd iv <= sh ff.
  Proof.
    intros e ff fp XSc s LB m iv HP HI I1 I2.
    pose proof (wframe_bounds H e ff fp XSc s LB m HP HI) as (_ & _ & _ & _ & _ & _ & SH1 & _).
    destruct SH1 as [X|X]; [left | right]; lia.
  Qed.

  Lemma wtc_xp : forall (e : went H) ff fp XSc s LB LBx m m' XO XS,
    wpre H e -> winv H e ff fp XSc s LB m -> xpres H LBx (wS1 e) (XO ++ XS) m m' ->
    Forall (fs_scratch H ((6, ff, fp) :: w_LF e)) XS ->
    Forall (fun iv : Z * Z => ff <= fst iv /\ snd iv <= ff + WO_FLAGP /\ (snd iv <= ff + 3408 \/ ff + 3416 <= fst iv)) XO ->
    wtc H e ff m -> wtc H e ff m'.
  Proof.
    intros e ff fp XSc s LB LBx m m' XO XS HP HI XP FS FO (C1 & C2 & C3 & C4 & W).
    pose proof (wframe_bounds H e ff fp XSc s LB m HP HI) as (F0 & F64 & FLO & FH & FL & FS1 & SH1 & SH2 & S1L & S1SP & SPH & LOS1).
    unfold WO_FLAGP, AINTRIN_STACK in *.
    assert (AP : forall A k, wS1 e <= A -> A + k <= wS1 e + 64 ->
                   Forall (fun iv : Z * Z => A + k <= fst iv \/ snd iv <= A) (XO ++ XS)).
    { intros A k K1 K2. eapply (wtx_apart e ff fp XSc s LB m XO XS); [exact HP | exact HI | exact FS | |].
      - intros iv (_ & _ & _ & _ & _ & A6 & _). lia.
      - eapply Forall_impl; [| exact FO]. intros iv K. cbn in K. lia. }
    split; [|split; [|split; [|split]]].
    - eapply (wrv_xs1 H e ff fp XSc s LB LBx m m' (XO ++ XS)); [exact HP | exact HI | exact XP | exact C1 | lia |].
      eapply Forall_impl; [| apply (AP (wS1 e) 16); lia]. intros iv K. cbn in K |- *. lia.
    - eapply (wrv_xs1 H e ff fp XSc s LB LBx m m' (XO ++ XS)); [exact HP | exact HI | exact XP | exact C2 | lia |].
      eapply Forall_impl; [| apply (AP (wS1 e + 40) 8); lia]. intros iv K. cbn in K |- *. lia.
    - eapply (wrv_xs1 H e ff fp XSc s LB LBx m m' (XO ++ XS)); [exact HP | exact HI | exact XP | exact C3 | lia |].
      eapply Forall_impl; [| apply (AP (wS1 e + 56) 8); lia]. intros iv K. cbn in K |- *. lia.
    - eapply (wrv_xcells H e ff fp XSc s LB LBx m m' (XO ++ XS)); [exact HP | exact HI | exact XP | exact C4 | lia | cbn; lia |].
      eapply (wtx_apart e ff fp XSc s LB m XO XS); [exact HP | exact HI | exact FS | |].
      + intros iv (_ & _ & A3 & _). cbn. lia.
      + eapply Forall_impl; [| exact FO]. intros iv K. cbn in K |- *. lia.
    - replace (sh ff) with (sh ff + 0) by lia. replace (sh ff) with (sh ff + 0) in W by lia.
      eapply (wsx_wr e ff fp XSc s LB LBx m m' (XO ++ XS) 0 476 HP HI XP W ltac:(lia) ltac:(lia) ltac:(lia)).
      eapply (wtx_apart e ff fp XSc s LB m XO XS); [exact HP | exact HI | exact FS | |].
      + intros iv (_ & _ & _ & _ & A5 & _). lia.
      + eapply Forall_impl; [| exact FO]. intros iv K. cbn in K.
        exact (wfw_sh e ff fp XSc s LB m iv HP HI ltac:(lia) ltac:(lia)).
  Qed.

  Definition wtd (e : went H) (ff fp : Z) (XS : list (Z * Z)) (s : as_St H) (LB LBs : list block) (m : mem) (c : stateC) : Prop :=
       winv H e ff fp XS s LB m /\ wtc H e ff m
    /\ state_repA LB m (ff + 3504) c /\ state_sh m c
    /\ Permutation LB (w_LB e ++ LBs) /\ Permutation (lbl LBs) (state_blocks c)
    /\ (forall p n, In (p, n) (state_blocks c) -> n <= 2 ^ 40)
    /\ addressable m (ff + 3456) 288.

  Definition ww3 (e : went H) (ff fp : Z) (XS : list (Z * Z)) (s : as_St H) (LB : list block) (m : mem) : Prop :=
    winv H e ff fp XS s LB m /\ wtc H e ff m /\ Permutation LB (w_LB e).

  Lemma seg_dt3 : forall (Q : config -> Prop) (e : went H) ff fp XS s LB LBs m msF mo c
      (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32),
    wpre H e -> wtd e ff fp XS s LB LBs m c -> frm_zero fc -> as_AKREL H s (mkCfg msF mo) -> 0 <= as_AL H s ->
    as_VIS H s msF = MS (mkR (Z_to_bv 64 WO_DT3_RA) (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) x5 x6 x7
                           (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e)) (Z_to_bv 64 (ff + 3504)) x11 x12 x13 x14 x15 x16 x17
                           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                        F (Z_to_bv 64 AST_DTOR) fc None m (seg_rom asegs) ->
    (forall msF' mo' s' LB' m' XS' (y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) (F' : bvmap 5 word) (fc' : bv 32),
       as_AKREL H s' (mkCfg msF' mo') -> as_MPRES H mo mo' -> as_AL H s' >= as_AL H s -> frm_zero fc' ->
       ww3 e ff fp XS' s' LB' m' ->
       as_VIS H s' msF' = MS (mkR (Z_to_bv 64 WO_DT3_RA) (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) y5 y6 y7
                                (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e)) y10 y11 y12 y13 y14 y15 y16 y17
                                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
                             F' (Z_to_bv 64 WO_DT3_RA) fc' None m' (seg_rom asegs) ->
       as_SR H Q (mkCfg msF' mo')) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros Q e ff fp XS s LB LBs m msF mo c x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 F fc
      HP W FZ KR AL0 VIS K.
    destruct W as (HI & WTC & RP & SP & PL & PB & BN & ADP).
    pose proof (wframe_bounds H e ff fp XS s LB m HP HI) as (F0 & F64 & FLO & FH & FL & FS1 & SH1 & SH2 & S1L & S1SP & SPH & LOS1).
    assert (AD : addressable m (ff + 3504) ST_SIZE).
    { replace (ff + 3504) with (ff + 3456 + 48) by lia. unfold ST_SIZE.
      apply (addressable_sub8 m (ff + 3456) 288 48 240 ADP); [reflexivity | reflexivity | reflexivity | lia | lia | lia]. }
    eapply (wdtP e ff fp XS s LB LBs c m msF mo Q WO_DT3_RA (ff + 3504) x5 x6 x7 x11 x12 x13 x14 x15 x16 x17
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 F fc HP HI ltac:(lia) ltac:(unfold ST_SIZE, WO_FLAGP in *; lia) AD VIS FZ
              ltac:(unfold WO_DT3_RA; lia) eq_refl ltac:(unfold PO_PF, WO_DT3_RA; cbn; tauto) KR AL0 RP SP PL PB BN).
    intros msF' mo' s' LB' m' XS' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc'
      VIS' FZ' KR' MP' HI' XP FS PERM WR' AL'.
    eapply (K msF' mo' s' LB' m' (XS ++ XS') t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc');
      [exact KR' | exact MP' | exact AL' | exact FZ' | | exact VIS'].
    split; [exact HI'|]. split; [|exact PERM].
    change ((ff + 3504, ff + 3504 + ST_SIZE) :: XS') with ([(ff + 3504, ff + 3504 + ST_SIZE)] ++ XS') in XP.
    eapply (wtc_xp e ff fp XS s LB (w_LB e) m m' [(ff + 3504, ff + 3504 + ST_SIZE)] XS' HP HI XP FS); [|exact WTC].
    apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. unfold ST_SIZE, WO_FLAGP in *. lia.
  Qed.

  Lemma wtd_xp : forall (e : went H) ff fp XS XS2 s s' LB LB' LBs m m' c o,
    wpre H e -> wtd e ff fp XS s LB LBs m c -> winv H e ff fp (XS ++ XS2) s' LB' m' ->
    xpres H LB (wS1 e) ([(o, o + ST_SIZE)] ++ XS2) m m' -> Forall (fs_scratch H ((6, ff, fp) :: w_LF e)) XS2 ->
    Permutation LB' LB -> ff + 8 <= o -> o + ST_SIZE <= ff + 3408 ->
    wtd e ff fp (XS ++ XS2) s' LB' LBs m' c.
  Proof.
    intros e ff fp XS XS2 s s' LB LB' LBs m m' c o HP W HI' XP FS PERM O1 O2.
    destruct W as (HI & WTC & RP & SP & PL & PB & BN & ADP).
    pose proof (wframe_bounds H e ff fp XS s LB m HP HI) as (F0 & F64 & FLO & FH & FL & FS1 & SH1 & SH2 & S1L & S1SP & SPH & LOS1).
    unfold ST_SIZE in *.
    assert (BL : forall p n, In (p, n) (state_blocks c) -> In (p, n) (lbl LB) /\ In (p, n) (lbl LB')).
    { intros p n Hin. assert (L : In (p, n) (lbl LBs)) by (eapply Permutation_in; [apply Permutation_sym; exact PB | exact Hin]).
      destruct (lbl_in_inv _ _ _ L) as (q & Hq).
      assert (I1 : In (q, p, n) LB) by (eapply Permutation_in; [apply Permutation_sym; exact PL | apply in_or_app; right; exact Hq]).
      split; apply (lbl_in _ q); [exact I1 | eapply Permutation_in; [apply Permutation_sym; exact PERM | exact I1]]. }
    destruct (wstate_xp H HHb e ff fp s LB LB' [(o, o + 240)] XS2 m m m' c (ff + 3504) HP (winv_rf H _ _ _ _ _ _ _ HI)
                (winv_ff H _ _ _ _ _ _ _ HI) (winv_rh H _ _ _ _ _ _ _ HI) XP FS ltac:(lia) ltac:(unfold ST_SIZE, WO_FLAGP; lia)
                ltac:(apply Forall_cons; [right; cbn [fst snd]; unfold ST_SIZE, WO_FLAGP; lia | apply Forall_nil]) BL RP SP)
      as [RP' SP'].
    split; [exact HI'|].
    split; [eapply (wtc_xp e ff fp XS s LB LB m m' [(o, o + 240)] XS2 HP HI XP FS); [|exact WTC];
            apply Forall_cons; [cbn [fst snd]; unfold WO_FLAGP; lia | apply Forall_nil]|].
    split; [exact RP'|]. split; [exact SP'|].
    split; [eapply Permutation_trans; [exact PERM | exact PL]|].
    split; [exact PB|]. split; [exact BN|].
    eapply (wsx_ad e ff fp XS s LB LB m m' ([(o, o + 240)] ++ XS2) (ff + 3456) 288 HP HI XP ADP ltac:(lia) ltac:(lia)).
    eapply (wtx_apart e ff fp XS s LB m [(o, o + 240)] XS2); [exact HP | exact HI | exact FS | |].
    - intros iv (_ & _ & _ & _ & A5 & _). lia.
    - apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. exact (wfw_sh e ff fp XS s LB m (o, o + 240) HP HI ltac:(cbn; lia) ltac:(cbn; lia)).
  Qed.

  Lemma wrv_outside : forall (W : list (Z * Z)) a, ~ rin_ivs W a -> outside W a.
  Proof.
    induction W as [|[lo hi] W IH]; intros a N; cbn in *; [exact I|].
    split; [intros Hin; apply N; left; exact Hin | apply IH; intros Hin; apply N; right; exact Hin].
  Qed.

  Lemma wxp_munch : forall LB SP W m m', munch W m m' -> wmono asegs m m' -> xpres H LB SP W m m'.
  Proof.
    intros LB SP W m m' MU WM a Ha (_ & NR). split.
    - apply MU. unfold wa. rewrite HLib.u64_of_Z by lia. exact (wrv_outside W a NR).
    - intros V. apply WM. exact V.
  Qed.

  Lemma wst_xsh : forall (e : went H) ff fp XSc sk LBk s LB m m' st c o k,
    wpre H e -> winv H e ff fp XSc sk LBk m -> as_RHEAP H s LB m ->
    munch [(sh ff + o, sh ff + o + k)] m m' -> wmono asegs m m' ->
    0 <= o -> 0 <= k -> o + k <= 476 -> ff <= st -> st + 240 <= ff + 4096 ->
    (forall p n, In (p, n) (state_blocks c) -> In (p, n) (lbl LB)) ->
    state_repA LB m st c -> state_sh m c -> state_repA LB m' st c /\ state_sh m' c.
  Proof.
    intros e ff fp XSc sk LBk s LB m m' st c o k HP HI RH MU WM O0 K0 OK S1 S2 BL R S.
    pose proof (wxp_munch LB (wS1 e) _ m m' MU WM) as XP.
    destruct (wrv_fsb H e ff fp XSc sk LBk m HP HI) as (F1 & F2 & F64 & FC & FAPP).
    pose proof aceil_facts as ACF.
    pose proof (wframe_bounds H e ff fp XSc sk LBk m HP HI) as (_ & _ & _ & _ & _ & _ & SH1 & _).
    assert (BA : forall p n, In (p, n) (state_blocks c) ->
                   Forall (fun iv : Z * Z => p + n <= fst iv \/ snd iv <= p) [(sh ff + o, sh ff + o + k)]
                   /\ Forall (fun iv : Z * Z => sh p + nsh n <= fst iv \/ snd iv <= sh p) [(sh ff + o, sh ff + o + k)]).
    { intros p n Hin. destruct (lbl_in_inv _ _ _ (BL p n Hin)) as (q & Hq).
      pose proof (ah_blocks H HB _ _ _ _ RH Hq) as (B0 & B16 & Bn & BI & BC & BF & BAPP). cbn in B0, B16, Bn, BI, BC, BF, BAPP.
      assert (DJ : p + n <= ff \/ ff + 4096 <= p).
      { destruct (wrv_blk_apart H HHb s LB m q p n e ff fp XSc sk LBk m [(ff, ff + 4096)] RH Hq HP HI
                    ltac:(apply Forall_cons; [cbn; lia | apply Forall_nil])) as (D1 & _).
        inversion D1 as [|? ? D1h _]. cbn in D1h. lia. }
      split; apply Forall_cons; try apply Forall_nil; cbn [fst snd].
      - clear - FAPP ACF BAPP B0 Bn F64 FC O0 K0 OK. unfold sh in *. rewrite ?ASHADOW_BASE_val in *.
        unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO, AIMG_TOP in BAPP.
        destruct FAPP as [[X Y]|[X Y]]; destruct BAPP as [[U V]|[U V]]; Z.div_mod_to_equations; lia.
      - clear - DJ B0 B16 Bn F64 O0 K0 OK. unfold sh, nsh in *. Z.div_mod_to_equations. lia. }
    split.
    - eapply (rep_keep H LB LB LB (wS1 e) _ m m' st c R XP).
      + apply (objx_intro H). { left. lia. }
        intros a Ha _. apply (wrv_noriv _ st 240); [| exact Ha]. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd].
        destruct SH1 as [X|X]; lia.
      + apply (blkx_intro H). intros p n Hin. split; [exact (BL p n Hin)|]. split; [exact (BL p n Hin)|].
        exact (wrv_noriv _ p n (proj1 (BA p n Hin))).
      + destruct FAPP as [[X1 Y]|[X1 Y]]; unfold AIMG_TOP; lia.
      + lia.
    - eapply (sh_keep H LB LB (wS1 e) _ m m' st c R S XP).
      apply (blksh_intro H). intros p n Hin. split; [exact (BL p n Hin)|].
      exact (wrv_noriv _ (sh p) (nsh n) (proj2 (BA p n Hin))).
  Qed.

  Lemma wtd_wd4 : forall (e : went H) ff fp XS s LB LBs m m' c,
    wpre H e -> wtd e ff fp XS s LB LBs m c -> munch [(sh ff + 382, sh ff + 412)] m m' -> wmono asegs m m' ->
    mem_inv asegs m' -> stk asegs m' (w_lo e) (wSP e) -> wtd e ff fp XS s LB LBs m' c.
  Proof.
    intros e ff fp XS s LB LBs m m' c HP W MU WM MI ST.
    destruct W as (HI & (C1 & C2 & C3 & C4 & WS) & RP & SP & PL & PB & BN & ADP).
    pose proof (wframe_bounds H e ff fp XS s LB m HP HI) as (F0 & F64 & FLO & FH & FL & FS1 & SH1 & SH2 & S1L & S1SP & SPH & LOS1).
    destruct (wrv_fsb H e ff fp XS s LB m HP HI) as (B1 & B2 & B64 & FC & FAPP).
    pose proof aceil_facts as ACF.
    unfold WO_FLAGP, AINTRIN_STACK in *.
    assert (BL : forall p n, In (p, n) (state_blocks c) -> In (p, n) (lbl LB)).
    { intros p n Hin. assert (L : In (p, n) (lbl LBs)) by (eapply Permutation_in; [apply Permutation_sym; exact PB | exact Hin]).
      destruct (lbl_in_inv _ _ _ L) as (q & Hq). apply (lbl_in _ q).
      eapply Permutation_in; [apply Permutation_sym; exact PL | apply in_or_app; right; exact Hq]. }
    replace (sh ff + 412) with (sh ff + 382 + 30) in MU by lia.
    destruct (wst_xsh e ff fp XS s LB s LB m m' (ff + 3504) c 382 30 HP HI (winv_rh H _ _ _ _ _ _ _ HI) MU WM
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) BL RP SP) as [RP' SP'].
    split.
    { eapply (winv_munch H HB); [exact HP | exact HI | exact MU | exact WM | exact MI | exact ST |].
      unfold wwin. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. right; right. lia. }
    split.
    { split; [eapply rw_cells_transport; [exact C1 | exact MU | exact WM | cbn; lia]|].
      split; [eapply rw_cells_transport; [exact C2 | exact MU | exact WM | cbn; lia]|].
      split; [eapply rw_cells_transport; [exact C3 | exact MU | exact WM | cbn; lia]|].
      split; [eapply rw_cells_transport; [exact C4 | exact MU | exact WM | cbn; destruct SH1 as [X|X]; lia]|].
      exact (wr_at_wmono m m' (sh ff) 476 WS WM). }
    split; [exact RP'|]. split; [exact SP'|]. split; [exact PL|]. split; [exact PB|]. split; [exact BN|].
    eapply addressable_transport; [exact ADP | exact MU | exact WM |].
    replace (sh (ff + 3456)) with (sh ff + 432) by (unfold sh; Z.div_mod_to_equations; lia).
    change (nsh 288) with 36. cbn [disjoint_from]. lia.
  Qed.

  Lemma seg_dt2 : forall (Q : config -> Prop) (e : went H) ff fp XS s LB LBs m msF mo c ct
      (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 s4 s5 s7 s8 s9 s10 s11 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32),
    wpre H e -> wtd e ff fp XS s LB LBs m c ->
    state_repA LB m (ff + 3056) ct -> state_sh m ct -> state_blocks ct = [] -> addressable m (ff + 3056) 240 ->
    frm_zero fc -> as_AKREL H s (mkCfg msF mo) -> 0 <= as_AL H s ->
    as_VIS H s msF = MS (mkR (Z_to_bv 64 WO_DT2_RA) (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) x5 x6 x7
                           (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e)) (Z_to_bv 64 (ff + 3056)) x11 x12 x13 x14 x15 x16 x17
                           (Z_to_bv 64 (ff + 3056)) (Z_to_bv 64 (sh ff)) s4 s5 (Z_to_bv 64 (ff + 3504)) s7 s8 s9 s10 s11
                           x28 x29 x30 x31)
                        F (Z_to_bv 64 AST_DTOR) fc None m (seg_rom asegs) ->
    (forall msF' mo' s' LB' m' XS' (y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) (F' : bvmap 5 word) (fc' : bv 32),
       as_AKREL H s' (mkCfg msF' mo') -> as_MPRES H mo mo' -> as_AL H s' >= as_AL H s -> frm_zero fc' ->
       wtd e ff fp XS' s' LB' LBs m' c ->
       as_VIS H s' msF' = MS (mkR (Z_to_bv 64 WO_DT3_RA) (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) y5 y6 y7
                                (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e)) (Z_to_bv 64 (ff + 3504)) y11 y12 y13 y14 y15 y16 y17
                                (Z_to_bv 64 (-8)) (Z_to_bv 64 (sh ff)) s4 s5 (Z_to_bv 64 (ff + 3504)) s7 s8 s9 s10 s11
                                y28 y29 y30 y31)
                             F' (Z_to_bv 64 AST_DTOR) fc' None m' (seg_rom asegs) ->
       as_SR H Q (mkCfg msF' mo')) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros Q e ff fp XS s LB LBs m msF mo c ct x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 s4 s5 s7 s8 s9 s10 s11 x28 x29 x30 x31 F fc
      HP W RT ST SB ADT FZ KR AL0 VIS K.
    pose proof W as (HI & WTC & RP & SP & PL & PB & BN & ADP).
    pose proof (wframe_bounds H e ff fp XS s LB m HP HI) as (F0 & F64 & FLO & FH & FL & FS1 & SH1 & SH2 & S1L & S1SP & SPH & LOS1).
    assert (INC : forall b, In b (w_LB e) -> In b LB)
      by (intros b Hb; eapply Permutation_in; [apply Permutation_sym; exact PL | apply in_or_app; left; exact Hb]).
    eapply (wdtT H HHb HOWN DTOR WTR e ff fp XS s LB ct m msF mo Q WO_DT2_RA (ff + 3056) x5 x6 x7 x11 x12 x13 x14 x15 x16 x17
              (Z_to_bv 64 (ff + 3056)) (Z_to_bv 64 (sh ff)) s4 s5 (Z_to_bv 64 (ff + 3504)) s7 s8 s9 s10 s11 x28 x29 x30 x31 F fc
              HP HI INC ltac:(lia) ltac:(unfold ST_SIZE, WO_FLAGP in *; lia) ADT VIS FZ
              ltac:(unfold WO_DT2_RA; lia) eq_refl ltac:(unfold PO_PF, WO_DT2_RA; cbn; tauto) KR AL0 RT ST SB).
    intros msF' mo' s' LB' m' XS2 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc'
      VIS' FZ' KR' MP' HI' XP FS PERM WR' AL'.
    change ((ff + 3056, ff + 3056 + ST_SIZE) :: XS2) with ([(ff + 3056, ff + 3056 + ST_SIZE)] ++ XS2) in XP.
    pose proof (wtd_xp e ff fp XS XS2 s s' LB LB' LBs m m' c (ff + 3056) HP W HI' XP FS PERM ltac:(lia)
                  ltac:(unfold ST_SIZE; lia)) as W'.
    pose proof W' as (HI2 & (C1 & C2 & C3 & C4 & WS) & _).
    pose proof (wrv_wr_sub m' (sh ff) 476 WS (sh ff + 382) 30 ltac:(lia) ltac:(lia)) as WRS.
    eapply (ahh_evt_then H HB (wd4_post (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
                               s4 s5 s7 s8 s9 s10 s11 F' fc' ff (w_lo e) (wSP e) m')
              Q s' msF' _ mo');
      [exact KR' | exact VIS' | exact (wd4 (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) t0' t1' t2' (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
                                          a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (ff + 3056)) s4 s5 s7 s8 s9 s10 s11 t3' t4' t5' t6'
                                          F' fc' m' ff (w_lo e) (wSP e) F0 ltac:(unfold WO_FLAGP in *; lia) WRS
                                          (winv_stk H _ _ _ _ _ _ _ HI2) (winv_mi H _ _ _ _ _ _ _ HI2)) |].
    intros msF2 mo2 KR2 MP2 (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m2 & EQ & MU & WM & MI & STK & _).
    eapply (K msF2 mo2 s' LB' m2 (XS ++ XS2) y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 F' fc');
      [exact KR2 | eapply (ah_mpres_trans H HB); [exact MP' | exact MP2] | exact AL' | exact FZ' | | exact EQ].
    exact (wtd_wd4 e ff fp (XS ++ XS2) s' LB' LBs m' m2 c HP W' MU WM MI STK).
  Qed.

  Lemma wperm_tail : forall (A B : list block) (x y z : block), Permutation (A ++ B ++ [x; y; z]) ([z; y; x] ++ (A ++ B)).
  Proof.
    intros A B x y z. rewrite app_assoc. eapply Permutation_trans; [apply Permutation_app_comm|].
    apply Permutation_app_tail. exact (Permutation_rev [x; y; z]).
  Qed.

  Lemma seg_mva2 : forall (Q : config -> Prop) (e : went H) ff fp XS s LB LBs m msF mo cP (p7 p8 p9 : bptr) b7 b8 b9
      (x5 x6 x7 x12 x13 x14 x15 x16 x17 s4 s5 s7 s8 s9 s10 s11 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32),
    wpre H e -> wtl H e ff fp XS s LB LBs [(p9, b9, 100); (p8, b8, 100); (p7, b7, 500)] m cP ->
    wtst0 ff m (vtrip b7 500) (vtrip b8 100) (vtrip b9 100) -> wblk m b7 500 -> wblk m b8 100 -> wblk m b9 100 ->
    frm_zero fc -> as_AKREL H s (mkCfg msF mo) -> 0 <= as_AL H s ->
    as_VIS H s msF = MS (mkR (Z_to_bv 64 WO_MVA2_RA) (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) x5 x6 x7
                           (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e)) (Z_to_bv 64 (ff + 3504)) (Z_to_bv 64 (ff + 3056))
                           x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (ff + 3056)) (Z_to_bv 64 (sh ff)) s4 s5 (Z_to_bv 64 (ff + 3504))
                           s7 s8 s9 s10 s11 x28 x29 x30 x31)
                        F (Z_to_bv 64 AST_MVA) fc None m (seg_rom asegs) ->
    (forall msF' mo' s' LB' m' XS' (y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) (F' : bvmap 5 word) (fc' : bv 32),
       as_AKREL H s' (mkCfg msF' mo') -> as_MPRES H mo mo' -> as_AL H s' >= as_AL H s -> frm_zero fc' ->
       wtd e ff fp XS' s' LB' [(p9, b9, 100); (p8, b8, 100); (p7, b7, 500)] m' (mkfreshA 0 0 b7 b8 b9) ->
       state_repA LB' m' (ff + 3056) (state_emptied (mkfreshA 0 0 b7 b8 b9)) -> addressable m' (ff + 3056) 240 ->
       as_VIS H s' msF' = MS (mkR (Z_to_bv 64 WO_DT2_RA) (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) y5 y6 y7
                                (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e)) (Z_to_bv 64 (ff + 3056)) y11 y12 y13 y14 y15 y16 y17
                                (Z_to_bv 64 (ff + 3056)) (Z_to_bv 64 (sh ff)) s4 s5 (Z_to_bv 64 (ff + 3504)) s7 s8 s9 s10 s11
                                y28 y29 y30 y31)
                             F' (Z_to_bv 64 AST_DTOR) fc' None m' (seg_rom asegs) ->
       as_SR H Q (mkCfg msF' mo')) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros Q e ff fp XS s LB LBs m msF mo cP p7 p8 p9 b7 b8 b9 x5 x6 x7 x12 x13 x14 x15 x16 x17 s4 s5 s7 s8 s9 s10 s11
      x28 x29 x30 x31 F fc HP W TS B7 B8 B9 FZ KR AL0 VIS K.
    destruct (wtl_incl H e ff fp XS s LB LBs _ m cP W) as (OINC & INC & BLP).
    destruct W as (HI & WTC & RP & SP & PB & BN & PL & OWN & ND & ADT & ADP).
    pose proof (wframe_bounds H e ff fp XS s LB m HP HI) as (F0 & F64 & FLO & FH & FL & FS1 & SH1 & SH2 & S1L & S1SP & SPH & LOS1).
    assert (IN7 : In (p7, b7, 500) LB) by (apply OINC; cbn; tauto).
    assert (IN8 : In (p8, b8, 100) LB) by (apply OINC; cbn; tauto).
    assert (IN9 : In (p9, b9, 100) LB) by (apply OINC; cbn; tauto).
    destruct (wst_T0_rep H HB e ff fp XS s LB m p7 p8 p9 b7 b8 b9 (w_LB e ++ LBs) HP HI TS B7 B8 B9 IN7 IN8 IN9
                (Permutation_trans PL (wperm_tail _ _ _ _ _))) as (RT & STs & G7 & G8 & G9).
    assert (PBt : Permutation (lbl [(p9, b9, 100); (p8, b8, 100); (p7, b7, 500)]) (state_blocks (mkfreshA 0 0 b7 b8 b9))).
    { rewrite mkfreshA_blocks by lia. cbn. exact (Permutation_rev [(b9, 100); (b8, 100); (b7, 500)]). }
    assert (BNt : forall p n, In (p, n) (state_blocks (mkfreshA 0 0 b7 b8 b9)) -> n <= 2 ^ 40).
    { rewrite mkfreshA_blocks by lia. intros p n Hin. cbn in Hin. destruct Hin as [E|[E|[E|[]]]]; inversion E; lia. }
    assert (ADd : addressable m (ff + 3504) ST_SIZE).
    { replace (ff + 3504) with (ff + 3456 + 48) by lia. unfold ST_SIZE.
      apply (addressable_sub8 m (ff + 3456) 288 48 240 ADP); [reflexivity | reflexivity | reflexivity | lia | lia | lia]. }
    eapply (wmva H HHb HOWN MVA WTR e ff fp XS s LB LBs _ cP (mkfreshA 0 0 b7 b8 b9) m msF mo Q (ff + 3504) (ff + 3056)
              (Z_to_bv 64 WO_MVA2_RA) x5 x6 x7 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (ff + 3056)) (Z_to_bv 64 (sh ff)) s4 s5
              (Z_to_bv 64 (ff + 3504)) s7 s8 s9 s10 s11 x28 x29 x30 x31 F fc HP HI ltac:(lia) ltac:(unfold ST_SIZE, WO_FLAGP in *; lia)
              ltac:(lia) ltac:(unfold ST_SIZE, WO_FLAGP in *; lia) ltac:(unfold ST_SIZE; lia) ADd ADT VIS FZ
              ltac:(rewrite HLib.u64_of_Z by (unfold WO_MVA2_RA; lia); unfold WO_MVA2_RA; reflexivity) KR AL0 RP SP RT STs PL PB PBt BN).
    intros msF' mo' s' LB' m' XS' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc'
      VIS' FZ' KR' MP' HI' XP FS PERM' RP' SP' RT' AL'.
    rewrite (ret_pc_even WO_MVA2_RA ltac:(unfold WO_MVA2_RA; lia) eq_refl) in VIS'.
    rewrite state_moved_mkfreshA in RP', SP'.
    change ((ff + 3504, ff + 3504 + ST_SIZE) :: (ff + 3056, ff + 3056 + ST_SIZE) :: XS')
      with ([(ff + 3504, ff + 3504 + ST_SIZE); (ff + 3056, ff + 3056 + ST_SIZE)] ++ XS') in XP.
    assert (FO : Forall (fun iv : Z * Z => sh ff + 476 <= fst iv \/ snd iv <= sh ff)
                   ([(ff + 3504, ff + 3504 + ST_SIZE); (ff + 3056, ff + 3056 + ST_SIZE)] ++ XS')).
    { eapply (wtx_apart e ff fp XS s LB m _ XS'); [exact HP | exact HI | exact FS | |].
      - intros iv (_ & _ & _ & _ & A5 & _). lia.
      - unfold ST_SIZE. repeat apply Forall_cons; try apply Forall_nil;
          apply (wfw_sh e ff fp XS s LB m _ HP HI); cbn; lia. }
    assert (WTC' : wtc H e ff m').
    { eapply (wtc_xp e ff fp XS s LB (w_LB e) m m' _ XS' HP HI XP FS); [|exact WTC].
      unfold ST_SIZE, WO_FLAGP. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia. }
    pose proof (wsx_ad e ff fp XS s LB (w_LB e) m m' _ (ff + 3456) 288 HP HI XP ADP ltac:(lia) ltac:(lia) FO) as ADP'.
    pose proof (wsx_ad e ff fp XS s LB (w_LB e) m m' _ (ff + 3056) 240 HP HI XP ADT ltac:(lia) ltac:(lia) FO) as ADT'.
    eapply (ahh_evt_then H HB (wd3_post (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
                               (Z_to_bv 64 (sh ff)) s4 s5 (Z_to_bv 64 (ff + 3504)) s7 s8 s9 s10 s11 F' fc' ff (w_lo e) (wSP e) m')
              Q s' msF' _ mo');
      [exact KR' | exact VIS' | exact (wd3 (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) t0' t1' t2' (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
                                          (Z_to_bv 64 (ff + 3504)) a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (sh ff)) s4 s5
                                          (Z_to_bv 64 (ff + 3504)) s7 s8 s9 s10 s11 t3' t4' t5' t6'
                                          F' fc' m' ff (w_lo e) (wSP e) F0 ltac:(unfold WO_FLAGP in *; lia)
                                          (winv_stk H _ _ _ _ _ _ _ HI') (winv_mi H _ _ _ _ _ _ _ HI')) |].
    intros msF2 mo2 KR2 MP2 (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m2 & EQ & MU & _ & _ & _).
    pose proof (munch_nil_eq5 m' m2 MU) as E2. subst m2.
    eapply (K msF2 mo2 s' LB' m' (XS ++ XS') y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 F' fc');
      [exact KR2 | eapply (ah_mpres_trans H HB); [exact MP' | exact MP2] | exact AL' | exact FZ' | | exact RT' | exact ADT' | exact EQ].
    split; [exact HI'|]. split; [exact WTC'|]. split; [exact RP'|]. split; [exact SP'|].
    split; [exact PERM'|]. split; [exact PBt|]. split; [exact BNt|]. exact ADP'.
  Qed.

End WoS5.
