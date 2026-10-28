(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface FPSteps SymExec3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BecLazy.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib HRep HRepFacts HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_MILB LbB_PrsStmt LbB_FKit LbB_Own LbB_PmBase LbB_PmOwn LbB_PmExit.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Lemma stk_wmono_fin : forall m m' lo hi, stk asegs m lo hi -> wmono asegs m m' -> 0x6e8000 <= lo -> stk asegs m' lo hi.
Proof.
  intros m m' lo hi (S0 & S1 & S) WM Hlo. split; [lia|]. split; [lia|]. intros a Ha.
  destruct (S a Ha) as [W _]. pose proof (WM _ W) as W'. split; [exact W'|].
  unfold wview in W'. unfold wa in W' |- *. rewrite HLib.u64_of_Z in W' by lia.
  destruct (m' (Z_to_bv 64 a)) as [b|] eqn:E.
  - exists b. unfold mrd. rewrite E. reflexivity.
  - rewrite BecLazy.asegs_find_segment_none_high in W' by lia. congruence.
Qed.

Section Fin.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.

  Lemma HHf : asan_rt_hyps H. Proof. exact (proj1 HHbp). Qed.

  Definition fin_ivl (w : pmwA H) (iv : Z * Z) : Prop :=
    (wa_lo w <= fst iv /\ snd iv <= wa_sp0 w - 104)
    \/ (wa_ff w <= fst iv /\ snd iv <= wa_ff w + fsz PM_FCLASS)
    \/ (sh (wa_ff w) <= fst iv /\ snd iv <= sh (wa_ff w) + PM_NSH)
    \/ (wa_fp w <= fst iv /\ snd iv <= wa_fp w + 1).

  Definition fin_apart (w : pmwA H) (a n : Z) : Prop :=
    forall iv, fin_ivl w iv -> a + n <= fst iv \/ snd iv <= a.

  Lemma disjoint_of_fin : forall w W a n, Forall (fin_ivl w) W -> fin_apart w a n -> disjoint_from W a n.
  Proof.
    intros w W a n FW AP. induction W as [|[lo hi] W IH]; cbn; [exact I|].
    split; [exact (AP (lo, hi) (Forall_inv FW)) | exact (IH (Forall_inv_tail FW))].
  Qed.

  Lemma fin_apart_sub : forall w a n a' n', fin_apart w a n -> a <= a' -> a' + n' <= a + n -> 0 <= n' -> fin_apart w a' n'.
  Proof. intros w a n a' n' AP H1 H2 H3 iv Hiv. destruct (AP iv Hiv); lia. Qed.

  Lemma Forall_fin_map : forall w (P : Z * Z -> Prop) W, Forall (fin_ivl w) W -> (forall iv, fin_ivl w iv -> P iv) -> Forall P W.
  Proof. intros w P W F HP. induction F; constructor; [apply HP; assumption | assumption]. Qed.

  Lemma fin_munch_eq : forall w W m m' a, munch W m m' -> Forall (fin_ivl w) W -> 0 <= a < 2 ^ 64 -> fin_apart w a 1 ->
    m' (Z_to_bv 64 a) = m (Z_to_bv 64 a).
  Proof.
    intros w W m m' a MU FW Ha AP. apply MU. rewrite HLib.u64_of_Z by lia.
    eapply disjoint_outside; [exact (disjoint_of_fin w W _ 1 FW AP) | lia].
  Qed.

  Lemma fin_apart_obj : forall w O n,
    pmw_okA H w -> fsobj H (wa_LF0 w) O n -> aapp O n -> 0 <= O -> 0 <= n -> O + n <= aceil ->
    fin_apart w O n /\ fin_apart w (sh O) (nsh n).
  Proof.
    intros w O n OK FO AP HO Hn Hc.
    pose proof (own_apart_obj3 H HHf w O n OK FO AP HO Hn Hc) as [A1 A2].
    pose proof (wk_rfs0 H w OK) as RF.
    pose proof (pmw_frame_facts H w OK) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    assert (Htop : O + n <= AAPP_HI) by (unfold AAPP_HI; lia).
    pose proof (fsobj_windows H HHf _ _ _ _ _ _ _ RF FO (wk_fresh H w OK) HO Hn Htop) as (D1 & D2 & D3 & D4).
    pose proof (aapp_disjoint_sh (as_FSB H) AFS_SIZE O n F8 HO Htop Hn) as SH.
    change (fsz PM_FCLASS) with 16384 in *.
    split.
    - intros iv [Hiv|[Hiv|[Hiv|Hiv]]].
      + apply A1. left. exact Hiv.
      + destruct Hiv as (I1 & I2). change (fsz PM_FCLASS) with 16384 in I2. destruct D1 as [D1|D1]; [left | right]; lia.
      + apply A1. right; right. exact Hiv.
      + destruct Hiv as (I1 & I2). destruct D3 as [D3|D3]; [left | right]; lia.
    - intros iv [Hiv|[Hiv|[Hiv|Hiv]]].
      + apply A2. left. exact Hiv.
      + destruct Hiv as (I1 & I2). change (fsz PM_FCLASS) with 16384 in I2. unfold AFS_HDR, AFS_SIZE in *.
        destruct SH as [SH|SH]; [left | right]; lia.
      + apply A2. right; right. exact Hiv.
      + destruct Hiv as (I1 & I2). unfold AFS_HDR, AFS_SIZE, AFS_FLAGS in *. destruct SH as [SH|SH]; [left | right]; lia.
  Qed.

  Lemma fin_apart_lbl : forall w s LB m A n,
    pmw_okA H w -> as_RHEAP H s LB m -> In (A, n) (lbl LB) -> fin_apart w A n /\ fin_apart w (sh A) (nsh n).
  Proof.
    intros w s LB m A n OK RH Hin. apply lbl_in_inv in Hin. destruct Hin as [pid Hin].
    pose proof (ah_blocks H HHf _ _ _ _ RH Hin) as (R0 & R16 & Rn & RI & RC & RF & RAPP). cbn in R0, R16, Rn, RI, RC, RF, RAPP.
    apply fin_apart_obj; [exact OK | eapply fsobj_block; [exact HHf | exact RH | exact Hin] | exact RAPP | lia | lia | lia].
  Qed.

  Lemma fin_apart_img : forall w a n, pmw_okA H w -> 0 <= n -> a + n <= AIMG_TOP -> fin_apart w a n.
  Proof.
    intros w a n OK Hn Ha iv Hiv. left.
    pose proof (pmw_frame_facts H w OK) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10).
    pose proof (wk_stack H w OK) as (S1 & S2 & S3 & S4 & S5 & S6).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    change (fsz PM_FCLASS) with 16384 in *.
    destruct Hiv as [(I1 & I2)|[(I1 & I2)|[(I1 & I2)|(I1 & I2)]]]; unfold AFS_HDR, AFS_FLAGS in *; try (unfold AIMG_TOP in *; lia).
    assert (sh AIMG_TOP <= sh (wa_ff w)) by (apply sh_mono; lia).
    replace (sh AIMG_TOP) with 0x800d5000 in * by reflexivity. unfold AIMG_TOP in *. lia.
  Qed.

  Lemma fin_aclient : forall w LB iv, pmw_okA H w -> fin_ivl w iv -> aclient_write_ok H LB iv.
  Proof.
    intros w LB iv OK Hiv.
    pose proof (pmw_frame_facts H w OK) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10).
    pose proof (wk_stack H w OK) as (S1 & S2 & S3 & S4 & S5 & S6).
    destruct Hiv as [(I1 & I2)|[(I1 & I2)|[(I1 & I2)|(I1 & I2)]]]; change (fsz PM_FCLASS) with 16384 in *.
    - left. lia.
    - right; right; right; right; left. unfold AFS_HDR in *. lia.
    - right; right; right; right; right; left. split.
      + eapply Z.le_trans; [| exact I1]. apply sh_mono; unfold AFS_HDR in *; lia.
      + eapply Z.le_trans; [exact I2|]. unfold PM_NSH.
        assert (sh (wa_ff w + 11584) <= sh (as_FSB H + AFS_SIZE)) by (apply sh_mono; lia).
        assert (sh (wa_ff w) + 1448 = sh (wa_ff w + 11584)) by (unfold sh; Z.div_mod_to_equations; lia). lia.
    - right; right; right; right; left. unfold AFS_HDR, AFS_SIZE, AFS_FLAGS in *. lia.
  Qed.

  Lemma fin_stack0_ok : forall w iv, pmw_okA H w -> fin_ivl w iv -> stack0_ok iv.
  Proof.
    intros w iv OK Hiv.
    pose proof (pmw_frame_facts H w OK) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10).
    pose proof (wk_stack H w OK) as (S1 & S2 & S3 & S4 & S5 & S6).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    unfold stack0_ok.
    assert (LS : ALOWSH_LO <= sh aceil) by (unfold sh, ALOWSH_LO, ASHADOW_BASE; Z.div_mod_to_equations; lia).
    destruct Hiv as [(I1 & I2)|[(I1 & I2)|[(I1 & I2)|(I1 & I2)]]]; change (fsz PM_FCLASS) with 16384 in *.
    - left. unfold AHI_LO. lia.
    - destruct F8 as [(L1 & L2)|(L1 & L2)].
      + right. unfold ALOWSH_LO, AFS_HDR, AFS_SIZE in *. lia.
      + left. unfold AFS_HDR in *. lia.
    - right. unfold PM_NSH in I2.
      assert (sh (wa_ff w + 11584) <= sh aceil) by (apply sh_mono; lia).
      assert (sh (wa_ff w) + 1448 = sh (wa_ff w + 11584)) by (unfold sh; Z.div_mod_to_equations; lia). lia.
    - destruct F8 as [(L1 & L2)|(L1 & L2)].
      + right. unfold ALOWSH_LO, AFS_HDR, AFS_SIZE, AFS_FLAGS in *. lia.
      + left. unfold AFS_HDR, AFS_FLAGS in *. lia.
  Qed.

  Lemma fin_above_img : forall w iv, pmw_okA H w -> fin_ivl w iv -> AIMG_TOP <= fst iv.
  Proof.
    intros w [lo hi] OK Hiv. cbn [fst]. unfold fin_ivl in Hiv. cbn [fst snd] in Hiv.
    pose proof (pmw_frame_facts H w OK) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10).
    pose proof (wk_stack H w OK) as (S1 & S2 & S3 & S4 & S5 & S6).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    change (fsz PM_FCLASS) with 16384 in *.
    destruct Hiv as [(I1 & I2)|[(I1 & I2)|[(I1 & I2)|(I1 & I2)]]]; unfold AFS_HDR, AFS_FLAGS in *; try (unfold AIMG_TOP in *; lia).
    assert (sh AIMG_TOP <= sh (wa_ff w)) by (apply sh_mono; lia).
    replace (sh AIMG_TOP) with 0x800d5000 in * by reflexivity. unfold AIMG_TOP in *. lia.
  Qed.

  Lemma fin_addr_lbl : forall w s LB m m' W A n, pmw_okA H w -> as_RHEAP H s LB m -> munch W m m' -> wmono asegs m m' ->
    Forall (fin_ivl w) W -> In (A, n) (lbl LB) -> addressable m A n -> addressable m' A n.
  Proof.
    intros w s LB m m' W A n OK RH MU WM FW Hin AD.
    pose proof (fin_apart_lbl w s LB m A n OK RH Hin) as [_ APs].
    eapply addressable_transport; [exact AD | exact MU | exact WM | exact (disjoint_of_fin w W _ _ FW APs)].
  Qed.

  Lemma fin_SHAD_lbl : forall w s LB m m' W A n sbs, pmw_okA H w -> as_RHEAP H s LB m -> munch W m m' -> wmono asegs m m' ->
    Forall (fin_ivl w) W -> In (A, n) (lbl LB) -> Z.of_nat (length sbs) <= nsh n -> SHAD m A sbs -> SHAD m' A sbs.
  Proof.
    intros w s LB m m' W A n sbs OK RH MU WM FW Hin Hl SH.
    pose proof (fin_apart_lbl w s LB m A n OK RH Hin) as [_ APs].
    eapply SHAD_transport; [exact SH | exact MU | exact WM |].
    apply (disjoint_of_fin w W); [exact FW|]. eapply fin_apart_sub; [exact APs | lia | lia | lia].
  Qed.

  Lemma fin_umap_sh : forall w s LB m m' W NS (V : Type) (nval : mem -> Z -> V -> Prop) obj bl bc ents,
    pmw_okA H w -> as_RHEAP H s LB m -> munch W m m' -> wmono asegs m m' -> Forall (fin_ivl w) W ->
    @umapx AC_A ASEGS LY_A MI_A NS V nval (lbl LB) m obj bl bc ents ->
    umap_sh m NS (bl, bc, ents) -> umap_sh m' NS (bl, bc, ents).
  Proof.
    intros w s LB m m' W NS V nval obj bl bc ents OK RH MU WM FW U [SB SN].
    destruct U as [_ _ _ _ _ _ Ublive _ _ _ _ _ _ _ Unode _]. cbn [t3a t3b t3c fst snd] in *. split.
    - intros Hbc. destruct Ublive as [[E _]|[_ Hl]]; [contradiction|].
      exact (fin_addr_lbl w s LB m m' W bl (8 * bc) OK RH MU WM FW Hl (SB Hbc)).
    - intros q k v Hin. destruct (Unode q k v Hin) as (Hl & _).
      exact (fin_addr_lbl w s LB m m' W q NS OK RH MU WM FW Hl (SN q k v Hin)).
  Qed.

  Lemma fin_pmc_sh : forall w s LB m m' W c, pmw_okA H w -> as_RHEAP H s LB m -> munch W m m' -> wmono asegs m m' ->
    Forall (fin_ivl w) W ->
    @umapx AC_A ASEGS LY_A MI_A 24 Z (nval24 ASEGS) (lbl LB) m (wa_p w + O_M1) (t3a (c_m1 c)) (t3b (c_m1 c)) (t3c (c_m1 c)) ->
    @umapx AC_A ASEGS LY_A MI_A 32 (Z * Z * Z) (nval32 ASEGS) (lbl LB) m (wa_p w + O_M2) (t3a (c_m2 c)) (t3b (c_m2 c)) (t3c (c_m2 c)) ->
    @umapx AC_A ASEGS LY_A MI_A 24 Z (nval24 ASEGS) (lbl LB) m (wa_p w + O_M3) (t3a (c_m3 c)) (t3b (c_m3 c)) (t3c (c_m3 c)) ->
    @vec_opnd AC_A ASEGS LY_A MI_A (lbl LB) m (wa_p w + O_V1) (t3a (c_v1 c)) (t3b (c_v1 c)) (t3c (c_v1 c)) ->
    @vec32 AC_A ASEGS LY_A MI_A (lbl LB) m (wa_p w + O_V2) (t3a (c_v2 c)) (t3b (c_v2 c)) (t3c (c_v2 c)) ->
    @vec32 AC_A ASEGS LY_A MI_A (lbl LB) m (wa_p w + O_V3) (t3a (c_v3 c)) (t3b (c_v3 c)) (t3c (c_v3 c)) ->
    pmc_sh m c -> pmc_sh m' c.
  Proof.
    intros w s LB m m' W c OK RH MU WM FW U1 U2 U3 V1 V2 V3 (S1 & S2 & S3 & S4 & S5 & S6).
    destruct (c_m1 c) as [[bl1 bc1] e1] eqn:E1. destruct (c_m2 c) as [[bl2 bc2] e2] eqn:E2. destruct (c_m3 c) as [[bl3 bc3] e3] eqn:E3.
    unfold pmc_sh. rewrite E1, E2, E3 in *. cbn [t3a t3b t3c fst snd] in *.
    split; [exact (fin_umap_sh w s LB m m' W 24 Z (nval24 ASEGS) _ bl1 bc1 e1 OK RH MU WM FW U1 S1)|].
    split; [exact (fin_umap_sh w s LB m m' W 32 (Z * Z * Z) (nval32 ASEGS) _ bl2 bc2 e2 OK RH MU WM FW U2 S2)|].
    split; [exact (fin_umap_sh w s LB m m' W 24 Z (nval24 ASEGS) _ bl3 bc3 e3 OK RH MU WM FW U3 S3)|].
    split; [| split].
    - intros Hb. pose proof V1 as (_ & _ & _ & Hlen & Hbb & _). destruct Hbb as [[E _]|(_ & _ & _ & _ & Hl & _)]; [contradiction|].
      eapply (fin_SHAD_lbl w s LB m m' W _ _ _ OK RH MU WM FW Hl); [| exact (S4 Hb)].
      rewrite cc_gen_length by (unfold OPND_SZ; lia). lia.
    - intros Hb. pose proof V2 as (_ & _ & _ & Hlen & Hbb & _). destruct Hbb as [[E _]|(_ & _ & _ & _ & Hl & _)]; [contradiction|].
      eapply (fin_SHAD_lbl w s LB m m' W _ _ _ OK RH MU WM FW Hl); [| exact (S5 Hb)].
      rewrite cc_gen_length by (unfold Zlen in *; lia). lia.
    - intros Hb. pose proof V3 as (_ & _ & _ & Hlen & Hbb & _). destruct Hbb as [[E _]|(_ & _ & _ & _ & Hl & _)]; [contradiction|].
      eapply (fin_SHAD_lbl w s LB m m' W _ _ _ OK RH MU WM FW Hl); [| exact (S6 Hb)].
      rewrite cc_gen_length by (unfold Zlen in *; lia). lia.
  Qed.

  Variable LINV : mem -> Prop.
  Hypothesis LINV_frame : forall m m' W, LINV m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) W -> LINV m'.

  Definition fin_XS (w : pmwA H) (XS : list (Z * Z)) : list (Z * Z) :=
    (wa_fp w, wa_fp w + 1) :: (wa_ff w, wa_ff w + fsz PM_FCLASS) :: (sh (wa_ff w), sh (wa_ff w) + fshn PM_FCLASS) :: XS.

  Lemma pm_fin : forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl spal m' W,
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl [] spal -> c_tr c = [] ->
    munch W m m' -> wmono asegs m m' -> Forall (fin_ivl w) W ->
    exists (errv' : word) (XS : list (Z * Z)),
      rw_cells asegs m' (errno_addr (wa_tp w)) [C4 errv'] /\ as_rauxv_ok H m' (wa_B w)
      /\ as_RHEAP H s LB m' /\ state_own LB (wa_LB0 w) LBs (pc_state (prc_ofA w c)) /\ lb_own LBs m'
      /\ parser_repA LB m' (wa_p w) (prc_ofA w c) /\ parser_sh m' (wa_p w) (prc_ofA w c)
      /\ lb_small LBs + 2 ^ 12 <= po_small (wa_n w) /\ Z.of_nat (length LBs) + 8 <= po_cnt (wa_n w)
      /\ nlarge LBs + 3 <= po_large (wa_n w)
      /\ st_vsteps (pc_state (prc_ofA w c))
      /\ Forall (fs_scratch H (wa_LF0 w)) XS
      /\ xpres H (wa_LB0 w) (wa_sp0 w) ((RtB_Td.ATDLOC, RtB_Td.ATDLOC + 8) :: (wa_p w, wa_p w + PARSER_SIZE) :: XS) (wa_m0 w) m'
      /\ stack0 m' (wa_lo w) (wa_shi w) /\ LINV m'
      /\ as_AL H s >= as_AL H (wa_s0 w) - po_cost (wa_n w).
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl spal m' W OK X Htr MU WM FW.
    pose proof (pmxa_bundle H HHbp LINV w s LB LBs m mo c ins tbl ftbl spal OK X Htr) as (PRb & PSb & SOb & LOb & VSb).
    pose proof (pmw_frame_facts H w OK) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10).
    pose proof (wk_stack H w OK) as (S1 & S2 & S3 & S4 & S5 & S6).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_papp H w OK) as (PA & P0 & P16).
    pose proof (wk_capp H w OK) as (CA & C0 & C16).
    pose proof (p_range H w OK) as (PR1 & PR2).
    pose proof (aapp_below_aceil _ _ CA) as C4.
    destruct (fin_apart_obj w (wa_p w) PARSER_SIZE OK (wk_pobj H w OK) PA ltac:(lia) ltac:(unfold PARSER_SIZE; lia) PR2) as [FP FPs].
    destruct (fin_apart_obj w (wa_cons w) 48 OK (wk_cobj H w OK) CA ltac:(lia) ltac:(lia) C4) as [FC FCs].
    pose proof (xa_rheap _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as RH.
    pose proof (xa_own _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as [OWN1 OWN2]. rewrite app_nil_r in OWN1.
    assert (FWa : Forall (aclient_write_ok H LB) W).
    { apply (Forall_fin_map w); [exact FW|]. intros iv Hiv. exact (fin_aclient w LB iv OK Hiv). }
    assert (SBL : forall A n, In (A, n) (state_blocks (pc_state (prc_ofA w c))) -> In (A, n) (lbl LB)).
    { intros A n Hb. destruct SOb as [_ SO2]. apply (Permutation_in _ (Permutation_sym SO2)) in Hb.
      apply lbl_in_inv in Hb as [pid Hb]. apply (lbl_in LB pid).
      apply (Permutation_in _ (Permutation_sym OWN1)). apply in_app_iff. right. exact Hb. }
    destruct (xa_errno _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as [errv Herr].
    destruct (xa_xpres _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as (XS & FXS & XP).
    exists errv, (fin_XS w XS).
    split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split;
      [| split; [| split; [| split; [| split]]]]]]]]]]]]]].
    -
      eapply rw_cells_transport; [exact Herr | exact MU | exact WM |].
      apply (disjoint_of_fin w W); [exact FW|]. rewrite (wk_tp H w OK). rewrite unsigned_lit by (unfold ATP; lia).
      apply fin_apart_img; [exact OK | cbn; lia | unfold ATP, AIMG_TOP; cbn; lia].
    -
      eapply (ah_rauxv_frame H HHf); [exact (xa_rauxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) | exact MU | exact WM | exact FWa].
    -
      eapply (ah_RHEAP_frame H HHf); [exact RH | exact MU | exact WM | exact FWa].
    - exact SOb.
    - exact (lb_own_wmono _ _ _ LOb WM).
    -
      eapply parser_repA_keep; [exact PRb | cbn [prc_ofA pc_cons]; lia | cbn [prc_ofA pc_cons]; lia | |].
      + intros a Ha. destruct Ha as [Ha|Ha].
        * apply (fin_munch_eq w W m m' a MU FW); [unfold PARSER_SIZE in *; lia|].
          eapply fin_apart_sub; [exact FP | lia | lia | lia].
        * destruct Ha as [Ha|((A & n) & Hb & Ha)].
          -- apply (fin_munch_eq w W m m' a MU FW); [unfold ST_OFF, PARSER_SIZE in *; lia|].
             eapply fin_apart_sub; [exact FP | unfold ST_OFF in *; lia | unfold ST_OFF, PARSER_SIZE in *; lia | lia].
          -- cbn [fst snd] in Ha. pose proof (SBL A n Hb) as HL.
             destruct (fin_apart_lbl w s LB m A n OK RH HL) as [FA _].
             destruct (lbl_in_inv LB A n HL) as [pid Hpb].
             pose proof (ah_blocks H HHf _ _ _ _ RH Hpb) as (R0 & R16 & Rn & RI & RC & RF & RAPP). cbn in R0, Rn, RC.
             apply (fin_munch_eq w W m m' a MU FW); [lia|]. eapply fin_apart_sub; [exact FA | lia | lia | lia].
      + intros a Ha. cbn [prc_ofA pc_cons] in Ha. apply (fin_munch_eq w W m m' a MU FW); [lia|].
        eapply fin_apart_sub; [exact FC | lia | lia | lia].
    -
      pose proof (xa_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as (SHc & SHp & SHk).
      pose proof (fin_pmc_sh w s LB m m' W c OK RH MU WM FW (xa_m1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) (xa_m2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)
                    (xa_m3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) (xa_v1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) (xa_v2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X)
                    (xa_v3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) SHc) as (U1 & U2 & U3 & V1 & V2 & V3).
      split; [eapply addressable_transport; [exact SHp | exact MU | exact WM | exact (disjoint_of_fin w W _ _ FW FPs)]|].
      split; [eapply addressable_transport; [exact SHk | exact MU | exact WM | exact (disjoint_of_fin w W _ _ FW FCs)]|].
      unfold state_sh. cbn [prc_ofA pc_state stc_ofA st_m1 st_m2 st_m3 st_v1 st_v2 st_v3].
      split; [exact U1|]. split; [exact U2|]. split; [exact U3|].
      split; [exact (vec_sh_of_opnd m' _ _ _ V1) |]. split; [exact (vec_sh_of_32 m' _ _ _ V2) | exact (vec_sh_of_32 m' _ _ _ V3)].
    - pose proof (xa_meas _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as (M1 & M2 & M3). lia.
    - pose proof (xa_meas _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as (M1 & M2 & M3). lia.
    - pose proof (xa_meas _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as (M1 & M2 & M3). lia.
    - exact VSb.
    -
      pose proof (fs_scratch_of_fresh H _ _ _ _ (wk_fresh H w OK)) as FS. apply Forall_inv_tail in FS.
      unfold fin_XS. constructor; [exact (Forall_inv FS)|]. constructor; [exact (Forall_inv (Forall_inv_tail FS))|].
      constructor; [exact (Forall_inv (Forall_inv_tail (Forall_inv_tail FS)))|]. exact FXS.
    -
      eapply xpres_trans.
      + eapply (xpres_weaken H (wa_LB0 w) (wa_LB0 w) (wa_sp0 w) (wa_sp0 w)); [exact XP | lia | intros b Hb; exact Hb |].
        intros a Ha. unfold fin_XS. cbn [rin_ivs fst snd] in Ha |- *. tauto.
      + eapply xpres_weaken; [| apply Z.le_refl | |].
        * eapply (xpres_of_munch H s LB (wa_sp0 w) ((RtB_Td.ATDLOC, RtB_Td.ATDLOC + 8) :: (wa_p w, wa_p w + PARSER_SIZE) :: fin_XS w XS) W m m m'); [exact HHf | exact RH | exact MU | exact WM |].
          apply (Forall_fin_map w); [exact FW|]. intros [lo hi] Hiv. unfold fin_ivl in Hiv. cbn [fst snd] in *.
          change (fsz PM_FCLASS) with 16384 in *.
          destruct Hiv as [(I1 & I2)|[(I1 & I2)|[(I1 & I2)|(I1 & I2)]]].
          -- left. split; lia.
          -- right. intros a Ha. unfold fin_XS. cbn [rin_ivs fst snd]. right; right; right; left. change (fsz PM_FCLASS) with 16384. lia.
          -- right. intros a Ha. unfold fin_XS. cbn [rin_ivs fst snd]. right; right; right; right; left. change (fshn PM_FCLASS) with 2048.
             unfold PM_NSH in I2. lia.
          -- right. intros a Ha. unfold fin_XS. cbn [rin_ivs fst snd]. right; right; left. lia.
        * intros b Hb. apply (Permutation_in _ (Permutation_sym OWN1)). apply in_app_iff. left. exact Hb.
        * intros a Ha. exact Ha.
    -
      eapply stack0_transport; [exact (xa_stack0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) | exact MU | exact WM |].
      apply (Forall_fin_map w); [exact FW |]. intros iv Hiv. exact (fin_stack0_ok w iv OK Hiv).
    -
      eapply LINV_frame; [exact (xa_linv _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) | exact MU | exact WM |].
      apply (Forall_fin_map w); [exact FW |]. intros iv Hiv. exact (fin_above_img w iv OK Hiv).
    -
      pose proof (xa_al _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as (A1 & A2 & A3 & A4). pose proof (pm_phi_le_cap c) as PCAP. lia.
  Qed.
End Fin.
