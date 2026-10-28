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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require RtB_Td.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Conv LbB_SR LbB_FKit LbB_MILB LbB_PrsStmt LbB_Own LbB_PmBase LbB_FSlots LbB_PmOwn LbB_PmCut LbB_PmTac LbB_PmCall.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section Xp.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  Definition xp_ok (w : pmwA H) (ftbl : list (Z * SymExec3.SX2.expr)) (iv : Z * Z) : Prop :=
    (fst iv <= snd iv /\ wa_ff w + 24 <= fst iv /\ snd iv <= wa_ff w + 16376 /\
     Forall (fun ke => snd iv <= wa_ff w + fst ke \/ wa_ff w + fst ke + 8 <= fst iv) ftbl)
    \/ iv = (RtB_Td.ATDLOC, RtB_Td.ATDLOC + 8).

  Definition PMLF (w : pmwA H) : list fframe := (PM_FCLASS, wa_ff w, wa_fp w) :: wa_LF0 w.

  Lemma xp_geom : forall w, pmw_okA H w ->
    as_FSB H + AFS_HDR <= wa_ff w /\ wa_ff w + 16384 <= as_FSB H + AFS_SIZE /\ AIMG_TOP <= as_FSB H
    /\ as_FSB H + AFS_SIZE <= aceil /\ aapp (as_FSB H) AFS_SIZE /\ aapp (wa_ff w) 16384
    /\ (exists f, In f (wa_LF0 w) /\ ff_addr f <= wa_p w /\ wa_p w + PARSER_SIZE <= ff_addr f + fsz (ff_class f)
                 /\ as_FSB H + AFS_HDR <= ff_addr f /\ ff_addr f + fsz (ff_class f) <= as_FSB H + AFS_SIZE).
  Proof.
    intros w OK. pose proof (pmw_frame_facts H w OK) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10).
    change (fsz PM_FCLASS) with 16384 in *.
    split; [exact F4|]. split; [exact F5|]. split; [exact F6|]. split; [exact F7|]. split; [exact F8|]. split.
    - eapply aapp_sub; [exact F8 | unfold AFS_HDR in *; lia | lia].
    - exact (p_frame H HH w OK).
  Qed.

  Lemma scratch_below : forall LF m iv, as_RFS H LF m -> fs_scratch H LF iv -> snd iv <= aceil.
  Proof.
    intros LF m iv R [->|(k & ff & fp & FF & E)].
    - cbn. destruct (proj1 (ah_RFS_range H HH _ _ R)) as (F1 & F2 & F3 & F4). unfold AFS_FLAGS, AFS_SIZE in *. lia.
    - pose proof (fresh_frame_facts H _ _ _ _ FF) as (K & R1 & R2 & M64 & M8 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9).
      pose proof (fsz_pos k ltac:(lia)). pose proof aceil_facts as ((AC1 & AC2) & _ & _).
      destruct E as [-> |[-> | ->]]; cbn; [lia | lia |].
      assert (SE : sh ff + fshn k = sh (ff + fsz k)).
      { unfold sh, fshn, fsz. rewrite (div8_add ff (64 * 2 ^ k) M8).
        replace (64 * 2 ^ k) with ((8 * 2 ^ k) * 8) by ring. rewrite Z.div_mul by lia. ring. }
      assert (sh (ff + fsz k) <= sh aceil) by (apply sh_mono; lia).
      assert (sh aceil <= aceil) by (unfold sh, ASHADOW_BASE; Z.div_mod_to_equations; lia). lia.
  Qed.

  Lemma xp_scr_obj : forall w m XS O n, pmw_okA H w -> as_RFS H (PMLF w) m -> Forall (fs_scratch H (PMLF w)) XS ->
    fsobj H (PMLF w) O n -> 0 <= O -> 0 <= n -> O + n <= AAPP_HI -> aapp O n ->
    Forall (fun iv : Z * Z => O + n <= fst iv \/ snd iv <= O) XS
    /\ Forall (fun iv : Z * Z => sh O + nsh n <= fst iv \/ snd iv <= sh O) XS.
  Proof.
    intros w m XS O n OK R FX FO H0 Hn Ht Ha. split; apply Forall_forall; intros iv Hiv; pose proof (proj1 (Forall_forall _ _) FX iv Hiv) as S.
    - exact (fsobj_scratch H HH _ _ _ _ _ R FO H0 Hn Ht Ha S).
    - exact (fsobj_scratch_sh H HH _ _ _ _ _ R FO H0 Hn Ht S).
  Qed.

  Lemma xpres_fld : forall LBk SP XX m m' a k v, xpres H LBk SP XX m m' -> fld ASEGS m a k v ->
    xclient_range H LBk SP XX a (Z.of_nat k) -> 0 <= a -> a + Z.of_nat k < 2 ^ 64 -> fld ASEGS m' a k v.
  Proof.
    intros LBk SP XX m m' a k v XP F XR H0 H1. eapply fld_agree; [exact H0 | exact H1 | exact F |].
    intros x Hx. unfold zwin in Hx.
    assert (XC : xclient H LBk SP XX x) by (eapply xclient_range_addr; [exact XR | lia]).
    destruct (XP x ltac:(lia) XC) as [E _]. exact E.
  Qed.

  Lemma xpres_mdef : forall LBk SP XX m m' a n, xpres H LBk SP XX m m' -> mdef m a n ->
    xclient_range H LBk SP XX a n -> 0 <= a -> a + n < 2 ^ 64 -> mdef m' a n.
  Proof.
    intros LBk SP XX m m' a n XP D XR H0 H1 i Hi.
    assert (XC : xclient H LBk SP XX (a + i)) by (eapply xclient_range_addr; [exact XR | lia]).
    destruct (XP (a + i) ltac:(lia) XC) as [E _]. unfold wa in E. rewrite E. apply D. exact Hi.
  Qed.

  Lemma xpres_SHAD : forall LBk SP XX m m' A sbs, xpres H LBk SP XX m m' -> SHAD m A sbs ->
    xclient_range H LBk SP XX (sh A) (Z.of_nat (length sbs)) -> SHAD m' A sbs.
  Proof.
    intros LBk SP XX m m' A sbs XP (S0 & S8 & [UB UW]) XR. split; [exact S0|]. split; [exact S8|]. split.
    - eapply xpres_bytes_at; [exact XP | exact UB | exact XR].
    - eapply xpres_wr_at; [exact XP | exact UW | exact XR].
  Qed.

  Lemma xpres_addressable : forall LBk SP XX m m' A n, xpres H LBk SP XX m m' -> addressable m A n ->
    xclient_range H LBk SP XX (sh A) (nsh n) -> addressable m' A n.
  Proof.
    intros LBk SP XX m m' A n XP [Hn SH] XR. split; [exact Hn|]. eapply xpres_SHAD; [exact XP | exact SH |].
    rewrite shadow_of_length by lia. exact XR.
  Qed.

  Lemma xr_stack : forall w LBk XX A n, pmw_okA H w -> wa_s1 w <= A -> 0 <= n ->
    Forall (fun iv : Z * Z => snd iv <= aceil) XX -> xclient_range H LBk (wa_s1 w) XX A n.
  Proof.
    intros w LBk XX A n OK HA Hn FX. pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
    split; [left; exact HA|]. eapply Forall_impl; [| exact FX]. intros iv Hiv. cbn beta in Hiv. right. lia.
  Qed.

  Lemma xr_fs : forall w LBk XX A n, pmw_okA H w -> as_FSB H <= A -> A + n <= as_FSB H + AFS_SIZE ->
    Forall (fun iv : Z * Z => A + n <= fst iv \/ snd iv <= A) XX -> xclient_range H LBk (wa_s1 w) XX A n.
  Proof. intros w LBk XX A n OK H1 H2 FX. split; [right; right; right; right; left; split; assumption | exact FX]. Qed.

  Lemma xr_fssh : forall w LBk XX A n, pmw_okA H w -> sh (as_FSB H) <= A -> A + n <= sh (as_FSB H + AFS_SIZE) ->
    Forall (fun iv : Z * Z => A + n <= fst iv \/ snd iv <= A) XX -> xclient_range H LBk (wa_s1 w) XX A n.
  Proof. intros w LBk XX A n OK H1 H2 FX. split; [right; right; right; right; right; left; split; assumption | exact FX]. Qed.

  Lemma xr_blk : forall (w : pmwA H) LBk XX b A n, In b LBk -> blk_addr b <= A -> A + n <= blk_addr b + blk_size b ->
    Forall (fun iv : Z * Z => A + n <= fst iv \/ snd iv <= A) XX -> xclient_range H LBk (wa_s1 w) XX A n.
  Proof. intros w LBk XX b A n Hb H1 H2 FX. split; [right; right; left; exists b; auto | exact FX]. Qed.

  Lemma xr_blksh : forall (w : pmwA H) LBk XX b A n, In b LBk -> sh (blk_addr b) <= A -> A + n <= sh (blk_addr b) + nsh (blk_size b) ->
    Forall (fun iv : Z * Z => A + n <= fst iv \/ snd iv <= A) XX -> xclient_range H LBk (wa_s1 w) XX A n.
  Proof. intros w LBk XX b A n Hb H1 H2 FX. split; [right; right; right; left; exists b; auto | exact FX]. Qed.

  Lemma ap_X_out : forall (w : pmwA H) ftbl X A n, Forall (xp_ok w ftbl) X -> (A + n <= wa_ff w + 24 \/ wa_ff w + 16376 <= A) ->
    RtB_Td.ATDLOC + 8 <= A ->
    Forall (fun iv : Z * Z => A + n <= fst iv \/ snd iv <= A) X.
  Proof.
    intros w ftbl X A n FX HA TD. eapply Forall_impl; [| exact FX]. intros iv [(I0 & I1 & I2 & _)| ->]; [lia | cbn [fst snd]; lia].
  Qed.

  Lemma ap_X_slot : forall (w : pmwA H) ftbl X k e, Forall (xp_ok w ftbl) X -> In (k, e) ftbl ->
    RtB_Td.ATDLOC + 8 <= wa_ff w + k ->
    Forall (fun iv : Z * Z => wa_ff w + k + 8 <= fst iv \/ snd iv <= wa_ff w + k) X.
  Proof.
    intros w ftbl X k e FX Hin TD. eapply Forall_impl; [| exact FX]. intros iv [(I0 & I1 & I2 & I3)| ->]; cbn beta; [| cbn [fst snd]; lia].
    pose proof (proj1 (Forall_forall _ _) I3 (k, e) Hin) as D. cbn [fst] in D. lia.
  Qed.

  Lemma ap_X_ffsh : forall w ftbl X, pmw_okA H w -> Forall (xp_ok w ftbl) X ->
    Forall (fun iv : Z * Z => sh (wa_ff w) + PM_NSH <= fst iv \/ snd iv <= sh (wa_ff w)) X.
  Proof.
    intros w ftbl X OK FX. pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
    assert (TD : RtB_Td.ATDLOC + 8 <= sh (wa_ff w)) by (unfold sh; rewrite ASHADOW_BASE_val; unfold RtB_Td.ATDLOC; clear - G1 G2 G3 G4 G5; Z.div_mod_to_equations; lia).
    eapply Forall_impl; [| exact FX]. intros iv [(I0 & I1 & I2 & _)| ->]; cbn beta; [| cbn [fst snd]; right; exact TD]. unfold PM_NSH. rewrite G13 in *.
    destruct G6 as [G6|G6]; [right | left]; lia.
  Qed.

  Lemma ap_X_sh : forall w ftbl X O n, pmw_okA H w -> Forall (xp_ok w ftbl) X -> 0 <= O -> 0 <= n -> O + n <= AAPP_HI ->
    Forall (fun iv : Z * Z => sh O + nsh n <= fst iv \/ snd iv <= sh O) X.
  Proof.
    intros w ftbl X O n OK FX H0 Hn Ht. pose proof (xp_geom w OK) as (_ & _ & _ & _ & _ & FA & _).
    pose proof (aapp_disjoint_sh (wa_ff w) 16384 O n FA H0 Ht Hn) as D.
    assert (TD : RtB_Td.ATDLOC + 8 <= sh O) by (unfold sh; rewrite ASHADOW_BASE_val; unfold RtB_Td.ATDLOC; clear - H0; Z.div_mod_to_equations; lia).
    eapply Forall_impl; [| exact FX]. intros iv [(I0 & I1 & I2 & _)| ->]; cbn beta; [| cbn [fst snd]; right; exact TD]. destruct D as [D|D]; [left | right]; lia.
  Qed.

  Lemma ap_X_apart : forall (w : pmwA H) ftbl X O n, Forall (xp_ok w ftbl) X -> (O + n <= wa_ff w \/ wa_ff w + 16384 <= O) ->
    RtB_Td.ATDLOC + 8 <= O ->
    Forall (fun iv : Z * Z => O + n <= fst iv \/ snd iv <= O) X.
  Proof. intros w ftbl X O n FX HO TD. eapply Forall_impl; [| exact FX]. intros iv [(I0 & I1 & I2 & _)| ->]; cbn beta; [lia | cbn [fst snd]; lia]. Qed.

  Lemma lf0_apart_ff : forall w f O n, pmw_okA H w -> In f (wa_LF0 w) -> ff_addr f <= O -> O + n <= ff_addr f + fsz (ff_class f) ->
    O + n <= wa_ff w \/ wa_ff w + 16384 <= O.
  Proof.
    intros w f O n OK Hf H1 H2. destruct (wk_fresh H w OK) as (_ & _ & FR). destruct (FR f Hf) as [D _].
    change (fsz PM_FCLASS) with 16384 in D. destruct D as [D|D]; [right | left]; lia.
  Qed.

  Lemma blk_apart_ff : forall w s LB m b, pmw_okA H w -> as_RHEAP H s LB m -> In b LB ->
    blk_addr b + blk_size b <= wa_ff w \/ wa_ff w + 16384 <= blk_addr b.
  Proof.
    intros w s LB m b OK RH Hb. pose proof (ah_blocks H HH _ _ _ _ RH Hb) as (R0 & R16 & Rn & RI & RC & RF & RAPP).
    pose proof (xp_geom w OK) as (F1 & F2 & _). unfold AFS_HDR in *. lia.
  Qed.
End Xp.

Section XpMain.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Variable LINV : mem -> Prop.

  Lemma fs_scratch_tail : forall f LF iv, fs_scratch H (f :: LF) iv -> fs_scratch H LF iv.
  Proof.
    intros f LF iv [E|(k & ff & fp & (FA & FB & FR) & E)]; [left; exact E | right].
    exists k, ff, fp. split; [| exact E]. split; [exact FA|]. split; [exact FB|]. intros g Hg. apply FR. right. exact Hg.
  Qed.

  Lemma chain_via_xpres : forall LBk SP XX m m' cur CH, as_chain H m cur CH -> xpres H LBk SP XX m m' ->
    (forall fp ra, In (fp, ra) CH -> SP + 16 <= fp) ->
    (forall fp ra, In (fp, ra) CH -> Forall (fun iv : Z * Z => fp <= fst iv \/ snd iv <= fp - 16) XX) ->
    as_chain H m' cur CH.
  Proof.
    intros LBk SP XX m m' cur CH C XP HS HX. eapply (ah_chain_ext H HH); [exact C|].
    intros fp ra a IN Ha. pose proof (ah_chain_range H HH _ _ _ _ _ C IN) as (R1 & R2 & R3).
    pose proof aceil_facts as ((AC1 & AC2) & _ & _).
    assert (XC : xclient H LBk SP XX a).
    { split; [left; pose proof (HS _ _ IN); lia|].
      pose proof (HX _ _ IN) as F. clear -F Ha. induction XX as [|iv XX IH]; cbn; [tauto|].
      apply Forall_cons_iff in F as [F1 F2]. intros [K|K]; [lia | exact (IH F2 K)]. }
    exact (proj1 (XP a ltac:(lia) XC)).
  Qed.

  Lemma pmxa_xp : forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl TB spal s' LB' LBs' m' mo' c' TB' spal' LBk X XS,
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal -> keys_nonneg (map fst tbl) = true ->

    as_RHEAP H s' LB' m' -> as_MPRES H mo mo' -> mem_inv asegs m' -> stk asegs m' (wa_lo w) (wa_s1 w) ->
    (exists errv : word, rw_cells asegs m' (errno_addr (wa_tp w)) [C4 errv]) -> as_rauxv_ok H m' (wa_B w) ->
    as_RFS H (PMLF H w) m' -> ACONST m' -> stack0 m' (wa_lo w) (wa_shi w) -> LINV m' ->
    Forall (fs_scratch H (PMLF H w)) XS -> xpres H LBk (wa_s1 w) (X ++ XS) m m' ->
    Forall (xp_ok H w ftbl) X -> Forall (fun iv : Z * Z => wr_at asegs m' (fst iv) (snd iv - fst iv)) X ->
    fkeys_ok (map fst ftbl) = true ->

    (forall b, In b LBk -> In b LB) -> (forall b, In b (wa_LB0 w) -> In b LBk) ->
    Permutation LB' (wa_LB0 w ++ LBs' ++ TB') -> Permutation (lbl LBs') (c_blocks c') -> lb_own LBs' m' -> pm_meas_ok (wa_n w) LBs' ->
    lb_own TB' m' -> (length TB' <= 1)%nat ->

    as_AL H s' >= as_AL H (wa_s0 w) - pm_phi c' - spal' -> pm_cap c' + PM_RESERVE <= po_cost (wa_n w) -> 0 <= spal' <= PM_RESERVE ->

    c_widx c' = c_widx c -> c_icount c' = c_icount c -> c_endian c' = c_endian c -> c_reqconv c' = c_reqconv c ->
    @umapx AC_A ASEGS LY_A MI_A 24 Z (nval24 ASEGS) (lbl LB') m' (wa_p w + O_M1) (t3a (c_m1 c')) (t3b (c_m1 c')) (t3c (c_m1 c')) ->
    @umapx AC_A ASEGS LY_A MI_A 32 (Z * Z * Z) (nval32 ASEGS) (lbl LB') m' (wa_p w + O_M2) (t3a (c_m2 c')) (t3b (c_m2 c')) (t3c (c_m2 c')) ->
    @umapx AC_A ASEGS LY_A MI_A 24 Z (nval24 ASEGS) (lbl LB') m' (wa_p w + O_M3) (t3a (c_m3 c')) (t3b (c_m3 c')) (t3c (c_m3 c')) ->
    @vec_opnd AC_A ASEGS LY_A MI_A (lbl LB') m' (wa_p w + O_V1) (t3a (c_v1 c')) (t3b (c_v1 c')) (t3c (c_v1 c')) ->
    @vec32 AC_A ASEGS LY_A MI_A (lbl LB') m' (wa_p w + O_V2) (t3a (c_v2 c')) (t3b (c_v2 c')) (t3c (c_v2 c')) ->
    @vec32 AC_A ASEGS LY_A MI_A (lbl LB') m' (wa_p w + O_V3) (t3a (c_v3 c')) (t3b (c_v3 c')) (t3c (c_v3 c')) ->
    pmc_sh m' c' ->
    PMXAT H LINV w s' LB' LBs' m' mo' c' ins tbl ftbl TB' spal'.
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal s' LB' LBs' m' mo' c' TB' spal' LBk X XS OK X0 Hknn
           RH' MP' MI' STK' ERR' RA' RFS' AC' S0' LI' FXS XP FX FXW Hfk LBk1 LBk0 OWN1 OWN2 OWN3 MEAS' TBO TBL AL1 AL2 SPAL
           Cw Ci Ce Cr U1 U2 U3 V1 V2 V3 SHc.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (xp_geom H HH w OK) as (F1 & F2 & F3 & F4 & F5 & FA & (fp0 & Hfp0 & PF1 & PF2 & PF3 & PF4)).
    pose proof (pmw_bounds H w OK) as BND.
    pose proof (wk_stack H w OK) as (S1 & S2 & S3 & S4 & S5 & S6).
    pose proof (p_range H w OK) as (PR1 & PR2).
    pose proof (wk_papp H w OK) as (PA & PA0 & PA16).
    pose proof (wk_capp H w OK) as (CA & CA0 & CA16).
    destruct (wk_cin H w OK) as (fc0 & Hfc0 & CF1 & CF2).
    pose proof (proj2 (ah_RFS_range H HH _ _ RFS') fc0 (or_intror Hfc0)) as (_ & CR1 & CR2 & _).
    set (XX := X ++ XS).
    assert (XXb : Forall (fun iv : Z * Z => snd iv <= aceil) XX).
    { apply Forall_app. split.
      - eapply Forall_impl; [| exact FX]. intros iv [(I0 & I1 & I2 & _)| ->]; [lia | cbn [snd]; unfold RtB_Td.ATDLOC; lia].
      - eapply Forall_impl; [| exact FXS]. intros iv Hiv. exact (scratch_below H HH _ _ _ RFS' Hiv). }

    assert (FOp : fsobj H (PMLF H w) (wa_p w) PARSER_SIZE) by (right; exists fp0; split; [right; exact Hfp0 | lia]).
    assert (FOc : fsobj H (PMLF H w) (wa_cons w) 48) by (right; exists fc0; split; [right; exact Hfc0 | lia]).
    assert (FOf : fsobj H (PMLF H w) (wa_ff w) 16384) by (right; exists (PM_FCLASS, wa_ff w, wa_fp w); split; [left; reflexivity | unfold ff_addr, ff_class; cbn [fst snd]; change (fsz PM_FCLASS) with 16384; lia]).
    pose proof (xp_scr_obj H HH w m' XS (wa_p w) PARSER_SIZE OK RFS' FXS FOp ltac:(lia) ltac:(unfold PARSER_SIZE; lia) ltac:(unfold AAPP_HI, PARSER_SIZE in *; lia) PA) as [SXp SXps].
    pose proof (xp_scr_obj H HH w m' XS (wa_cons w) 48 OK RFS' FXS FOc ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI in *; lia) CA) as [SXc SXcs].
    pose proof (xp_scr_obj H HH w m' XS (wa_ff w) 16384 OK RFS' FXS FOf ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI in *; lia) FA) as [SXf SXfs].
    assert (SUBXS : forall O n O' n', Forall (fun iv : Z * Z => O + n <= fst iv \/ snd iv <= O) XS -> O <= O' -> O' + n' <= O + n ->
              Forall (fun iv : Z * Z => O' + n' <= fst iv \/ snd iv <= O') XS).
    { intros O n O' n' F HO HO'. eapply Forall_impl; [| exact F]. intros iv Hiv. cbn beta in *. lia. }

    pose proof (lf0_apart_ff H w fp0 (wa_p w) PARSER_SIZE OK Hfp0 PF1 PF2) as PFF.
    pose proof (lf0_apart_ff H w fc0 (wa_cons w) 48 OK Hfc0 CF1 CF2) as CFF.

    assert (XRp : forall k n, 0 <= k -> 0 <= n -> k + n <= PARSER_SIZE -> xclient_range H LBk (wa_s1 w) XX (wa_p w + k) n).
    { intros k n Hk Hn Hkn. apply (xr_fs H w); [exact OK | unfold PARSER_SIZE, AFS_HDR in *; lia | unfold PARSER_SIZE in *; lia |].
      apply Forall_app. split.
      - eapply ap_X_apart; [exact FX | unfold PARSER_SIZE in *; lia | unfold RtB_Td.ATDLOC, AIMG_TOP, AFS_HDR, PARSER_SIZE in *; lia].
      - eapply SUBXS; [exact SXp | lia | lia]. }
    assert (XRc : forall k n, 0 <= k -> 0 <= n -> k + n <= 48 -> xclient_range H LBk (wa_s1 w) XX (wa_cons w + k) n).
    { intros k n Hk Hn Hkn. apply (xr_fs H w); [exact OK | unfold AFS_HDR in *; lia | lia |].
      apply Forall_app. split.
      - eapply ap_X_apart; [exact FX | lia | unfold RtB_Td.ATDLOC, AIMG_TOP, AFS_HDR, PARSER_SIZE in *; lia].
      - eapply SUBXS; [exact SXc | lia | lia]. }
    assert (XRffh : forall k n, 0 <= k -> 0 <= n -> k + n <= 16384 -> (k + n <= 24 \/ 16376 <= k) ->
              xclient_range H LBk (wa_s1 w) XX (wa_ff w + k) n).
    { intros k n Hk Hn Hkn Hh. apply (xr_fs H w); [exact OK | unfold AFS_HDR in *; lia | lia |].
      apply Forall_app. split.
      - eapply ap_X_out; [exact FX | lia | unfold RtB_Td.ATDLOC, AIMG_TOP, AFS_HDR, PARSER_SIZE in *; lia].
      - eapply SUBXS; [exact SXf | lia | lia]. }
    assert (XRsl : forall k e, In (k, e) ftbl -> 0 <= k -> k + 8 <= 16384 -> xclient_range H LBk (wa_s1 w) XX (wa_ff w + k) 8).
    { intros k e Hin Hk Hk8. apply (xr_fs H w); [exact OK | unfold AFS_HDR in *; lia | lia |].
      apply Forall_app. split.
      - pose proof (ap_X_slot H w ftbl X k e FX Hin ltac:(unfold RtB_Td.ATDLOC, AIMG_TOP, AFS_HDR, PARSER_SIZE in *; lia)) as D. exact D.
      - eapply SUBXS; [exact SXf | lia | lia]. }
    assert (XRfsh : xclient_range H LBk (wa_s1 w) XX (sh (wa_ff w)) PM_NSH).
    { apply (xr_fssh H w); [exact OK | apply sh_mono; unfold AFS_HDR in *; lia | |].
      - assert (sh (wa_ff w + 11584) <= sh (as_FSB H + AFS_SIZE)) by (apply sh_mono; lia).
        assert (sh (wa_ff w) + 1448 = sh (wa_ff w + 11584)) by (unfold sh; rewrite (div8_add (wa_ff w) 11584) by (Z.div_mod_to_equations; lia); change (11584 / 8) with 1448; ring).
        unfold PM_NSH. lia.
      - apply Forall_app. split; [exact (ap_X_ffsh H w ftbl X OK FX)|].
        eapply SUBXS; [exact SXfs | lia | unfold nsh, PM_NSH; change ((16384 + 7) / 8) with 2048; lia]. }
    assert (XRst : forall A n, wa_s1 w <= A -> 0 <= n -> xclient_range H LBk (wa_s1 w) XX A n).
    { intros A n HA Hn. apply (xr_stack H w); [exact OK | exact HA | exact Hn | exact XXb]. }
    assert (XRsh : forall O n, 0 <= O -> 0 <= n -> O + n <= AAPP_HI -> Forall (fun iv : Z * Z => sh O + nsh n <= fst iv \/ snd iv <= sh O) XS ->
              (sh (as_FSB H) <= sh O /\ sh O + nsh n <= sh (as_FSB H + AFS_SIZE)) -> xclient_range H LBk (wa_s1 w) XX (sh O) (nsh n)).
    { intros O n H0 Hn Ht SX [B1 B2]. apply (xr_fssh H w); [exact OK | exact B1 | exact B2 |].
      apply Forall_app. split; [exact (ap_X_sh H HH w ftbl X O n OK FX H0 Hn Ht) | exact SX]. }

    destruct X0 as [Xrheap Xlbown Xtb Xown Xmeas Xmpres Xmeminv Xstk Xerrno Xrauxv Xaconst Xstack0 Xlinv Xrfs Xxpres Xal Xsaved Xfhdr Xfflag Xfwr Xchain Xfsh Xslots Xfslots Xpdef Xcons Xuser Xhdrfn Xinsfn Xhunk Xwords Xn Xdiag Xwidx Xicount Xendian Xflags Xretry Xscal Xconsf Xconsd Xconsw Xwbuf Xm1 Xm2 Xm3 Xv1 Xv2 Xv3 Xsh].
    constructor.
    - exact RH'.
    - exact OWN3.
    - split; [exact TBO | exact TBL].
    - split; [exact OWN1 | exact OWN2].
    - exact MEAS'.
    - eapply (ah_mpres_trans H HH); [exact Xmpres | exact MP'].
    - exact MI'.
    - apply (stk_join m' (wa_lo w) (wa_s1 w) (wa_sp0 w)); [exact STK' | | lia].
      destruct (stk_split asegs m (wa_lo w) (wa_s1 w) (wa_sp0 w) Xstk ltac:(lia)) as [_ ST2].
      eapply (xpres_stk H); [exact XP | exact ST2 | lia |]. eapply Forall_impl; [| exact XXb]. intros iv Hiv. cbn beta in *. right. lia.
    - exact ERR'.
    - exact RA'.
    - exact AC'.
    - exact S0'.
    - exact LI'.
    - exact RFS'.
    - destruct Xxpres as (XS0 & FXS0 & XP0). exists (XS0 ++ XS). split.
      + apply Forall_app. split; [exact FXS0|]. eapply Forall_impl; [| exact FXS]. intros iv Hiv. exact (fs_scratch_tail _ _ _ Hiv).
      + eapply xpres_trans.
        * eapply (xpres_weaken H); [exact XP0 | lia | intros b Hb; exact Hb |].
          intros a Ha. cbn [rin_ivs] in *. destruct Ha as [Ha|[Ha|[Ha|[Ha|Ha]]]]; [left | right; left | right; right; left | right; right; right; left |]; try exact Ha.
          right; right; right; right. apply rin_ivs_app. left. exact Ha.
        * eapply (xpres_weaken H); [exact XP | lia | intros b Hb; exact (LBk0 b Hb) |].
          intros a Ha. apply rin_ivs_app in Ha as [Ha|Ha].
          -- cbn [rin_ivs fst snd]. change (fsz PM_FCLASS) with 16384.
             clear -Ha FX. induction X as [|iv X IH]; cbn in Ha; [contradiction|].
             apply Forall_cons_iff in FX as [[(I0 & I1 & I2 & _)|E] FX]; (destruct Ha as [Ha|Ha]; [| exact (IH FX Ha)]);
               [right; right; left; lia | left; rewrite E in Ha; exact Ha].
          -- right; right; right; right. apply rin_ivs_app. right. exact Ha.
    - split; [exact AL1|]. split; [exact AL2|]. split; [exact (proj1 (proj2 (proj2 Xal))) | exact SPAL].
    - eapply (xpres_rw_cells H); [exact XP | exact Xsaved |]. rewrite cells_size_mapC8, (wk_saved H w OK). apply XRst; lia.
    - eapply (xpres_rw_cells H); [exact XP | exact Xfhdr |]. cbn [cells_size csize Nat.add].
      replace (wa_ff w) with (wa_ff w + 0) at 1 by lia. apply XRffh; lia.
    - eapply (xpres_rw_cells H); [exact XP | exact Xfflag |]. cbn [cells_size csize Nat.add]. change (fsz PM_FCLASS) with 16384.
      replace (wa_ff w + 16384 - 8) with (wa_ff w + 16376) by lia. apply XRffh; lia.
    - destruct Xfwr as (W1 & W2 & W3). split; [exact W1|]. split; [exact W2|]. intros i Hi. change (fsz PM_FCLASS) with 16384 in *.
      destruct (Z_lt_le_dec i 24) as [Li|Li]; [| destruct (Z_le_gt_dec 16376 i) as [Ui|Ui]].
      + pose proof (XP (wa_ff w + i) ltac:(lia)) as K. destruct K as [_ K]; [| exact (K (W3 i Hi))].
        eapply (xclient_range_addr H); [apply (XRffh 0 24); lia | lia].
      + pose proof (XP (wa_ff w + i) ltac:(lia)) as K. destruct K as [_ K]; [| exact (K (W3 i Hi))].
        eapply (xclient_range_addr H); [apply (XRffh 16376 8); lia | lia].
      +
        destruct (outside_dec X (wa_ff w + i)) as [Ho|(lo & hi & Hin & Hr)].
        * assert (XC : xclient H LBk (wa_s1 w) XX (wa_ff w + i)).
          { split; [right; right; right; right; left; unfold AFS_HDR in *; lia|].
            intros R. apply rin_ivs_app in R as [R|R].
            - clear -R Ho. induction X as [|[lo hi] X IH]; cbn in R, Ho; [contradiction|]. destruct Ho as [Ho1 Ho2]. destruct R as [R|R]; [lia | eapply IH; eassumption].
            - pose proof SXf as F. clear -R F Hi. induction XS as [|iv XS IH]; cbn in R; [contradiction|].
              apply Forall_cons_iff in F as [F1 F2]. destruct R as [R|R]; [cbn beta in F1; lia | eapply IH; eassumption]. }
          exact (proj2 (XP (wa_ff w + i) ltac:(lia) XC) (W3 i Hi)).
        * pose proof (proj1 (Forall_forall _ _) FXW (lo, hi) Hin) as (_ & _ & WW). cbn [fst snd] in WW.
          replace (wa_ff w + i) with (lo + (wa_ff w + i - lo)) by lia. apply WW. lia.
    - eapply chain_via_xpres; [exact Xchain | exact XP | |].
      + intros fp ra Hin. destruct Hin as [Hin|Hin]; [injection Hin as <- <-; lia | pose proof (wk_chfr H w OK fp ra Hin); lia].
      + intros fp ra Hin. assert (Hfp : wa_sp0 w <= fp) by (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; lia | pose proof (wk_chfr H w OK fp ra Hin); lia]).
        eapply Forall_impl; [| exact XXb]. intros iv Hiv. cbn beta in *. right. lia.
    - eapply (xpres_SHAD H); [exact XP | exact Xfsh |]. unfold pm_fsh. rewrite length_map, pm_fsh_len. exact XRfsh.
    - unfold slots_ok in *. apply Forall_forall. intros [k e] Hin. pose proof (proj1 (Forall_forall _ _) Xslots (k, e) Hin) as C.
      cbn [fst snd] in *. pose proof (proj1 (forallb_forall _ _) Hknn k (in_map fst _ (k, e) Hin)) as Kk. apply Z.leb_le in Kk.
      eapply (xpres_rw_cells H); [exact XP | exact C |]. cbn [cells_size csize]. apply XRst; lia.
    - unfold fslots_ok in *. apply Forall_forall. intros [k e] Hin. pose proof (proj1 (Forall_forall _ _) Xfslots (k, e) Hin) as C.
      cbn [fst snd] in *. pose proof (proj1 (forallb_forall _ _) Hfk k (in_map fst _ (k, e) Hin)) as Kk.
      apply andb_true_iff in Kk as [K1 K2]. apply Z.leb_le in K1. apply Z.leb_le in K2.
      eapply (xpres_rw_cells H); [exact XP | exact C |]. cbn [cells_size csize]. apply (XRsl k e Hin); lia.
    - eapply xpres_mdef; [exact XP | exact Xpdef | | lia | unfold PARSER_SIZE in *; lia].
      replace (wa_p w) with (wa_p w + 0) by lia. apply XRp; unfold PARSER_SIZE; lia.
    - eapply xpres_fld; [exact XP | exact Xcons | apply XRp; unfold PARSER_SIZE; cbn; lia | lia | cbn; unfold PARSER_SIZE in *; lia].
    - eapply xpres_fld; [exact XP | exact Xuser | apply XRp; unfold PARSER_SIZE; cbn; lia | lia | cbn; unfold PARSER_SIZE in *; lia].
    - eapply xpres_fld; [exact XP | exact Xhdrfn | apply XRp; unfold PARSER_SIZE; cbn; lia | lia | cbn; unfold PARSER_SIZE in *; lia].
    - eapply xpres_fld; [exact XP | exact Xinsfn | apply XRp; unfold PARSER_SIZE; cbn; lia | lia | cbn; unfold PARSER_SIZE in *; lia].
    - eapply xpres_fld; [exact XP | exact Xhunk | apply XRp; unfold PARSER_SIZE; cbn; lia | lia | cbn; unfold PARSER_SIZE in *; lia].
    - eapply xpres_fld; [exact XP | exact Xwords | apply XRp; unfold O_WORDS, PARSER_SIZE; cbn; lia | unfold O_WORDS; lia | cbn; unfold O_WORDS, PARSER_SIZE in *; lia].
    - eapply xpres_fld; [exact XP | exact Xn | apply XRp; unfold O_N, PARSER_SIZE; cbn; lia | unfold O_N; lia | cbn; unfold O_N, PARSER_SIZE in *; lia].
    - eapply xpres_fld; [exact XP | exact Xdiag | apply XRp; unfold O_DIAG, PARSER_SIZE; cbn; lia | unfold O_DIAG; lia | cbn; unfold O_DIAG, PARSER_SIZE in *; lia].
    - rewrite Cw. eapply xpres_fld; [exact XP | exact Xwidx | apply XRp; unfold O_WIDX, PARSER_SIZE; cbn; lia | unfold O_WIDX; lia | cbn; unfold O_WIDX, PARSER_SIZE in *; lia].
    - rewrite Ci. eapply xpres_fld; [exact XP | exact Xicount | apply XRp; unfold O_ICOUNT, PARSER_SIZE; cbn; lia | unfold O_ICOUNT; lia | cbn; unfold O_ICOUNT, PARSER_SIZE in *; lia].
    - rewrite Ce. eapply xpres_fld; [exact XP | exact Xendian | apply XRp; unfold O_ENDIAN, PARSER_SIZE; cbn; lia | unfold O_ENDIAN; lia | cbn; unfold O_ENDIAN, PARSER_SIZE in *; lia].
    - rewrite Cr. eapply xpres_fld; [exact XP | exact Xflags | apply XRp; unfold O_FLAGS, PARSER_SIZE; cbn; lia | unfold O_FLAGS; lia | cbn; unfold O_FLAGS, PARSER_SIZE in *; lia].
    - rewrite <- Z.add_assoc in *. eapply xpres_fld; [exact XP | exact Xretry | apply XRp; unfold O_FLAGS, PARSER_SIZE; cbn; lia | unfold O_FLAGS; lia | cbn; unfold O_FLAGS, PARSER_SIZE in *; lia].
    - rewrite Cw, Ci, Ce, Cr. exact Xscal.
    - eapply xpres_fld; [exact XP | exact Xconsf | apply XRc; cbn; lia | lia | cbn; lia].
    - eapply xpres_mdef; [exact XP | exact Xconsd | apply XRc; lia | lia | lia].
    - eapply (xpres_wr_at H); [exact XP | exact Xconsw |]. replace (wa_cons w) with (wa_cons w + 0) at 1 by lia. apply XRc; lia.
    - intros Hwz. destruct (wk_words H w OK) as [[E0 _]|(pw & k & Hin & Hk & W0 & W16 & Whi & Wdef & Wsh)]; [contradiction|].
      assert (HinLB : In (pw, wa_words w, k) LB).
      { apply (Permutation_in _ (Permutation_sym (proj1 Xown))). apply in_app_iff. left. exact Hin. }
      pose proof (ah_blocks H HH _ _ _ _ Xrheap HinLB) as (R0 & R16 & Rn & RI & RC & RF & RAPP). cbn [blk_addr blk_size fst snd] in *.
      pose proof (blk_apart_ff H HH w s LB m _ OK Xrheap HinLB) as BF. cbn [blk_addr blk_size fst snd] in BF.
      assert (FOw : fsobj H (PMLF H w) (wa_words w) k) by (eapply fsobj_block; [exact HH | exact Xrheap | exact HinLB]).
      pose proof (xp_scr_obj H HH w m' XS (wa_words w) k OK RFS' FXS FOw ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI in *; lia) RAPP) as [SXw _].
      eapply xpres_mdef; [exact XP | exact (Xwbuf Hwz) | | lia | lia].
      apply (xr_blk H w LBk XX (pw, wa_words w, k)); [exact (LBk0 _ Hin) | cbn; lia | cbn; lia |].
      apply Forall_app. split; [eapply ap_X_apart; [exact FX | lia | unfold RtB_Td.ATDLOC, AIMG_TOP, AFS_HDR, PARSER_SIZE in *; lia] | eapply SUBXS; [exact SXw | lia | lia]].
    - exact U1.
    - exact U2.
    - exact U3.
    - exact V1.
    - exact V2.
    - exact V3.
    - split; [exact SHc|]. destruct Xsh as (_ & SHp & SHk). split.
      + eapply xpres_addressable; [exact XP | exact SHp |].
        apply XRsh; [lia | unfold PARSER_SIZE; lia | unfold AAPP_HI, PARSER_SIZE in *; lia | exact SXps |].
        split; [apply sh_mono; unfold AFS_HDR in *; lia|].
        assert (sh (wa_p w + PARSER_SIZE) <= sh (as_FSB H + AFS_SIZE)) by (apply sh_mono; unfold PARSER_SIZE in *; lia).
        assert (sh (wa_p w) + nsh PARSER_SIZE = sh (wa_p w + PARSER_SIZE)).
        { unfold sh, nsh, PARSER_SIZE. rewrite (div8_add (wa_p w) 288) by (Z.div_mod_to_equations; lia).
          change (288 / 8) with 36. change ((288 + 7) / 8) with 36. ring. }
        lia.
      + eapply xpres_addressable; [exact XP | exact SHk |].
        apply XRsh; [lia | lia | unfold AAPP_HI in *; lia | exact SXcs |].
        split; [apply sh_mono; unfold AFS_HDR in *; lia|].
        assert (sh (wa_cons w + 48) <= sh (as_FSB H + AFS_SIZE)) by (apply sh_mono; lia).
        assert (sh (wa_cons w) + nsh 48 = sh (wa_cons w + 48)).
        { unfold sh, nsh. rewrite (div8_add (wa_cons w) 48) by (Z.div_mod_to_equations; lia).
          change (48 / 8) with 6. change ((48 + 7) / 8) with 6. ring. }
        lia.
  Qed.
End XpMain.

Lemma vec32_live : forall m L L' v b xs cap, @vec32 AC_A ASEGS LY_A MI_A L m v b xs cap ->
  (b <> 0 -> In (b, 4 * cap) L -> In (b, 4 * cap) L') -> @vec32 AC_A ASEGS LY_A MI_A L' m v b xs cap.
Proof.
  intros m L L' v b xs cap (V0 & V1 & V2 & V3 & V4 & V5) HL. unfold vec32.
  split; [exact V0|]. split; [exact V1|]. split; [exact V2|]. split; [exact V3|]. split; [| exact V5].
  destruct V4 as [V4|(B0 & B1 & B2 & B3 & B4 & B5)]; [left; exact V4 | right].
  split; [exact B0|]. split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [apply HL; [lia | exact B4] | exact B5].
Qed.

Lemma vec_opnd_live : forall m L L' v b n cap, @vec_opnd AC_A ASEGS LY_A MI_A L m v b n cap ->
  (b <> 0 -> In (b, OPND_SZ * cap) L -> In (b, OPND_SZ * cap) L') -> @vec_opnd AC_A ASEGS LY_A MI_A L' m v b n cap.
Proof.
  intros m L L' v b n cap (V0 & V1 & V2 & V3 & V4 & V5) HL. unfold vec_opnd.
  split; [exact V0|]. split; [exact V1|]. split; [exact V2|]. split; [exact V3|]. split; [| exact V5].
  destruct V4 as [V4|(B0 & B1 & B2 & B3 & B4 & B5)]; [left; exact V4 | right].
  split; [exact B0|]. split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [apply HL; [lia | exact B4] | exact B5].
Qed.

Section Keep.
  Context {HCEIL : HeapCeil}.

  Lemma pmc_keep_gen : forall (p : Z) L L' m m' (c : pmc),
    @umapx AC_A ASEGS LY_A MI_A 24 Z (nval24 ASEGS) L m (p + O_M1) (t3a (c_m1 c)) (t3b (c_m1 c)) (t3c (c_m1 c)) ->
    @umapx AC_A ASEGS LY_A MI_A 32 (Z * Z * Z) (nval32 ASEGS) L m (p + O_M2) (t3a (c_m2 c)) (t3b (c_m2 c)) (t3c (c_m2 c)) ->
    @umapx AC_A ASEGS LY_A MI_A 24 Z (nval24 ASEGS) L m (p + O_M3) (t3a (c_m3 c)) (t3b (c_m3 c)) (t3c (c_m3 c)) ->
    @vec_opnd AC_A ASEGS LY_A MI_A L m (p + O_V1) (t3a (c_v1 c)) (t3b (c_v1 c)) (t3c (c_v1 c)) ->
    @vec32 AC_A ASEGS LY_A MI_A L m (p + O_V2) (t3a (c_v2 c)) (t3b (c_v2 c)) (t3c (c_v2 c)) ->
    @vec32 AC_A ASEGS LY_A MI_A L m (p + O_V3) (t3a (c_v3 c)) (t3b (c_v3 c)) (t3c (c_v3 c)) ->
    pmc_sh m c ->
    0 <= p -> p + PARSER_SIZE < 2 ^ 47 ->
    (forall a, p + O_M1 <= a < p + PARSER_SIZE -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)) ->
    (forall A n a, In (A, n) (c_blocks c) -> A <= a < A + n -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)) ->
    (forall A n sbs, In (A, n) (c_blocks c) -> Z.of_nat (length sbs) <= nsh n -> SHAD m A sbs -> SHAD m' A sbs) ->
    (forall b, In b (c_blocks c) -> In b L -> In b L') ->
    @umapx AC_A ASEGS LY_A MI_A 24 Z (nval24 ASEGS) L' m' (p + O_M1) (t3a (c_m1 c)) (t3b (c_m1 c)) (t3c (c_m1 c))
    /\ @umapx AC_A ASEGS LY_A MI_A 32 (Z * Z * Z) (nval32 ASEGS) L' m' (p + O_M2) (t3a (c_m2 c)) (t3b (c_m2 c)) (t3c (c_m2 c))
    /\ @umapx AC_A ASEGS LY_A MI_A 24 Z (nval24 ASEGS) L' m' (p + O_M3) (t3a (c_m3 c)) (t3b (c_m3 c)) (t3c (c_m3 c))
    /\ @vec_opnd AC_A ASEGS LY_A MI_A L' m' (p + O_V1) (t3a (c_v1 c)) (t3b (c_v1 c)) (t3c (c_v1 c))
    /\ @vec32 AC_A ASEGS LY_A MI_A L' m' (p + O_V2) (t3a (c_v2 c)) (t3b (c_v2 c)) (t3c (c_v2 c))
    /\ @vec32 AC_A ASEGS LY_A MI_A L' m' (p + O_V3) (t3a (c_v3 c)) (t3b (c_v3 c)) (t3c (c_v3 c))
    /\ pmc_sh m' c.
  Proof.
    intros p L L' m m' c U1 U2 U3 V1 V2 V3 SHc Hp0 Hp1 HEQ BEQ SEQ LIVE.
    assert (CB : forall bs, incl bs (c_blocks c) -> forall A n a, In (A, n) bs -> A <= a < A + n -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)).
    { intros bs I A n a Hin Ha. exact (BEQ A n a (I _ Hin) Ha). }
    unfold c_blocks in BEQ, SEQ, LIVE.
    assert (I1 : forall b, In b (umap_blocks 24 (t3a (c_m1 c)) (t3b (c_m1 c)) (t3c (c_m1 c))) -> In b (c_blocks c)).
    { intros b Hb. unfold c_blocks. apply in_app_iff. left. exact Hb. }
    assert (I2 : forall b, In b (umap_blocks 32 (t3a (c_m2 c)) (t3b (c_m2 c)) (t3c (c_m2 c))) -> In b (c_blocks c)).
    { intros b Hb. unfold c_blocks. apply in_app_iff. right. apply in_app_iff. left. exact Hb. }
    assert (I3 : forall b, In b (umap_blocks 24 (t3a (c_m3 c)) (t3b (c_m3 c)) (t3c (c_m3 c))) -> In b (c_blocks c)).
    { intros b Hb. unfold c_blocks. do 2 (apply in_app_iff; right). apply in_app_iff. left. exact Hb. }
    assert (I4 : forall b, In b (vec_opnd_blocks (t3a (c_v1 c)) (t3c (c_v1 c))) -> In b (c_blocks c)).
    { intros b Hb. unfold c_blocks. do 3 (apply in_app_iff; right). apply in_app_iff. left. exact Hb. }
    assert (I5 : forall b, In b (if t3a (c_v2 c) =? 0 then [] else [(t3a (c_v2 c), 4 * t3c (c_v2 c))]) -> In b (c_blocks c)).
    { intros b Hb. unfold c_blocks. do 4 (apply in_app_iff; right). apply in_app_iff. left. exact Hb. }
    assert (I6 : forall b, In b (if t3a (c_v3 c) =? 0 then [] else [(t3a (c_v3 c), 4 * t3c (c_v3 c))]) -> In b (c_blocks c)).
    { intros b Hb. unfold c_blocks. do 5 (apply in_app_iff; right). apply in_app_iff. left. exact Hb. }
    fold (c_blocks c) in *.
    assert (UK : forall NS (V : Type) (nval : mem -> Z -> V -> Prop)
      (nval_agree : forall M M' p v, nval M p v -> HRepFacts.agree_on M M' (p + 20) (NS - 20) -> 0 < p -> p + NS <= 2 ^ 47 -> nval M' p v)
      (HNS : 24 <= NS) off bl bc ents,
      O_M1 <= off -> off + 40 <= PARSER_SIZE ->
      (forall b, In b (umap_blocks NS bl bc ents) -> In b (c_blocks c)) ->
      @umapx AC_A ASEGS LY_A MI_A NS V nval L m (p + off) bl bc ents ->
      @umapx AC_A ASEGS LY_A MI_A NS V nval L' m' (p + off) bl bc ents).
    { intros NS V nval nval_agree HNS off bl bc ents Ho1 Ho2 IB U.
      eapply (umapx_agree ASEGS LY_A MI_A NS V nval nval_agree HNS); [exact U | |].
      - intros a Ha. unfold umap_foot in Ha. destruct Ha as [Ha|[(Hbc & Ha)|(q & Hq & Ha)]].
        + apply HEQ. unfold O_M1, PARSER_SIZE in *. lia.
        + apply (BEQ bl (8 * bc) a); [apply IB; unfold umap_blocks; apply in_app_iff; left; destruct (Z.eqb_spec bc 0); [lia | left; reflexivity] | exact Ha].
        + apply (BEQ q NS a); [| exact Ha]. apply IB. unfold umap_blocks. apply in_app_iff. right.
          apply in_map_iff in Hq. destruct Hq as ([q' kv] & Eq & Hin). cbn in Eq. subst q'.
          apply in_map_iff. exists (q, kv). split; [reflexivity | exact Hin].
      - intros b n0 Hb Hl. apply LIVE; [apply IB; exact Hb | exact Hl]. }
    pose proof SHc as (SH1 & SH2 & SH3 & SH4 & SH5 & SH6).
    split; [apply (UK 24 Z (nval24 ASEGS) (nval24_agree ASEGS) ltac:(lia) O_M1); [unfold O_M1; lia | unfold O_M1, PARSER_SIZE; lia | exact I1 | exact U1]|].
    split; [apply (UK 32 (Z * Z * Z)%type (nval32 ASEGS) (nval32_agree ASEGS) ltac:(lia) O_M2); [unfold O_M1, O_M2; lia | unfold O_M2, PARSER_SIZE; lia | exact I2 | exact U2]|].
    split; [apply (UK 24 Z (nval24 ASEGS) (nval24_agree ASEGS) ltac:(lia) O_M3); [unfold O_M1, O_M3; lia | unfold O_M3, PARSER_SIZE; lia | exact I3 | exact U3]|].
    split.
    { eapply vec_opnd_live; [eapply vec_opnd_frame; [exact V1|] |].
      - intros a Ha. unfold vec_opnd_fp, zwin in Ha. apply HEQ. unfold O_V1, O_M1, PARSER_SIZE in *. lia.
      - intros Hb Hl. apply LIVE; [apply I4; unfold vec_opnd_blocks; destruct (Z.eqb_spec (t3a (c_v1 c)) 0); [lia | left; reflexivity] | exact Hl]. }
    split.
    { eapply vec32_live; [eapply vec32_frame; [exact V2|] |].
      - intros a Ha. unfold vec32_fp, zwin in Ha. destruct Ha as [Ha|(Hb & Ha)].
        + apply HEQ. unfold O_V2, O_M1, PARSER_SIZE in *. lia.
        + pose proof V2 as (_ & _ & _ & Hlen & _). apply (BEQ (t3a (c_v2 c)) (4 * t3c (c_v2 c)) a).
          * apply I5. destruct (Z.eqb_spec (t3a (c_v2 c)) 0); [lia | left; reflexivity].
          * unfold Zlen in *. lia.
      - intros Hb Hl. apply LIVE; [apply I5; destruct (Z.eqb_spec (t3a (c_v2 c)) 0); [lia | left; reflexivity] | exact Hl]. }
    split.
    { eapply vec32_live; [eapply vec32_frame; [exact V3|] |].
      - intros a Ha. unfold vec32_fp, zwin in Ha. destruct Ha as [Ha|(Hb & Ha)].
        + apply HEQ. unfold O_V3, O_M1, PARSER_SIZE in *. lia.
        + pose proof V3 as (_ & _ & _ & Hlen & _). apply (BEQ (t3a (c_v3 c)) (4 * t3c (c_v3 c)) a).
          * apply I6. destruct (Z.eqb_spec (t3a (c_v3 c)) 0); [lia | left; reflexivity].
          * unfold Zlen in *. lia.
      - intros Hb Hl. apply LIVE; [apply I6; destruct (Z.eqb_spec (t3a (c_v3 c)) 0); [lia | left; reflexivity] | exact Hl]. }

    destruct (c_m1 c) as [[bl1 bc1] e1] eqn:E1. destruct (c_m2 c) as [[bl2 bc2] e2] eqn:E2. destruct (c_m3 c) as [[bl3 bc3] e3] eqn:E3.
    unfold pmc_sh. rewrite E1, E2, E3. cbn [t3a t3b t3c fst snd] in *.
    assert (USH : forall NS (V : Type) bl bc (ents : list (Z * (Z * V))),
      (forall b, In b (umap_blocks NS bl bc ents) -> In b (c_blocks c)) ->
      umap_sh m NS (bl, bc, ents) -> umap_sh m' NS (bl, bc, ents)).
    { intros NS V bl bc ents IB [SB SN]. unfold umap_sh. cbn [t3a t3b t3c fst snd] in *. split.
      - intros Hbc. destruct (SB Hbc) as [Hn SH]. split; [exact Hn|].
        eapply (SEQ bl (8 * bc)); [apply IB; unfold umap_blocks; apply in_app_iff; left; destruct (Z.eqb_spec bc 0); [lia | left; reflexivity] | | exact SH].
        rewrite shadow_of_length by lia. lia.
      - intros q k v Hin. destruct (SN q k v Hin) as [Hn SH]. split; [exact Hn|].
        eapply (SEQ q NS); [| | exact SH].
        + apply IB. unfold umap_blocks. apply in_app_iff. right. apply in_map_iff. exists (q, (k, v)). split; [reflexivity | exact Hin].
        + rewrite shadow_of_length by lia. lia. }
    split; [apply (USH 24 Z); [exact I1 | exact SH1]|].
    split; [apply (USH 32 (Z * Z * Z)%type); [exact I2 | exact SH2]|].
    split; [apply (USH 24 Z); [exact I3 | exact SH3]|].
    split; [| split].
    - intros Hb. pose proof V1 as (_ & _ & _ & Hlen & _). eapply (SEQ (t3a (c_v1 c)) (OPND_SZ * t3c (c_v1 c))); [| | exact (SH4 Hb)].
      + apply I4. unfold vec_opnd_blocks. destruct (Z.eqb_spec (t3a (c_v1 c)) 0); [lia | left; reflexivity].
      + rewrite cc_gen_length by (unfold OPND_SZ; lia). lia.
    - intros Hb. pose proof V2 as (_ & _ & _ & Hlen & _). eapply (SEQ (t3a (c_v2 c)) (4 * t3c (c_v2 c))); [| | exact (SH5 Hb)].
      + apply I5. destruct (Z.eqb_spec (t3a (c_v2 c)) 0); [lia | left; reflexivity].
      + rewrite cc_gen_length by (unfold Zlen in *; lia). lia.
    - intros Hb. pose proof V3 as (_ & _ & _ & Hlen & _). eapply (SEQ (t3a (c_v3 c)) (4 * t3c (c_v3 c))); [| | exact (SH6 Hb)].
      + apply I6. destruct (Z.eqb_spec (t3a (c_v3 c)) 0); [lia | left; reflexivity].
      + rewrite cc_gen_length by (unfold Zlen in *; lia). lia.
  Qed.
End Keep.

Section XpKeep.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Variable LINV : mem -> Prop.

  Lemma xr_kept_blk : forall (w : pmwA H) s LB m LBk ftbl X XS m' pid A n a k,
    pmw_okA H w -> as_RHEAP H s LB m -> In (pid, A, n) LB -> In (pid, A, n) LBk ->
    as_RFS H (PMLF H w) m' -> Forall (fs_scratch H (PMLF H w)) XS -> Forall (xp_ok H w ftbl) X ->
    A <= a -> a + k <= A + n -> 0 <= k ->
    xclient_range H LBk (wa_s1 w) (X ++ XS) a k.
  Proof.
    intros w s LB m LBk ftbl X XS m' pid A n a k OK RH Hin Hk RFS FXS FX H1 H2 H3.
    pose proof (ah_blocks H HH _ _ _ _ RH Hin) as (R0 & R16 & Rn & RI & RC & RF & RAPP). cbn [blk_addr blk_size fst snd] in *.
    pose proof aceil_facts as ((AC1 & AC2) & _ & _).
    pose proof (blk_apart_ff H HH w s LB m _ OK RH Hin) as BF. cbn [blk_addr blk_size fst snd] in BF.
    assert (FO : fsobj H (PMLF H w) A n) by (eapply fsobj_block; [exact HH | exact RH | exact Hin]).
    pose proof (xp_scr_obj H HH w m' XS A n OK RFS FXS FO ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI in *; lia) RAPP) as [SX _].
    apply (xr_blk H w LBk (X ++ XS) (pid, A, n)); [exact Hk | cbn; lia | cbn; lia |].
    apply Forall_app. split.
    - eapply ap_X_apart; [exact FX | lia | unfold RtB_Td.ATDLOC, AIMG_TOP, AFS_HDR, PARSER_SIZE in *; lia].
    - eapply Forall_impl; [| exact SX]. intros iv Hiv. cbn beta in *. lia.
  Qed.

  Lemma xr_kept_blksh : forall (w : pmwA H) s LB m LBk ftbl X XS m' pid A n a k,
    pmw_okA H w -> as_RHEAP H s LB m -> In (pid, A, n) LB -> In (pid, A, n) LBk ->
    as_RFS H (PMLF H w) m' -> Forall (fs_scratch H (PMLF H w)) XS -> Forall (xp_ok H w ftbl) X ->
    sh A <= a -> a + k <= sh A + nsh n -> 0 <= k ->
    xclient_range H LBk (wa_s1 w) (X ++ XS) a k.
  Proof.
    intros w s LB m LBk ftbl X XS m' pid A n a k OK RH Hin Hk RFS FXS FX H1 H2 H3.
    pose proof (ah_blocks H HH _ _ _ _ RH Hin) as (R0 & R16 & Rn & RI & RC & RF & RAPP). cbn [blk_addr blk_size fst snd] in *.
    pose proof aceil_facts as ((AC1 & AC2) & _ & _).
    assert (FO : fsobj H (PMLF H w) A n) by (eapply fsobj_block; [exact HH | exact RH | exact Hin]).
    pose proof (xp_scr_obj H HH w m' XS A n OK RFS FXS FO ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI in *; lia) RAPP) as [_ SX].
    apply (xr_blksh H w LBk (X ++ XS) (pid, A, n)); [exact Hk | cbn; lia | cbn; lia |].
    apply Forall_app. split.
    - pose proof (ap_X_sh H HH w ftbl X A n OK FX ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI in *; lia)) as D.
      eapply Forall_impl; [| exact D]. intros iv Hiv. cbn beta in *. lia.
    - eapply Forall_impl; [| exact SX]. intros iv Hiv. cbn beta in *. lia.
  Qed.

  Lemma xr_parser : forall (w : pmwA H) LBk ftbl X XS m' k n,
    pmw_okA H w -> as_RFS H (PMLF H w) m' -> Forall (fs_scratch H (PMLF H w)) XS -> Forall (xp_ok H w ftbl) X ->
    0 <= k -> 0 <= n -> k + n <= PARSER_SIZE -> xclient_range H LBk (wa_s1 w) (X ++ XS) (wa_p w + k) n.
  Proof.
    intros w LBk ftbl X XS m' k n OK RFS FXS FX Hk Hn Hkn.
    pose proof aceil_facts as ((AC1 & AC2) & _ & _).
    pose proof (xp_geom H HH w OK) as (F1 & F2 & F3 & F4 & F5 & FA & (fp0 & Hfp0 & PF1 & PF2 & PF3 & PF4)).
    pose proof (wk_papp H w OK) as (PA & PA0 & PA16). pose proof (p_range H w OK) as (PR1 & PR2).
    assert (FOp : fsobj H (PMLF H w) (wa_p w) PARSER_SIZE) by (right; exists fp0; split; [right; exact Hfp0 | lia]).
    pose proof (xp_scr_obj H HH w m' XS (wa_p w) PARSER_SIZE OK RFS FXS FOp ltac:(lia) ltac:(unfold PARSER_SIZE; lia) ltac:(unfold AAPP_HI, PARSER_SIZE in *; lia) PA) as [SXp _].
    pose proof (lf0_apart_ff H w fp0 (wa_p w) PARSER_SIZE OK Hfp0 PF1 PF2) as PFF.
    apply (xr_fs H w); [exact OK | unfold PARSER_SIZE, AFS_HDR in *; lia | unfold PARSER_SIZE in *; lia |].
    apply Forall_app. split.
    - eapply ap_X_apart; [exact FX | unfold PARSER_SIZE in *; lia | unfold RtB_Td.ATDLOC, AIMG_TOP, AFS_HDR, PARSER_SIZE in *; lia].
    - eapply Forall_impl; [| exact SXp]. intros iv Hiv. cbn beta in *. unfold PARSER_SIZE in *. lia.
  Qed.

  Lemma pmc_xp_keep : forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl TB spal LB' m' LBk X XS,
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal ->
    as_RFS H (PMLF H w) m' -> Forall (fs_scratch H (PMLF H w)) XS -> xpres H LBk (wa_s1 w) (X ++ XS) m m' ->
    Forall (xp_ok H w ftbl) X -> (forall b, In b LBs -> In b LBk) -> (forall b, In b LBs -> In b LB') ->
    @umapx AC_A ASEGS LY_A MI_A 24 Z (nval24 ASEGS) (lbl LB') m' (wa_p w + O_M1) (t3a (c_m1 c)) (t3b (c_m1 c)) (t3c (c_m1 c))
    /\ @umapx AC_A ASEGS LY_A MI_A 32 (Z * Z * Z) (nval32 ASEGS) (lbl LB') m' (wa_p w + O_M2) (t3a (c_m2 c)) (t3b (c_m2 c)) (t3c (c_m2 c))
    /\ @umapx AC_A ASEGS LY_A MI_A 24 Z (nval24 ASEGS) (lbl LB') m' (wa_p w + O_M3) (t3a (c_m3 c)) (t3b (c_m3 c)) (t3c (c_m3 c))
    /\ @vec_opnd AC_A ASEGS LY_A MI_A (lbl LB') m' (wa_p w + O_V1) (t3a (c_v1 c)) (t3b (c_v1 c)) (t3c (c_v1 c))
    /\ @vec32 AC_A ASEGS LY_A MI_A (lbl LB') m' (wa_p w + O_V2) (t3a (c_v2 c)) (t3b (c_v2 c)) (t3c (c_v2 c))
    /\ @vec32 AC_A ASEGS LY_A MI_A (lbl LB') m' (wa_p w + O_V3) (t3a (c_v3 c)) (t3b (c_v3 c)) (t3c (c_v3 c))
    /\ pmc_sh m' c.
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal LB' m' LBk X XS OK X0 RFS FXS XP FX KEEP LIVE'.
    pose proof (pmw_bounds H w OK) as BND.
    pose proof (xa_rheap _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as RH.
    pose proof (xa_own _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as [OWN1 OWN2].
    assert (BLK : forall A n, In (A, n) (c_blocks c) -> exists pid, In (pid, A, n) LBs /\ In (pid, A, n) LB).
    { intros A n Hin. apply (Permutation_in _ (Permutation_sym OWN2)) in Hin. destruct (lbl_in_inv LBs A n Hin) as [pid Hp].
      exists pid. split; [exact Hp|]. apply (Permutation_in _ (Permutation_sym OWN1)). apply in_app_iff. right. apply in_app_iff. left. exact Hp. }
    apply (pmc_keep_gen (wa_p w) (lbl LB) (lbl LB') m m' c
             (xa_m1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) (xa_m2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) (xa_m3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0)
             (xa_v1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) (xa_v2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) (xa_v3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0)
             (proj1 (xa_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0)));
      [lia | pose proof (p_range H w OK) as [_ PR2]; pose proof aceil_facts as ((AC1 & AC2) & _ & _); unfold PARSER_SIZE in *; lia | | | |].
    - intros a Ha.
      assert (XC : xclient H LBk (wa_s1 w) (X ++ XS) a).
      { eapply (xclient_range_addr H); [apply (xr_parser w LBk ftbl X XS m' (a - wa_p w) 1 OK RFS FXS FX); unfold O_M1, PARSER_SIZE in *; lia | lia]. }
      exact (proj1 (XP a ltac:(unfold O_M1, PARSER_SIZE in *; lia) XC)).
    - intros A n a Hin Ha. destruct (BLK A n Hin) as (pid & Hs & Hl).
      pose proof (ah_blocks H HH _ _ _ _ RH Hl) as (R0 & R16 & Rn & RI & RC & RF & RAPP). cbn [blk_addr blk_size fst snd] in *.
      pose proof aceil_facts as ((AC1 & AC2) & _ & _).
      assert (XC : xclient H LBk (wa_s1 w) (X ++ XS) a).
      { eapply (xclient_range_addr H); [apply (xr_kept_blk w s LB m LBk ftbl X XS m' pid A n a 1 OK RH Hl (KEEP _ Hs) RFS FXS FX); lia | lia]. }
      exact (proj1 (XP a ltac:(lia) XC)).
    - intros A n sbs Hin Hlen SH. destruct (BLK A n Hin) as (pid & Hs & Hl).
      eapply (xpres_SHAD H); [exact XP | exact SH |].
      apply (xr_kept_blksh w s LB m LBk ftbl X XS m' pid A n (sh A) _ OK RH Hl (KEEP _ Hs) RFS FXS FX); lia.
    - intros b Hb _. destruct b as [A n]. destruct (BLK A n Hb) as (pid & Hs & Hl). apply (lbl_in LB' pid). exact (LIVE' _ Hs).
  Qed.
End XpKeep.
