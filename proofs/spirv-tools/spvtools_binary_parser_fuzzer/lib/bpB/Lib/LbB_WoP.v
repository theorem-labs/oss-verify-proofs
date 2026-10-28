(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 BsWalk RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_PrsStmt LbB_SR LbB_Conv LbB_MILB LbB_Own LbB_RtOwn LbB_ContStmt LbB_ResvB.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require LbB_ContV4 LbB_DRep LbB_RvOC LbB_RvWC.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_WoDefs LbB_WoKit LbB_WoKit3 LbB_WoSt LbB_WoCut LbB_WoVec.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_WoR3 LbB_WoR4 LbB_WoE0 LbB_WoE0b.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.



Lemma wp_reshape : forall m A cs1 cs2, cells_bytes cs1 = cells_bytes cs2 -> cells_size cs1 = cells_size cs2 -> cells_wf cs2 ->
  rw_cells asegs m A cs1 -> rw_cells asegs m A cs2.
Proof.
  intros m A cs1 cs2 EB ES WF [[_ B] W]. split; [split; [exact WF | rewrite <- EB; exact B] | rewrite <- ES; exact W].
Qed.

Lemma wp_z24 : forall m A, rw_cells asegs m A Z24 ->
  rw_cells asegs m A [C8 (Z_to_bv 64 0)] /\ rw_cells asegs m (A + 8) [C8 (Z_to_bv 64 0)] /\ rw_cells asegs m (A + 16) [C8 (Z_to_bv 64 0)].
Proof.
  intros m A Z.
  assert (R : rw_cells asegs m A [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]).
  { apply (wp_reshape m A Z24); [vm_compute; reflexivity | reflexivity | cbn; tauto | exact Z]. }
  apply (rw_cells_app asegs m A [C8 (Z_to_bv 64 0)] [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) in R as [R0 R].
  apply (rw_cells_app asegs m _ [C8 (Z_to_bv 64 0)] [C8 (Z_to_bv 64 0)]) in R as [R1 R2].
  cbn [cells_size csize] in R1, R2. change (Z.of_nat (8 + 0)) with 8 in R1, R2.
  replace (A + 8 + 8) with (A + 16) in R2 by lia.
  split; [exact R0 | split; [exact R1 | exact R2]].
Qed.

Lemma wp_wr_sub : forall m A n o k, wr_at asegs m A n -> 0 <= o -> 0 <= k -> o + k <= n -> wr_at asegs m (A + o) k.
Proof.
  intros m A n o k (W0 & W1 & W) Ho Hk Hn. split; [lia|]. split; [lia|]. intros i Hi.
  replace (A + o + i) with (A + (o + i)) by lia. apply W. lia.
Qed.

Lemma wp_vtrip : forall m v b k, CRep.fld ASEGS m v 8 b -> CRep.fld ASEGS m (v + 8) 8 b -> CRep.fld ASEGS m (v + 16) 8 (b + k) ->
  wr_at asegs m v 24 -> rw_cells asegs m v (vtrip b k).
Proof.
  intros m v b k F0 F1 F2 W. unfold vtrip.
  assert (W0 : wr_at asegs m v 8) by (pose proof (wp_wr_sub m v 24 0 8 W) as X; rewrite Z.add_0_r in X; apply X; lia).
  apply rw_cells_cons8_c; [exact (LbB_DRep.rw_cells_of_fld8 m v b F0 W0)|].
  apply rw_cells_cons8_c; [exact (LbB_DRep.rw_cells_of_fld8 m (v + 8) b F1 (wp_wr_sub m v 24 8 8 W ltac:(lia) ltac:(lia) ltac:(lia)))|].
  replace (v + 8 + 8) with (v + 16) by lia.
  exact (LbB_DRep.rw_cells_of_fld8 m (v + 16) (b + k) F2 (wp_wr_sub m v 24 16 8 W ltac:(lia) ltac:(lia) ltac:(lia))).
Qed.

Section WoP.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHb : asan_rt_hyps_bp H.
  Let HB := rt_bp_base H HHb.
  Hypothesis HOWN : rt_own H.
  Hypothesis WTR : po_tr_ok H.

  Lemma wp_tr : forall r, In r RESV_DEL_RAS -> trace_ok (as_TR H) APC0_FREE [r].
  Proof.
    intros r Hr. destruct WTR as [_ W]. rewrite Forall_forall in W. apply W.
    apply in_app_iff. right. apply in_app_iff. right. exact Hr.
  Qed.

  Lemma wp_cells_x : forall LB SP X m m' A cs, xpres H LB SP X m m' -> rw_cells asegs m A cs ->
    as_FSB H <= A -> A + Z.of_nat (cells_size cs) <= as_FSB H + AFS_SIZE ->
    Forall (fun iv : Z * Z => A + Z.of_nat (cells_size cs) <= fst iv \/ snd iv <= A) X -> rw_cells asegs m' A cs.
  Proof.
    intros LB SP X m m' A cs XP C L1 L2 D. eapply xpres_rw_cells; [exact XP | exact C |].
    unfold xclient_range. split; [|exact D]. unfold aclient_range. right; right; right; right; left. lia.
  Qed.

  Lemma wp_pst_x : forall LB SP X m m' ff, xpres H LB SP X m m' ->
    as_FSB H <= ff -> ff + 4096 <= as_FSB H + AFS_SIZE ->
    Forall (fun iv : Z * Z => ff + 3668 <= fst iv \/ snd iv <= ff + 3504) X ->
    rw_cells asegs m (ff + 3504) [CB 46 (poison_bytes 46 0)] -> st_maps_cells m (ff + 3504) ->
    rw_cells asegs m' (ff + 3504) [CB 46 (poison_bytes 46 0)] /\ st_maps_cells m' (ff + 3504).
  Proof.
    intros LB SP X m m' ff XP L1 L2 D C0 (C1 & C2 & C3 & C4 & C5 & C6).
    assert (K : forall A cs, rw_cells asegs m A cs -> ff + 3504 <= A -> A + Z.of_nat (cells_size cs) <= ff + 3668 -> rw_cells asegs m' A cs).
    { intros A cs C Ha Hb. eapply (wp_cells_x LB SP X m m' A cs XP C); [lia | lia |].
      eapply Forall_impl; [| exact D]. intros iv Hiv. cbn in Hiv. lia. }
    split; [apply K; [exact C0 | lia | cbn; lia]|].
    unfold st_maps_cells. do 5 (split; [apply K; [assumption | lia | cbn; lia]|]). apply K; [assumption | lia | cbn; lia].
  Qed.

  Definition wp1_pre (e : went H) (ff : Z) (m : mem) (x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) : machine_state :=
    MS (mkR (Z_to_bv 64 WO_ON1_RA) (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) x5 x6 x7 (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
            (Z_to_bv 64 (ff + 3672)) (Z_to_bv 64 25) x12 x13 x14 x15 x16 x17
            (Z_to_bv 64 (ff + 3456)) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) (Z_to_bv 64 (ff + 3720)) (Z_to_bv 64 (ff + 3504))
            (Z_to_bv 64 0x3f800000) (Z_to_bv 64 0) (Z_to_bv 64 (ff + 3672)) (Z_to_bv 64 (ff + 3696)) (Z_to_bv 64 (ff + 2752))
            x28 x29 x30 x31)
       (w_F e) (Z_to_bv 64 RESV_OPND_ENTRY) (w_fc e) None m (seg_rom asegs).

  Definition wp2_pre (e : went H) (ff : Z) (m : mem) (x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) : machine_state :=
    MS (mkR (Z_to_bv 64 WO_AN2_RA) (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) x5 x6 x7 (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
            (Z_to_bv 64 (ff + 3696)) (Z_to_bv 64 25) x12 x13 x14 x15 x16 x17
            (Z_to_bv 64 (ff + 3456)) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) (Z_to_bv 64 (ff + 3720)) (Z_to_bv 64 (ff + 3504))
            (Z_to_bv 64 0x3f800000) (Z_to_bv 64 0) (Z_to_bv 64 (ff + 3672)) (Z_to_bv 64 (ff + 3696)) (Z_to_bv 64 (ff + 2752))
            x28 x29 x30 x31)
       (w_F e) (Z_to_bv 64 (rv_entry RESV_W32)) (w_fc e) None m (seg_rom asegs).

  Definition wp3_pre (e : went H) (ff : Z) (m : mem) (x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) : machine_state :=
    MS (mkR (Z_to_bv 64 WO_AN3_RA) (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) x5 x6 x7 (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
            (Z_to_bv 64 (ff + 3720)) (Z_to_bv 64 25) x12 x13 x14 x15 x16 x17
            (Z_to_bv 64 (ff + 3456)) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) (Z_to_bv 64 (ff + 3720)) (Z_to_bv 64 (ff + 3504))
            (Z_to_bv 64 0x3f800000) (Z_to_bv 64 0) (Z_to_bv 64 (ff + 3672)) (Z_to_bv 64 (ff + 3696)) (Z_to_bv 64 (ff + 2752))
            x28 x29 x30 x31)
       (w_F e) (Z_to_bv 64 (rv_entry RESV_TYP)) (w_fc e) None m (seg_rom asegs).

  Definition wp1_post (e : went H) (ff fp : Z) (sk : as_St H) (LBk : list block) (mo : Model) : config -> Prop :=
    fun cf => exists (s' : as_St H) (p : bptr) (b : Z) (x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (m' : mem),
      as_VIS H s' (cfg_ms cf) = wp2_pre e ff m' x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31
      /\ as_AKREL H s' cf /\ as_MPRES H mo (cfg_model cf) /\ as_AL H s' >= as_AL H sk
      /\ ~ In p (map blk_id LBk) /\ ablock_range H b 500
      /\ winv H e ff fp [] s' ((p, b, 500) :: LBk) m' /\ wfc H e ff m'
      /\ wpst ff m' (vtrip b 500) Z24 Z24 /\ wblk m' b 500.

  Definition wp2_post (e : went H) (ff fp : Z) (sk : as_St H) (LBk : list block) (b : Z) (mo : Model) : config -> Prop :=
    fun cf => exists (s' : as_St H) (q : bptr) (c : Z) (x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (m' : mem),
      as_VIS H s' (cfg_ms cf) = wp3_pre e ff m' x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31
      /\ as_AKREL H s' cf /\ as_MPRES H mo (cfg_model cf) /\ as_AL H s' >= as_AL H sk
      /\ ~ In q (map blk_id LBk) /\ ablock_range H c 100
      /\ winv H e ff fp [] s' ((q, c, 100) :: LBk) m' /\ wfc H e ff m'
      /\ wpst ff m' (vtrip b 500) (vtrip c 100) Z24 /\ wblk m' b 500 /\ wblk m' c 100.

  Ltac wp_geo e ff HP HI :=
    pose proof (wpre_geo H e HP) as (CE & LO & SSHI & SHIH & SP16 & TP);
    pose proof (wS1_facts H e HP) as (S32 & S1SP & S1L & SPH & LOS1 & _);
    pose proof aceil_facts as ACF;
    pose proof HI as (RF & FF & RH & AC & MI & S0 & RA & (errv & ER) & ST & SV & SF & WF & WFP & XP & FS & LVI);
    pose proof (wframe_facts H _ _ _ FF) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16);
    assert (FAPP : ff + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= ff)
      by (unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO, AIMG_TOP in F10; destruct F10 as [[X Y]|[X Y]]; [left | right]; lia);
    assert (FSH : sh ff + 512 <= ff \/ ff + 4096 <= sh ff)
      by (destruct FAPP as [X|X];
          [ right; assert (0x7fff8000 <= sh ff) by lia; lia
          | left; unfold sh in *; rewrite ASHADOW_BASE_val in *; clear - X; Z.div_mod_to_equations; lia ]).

  Lemma wp_obj : forall (e : went H) ff fp LB v, wpre H e -> fresh_frame H (w_LF e) 6 ff fp ->
    ff + 3456 <= v -> v + 24 <= ff + 3744 -> v mod 8 = 0 ->
    obj_win H LB ((6, ff, fp) :: w_LF e) (wS1 e) (w_lo e) v 24
    /\ ((0x6e8000 <= v /\ v + 24 <= 0x7fff7000) \/ (0x10007fff8000 <= v /\ v + 24 <= 2 ^ 47)).
  Proof.
    intros e ff fp LB v HP FF V1 V2 V8.
    pose proof (wpre_geo H e HP) as (CE & LO & SSHI & SHIH & SP16 & TP).
    pose proof (wS1_facts H e HP) as (S32 & S1SP & S1L & SPH & LOS1 & _).
    pose proof aceil_facts as ACF.
    pose proof (wframe_facts H _ _ _ FF) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16).
    assert (FAPP : ff + 4096 <= 0x7fff7000 \/ 0x10007fff8000 <= ff)
      by (unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO, AIMG_TOP in F10; destruct F10 as [[X Y]|[X Y]]; [left | right]; lia).
    destruct (wwin_ok H e ff fp [] (v, v + 24) FF CE ltac:(unfold WO_SAVED; lia) ltac:(unfold AAPP_HI in *; lia)
                ltac:(unfold wwin, WO_FLAGP; cbn [fst snd]; right; left; lia)) as (W1 & W2 & W3 & _).
    assert (SHV : sh v + 3 <= sh (ff + 4096) /\ sh ff <= sh v) by (unfold sh; clear - V1 V2 F3; Z.div_mod_to_equations; lia).
    split; [|destruct FAPP; [left | right]; unfold AAPP_HI in *; lia].
    unfold obj_win. split; [unfold aclient_range; right; right; right; right; left; lia|].
    split; [unfold aclient_range; right; right; right; right; right; left; change (nsh 24) with 3; lia|].
    split; [exact (W2 LB)|]. split; [exact W1|]. split; [exact W3|]. left. lia.
  Qed.

  Lemma wp1 : forall (e : went H) ff fp sk LBk m msF mo (x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    wpre H e -> winv H e ff fp [] sk LBk m -> (forall bb, In bb (w_LB e) -> In bb LBk) ->
    wfc H e ff m -> wpst ff m Z24 Z24 Z24 ->
    as_VIS H sk msF = wp1_pre e ff m x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 -> as_AKREL H sk (mkCfg msF mo) ->
    0 <= as_AL H sk -> lb_small LBk + 500 <= RT_SMALL_MAX -> Z.of_nat (length LBk) + 1 <= RT_CNT_MAX -> nlarge LBk <= RT_LARGE_MAX ->
    as_SR H (wp1_post e ff fp sk LBk mo) (mkCfg msF mo).
  Proof.
    intros e ff fp sk LBk m msF mo x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 HP HI INC WC PS VIS KR AL0 BS BC BL.
    assert (TRO : trace_ok (as_TR H) APC0_FREE [RESV_OPND_DEL_RA]) by (apply wp_tr; unfold RESV_DEL_RAS; cbn [In]; left; reflexivity).
    wp_geo e ff HP HI.
    pose proof WC as (_ & _ & _ & _ & _ & USH & _).
    destruct PS as (PS0 & PSM & PV1 & PV2 & PV3).
    destruct (wp_z24 m _ PV1) as (Z0 & Z1 & Z2).
    destruct (wp_obj e ff fp LBk (ff + 3672) HP FF ltac:(lia) ltac:(lia) ltac:(clear - F3; Z.div_mod_to_equations; lia)) as (OW & RNG).
    assert (AD : addressable m (ff + 3672) 24).
    { pose proof (wo_pad m ff USH F3 ltac:(lia)) as AP. replace (ff + 3672) with (ff + 3456 + 216) by lia.
      apply (addressable_sub8 m (ff + 3456) 288 216 24 AP); first [reflexivity | lia]. }
    assert (WV : wr_at asegs m (ff + 3672) 24).
    { replace (ff + 3672) with (ff + 3672) by reflexivity. apply (wp_wr_sub m ff WO_FLAGP 3672 24 WF); unfold WO_FLAGP; lia. }
    destruct (rt_bp_cost H HHb) as [CFc CMc].
    pose proof (LbB_RvOC.resv_opnd_ok H HB) as RO. unfold resv_opnd_stmt in RO.
    unfold wp1_pre in VIS.
    assert (US1 : bv_unsigned (Z_to_bv 64 (wS1 e)) = wS1 e) by (apply HLib.u64_of_Z; lia).
    assert (URA : bv_unsigned (Z_to_bv 64 WO_ON1_RA) = WO_ON1_RA) by (apply HLib.u64_of_Z; unfold WO_ON1_RA; lia).
    eapply (ah_seq H HB).
    { eapply RO with (v := ff + 3672) (b := 0) (n := 0) (cap := 0) (k := 25) (pid := 0) (LB := LBk) (LBo := LBk) (LF := (6, ff, fp) :: w_LF e)
                     (lo := w_lo e) (B := w_B e) (shi := w_shi e) (errv := errv); [exact VIS | ..].
      all: rewrite ?US1, ?URA.
      - reflexivity.
      - reflexivity.
      - unfold vopndA, CRep.vec_opnd.
        split; [lia|]. split; [lia|].
        split; [exact (LbB_ContV4.mdef_of_rw_cells_hi m _ Z24 PV1 ltac:(unfold AIMG_TOP; lia))|].
        split; [lia|]. split; [left; split; reflexivity|].
        split; [exact (LbB_ContV4.fld_of_rw_cells8 m _ 0 Z0 ltac:(lia))|].
        split; [exact (LbB_ContV4.fld_of_rw_cells8 m _ 0 Z1 ltac:(lia)) | exact (LbB_ContV4.fld_of_rw_cells8 m _ 0 Z2 ltac:(lia))].
      - clear - F3. Z.div_mod_to_equations. lia.
      - exact AD.
      - exact OW.
      - exact RNG.
      - exact WV.
      - exact (HOWN _ _ _ RH).
      - intros bb Hb; exact Hb.
      - exact (ah_nodup H HB _ _ _ RH).
      - left. split; reflexivity.
      - intros X. lia.
      - lia.
      - unfold CRep.OPND_SZ. lia.
      - exact RH.
      - exact KR.
      - intros _. split.
        + apply (rt_bp_live H HHb _ _ _ _ RH); [unfold CRep.OPND_SZ; lia | change (nsmall (CRep.OPND_SZ * 25)) with 500; lia | lia
                                               | change (nlg (CRep.OPND_SZ * 25)) with 0; lia].
        + rewrite CFc, CMc. change (ICM (CRep.OPND_SZ * 25)) with 0. lia.
      - exact TRO.
      - exact RA.
      - pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & SPB & _). lia.
      - clear - S32. Z.div_mod_to_equations. lia.
      - lia.
      - exact (proj1 (stk_split asegs m (w_lo e) (wS1 e) (wSP e) ST ltac:(lia))).
      - exact CE.
      - unfold RESV_STACK, AOPNEW_STACK, AMALLOC_STACK. lia.
      - exact ER.
      - exact MI.
      - exact TP.
      - unfold WO_ON1_RA. reflexivity.
      - exact AC.
      - exact RF.
      - exact S0.
      - lia. }
    intros c2 POST. destruct c2 as [msF2 mo2].
    unfold resv_opnd_post in POST.
    destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & errv' & s' & pid' & b' & cap' & POST).
    cbv zeta in POST.
    replace (if 25 <=? 0 then LBk else v4_newLB H LBk 0 0 pid' b' (CRep.OPND_SZ * 25)) with ((pid', b', 500) :: LBk) in POST by reflexivity.
    destruct POST as (VIS2 & KR2 & MP2 & MI2 & ST2 & ER2 & RA2 & XP2 & _ & NEW & RH2 & VO2 & AD2 & WV2 & OW2 & RF2 & AC2 & S02).
    destruct (NEW ltac:(lia)) as (EC & ABR & SHB & AL2). subst cap'.
    cbn [cfg_ms cfg_model] in VIS2, MP2.
    rewrite HLib.u64_of_Z in ST2, XP2 by lia.
    replace ((ff + 3672, ff + 3672 + 24) :: v4_oldx 0 (CRep.OPND_SZ * 0)) with [(ff + 3672, ff + 3672 + 24)] in XP2 by reflexivity.
    rewrite (ret_pc_even WO_ON1_RA ltac:(unfold WO_ON1_RA; lia) eq_refl) in VIS2.
    rewrite CFc, CMc in AL2. change (ICM (CRep.OPND_SZ * 25)) with 0 in AL2. change (CRep.OPND_SZ * 25) with 500 in ABR, SHB.
    change (CRep.OPND_SZ * 0) with 0 in SHB.
    unfold vopndA, CRep.vec_opnd in VO2. destruct VO2 as (_ & _ & _ & _ & _ & FL0 & FL1 & FL2).
    change (b' + CRep.OPND_SZ * 0) with (b' + 0) in FL1. rewrite Z.add_0_r in FL1. change (CRep.OPND_SZ * 25) with 500 in FL2.
    assert (NI : ~ In pid' (map blk_id LBk)).
    { pose proof (ah_nodup H HB _ _ _ RH2) as ND. cbn [map blk_id fst] in ND. inversion ND. assumption. }
    assert (HI2 : winv H e ff fp [] s' ((pid', b', 500) :: LBk) m').
    { change (@nil (Z * Z)) with (@nil (Z * Z) ++ @nil (Z * Z)).
      eapply (winv_sr H HB e ff fp [] [] [(ff + 3672, ff + 3672 + 24)] sk LBk LBk s' ((pid', b', 500) :: LBk) m m' HP HI INC XP2);
        [apply Forall_nil | | exact RF2 | exact RH2 | exact AC2 | exact MI2 | exact ST2 | exists errv'; exact ER2 | exact RA2 |].
      - apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. right; left. unfold WO_FLAGP. lia.
      - apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. intros _. replace (ff + 3672 + 24 - (ff + 3672)) with 24 by lia. exact WV2. }
    assert (WC2 : wfc H e ff m').
    { eapply (wfc_xpres H e ff fp LBk _ m m' HP FF WC XP2). apply Forall_cons; [|apply Forall_nil].
      unfold wfc_apart. cbn [fst snd]. unfold AFS_SIZE in *. lia. }
    assert (DX : forall A n, ff <= A -> A + n <= ff + 3672 \/ ff + 3696 <= A -> A + n <= ff + 4096 ->
               Forall (fun iv : Z * Z => A + n <= fst iv \/ snd iv <= A) [(ff + 3672, ff + 3672 + 24)]).
    { intros A n X1 X2 X3. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. lia. }
    destruct (wp_pst_x LBk (wS1 e) _ m m' ff XP2 ltac:(lia) ltac:(lia)
                ltac:(apply Forall_cons; [|apply Forall_nil]; cbn [fst snd]; lia) PS0 PSM) as (PS0' & PSM').
    assert (PV2' : rw_cells asegs m' (ff + 3696) Z24)
      by (eapply (wp_cells_x LBk (wS1 e) _ m m' _ Z24 XP2 PV2); cbn; [lia | lia | apply DX; lia]).
    assert (PV3' : rw_cells asegs m' (ff + 3720) Z24)
      by (eapply (wp_cells_x LBk (wS1 e) _ m m' _ Z24 XP2 PV3); cbn; [lia | lia | apply DX; lia]).
    assert (PV1' : rw_cells asegs m' (ff + 3672) (vtrip b' 500)) by exact (wp_vtrip m' _ b' 500 FL0 FL1 FL2 WV2).
    assert (WB : wblk m' b' 500).
    { split; [|exact SHB]. exact (lb_own_In _ _ (pid', b', 500) OW2 (or_introl eq_refl)). }
    eapply (ahh_evt_then H HB _ _ s' msF2 _ mo2 KR2 VIS2).
    { apply we1c. }
    intros msF3 mo3 KR3 MP3 P3. unfold we1c_post in P3.
    apply (ah_done H HB).
    exists s', pid', b', t0', t1', t2', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    split; [exact P3|]. split; [exact KR3|]. split; [exact (ah_mpres_trans H HB _ _ _ MP2 MP3)|].
    split; [lia|]. split; [exact NI|]. split; [exact ABR|]. split; [exact HI2|]. split; [exact WC2|].
    split; [|exact WB]. split; [exact PS0'|]. split; [exact PSM'|]. split; [exact PV1'|]. split; [exact PV2' | exact PV3'].
  Qed.

  Lemma wp2 : forall (e : went H) ff fp sk LBk (p : bptr) b m msF mo (x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    wpre H e -> winv H e ff fp [] sk LBk m -> (forall bb, In bb (w_LB e) -> In bb LBk) -> In (p, b, 500) LBk ->
    wfc H e ff m -> wpst ff m (vtrip b 500) Z24 Z24 -> wblk m b 500 ->
    as_VIS H sk msF = wp2_pre e ff m x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 -> as_AKREL H sk (mkCfg msF mo) ->
    0 <= as_AL H sk -> lb_small LBk + 100 <= RT_SMALL_MAX -> Z.of_nat (length LBk) + 1 <= RT_CNT_MAX -> nlarge LBk <= RT_LARGE_MAX ->
    as_SR H (wp2_post e ff fp sk LBk b mo) (mkCfg msF mo).
  Proof.
    intros e ff fp sk LBk p b m msF mo x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 HP HI INC INB WC PS WBb VIS KR AL0 BS BC BL.
    assert (TRO : trace_ok (as_TR H) APC0_FREE [rv_del_ra RESV_W32]) by (apply wp_tr; unfold RESV_DEL_RAS; cbn [In]; right; left; reflexivity).
    wp_geo e ff HP HI.
    pose proof WC as (_ & _ & _ & _ & _ & USH & _).
    destruct PS as (PS0 & PSM & PV1 & PV2 & PV3).
    destruct (wp_z24 m _ PV2) as (Z0 & Z1 & Z2).
    destruct (wp_obj e ff fp LBk (ff + 3696) HP FF ltac:(lia) ltac:(lia) ltac:(clear - F3; Z.div_mod_to_equations; lia)) as (OW & RNG).
    assert (AD : addressable m (ff + 3696) 24).
    { pose proof (wo_pad m ff USH F3 ltac:(lia)) as AP. replace (ff + 3696) with (ff + 3456 + 240) by lia.
      apply (addressable_sub8 m (ff + 3456) 288 240 24 AP); first [reflexivity | lia]. }
    assert (WV : wr_at asegs m (ff + 3696) 24) by (apply (wp_wr_sub m ff WO_FLAGP 3696 24 WF); unfold WO_FLAGP; lia).
    pose proof (ah_blocks H HB _ _ _ _ RH INB) as ABb. cbn [blk_addr blk_size fst snd] in ABb.
    destruct (rt_bp_cost H HHb) as [CFc CMc].
    pose proof (LbB_RvWC.resv_w32_ok H HB) as RW. unfold resv32_stmt in RW.
    unfold wp2_pre in VIS.
    assert (US1 : bv_unsigned (Z_to_bv 64 (wS1 e)) = wS1 e) by (apply HLib.u64_of_Z; lia).
    assert (URA : bv_unsigned (Z_to_bv 64 WO_AN2_RA) = WO_AN2_RA) by (apply HLib.u64_of_Z; unfold WO_AN2_RA; lia).
    eapply (ah_seq H HB).
    { eapply RW with (v := ff + 3696) (b := 0) (xs := []) (cap := 0) (k := 25) (pid := 0) (LB := LBk) (LBo := LBk) (LF := (6, ff, fp) :: w_LF e)
                     (lo := w_lo e) (B := w_B e) (shi := w_shi e) (errv := errv); [exact VIS | ..].
      all: rewrite ?US1, ?URA.
      - reflexivity.
      - reflexivity.
      - unfold vec32A, CRep.vec32.
        split; [lia|]. split; [lia|].
        split; [exact (LbB_ContV4.mdef_of_rw_cells_hi m _ Z24 PV2 ltac:(unfold AIMG_TOP; lia))|].
        split; [change (CRep.Zlen (@nil Z)) with 0; lia|]. split; [left; split; reflexivity|].
        split; [exact (LbB_ContV4.fld_of_rw_cells8 m _ 0 Z0 ltac:(lia))|].
        split; [exact (LbB_ContV4.fld_of_rw_cells8 m _ 0 Z1 ltac:(lia))|].
        split; [exact (LbB_ContV4.fld_of_rw_cells8 m _ 0 Z2 ltac:(lia))|].
        intros i Hi. change (CRep.Zlen (@nil Z)) with 0 in Hi. lia.
      - clear - F3. Z.div_mod_to_equations. lia.
      - exact AD.
      - exact OW.
      - exact RNG.
      - exact WV.
      - exact (HOWN _ _ _ RH).
      - intros bb Hb; exact Hb.
      - exact (ah_nodup H HB _ _ _ RH).
      - left. split; reflexivity.
      - intros X. lia.
      - lia.
      - lia.
      - exact RH.
      - exact KR.
      - intros _. split.
        + apply (rt_bp_live H HHb _ _ _ _ RH); [lia | change (nsmall (4 * 25)) with 100; lia | lia | change (nlg (4 * 25)) with 0; lia].
        + rewrite CFc, CMc. change (ICM (4 * 25)) with 0. lia.
      - exact TRO.
      - exact RA.
      - pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & SPB & _). lia.
      - clear - S32. Z.div_mod_to_equations. lia.
      - lia.
      - exact (proj1 (stk_split asegs m (w_lo e) (wS1 e) (wSP e) ST ltac:(lia))).
      - exact CE.
      - unfold RESV_STACK, AOPNEW_STACK, AMALLOC_STACK. lia.
      - exact ER.
      - exact MI.
      - exact TP.
      - unfold WO_AN2_RA. reflexivity.
      - exact AC.
      - exact RF.
      - exact S0.
      - lia. }
    intros c2 POST. destruct c2 as [msF2 mo2].
    unfold resv32_post in POST.
    destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & errv' & s' & pid' & c' & cap' & POST).
    cbv zeta in POST.
    replace (if 25 <=? 0 then LBk else v4_newLB H LBk 0 0 pid' c' (4 * 25)) with ((pid', c', 100) :: LBk) in POST by reflexivity.
    destruct POST as (VIS2 & KR2 & MP2 & MI2 & ST2 & ER2 & RA2 & XP2 & _ & NEW & RH2 & VO2 & AD2 & WV2 & OW2 & RF2 & AC2 & S02).
    destruct (NEW ltac:(lia)) as (EC & ABR & SHB & AL2). subst cap'.
    cbn [cfg_ms cfg_model] in VIS2, MP2.
    rewrite HLib.u64_of_Z in ST2, XP2 by lia.
    replace ((ff + 3696, ff + 3696 + 24) :: v4_oldx 0 (4 * 0)) with [(ff + 3696, ff + 3696 + 24)] in XP2 by reflexivity.
    rewrite (ret_pc_even WO_AN2_RA ltac:(unfold WO_AN2_RA; lia) eq_refl) in VIS2.
    rewrite CFc, CMc in AL2. change (ICM (4 * 25)) with 0 in AL2. change (4 * 25) with 100 in ABR, SHB.
    change (4 * CRep.Zlen (@nil Z)) with 0 in SHB.
    unfold vec32A, CRep.vec32 in VO2. destruct VO2 as (_ & _ & _ & _ & _ & FL0 & FL1 & FL2 & _).
    change (c' + 4 * CRep.Zlen (@nil Z)) with (c' + 0) in FL1. rewrite Z.add_0_r in FL1. change (4 * 25) with 100 in FL2.
    assert (NI : ~ In pid' (map blk_id LBk)).
    { pose proof (ah_nodup H HB _ _ _ RH2) as ND. cbn [map blk_id fst] in ND. inversion ND. assumption. }
    assert (HI2 : winv H e ff fp [] s' ((pid', c', 100) :: LBk) m').
    { change (@nil (Z * Z)) with (@nil (Z * Z) ++ @nil (Z * Z)).
      eapply (winv_sr H HB e ff fp [] [] [(ff + 3696, ff + 3696 + 24)] sk LBk LBk s' ((pid', c', 100) :: LBk) m m' HP HI INC XP2);
        [apply Forall_nil | | exact RF2 | exact RH2 | exact AC2 | exact MI2 | exact ST2 | exists errv'; exact ER2 | exact RA2 |].
      - apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. right; left. unfold WO_FLAGP. lia.
      - apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. intros _. replace (ff + 3696 + 24 - (ff + 3696)) with 24 by lia. exact WV2. }
    assert (WC2 : wfc H e ff m').
    { eapply (wfc_xpres H e ff fp LBk _ m m' HP FF WC XP2). apply Forall_cons; [|apply Forall_nil].
      unfold wfc_apart. cbn [fst snd]. unfold AFS_SIZE in *. lia. }
    assert (DX : forall A n, ff <= A -> A + n <= ff + 3696 \/ ff + 3720 <= A -> A + n <= ff + 4096 ->
               Forall (fun iv : Z * Z => A + n <= fst iv \/ snd iv <= A) [(ff + 3696, ff + 3696 + 24)]).
    { intros A n X1 X2 X3. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. lia. }
    destruct (wp_pst_x LBk (wS1 e) _ m m' ff XP2 ltac:(lia) ltac:(lia)
                ltac:(apply Forall_cons; [|apply Forall_nil]; cbn [fst snd]; lia) PS0 PSM) as (PS0' & PSM').
    assert (PV1' : rw_cells asegs m' (ff + 3672) (vtrip b 500))
      by (eapply (wp_cells_x LBk (wS1 e) _ m m' _ (vtrip b 500) XP2 PV1); cbn; [lia | lia | apply DX; lia]).
    assert (PV3' : rw_cells asegs m' (ff + 3720) Z24)
      by (eapply (wp_cells_x LBk (wS1 e) _ m m' _ Z24 XP2 PV3); cbn; [lia | lia | apply DX; lia]).
    assert (PV2' : rw_cells asegs m' (ff + 3696) (vtrip c' 100)) by exact (wp_vtrip m' _ c' 100 FL0 FL1 FL2 WV2).
    assert (WC' : wblk m' c' 100).
    { split; [|exact SHB]. exact (lb_own_In _ _ (pid', c', 100) OW2 (or_introl eq_refl)). }
    assert (WB' : wblk m' b 500).
    { destruct WBb as (_ & (SB0 & SB8 & SBU)).
      split; [exact (lb_own_In _ _ (p, b, 500) OW2 (or_intror INB))|].
      split; [exact SB0|]. split; [exact SB8|].
      eapply (xpres_u8arr H LBk (wS1 e) _ m m' _ _ XP2 SBU).
      assert (LC : Z.of_nat (length (cc_gen 500 0)) = 63) by (vm_compute; reflexivity). rewrite LC.
      unfold xclient_range. split.
      - unfold aclient_range. right; right; right; left. exists (p, b, 500). cbn [blk_addr blk_size fst snd].
        split; [exact INB|]. change (nsh 500) with 63. lia.
      - apply Forall_cons; [|apply Forall_nil]. cbn [fst snd].
        destruct ABb as (B0 & B16 & _ & BT & BC' & _ & BAPP).
        unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO, AIMG_TOP in BAPP.
        unfold sh. rewrite ASHADOW_BASE_val. clear - FAPP BAPP B0 BC' ACF F2.
        destruct FAPP as [X|X]; [right | left]; Z.div_mod_to_equations; lia. }
    eapply (ahh_evt_then H HB _ _ s' msF2 _ mo2 KR2 VIS2).
    { apply we2c. }
    intros msF3 mo3 KR3 MP3 P3. unfold we2c_post in P3.
    apply (ah_done H HB).
    exists s', pid', c', t0', t1', t2', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    split; [exact P3|]. split; [exact KR3|]. split; [exact (ah_mpres_trans H HB _ _ _ MP2 MP3)|].
    split; [lia|]. split; [exact NI|]. split; [exact ABR|]. split; [exact HI2|]. split; [exact WC2|].
    split; [|split; [exact WB' | exact WC']]. split; [exact PS0'|]. split; [exact PSM'|]. split; [exact PV1'|]. split; [exact PV2' | exact PV3'].
  Qed.
End WoP.
