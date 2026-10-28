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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_PrsStmt LbB_SR LbB_Conv LbB_WoGen LbB_WoDefs LbB_WoKit LbB_WoSt LbB_WoMs LbB_WoCall LbB_WoCut LbB_WoZ.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_MILB LbB_StateStmt LbB_ResvB LbB_Own LbB_RtOwn LbB_HKit LbB_HStKit.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_WoR2 LbB_WoR3 LbB_WoR4 LbB_WoR5 LbB_WoE0 LbB_WoE0b LbB_WoP LbB_WoQ LbB_WoF.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_WoVec LbB_WoSt2 LbB_WoRv LbB_WoBP LbB_WoBPsh.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section WoS1.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHb : asan_rt_hyps_bp H.
  Let HB := rt_bp_base H HHb.
  Hypothesis HOWN : rt_own H.
  Hypothesis WTR : po_tr_ok H.

  Lemma wpre_budget : forall e, wpre H e ->
       0 <= w_n e < 2 ^ 24
    /\ lb_small (w_LB e) + po_small (w_n e) <= RT_SMALL_MAX /\ Z.of_nat (length (w_LB e)) + po_cnt (w_n e) <= RT_CNT_MAX
    /\ nlarge (w_LB e) + po_large (w_n e) <= RT_LARGE_MAX /\ po_cost (w_n e) <= as_AL H (w_s e).
  Proof.
    intros e HP. unfold wpre in HP.
    destruct HP as (_ & _ & HN & _ & _ & BS & BC & BL & HP). split; [exact HN|]. split; [exact BS|]. split; [exact BC|].
    split; [exact BL|]. repeat (let X := fresh in destruct HP as [X HP]). exact HP.
  Qed.

  Lemma po_budget_facts : forall n, 0 <= n -> 2 ^ 20 <= po_small n /\ 64 <= po_cnt n /\ 0 <= po_large n /\ 2 ^ 30 <= po_cost n.
  Proof. intros n Hn. unfold po_small, po_cnt, po_large, po_cost. Z.div_mod_to_equations. lia. Qed.

  Ltac mpres_chain :=
    repeat match goal with
    | |- as_MPRES H ?a ?a => apply (ah_mpres_refl H (rt_bp_base H HHb))
    | K : as_MPRES H ?a ?b |- as_MPRES H ?a ?c => apply (ah_mpres_trans H (rt_bp_base H HHb) a b c K)
    end.

  Ltac ws1_dj :=
    lazymatch goal with |- disjoint_from _ _ ?n => let k := eval simpl in n in change n with k end;
    cbn [disjoint_from]; unfold WO_FLAGP, AINTRIN_STACK in *; repeat split; lia.

  Ltac ws1_fw := unfold WO_FLAGP, AINTRIN_STACK in *; repeat (apply Forall_cons; [cbn [fst snd]; lia |]); apply Forall_nil.

  Lemma ws1_wp1 : forall (e : went H) ff fp sk LBk m msF mo (x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    wpre H e -> winv H e ff fp [] sk LBk m -> (forall bb, In bb (w_LB e) -> In bb LBk) ->
    wfc H e ff m -> wpst ff m Z24 Z24 Z24 ->
    as_VIS H sk msF = LbB_WoP.wp1_pre H e ff m x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 -> as_AKREL H sk (mkCfg msF mo) ->
    0 <= as_AL H sk -> lb_small LBk + 500 <= RT_SMALL_MAX -> Z.of_nat (length LBk) + 1 <= RT_CNT_MAX -> nlarge LBk <= RT_LARGE_MAX ->
    as_SR H (LbB_WoP.wp1_post H e ff fp sk LBk mo) (mkCfg msF mo).
  Proof using HHb HOWN WTR. intros. eapply LbB_WoP.wp1; eassumption. Qed.

  Lemma ws1_wp2 : forall (e : went H) ff fp sk LBk (p : bptr) b m msF mo (x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    wpre H e -> winv H e ff fp [] sk LBk m -> (forall bb, In bb (w_LB e) -> In bb LBk) -> In (p, b, 500) LBk ->
    wfc H e ff m -> wpst ff m (vtrip b 500) Z24 Z24 -> wblk m b 500 ->
    as_VIS H sk msF = LbB_WoP.wp2_pre H e ff m x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 -> as_AKREL H sk (mkCfg msF mo) ->
    0 <= as_AL H sk -> lb_small LBk + 100 <= RT_SMALL_MAX -> Z.of_nat (length LBk) + 1 <= RT_CNT_MAX -> nlarge LBk <= RT_LARGE_MAX ->
    as_SR H (LbB_WoP.wp2_post H e ff fp sk LBk b mo) (mkCfg msF mo).
  Proof using HHb HOWN WTR. intros. eapply LbB_WoP.wp2; eassumption. Qed.

  Lemma ws1_split8 : forall m A (w : word) cs, rw_cells asegs m A (C8 w :: cs) -> rw_cells asegs m A [C8 w] /\ rw_cells asegs m (A + 8) cs.
  Proof. intros m A w cs C. change (C8 w :: cs) with ([C8 w] ++ cs) in C. apply rw_cells_app in C as [C1 C2]. split; [exact C1 | exact C2]. Qed.

  Lemma ws1_addr_munch : forall W m m' A n, addressable m A n -> munch W m m' -> wmono asegs m m' ->
    disjoint_from W (sh A) (nsh n) -> addressable m' A n.
  Proof.
    intros W m m' A n (N0 & S) MU WM D. split; [exact N0|].
    eapply SHAD_transport; [exact S | exact MU | exact WM |]. rewrite shadow_of_length by exact N0. exact D.
  Qed.

  Lemma ws1_xc : forall (e : went H) ff fp XSc sk LBk LB m m' A cs, wpre H e -> winv H e ff fp XSc sk LBk m ->
    xpres H LB (wS1 e) [(ff + 3720, ff + 3720 + 24)] m m' -> rw_cells asegs m A cs ->
    ff <= A -> A + Z.of_nat (cells_size cs) <= ff + 3720 -> rw_cells asegs m' A cs.
  Proof.
    intros e ff fp XSc sk LBk LB m m' A cs HP HI XP C A1 A2.
    eapply wrv_xcells; try eassumption.
    - lia.
    - apply Forall_cons; [cbn [fst snd]; lia | apply Forall_nil].
  Qed.

  Lemma ws1_maps_x : forall (e : went H) ff fp XSc sk LBk LB m m', wpre H e -> winv H e ff fp XSc sk LBk m ->
    xpres H LB (wS1 e) [(ff + 3720, ff + 3720 + 24)] m m' -> st_maps_cells m (ff + 3504) -> st_maps_cells m' (ff + 3504).
  Proof.
    intros e ff fp XSc sk LBk LB m m' HP HI XP (M1 & M2 & M3 & M4 & M5 & M6).
    split; [|split; [|split; [|split; [|split]]]];
      (eapply ws1_xc; [exact HP | exact HI | exact XP | eassumption | lia | simpl; lia]).
  Qed.


  Definition wn3_post (e : went H) (ff fp : Z) (XS : list (Z * Z)) (sk : as_St H) (LBk : list block) (b1 b2 b3 : Z)
      : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m',
      ms' = MS (mkR (Z_to_bv 64 WO_ON4_RA) (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) x5 x6 x7 (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
                    (Z_to_bv 64 (ff + 2920)) (Z_to_bv 64 25) x12 x13 x14 x15 x16 x17
                    (Z_to_bv 64 (ff + 3456)) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) (Z_to_bv 64 (ff + 2920)) (Z_to_bv 64 (ff + 3504))
                    (Z_to_bv 64 0x3f800000) (Z_to_bv 64 (ff + 2944)) (Z_to_bv 64 (ff + 2968)) (Z_to_bv 64 (ff + 3696))
                    (Z_to_bv 64 (ff + 2752)) x28 x29 x30 x31)
               (w_F e) (Z_to_bv 64 RESV_OPND_ENTRY) (w_fc e) None m' (seg_rom asegs)
      /\ winv H e ff fp XS sk LBk m' /\ wpcells H e ff m' /\ bp_slots H e ff m' /\ bp_shad ff [18; 20; 21]%nat m'
      /\ wps3 ff m' b1 b2 b3 /\ wtst ff m' (w_words e) (w_n e) Z24 Z24 Z24 /\ addressable m' (ff + 2752) 240.

  Lemma seg_on13 : forall (Q : config -> Prop) (e : went H) msF mo mo0,
    wpre H e -> as_AKREL H (w_s e) (mkCfg msF mo) -> as_MPRES H mo0 mo ->
    e0_post H e (as_VIS H (w_s e) msF) ->
    (forall ff fp msF' mo' s3 XS3 (p1 p2 p3 : bptr) b1 b2 b3,
       let LB3 := (p3, b3, 100) :: (p2, b2, 100) :: (p1, b1, 500) :: w_LB e in
       as_AKREL H s3 (mkCfg msF' mo') -> as_MPRES H mo0 mo' -> as_AL H s3 >= as_AL H (w_s e) ->
       List.NoDup (map blk_id LB3) ->
       wn3_post e ff fp XS3 s3 LB3 b1 b2 b3 (as_VIS H s3 msF') -> as_SR H Q (mkCfg msF' mo')) ->
    as_SR H Q (mkCfg msF mo).
  Proof using HHb HOWN WTR.
    intros Q e msF mo mo0 HP KR MP P0 K.
    destruct P0 as (ff & fp & x5 & x6 & x7 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m0 & VIS & HI & WC & C46 & PM & C72).
    pose proof (wpre_budget e HP) as (HN & BS & BC & BL & AL0).
    pose proof (po_budget_facts (w_n e) ltac:(lia)) as (PB1 & PB2 & PB3 & PB4).
    destruct (z72_split m0 (ff + 3672) C72) as (V1 & V2 & V3).
    replace (ff + 3672 + 24) with (ff + 3696) in V2 by lia. replace (ff + 3672 + 48) with (ff + 3720) in V3 by lia.
    assert (VIS0 : as_VIS H (w_s e) msF = LbB_WoP.wp1_pre H e ff m0 x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31)
      by (rewrite VIS; reflexivity).
    eapply (ah_seq H (rt_bp_base H HHb)).
    { eapply (ws1_wp1 e ff fp (w_s e) (w_LB e) m0 msF mo x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31);
        [exact HP | exact HI | intros bb Hb; exact Hb | exact WC | | exact VIS0 | exact KR | lia | lia | lia | lia].
      split; [exact C46|]. split; [exact PM|]. split; [exact V1|]. split; [exact V2 | exact V3]. }
    intros [msF1 mo1] P1.
    destruct P1 as (s1 & p1 & b1 & y5 & y6 & y7 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m1
                    & VIS1 & KR1 & MP1 & AL1 & NI1 & BR1 & HI1 & WC1 & PST1 & WB1).
    cbn [cfg_ms cfg_model] in VIS1, KR1, MP1.
    eapply (ah_seq H (rt_bp_base H HHb)).
    { eapply (ws1_wp2 e ff fp s1 ((p1, b1, 500) :: w_LB e) p1 b1 m1 msF1 mo1 y5 y6 y7 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31);
        [exact HP | exact HI1 | intros bb Hb; right; exact Hb | left; reflexivity | exact WC1 | exact PST1 | exact WB1 | exact VIS1
        | exact KR1 | lia
        | rewrite lb_small_cons; change (nsmall (blk_size (p1, b1, 500))) with 500; lia
        | cbn [length]; lia
        | rewrite nlarge_cons; change (nlg (blk_size (p1, b1, 500))) with 0; lia]. }
    intros [msF2 mo2] P2.
    destruct P2 as (s2 & p2 & b2 & z5 & z6 & z7 & z12 & z13 & z14 & z15 & z16 & z17 & z28 & z29 & z30 & z31 & m2
                    & VIS2 & KR2 & MP2 & AL2 & NI2 & BR2 & HI2 & WC2 & PST2 & WB1b & WB2).
    cbn [cfg_ms cfg_model] in VIS2, KR2, MP2.
    unfold LbB_WoP.wp3_pre in VIS2.
    destruct (wframe_bounds H e ff fp [] s2 _ m2 HP HI2) as (F0 & F64 & FLO & FH & FL & FS & FSH & SHS & S1L & S1SP & SPH & LOS1).
    pose proof (wfc_wpcells H e ff fp [] s2 _ m2 HI2 WC2) as (_ & _ & _ & QA & _).
    assert (AD24 : addressable m2 (ff + 3720) 24).
    { replace (ff + 3720) with (ff + 3456 + 264) by lia.
      apply (LbB_WoKit3.addressable_sub8 m2 (ff + 3456) 288 264 24 QA); [reflexivity | reflexivity | reflexivity | lia | lia | lia]. }
    assert (TRO : trace_ok (as_TR H) APC0_FREE [rv_del_ra RESV_TYP]).
    { destruct WTR as [_ F]. apply (proj1 (Forall_forall _ _) F). rewrite !in_app_iff. right; right.
      unfold RESV_DEL_RAS. cbn. repeat (first [left; reflexivity | right]). }
    destruct PST2 as (P46 & PM2 & PV1 & PV2 & PV3).
    eapply (wrv_typ H HHb e ff fp [] s2 ((p2, b2, 100) :: (p1, b1, 500) :: w_LB e) [] m2 msF2 mo2 Q
              _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ff + 3720) (w_F e) (w_fc e));
      [exact HP | exact HI2 | intros bb Hb; right; right; exact Hb | exact VIS2 | exact KR2
      | rewrite HLib.u64_of_Z by (unfold WO_AN3_RA; lia); reflexivity | lia | exact PV3 | exact AD24 | lia | unfold WO_FLAGP; lia
      | clear - F64; Z.div_mod_to_equations; lia | apply lb_own_nil | intros bb [] | constructor
      | rewrite !lb_small_cons; change (nsmall (blk_size (p1, b1, 500))) with 500; change (nsmall (blk_size (p2, b2, 100))) with 100; lia
      | cbn [length]; lia
      | rewrite !nlarge_cons; change (nlg (blk_size (p1, b1, 500))) with 0; change (nlg (blk_size (p2, b2, 100))) with 0; lia
      | exact TRO |].
    intros msF3 mo3 s3 p3 b3 m3 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6'
      VIS3 KR3 MP3 HI3 XP3 NI3 VT3 BR3 SH3 AD3 WR3 OWN3 ND3 AL3.
    rewrite (ret_pc_even WO_AN3_RA ltac:(unfold WO_AN3_RA; lia) eq_refl) in VIS3.
    pose proof (winv_rh H _ _ _ _ _ _ _ HI2) as RH2.
    assert (XF : Forall (fun iv : Z * Z => ff <= fst iv /\ snd iv <= ff + 4096) [(ff + 3720, ff + 3720 + 24)])
      by (apply Forall_cons; [cbn [fst snd]; lia | apply Forall_nil]).
    assert (FF2 : fresh_frame H (w_LF e) 6 ff fp) by exact (winv_ff H _ _ _ _ _ _ _ HI2).
    assert (XA : Forall (wfc_apart H e ff) [(ff + 3720, ff + 3720 + 24)]).
    { apply Forall_cons; [| apply Forall_nil]. unfold wfc_apart; cbn [fst snd]. unfold WO_FLAGP, AINTRIN_STACK in *. repeat split; lia. }
    assert (WC3 : wfc H e ff m3) by exact (LbB_WoKit3.wfc_xpres H e ff fp _ _ m2 m3 HP FF2 WC2 XP3 XA).
    pose proof (wfc_wpcells H e ff fp [] s3 _ m3 HI3 WC3) as WPC3.
    destruct WC3 as (_ & _ & _ & _ & _ & SH2C & W0 & W16 & W40 & W48 & W80).
    destruct (ws1_split8 _ _ _ _ W16) as [C16 W24]. replace (wS1 e + 16 + 8) with (wS1 e + 24) in W24 by lia.
    destruct (ws1_split8 _ _ _ _ W24) as [C24 C32]. replace (wS1 e + 24 + 8) with (wS1 e + 32) in C32 by lia.
    assert (WB : 0 <= w_words e < 2 ^ 64 /\ 0 <= w_n e < 2 ^ 64).
    { split; [| lia]. pose proof HP as HP'. unfold wpre in HP'.
      destruct HP' as (_ & _ & _ & [(-> & _) | (pw & k & INw & KR0 & W0' & _ & WK & _)] & _); lia. }
    assert (T24 : rw_cells asegs m3 (wS1 e + 24)
                    [C8 (wz (w_words e)); C8 (wz (w_n e)); C8 (wz ASHADOW_BASE); C8 (wz (ff + 2224)); C8 (wz (ff + 3376))]).
    { change [C8 (wz (w_words e)); C8 (wz (w_n e)); C8 (wz ASHADOW_BASE); C8 (wz (ff + 2224)); C8 (wz (ff + 3376))]
        with ([C8 (wz (w_words e)); C8 (wz (w_n e))] ++ [C8 (wz ASHADOW_BASE); C8 (wz (ff + 2224)); C8 (wz (ff + 3376))]).
      apply rw_cells_app. split; [exact W24|].
      change (wS1 e + 24 + Z.of_nat (cells_size [C8 (wz (w_words e)); C8 (wz (w_n e))])) with (wS1 e + 24 + 16).
      replace (wS1 e + 24 + 16) with (wS1 e + 40) by lia.
      apply rw_cells_cons8_c; [| replace (wS1 e + 40 + 8) with (wS1 e + 48) by lia; exact W48].
      unfold wz. rewrite ASHADOW_BASE_val. exact W40. }
    assert (PST3 : wpst ff m3 (vtrip b1 500) (vtrip b2 100) (vtrip b3 100)).
    { split; [|split; [|split; [|split]]].
      - eapply ws1_xc; [exact HP | exact HI2 | exact XP3 | exact P46 | lia | simpl; lia].
      - exact (ws1_maps_x e ff fp [] s2 _ _ m2 m3 HP HI2 XP3 PM2).
      - eapply ws1_xc; [exact HP | exact HI2 | exact XP3 | exact PV1 | lia | simpl; lia].
      - eapply ws1_xc; [exact HP | exact HI2 | exact XP3 | exact PV2 | lia | simpl; lia].
      - exact (wrv_vtrip32 _ m3 (ff + 3720) b3 VT3 WR3). }
    assert (WB1c : wblk m3 b1 500)
      by exact (wrv_xblk H HHb e ff fp [] s2 _ s2 _ m2 m3 _ p1 b1 500 HP HI2 RH2 XP3 XF ltac:(right; left; reflexivity) WB1b).
    assert (WB2c : wblk m3 b2 100)
      by exact (wrv_xblk H HHb e ff fp [] s2 _ s2 _ m2 m3 _ p2 b2 100 HP HI2 RH2 XP3 XF ltac:(left; reflexivity) WB2).
    assert (WB3 : wblk m3 b3 100) by exact (wrv_wblk [] m3 p3 b3 100 OWN3 SH3).
    eapply (ahh_evt_then H (rt_bp_base H HHb)
              (LbB_WoQ.wp3_post H e ff fp [] s3 ((p3, b3, 100) :: (p2, b2, 100) :: (p1, b1, 500) :: w_LB e) m3 (w_words e) (w_n e))
              Q s3 msF3 _ mo3); [exact KR3 | exact VIS3 | |].
    { exact (LbB_WoQ.wp3 H HHb e ff fp [] s3 _ m3 (w_words e) (w_n e) t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6'
               HP HI3 C16 C24 C32 WB SH2C). }
    intros msF4 mo4 KR4 MP4 P3.
    destruct P3 as (w5 & w6 & w7 & w12 & w13 & w14 & w15 & w16 & w17 & w28 & w29 & w30 & w31 & m4
                    & VIS4 & HI4 & MU4 & WM4 & WT4 & AD4 & SH4).
    eapply (K ff fp msF4 mo4 s3 [] p1 p2 p3 b1 b2 b3); [exact KR4 | mpres_chain | lia | |].
    { exact (ah_nodup H (rt_bp_base H HHb) _ _ _ (winv_rh H _ _ _ _ _ _ _ HI4)). }
    unfold wn3_post.
    exists w5, w6, w7, w12, w13, w14, w15, w16, w17, w28, w29, w30, w31, m4.
    split; [exact VIS4|]. split; [exact HI4|].
    assert (SA1 : sh (ff + 3456) = sh ff + 432) by (unfold sh; clear - F64; Z.div_mod_to_equations; lia).
    assert (SA2 : sh (ff + 3376) = sh ff + 422) by (unfold sh; clear - F64; Z.div_mod_to_equations; lia).
    split.
    { destruct WPC3 as (Q1 & Q2 & Q3 & QA1 & QA2).
      split; [eapply rw_cells_transport; [exact Q1 | exact MU4 | exact WM4 | ws1_dj]|].
      split; [eapply rw_cells_transport; [exact Q2 | exact MU4 | exact WM4 | ws1_dj]|].
      split; [eapply rw_cells_transport; [exact Q3 | exact MU4 | exact WM4 | ws1_dj]|].
      split.
      - eapply ws1_addr_munch; [exact QA1 | exact MU4 | exact WM4 |]. rewrite SA1. change (nsh 288) with 36. ws1_dj.
      - eapply ws1_addr_munch; [exact QA2 | exact MU4 | exact WM4 |]. rewrite SA2. change (nsh 48) with 6. ws1_dj. }
    split.
    { split; [|split].
      - eapply rw_cells_transport; [exact W0 | exact MU4 | exact WM4 | ws1_dj].
      - eapply rw_cells_transport; [exact T24 | exact MU4 | exact WM4 | ws1_dj].
      - eapply rw_cells_transport; [exact W80 | exact MU4 | exact WM4 | ws1_dj]. }
    split; [unfold bp_shad; rewrite <- wo_sh_4t; exact SH4|].
    split; [| split; [exact WT4 | exact AD4]].
    split; [|split; [|split]].
    - eapply wpst_munch; [exact PST3 | exact MU4 | exact WM4 | reflexivity | reflexivity | reflexivity | ws1_fw].
    - destruct (wblk_geo H (rt_bp_base H HHb) e ff fp [] s3 _ m3 p1 b1 500 HP HI3 ltac:(right; right; left; reflexivity))
        as (_ & _ & _ & _ & _ & GS1 & GS2 & GS3 & GS4 & _ & GZ2 & GZ3 & _ & _).
      eapply wblk_munch; [exact WB1c | exact MU4 | exact WM4 | lia |]. unfold zap in *. ws1_fw.
    - destruct (wblk_geo H (rt_bp_base H HHb) e ff fp [] s3 _ m3 p2 b2 100 HP HI3 ltac:(right; left; reflexivity))
        as (_ & _ & _ & _ & _ & GS1 & GS2 & GS3 & GS4 & _ & GZ2 & GZ3 & _ & _).
      eapply wblk_munch; [exact WB2c | exact MU4 | exact WM4 | lia |]. unfold zap in *. ws1_fw.
    - destruct (wblk_geo H (rt_bp_base H HHb) e ff fp [] s3 _ m3 p3 b3 100 HP HI3 ltac:(left; reflexivity))
        as (_ & _ & _ & _ & _ & GS1 & GS2 & GS3 & GS4 & _ & GZ2 & GZ3 & _ & _).
      eapply wblk_munch; [exact WB3 | exact MU4 | exact WM4 | lia |]. unfold zap in *. ws1_fw.
  Qed.
End WoS1.
