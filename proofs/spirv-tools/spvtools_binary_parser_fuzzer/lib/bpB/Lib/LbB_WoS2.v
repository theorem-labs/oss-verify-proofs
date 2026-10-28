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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_WoR2 LbB_WoR3 LbB_WoR4 LbB_WoR5 LbB_WoE0 LbB_WoE0b LbB_WoQ LbB_WoF.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_WoVec LbB_WoSt2 LbB_WoRv LbB_WoBP LbB_WoBPsh LbB_WoS1 LbB_WoS3.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section WoS2.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHb : asan_rt_hyps_bp H.
  Let HB := rt_bp_base H HHb.
  Hypothesis HOWN : rt_own H.
  Hypothesis WTR : po_tr_ok H.

  Ltac mpres_chain :=
    repeat match goal with
    | |- as_MPRES H ?a ?a => apply (ah_mpres_refl H HB)
    | K : as_MPRES H ?a ?b |- as_MPRES H ?a ?c => apply (ah_mpres_trans H HB a b c K)
    end.

  Lemma lb_small_wcons : forall (p : bptr) A n LB, 0 <= n <= 64512 -> lb_small ((p, A, n) :: LB) = n + lb_small LB.
  Proof. intros p A n LB Hn. rewrite lb_small_cons. cbn [blk_size fst snd]. unfold nsmall. destruct (Z.leb_spec n 64512); lia. Qed.
  Lemma nlarge_wcons : forall (p : bptr) A n LB, 0 <= n <= 64512 -> nlarge ((p, A, n) :: LB) = nlarge LB.
  Proof. intros p A n LB Hn. rewrite nlarge_cons. cbn [blk_size fst snd]. unfold nlg. destruct (Z.ltb_spec 64512 n); lia. Qed.


  Lemma ws2_tr : forall r, In r RESV_DEL_RAS -> trace_ok (as_TR H) APC0_FREE [r].
  Proof.
    intros r Hr. pose proof WTR as [_ F]. apply (proj1 (List.Forall_forall _ _) F).
    rewrite !List.in_app_iff. tauto.
  Qed.

  Lemma ws2_slot : forall (e : went H) ff fp XSc sk LBk LB m m' v A cs,
    wpre H e -> winv H e ff fp XSc sk LBk m -> xpres H LB (wS1 e) [(v, v + 24)] m m' -> rw_cells asegs m A cs ->
    cells_size cs = 24%nat -> ff <= A -> A + 24 <= ff + 4096 -> A + 24 <= v \/ v + 24 <= A -> rw_cells asegs m' A cs.
  Proof.
    intros e ff fp XSc sk LBk LB m m' v A cs HP HI XP C S A1 A2 A3.
    apply (wrv_xcells H e ff fp XSc sk LBk LB m m' [(v, v + 24)] A cs HP HI XP C A1); rewrite S; change (Z.of_nat 24) with 24.
    - exact A2.
    - constructor; [cbn [fst snd]; lia | constructor].
  Qed.

  Lemma ws2_xblk : forall (e : went H) ff fp XSc s LB m m' v (q : bptr) b n,
    wpre H e -> winv H e ff fp XSc s LB m -> xpres H LB (wS1 e) [(v, v + 24)] m m' -> ff <= v -> v + 24 <= ff + 4096 ->
    In (q, b, n) LB -> wblk m b n -> wblk m' b n.
  Proof.
    intros e ff fp XSc s LB m m' v q b n HP HI XP V1 V2 IN W.
    apply (wrv_xblk H HHb e ff fp XSc s LB s LB m m' [(v, v + 24)] q b n HP HI (winv_rh H _ _ _ _ _ _ _ HI) XP); [| exact IN | exact W].
    constructor; [cbn [fst snd]; lia | constructor].
  Qed.

  Lemma ws2_shad : forall (e : went H) ff fp XSc sk LBk LB m m' X,
    wpre H e -> winv H e ff fp XSc sk LBk m -> xpres H LB (wS1 e) X m m' ->
    Forall (fun iv : Z * Z => ff <= fst iv /\ snd iv <= ff + 4096) X ->
    bp_shad ff [18; 20; 21]%nat m -> bp_shad ff [18; 20; 21]%nat m'.
  Proof.
    intros e ff fp XSc sk LBk LB m m' X HP HI XP FX SH. unfold bp_shad in *.
    destruct (wrv_fsb H e ff fp XSc sk LBk m HP HI) as (B1 & B2 & F64 & FC & FAPP).
    pose proof aceil_facts as ACF.
    eapply (LbB_WoKit3.xpres_u8arr H); [exact XP | exact SH |].
    replace (Z.of_nat (length (map (Z_to_bv 8) (wo_sh [18; 20; 21]%nat)))) with 476 by (rewrite <- wo_sh_4t; reflexivity).
    split.
    - unfold aclient_range. right; right; right; right; right; left.
      clear - B1 B2 F64. unfold sh. Z.div_mod_to_equations. lia.
    - eapply Forall_impl; [| exact FX]. intros iv Kv. cbn in Kv.
      clear - Kv FAPP ACF F64 FC. unfold sh in *. rewrite ASHADOW_BASE_val in *.
      destruct FAPP as [[X1 Y]|[X1 Y]]; [right | left]; Z.div_mod_to_equations; lia.
  Qed.

  Ltac ws2sz := first [lia | (try unfold vtrip); (try unfold Z24); cbn; lia].

  Lemma ws2_keep : forall (e : went H) ff fp XSc s LB m m' v b1 b2 b3 (p1 p2 p3 : bptr),
    wpre H e -> winv H e ff fp XSc s LB m -> xpres H LB (wS1 e) [(v, v + 24)] m m' ->
    ff + 2920 <= v -> v + 24 <= ff + 2992 ->
    In (p1, b1, 500) LB -> In (p2, b2, 100) LB -> In (p3, b3, 100) LB ->
    wpcells H e ff m -> bp_slots H e ff m -> bp_shad ff [18; 20; 21]%nat m -> wps3 ff m b1 b2 b3 ->
    addressable m (ff + 2752) 240 ->
    rw_cells asegs m (ff + 2752) [C8 (Z_to_bv 64 (w_words e)); C8 (Z_to_bv 64 (w_n e)); C8 (Z_to_bv 64 0)] ->
    rw_cells asegs m (ff + 2776) [CB 22 (poison_bytes 22 0)] -> st_maps_cells m (ff + 2752) ->
    wpcells H e ff m' /\ bp_slots H e ff m' /\ bp_shad ff [18; 20; 21]%nat m' /\ wps3 ff m' b1 b2 b3
    /\ addressable m' (ff + 2752) 240
    /\ rw_cells asegs m' (ff + 2752) [C8 (Z_to_bv 64 (w_words e)); C8 (Z_to_bv 64 (w_n e)); C8 (Z_to_bv 64 0)]
    /\ rw_cells asegs m' (ff + 2776) [CB 22 (poison_bytes 22 0)] /\ st_maps_cells m' (ff + 2752).
  Proof.
    intros e ff fp XSc s LB m m' v b1 b2 b3 p1 p2 p3 HP HI XP V1 V2 I1 I2 I3
      (C1 & C2 & C3 & A1 & A2) (S1 & S2 & S3) SH ((P0 & (M1 & M2 & M3 & M4 & M5 & M6) & Q1 & Q2 & Q3) & W1 & W2 & W3) AD T0 T1
      (N1 & N2 & N3 & N4 & N5 & N6).
    pose proof (wframe_bounds H e ff fp XSc s LB m HP HI) as (G0 & G64 & _ & _ & _ & G5 & _).
    unfold WO_FLAGP, AINTRIN_STACK in G5.
    assert (FX : Forall (fun iv : Z * Z => ff <= fst iv /\ snd iv <= ff + 4096) [(v, v + 24)])
      by (constructor; [cbn [fst snd]; lia | constructor]).
    assert (XC : forall A cs, rw_cells asegs m A cs -> ff <= A -> A + Z.of_nat (cells_size cs) <= ff + 4096 ->
                   A + Z.of_nat (cells_size cs) <= v \/ v + 24 <= A -> rw_cells asegs m' A cs).
    { intros A cs C X1 X2 X3. apply (wrv_xcells H e ff fp XSc s LB LB m m' [(v, v + 24)] A cs HP HI XP C X1 X2).
      constructor; [cbn [fst snd]; lia | constructor]. }
    assert (XS : forall A cs, rw_cells asegs m A cs -> wS1 e <= A -> rw_cells asegs m' A cs).
    { intros A cs C X1. apply (wrv_xs1 H e ff fp XSc s LB LB m m' [(v, v + 24)] A cs HP HI XP C X1).
      constructor; [cbn [fst snd]; lia | constructor]. }
    assert (XA : forall A n, addressable m A n -> ff <= A -> A + n <= ff + 4088 -> addressable m' A n).
    { intros A n AA X1 X2. apply (wrv_xaddr H e ff fp XSc s LB LB m m' [(v, v + 24)] A n HP HI XP AA X1); [unfold WO_FLAGP; lia | exact FX]. }
    assert (XB : forall q b n, In (q, b, n) LB -> wblk m b n -> wblk m' b n).
    { intros q b n IN W. exact (ws2_xblk e ff fp XSc s LB m m' v q b n HP HI XP ltac:(lia) ltac:(lia) IN W). }
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))).
    - refine (conj _ (conj _ (conj _ (conj _ _)))).
      + apply XC; [exact C1 | lia | ws2sz | ws2sz].
      + apply XC; [exact C2 | lia | ws2sz | ws2sz].
      + apply XC; [exact C3 | lia | ws2sz | ws2sz].
      + apply XA; [exact A1 | lia | lia].
      + apply XA; [exact A2 | lia | lia].
    - refine (conj _ (conj _ _)).
      + apply XS; [exact S1 | lia].
      + apply XS; [exact S2 | lia].
      + apply XS; [exact S3 | lia].
    - exact (ws2_shad e ff fp XSc s LB LB m m' [(v, v + 24)] HP HI XP FX SH).
    - refine (conj (conj _ (conj _ (conj _ (conj _ _)))) (conj _ (conj _ _))).
      + apply XC; [exact P0 | lia | ws2sz | ws2sz].
      + unfold st_maps_cells. refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
        * apply XC; [exact M1 | lia | ws2sz | ws2sz].
        * apply XC; [exact M2 | lia | ws2sz | ws2sz].
        * apply XC; [exact M3 | lia | ws2sz | ws2sz].
        * apply XC; [exact M4 | lia | ws2sz | ws2sz].
        * apply XC; [exact M5 | lia | ws2sz | ws2sz].
        * apply XC; [exact M6 | lia | ws2sz | ws2sz].
      + apply XC; [exact Q1 | lia | ws2sz | ws2sz].
      + apply XC; [exact Q2 | lia | ws2sz | ws2sz].
      + apply XC; [exact Q3 | lia | ws2sz | ws2sz].
      + exact (XB p1 b1 500 I1 W1).
      + exact (XB p2 b2 100 I2 W2).
      + exact (XB p3 b3 100 I3 W3).
    - apply XA; [exact AD | lia | lia].
    - apply XC; [exact T0 | lia | ws2sz | ws2sz].
    - apply XC; [exact T1 | lia | ws2sz | ws2sz].
    - unfold st_maps_cells. refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
      + apply XC; [exact N1 | lia | ws2sz | ws2sz].
      + apply XC; [exact N2 | lia | ws2sz | ws2sz].
      + apply XC; [exact N3 | lia | ws2sz | ws2sz].
      + apply XC; [exact N4 | lia | ws2sz | ws2sz].
      + apply XC; [exact N5 | lia | ws2sz | ws2sz].
      + apply XC; [exact N6 | lia | ws2sz | ws2sz].
  Qed.

  Ltac ws2_inlb := unfold RESV_DEL_RAS; repeat (first [left; reflexivity | right]).

  Lemma seg_on46 : forall (Q : config -> Prop) (e : went H) ff fp msF mo mo0 s3 XS3 (p1 p2 p3 : bptr) b1 b2 b3,
    let LB3 := (p3, b3, 100) :: (p2, b2, 100) :: (p1, b1, 500) :: w_LB e in
    wpre H e -> as_AKREL H s3 (mkCfg msF mo) -> as_MPRES H mo0 mo -> as_AL H s3 >= as_AL H (w_s e) ->
    List.NoDup (map blk_id LB3) ->
    wn3_post H e ff fp XS3 s3 LB3 b1 b2 b3 (as_VIS H s3 msF) ->
    (forall msF' mo' s6 XS6 (p4 p5 p6 : bptr) g h k,
       let LB6 := (p6, k, 100) :: (p5, h, 100) :: (p4, g, 500) :: LB3 in
       as_AKREL H s6 (mkCfg msF' mo') -> as_MPRES H mo0 mo' -> as_AL H s6 >= as_AL H (w_s e) ->
       List.NoDup (map blk_id LB6) ->
       wm3_post H e ff fp XS6 s6 LB6 p4 p5 p6 b1 b2 b3 g h k (as_VIS H s6 msF') -> as_SR H Q (mkCfg msF' mo')) ->
    as_SR H Q (mkCfg msF mo).
  Proof using HHb HOWN WTR.
    intros Q e ff fp msF mo mo0 s3 XS3 p1 p2 p3 b1 b2 b3 LB3 HP KR MP AL3 ND P3 K.
    destruct P3 as (x5 & x6 & x7 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m0 & VIS & HI & WC & BS & SHD & PS & TS & AD).
    destruct TS as (T0 & T1 & TM & Z1 & Z2 & Z3).
    pose proof (wpre_budget H e HP) as (HN & BSm & BC & BL & AL0).
    pose proof (po_budget_facts (w_n e) ltac:(lia)) as (PB1 & PB2 & PB3 & PB4).
    pose proof (wframe_bounds H e ff fp XS3 s3 LB3 m0 HP HI) as (G0 & G64 & _).
    assert (V8 : forall o, o mod 8 = 0 -> (ff + o) mod 8 = 0) by (intros o Ho; clear - G64 Ho; Z.div_mod_to_equations; lia).
    assert (IN3 : forall b, In b (w_LB e) -> In b LB3) by (intros b Hb; unfold LB3; right; right; right; exact Hb).
    assert (ADs : forall m o, addressable m (ff + 2752) 240 -> 0 <= o -> o + 24 <= 240 -> o mod 8 = 0 -> addressable m (ff + 2752 + o) 24).
    { intros m o A Ho1 Ho2 Ho3. apply (LbB_WoKit3.addressable_sub8 m (ff + 2752) 240 o 24 A); first [reflexivity | lia]. }
    eapply (wrv_opnd H HHb e ff fp XS3 s3 LB3 [] m0 msF mo Q);
      [exact HP | exact HI | exact IN3 | exact VIS | exact KR | first [reflexivity | rewrite Z_to_bv_unsigned; reflexivity] | lia | exact Z1
      | replace (ff + 2920) with (ff + 2752 + 168) by lia; exact (ADs m0 168 AD ltac:(lia) ltac:(lia) eq_refl)
      | lia | unfold WO_FLAGP; lia | apply V8; reflexivity
      | apply lb_own_nil | intros b Hb; destruct Hb | apply List.NoDup_nil
      | unfold LB3; rewrite !lb_small_wcons by lia; lia | unfold LB3; cbn [length]; lia
      | unfold LB3; rewrite !nlarge_wcons by lia; lia | apply ws2_tr; ws2_inlb |].
    intros msF1 mo1 s4 q4 g m1 u0 u1 u2 c0 c1 c2 c3 c4 c5 c6 c7 u3 u4 u5 u6 VIS1 KR1 MP1 HI1 XP1 NI1 VO1 _ SH1 _ WR1 OWN1 ND1 ALr1.
    rewrite (ret_pc_even WO_ON4_RA ltac:(unfold WO_ON4_RA; lia) eq_refl) in VIS1.
    destruct (ws2_keep e ff fp XS3 s3 LB3 m0 m1 (ff + 2920) b1 b2 b3 p1 p2 p3 HP HI XP1 ltac:(lia) ltac:(lia)
                (or_intror (or_intror (or_introl eq_refl))) (or_intror (or_introl eq_refl)) (or_introl eq_refl)
                WC BS SHD PS AD T0 T1 TM) as (WC1 & BS1 & SHD1 & PS1 & AD1 & T01 & T11 & TM1).
    pose proof (wrv_vtrip_opnd _ m1 (ff + 2920) g VO1 WR1) as VT1.
    pose proof (wrv_wblk [] m1 q4 g 500 OWN1 SH1) as WG1.
    pose proof (ws2_slot e ff fp XS3 s3 LB3 LB3 m0 m1 (ff + 2920) (ff + 2944) Z24 HP HI XP1 Z2 eq_refl ltac:(lia) ltac:(lia) ltac:(lia)) as Z2a.
    pose proof (ws2_slot e ff fp XS3 s3 LB3 LB3 m0 m1 (ff + 2920) (ff + 2968) Z24 HP HI XP1 Z3 eq_refl ltac:(lia) ltac:(lia) ltac:(lia)) as Z3a.
    refine (ahh_evt_then H HB _ Q s4 msF1 _ mo1 KR1 VIS1
              (wq1 H e ff fp XS3 s4 _ m1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HP HI1) _).
    intros msF2 mo2 KR2 MP2 P2.
    destruct P2 as (y5 & y6 & y7 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & VIS2).
    eapply (wrv_w32 H HHb e ff fp XS3 s4 ((q4, g, 500) :: LB3) [(q4, g, 500)] m1 msF2 mo2 Q);
      [exact HP | exact HI1 | intros b Hb; right; exact (IN3 b Hb) | exact VIS2 | exact KR2
      | first [reflexivity | rewrite Z_to_bv_unsigned; reflexivity] | lia | exact Z2a
      | replace (ff + 2944) with (ff + 2752 + 192) by lia; exact (ADs m1 192 AD1 ltac:(lia) ltac:(lia) eq_refl)
      | lia | unfold WO_FLAGP; lia | apply V8; reflexivity
      | exact OWN1 | intros b Hb; destruct Hb as [Hb | []]; left; exact Hb | exact ND1
      | unfold LB3; rewrite !lb_small_wcons by lia; lia | unfold LB3; cbn [length]; lia
      | unfold LB3; rewrite !nlarge_wcons by lia; lia | apply ws2_tr; ws2_inlb |].
    intros msF3 mo3 s5 q5 h m2 v0 v1 v2 d0 d1 d2 d3 d4 d5 d6 d7 v3 v4 v5 v6 VIS3 KR3 MP3 HI2 XP2 NI2 VC2 _ SH2 _ WR2 OWN2 ND2 ALr2.
    rewrite (ret_pc_even WO_ON5_RA ltac:(unfold WO_ON5_RA; lia) eq_refl) in VIS3.
    destruct (ws2_keep e ff fp XS3 s4 ((q4, g, 500) :: LB3) m1 m2 (ff + 2944) b1 b2 b3 p1 p2 p3 HP HI1 XP2 ltac:(lia) ltac:(lia)
                (or_intror (or_intror (or_intror (or_introl eq_refl)))) (or_intror (or_intror (or_introl eq_refl)))
                (or_intror (or_introl eq_refl)) WC1 BS1 SHD1 PS1 AD1 T01 T11 TM1)
      as (WC2 & BS2 & SHD2 & PS2 & AD2 & T02 & T12 & TM2).
    pose proof (wrv_vtrip32 _ m2 (ff + 2944) h VC2 WR2) as VT2.
    pose proof (wrv_wblk [(q4, g, 500)] m2 q5 h 100 OWN2 SH2) as WH2.
    pose proof (ws2_slot e ff fp XS3 s4 _ _ m1 m2 (ff + 2944) (ff + 2920) (vtrip g 500) HP HI1 XP2 VT1 eq_refl
                  ltac:(lia) ltac:(lia) ltac:(lia)) as VT1a.
    pose proof (ws2_slot e ff fp XS3 s4 _ _ m1 m2 (ff + 2944) (ff + 2968) Z24 HP HI1 XP2 Z3a eq_refl
                  ltac:(lia) ltac:(lia) ltac:(lia)) as Z3b.
    pose proof (ws2_xblk e ff fp XS3 s4 _ m1 m2 (ff + 2944) q4 g 500 HP HI1 XP2 ltac:(lia) ltac:(lia) (or_introl eq_refl) WG1) as WG2.
    refine (ahh_evt_then H HB _ Q s5 msF3 _ mo3 KR3 VIS3
              (wq2 H e ff fp XS3 s5 _ m2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HP HI2) _).
    intros msF4 mo4 KR4 MP4 P4.
    destruct P4 as (w5 & w6 & w7 & w12 & w13 & w14 & w15 & w16 & w17 & w28 & w29 & w30 & w31 & VIS4).
    eapply (wrv_typ H HHb e ff fp XS3 s5 ((q5, h, 100) :: (q4, g, 500) :: LB3) [(q5, h, 100); (q4, g, 500)] m2 msF4 mo4 Q);
      [exact HP | exact HI2 | intros b Hb; right; right; exact (IN3 b Hb) | exact VIS4 | exact KR4
      | first [reflexivity | rewrite Z_to_bv_unsigned; reflexivity] | lia | exact Z3b
      | replace (ff + 2968) with (ff + 2752 + 216) by lia; exact (ADs m2 216 AD2 ltac:(lia) ltac:(lia) eq_refl)
      | lia | unfold WO_FLAGP; lia | apply V8; reflexivity
      | exact OWN2 | intros b Hb; destruct Hb as [Hb | [Hb | []]]; [left | right; left]; exact Hb | exact ND2
      | unfold LB3; rewrite !lb_small_wcons by lia; lia | unfold LB3; cbn [length]; lia
      | unfold LB3; rewrite !nlarge_wcons by lia; lia | apply ws2_tr; ws2_inlb |].
    intros msF5 mo5 s6 q6 k m3 r0 r1 r2 f0 f1 f2 f3 f4 f5 f6 f7 r3 r4 r5 r6 VIS5 KR5 MP5 HI3 XP3 NI3 VC3 _ SH3 _ WR3 OWN3 ND3 ALr3.
    rewrite (ret_pc_even WO_ON6_RA ltac:(unfold WO_ON6_RA; lia) eq_refl) in VIS5.
    destruct (ws2_keep e ff fp XS3 s5 ((q5, h, 100) :: (q4, g, 500) :: LB3) m2 m3 (ff + 2968) b1 b2 b3 p1 p2 p3 HP HI2 XP3
                ltac:(lia) ltac:(lia)
                (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl)))))
                (or_intror (or_intror (or_intror (or_introl eq_refl))))
                (or_intror (or_intror (or_introl eq_refl))) WC2 BS2 SHD2 PS2 AD2 T02 T12 TM2)
      as (WC3 & BS3 & SHD3 & PS3 & AD3 & T03 & T13 & TM3).
    pose proof (wrv_vtrip32 _ m3 (ff + 2968) k VC3 WR3) as VT3.
    pose proof (wrv_wblk [(q5, h, 100); (q4, g, 500)] m3 q6 k 100 OWN3 SH3) as WK3.
    pose proof (ws2_slot e ff fp XS3 s5 _ _ m2 m3 (ff + 2968) (ff + 2920) (vtrip g 500) HP HI2 XP3 VT1a eq_refl
                  ltac:(lia) ltac:(lia) ltac:(lia)) as VT1b.
    pose proof (ws2_slot e ff fp XS3 s5 _ _ m2 m3 (ff + 2968) (ff + 2944) (vtrip h 100) HP HI2 XP3 VT2 eq_refl
                  ltac:(lia) ltac:(lia) ltac:(lia)) as VT2a.
    pose proof (ws2_xblk e ff fp XS3 s5 _ m2 m3 (ff + 2968) q4 g 500 HP HI2 XP3 ltac:(lia) ltac:(lia)
                  (or_intror (or_introl eq_refl)) WG2) as WG3.
    pose proof (ws2_xblk e ff fp XS3 s5 _ m2 m3 (ff + 2968) q5 h 100 HP HI2 XP3 ltac:(lia) ltac:(lia)
                  (or_introl eq_refl) WH2) as WH3.
    refine (ahh_evt_then H HB _ Q s6 msF5 _ mo5 KR5 VIS5
              (wq3 H e ff fp XS3 s6 _ m3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HP HI3) _).
    intros msF6 mo6 KR6 MP6 P6.
    destruct P6 as (z5 & z6 & z7 & z12 & z13 & z14 & z15 & z16 & z17 & z28 & z29 & z30 & z31 & VIS6).
    pose proof WC3 as (_ & _ & _ & A288 & _).
    eapply (K msF6 mo6 s6 XS3 q4 q5 q6 g h k); [exact KR6 | mpres_chain | lia | |].
    - apply List.NoDup_cons; [exact NI3 |]. apply List.NoDup_cons; [exact NI2 |]. apply List.NoDup_cons; [exact NI1 | exact ND].
    - exists z5, z6, z7, z12, z13, z14, z15, z16, z17, z28, z29, z30, z31, m3.
      split; [exact VIS6 |]. split; [exact HI3 |]. split; [exact WC3 |]. split; [exact BS3 |]. split; [exact SHD3 |].
      split; [exact PS3 |].
      split; [exact (conj T03 (conj T13 (conj TM3 (conj VT1b (conj VT2a VT3))))) |].
      split; [exact WG3 |]. split; [exact WH3 |]. split; [exact WK3 |].
      split; [eapply lb_own_incl; [| exact OWN3]; intros b Hb; cbn in Hb |- *; tauto |].
      unfold ST_SIZE. split.
      + replace (ff + 3504) with (ff + 3456 + 48) by lia.
        apply (LbB_WoKit3.addressable_sub8 m3 (ff + 3456) 288 48 240 A288); first [reflexivity | lia].
      + exact AD3.
  Qed.
End WoS2.
