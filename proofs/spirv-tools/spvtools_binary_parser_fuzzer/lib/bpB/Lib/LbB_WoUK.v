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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_MILB LbB_PrsStmt LbB_StateStmt LbB_HKit LbB_HStKit.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_WoGen LbB_WoDefs LbB_WoKit LbB_WoKit3 LbB_WoSt LbB_WoMs LbB_WoCut LbB_WoZ LbB_WoT2.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_WoVec LbB_WoUR LbB_WoBP LbB_WoShK LbB_PmMagW.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section WoUK.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHb : asan_rt_hyps_bp H.
  Let HB := rt_bp_base H HHb.

  Lemma uk_fill : forall (ff S1 : Z) (m5 m6 m7 m8 m9 m10 m11 m12 m13 : mem),
    0 <= ff -> ff + 3296 <= S1 - AINTRIN_STACK ->
    munch [(ff + 3056, ff + 3056 + 46); (S1 - AINTRIN_STACK, S1)] m5 m6 -> wmono asegs m5 m6 ->
    rw_cells asegs m6 (ff + 3056) [CB (Z.to_nat 46) (poison_bytes (Z.to_nat 46) 0)] ->
    munch [(ff + 3104, ff + 3104 + 32); (S1 - AINTRIN_STACK, S1)] m6 m7 -> wmono asegs m6 m7 ->
    rw_cells asegs m7 (ff + 3104) [CB (Z.to_nat 32) (poison_bytes (Z.to_nat 32) 0)] ->
    munch [(ff + 3136, ff + 3140)] m7 m8 -> wmono asegs m7 m8 -> rw_cells asegs m8 (ff + 3136) [C4 (Z_to_bv 64 0x3f800000)] ->
    munch [(ff + 3144, ff + 3144 + 32); (S1 - AINTRIN_STACK, S1)] m8 m9 -> wmono asegs m8 m9 ->
    rw_cells asegs m9 (ff + 3144) [CB (Z.to_nat 32) (poison_bytes (Z.to_nat 32) 0)] ->
    munch [(ff + 3176, ff + 3180)] m9 m10 -> wmono asegs m9 m10 -> rw_cells asegs m10 (ff + 3176) [C4 (Z_to_bv 64 0x3f800000)] ->
    munch [(ff + 3184, ff + 3184 + 32); (S1 - AINTRIN_STACK, S1)] m10 m11 -> wmono asegs m10 m11 ->
    rw_cells asegs m11 (ff + 3184) [CB (Z.to_nat 32) (poison_bytes (Z.to_nat 32) 0)] ->
    munch [(ff + 3216, ff + 3220)] m11 m12 -> wmono asegs m11 m12 -> rw_cells asegs m12 (ff + 3216) [C4 (Z_to_bv 64 0x3f800000)] ->
    munch [(ff + 3224, ff + 3224 + 72); (S1 - AINTRIN_STACK, S1)] m12 m13 -> wmono asegs m12 m13 ->
    rw_cells asegs m13 (ff + 3224) [CB 72 (poison_bytes 72 0)] ->
    wtst0 ff m13 Z24 Z24 Z24 /\ munch [(S1 - AINTRIN_STACK, S1); (ff + 3056, ff + 3296)] m5 m13 /\ wmono asegs m5 m13.
  Proof.
    intros ff S1 m5 m6 m7 m8 m9 m10 m11 m12 m13 F0 FS MU6 WM6 Z6 MU7 WM7 Z7 MU8 WM8 C8 MU9 WM9 Z9 MU10 WM10 C10
      MU11 WM11 Z11 MU12 WM12 C12 MU13 WM13 Z13.
    pose proof (munch_app _ _ _ _ _ MU12 MU13) as S12. pose proof (wmono_trans asegs _ _ _ WM12 WM13) as U12.
    pose proof (munch_app _ _ _ _ _ MU11 S12) as S11. pose proof (wmono_trans asegs _ _ _ WM11 U12) as U11.
    pose proof (munch_app _ _ _ _ _ MU10 S11) as S10. pose proof (wmono_trans asegs _ _ _ WM10 U11) as U10.
    pose proof (munch_app _ _ _ _ _ MU9 S10) as S9. pose proof (wmono_trans asegs _ _ _ WM9 U10) as U9.
    pose proof (munch_app _ _ _ _ _ MU8 S9) as S8. pose proof (wmono_trans asegs _ _ _ WM8 U9) as U8.
    pose proof (munch_app _ _ _ _ _ MU7 S8) as S7. pose proof (wmono_trans asegs _ _ _ WM7 U8) as U7.
    pose proof (munch_app _ _ _ _ _ MU6 S7) as S6. pose proof (wmono_trans asegs _ _ _ WM6 U7) as U6.
    cbn [app] in S6, S7, S8, S9, S10, S11, S12.
    unfold AINTRIN_STACK in *.
    assert (T1 : rw_cells asegs m13 (ff + 3224) Z24)
      by (unfold Z24; replace (ff + 3224) with (ff + 3224 + 0) by lia; apply (zero_cells_sub m13 (ff + 3224) 72 0 24 Z13); lia).
    assert (T2 : rw_cells asegs m13 (ff + 3224 + 24) Z24) by (unfold Z24; apply (zero_cells_sub m13 (ff + 3224) 72 24 24 Z13); lia).
    assert (T3 : rw_cells asegs m13 (ff + 3224 + 48) Z24) by (unfold Z24; apply (zero_cells_sub m13 (ff + 3224) 72 48 24 Z13); lia).
    split; [|split; [eapply munch_in2; [exact S6 | repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia] | exact U6]].
    split; [eapply rw_cells_transport; [exact Z6 | exact S7 | exact U7 | cbn; lia]|].
    split; [unfold st_maps_cells; refine (conj _ (conj _ (conj _ (conj _ (conj _ _)))))|].
    - replace (ff + 3056 + 48) with (ff + 3104) by lia. eapply rw_cells_transport; [exact Z7 | exact S8 | exact U8 | cbn; lia].
    - replace (ff + 3056 + 80) with (ff + 3136) by lia. eapply rw_cells_transport; [exact C8 | exact S9 | exact U9 | cbn; lia].
    - replace (ff + 3056 + 88) with (ff + 3144) by lia. eapply rw_cells_transport; [exact Z9 | exact S10 | exact U10 | cbn; lia].
    - replace (ff + 3056 + 120) with (ff + 3176) by lia. eapply rw_cells_transport; [exact C10 | exact S11 | exact U11 | cbn; lia].
    - replace (ff + 3056 + 128) with (ff + 3184) by lia. eapply rw_cells_transport; [exact Z11 | exact S12 | exact U12 | cbn; lia].
    - replace (ff + 3056 + 160) with (ff + 3216) by lia. eapply rw_cells_transport; [exact C12 | exact MU13 | exact WM13 | cbn; lia].
    - split; [exact T1|]. split; [replace (ff + 3248) with (ff + 3224 + 24) by lia; exact T2|].
      replace (ff + 3272) with (ff + 3224 + 48) by lia; exact T3.
  Qed.

  Lemma uk_slots : forall (e : went H) ff m m' W, bp_slots H e ff m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => snd iv <= wS1 e) W -> bp_slots H e ff m'.
  Proof.
    intros e ff m m' W (C1 & C2 & C3) MU WM FW.
    assert (DJ : forall k n, 0 <= k -> disjoint_from W (wS1 e + k) n).
    { intros k n Hk. apply disj_of_all. intros iv Hiv. right. rewrite Forall_forall in FW. pose proof (FW iv Hiv). lia. }
    split; [|split].
    - eapply (rw_cells_transport asegs W m m'); [exact C1 | exact MU | exact WM |]. replace (wS1 e) with (wS1 e + 0) by lia. apply DJ; lia.
    - eapply (rw_cells_transport asegs W m m'); [exact C2 | exact MU | exact WM |]. apply DJ; lia.
    - eapply (rw_cells_transport asegs W m m'); [exact C3 | exact MU | exact WM |]. apply DJ; lia.
  Qed.

  Lemma uk_shad : forall ff (m m' : mem) W, bp_shad ff [19; 20; 21]%nat m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => snd iv <= sh ff \/ sh ff + 512 <= fst iv) W -> bp_shad ff [19; 20; 21]%nat m'.
  Proof.
    intros ff m m' W SH MU WM FW. unfold bp_shad in *.
    eapply u8arr_transport; [exact SH | exact MU | exact WM |].
    rewrite length_map. replace (Z.of_nat (length (wo_sh [19; 20; 21]%nat))) with 476 by (vm_compute; reflexivity).
    apply disj_of_all. intros iv Hiv. rewrite Forall_forall in FW. pose proof (FW iv Hiv). lia.
  Qed.

  Lemma uk_addr : forall ff (m : mem), 0 <= ff -> ff mod 64 = 0 -> bp_shad ff [19; 20; 21]%nat m -> addressable m (ff + 3056) 240.
  Proof.
    intros ff m F0 F64 SH.
    apply (bp_shad_addr ff [19; 20; 21]%nat m 3056 240 SH).
    - exact F0.
    - clear - F64. Z.div_mod_to_equations. lia.
    - lia.
    - reflexivity.
    - lia.
    - reflexivity.
    - vm_compute. discriminate.
    - vm_compute. reflexivity.
  Qed.

  Lemma uk_wr : forall (e : went H) ff fp XS sk LBk m, winv H e ff fp XS sk LBk m -> wr_at asegs m (ff + 3056) 240.
  Proof.
    intros e ff fp XS sk LBk m HI.
    apply (wr_at_sub m ff WO_FLAGP); [exact (winv_wf H _ _ _ _ _ _ _ HI) | lia | unfold WO_FLAGP; lia | lia].
  Qed.

  Ltac ukF := repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; unfold AINTRIN_STACK in *; lia.

  Lemma wu_run : forall (e : went H) ff fp XS sk LBk m (Q : machine_state -> Prop)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 s2 s5 s6 s7 s9 s10 s11 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (r : Z),
    wpre H e -> winv H e ff fp XS sk LBk m -> bp_slots H e ff m -> bp_shad ff [20; 21]%nat m ->
    (forall (m' : mem) (y5 y6 y7 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
       winv H e ff fp XS sk LBk m' -> bp_slots H e ff m' -> bp_shad ff [19; 20; 21]%nat m' ->
       wtst0 ff m' Z24 Z24 Z24 -> wmono asegs m m' ->
       munch [(sh ff + 382, sh ff + 412); (wS1 e - AINTRIN_STACK, wS1 e); (ff + 3056, ff + 3296)] m m' ->
       evt asegs Q (MS (mkR (Z_to_bv 64 0xec200) (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) y5 y6 y7
                          (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e)) (Z_to_bv 64 (ff + 3224)) (Z_to_bv 64 25)
                          y12 y13 y14 y15 y16 y17
                          (Z_to_bv 64 (ff + 3056)) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) (Z_to_bv 64 (ff + 3224)) s6
                          (Z_to_bv 64 (ff + 3248)) (Z_to_bv 64 r) (Z_to_bv 64 (ff + 3272)) (Z_to_bv 64 32) s11
                          y28 y29 y30 y31)
                       F (Z_to_bv 64 0xec4ac) fc None m' (seg_rom asegs))) ->
    evt asegs Q (MS (mkR x1 (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) x5 x6 x7 (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
                       x10 x11 x12 x13 x14 x15 x16 x17 s2 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) s5 s6 s7 (Z_to_bv 64 r)
                       s9 s10 s11 x28 x29 x30 x31)
                    F (Z_to_bv 64 BP_WCF) fc None m (seg_rom asegs)).
  Proof.
    intros e ff fp XS sk LBk m Q x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 s2 s5 s6 s7 s9 s10 s11 x28 x29 x30 x31 F fc r
      HP HI SL SH K.
    pose proof (hdr_geo H e ff fp XS sk LBk m HP HI) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16).
    pose proof (wS1_facts H e HP) as (S32 & S1SP & S1L & SPH & LOS1 & _).
    pose proof SL as (SLa & SLb & SLc).
    pose proof (proj1 (rw_cells_app asegs m (wS1 e + 24) [C8 (wz (w_words e)); C8 (wz (w_n e)); C8 (wz ASHADOW_BASE)]
                  [C8 (wz (ff + 2224)); C8 (wz (ff + 3376))]) SLb) as (_ & SLd).
    pose proof (proj1 (rw_cells_app asegs m _ [C8 (wz (ff + 2224))] [C8 (wz (ff + 3376))]) SLd) as (SLe & _).
    assert (C48 : rw_cells asegs m (wS1 e + 48) [C8 (Z_to_bv 64 (ff + 2224))]).
    { replace (wS1 e + 48) with (wS1 e + 24 + Z.of_nat (cells_size [C8 (wz (w_words e)); C8 (wz (w_n e)); C8 (wz ASHADOW_BASE)]))
        by (cbn; lia). exact SLe. }
    assert (F0 : 0 <= ff) by lia.
    assert (FS : ff + 3296 <= wS1 e - AINTRIN_STACK) by (unfold AINTRIN_STACK; lia).
    eapply evt_cut.
    { exact (wu1 x1 (w_gp e) (w_tp e) x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 s2 s5 s6 s7 s9 s10 s11 x28 x29 x30 x31 F fc m
                 (wSP e) (wS1 e) ff r (w_lo e) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) G1 ltac:(lia) ltac:(lia) G9 C48 SH
                 (winv_stk H _ _ _ _ _ _ _ HI) (winv_mi H _ _ _ _ _ _ _ HI)). }
    intros ms1 (u5 & u6 & u7 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & m1 & EQ1 & MU1 & WM1 & MI1 & ST1 & US1).
    subst ms1.
    assert (HI1 : winv H e ff fp XS sk LBk m1).
    { eapply (winv_munch H HB); [exact HP | exact HI | exact MU1 | exact WM1 | exact MI1 | exact ST1 |].
      repeat apply Forall_cons; try apply Forall_nil. unfold wwin; cbn [fst snd]. right; right. lia. }
    assert (SL1 : bp_slots H e ff m1) by (apply (uk_slots e ff m m1 _ SL MU1 WM1); ukF).
    assert (SH1 : bp_shad ff [19; 20; 21]%nat m1) by exact US1.
    eapply (wms_ff H HB e ff fp XS sk LBk m1 Q) with (A := ff + 3056) (N := 240);
      [exact HP | exact HI1 | exact (uk_addr ff m1 F0 G1 SH1) | lia | unfold WO_FLAGP; lia | lia | lia | lia |].
    intros m2 a0 a1 a2 b1 b2 b3 b4 b5 b6 b7 c3 c4 c5 c6 HI2 MU2 WM2 Z2.
    rewrite (ret_pc_even WO_MS11_RA ltac:(unfold WO_MS11_RA; lia) eq_refl).
    assert (SL2 : bp_slots H e ff m2) by (apply (uk_slots e ff m1 m2 _ SL1 MU2 WM2); ukF).
    assert (SH2 : bp_shad ff [19; 20; 21]%nat m2) by (apply (uk_shad ff m1 m2 _ SH1 MU2 WM2); ukF).
    eapply evt_cut; [eapply wu2; lia |].
    intros ms3 (v5 & v6 & v7 & v13 & v14 & v15 & v16 & v17 & v28 & v29 & v30 & v31 & EQ3). subst ms3.
    eapply (wms_ff H HB e ff fp XS sk LBk m2 Q) with (A := ff + 3056) (N := 240);
      [exact HP | exact HI2 | exact (uk_addr ff m2 F0 G1 SH2) | lia | unfold WO_FLAGP; lia | lia | lia | lia |].
    intros m3 d0 d1 d2 e1 e2 e3 e4 e5 e6 e7 f3 f4 f5 f6 HI3 MU3 WM3 Z3.
    rewrite (ret_pc_even WO_MS12_RA ltac:(unfold WO_MS12_RA; lia) eq_refl).
    assert (SL3 : bp_slots H e ff m3) by (apply (uk_slots e ff m2 m3 _ SL2 MU3 WM3); ukF).
    assert (SH3 : bp_shad ff [19; 20; 21]%nat m3) by (apply (uk_shad ff m2 m3 _ SH2 MU3 WM3); ukF).
    pose proof (uk_wr e ff fp XS sk LBk m3 HI3) as W3. pose proof (winv_mi H _ _ _ _ _ _ _ HI3) as MI3.
    eapply evt_cut; [eapply wu3; first [exact W3 | exact MI3 | lia] |].
    intros ms4 (n5 & n6 & n7 & n13 & n14 & n15 & n16 & n17 & n28 & n29 & n30 & n31 & m4 & EQ4 & MU4 & WM4 & MI4 & C4). subst ms4.
    assert (HI4 : winv H e ff fp XS sk LBk m4).
    { eapply (winv_munch H HB); [exact HP | exact HI3 | exact MU4 | exact WM4 | exact MI4 | |].
      - apply (stk_keepW _ m3 m4 _ _ (winv_stk H _ _ _ _ _ _ _ HI3) MU4 WM4). unfold AIMG_TOP. lia.
      - repeat apply Forall_cons; try apply Forall_nil. unfold wwin, WO_FLAGP; cbn [fst snd]. right; left. lia. }
    assert (SL4 : bp_slots H e ff m4) by (apply (uk_slots e ff m3 m4 _ SL3 MU4 WM4); ukF).
    assert (SH4 : bp_shad ff [19; 20; 21]%nat m4) by (apply (uk_shad ff m3 m4 _ SH3 MU4 WM4); ukF).
    eapply (wms_ff H HB e ff fp XS sk LBk m4 Q) with (A := ff + 3056) (N := 240);
      [exact HP | exact HI4 | exact (uk_addr ff m4 F0 G1 SH4) | lia | unfold WO_FLAGP; lia | lia | lia | lia |].
    intros m5 g0 g1 g2 h1 h2 h3 h4 h5 h6 h7 i3 i4 i5 i6 HI5 MU5 WM5 Z5.
    rewrite (ret_pc_even WO_MS13_RA ltac:(unfold WO_MS13_RA; lia) eq_refl).
    assert (SL5 : bp_slots H e ff m5) by (apply (uk_slots e ff m4 m5 _ SL4 MU5 WM5); ukF).
    assert (SH5 : bp_shad ff [19; 20; 21]%nat m5) by (apply (uk_shad ff m4 m5 _ SH4 MU5 WM5); ukF).
    pose proof (uk_wr e ff fp XS sk LBk m5 HI5) as W5. pose proof (winv_mi H _ _ _ _ _ _ _ HI5) as MI5.
    eapply evt_cut; [eapply wu4; first [exact W5 | exact MI5 | lia] |].
    intros ms6 (o5 & o6 & o7 & o13 & o14 & o15 & o16 & o17 & o28 & o29 & o30 & o31 & m6 & EQ6 & MU6 & WM6 & MI6 & C6). subst ms6.
    assert (HI6 : winv H e ff fp XS sk LBk m6).
    { eapply (winv_munch H HB); [exact HP | exact HI5 | exact MU6 | exact WM6 | exact MI6 | |].
      - apply (stk_keepW _ m5 m6 _ _ (winv_stk H _ _ _ _ _ _ _ HI5) MU6 WM6). unfold AIMG_TOP. lia.
      - repeat apply Forall_cons; try apply Forall_nil. unfold wwin, WO_FLAGP; cbn [fst snd]. right; left. lia. }
    assert (SL6 : bp_slots H e ff m6) by (apply (uk_slots e ff m5 m6 _ SL5 MU6 WM6); ukF).
    assert (SH6 : bp_shad ff [19; 20; 21]%nat m6) by (apply (uk_shad ff m5 m6 _ SH5 MU6 WM6); ukF).
    eapply (wms_ff H HB e ff fp XS sk LBk m6 Q) with (A := ff + 3056) (N := 240);
      [exact HP | exact HI6 | exact (uk_addr ff m6 F0 G1 SH6) | lia | unfold WO_FLAGP; lia | lia | lia | lia |].
    intros m7 j0 j1 j2 k1 k2 k3 k4 k5 k6 k7 l3 l4 l5 l6 HI7 MU7 WM7 Z7.
    rewrite (ret_pc_even WO_MS14_RA ltac:(unfold WO_MS14_RA; lia) eq_refl).
    assert (SL7 : bp_slots H e ff m7) by (apply (uk_slots e ff m6 m7 _ SL6 MU7 WM7); ukF).
    assert (SH7 : bp_shad ff [19; 20; 21]%nat m7) by (apply (uk_shad ff m6 m7 _ SH6 MU7 WM7); ukF).
    pose proof (uk_wr e ff fp XS sk LBk m7 HI7) as W7. pose proof (winv_mi H _ _ _ _ _ _ _ HI7) as MI7.
    eapply evt_cut; [eapply wu5; first [exact W7 | exact MI7 | lia] |].
    intros ms8 (p5 & p6 & p7 & p13 & p14 & p15 & p16 & p17 & p28 & p29 & p30 & p31 & m8 & EQ8 & MU8 & WM8 & MI8 & C8). subst ms8.
    assert (HI8 : winv H e ff fp XS sk LBk m8).
    { eapply (winv_munch H HB); [exact HP | exact HI7 | exact MU8 | exact WM8 | exact MI8 | |].
      - apply (stk_keepW _ m7 m8 _ _ (winv_stk H _ _ _ _ _ _ _ HI7) MU8 WM8). unfold AIMG_TOP. lia.
      - repeat apply Forall_cons; try apply Forall_nil. unfold wwin, WO_FLAGP; cbn [fst snd]. right; left. lia. }
    assert (SL8 : bp_slots H e ff m8) by (apply (uk_slots e ff m7 m8 _ SL7 MU8 WM8); ukF).
    assert (SH8 : bp_shad ff [19; 20; 21]%nat m8) by (apply (uk_shad ff m7 m8 _ SH7 MU8 WM8); ukF).
    eapply (wms_ff H HB e ff fp XS sk LBk m8 Q) with (A := ff + 3056) (N := 240);
      [exact HP | exact HI8 | exact (uk_addr ff m8 F0 G1 SH8) | lia | unfold WO_FLAGP; lia | lia | lia | lia |].
    intros m9 q0 q1 q2 t1 t2 t3 t4 t5 t6 t7 z3 z4 z5 z6 HI9 MU9 WM9 Z9.
    rewrite (ret_pc_even WO_MS15_RA ltac:(unfold WO_MS15_RA; lia) eq_refl).
    assert (SL9 : bp_slots H e ff m9) by (apply (uk_slots e ff m8 m9 _ SL8 MU9 WM9); ukF).
    assert (SH9 : bp_shad ff [19; 20; 21]%nat m9) by (apply (uk_shad ff m8 m9 _ SH8 MU9 WM9); ukF).
    eapply evt_cut; [eapply wu6; lia |].
    intros ms10 (y5 & y6 & y7 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & y12 & EQ10). subst ms10.
    pose proof (uk_fill ff (wS1 e) m1 m2 m3 m4 m5 m6 m7 m8 m9 F0 FS MU2 WM2 Z2 MU3 WM3 Z3 MU4 WM4 C4 MU5 WM5 Z5
                  MU6 WM6 C6 MU7 WM7 Z7 MU8 WM8 C8 MU9 WM9 Z9) as (TS & MUf & WMf).
    pose proof (munch_app _ _ _ _ _ MU1 MUf) as MUa. cbn [app] in MUa.
    apply K; [exact HI9 | exact SL9 | exact SH9 | exact TS | exact (wmono_trans asegs _ _ _ WM1 WMf) | exact MUa].
  Qed.
End WoUK.
