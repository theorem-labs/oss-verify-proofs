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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_PrsStmt LbB_SR LbB_Conv LbB_WoGen LbB_WoDefs LbB_WoKit LbB_WoSt LbB_WoMs.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_WoR2 LbB_WoR3 LbB_WoE0.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Lemma wo_pad : forall m ff, u8arr asegs m (sh ff) (map (Z_to_bv 8) WO_SH2C) -> ff mod 64 = 0 -> 0 <= ff ->
  addressable m (ff + 3456) 288.
Proof.
  intros m ff U F64 F0. split; [lia|]. split; [lia|]. split; [clear - F64; Z.div_mod_to_equations; lia|].
  pose proof (u8arr_sub m (sh ff) _ 432 36 U ltac:(lia) ltac:(lia) ltac:(rewrite length_map; cbn; lia)) as X.
  replace (sh (ff + 3456)) with (sh ff + 432) by (rewrite <- (sh_add8 ff 432); f_equal).
  replace (shadow_of 288) with (firstn (Z.to_nat 36) (skipn (Z.to_nat 432) (map (Z_to_bv 8) WO_SH2C))) by (vm_compute; reflexivity).
  exact X.
Qed.
Lemma wo_cad : forall m ff, u8arr asegs m (sh ff) (map (Z_to_bv 8) WO_SH2C) -> ff mod 64 = 0 -> 0 <= ff ->
  addressable m (ff + 3376) 48.
Proof.
  intros m ff U F64 F0. split; [lia|]. split; [lia|]. split; [clear - F64; Z.div_mod_to_equations; lia|].
  pose proof (u8arr_sub m (sh ff) _ 422 6 U ltac:(lia) ltac:(lia) ltac:(rewrite length_map; cbn; lia)) as X.
  replace (sh (ff + 3376)) with (sh ff + 422) by (rewrite <- (sh_add8 ff 422); f_equal).
  replace (shadow_of 48) with (firstn (Z.to_nat 6) (skipn (Z.to_nat 422) (map (Z_to_bv 8) WO_SH2C))) by (vm_compute; reflexivity).
  exact X.
Qed.

Ltac wtr C MU WM := eapply rw_cells_transport; [exact C | exact MU | exact WM | cbn; unfold AINTRIN_STACK in *; lia].

Section E0b.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps_bp H.

  Definition e0_post (e : went H) : machine_state -> Prop :=
    fun ms' => exists (ff fp : Z) x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m',
      ms' = MS (mkR (Z_to_bv 64 WO_ON1_RA) (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) x5 x6 x7 (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
                    (Z_to_bv 64 (ff + 3672)) (Z_to_bv 64 25) x12 x13 x14 x15 x16 x17
                    (Z_to_bv 64 (ff + 3456)) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) (Z_to_bv 64 (ff + 3720)) (Z_to_bv 64 (ff + 3504))
                    (Z_to_bv 64 0x3f800000) (Z_to_bv 64 0) (Z_to_bv 64 (ff + 3672)) (Z_to_bv 64 (ff + 3696)) (Z_to_bv 64 (ff + 2752))
                    x28 x29 x30 x31)
               (w_F e) (Z_to_bv 64 0xec4ac) (w_fc e) None m' (seg_rom asegs)
      /\ winv H e ff fp [] (w_s e) (w_LB e) m'
      /\ wfc H e ff m'
      /\ rw_cells asegs m' (ff + 3504) [CB 46 (poison_bytes 46 0)] /\ st_maps_cells m' (ff + 3504)
      /\ rw_cells asegs m' (ff + 3672) [CB 72 (poison_bytes 72 0)].

  Lemma e0b : forall (e : went H) ms, wpre H e -> e0a_post H e ms -> evt asegs (e0_post e) ms.
  Proof.
    intros e ms HP P0. destruct P0 as (ff & fp & x5 & x6 & x7 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m0 & EQ0 & HI0 & WC0).
    subst ms.
    pose proof (rt_bp_base H HH) as HB.
    pose proof (wpre_geo H e HP) as (CE & LO & SSHI & SHIH & SP16 & TP).
    pose proof (wS1_facts H e HP) as (S32 & S1SP & S1L & SPH & LOS1 & _).
    pose proof (winv_ff H _ _ _ _ _ _ _ HI0) as FFR.
    pose proof (wframe_facts H _ _ _ FFR) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16).
    pose proof aceil_facts as ACF.
    set (SP := wSP e) in *. set (S1 := wS1 e) in *. set (lo := w_lo e) in *.
    assert (WFW : forall m a n, winv H e ff fp [] (w_s e) (w_LB e) m -> ff <= a -> a + n <= ff + WO_FLAGP -> wr_at asegs m a n).
    { intros m a n HI X1 X2. pose proof (winv_wf H _ _ _ _ _ _ _ HI) as (W0 & W1 & W). unfold WO_FLAGP in *.
      split; [lia|]. split; [lia|]. intros i Hi. replace (a + i) with (ff + (a - ff + i)) by lia. apply W. lia. }
    assert (WFM : forall m m' W, wfc H e ff m -> munch W m m' -> wmono asegs m m' -> Forall (wfc_apart H e ff) W -> wfc H e ff m')
      by (intros; eapply wfc_munch; eassumption).
    assert (PADm : forall m, wfc H e ff m -> addressable m (ff + 3456) 288)
      by (intros m (_ & _ & _ & _ & _ & U & _); exact (wo_pad m ff U F3 ltac:(lia))).

    eapply (wms_ff H HB e ff fp [] (w_s e) (w_LB e) m0); [exact HP | exact HI0 | exact (PADm m0 WC0) | lia | unfold WO_FLAGP; lia | lia | lia | lia |].
    intros m1 y0 y1 y2 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 HI1 MU1 WM1 Z1.
    rewrite (ret_pc_even WO_MS1_RA ltac:(unfold WO_MS1_RA; lia) eq_refl).
    assert (WC1 : wfc H e ff m1) by (eapply WFM; [exact WC0 | exact MU1 | exact WM1 |]; unfold wfc_apart, AINTRIN_STACK;
                                     repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia).

    eapply evt_cut.
    { eapply wr1 with (ff := ff) (lo := lo) (SP := SP) (m := m1);
        [lia | lia | exact (winv_stk H _ _ _ _ _ _ _ HI1) | exact (winv_mi H _ _ _ _ _ _ _ HI1)]. }
    intros ms2 (z5 & z6 & z7 & z13 & z14 & z15 & z16 & z17 & z28 & z29 & z30 & z31 & m2 & EQ2 & MU2 & WM2 & MI2 & ST2). subst ms2.
    assert (HI2 : winv H e ff fp [] (w_s e) (w_LB e) m2)
      by (eapply (winv_munch H HB); [exact HP | exact HI1 | exact MU2 | exact WM2 | exact MI2 | exact ST2 | apply Forall_nil]).
    assert (WC2 : wfc H e ff m2) by (eapply WFM; [exact WC1 | exact MU2 | exact WM2 | apply Forall_nil]).

    eapply (wms_ff H HB e ff fp [] (w_s e) (w_LB e) m2); [exact HP | exact HI2 | exact (PADm m2 WC2) | lia | unfold WO_FLAGP; lia | lia | lia | lia |].
    intros m3 u0 u1 u2 u11 u12 u13 u14 u15 u16 u17 u28 u29 u30 u31 HI3 MU3 WM3 Z3.
    rewrite (ret_pc_even WO_MS2_RA ltac:(unfold WO_MS2_RA; lia) eq_refl).
    assert (WC3 : wfc H e ff m3) by (eapply WFM; [exact WC2 | exact MU3 | exact WM3 |]; unfold wfc_apart, AINTRIN_STACK;
                                     repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia).

    eapply evt_cut.
    { eapply wr2 with (ff := ff) (lo := lo) (SP := SP) (m := m3);
        [lia | lia | exact (WFW m3 (ff + 3584) 4 HI3 ltac:(lia) ltac:(unfold WO_FLAGP; lia))
        | exact (winv_stk H _ _ _ _ _ _ _ HI3) | exact (winv_mi H _ _ _ _ _ _ _ HI3)]. }
    intros ms4 (v5 & v6 & v7 & v13 & v14 & v15 & v16 & v17 & v28 & v29 & v30 & v31 & m4 & EQ4 & MU4 & WM4 & MI4 & ST4 & CF4). subst ms4.
    assert (HI4 : winv H e ff fp [] (w_s e) (w_LB e) m4).
    { eapply (winv_munch H HB); [exact HP | exact HI3 | exact MU4 | exact WM4 | exact MI4 | exact ST4 |].
      unfold wwin, WO_FLAGP, WO_SAVED. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]. right; left. lia. }
    assert (WC4 : wfc H e ff m4) by (eapply WFM; [exact WC3 | exact MU4 | exact WM4 |]; unfold wfc_apart;
                                     repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia).

    eapply (wms_ff H HB e ff fp [] (w_s e) (w_LB e) m4); [exact HP | exact HI4 | exact (PADm m4 WC4) | lia | unfold WO_FLAGP; lia | lia | lia | lia |].
    intros m5 w0 w1 w2 w11 w12 w13 w14 w15 w16 w17 w28 w29 w30 w31 HI5 MU5 WM5 Z5.
    rewrite (ret_pc_even WO_MS3_RA ltac:(unfold WO_MS3_RA; lia) eq_refl).
    assert (WC5 : wfc H e ff m5) by (eapply WFM; [exact WC4 | exact MU5 | exact WM5 |]; unfold wfc_apart, AINTRIN_STACK;
                                     repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia).

    eapply evt_cut.
    { eapply wr3 with (ff := ff) (lo := lo) (SP := SP) (m := m5);
        [lia | lia | exact (WFW m5 (ff + 3624) 4 HI5 ltac:(lia) ltac:(unfold WO_FLAGP; lia))
        | exact (winv_stk H _ _ _ _ _ _ _ HI5) | exact (winv_mi H _ _ _ _ _ _ _ HI5)]. }
    intros ms6 (k5 & k6 & k7 & k13 & k14 & k15 & k16 & k17 & k28 & k29 & k30 & k31 & m6 & EQ6 & MU6 & WM6 & MI6 & ST6 & CF6). subst ms6.
    assert (HI6 : winv H e ff fp [] (w_s e) (w_LB e) m6).
    { eapply (winv_munch H HB); [exact HP | exact HI5 | exact MU6 | exact WM6 | exact MI6 | exact ST6 |].
      unfold wwin, WO_FLAGP, WO_SAVED. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]. right; left. lia. }
    assert (WC6 : wfc H e ff m6) by (eapply WFM; [exact WC5 | exact MU6 | exact WM6 |]; unfold wfc_apart;
                                     repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia).

    eapply (wms_ff H HB e ff fp [] (w_s e) (w_LB e) m6); [exact HP | exact HI6 | exact (PADm m6 WC6) | lia | unfold WO_FLAGP; lia | lia | lia | lia |].
    intros m7 c0 c1 c2 c11 c12 c13 c14 c15 c16 c17 c28 c29 c30 c31 HI7 MU7 WM7 Z7.
    rewrite (ret_pc_even WO_MS4_RA ltac:(unfold WO_MS4_RA; lia) eq_refl).
    assert (WC7 : wfc H e ff m7) by (eapply WFM; [exact WC6 | exact MU7 | exact WM7 |]; unfold wfc_apart, AINTRIN_STACK;
                                     repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia).

    eapply evt_cut.
    { eapply wr4 with (ff := ff) (lo := lo) (SP := SP) (m := m7);
        [lia | lia | exact (WFW m7 (ff + 3664) 4 HI7 ltac:(lia) ltac:(unfold WO_FLAGP; lia))
        | exact (winv_stk H _ _ _ _ _ _ _ HI7) | exact (winv_mi H _ _ _ _ _ _ _ HI7)]. }
    intros ms8 (d5 & d6 & d7 & d13 & d14 & d15 & d16 & d17 & d28 & d29 & d30 & d31 & m8 & EQ8 & MU8 & WM8 & MI8 & ST8 & CF8). subst ms8.
    assert (HI8 : winv H e ff fp [] (w_s e) (w_LB e) m8).
    { eapply (winv_munch H HB); [exact HP | exact HI7 | exact MU8 | exact WM8 | exact MI8 | exact ST8 |].
      unfold wwin, WO_FLAGP, WO_SAVED. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]. right; left. lia. }
    assert (WC8 : wfc H e ff m8) by (eapply WFM; [exact WC7 | exact MU8 | exact WM8 |]; unfold wfc_apart;
                                     repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia).

    eapply (wms_ff H HB e ff fp [] (w_s e) (w_LB e) m8); [exact HP | exact HI8 | exact (PADm m8 WC8) | lia | unfold WO_FLAGP; lia | lia | lia | lia |].
    intros m9 g0 g1 g2 g11 g12 g13 g14 g15 g16 g17 g28 g29 g30 g31 HI9 MU9 WM9 Z9.
    rewrite (ret_pc_even WO_MS5_RA ltac:(unfold WO_MS5_RA; lia) eq_refl).
    assert (WC9 : wfc H e ff m9) by (eapply WFM; [exact WC8 | exact MU9 | exact WM9 |]; unfold wfc_apart, AINTRIN_STACK;
                                     repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia).

    eapply evt_cut.
    { eapply wr5 with (ff := ff) (lo := lo) (SP := SP) (m := m9);
        [lia | lia | exact (winv_stk H _ _ _ _ _ _ _ HI9) | exact (winv_mi H _ _ _ _ _ _ _ HI9)]. }
    intros ms10 (h5 & h6 & h7 & h12 & h13 & h14 & h15 & h16 & h17 & h28 & h29 & h30 & h31 & m10 & EQ10 & MU10 & WM10 & MI10 & ST10).
    subst ms10. apply evt_done.
    assert (HI10 : winv H e ff fp [] (w_s e) (w_LB e) m10)
      by (eapply (winv_munch H HB); [exact HP | exact HI9 | exact MU10 | exact WM10 | exact MI10 | exact ST10 | apply Forall_nil]).
    exists ff, fp, h5, h6, h7, h12, h13, h14, h15, h16, h17, h28, h29, h30, h31, m10. split; [reflexivity|].
    split; [exact HI10|].
    split; [eapply WFM; [exact WC9 | exact MU10 | exact WM10 | apply Forall_nil]|].

    pose proof (munch_app _ _ _ _ _ MU9 MU10) as M9. pose proof (wmono_trans asegs _ _ _ WM9 WM10) as V9.
    pose proof (munch_app _ _ _ _ _ MU8 M9) as M8. pose proof (wmono_trans asegs _ _ _ WM8 V9) as V8.
    pose proof (munch_app _ _ _ _ _ MU7 M8) as M7. pose proof (wmono_trans asegs _ _ _ WM7 V8) as V7.
    pose proof (munch_app _ _ _ _ _ MU6 M7) as M6. pose proof (wmono_trans asegs _ _ _ WM6 V7) as V6.
    pose proof (munch_app _ _ _ _ _ MU5 M6) as M5. pose proof (wmono_trans asegs _ _ _ WM5 V6) as V5.
    pose proof (munch_app _ _ _ _ _ MU4 M5) as M4. pose proof (wmono_trans asegs _ _ _ WM4 V5) as V4.
    pose proof (munch_app _ _ _ _ _ MU3 M4) as M3. pose proof (wmono_trans asegs _ _ _ WM3 V4) as V3.
    pose proof (munch_app _ _ _ _ _ MU2 M3) as M2. pose proof (wmono_trans asegs _ _ _ WM2 V3) as V2.
    cbn [app] in M2, M3, M4, M5, M6, M7, M8, M9.
    split; [wtr Z1 M2 V2|].
    split.
    { unfold st_maps_cells.
      replace (ff + 3504 + 48) with (ff + 3552) by lia. replace (ff + 3504 + 80) with (ff + 3584) by lia.
      replace (ff + 3504 + 88) with (ff + 3592) by lia. replace (ff + 3504 + 120) with (ff + 3624) by lia.
      replace (ff + 3504 + 128) with (ff + 3632) by lia. replace (ff + 3504 + 160) with (ff + 3664) by lia.
      split; [wtr Z3 M4 V4|]. split; [wtr CF4 M5 V5|]. split; [wtr Z5 M6 V6|]. split; [wtr CF6 M7 V7|].
      split; [wtr Z7 M8 V8|]. wtr CF8 M9 V9. }
    eapply rw_cells_transport; [exact Z9 | exact MU10 | exact WM10 | exact I].
  Qed.
End E0b.
