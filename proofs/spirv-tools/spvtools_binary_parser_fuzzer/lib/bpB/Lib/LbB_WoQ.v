(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 BsWalk RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_PrsStmt LbB_SR LbB_Conv LbB_WoGen LbB_WoDefs LbB_WoKit LbB_WoSt LbB_WoMs LbB_WoCall LbB_WoCut LbB_WoZ.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_ResvB LbB_WoR2 LbB_WoR4 LbB_WoR5 LbB_WoVec.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Lemma z72_split : forall m a, rw_cells asegs m a [CB 72 (poison_bytes 72 0)] ->
  rw_cells asegs m a Z24 /\ rw_cells asegs m (a + 24) Z24 /\ rw_cells asegs m (a + 48) Z24.
Proof.
  intros m a C. unfold Z24.
  split; [replace a with (a + 0) by lia; apply (zero_cells_sub m a 72 0 24 C); lia|].
  split; apply (zero_cells_sub m a 72 _ 24 C); lia.
Qed.

Section WoQ.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHb : asan_rt_hyps_bp H.
  Let HB := rt_bp_base H HHb.

  Lemma munch_nil_eqQ : forall (m m' : mem), munch [] m m' -> m' = m.
  Proof. intros m m' MU. apply functional_extensionality. intros x. apply MU. exact I. Qed.

  Lemma maps_fill : forall (ff S1 : Z) (m7 m8 m9 m10 m11 m12 m13 m14 m15 : mem),
    0 <= ff -> ff + 2992 <= S1 - AINTRIN_STACK ->
    munch [(ff + 2800, ff + 2800 + 32); (S1 - AINTRIN_STACK, S1)] m7 m8 -> wmono asegs m7 m8 ->
    rw_cells asegs m8 (ff + 2800) [CB (Z.to_nat 32) (poison_bytes (Z.to_nat 32) 0)] ->
    munch [(ff + 2832, ff + 2836)] m8 m9 -> wmono asegs m8 m9 -> rw_cells asegs m9 (ff + 2832) [C4 (Z_to_bv 64 0x3f800000)] ->
    munch [(ff + 2840, ff + 2840 + 32); (S1 - AINTRIN_STACK, S1)] m9 m10 -> wmono asegs m9 m10 ->
    rw_cells asegs m10 (ff + 2840) [CB (Z.to_nat 32) (poison_bytes (Z.to_nat 32) 0)] ->
    munch [(ff + 2872, ff + 2876)] m10 m11 -> wmono asegs m10 m11 -> rw_cells asegs m11 (ff + 2872) [C4 (Z_to_bv 64 0x3f800000)] ->
    munch [(ff + 2880, ff + 2880 + 32); (S1 - AINTRIN_STACK, S1)] m11 m12 -> wmono asegs m11 m12 ->
    rw_cells asegs m12 (ff + 2880) [CB (Z.to_nat 32) (poison_bytes (Z.to_nat 32) 0)] ->
    munch [(ff + 2912, ff + 2916)] m12 m13 -> wmono asegs m12 m13 -> rw_cells asegs m13 (ff + 2912) [C4 (Z_to_bv 64 0x3f800000)] ->
    munch [(ff + 2920, ff + 2920 + 72); (S1 - AINTRIN_STACK, S1)] m13 m14 -> wmono asegs m13 m14 ->
    rw_cells asegs m14 (ff + 2920) [CB (Z.to_nat 72) (poison_bytes (Z.to_nat 72) 0)] ->
    munch [] m14 m15 -> wmono asegs m14 m15 ->
    st_maps_cells m15 (ff + 2752) /\ rw_cells asegs m15 (ff + 2920) [CB 72 (poison_bytes 72 0)]
    /\ munch [(S1 - AINTRIN_STACK, S1); (ff + 2800, ff + 2992)] m7 m15 /\ wmono asegs m7 m15.
  Proof.
    intros ff S1 m7 m8 m9 m10 m11 m12 m13 m14 m15 F0 FS MU8 WM8 Z8 MU9 WM9 C9 MU10 WM10 Z10 MU11 WM11 C11
      MU12 WM12 Z12 MU13 WM13 C13 MU14 WM14 Z14 MU15 WM15.
    pose proof (munch_app _ _ _ _ _ MU14 MU15) as S14. pose proof (wmono_trans asegs _ _ _ WM14 WM15) as U14.
    pose proof (munch_app _ _ _ _ _ MU13 S14) as S13. pose proof (wmono_trans asegs _ _ _ WM13 U14) as U13.
    pose proof (munch_app _ _ _ _ _ MU12 S13) as S12. pose proof (wmono_trans asegs _ _ _ WM12 U13) as U12.
    pose proof (munch_app _ _ _ _ _ MU11 S12) as S11. pose proof (wmono_trans asegs _ _ _ WM11 U12) as U11.
    pose proof (munch_app _ _ _ _ _ MU10 S11) as S10. pose proof (wmono_trans asegs _ _ _ WM10 U11) as U10.
    pose proof (munch_app _ _ _ _ _ MU9 S10) as S9. pose proof (wmono_trans asegs _ _ _ WM9 U10) as U9.
    pose proof (munch_app _ _ _ _ _ MU8 S9) as S8. pose proof (wmono_trans asegs _ _ _ WM8 U9) as U8.
    cbn [app] in S8, S9, S10, S11, S12, S13, S14.
    unfold AINTRIN_STACK in *.
    split; [|split; [|split; [eapply munch_in2; [exact S8 | repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia] | exact U8]]].
    - unfold st_maps_cells; refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
      + replace (ff + 2752 + 48) with (ff + 2800) by lia. eapply rw_cells_transport; [exact Z8 | exact S9 | exact U9 | cbn; lia].
      + replace (ff + 2752 + 80) with (ff + 2832) by lia. eapply rw_cells_transport; [exact C9 | exact S10 | exact U10 | cbn; lia].
      + replace (ff + 2752 + 88) with (ff + 2840) by lia. eapply rw_cells_transport; [exact Z10 | exact S11 | exact U11 | cbn; lia].
      + replace (ff + 2752 + 120) with (ff + 2872) by lia. eapply rw_cells_transport; [exact C11 | exact S12 | exact U12 | cbn; lia].
      + replace (ff + 2752 + 128) with (ff + 2880) by lia. eapply rw_cells_transport; [exact Z12 | exact S13 | exact U13 | cbn; lia].
      + replace (ff + 2752 + 160) with (ff + 2912) by lia. eapply rw_cells_transport; [exact C13 | exact S14 | exact U14 | cbn; lia].
    - eapply rw_cells_transport; [exact Z14 | exact MU15 | exact WM15 | exact I].
  Qed.

  Definition wp3t_pre (e : went H) (ff : Z) (m : mem) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s8 s9 s10 t3 t4 t5 t6 : word)
      : machine_state :=
    MS (mkR (Z_to_bv 64 WO_MS6_RA) (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) t0 t1 t2 (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
            a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 (ff + 2800)) s6 (Z_to_bv 64 0x3f800000) s8 s9 s10 (Z_to_bv 64 (ff + 2752))
            t3 t4 t5 t6)
       (w_F e) (Z_to_bv 64 WO_MS6_RA) (w_fc e) None m (seg_rom asegs).

  Definition wp3t_post (e : went H) (ff fp : Z) (XSc : list (Z * Z)) (sk : as_St H) (LBk : list block) (m : mem)
      (s2 s3 s4 s6 s10 : word) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m',
      ms' = MS (mkR (Z_to_bv 64 WO_ON4_RA) (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) x5 x6 x7 (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
                    (Z_to_bv 64 (ff + 2920)) (Z_to_bv 64 25) x12 x13 x14 x15 x16 x17
                    s2 s3 s4 (Z_to_bv 64 (ff + 2920)) s6 (Z_to_bv 64 0x3f800000) (Z_to_bv 64 (ff + 2944)) (Z_to_bv 64 (ff + 2968)) s10
                    (Z_to_bv 64 (ff + 2752)) x28 x29 x30 x31)
               (w_F e) (Z_to_bv 64 RESV_OPND_ENTRY) (w_fc e) None m' (seg_rom asegs)
      /\ winv H e ff fp XSc sk LBk m'
      /\ munch [(wS1 e - AINTRIN_STACK, wS1 e); (ff + 2800, ff + 2992)] m m' /\ wmono asegs m m'
      /\ st_maps_cells m' (ff + 2752) /\ rw_cells asegs m' (ff + 2920) [CB 72 (poison_bytes 72 0)].

  Lemma wp3t : forall (e : went H) ff fp XSc sk LBk m (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s8 s9 s10 t3 t4 t5 t6 : word),
    wpre H e -> winv H e ff fp XSc sk LBk m -> addressable m (ff + 2752) 240 ->
    evt asegs (wp3t_post e ff fp XSc sk LBk m s2 s3 s4 s6 s10)
      (wp3t_pre e ff m t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s8 s9 s10 t3 t4 t5 t6).
  Proof.
    intros e ff fp XSc sk LBk m t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s8 s9 s10 t3 t4 t5 t6 HP HI AD.
    destruct (wframe_bounds H e ff fp XSc sk LBk m HP HI) as (F0 & F64 & FLO & FH & FL & FS & SH1 & SH2 & S1L & S1SP & SPH & LOS1).
    assert (F32 : ff mod 32 = 0) by (clear - F64; Z.div_mod_to_equations; lia).
    assert (FH' : ff + 3808 <= 2 ^ 47) by lia.
    assert (WFW : forall mm, winv H e ff fp XSc sk LBk mm -> wr_at asegs mm (ff + 2752) 240).
    { intros mm HI'. pose proof (winv_wf H _ _ _ _ _ _ _ HI') as (W0 & W1 & W).
      split; [lia|]. split; [lia|]. intros i Hi. replace (ff + 2752 + i) with (ff + (2752 + i)) by lia. apply W. lia. }
    assert (SHA : sh (ff + 2752) = sh ff + 344) by (unfold sh; Z.div_mod_to_equations; lia).
    unfold wp3t_pre.
    eapply evt_cut.
    { exact (wt1 (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) t0 t1 t2 (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
                 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 (Z_to_bv 64 0x3f800000) s8 s9 s10 (Z_to_bv 64 (ff + 2752)) t3 t4 t5 t6
                 (w_F e) (w_fc e) m ff (w_lo e) (wSP e) F0 FH' (winv_stk H _ _ _ _ _ _ _ HI) (winv_mi H _ _ _ _ _ _ _ HI)). }
    intros ms1 (i5 & i6 & i7 & i13 & i14 & i15 & i16 & i17 & i28 & i29 & i30 & i31 & m1 & EQ1 & MU1 & _ & _ & _). subst ms1.
    pose proof (munch_nil_eqQ m m1 MU1) as E1. subst m1.

    eapply (wms_ff H HB e ff fp XSc sk LBk m _ (Z_to_bv 64 WO_MS7_RA) i5 i6 i7 (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
              i13 i14 i15 i16 i17 s2 s3 s4 (Z_to_bv 64 (ff + 2800)) s6 (Z_to_bv 64 0x3f800000) s8 s9 s10 (Z_to_bv 64 (ff + 2752))
              i28 i29 i30 i31 (ff + 2752) 240 (ff + 2800) 32 (w_F e) (w_fc e));
      [exact HP | exact HI | exact AD | lia | lia | lia | lia | lia |].
    intros m8 j0 j1 j2 j11 j12 j13 j14 j15 j16 j17 j28 j29 j30 j31 HI8 MU8 WM8 Z8.
    rewrite (ret_pc_even WO_MS7_RA ltac:(unfold WO_MS7_RA; lia) eq_refl).
    assert (AD8 : addressable m8 (ff + 2752) 240)
      by (eapply addressable_transport; [exact AD | exact MU8 | exact WM8 | rewrite SHA; change (nsh 240) with 30; cbn [disjoint_from]; unfold AINTRIN_STACK in *; lia]).
    eapply evt_cut.
    { exact (wt2 (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) j0 j1 j2 (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
                 (Z_to_bv 64 (ff + 2800)) j11 j12 j13 j14 j15 j16 j17 s2 s3 s4 (Z_to_bv 64 (ff + 2800)) s6 s8 s9 s10 j28 j29 j30 j31
                 (w_F e) (w_fc e) m8 ff (w_lo e) (wSP e) F0 FH' (WFW m8 HI8) (winv_stk H _ _ _ _ _ _ _ HI8) (winv_mi H _ _ _ _ _ _ _ HI8)). }
    intros ms9 (n5 & n6 & n7 & n13 & n14 & n15 & n16 & n17 & n28 & n29 & n30 & n31 & m9 & EQ9 & MU9 & WM9 & MI9 & ST9 & C9). subst ms9.
    assert (HI9 : winv H e ff fp XSc sk LBk m9).
    { eapply (winv_munch H HB); [exact HP | exact HI8 | exact MU9 | exact WM9 | exact MI9 | exact ST9 |].
      unfold wwin. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]. right; left. lia. }
    assert (AD9 : addressable m9 (ff + 2752) 240)
      by (eapply addressable_transport; [exact AD8 | exact MU9 | exact WM9 | rewrite SHA; change (nsh 240) with 30; cbn [disjoint_from]; unfold AINTRIN_STACK in *; lia]).

    eapply (wms_ff H HB e ff fp XSc sk LBk m9 _ (Z_to_bv 64 WO_MS8_RA) n5 n6 n7 (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
              n13 n14 n15 n16 n17 s2 s3 s4 (Z_to_bv 64 (ff + 2800)) s6 (Z_to_bv 64 0x3f800000) s8 s9 s10 (Z_to_bv 64 (ff + 2752))
              n28 n29 n30 n31 (ff + 2752) 240 (ff + 2840) 32 (w_F e) (w_fc e));
      [exact HP | exact HI9 | exact AD9 | lia | lia | lia | lia | lia |].
    intros m10 o0 o1 o2 o11 o12 o13 o14 o15 o16 o17 o28 o29 o30 o31 HI10 MU10 WM10 Z10.
    rewrite (ret_pc_even WO_MS8_RA ltac:(unfold WO_MS8_RA; lia) eq_refl).
    assert (AD10 : addressable m10 (ff + 2752) 240)
      by (eapply addressable_transport; [exact AD9 | exact MU10 | exact WM10 | rewrite SHA; change (nsh 240) with 30; cbn [disjoint_from]; unfold AINTRIN_STACK in *; lia]).
    eapply evt_cut.
    { exact (wt3 (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) o0 o1 o2 (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
                 (Z_to_bv 64 (ff + 2840)) o11 o12 o13 o14 o15 o16 o17 s2 s3 s4 (Z_to_bv 64 (ff + 2800)) s6 s8 s9 s10 o28 o29 o30 o31
                 (w_F e) (w_fc e) m10 ff (w_lo e) (wSP e) F0 FH' (WFW m10 HI10) (winv_stk H _ _ _ _ _ _ _ HI10) (winv_mi H _ _ _ _ _ _ _ HI10)). }
    intros ms11 (q5 & q6 & q7 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & m11 & EQ11 & MU11 & WM11 & MI11 & ST11 & C11). subst ms11.
    assert (HI11 : winv H e ff fp XSc sk LBk m11).
    { eapply (winv_munch H HB); [exact HP | exact HI10 | exact MU11 | exact WM11 | exact MI11 | exact ST11 |].
      unfold wwin. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]. right; left. lia. }
    assert (AD11 : addressable m11 (ff + 2752) 240)
      by (eapply addressable_transport; [exact AD10 | exact MU11 | exact WM11 | rewrite SHA; change (nsh 240) with 30; cbn [disjoint_from]; unfold AINTRIN_STACK in *; lia]).

    eapply (wms_ff H HB e ff fp XSc sk LBk m11 _ (Z_to_bv 64 WO_MS9_RA) q5 q6 q7 (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
              q13 q14 q15 q16 q17 s2 s3 s4 (Z_to_bv 64 (ff + 2800)) s6 (Z_to_bv 64 0x3f800000) s8 s9 s10 (Z_to_bv 64 (ff + 2752))
              q28 q29 q30 q31 (ff + 2752) 240 (ff + 2880) 32 (w_F e) (w_fc e));
      [exact HP | exact HI11 | exact AD11 | lia | lia | lia | lia | lia |].
    intros m12 g0 g1 g2 g11 g12 g13 g14 g15 g16 g17 g28 g29 g30 g31 HI12 MU12 WM12 Z12.
    rewrite (ret_pc_even WO_MS9_RA ltac:(unfold WO_MS9_RA; lia) eq_refl).
    assert (AD12 : addressable m12 (ff + 2752) 240)
      by (eapply addressable_transport; [exact AD11 | exact MU12 | exact WM12 | rewrite SHA; change (nsh 240) with 30; cbn [disjoint_from]; unfold AINTRIN_STACK in *; lia]).
    eapply evt_cut.
    { exact (wt4 (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) g0 g1 g2 (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
                 (Z_to_bv 64 (ff + 2880)) g11 g12 g13 g14 g15 g16 g17 s2 s3 s4 (Z_to_bv 64 (ff + 2800)) s6 s8 s9 s10 g28 g29 g30 g31
                 (w_F e) (w_fc e) m12 ff (w_lo e) (wSP e) F0 FH' (WFW m12 HI12) (winv_stk H _ _ _ _ _ _ _ HI12) (winv_mi H _ _ _ _ _ _ _ HI12)). }
    intros ms13 (h5 & h6 & h7 & h13 & h14 & h15 & h16 & h17 & h28 & h29 & h30 & h31 & m13 & EQ13 & MU13 & WM13 & MI13 & ST13 & C13). subst ms13.
    assert (HI13 : winv H e ff fp XSc sk LBk m13).
    { eapply (winv_munch H HB); [exact HP | exact HI12 | exact MU13 | exact WM13 | exact MI13 | exact ST13 |].
      unfold wwin. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]. right; left. lia. }
    assert (AD13 : addressable m13 (ff + 2752) 240)
      by (eapply addressable_transport; [exact AD12 | exact MU13 | exact WM13 | rewrite SHA; change (nsh 240) with 30; cbn [disjoint_from]; unfold AINTRIN_STACK in *; lia]).

    eapply (wms_ff H HB e ff fp XSc sk LBk m13 _ (Z_to_bv 64 WO_MS10_RA) h5 h6 h7 (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
              h13 h14 h15 h16 h17 s2 s3 s4 (Z_to_bv 64 (ff + 2920)) s6 (Z_to_bv 64 0x3f800000) (Z_to_bv 64 (ff + 2944))
              (Z_to_bv 64 (ff + 2968)) s10 (Z_to_bv 64 (ff + 2752))
              h28 h29 h30 h31 (ff + 2752) 240 (ff + 2920) 72 (w_F e) (w_fc e));
      [exact HP | exact HI13 | exact AD13 | lia | lia | lia | lia | lia |].
    intros m14 f0 f1 f2 f11 f12 f13 f14 f15 f16 f17 f28 f29 f30 f31 HI14 MU14 WM14 Z14.
    rewrite (ret_pc_even WO_MS10_RA ltac:(unfold WO_MS10_RA; lia) eq_refl).
    eapply evt_cut.
    { exact (wt5 (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) f0 f1 f2 (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
                 (Z_to_bv 64 (ff + 2920)) f11 f12 f13 f14 f15 f16 f17 s2 s3 s4 s6 (Z_to_bv 64 0x3f800000) (Z_to_bv 64 (ff + 2944))
                 (Z_to_bv 64 (ff + 2968)) s10 (Z_to_bv 64 (ff + 2752)) f28 f29 f30 f31
                 (w_F e) (w_fc e) m14 ff (w_lo e) (wSP e) F0 FH' (winv_stk H _ _ _ _ _ _ _ HI14) (winv_mi H _ _ _ _ _ _ _ HI14)). }
    intros ms15 (l5 & l6 & l7 & l12 & l13 & l14 & l15 & l16 & l17 & l28 & l29 & l30 & l31 & m15 & EQ15 & MU15 & WM15 & MI15 & ST15). subst ms15.
    apply evt_done.
    assert (HI15 : winv H e ff fp XSc sk LBk m15)
      by (eapply (winv_munch H HB); [exact HP | exact HI14 | exact MU15 | exact WM15 | exact MI15 | exact ST15 | apply Forall_nil]).
    destruct (maps_fill ff (wS1 e) m m8 m9 m10 m11 m12 m13 m14 m15 F0 ltac:(unfold AINTRIN_STACK in *; lia)
                MU8 WM8 Z8 MU9 WM9 C9 MU10 WM10 Z10 MU11 WM11 C11 MU12 WM12 Z12 MU13 WM13 C13 MU14 WM14 Z14 MU15 WM15)
      as (SM & Z72 & MUf & WMf).
    exists l5, l6, l7, l12, l13, l14, l15, l16, l17, l28, l29, l30, l31, m15. split; [reflexivity|].
    split; [exact HI15|]. split; [exact MUf|]. split; [exact WMf|]. split; [exact SM | exact Z72].
  Qed.

  Definition wp3m_pre (e : went H) (ff : Z) (m : mem) (t0 t1 t2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s8 s9 s10 t3 t4 t5 t6 : word)
      : machine_state :=
    MS (mkR (Z_to_bv 64 WO_MS6_RA) (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) t0 t1 t2 (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
            (Z_to_bv 64 (ff + 2776)) (Z_to_bv 64 0) (Z_to_bv 64 22) a3 a4 a5 a6 a7
            s2 s3 s4 (Z_to_bv 64 (ff + 2800)) s6 (Z_to_bv 64 0x3f800000) s8 s9 s10 (Z_to_bv 64 (ff + 2752)) t3 t4 t5 t6)
       (w_F e) (Z_to_bv 64 AASAN_MEMSET) (w_fc e) None m (seg_rom asegs).

  Definition wp3m_post (e : went H) (ff fp : Z) (XSc : list (Z * Z)) (sk : as_St H) (LBk : list block) (m : mem) (words nw : Z)
      (s2 s3 s4 s6 s10 : word) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m',
      ms' = MS (mkR (Z_to_bv 64 WO_ON4_RA) (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) x5 x6 x7 (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
                    (Z_to_bv 64 (ff + 2920)) (Z_to_bv 64 25) x12 x13 x14 x15 x16 x17
                    s2 s3 s4 (Z_to_bv 64 (ff + 2920)) s6 (Z_to_bv 64 0x3f800000) (Z_to_bv 64 (ff + 2944)) (Z_to_bv 64 (ff + 2968)) s10
                    (Z_to_bv 64 (ff + 2752)) x28 x29 x30 x31)
               (w_F e) (Z_to_bv 64 RESV_OPND_ENTRY) (w_fc e) None m' (seg_rom asegs)
      /\ winv H e ff fp XSc sk LBk m'
      /\ munch [(wS1 e - AINTRIN_STACK, wS1 e); (ff + 2776, ff + 2992)] m m' /\ wmono asegs m m'
      /\ wtst ff m' words nw Z24 Z24 Z24 /\ addressable m' (ff + 2752) 240.

  Lemma wp3m : forall (e : went H) ff fp XSc sk LBk m (words nw : Z)
      (t0 t1 t2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s8 s9 s10 t3 t4 t5 t6 : word),
    wpre H e -> winv H e ff fp XSc sk LBk m ->
    rw_cells asegs m (ff + 2752) [C8 (Z_to_bv 64 words); C8 (Z_to_bv 64 nw); C8 (Z_to_bv 64 0)] ->
    addressable m (ff + 2752) 240 ->
    evt asegs (wp3m_post e ff fp XSc sk LBk m words nw s2 s3 s4 s6 s10)
      (wp3m_pre e ff m t0 t1 t2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s8 s9 s10 t3 t4 t5 t6).
  Proof.
    intros e ff fp XSc sk LBk m words nw t0 t1 t2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s8 s9 s10 t3 t4 t5 t6 HP HI C0 AD.
    destruct (wframe_bounds H e ff fp XSc sk LBk m HP HI) as (F0 & F64 & FLO & FH & FL & FS & SH1 & SH2 & S1L & S1SP & SPH & LOS1).
    assert (F32 : ff mod 32 = 0) by (clear - F64; Z.div_mod_to_equations; lia).
    assert (SHA : sh (ff + 2752) = sh ff + 344) by (unfold sh; Z.div_mod_to_equations; lia).
    unfold wp3m_pre.
    eapply (wms_ff H HB e ff fp XSc sk LBk m _ (Z_to_bv 64 WO_MS6_RA) t0 t1 t2 (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
              a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 (ff + 2800)) s6 (Z_to_bv 64 0x3f800000) s8 s9 s10 (Z_to_bv 64 (ff + 2752))
              t3 t4 t5 t6 (ff + 2752) 240 (ff + 2776) 22 (w_F e) (w_fc e));
      [exact HP | exact HI | exact AD | lia | lia | lia | lia | lia |].
    intros m1 u0 u1 u2 u11 u12 u13 u14 u15 u16 u17 u28 u29 u30 u31 HI1 MU1 WM1 Z1.
    rewrite (ret_pc_even WO_MS6_RA ltac:(unfold WO_MS6_RA; lia) eq_refl).
    assert (AD1 : addressable m1 (ff + 2752) 240)
      by (eapply addressable_transport; [exact AD | exact MU1 | exact WM1 | rewrite SHA; change (nsh 240) with 30; cbn [disjoint_from]; unfold AINTRIN_STACK in *; lia]).
    eapply evt_cut.
    { exact (wp3t e ff fp XSc sk LBk m1 u0 u1 u2 (Z_to_bv 64 (ff + 2776)) u11 u12 u13 u14 u15 u16 u17 s2 s3 s4 s6 s8 s9 s10
                  u28 u29 u30 u31 HP HI1 AD1). }
    intros ms (x5 & x6 & x7 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m2 & EQ & HI2 & MU2 & WM2 & SM & Z72).
    subst ms. apply evt_done.
    pose proof (munch_app _ _ _ _ _ MU1 MU2) as MU12. pose proof (wmono_trans asegs _ _ _ WM1 WM2) as WM12.
    cbn [app] in MU12.
    destruct (z72_split m2 (ff + 2920) Z72) as (T1 & T2 & T3).
    exists x5, x6, x7, x12, x13, x14, x15, x16, x17, x28, x29, x30, x31, m2. split; [reflexivity|].
    split; [exact HI2|].
    split; [eapply munch_in2; [exact MU12 | repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; unfold AINTRIN_STACK in *; lia]|].
    split; [exact WM12|].
    split.
    { unfold wtst. unfold AINTRIN_STACK in *.
      split; [eapply rw_cells_transport; [exact C0 | exact MU12 | exact WM12 | cbn; lia]|].
      split; [eapply rw_cells_transport; [exact Z1 | exact MU2 | exact WM2 | cbn; lia]|].
      split; [exact SM|].
      split; [exact T1|].
      split; [replace (ff + 2944) with (ff + 2920 + 24) by lia; exact T2|].
      replace (ff + 2968) with (ff + 2920 + 48) by lia; exact T3. }
    eapply addressable_transport; [exact AD1 | exact MU2 | exact WM2 | rewrite SHA; change (nsh 240) with 30; cbn [disjoint_from]; unfold AINTRIN_STACK in *; lia].
  Qed.

  Definition wp3_pre (e : went H) (ff : Z) (m : mem) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) : machine_state :=
    MS (mkR (Z_to_bv 64 WO_AN3_RA) (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) t0 t1 t2 (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
            a0 a1 a2 a3 a4 a5 a6 a7
            (Z_to_bv 64 (ff + 3456)) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) (Z_to_bv 64 (ff + 3720)) (Z_to_bv 64 (ff + 3504))
            (Z_to_bv 64 0x3f800000) (Z_to_bv 64 0) (Z_to_bv 64 (ff + 3672)) (Z_to_bv 64 (ff + 3696)) (Z_to_bv 64 (ff + 2752))
            t3 t4 t5 t6)
       (w_F e) (Z_to_bv 64 WO_AN3_RA) (w_fc e) None m (seg_rom asegs).

  Definition wp3_post (e : went H) (ff fp : Z) (XSc : list (Z * Z)) (sk : as_St H) (LBk : list block) (m : mem) (words nw : Z)
      : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m',
      ms' = MS (mkR (Z_to_bv 64 WO_ON4_RA) (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) x5 x6 x7 (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
                    (Z_to_bv 64 (ff + 2920)) (Z_to_bv 64 25) x12 x13 x14 x15 x16 x17
                    (Z_to_bv 64 (ff + 3456)) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) (Z_to_bv 64 (ff + 2920)) (Z_to_bv 64 (ff + 3504))
                    (Z_to_bv 64 0x3f800000) (Z_to_bv 64 (ff + 2944)) (Z_to_bv 64 (ff + 2968)) (Z_to_bv 64 (ff + 3696))
                    (Z_to_bv 64 (ff + 2752)) x28 x29 x30 x31)
               (w_F e) (Z_to_bv 64 RESV_OPND_ENTRY) (w_fc e) None m' (seg_rom asegs)
      /\ winv H e ff fp XSc sk LBk m'
      /\ munch [(sh ff + 344, sh ff + 374); (ff + 2752, ff + 2776); (wS1 e - AINTRIN_STACK, wS1 e); (ff + 2776, ff + 2992)] m m'
      /\ wmono asegs m m'
      /\ wtst ff m' words nw Z24 Z24 Z24 /\ addressable m' (ff + 2752) 240
      /\ u8arr asegs m' (sh ff) (map (Z_to_bv 8) WO_SH4T).

  Lemma wp3 : forall (e : went H) ff fp XSc sk LBk m (words nw : Z) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    wpre H e -> winv H e ff fp XSc sk LBk m ->
    rw_cells asegs m (wS1 e + 16) [C8 (Z_to_bv 64 0)] ->
    rw_cells asegs m (wS1 e + 24) [C8 (Z_to_bv 64 words)] -> rw_cells asegs m (wS1 e + 32) [C8 (Z_to_bv 64 nw)] ->
    0 <= words < 2 ^ 64 /\ 0 <= nw < 2 ^ 64 ->
    u8arr asegs m (sh ff) (map (Z_to_bv 8) WO_SH2C) ->
    evt asegs (wp3_post e ff fp XSc sk LBk m words nw) (wp3_pre e ff m t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6).
  Proof.
    intros e ff fp XSc sk LBk m words nw t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 HP HI C16 C24 C32 WN SH2.
    destruct (wframe_bounds H e ff fp XSc sk LBk m HP HI) as (F0 & F64 & FLO & FH & FL & FS & SH1 & SH2' & S1L & S1SP & SPH & LOS1).
    assert (F32 : ff mod 32 = 0) by (clear - F64; Z.div_mod_to_equations; lia).
    assert (SHA : sh (ff + 2752) = sh ff + 344) by (unfold sh; Z.div_mod_to_equations; lia).
    assert (WR24 : wr_at asegs m (ff + 2752) 24).
    { pose proof (winv_wf H _ _ _ _ _ _ _ HI) as (W0 & W1 & W). split; [lia|]. split; [lia|]. intros i Hi.
      replace (ff + 2752 + i) with (ff + (2752 + i)) by lia. apply W. lia. }
    assert (FS1 : ff + 3808 <= wS1 e) by (unfold AINTRIN_STACK in *; lia).
    assert (FSH : sh ff + 476 <= ff \/ ff + 3808 <= sh ff) by (destruct SH1 as [X|X]; [left|right]; lia).
    unfold wp3_pre.
    eapply evt_cut.
    { exact (we3c (w_gp e) (w_tp e) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (w_F e) (w_fc e) m (wSP e) (wS1 e) ff (w_lo e) words nw
                  S1L ltac:(lia) SPH LOS1 F64 ltac:(unfold AIMG_TOP, AFS_HDR in FLO; lia) FS1 FSH
                  C16 C24 C32 WN WR24 SH2 (winv_stk H _ _ _ _ _ _ _ HI) (winv_mi H _ _ _ _ _ _ _ HI)). }
    intros ms1 (x5 & x6 & x7 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m1 & EQ1 & MU1 & WM1 & MI1 & ST1 & C1 & SH4).
    subst ms1.
    assert (HI1 : winv H e ff fp XSc sk LBk m1).
    { eapply (winv_munch H HB); [exact HP | exact HI | exact MU1 | exact WM1 | exact MI1 | exact ST1 |].
      unfold wwin. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; [right; right | right; left]; lia. }
    assert (AD1 : addressable m1 (ff + 2752) 240).
    { split; [lia|]. split; [lia|]. split; [Z.div_mod_to_equations; lia|].
      rewrite SHA.
      pose proof (u8arr_sub m1 (sh ff) _ 344 30 SH4 ltac:(lia) ltac:(lia) ltac:(rewrite length_map; vm_compute; discriminate)) as U.
      replace (shadow_of 240) with (firstn (Z.to_nat 30) (skipn (Z.to_nat 344) (map (Z_to_bv 8) WO_SH4T))) by (vm_compute; reflexivity).
      exact U. }
    eapply evt_cut.
    { exact (wp3m e ff fp XSc sk LBk m1 words nw x5 x6 x7 x13 x14 x15 x16 x17
                  (Z_to_bv 64 (ff + 3456)) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) (Z_to_bv 64 (ff + 3504)) (Z_to_bv 64 0)
                  (Z_to_bv 64 (ff + 3672)) (Z_to_bv 64 (ff + 3696)) x28 x29 x30 x31 HP HI1 C1 AD1). }
    intros ms (y5 & y6 & y7 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m2 & EQ & HI2 & MU2 & WM2 & TS & AD2).
    subst ms. apply evt_done.
    pose proof (munch_app _ _ _ _ _ MU1 MU2) as MU12. pose proof (wmono_trans asegs _ _ _ WM1 WM2) as WM12. cbn [app] in MU12.
    exists y5, y6, y7, y12, y13, y14, y15, y16, y17, y28, y29, y30, y31, m2. split; [reflexivity|].
    split; [exact HI2|]. split; [exact MU12|]. split; [exact WM12|]. split; [exact TS|]. split; [exact AD2|].
    eapply (u8arr_transport asegs); [exact SH4 | exact MU2 | exact WM2 |].
    rewrite length_map. change (Z.of_nat (length WO_SH4T)) with 476. cbn [disjoint_from].
    unfold AINTRIN_STACK in *. destruct SH1 as [X|X]; lia.
  Qed.

End WoQ.
