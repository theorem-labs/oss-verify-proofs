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
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require Import LbA_MILB LbA_PrsStmt LbA_StateStmt LbA_HKit LbA_HStKit.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbA_WoGen LbA_WoDefs LbA_WoKit LbA_WoKit3 LbA_WoSt LbA_WoSt2 LbA_WoMs LbA_WoCall LbA_WoCut LbA_WoZ.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbA_WoR2 LbA_WoR6 LbA_WoE0 LbA_WoE0b LbA_WoP LbA_WoF LbA_WoQ LbA_WoT2 LbA_WoPm.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section WoU.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHb : asan_rt_hyps_bp H.
  Let HB := rt_bp_base H HHb.

  Lemma munch_nil_eqU : forall (m m' : mem), munch [] m m' -> m' = m.
  Proof. intros m m' MU. apply functional_extensionality. intros x. apply MU. exact I. Qed.

  Lemma wtst0_fill : forall (S1 : Z) (m5 m6 m8 m9 m10 m11 m12 m13 m14 : mem),
    0 <= S1 ->
    munch [(S1 + 120, S1 + 120 + 32); (S1 - AINTRIN_STACK, S1)] m5 m6 -> wmono asegs m5 m6 ->
    rw_cells asegs m6 (S1 + 120) [CB (Z.to_nat 32) (poison_bytes (Z.to_nat 32) 0)] ->
    munch [(S1 + 72, S1 + 72 + 46); (S1 - AINTRIN_STACK, S1)] m6 m8 -> wmono asegs m6 m8 ->
    rw_cells asegs m8 (S1 + 72) [CB (Z.to_nat 46) (poison_bytes (Z.to_nat 46) 0)] ->
    munch [(S1 + 152, S1 + 156)] m8 m9 -> wmono asegs m8 m9 -> rw_cells asegs m9 (S1 + 152) [C4 (Z_to_bv 64 0x3f800000)] ->
    munch [(S1 + 160, S1 + 160 + 32); (S1 - AINTRIN_STACK, S1)] m9 m10 -> wmono asegs m9 m10 ->
    rw_cells asegs m10 (S1 + 160) [CB (Z.to_nat 32) (poison_bytes (Z.to_nat 32) 0)] ->
    munch [(S1 + 192, S1 + 196)] m10 m11 -> wmono asegs m10 m11 -> rw_cells asegs m11 (S1 + 192) [C4 (Z_to_bv 64 0x3f800000)] ->
    munch [(S1 + 200, S1 + 200 + 32); (S1 - AINTRIN_STACK, S1)] m11 m12 -> wmono asegs m11 m12 ->
    rw_cells asegs m12 (S1 + 200) [CB (Z.to_nat 32) (poison_bytes (Z.to_nat 32) 0)] ->
    munch [(S1 + 232, S1 + 236)] m12 m13 -> wmono asegs m12 m13 -> rw_cells asegs m13 (S1 + 232) [C4 (Z_to_bv 64 0x3f800000)] ->
    munch [(S1 + 240, S1 + 240 + 72); (S1 - AINTRIN_STACK, S1)] m13 m14 -> wmono asegs m13 m14 ->
    rw_cells asegs m14 (S1 + 240) [CB (Z.to_nat 72) (poison_bytes (Z.to_nat 72) 0)] ->
    wtst0 S1 m14 Z24 Z24 Z24 /\ munch [(S1 - AINTRIN_STACK, S1); (S1 + 72, S1 + 312)] m5 m14 /\ wmono asegs m5 m14.
  Proof.
    intros S1 m5 m6 m8 m9 m10 m11 m12 m13 m14 S0 MU6 WM6 Z6 MU8 WM8 Z8 MU9 WM9 C9 MU10 WM10 Z10
      MU11 WM11 C11 MU12 WM12 Z12 MU13 WM13 C13 MU14 WM14 Z14.
    pose proof (munch_app _ _ _ _ _ MU13 MU14) as S13. pose proof (wmono_trans asegs _ _ _ WM13 WM14) as U13.
    pose proof (munch_app _ _ _ _ _ MU12 S13) as S12. pose proof (wmono_trans asegs _ _ _ WM12 U13) as U12.
    pose proof (munch_app _ _ _ _ _ MU11 S12) as S11. pose proof (wmono_trans asegs _ _ _ WM11 U12) as U11.
    pose proof (munch_app _ _ _ _ _ MU10 S11) as S10. pose proof (wmono_trans asegs _ _ _ WM10 U11) as U10.
    pose proof (munch_app _ _ _ _ _ MU9 S10) as S9. pose proof (wmono_trans asegs _ _ _ WM9 U10) as U9.
    pose proof (munch_app _ _ _ _ _ MU8 S9) as S8. pose proof (wmono_trans asegs _ _ _ WM8 U9) as U8.
    pose proof (munch_app _ _ _ _ _ MU6 S8) as S6. pose proof (wmono_trans asegs _ _ _ WM6 U8) as U6.
    cbn [app] in S6, S8, S9, S10, S11, S12, S13.
    unfold AINTRIN_STACK in *.
    destruct (z72_split m14 (S1 + 240) Z14) as (T1 & T2 & T3).
    split; [|split; [eapply munch_in2; [exact S6 | repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia] | exact U6]].
    split; [eapply rw_cells_transport; [exact Z8 | exact S9 | exact U9 | cbn; lia]|].
    split; [unfold st_maps_cells; refine (conj _ (conj _ (conj _ (conj _ (conj _ _)))))|].
    - replace (S1 + 72 + 48) with (S1 + 120) by lia. eapply rw_cells_transport; [exact Z6 | exact S8 | exact U8 | cbn; lia].
    - replace (S1 + 72 + 80) with (S1 + 152) by lia. eapply rw_cells_transport; [exact C9 | exact S10 | exact U10 | cbn; lia].
    - replace (S1 + 72 + 88) with (S1 + 160) by lia. eapply rw_cells_transport; [exact Z10 | exact S11 | exact U11 | cbn; lia].
    - replace (S1 + 72 + 120) with (S1 + 192) by lia. eapply rw_cells_transport; [exact C11 | exact S12 | exact U12 | cbn; lia].
    - replace (S1 + 72 + 128) with (S1 + 200) by lia. eapply rw_cells_transport; [exact Z12 | exact S13 | exact U13 | cbn; lia].
    - replace (S1 + 72 + 160) with (S1 + 232) by lia. eapply rw_cells_transport; [exact C13 | exact MU14 | exact WM14 | cbn; lia].
    - split; [exact T1|]. split; [replace (S1 + 264) with (S1 + 240 + 24) by lia; exact T2|].
      replace (S1 + 288) with (S1 + 240 + 48) by lia; exact T3.
  Qed.

  Definition wu_post (e : went H) (ff fp : Z) (XS : list (Z * Z)) (sk : as_St H) (LBk : list block) (cP : stateC) (k r : Z)
      (F : bvmap 5 word) (fc : bv 32) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m',
      ms' = MS (mkR (Z_to_bv 64 WO_ON7_RA) (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) x5 x6 x7 (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
                    (Z_to_bv 64 500) x11 x12 x13 x14 x15 x16 x17
                    (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) (Z_to_bv 64 0x3f800000) (Z_to_bv 64 k) (Z_to_bv 64 99)
                    (Z_to_bv 64 r) (Z_to_bv 64 (k + 100)) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31)
               F (Z_to_bv 64 AOPNEW) fc None m' (seg_rom asegs)
      /\ winv H e ff fp XS sk LBk m' /\ wfc2 H e ff m' /\ rw_cells asegs m' (wS1 e + 48) [C8 (Z_to_bv 64 (ff + 176))]
      /\ state_repA LBk m' (ff + 176) cP /\ state_sh m' cP
      /\ wtst0 (wS1 e) m' Z24 Z24 Z24.

  Lemma wu : forall (e : went H) ff fp XS sk LBk (cP : stateC) k r m (F : bvmap 5 word) (fc : bv 32) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    wpre H e -> winv H e ff fp XS sk LBk m ->
    wfc2 H e ff m -> rw_cells asegs m (wS1 e + 48) [C8 (Z_to_bv 64 (ff + 176))] ->
    state_repA LBk m (ff + 176) cP -> state_sh m cP -> (forall p n, In (p, n) (state_blocks cP) -> In (p, n) (lbl LBk)) ->
    evt asegs (wu_post e ff fp XS sk LBk cP k r F fc)
      (MS (mkR (Z_to_bv 64 AWO_PM_RA) (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) t0 t1 t2 (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
               (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) (Z_to_bv 64 0) (Z_to_bv 64 k) (Z_to_bv 64 99)
               (Z_to_bv 64 k) (Z_to_bv 64 (k + 100)) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (ff + 128)) t3 t4 t5 t6)
          F (Z_to_bv 64 AWO_PM_RA) fc None m (seg_rom asegs)).
  Proof.
    intros e ff fp XS sk LBk cP k r m F fc t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 HP HI WC C48 R S BL.
    pose proof (wpre_geo H e HP) as (CE & LO & SSHI & SHIH & SP16 & TP).
    pose proof (wS1_facts H e HP) as (S32 & S1SP & S1L & SPH & LOS1 & _).
    pose proof (wframe_z H _ _ _ (winv_ff H _ _ _ _ _ _ _ HI)) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & FAPP & FSH).
    pose proof aceil_facts as ACF.

    eapply evt_cut.
    { exact (wu1 (w_gp e) (w_tp e) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m (wSP e) (wS1 e) ff (w_lo e) k r
                 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) F3 ltac:(lia) ltac:(lia) FSH FAPP (winv_stk H _ _ _ _ _ _ _ HI) (winv_mi H _ _ _ _ _ _ _ HI)). }
    intros ms5 (u5 & u6 & u7 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & m5 & EQ5 & MU5 & WM5 & MI5 & ST5). subst ms5.
    pose proof (munch_nil_eqU m m5 MU5) as EM5. subst m5.
    eapply (wms_rs H HB e ff fp XS sk LBk m); [exact HP | exact HI | lia | lia | lia |].
    intros m6 z0 z1 z2 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 HI6 MU6 WM6 Z6.
    rewrite (ret_pc_even WO_MS11_RA ltac:(unfold WO_MS11_RA; lia) eq_refl).

    eapply evt_cut.
    { exact (wu2 (w_gp e) (w_tp e) z0 z1 z2 (Z_to_bv 64 (wS1 e + 120)) z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 F fc m6 (wSP e) (wS1 e) ff (w_lo e) k r
                 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) F3 ltac:(lia) ltac:(lia) FSH FAPP (winv_stk H _ _ _ _ _ _ _ HI6) (winv_mi H _ _ _ _ _ _ _ HI6)). }
    intros ms7 (i5 & i6 & i7 & i13 & i14 & i15 & i16 & i17 & i28 & i29 & i30 & i31 & m7 & EQ7 & MU7 & WM7 & MI7 & ST7). subst ms7.
    pose proof (munch_nil_eqU m6 m7 MU7) as EM7. subst m7.
    eapply (wms_rs H HB e ff fp XS sk LBk m6); [exact HP | exact HI6 | lia | lia | lia |].
    intros m8 j0 j1 j2 j11 j12 j13 j14 j15 j16 j17 j28 j29 j30 j31 HI8 MU8 WM8 Z8.
    rewrite (ret_pc_even WO_MS12_RA ltac:(unfold WO_MS12_RA; lia) eq_refl).

    eapply evt_cut.
    { exact (wu3 (w_gp e) (w_tp e) j0 j1 j2 (Z_to_bv 64 (wS1 e + 72)) j11 j12 j13 j14 j15 j16 j17 j28 j29 j30 j31 F fc m8 (wSP e) (wS1 e) ff (w_lo e) k r
                 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) F3 ltac:(lia) ltac:(lia) FSH FAPP (winv_stk H _ _ _ _ _ _ _ HI8) (winv_mi H _ _ _ _ _ _ _ HI8)). }
    intros ms9 (n5 & n6 & n7 & n13 & n14 & n15 & n16 & n17 & n28 & n29 & n30 & n31 & m9 & EQ9 & MU9 & WM9 & MI9 & ST9 & C9). subst ms9.
    assert (HI9 : winv H e ff fp XS sk LBk m9).
    { eapply (winv_munch H HB); [exact HP | exact HI8 | exact MU9 | exact WM9 | exact MI9 | exact ST9 |].
      unfold wwin, WO_SAVED. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]. left. lia. }
    eapply (wms_rs H HB e ff fp XS sk LBk m9); [exact HP | exact HI9 | lia | lia | lia |].
    intros m10 o0 o1 o2 o11 o12 o13 o14 o15 o16 o17 o28 o29 o30 o31 HI10 MU10 WM10 Z10.
    rewrite (ret_pc_even WO_MS13_RA ltac:(unfold WO_MS13_RA; lia) eq_refl).

    eapply evt_cut.
    { exact (wu4 (w_gp e) (w_tp e) o0 o1 o2 (Z_to_bv 64 (wS1 e + 160)) o11 o12 o13 o14 o15 o16 o17 o28 o29 o30 o31 F fc m10 (wSP e) (wS1 e) ff (w_lo e) k r
                 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) F3 ltac:(lia) ltac:(lia) FSH FAPP (winv_stk H _ _ _ _ _ _ _ HI10) (winv_mi H _ _ _ _ _ _ _ HI10)). }
    intros ms11 (q5 & q6 & q7 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & m11 & EQ11 & MU11 & WM11 & MI11 & ST11 & C11). subst ms11.
    assert (HI11 : winv H e ff fp XS sk LBk m11).
    { eapply (winv_munch H HB); [exact HP | exact HI10 | exact MU11 | exact WM11 | exact MI11 | exact ST11 |].
      unfold wwin, WO_SAVED. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]. left. lia. }
    eapply (wms_rs H HB e ff fp XS sk LBk m11); [exact HP | exact HI11 | lia | lia | lia |].
    intros m12 g0 g1 g2 g11 g12 g13 g14 g15 g16 g17 g28 g29 g30 g31 HI12 MU12 WM12 Z12.
    rewrite (ret_pc_even WO_MS14_RA ltac:(unfold WO_MS14_RA; lia) eq_refl).

    eapply evt_cut.
    { exact (wu5 (w_gp e) (w_tp e) g0 g1 g2 (Z_to_bv 64 (wS1 e + 200)) g11 g12 g13 g14 g15 g16 g17 g28 g29 g30 g31 F fc m12 (wSP e) (wS1 e) ff (w_lo e) k r
                 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) F3 ltac:(lia) ltac:(lia) FSH FAPP (winv_stk H _ _ _ _ _ _ _ HI12) (winv_mi H _ _ _ _ _ _ _ HI12)). }
    intros ms13 (h5 & h6 & h7 & h13 & h14 & h15 & h16 & h17 & h28 & h29 & h30 & h31 & m13 & EQ13 & MU13 & WM13 & MI13 & ST13 & C13). subst ms13.
    assert (HI13 : winv H e ff fp XS sk LBk m13).
    { eapply (winv_munch H HB); [exact HP | exact HI12 | exact MU13 | exact WM13 | exact MI13 | exact ST13 |].
      unfold wwin, WO_SAVED. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]. left. lia. }
    eapply (wms_rs H HB e ff fp XS sk LBk m13); [exact HP | exact HI13 | lia | lia | lia |].
    intros m14 f0 f1 f2 f11 f12 f13 f14 f15 f16 f17 f28 f29 f30 f31 HI14 MU14 WM14 Z14.
    rewrite (ret_pc_even WO_MS15_RA ltac:(unfold WO_MS15_RA; lia) eq_refl).

    eapply evt_cut.
    { exact (wu6 (w_gp e) (w_tp e) f0 f1 f2 (Z_to_bv 64 (wS1 e + 240)) f11 f12 f13 f14 f15 f16 f17 f28 f29 f30 f31 F fc m14 (wSP e) (wS1 e) ff (w_lo e) k r
                 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) F3 ltac:(lia) ltac:(lia) FSH FAPP (winv_stk H _ _ _ _ _ _ _ HI14) (winv_mi H _ _ _ _ _ _ _ HI14)). }
    intros ms15 (l5 & l6 & l7 & l11 & l12 & l13 & l14 & l15 & l16 & l17 & l28 & l29 & l30 & l31 & m15 & EQ15 & MU15 & WM15 & MI15 & ST15). subst ms15.
    pose proof (munch_nil_eqU m14 m15 MU15) as EM15. subst m15.
    apply evt_done.
    exists l5, l6, l7, l11, l12, l13, l14, l15, l16, l17, l28, l29, l30, l31, m14. split; [reflexivity|].
    split; [exact HI14|].

    destruct (wtst0_fill (wS1 e) m m6 m8 m9 m10 m11 m12 m13 m14 ltac:(lia) MU6 WM6 Z6 MU8 WM8 Z8 MU9 WM9 C9 MU10 WM10 Z10
                MU11 WM11 C11 MU12 WM12 Z12 MU13 WM13 C13 MU14 WM14 Z14) as (WT & S6 & U6).
    split; [eapply (wfc2_munch H e ff m m14); [exact WC | exact S6 | exact U6 |]; unfold wfc2_apart, AINTRIN_STACK;
            repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia|].
    split; [eapply rw_cells_transport; [exact C48 | exact S6 | exact U6 | cbn; unfold AINTRIN_STACK; lia]|].
    destruct (wstate_mu H HB e ff fp XS sk LBk m m14 _ cP HP HI S6 U6
                ltac:(unfold wsw, AINTRIN_STACK; apply Forall_cons; [left; cbn [fst snd]; lia|]; apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil])
                BL R S) as [R' S'].
    split; [exact R'|]. split; [exact S' | exact WT].
  Qed.
End WoU.
