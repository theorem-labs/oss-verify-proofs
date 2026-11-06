(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HeapCeil.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HTac HArr HSysStep HExec CellsX TacX HMem HMState HLFrame.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HPrelim.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import ASegs AsShadow AsConst AsIface AsCXXHeap CXXRep AsStack0 AsWalk RtA_Iface.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require HLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbA_PrsStmt LbA_SR LbA_Conv LbA_WoGen LbA_WoDefs LbA_WoKit LbA_WoSt LbA_WoMs LbA_WoCall LbA_WoCut LbA_WoZ.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbA_WoR2 LbA_WoR3 LbA_WoR4 LbA_WoR5 LbA_WoE0 LbA_WoE0b LbA_WoP.
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

  Lemma wtst_fill1 : forall (S1 : Z) (m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 : mem) words nw,
    0 <= S1 ->
    rw_cells asegs m5 (S1 + 72) [C8 (Z_to_bv 64 words); C8 (Z_to_bv 64 nw); C8 (Z_to_bv 64 0)] ->
    munch [(S1 + 120, S1 + 120 + 32); (S1 - AINTRIN_STACK, S1)] m5 m6 -> wmono asegs m5 m6 ->
    rw_cells asegs m6 (S1 + 120) [CB (Z.to_nat 32) (poison_bytes (Z.to_nat 32) 0)] ->
    munch [] m6 m7 -> wmono asegs m6 m7 ->
    munch [(S1 + 96, S1 + 96 + 22); (S1 - AINTRIN_STACK, S1)] m7 m8 -> wmono asegs m7 m8 ->
    rw_cells asegs m8 (S1 + 96) [CB (Z.to_nat 22) (poison_bytes (Z.to_nat 22) 0)] ->
    munch [(S1 + 152, S1 + 156)] m8 m9 -> wmono asegs m8 m9 -> rw_cells asegs m9 (S1 + 152) [C4 (Z_to_bv 64 0x3f800000)] ->
    munch [(S1 + 160, S1 + 160 + 32); (S1 - AINTRIN_STACK, S1)] m9 m10 -> wmono asegs m9 m10 ->
    rw_cells asegs m10 (S1 + 160) [CB (Z.to_nat 32) (poison_bytes (Z.to_nat 32) 0)] ->
    munch [(S1 + 192, S1 + 196)] m10 m11 -> wmono asegs m10 m11 -> rw_cells asegs m11 (S1 + 192) [C4 (Z_to_bv 64 0x3f800000)] ->
    munch [(S1 + 200, S1 + 200 + 32); (S1 - AINTRIN_STACK, S1)] m11 m12 -> wmono asegs m11 m12 ->
    rw_cells asegs m12 (S1 + 200) [CB (Z.to_nat 32) (poison_bytes (Z.to_nat 32) 0)] ->
    munch [(S1 + 232, S1 + 236)] m12 m13 -> wmono asegs m12 m13 -> rw_cells asegs m13 (S1 + 232) [C4 (Z_to_bv 64 0x3f800000)] ->
    munch [(S1 + 240, S1 + 240 + 72); (S1 - AINTRIN_STACK, S1)] m13 m14 -> wmono asegs m13 m14 ->
    rw_cells asegs m14 (S1 + 240) [CB (Z.to_nat 72) (poison_bytes (Z.to_nat 72) 0)] ->
    munch [] m14 m15 -> wmono asegs m14 m15 ->
    wtst S1 m15 words nw Z24 Z24 Z24 /\ munch [(S1 - AINTRIN_STACK, S1); (S1 + 72, S1 + 312)] m5 m15 /\ wmono asegs m5 m15.
  Proof.
    intros S1 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 words nw S0 TS5 MU6 WM6 Z6 MU7 WM7 MU8 WM8 Z8 MU9 WM9 C9 MU10 WM10 Z10
      MU11 WM11 C11 MU12 WM12 Z12 MU13 WM13 C13 MU14 WM14 Z14 MU15 WM15.
    pose proof (munch_app _ _ _ _ _ MU14 MU15) as S14. pose proof (wmono_trans asegs _ _ _ WM14 WM15) as U14.
    pose proof (munch_app _ _ _ _ _ MU13 S14) as S13. pose proof (wmono_trans asegs _ _ _ WM13 U14) as U13.
    pose proof (munch_app _ _ _ _ _ MU12 S13) as S12. pose proof (wmono_trans asegs _ _ _ WM12 U13) as U12.
    pose proof (munch_app _ _ _ _ _ MU11 S12) as S11. pose proof (wmono_trans asegs _ _ _ WM11 U12) as U11.
    pose proof (munch_app _ _ _ _ _ MU10 S11) as S10. pose proof (wmono_trans asegs _ _ _ WM10 U11) as U10.
    pose proof (munch_app _ _ _ _ _ MU9 S10) as S9. pose proof (wmono_trans asegs _ _ _ WM9 U10) as U9.
    pose proof (munch_app _ _ _ _ _ MU8 S9) as S8. pose proof (wmono_trans asegs _ _ _ WM8 U9) as U8.
    pose proof (munch_app _ _ _ _ _ MU7 S8) as S7. pose proof (wmono_trans asegs _ _ _ WM7 U8) as U7.
    pose proof (munch_app _ _ _ _ _ MU6 S7) as S6. pose proof (wmono_trans asegs _ _ _ WM6 U7) as U6.
    cbn [app] in S6, S7, S8, S9, S10, S11, S12, S13, S14.
    unfold AINTRIN_STACK in *.
    destruct (z72_split m14 (S1 + 240) Z14) as (T1 & T2 & T3).
    split; [|split; [eapply munch_in2; [exact S6 | repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia] | exact U6]].
    split; [eapply rw_cells_transport; [exact TS5 | exact S6 | exact U6 | cbn; lia]|].
    split; [eapply rw_cells_transport; [exact Z8 | exact S9 | exact U9 | cbn; lia]|].
    split; [unfold st_maps_cells; refine (conj _ (conj _ (conj _ (conj _ (conj _ _)))))|].
    - replace (S1 + 72 + 48) with (S1 + 120) by lia. eapply rw_cells_transport; [exact Z6 | exact S7 | exact U7 | cbn; lia].
    - replace (S1 + 72 + 80) with (S1 + 152) by lia. eapply rw_cells_transport; [exact C9 | exact S10 | exact U10 | cbn; lia].
    - replace (S1 + 72 + 88) with (S1 + 160) by lia. eapply rw_cells_transport; [exact Z10 | exact S11 | exact U11 | cbn; lia].
    - replace (S1 + 72 + 120) with (S1 + 192) by lia. eapply rw_cells_transport; [exact C11 | exact S12 | exact U12 | cbn; lia].
    - replace (S1 + 72 + 128) with (S1 + 200) by lia. eapply rw_cells_transport; [exact Z12 | exact S13 | exact U13 | cbn; lia].
    - replace (S1 + 72 + 160) with (S1 + 232) by lia. eapply rw_cells_transport; [exact C13 | exact S14 | exact U14 | cbn; lia].
    - split; [eapply rw_cells_transport; [exact T1 | exact MU15 | exact WM15 | exact I]|].
      split; [replace (S1 + 264) with (S1 + 240 + 24) by lia; eapply rw_cells_transport; [exact T2 | exact MU15 | exact WM15 | exact I]|].
      replace (S1 + 288) with (S1 + 240 + 48) by lia; eapply rw_cells_transport; [exact T3 | exact MU15 | exact WM15 | exact I].
  Qed.

  Definition wp3_pre (e : went H) (ff c d : Z) (m : mem) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) : machine_state :=
    MS (mkR (Z_to_bv 64 WO_ON3_RA) (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) t0 t1 t2 (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
            (Z_to_bv 64 d) a1 a2 a3 a4 a5 a6 a7
            (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) (Z_to_bv 64 0) (Z_to_bv 64 c) (Z_to_bv 64 99) (Z_to_bv 64 0)
            (Z_to_bv 64 0) (Z_to_bv 64 (c + 100)) (Z_to_bv 64 0) (Z_to_bv 64 (ff + 128)) t3 t4 t5 t6)
       (w_F e) (Z_to_bv 64 WO_ON3_RA) (w_fc e) None m (seg_rom asegs).

  Definition wp3_post (e : went H) (ff fp : Z) (sk : as_St H) (LBk : list block) (b c d : Z) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m',
      ms' = MS (mkR (Z_to_bv 64 WO_ON4_RA) (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) x5 x6 x7 (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
                    (Z_to_bv 64 500) x11 x12 x13 x14 x15 x16 x17
                    (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) (Z_to_bv 64 0x3f800000) (Z_to_bv 64 (wS1 e + 96)) (Z_to_bv 64 99)
                    (Z_to_bv 64 0) (Z_to_bv 64 d) (Z_to_bv 64 (d + 100)) (Z_to_bv 64 0) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31)
               (w_F e) (Z_to_bv 64 AOPNEW) (w_fc e) None m' (seg_rom asegs)
      /\ winv H e ff fp [] sk LBk m' /\ wfc H e ff m' /\ rw_cells asegs m' (wS1 e + 48) [C8 (Z_to_bv 64 (ff + 176))]
      /\ wpst ff m' (vtrip b 500) (vtrip c 100) (vtrip d 100) /\ wblk m' b 500 /\ wblk m' c 100 /\ wblk m' d 100
      /\ wtst (wS1 e) m' (w_words e) (w_n e) Z24 Z24 Z24.

  Lemma wp3 : forall (e : went H) ff fp sk LBk (p q r : bptr) b c d m t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    wpre H e -> winv H e ff fp [] sk LBk m -> In (p, b, 500) LBk -> In (q, c, 100) LBk -> In (r, d, 100) LBk -> p <> r -> q <> r ->
    (forall bb, In bb (w_LB e) -> In bb LBk /\ blk_id bb <> r) ->
    wfc H e ff m -> rw_cells asegs m (wS1 e + 48) [C8 (Z_to_bv 64 (ff + 176))] ->
    wpst ff m (vtrip b 500) (vtrip c 100) Z24 -> wblk m b 500 -> wblk m c 100 -> addressable m d 100 -> wr_at asegs m d 100 ->
    evt asegs (wp3_post e ff fp sk LBk b c d) (wp3_pre e ff c d m t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6).
  Proof.
    intros e ff fp sk LBk p q r b c d m t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 HP HI INb INc IN NEb NEc LBI WC C48 PST WB WCc AD WRd.
    pose proof (wpre_geo H e HP) as (CE & LO & SSHI & SHIH & SP16 & TP).
    pose proof (wS1_facts H e HP) as (S32 & S1SP & S1L & SPH & LOS1 & _).
    pose proof (wframe_z H _ _ _ (winv_ff H _ _ _ _ _ _ _ HI)) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & FAPP & FSH).
    pose proof (wblk_geo H HB e ff fp [] sk LBk m r d 100 HP HI IN) as (G0 & G16 & Gn & GC & GH & GSA & GSC & GLO & GLS & GF & GSF & GSS & GSB & GSH).
    pose proof (wblk_geo H HB e ff fp [] sk LBk m p b 500 HP HI INb) as (H0 & H16 & Hn & HC & HH' & HSA & HSC & _ & _ & HF & HSF & HSS & HSB & HSH).
    pose proof (wblk_geo H HB e ff fp [] sk LBk m q c 100 HP HI INc) as (K0 & K16 & Kn & KC & KH' & KSA & KSC & _ & _ & KF & KSF & KSS & KSB & KSH).
    pose proof (wblk2_geo H HB _ _ _ p b 500 r d 100 (winv_rh H _ _ _ _ _ _ _ HI) INb IN NEb) as (X1 & X2 & X3 & X4).
    pose proof (wblk2_geo H HB _ _ _ q c 100 r d 100 (winv_rh H _ _ _ _ _ _ _ HI) INc IN NEc) as (Y1 & Y2 & Y3 & Y4).
    pose proof aceil_facts as ACF.
    pose proof WC as (_ & _ & _ & _ & _ & _ & WC7 & _).
    pose proof HP as (_ & _ & HN & _).
    destruct PST as (PZ & PM & PV1 & PV2 & PV3).
    assert (Zv : forall mm a k a', rw_cells asegs mm a Z24 -> 0 <= k <= 16 -> a' = a + k -> rw_cells asegs mm a' [CB 8 (poison_bytes 8 0)])
      by (intros mm a k a' X Hk Ea; subst a'; exact (zero_cells_sub mm a 24 k 8 X ltac:(lia) ltac:(lia))).
    assert (WFW : forall mm a n, winv H e ff fp [] sk LBk mm -> ff <= a -> a + n <= ff + 504 -> wr_at asegs mm a n).
    { intros mm a n HI' K1 K2. pose proof (winv_wf H _ _ _ _ _ _ _ HI') as (W0 & W1 & W). unfold WO_FLAGP in *.
      split; [lia|]. split; [lia|]. intros i Hi. replace (a + i) with (ff + (a - ff + i)) by lia. apply W. lia. }

    change [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (w_words e)); C8 (Z_to_bv 64 (w_n e))]
      with ([C8 (Z_to_bv 64 0)] ++ [C8 (Z_to_bv 64 (w_words e))] ++ [C8 (Z_to_bv 64 (w_n e))]) in WC7.
    apply rw_cells_app in WC7 as [SP0 WC7]. apply rw_cells_app in WC7 as [SP8 SP16'].
    cbn [cells_size csize] in SP8, SP16'.
    replace (wS1 e + Z.of_nat (8 + 0) + Z.of_nat (8 + 0)) with (wS1 e + 16) in SP16' by (cbn; lia).
    assert (WDS : 0 <= w_words e < 2 ^ 64 /\ 0 <= w_n e < 2 ^ 64).
    { pose proof HP as (_ & _ & _ & WK & _). destruct WK as [(W0 & W1)|(pw & kk & INw & W1 & W2 & W3 & W4 & _)].
      - rewrite W0. lia.
      - lia. }
    unfold wp3_pre.

    eapply evt_cut.
    { exact (we3a (w_gp e) (w_tp e) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (w_F e) (w_fc e) m (wSP e) (wS1 e) ff (w_lo e) c d
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) F3 ltac:(lia) ltac:(lia) FSH FAPP
                  ltac:(exact (Zv m (ff + 392) 0 (ff + 392) PV3 ltac:(lia) ltac:(lia))) ltac:(exact (Zv m (ff + 392) 8 (ff + 400) PV3 ltac:(lia) ltac:(lia)))
                  ltac:(lia) (winv_stk H _ _ _ _ _ _ _ HI) (winv_mi H _ _ _ _ _ _ _ HI)). }
    intros ms1 (u5 & u6 & u7 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & m1 & EQ1 & MU1 & WM1 & MI1 & ST1). subst ms1.
    assert (HI1 : winv H e ff fp [] sk LBk m1)
      by (eapply (winv_munch H HB); [exact HP | exact HI | exact MU1 | exact WM1 | exact MI1 | exact ST1 | apply Forall_nil]).

    eapply (wmc0 H HB e ff fp [] sk LBk m1); [exact HP | exact HI1 | exact IN | exact LBI |].
    intros m2 v0 v1 v2 v11 v12 v13 v14 v15 v16 v17 v28 v29 v30 v31 HI2 MU2 WM2.
    rewrite (ret_pc_even WO_MC3_RA ltac:(unfold WO_MC3_RA; lia) eq_refl).

    assert (PV3' : rw_cells asegs m2 (ff + 392) Z24).
    { eapply rw_cells_transport; [| exact MU2 | exact WM2 | cbn; unfold AINTRIN_STACK; zdj].
      eapply rw_cells_transport; [exact PV3 | exact MU1 | exact WM1 | exact I]. }
    eapply evt_cut.
    { exact (we3b (w_gp e) (w_tp e) v0 v1 v2 v11 v12 v13 v14 v15 v16 v17 v28 v29 v30 v31 (w_F e) (w_fc e) m2 (wSP e) (wS1 e) ff (w_lo e) d
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) F3 ltac:(lia) ltac:(lia) FSH FAPP
                  (WFW m2 (ff + 392) 24 HI2 ltac:(lia) ltac:(lia)) ltac:(exact (Zv m2 (ff + 392) 16 (ff + 408) PV3' ltac:(lia) ltac:(lia)))
                  ltac:(lia) (winv_stk H _ _ _ _ _ _ _ HI2) (winv_mi H _ _ _ _ _ _ _ HI2)). }
    intros ms3 (k5 & k6 & k7 & k14 & k15 & k16 & k17 & k28 & k29 & k30 & k31 & m3 & EQ3 & MU3 & WM3 & MI3 & ST3 & CV3). subst ms3.
    assert (HI3 : winv H e ff fp [] sk LBk m3).
    { eapply (winv_munch H HB); [exact HP | exact HI2 | exact MU3 | exact WM3 | exact MI3 | exact ST3 |].
      unfold wwin, WO_FLAGP. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]. right; left. lia. }

    assert (SB3 : SHAD m3 d (shadow_of 100)).
    { destruct AD as [_ SB]. eapply SHAD_transport; [| exact MU3 | exact WM3 | rewrite shadow_of_length by lia; cbn; zdj].
      eapply SHAD_transport; [| exact MU2 | exact WM2 | rewrite shadow_of_length by lia; cbn; unfold AINTRIN_STACK; zdj].
      eapply SHAD_transport; [exact SB | exact MU1 | exact WM1 | exact I]. }
    eapply (wann H HB e ff fp [] sk LBk m3); [exact HHb | exact HP | exact HI3 | exact IN | exact LBI | exact SB3 | lia |].
    intros m4 w0 w1 w2 w10 w11 w12 w13 w14 w15 w16 w17 w28 w29 w30 w31 HI4 MU4 WM4 SB4.
    rewrite (ret_pc_even WO_AN3_RA ltac:(unfold WO_AN3_RA; lia) eq_refl).

    pose proof (munch_app _ _ _ _ _ MU3 MU4) as N3. pose proof (wmono_trans asegs _ _ _ WM3 WM4) as V3.
    pose proof (munch_app _ _ _ _ _ MU2 N3) as N2. pose proof (wmono_trans asegs _ _ _ WM2 V3) as V2.
    pose proof (munch_app _ _ _ _ _ MU1 N2) as N1. pose proof (wmono_trans asegs _ _ _ WM1 V2) as V1.
    cbn [app] in N1, N2, N3.
    assert (DJ4 : forall A n, (A + n <= d \/ d + 100 <= A) -> (A + n <= sh d \/ sh d + nsh 100 <= A) ->
                    (A + n <= ff + 392 \/ ff + 416 <= A) -> (A + n <= wS1 e - 4096 \/ wS1 e <= A) ->
                    disjoint_from [(d, d + 0); (wS1 e - AINTRIN_STACK, wS1 e); (ff + 392, ff + 416); (sh d, sh d + nsh 100);
                                   (wS1 e - AINTRIN_STACK, wS1 e)] A n).
    { intros A n K1 K2 K3 K4. unfold AINTRIN_STACK. cbn. lia. }

    eapply evt_cut.
    { exact (we3c (w_gp e) (w_tp e) w0 w1 w2 w10 w11 w12 w13 w14 w15 w16 w17 w28 w29 w30 w31 (w_F e) (w_fc e) m4 (wSP e) (wS1 e) ff (w_lo e) d
                  (w_words e) (w_n e)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) F3 ltac:(lia) ltac:(lia) FSH FAPP
                  ltac:(rewrite Z.add_0_r; eapply rw_cells_transport; [exact SP0 | exact N1 | exact V1 | apply DJ4; lia])
                  ltac:(eapply rw_cells_transport; [exact SP8 | exact N1 | exact V1 | apply DJ4; cbn; lia])
                  ltac:(eapply rw_cells_transport; [exact SP16' | exact N1 | exact V1 | apply DJ4; cbn; lia])
                  WDS (winv_stk H _ _ _ _ _ _ _ HI4) (winv_mi H _ _ _ _ _ _ _ HI4)). }
    intros ms5 (y5 & y6 & y7 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m5 & EQ5 & MU5 & WM5 & MI5 & ST5 & TS5). subst ms5.
    assert (HI5 : winv H e ff fp [] sk LBk m5).
    { eapply (winv_munch H HB); [exact HP | exact HI4 | exact MU5 | exact WM5 | exact MI5 | exact ST5 |].
      unfold wwin, WO_SAVED. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]. left. lia. }

    eapply (wms_rs H HB e ff fp [] sk LBk m5); [exact HP | exact HI5 | lia | lia | lia |].
    intros m6 z0 z1 z2 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 HI6 MU6 WM6 Z6.
    rewrite (ret_pc_even WO_MS6_RA ltac:(unfold WO_MS6_RA; lia) eq_refl).
    eapply evt_cut.
    { exact (wt1 (w_gp e) (w_tp e) z0 z1 z2 (Z_to_bv 64 (wS1 e + 120)) z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 (w_F e) (w_fc e) m6
                 (wSP e) (wS1 e) ff (w_lo e) d
                 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) F3 ltac:(lia) ltac:(lia) FSH FAPP (winv_stk H _ _ _ _ _ _ _ HI6) (winv_mi H _ _ _ _ _ _ _ HI6)). }
    intros ms7 (i5 & i6 & i7 & i13 & i14 & i15 & i16 & i17 & i28 & i29 & i30 & i31 & m7 & EQ7 & MU7 & WM7 & MI7 & ST7). subst ms7.
    assert (HI7 : winv H e ff fp [] sk LBk m7)
      by (eapply (winv_munch H HB); [exact HP | exact HI6 | exact MU7 | exact WM7 | exact MI7 | exact ST7 | apply Forall_nil]).
    eapply (wms_rs H HB e ff fp [] sk LBk m7); [exact HP | exact HI7 | lia | lia | lia |].
    intros m8 j0 j1 j2 j11 j12 j13 j14 j15 j16 j17 j28 j29 j30 j31 HI8 MU8 WM8 Z8.
    rewrite (ret_pc_even WO_MS7_RA ltac:(unfold WO_MS7_RA; lia) eq_refl).
    eapply evt_cut.
    { exact (wt2 (w_gp e) (w_tp e) j0 j1 j2 (Z_to_bv 64 (wS1 e + 96)) j11 j12 j13 j14 j15 j16 j17 j28 j29 j30 j31 (w_F e) (w_fc e) m8
                 (wSP e) (wS1 e) ff (w_lo e) d
                 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) F3 ltac:(lia) ltac:(lia) FSH FAPP (winv_stk H _ _ _ _ _ _ _ HI8) (winv_mi H _ _ _ _ _ _ _ HI8)). }
    intros ms9 (n5 & n6 & n7 & n13 & n14 & n15 & n16 & n17 & n28 & n29 & n30 & n31 & m9 & EQ9 & MU9 & WM9 & MI9 & ST9 & C9). subst ms9.
    assert (HI9 : winv H e ff fp [] sk LBk m9).
    { eapply (winv_munch H HB); [exact HP | exact HI8 | exact MU9 | exact WM9 | exact MI9 | exact ST9 |].
      unfold wwin, WO_SAVED. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]. left. lia. }
    eapply (wms_rs H HB e ff fp [] sk LBk m9); [exact HP | exact HI9 | lia | lia | lia |].
    intros m10 o0 o1 o2 o11 o12 o13 o14 o15 o16 o17 o28 o29 o30 o31 HI10 MU10 WM10 Z10.
    rewrite (ret_pc_even WO_MS8_RA ltac:(unfold WO_MS8_RA; lia) eq_refl).
    eapply evt_cut.
    { exact (wt3 (w_gp e) (w_tp e) o0 o1 o2 (Z_to_bv 64 (wS1 e + 160)) o11 o12 o13 o14 o15 o16 o17 o28 o29 o30 o31 (w_F e) (w_fc e) m10
                 (wSP e) (wS1 e) ff (w_lo e) d
                 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) F3 ltac:(lia) ltac:(lia) FSH FAPP (winv_stk H _ _ _ _ _ _ _ HI10) (winv_mi H _ _ _ _ _ _ _ HI10)). }
    intros ms11 (q5 & q6 & q7 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & m11 & EQ11 & MU11 & WM11 & MI11 & ST11 & C11). subst ms11.
    assert (HI11 : winv H e ff fp [] sk LBk m11).
    { eapply (winv_munch H HB); [exact HP | exact HI10 | exact MU11 | exact WM11 | exact MI11 | exact ST11 |].
      unfold wwin, WO_SAVED. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]. left. lia. }
    eapply (wms_rs H HB e ff fp [] sk LBk m11); [exact HP | exact HI11 | lia | lia | lia |].
    intros m12 g0 g1 g2 g11 g12 g13 g14 g15 g16 g17 g28 g29 g30 g31 HI12 MU12 WM12 Z12.
    rewrite (ret_pc_even WO_MS9_RA ltac:(unfold WO_MS9_RA; lia) eq_refl).
    eapply evt_cut.
    { exact (wt4 (w_gp e) (w_tp e) g0 g1 g2 (Z_to_bv 64 (wS1 e + 200)) g11 g12 g13 g14 g15 g16 g17 g28 g29 g30 g31 (w_F e) (w_fc e) m12
                 (wSP e) (wS1 e) ff (w_lo e) d
                 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) F3 ltac:(lia) ltac:(lia) FSH FAPP (winv_stk H _ _ _ _ _ _ _ HI12) (winv_mi H _ _ _ _ _ _ _ HI12)). }
    intros ms13 (h5 & h6 & h7 & h13 & h14 & h15 & h16 & h17 & h28 & h29 & h30 & h31 & m13 & EQ13 & MU13 & WM13 & MI13 & ST13 & C13). subst ms13.
    assert (HI13 : winv H e ff fp [] sk LBk m13).
    { eapply (winv_munch H HB); [exact HP | exact HI12 | exact MU13 | exact WM13 | exact MI13 | exact ST13 |].
      unfold wwin, WO_SAVED. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]. left. lia. }
    eapply (wms_rs H HB e ff fp [] sk LBk m13); [exact HP | exact HI13 | lia | lia | lia |].
    intros m14 f0 f1 f2 f11 f12 f13 f14 f15 f16 f17 f28 f29 f30 f31 HI14 MU14 WM14 Z14.
    rewrite (ret_pc_even WO_MS10_RA ltac:(unfold WO_MS10_RA; lia) eq_refl).
    eapply evt_cut.
    { exact (wt5 (w_gp e) (w_tp e) f0 f1 f2 (Z_to_bv 64 (wS1 e + 240)) f11 f12 f13 f14 f15 f16 f17 f28 f29 f30 f31 (w_F e) (w_fc e) m14
                 (wSP e) (wS1 e) ff (w_lo e) d
                 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) F3 ltac:(lia) ltac:(lia) FSH FAPP (winv_stk H _ _ _ _ _ _ _ HI14) (winv_mi H _ _ _ _ _ _ _ HI14)). }
    intros ms15 (l5 & l6 & l7 & l11 & l12 & l13 & l14 & l15 & l16 & l17 & l28 & l29 & l30 & l31 & m15 & EQ15 & MU15 & WM15 & MI15 & ST15). subst ms15.
    apply evt_done.
    assert (HI15 : winv H e ff fp [] sk LBk m15)
      by (eapply (winv_munch H HB); [exact HP | exact HI14 | exact MU15 | exact WM15 | exact MI15 | exact ST15 | apply Forall_nil]).
    exists l5, l6, l7, l11, l12, l13, l14, l15, l16, l17, l28, l29, l30, l31, m15. split; [reflexivity|].
    split; [exact HI15|].

    destruct (wtst_fill1 (wS1 e) m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 (w_words e) (w_n e) ltac:(lia) TS5 MU6 WM6 Z6 MU7 WM7
                MU8 WM8 Z8 MU9 WM9 C9 MU10 WM10 Z10 MU11 WM11 C11 MU12 WM12 Z12 MU13 WM13 C13 MU14 WM14 Z14 MU15 WM15) as (WT & S6 & U6).
    pose proof (munch_app _ _ _ _ _ MU5 S6) as S5. pose proof (wmono_trans asegs _ _ _ WM5 U6) as U5.
    pose proof (munch_app _ _ _ _ _ N1 S5) as S1f. pose proof (wmono_trans asegs _ _ _ V1 U5) as U1f.
    cbn [app] in S1f, S5.
    split; [eapply (wfc_munch H e ff m m15); [exact WC | exact S1f | exact U1f |]; unfold wfc_apart, AINTRIN_STACK;
            repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; zdj|].
    split; [eapply rw_cells_transport; [exact C48 | exact S1f | exact U1f | cbn; unfold AINTRIN_STACK; zdj]|].
    split.
    { split; [eapply rw_cells_transport; [exact PZ | exact S1f | exact U1f | cbn; unfold AINTRIN_STACK; zdj]|].
      split; [unfold st_maps_cells in *; destruct PM as (Y5 & Y6 & Y7 & Y8 & Y9 & Y10);
              refine (conj _ (conj _ (conj _ (conj _ (conj _ _)))));
              (eapply rw_cells_transport; [eassumption | exact S1f | exact U1f | cbn; unfold AINTRIN_STACK; zdj])|].
      split; [eapply rw_cells_transport; [exact PV1 | exact S1f | exact U1f | cbn; unfold AINTRIN_STACK; zdj]|].
      split; [eapply rw_cells_transport; [exact PV2 | exact S1f | exact U1f | cbn; unfold AINTRIN_STACK; zdj]|].
      eapply rw_cells_transport; [| exact S5 | exact U5 | cbn; unfold AINTRIN_STACK; lia].
      eapply rw_cells_transport; [exact CV3 | exact MU4 | exact WM4 | cbn; unfold AINTRIN_STACK; zdj]. }
    split; [eapply wblk_munch; [exact WB | exact S1f | exact U1f | lia | unfold AINTRIN_STACK; zdj]|].
    split; [eapply wblk_munch; [exact WCc | exact S1f | exact U1f | lia | unfold AINTRIN_STACK; zdj]|].
    split; [split; [exact (wr_at_wmono _ _ _ _ WRd U1f) |]|].
    { eapply SHAD_transport; [exact SB4 | exact S5 | exact U5 | rewrite cc_gen_length by lia; cbn; unfold AINTRIN_STACK; lia]. }
    exact WT.
  Qed.
End WoQ.
