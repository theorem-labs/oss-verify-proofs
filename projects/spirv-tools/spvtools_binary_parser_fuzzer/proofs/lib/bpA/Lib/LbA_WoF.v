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
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbA_PrsStmt LbA_StateStmt LbA_SR LbA_Conv LbA_WoGen LbA_WoDefs LbA_WoKit LbA_WoSt LbA_WoMs LbA_WoCall LbA_WoCut LbA_WoZ.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbA_WoR2 LbA_WoR3 LbA_WoR4 LbA_WoR5 LbA_WoE0 LbA_WoE0b LbA_WoP LbA_WoQ.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section WoF.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHb : asan_rt_hyps_bp H.
  Let HB := rt_bp_base H HHb.

  Definition wps3 (ff : Z) (m : mem) (b1 b2 b3 : Z) : Prop :=
    wpst ff m (vtrip b1 500) (vtrip b2 100) (vtrip b3 100) /\ wblk m b1 500 /\ wblk m b2 100 /\ wblk m b3 100.

  Lemma wtst_upd1 : forall S1 m m' W words n v1 v2 v3 v1', wtst S1 m words n v1 v2 v3 -> rw_cells asegs m' (S1 + 240) v1' ->
    munch W m m' -> wmono asegs m m' -> v24 v2 -> v24 v3 ->
    Forall (fun iv : Z * Z => (snd iv <= S1 + 72 \/ S1 + 240 <= fst iv) /\ (snd iv <= S1 + 264 \/ S1 + 312 <= fst iv)) W ->
    wtst S1 m' words n v1' v2 v3.
  Proof.
    intros S1 m m' W words n v1 v2 v3 v1' (C0 & C1 & (M1 & F1 & M2 & F2 & M3 & F3) & V1 & V2 & V3) V1' MU WM Sz2 Sz3 FW.
    unfold v24 in *.
    assert (DJ : forall A k, (S1 + 72 <= A /\ A + k <= S1 + 240) \/ (S1 + 264 <= A /\ A + k <= S1 + 312) -> disjoint_from W A k).
    { intros A k X. clear - FW X. induction W as [|[x y] W IH]; cbn; [exact I|].
      inversion FW as [|? ? K K2]; subst. cbn in K. split; [lia | apply IH; exact K2]. }
    split; [eapply rw_cells_transport; [exact C0 | exact MU | exact WM | apply DJ; cbn; lia]|].
    split; [eapply rw_cells_transport; [exact C1 | exact MU | exact WM | apply DJ; cbn; lia]|].
    split; [unfold st_maps_cells; refine (conj _ (conj _ (conj _ (conj _ (conj _ _)))));
            (eapply rw_cells_transport; [eassumption | exact MU | exact WM | apply DJ; cbn; lia])|].
    split; [exact V1'|].
    split; [eapply rw_cells_transport; [exact V2 | exact MU | exact WM | apply DJ; rewrite ?Sz2; cbn; lia]|].
    eapply rw_cells_transport; [exact V3 | exact MU | exact WM | apply DJ; rewrite ?Sz3; cbn; lia].
  Qed.

  Lemma wtst_upd2 : forall S1 m m' W words n v1 v2 v3 v2', wtst S1 m words n v1 v2 v3 -> rw_cells asegs m' (S1 + 264) v2' ->
    munch W m m' -> wmono asegs m m' -> v24 v1 -> v24 v3 ->
    Forall (fun iv : Z * Z => (snd iv <= S1 + 72 \/ S1 + 264 <= fst iv) /\ (snd iv <= S1 + 288 \/ S1 + 312 <= fst iv)) W ->
    wtst S1 m' words n v1 v2' v3.
  Proof.
    intros S1 m m' W words n v1 v2 v3 v2' (C0 & C1 & (M1 & F1 & M2 & F2 & M3 & F3) & V1 & V2 & V3) V2' MU WM Sz1 Sz3 FW.
    unfold v24 in *.
    assert (DJ : forall A k, (S1 + 72 <= A /\ A + k <= S1 + 264) \/ (S1 + 288 <= A /\ A + k <= S1 + 312) -> disjoint_from W A k).
    { intros A k X. clear - FW X. induction W as [|[x y] W IH]; cbn; [exact I|].
      inversion FW as [|? ? K K2]; subst. cbn in K. split; [lia | apply IH; exact K2]. }
    split; [eapply rw_cells_transport; [exact C0 | exact MU | exact WM | apply DJ; cbn; lia]|].
    split; [eapply rw_cells_transport; [exact C1 | exact MU | exact WM | apply DJ; cbn; lia]|].
    split; [unfold st_maps_cells; refine (conj _ (conj _ (conj _ (conj _ (conj _ _)))));
            (eapply rw_cells_transport; [eassumption | exact MU | exact WM | apply DJ; cbn; lia])|].
    split; [eapply rw_cells_transport; [exact V1 | exact MU | exact WM | apply DJ; rewrite ?Sz1; cbn; lia]|].
    split; [exact V2'|].
    eapply rw_cells_transport; [exact V3 | exact MU | exact WM | apply DJ; rewrite ?Sz3; cbn; lia].
  Qed.

  Lemma wtst_upd3 : forall S1 m m' W words n v1 v2 v3 v3', wtst S1 m words n v1 v2 v3 -> rw_cells asegs m' (S1 + 288) v3' ->
    munch W m m' -> wmono asegs m m' -> v24 v1 -> v24 v2 ->
    Forall (fun iv : Z * Z => snd iv <= S1 + 72 \/ S1 + 288 <= fst iv) W ->
    wtst S1 m' words n v1 v2 v3'.
  Proof.
    intros S1 m m' W words n v1 v2 v3 v3' (C0 & C1 & (M1 & F1 & M2 & F2 & M3 & F3) & V1 & V2 & V3) V3' MU WM Sz1 Sz2 FW.
    unfold v24 in *.
    assert (DJ : forall A k, S1 + 72 <= A -> A + k <= S1 + 288 -> disjoint_from W A k).
    { intros A k X1 X2. clear - FW X1 X2. induction W as [|[x y] W IH]; cbn; [exact I|].
      inversion FW as [|? ? K K2]; subst. cbn in K. split; [lia | apply IH; exact K2]. }
    split; [eapply rw_cells_transport; [exact C0 | exact MU | exact WM | apply DJ; cbn; lia]|].
    split; [eapply rw_cells_transport; [exact C1 | exact MU | exact WM | apply DJ; cbn; lia]|].
    split; [unfold st_maps_cells; refine (conj _ (conj _ (conj _ (conj _ (conj _ _)))));
            (eapply rw_cells_transport; [eassumption | exact MU | exact WM | apply DJ; cbn; lia])|].
    split; [eapply rw_cells_transport; [exact V1 | exact MU | exact WM | apply DJ; rewrite ?Sz1; cbn; lia]|].
    split; [eapply rw_cells_transport; [exact V2 | exact MU | exact WM | apply DJ; rewrite ?Sz2; cbn; lia]|].
    exact V3'.
  Qed.

  Lemma wps3_munch : forall ff m m' W b1 b2 b3, wps3 ff m b1 b2 b3 -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => (snd iv <= ff + 176 \/ ff + 416 <= fst iv)
                              /\ (snd iv <= sh b1 \/ sh b1 + nsh 500 <= fst iv) /\ (snd iv <= sh b2 \/ sh b2 + nsh 100 <= fst iv)
                              /\ (snd iv <= sh b3 \/ sh b3 + nsh 100 <= fst iv)) W ->
    wps3 ff m' b1 b2 b3.
  Proof.
    intros ff m m' W b1 b2 b3 (P & W1 & W2 & W3) MU WM FW.
    split; [eapply wpst_munch; [exact P | exact MU | exact WM | reflexivity | reflexivity | reflexivity |]; eapply Forall_impl; [|exact FW]; intros iv K; apply K|].
    split; [eapply wblk_munch; [exact W1 | exact MU | exact WM | lia |]; eapply Forall_impl; [|exact FW]; intros iv K; apply K|].
    split; [eapply wblk_munch; [exact W2 | exact MU | exact WM | lia |]; eapply Forall_impl; [|exact FW]; intros iv K; apply K|].
    eapply wblk_munch; [exact W3 | exact MU | exact WM | lia |]; eapply Forall_impl; [|exact FW]; intros iv K; apply K.
  Qed.

  Definition wq1_pre (e : went H) (ff d g : Z) (m : mem) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) : machine_state :=
    MS (mkR (Z_to_bv 64 WO_ON4_RA) (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) t0 t1 t2 (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
            (Z_to_bv 64 g) a1 a2 a3 a4 a5 a6 a7
            (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) (Z_to_bv 64 0x3f800000) (Z_to_bv 64 (wS1 e + 96)) (Z_to_bv 64 99) (Z_to_bv 64 0)
            (Z_to_bv 64 d) (Z_to_bv 64 (d + 100)) (Z_to_bv 64 0) (Z_to_bv 64 (ff + 128)) t3 t4 t5 t6)
       (w_F e) (Z_to_bv 64 WO_ON4_RA) (w_fc e) None m (seg_rom asegs).

  Definition wq1_post (e : went H) (ff fp : Z) (sk : as_St H) (LBk : list block) (b1 b2 b3 d g : Z) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m',
      ms' = MS (mkR (Z_to_bv 64 WO_ON5_RA) (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) x5 x6 x7 (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
                    (Z_to_bv 64 100) x11 x12 x13 x14 x15 x16 x17
                    (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) (Z_to_bv 64 0x3f800000) (Z_to_bv 64 (wS1 e + 96)) (Z_to_bv 64 99)
                    (Z_to_bv 64 0) (Z_to_bv 64 d) (Z_to_bv 64 (d + 100)) (Z_to_bv 64 0) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31)
               (w_F e) (Z_to_bv 64 AOPNEW) (w_fc e) None m' (seg_rom asegs)
      /\ winv H e ff fp [] sk LBk m' /\ wfc H e ff m' /\ rw_cells asegs m' (wS1 e + 48) [C8 (Z_to_bv 64 (ff + 176))]
      /\ wps3 ff m' b1 b2 b3 /\ wtst (wS1 e) m' (w_words e) (w_n e) (vtrip g 500) Z24 Z24 /\ wblk m' g 500.

  Lemma wq1 : forall (e : went H) ff fp sk LBk (p1 p2 p3 p4 : bptr) b1 b2 b3 d g m t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    wpre H e -> winv H e ff fp [] sk LBk m ->
    In (p1, b1, 500) LBk -> In (p2, b2, 100) LBk -> In (p3, b3, 100) LBk -> In (p4, g, 500) LBk ->
    p1 <> p4 -> p2 <> p4 -> p3 <> p4 ->
    (forall bb, In bb (w_LB e) -> In bb LBk /\ blk_id bb <> p4) ->
    wfc H e ff m -> rw_cells asegs m (wS1 e + 48) [C8 (Z_to_bv 64 (ff + 176))] ->
    wps3 ff m b1 b2 b3 -> wtst (wS1 e) m (w_words e) (w_n e) Z24 Z24 Z24 -> addressable m g 500 -> wr_at asegs m g 500 ->
    evt asegs (wq1_post e ff fp sk LBk b1 b2 b3 d g) (wq1_pre e ff d g m t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6).
  Proof.
    intros e ff fp sk LBk p1 p2 p3 p4 b1 b2 b3 d g m t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 HP HI IN1 IN2 IN3 IN NE1 NE2 NE3 LBI WC C48 PS TS AD WRg.
    pose proof (wpre_geo H e HP) as (CE & LO & SSHI & SHIH & SP16 & TP).
    pose proof (wS1_facts H e HP) as (S32 & S1SP & S1L & SPH & LOS1 & _).
    pose proof (wframe_z H _ _ _ (winv_ff H _ _ _ _ _ _ _ HI)) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & FAPP & FSH).
    pose proof (wblk_geo H HB e ff fp [] sk LBk m p4 g 500 HP HI IN) as (G0 & G16 & Gn & GC & GH & GSA & GSC & GLO & GLS & GF & GSF & GSS & GSB & GSH).
    pose proof (wblk_geo H HB e ff fp [] sk LBk m p1 b1 500 HP HI IN1) as (_ & _ & _ & _ & _ & J1 & _).
    pose proof (wblk_geo H HB e ff fp [] sk LBk m p2 b2 100 HP HI IN2) as (_ & _ & _ & _ & _ & J2 & _).
    pose proof (wblk_geo H HB e ff fp [] sk LBk m p3 b3 100 HP HI IN3) as (_ & _ & _ & _ & _ & J3 & _).
    pose proof (wblk2_geo H HB _ _ _ p1 b1 500 p4 g 500 (winv_rh H _ _ _ _ _ _ _ HI) IN1 IN NE1) as (_ & _ & _ & X1).
    pose proof (wblk2_geo H HB _ _ _ p2 b2 100 p4 g 500 (winv_rh H _ _ _ _ _ _ _ HI) IN2 IN NE2) as (_ & _ & _ & X2).
    pose proof (wblk2_geo H HB _ _ _ p3 b3 100 p4 g 500 (winv_rh H _ _ _ _ _ _ _ HI) IN3 IN NE3) as (_ & _ & _ & X3).
    pose proof aceil_facts as ACF.
    assert (Zv : forall mm a k a', rw_cells asegs mm a Z24 -> 0 <= k <= 16 -> a' = a + k -> rw_cells asegs mm a' [CB 8 (poison_bytes 8 0)])
      by (intros mm a k a' X Hk Ea; subst a'; exact (zero_cells_sub mm a 24 k 8 X ltac:(lia) ltac:(lia))).
    pose proof TS as (_ & _ & _ & _ & TV2 & _).
    unfold wq1_pre.

    eapply evt_cut.
    { exact (wf1a (w_gp e) (w_tp e) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (w_F e) (w_fc e) m (wSP e) (wS1 e) ff (w_lo e) d g
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) F3 ltac:(lia) ltac:(lia) FSH FAPP
                  ltac:(lia) (winv_stk H _ _ _ _ _ _ _ HI) (winv_mi H _ _ _ _ _ _ _ HI)). }
    intros ms1 (u5 & u6 & u7 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & m1 & EQ1 & MU1 & WM1 & MI1 & ST1 & CV1). subst ms1.
    assert (HI1 : winv H e ff fp [] sk LBk m1).
    { eapply (winv_munch H HB); [exact HP | exact HI | exact MU1 | exact WM1 | exact MI1 | exact ST1 |].
      unfold wwin, WO_SAVED. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]. left. lia. }

    assert (SB1 : SHAD m1 g (shadow_of 500)).
    { destruct AD as [_ SB]. eapply SHAD_transport; [exact SB | exact MU1 | exact WM1 | rewrite shadow_of_length by lia; cbn; lia]. }
    eapply (wann H HB e ff fp [] sk LBk m1); [exact HHb | exact HP | exact HI1 | exact IN | exact LBI | exact SB1 | lia |].
    intros m2 w0 w1 w2 w10 w11 w12 w13 w14 w15 w16 w17 w28 w29 w30 w31 HI2 MU2 WM2 SB2.
    rewrite (ret_pc_even WO_AN4_RA ltac:(unfold WO_AN4_RA; lia) eq_refl).

    assert (TV2' : rw_cells asegs m2 (wS1 e + 264) Z24).
    { eapply rw_cells_transport; [| exact MU2 | exact WM2 | cbn; unfold AINTRIN_STACK; lia].
      eapply rw_cells_transport; [exact TV2 | exact MU1 | exact WM1 | cbn; lia]. }
    eapply evt_cut.
    { exact (wf1b (w_gp e) (w_tp e) w0 w1 w2 w10 w11 w12 w13 w14 w15 w16 w17 w28 w29 w30 w31 (w_F e) (w_fc e) m2 (wSP e) (wS1 e) ff (w_lo e) d
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) F3 ltac:(lia) ltac:(lia) FSH FAPP
                  ltac:(exact (Zv m2 (wS1 e + 264) 0 (wS1 e + 264) TV2' ltac:(lia) ltac:(lia)))
                  ltac:(exact (Zv m2 (wS1 e + 264) 16 (wS1 e + 280) TV2' ltac:(lia) ltac:(lia)))
                  ltac:(exact (Zv m2 (wS1 e + 264) 8 (wS1 e + 272) TV2' ltac:(lia) ltac:(lia)))
                  (winv_stk H _ _ _ _ _ _ _ HI2) (winv_mi H _ _ _ _ _ _ _ HI2)). }
    intros ms3 (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m3 & EQ3 & MU3 & WM3 & MI3 & ST3). subst ms3.
    apply evt_done.
    assert (HI3 : winv H e ff fp [] sk LBk m3)
      by (eapply (winv_munch H HB); [exact HP | exact HI2 | exact MU3 | exact WM3 | exact MI3 | exact ST3 | apply Forall_nil]).
    exists y5, y6, y7, y11, y12, y13, y14, y15, y16, y17, y28, y29, y30, y31, m3. split; [reflexivity|].
    split; [exact HI3|].
    pose proof (munch_app _ _ _ _ _ MU2 MU3) as M2. pose proof (wmono_trans asegs _ _ _ WM2 WM3) as V2.
    pose proof (munch_app _ _ _ _ _ MU1 M2) as M1. pose proof (wmono_trans asegs _ _ _ WM1 V2) as V1.
    cbn [app] in M1, M2.
    split; [eapply (wfc_munch H e ff m m3); [exact WC | exact M1 | exact V1 |]; unfold wfc_apart, AINTRIN_STACK;
            repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; zdj|].
    split; [eapply rw_cells_transport; [exact C48 | exact M1 | exact V1 | cbn; unfold AINTRIN_STACK; zdj]|].
    split; [eapply wps3_munch; [exact PS | exact M1 | exact V1 | unfold AINTRIN_STACK; zdj]|].
    split; [eapply wtst_upd1; [exact TS | | exact M1 | exact V1 | reflexivity | reflexivity | unfold AINTRIN_STACK; zdj];
            eapply rw_cells_transport; [exact CV1 | exact M2 | exact V2 | cbn; unfold AINTRIN_STACK; lia]|].
    split; [exact (wr_at_wmono _ _ _ _ WRg V1)|].
    eapply SHAD_transport; [exact SB2 | exact MU3 | exact WM3 | exact I].
  Qed.

  Definition wq2_pre (e : went H) (ff d h : Z) (m : mem) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) : machine_state :=
    MS (mkR (Z_to_bv 64 WO_ON5_RA) (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) t0 t1 t2 (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
            (Z_to_bv 64 h) a1 a2 a3 a4 a5 a6 a7
            (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) (Z_to_bv 64 0x3f800000) (Z_to_bv 64 (wS1 e + 96)) (Z_to_bv 64 99) (Z_to_bv 64 0)
            (Z_to_bv 64 d) (Z_to_bv 64 (d + 100)) (Z_to_bv 64 0) (Z_to_bv 64 (ff + 128)) t3 t4 t5 t6)
       (w_F e) (Z_to_bv 64 WO_ON5_RA) (w_fc e) None m (seg_rom asegs).

  Definition wq2_post (e : went H) (ff fp : Z) (sk : as_St H) (LBk : list block) (b1 b2 b3 g h : Z) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m',
      ms' = MS (mkR (Z_to_bv 64 WO_ON6_RA) (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) x5 x6 x7 (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
                    (Z_to_bv 64 100) x11 x12 x13 x14 x15 x16 x17
                    (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) (Z_to_bv 64 0) (Z_to_bv 64 h) (Z_to_bv 64 99)
                    (Z_to_bv 64 0) (Z_to_bv 64 (h + 100)) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31)
               (w_F e) (Z_to_bv 64 AOPNEW) (w_fc e) None m' (seg_rom asegs)
      /\ winv H e ff fp [] sk LBk m' /\ wfc H e ff m' /\ rw_cells asegs m' (wS1 e + 48) [C8 (Z_to_bv 64 (ff + 176))]
      /\ wps3 ff m' b1 b2 b3 /\ wtst (wS1 e) m' (w_words e) (w_n e) (vtrip g 500) (vtrip h 100) Z24 /\ wblk m' g 500 /\ wblk m' h 100.

  Lemma wq2 : forall (e : went H) ff fp sk LBk (p1 p2 p3 p4 p5 : bptr) b1 b2 b3 d g h m t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    wpre H e -> winv H e ff fp [] sk LBk m ->
    In (p1, b1, 500) LBk -> In (p2, b2, 100) LBk -> In (p3, b3, 100) LBk -> In (p4, g, 500) LBk -> In (p5, h, 100) LBk ->
    p1 <> p5 -> p2 <> p5 -> p3 <> p5 -> p4 <> p5 ->
    (forall bb, In bb (w_LB e) -> In bb LBk /\ blk_id bb <> p5) ->
    wfc H e ff m -> rw_cells asegs m (wS1 e + 48) [C8 (Z_to_bv 64 (ff + 176))] ->
    wps3 ff m b1 b2 b3 -> wtst (wS1 e) m (w_words e) (w_n e) (vtrip g 500) Z24 Z24 -> wblk m g 500 ->
    addressable m h 100 -> wr_at asegs m h 100 ->
    evt asegs (wq2_post e ff fp sk LBk b1 b2 b3 g h) (wq2_pre e ff d h m t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6).
  Proof.
    intros e ff fp sk LBk p1 p2 p3 p4 p5 b1 b2 b3 d g h m t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 HP HI IN1 IN2 IN3 IN4 IN
      NE1 NE2 NE3 NE4 LBI WC C48 PS TS WG AD WRh.
    pose proof (wpre_geo H e HP) as (CE & LO & SSHI & SHIH & SP16 & TP).
    pose proof (wS1_facts H e HP) as (S32 & S1SP & S1L & SPH & LOS1 & _).
    pose proof (wframe_z H _ _ _ (winv_ff H _ _ _ _ _ _ _ HI)) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & FAPP & FSH).
    pose proof (wblk_geo H HB e ff fp [] sk LBk m p5 h 100 HP HI IN) as (G0 & G16 & Gn & GC & GH & GSA & GSC & GLO & GLS & GF & GSF & GSS & GSB & GSH).
    pose proof (wblk_geo H HB e ff fp [] sk LBk m p1 b1 500 HP HI IN1) as (_ & _ & _ & _ & _ & J1 & _).
    pose proof (wblk_geo H HB e ff fp [] sk LBk m p2 b2 100 HP HI IN2) as (_ & _ & _ & _ & _ & J2 & _).
    pose proof (wblk_geo H HB e ff fp [] sk LBk m p3 b3 100 HP HI IN3) as (_ & _ & _ & _ & _ & J3 & _).
    pose proof (wblk_geo H HB e ff fp [] sk LBk m p4 g 500 HP HI IN4) as (_ & _ & _ & _ & _ & J4 & _).
    pose proof (wblk2_geo H HB _ _ _ p1 b1 500 p5 h 100 (winv_rh H _ _ _ _ _ _ _ HI) IN1 IN NE1) as (_ & _ & _ & X1).
    pose proof (wblk2_geo H HB _ _ _ p2 b2 100 p5 h 100 (winv_rh H _ _ _ _ _ _ _ HI) IN2 IN NE2) as (_ & _ & _ & X2).
    pose proof (wblk2_geo H HB _ _ _ p3 b3 100 p5 h 100 (winv_rh H _ _ _ _ _ _ _ HI) IN3 IN NE3) as (_ & _ & _ & X3).
    pose proof (wblk2_geo H HB _ _ _ p4 g 500 p5 h 100 (winv_rh H _ _ _ _ _ _ _ HI) IN4 IN NE4) as (_ & _ & _ & X4).
    pose proof aceil_facts as ACF.
    assert (Zv : forall mm a k a', rw_cells asegs mm a Z24 -> 0 <= k <= 16 -> a' = a + k -> rw_cells asegs mm a' [CB 8 (poison_bytes 8 0)])
      by (intros mm a k a' X Hk Ea; subst a'; exact (zero_cells_sub mm a 24 k 8 X ltac:(lia) ltac:(lia))).
    pose proof TS as (_ & _ & _ & _ & TV2 & TV3).
    unfold wq2_pre.

    eapply evt_cut.
    { exact (wf2a (w_gp e) (w_tp e) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (w_F e) (w_fc e) m (wSP e) (wS1 e) ff (w_lo e) d h
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) F3 ltac:(lia) ltac:(lia) FSH FAPP
                  ltac:(exact (Zv m (wS1 e + 264) 0 (wS1 e + 264) TV2 ltac:(lia) ltac:(lia)))
                  ltac:(exact (Zv m (wS1 e + 264) 8 (wS1 e + 272) TV2 ltac:(lia) ltac:(lia)))
                  ltac:(lia) (winv_stk H _ _ _ _ _ _ _ HI) (winv_mi H _ _ _ _ _ _ _ HI)). }
    intros ms1 (u5 & u6 & u7 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & m1 & EQ1 & MU1 & WM1 & MI1 & ST1). subst ms1.
    assert (HI1 : winv H e ff fp [] sk LBk m1)
      by (eapply (winv_munch H HB); [exact HP | exact HI | exact MU1 | exact WM1 | exact MI1 | exact ST1 | apply Forall_nil]).

    eapply (wmc0 H HB e ff fp [] sk LBk m1); [exact HP | exact HI1 | exact IN | exact LBI |].
    intros m2 v0 v1 v2 v11 v12 v13 v14 v15 v16 v17 v28 v29 v30 v31 HI2 MU2 WM2.
    apply munch_drop0 in MU2.
    rewrite (ret_pc_even WO_MC5_RA ltac:(unfold WO_MC5_RA; lia) eq_refl).

    assert (TV2' : rw_cells asegs m2 (wS1 e + 264) Z24).
    { eapply rw_cells_transport; [| exact MU2 | exact WM2 | cbn; unfold AINTRIN_STACK; lia].
      eapply rw_cells_transport; [exact TV2 | exact MU1 | exact WM1 | exact I]. }
    eapply evt_cut.
    { exact (wf2b (w_gp e) (w_tp e) v0 v1 v2 v11 v12 v13 v14 v15 v16 v17 v28 v29 v30 v31 (w_F e) (w_fc e) m2 (wSP e) (wS1 e) ff (w_lo e) h
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) F3 ltac:(lia) ltac:(lia) FSH FAPP
                  ltac:(exact (Zv m2 (wS1 e + 264) 16 (wS1 e + 280) TV2' ltac:(lia) ltac:(lia)))
                  ltac:(lia) (winv_stk H _ _ _ _ _ _ _ HI2) (winv_mi H _ _ _ _ _ _ _ HI2)). }
    intros ms3 (k5 & k6 & k7 & k14 & k15 & k16 & k17 & k28 & k29 & k30 & k31 & m3 & EQ3 & MU3 & WM3 & MI3 & ST3 & CV3). subst ms3.
    assert (HI3 : winv H e ff fp [] sk LBk m3).
    { eapply (winv_munch H HB); [exact HP | exact HI2 | exact MU3 | exact WM3 | exact MI3 | exact ST3 |].
      unfold wwin, WO_SAVED. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]. left. lia. }

    assert (SB3 : SHAD m3 h (shadow_of 100)).
    { destruct AD as [_ SB]. eapply SHAD_transport; [| exact MU3 | exact WM3 | rewrite shadow_of_length by lia; cbn; lia].
      eapply SHAD_transport; [| exact MU2 | exact WM2 | rewrite shadow_of_length by lia; cbn; unfold AINTRIN_STACK; lia].
      eapply SHAD_transport; [exact SB | exact MU1 | exact WM1 | exact I]. }
    eapply (wann H HB e ff fp [] sk LBk m3); [exact HHb | exact HP | exact HI3 | exact IN | exact LBI | exact SB3 | lia |].
    intros m4 w0 w1 w2 w10 w11 w12 w13 w14 w15 w16 w17 w28 w29 w30 w31 HI4 MU4 WM4 SB4.
    rewrite (ret_pc_even WO_AN5_RA ltac:(unfold WO_AN5_RA; lia) eq_refl).

    pose proof (munch_app _ _ _ _ _ MU3 MU4) as N3. pose proof (wmono_trans asegs _ _ _ WM3 WM4) as W3.
    pose proof (munch_app _ _ _ _ _ MU2 N3) as N2. pose proof (wmono_trans asegs _ _ _ WM2 W3) as W2.
    pose proof (munch_app _ _ _ _ _ MU1 N2) as N1. pose proof (wmono_trans asegs _ _ _ WM1 W2) as W1.
    cbn [app] in N1, N2, N3.
    assert (TV3' : rw_cells asegs m4 (wS1 e + 288) Z24) by (eapply rw_cells_transport; [exact TV3 | exact N1 | exact W1 | cbn; unfold AINTRIN_STACK; lia]).
    eapply evt_cut.
    { exact (wf2c (w_gp e) (w_tp e) w0 w1 w2 w10 w11 w12 w13 w14 w15 w16 w17 w28 w29 w30 w31 (w_F e) (w_fc e) m4 (wSP e) (wS1 e) ff (w_lo e) h
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) F3 ltac:(lia) ltac:(lia) FSH FAPP
                  ltac:(exact (Zv m4 (wS1 e + 288) 0 (wS1 e + 288) TV3' ltac:(lia) ltac:(lia)))
                  ltac:(exact (Zv m4 (wS1 e + 288) 16 (wS1 e + 304) TV3' ltac:(lia) ltac:(lia)))
                  ltac:(exact (Zv m4 (wS1 e + 288) 8 (wS1 e + 296) TV3' ltac:(lia) ltac:(lia)))
                  (winv_stk H _ _ _ _ _ _ _ HI4) (winv_mi H _ _ _ _ _ _ _ HI4)). }
    intros ms5 (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m5 & EQ5 & MU5 & WM5 & MI5 & ST5). subst ms5.
    apply evt_done.
    assert (HI5 : winv H e ff fp [] sk LBk m5)
      by (eapply (winv_munch H HB); [exact HP | exact HI4 | exact MU5 | exact WM5 | exact MI5 | exact ST5 | apply Forall_nil]).
    exists y5, y6, y7, y11, y12, y13, y14, y15, y16, y17, y28, y29, y30, y31, m5. split; [reflexivity|].
    split; [exact HI5|].
    pose proof (munch_app _ _ _ _ _ N1 MU5) as M1. pose proof (wmono_trans asegs _ _ _ W1 WM5) as V1.
    cbn [app] in M1.
    split; [eapply (wfc_munch H e ff m m5); [exact WC | exact M1 | exact V1 |]; unfold wfc_apart, AINTRIN_STACK;
            repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; zdj|].
    split; [eapply rw_cells_transport; [exact C48 | exact M1 | exact V1 | cbn; unfold AINTRIN_STACK; zdj]|].
    split; [eapply wps3_munch; [exact PS | exact M1 | exact V1 | unfold AINTRIN_STACK; zdj]|].
    pose proof (munch_app _ _ _ _ _ MU4 MU5) as M4. pose proof (wmono_trans asegs _ _ _ WM4 WM5) as V4. cbn [app] in M4.
    split; [eapply wtst_upd2; [exact TS | | exact M1 | exact V1 | reflexivity | reflexivity | unfold AINTRIN_STACK; zdj];
            eapply rw_cells_transport; [exact CV3 | exact M4 | exact V4 | cbn; unfold AINTRIN_STACK; lia]|].
    split; [eapply wblk_munch; [exact WG | exact M1 | exact V1 | lia | unfold AINTRIN_STACK; zdj]|].
    split; [exact (wr_at_wmono _ _ _ _ WRh V1)|].
    eapply SHAD_transport; [exact SB4 | exact MU5 | exact WM5 | exact I].
  Qed.

  Definition wq3_pre (e : went H) (ff h k : Z) (m : mem) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) : machine_state :=
    MS (mkR (Z_to_bv 64 WO_ON6_RA) (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) t0 t1 t2 (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
            (Z_to_bv 64 k) a1 a2 a3 a4 a5 a6 a7
            (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) (Z_to_bv 64 0) (Z_to_bv 64 h) (Z_to_bv 64 99) (Z_to_bv 64 0)
            (Z_to_bv 64 (h + 100)) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (ff + 128)) t3 t4 t5 t6)
       (w_F e) (Z_to_bv 64 WO_ON6_RA) (w_fc e) None m (seg_rom asegs).

  Definition wq3_post (e : went H) (ff fp : Z) (sk : as_St H) (LBk : list block) (b1 b2 b3 g h k : Z) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m',
      ms' = MS (mkR (Z_to_bv 64 WO_MVA1_RA) (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) x5 x6 x7 (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
                    (Z_to_bv 64 (ff + 176)) (Z_to_bv 64 (wS1 e + 72)) x12 x13 x14 x15 x16 x17
                    (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) (Z_to_bv 64 0) (Z_to_bv 64 k) (Z_to_bv 64 99)
                    (Z_to_bv 64 k) (Z_to_bv 64 (k + 100)) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31)
               (w_F e) (Z_to_bv 64 AST_MVA) (w_fc e) None m' (seg_rom asegs)
      /\ winv H e ff fp [] sk LBk m' /\ wfc H e ff m' /\ rw_cells asegs m' (wS1 e + 48) [C8 (Z_to_bv 64 (ff + 176))]
      /\ wps3 ff m' b1 b2 b3 /\ wtst (wS1 e) m' (w_words e) (w_n e) (vtrip g 500) (vtrip h 100) (vtrip k 100)
      /\ wblk m' g 500 /\ wblk m' h 100 /\ wblk m' k 100.

  Lemma wq3 : forall (e : went H) ff fp sk LBk (p1 p2 p3 p4 p5 p6 : bptr) b1 b2 b3 g h k m t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    wpre H e -> winv H e ff fp [] sk LBk m ->
    In (p1, b1, 500) LBk -> In (p2, b2, 100) LBk -> In (p3, b3, 100) LBk -> In (p4, g, 500) LBk -> In (p5, h, 100) LBk ->
    In (p6, k, 100) LBk ->
    p1 <> p6 -> p2 <> p6 -> p3 <> p6 -> p4 <> p6 -> p5 <> p6 ->
    (forall bb, In bb (w_LB e) -> In bb LBk /\ blk_id bb <> p6) ->
    wfc H e ff m -> rw_cells asegs m (wS1 e + 48) [C8 (Z_to_bv 64 (ff + 176))] ->
    wps3 ff m b1 b2 b3 -> wtst (wS1 e) m (w_words e) (w_n e) (vtrip g 500) (vtrip h 100) Z24 -> wblk m g 500 -> wblk m h 100 ->
    addressable m k 100 -> wr_at asegs m k 100 ->
    evt asegs (wq3_post e ff fp sk LBk b1 b2 b3 g h k) (wq3_pre e ff h k m t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6).
  Proof.
    intros e ff fp sk LBk p1 p2 p3 p4 p5 p6 b1 b2 b3 g h k m t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 HP HI IN1 IN2 IN3 IN4 IN5 IN
      NE1 NE2 NE3 NE4 NE5 LBI WC C48 PS TS WG WH AD WRk.
    pose proof (wpre_geo H e HP) as (CE & LO & SSHI & SHIH & SP16 & TP).
    pose proof (wS1_facts H e HP) as (S32 & S1SP & S1L & SPH & LOS1 & _).
    pose proof (wframe_z H _ _ _ (winv_ff H _ _ _ _ _ _ _ HI)) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & FAPP & FSH).
    pose proof (wblk_geo H HB e ff fp [] sk LBk m p6 k 100 HP HI IN) as (G0 & G16 & Gn & GC & GH & GSA & GSC & GLO & GLS & GF & GSF & GSS & GSB & GSH).
    pose proof (wblk_geo H HB e ff fp [] sk LBk m p1 b1 500 HP HI IN1) as (_ & _ & _ & _ & _ & J1 & _).
    pose proof (wblk_geo H HB e ff fp [] sk LBk m p2 b2 100 HP HI IN2) as (_ & _ & _ & _ & _ & J2 & _).
    pose proof (wblk_geo H HB e ff fp [] sk LBk m p3 b3 100 HP HI IN3) as (_ & _ & _ & _ & _ & J3 & _).
    pose proof (wblk_geo H HB e ff fp [] sk LBk m p4 g 500 HP HI IN4) as (_ & _ & _ & _ & _ & J4 & _).
    pose proof (wblk_geo H HB e ff fp [] sk LBk m p5 h 100 HP HI IN5) as (_ & _ & _ & _ & _ & J5 & _).
    pose proof (wblk2_geo H HB _ _ _ p1 b1 500 p6 k 100 (winv_rh H _ _ _ _ _ _ _ HI) IN1 IN NE1) as (_ & _ & _ & X1).
    pose proof (wblk2_geo H HB _ _ _ p2 b2 100 p6 k 100 (winv_rh H _ _ _ _ _ _ _ HI) IN2 IN NE2) as (_ & _ & _ & X2).
    pose proof (wblk2_geo H HB _ _ _ p3 b3 100 p6 k 100 (winv_rh H _ _ _ _ _ _ _ HI) IN3 IN NE3) as (_ & _ & _ & X3).
    pose proof (wblk2_geo H HB _ _ _ p4 g 500 p6 k 100 (winv_rh H _ _ _ _ _ _ _ HI) IN4 IN NE4) as (_ & _ & _ & X4).
    pose proof (wblk2_geo H HB _ _ _ p5 h 100 p6 k 100 (winv_rh H _ _ _ _ _ _ _ HI) IN5 IN NE5) as (_ & _ & _ & X5).
    pose proof aceil_facts as ACF.
    assert (Zv : forall mm a k a', rw_cells asegs mm a Z24 -> 0 <= k <= 16 -> a' = a + k -> rw_cells asegs mm a' [CB 8 (poison_bytes 8 0)])
      by (intros mm a k0 a' X Hk Ea; subst a'; exact (zero_cells_sub mm a 24 k0 8 X ltac:(lia) ltac:(lia))).
    pose proof TS as (_ & _ & _ & _ & _ & TV3).
    unfold wq3_pre.

    eapply evt_cut.
    { exact (wf3a (w_gp e) (w_tp e) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (w_F e) (w_fc e) m (wSP e) (wS1 e) ff (w_lo e) h k
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) F3 ltac:(lia) ltac:(lia) FSH FAPP
                  ltac:(exact (Zv m (wS1 e + 288) 0 (wS1 e + 288) TV3 ltac:(lia) ltac:(lia)))
                  ltac:(exact (Zv m (wS1 e + 288) 8 (wS1 e + 296) TV3 ltac:(lia) ltac:(lia)))
                  ltac:(lia) (winv_stk H _ _ _ _ _ _ _ HI) (winv_mi H _ _ _ _ _ _ _ HI)). }
    intros ms1 (u5 & u6 & u7 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & m1 & EQ1 & MU1 & WM1 & MI1 & ST1). subst ms1.
    assert (HI1 : winv H e ff fp [] sk LBk m1)
      by (eapply (winv_munch H HB); [exact HP | exact HI | exact MU1 | exact WM1 | exact MI1 | exact ST1 | apply Forall_nil]).

    eapply (wmc0 H HB e ff fp [] sk LBk m1); [exact HP | exact HI1 | exact IN | exact LBI |].
    intros m2 v0 v1 v2 v11 v12 v13 v14 v15 v16 v17 v28 v29 v30 v31 HI2 MU2 WM2.
    apply munch_drop0 in MU2.
    rewrite (ret_pc_even WO_MC6_RA ltac:(unfold WO_MC6_RA; lia) eq_refl).

    assert (TV3' : rw_cells asegs m2 (wS1 e + 288) Z24).
    { eapply rw_cells_transport; [| exact MU2 | exact WM2 | cbn; unfold AINTRIN_STACK; lia].
      eapply rw_cells_transport; [exact TV3 | exact MU1 | exact WM1 | exact I]. }
    eapply evt_cut.
    { exact (wf3b (w_gp e) (w_tp e) v0 v1 v2 v11 v12 v13 v14 v15 v16 v17 v28 v29 v30 v31 (w_F e) (w_fc e) m2 (wSP e) (wS1 e) ff (w_lo e) k
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) F3 ltac:(lia) ltac:(lia) FSH FAPP
                  ltac:(exact (Zv m2 (wS1 e + 288) 16 (wS1 e + 304) TV3' ltac:(lia) ltac:(lia)))
                  ltac:(lia) (winv_stk H _ _ _ _ _ _ _ HI2) (winv_mi H _ _ _ _ _ _ _ HI2)). }
    intros ms3 (k5 & k6 & k7 & k14 & k15 & k16 & k17 & k28 & k29 & k30 & k31 & m3 & EQ3 & MU3 & WM3 & MI3 & ST3 & CV3). subst ms3.
    assert (HI3 : winv H e ff fp [] sk LBk m3).
    { eapply (winv_munch H HB); [exact HP | exact HI2 | exact MU3 | exact WM3 | exact MI3 | exact ST3 |].
      unfold wwin, WO_SAVED. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]. left. lia. }

    assert (SB3 : SHAD m3 k (shadow_of 100)).
    { destruct AD as [_ SB]. eapply SHAD_transport; [| exact MU3 | exact WM3 | rewrite shadow_of_length by lia; cbn; lia].
      eapply SHAD_transport; [| exact MU2 | exact WM2 | rewrite shadow_of_length by lia; cbn; unfold AINTRIN_STACK; lia].
      eapply SHAD_transport; [exact SB | exact MU1 | exact WM1 | exact I]. }
    eapply (wann H HB e ff fp [] sk LBk m3); [exact HHb | exact HP | exact HI3 | exact IN | exact LBI | exact SB3 | lia |].
    intros m4 w0 w1 w2 w10 w11 w12 w13 w14 w15 w16 w17 w28 w29 w30 w31 HI4 MU4 WM4 SB4.
    rewrite (ret_pc_even WO_AN6_RA ltac:(unfold WO_AN6_RA; lia) eq_refl).

    pose proof (munch_app _ _ _ _ _ MU3 MU4) as N3. pose proof (wmono_trans asegs _ _ _ WM3 WM4) as W3.
    pose proof (munch_app _ _ _ _ _ MU2 N3) as N2. pose proof (wmono_trans asegs _ _ _ WM2 W3) as W2.
    pose proof (munch_app _ _ _ _ _ MU1 N2) as N1. pose proof (wmono_trans asegs _ _ _ WM1 W2) as W1.
    cbn [app] in N1, N2, N3.
    assert (C48' : rw_cells asegs m4 (wS1 e + 48) [C8 (Z_to_bv 64 (ff + 176))])
      by (eapply rw_cells_transport; [exact C48 | exact N1 | exact W1 | cbn; unfold AINTRIN_STACK; zdj]).
    eapply evt_cut.
    { exact (wf3c (w_gp e) (w_tp e) w0 w1 w2 w10 w11 w12 w13 w14 w15 w16 w17 w28 w29 w30 w31 (w_F e) (w_fc e) m4 (wSP e) (wS1 e) ff (w_lo e) k
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) F3 ltac:(lia) ltac:(lia) FSH FAPP C48'
                  (winv_stk H _ _ _ _ _ _ _ HI4) (winv_mi H _ _ _ _ _ _ _ HI4)). }
    intros ms5 (y5 & y6 & y7 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m5 & EQ5 & MU5 & WM5 & MI5 & ST5). subst ms5.
    apply evt_done.
    assert (HI5 : winv H e ff fp [] sk LBk m5)
      by (eapply (winv_munch H HB); [exact HP | exact HI4 | exact MU5 | exact WM5 | exact MI5 | exact ST5 | apply Forall_nil]).
    exists y5, y6, y7, y12, y13, y14, y15, y16, y17, y28, y29, y30, y31, m5. split; [reflexivity|].
    split; [exact HI5|].
    pose proof (munch_app _ _ _ _ _ N1 MU5) as M1. pose proof (wmono_trans asegs _ _ _ W1 WM5) as V1.
    cbn [app] in M1.
    split; [eapply (wfc_munch H e ff m m5); [exact WC | exact M1 | exact V1 |]; unfold wfc_apart, AINTRIN_STACK;
            repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; zdj|].
    split; [eapply rw_cells_transport; [exact C48' | exact MU5 | exact WM5 | exact I]|].
    split; [eapply wps3_munch; [exact PS | exact M1 | exact V1 | unfold AINTRIN_STACK; zdj]|].
    pose proof (munch_app _ _ _ _ _ MU4 MU5) as M4. pose proof (wmono_trans asegs _ _ _ WM4 WM5) as V4. cbn [app] in M4.
    split; [eapply wtst_upd3; [exact TS | | exact M1 | exact V1 | reflexivity | reflexivity | unfold AINTRIN_STACK; zdj];
            eapply rw_cells_transport; [exact CV3 | exact M4 | exact V4 | cbn; unfold AINTRIN_STACK; lia]|].
    split; [eapply wblk_munch; [exact WG | exact M1 | exact V1 | lia | unfold AINTRIN_STACK; zdj]|].
    split; [eapply wblk_munch; [exact WH | exact M1 | exact V1 | lia | unfold AINTRIN_STACK; zdj]|].
    split; [exact (wr_at_wmono _ _ _ _ WRk V1)|].
    eapply SHAD_transport; [exact SB4 | exact MU5 | exact WM5 | exact I].
  Qed.
End WoF.
