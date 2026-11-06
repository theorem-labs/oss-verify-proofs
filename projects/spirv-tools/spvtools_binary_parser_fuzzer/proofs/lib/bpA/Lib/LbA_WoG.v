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

Section WoG.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHb : asan_rt_hyps_bp H.
  Let HB := rt_bp_base H HHb.

  Lemma munch_nil_eqG : forall (m m' : mem), munch [] m m' -> m' = m.
  Proof. intros m m' MU. apply functional_extensionality. intros x. apply MU. exact I. Qed.

  Definition wv1_post (e : went H) (ff fp : Z) (XS : list (Z * Z)) (sk : as_St H) (LBk : list block) (cP : stateC) (k r u : Z)
      (F : bvmap 5 word) (fc : bv 32) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m',
      ms' = MS (mkR (Z_to_bv 64 WO_ON8_RA) (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) x5 x6 x7 (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
                    (Z_to_bv 64 100) x11 x12 x13 x14 x15 x16 x17
                    (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) (Z_to_bv 64 0x3f800000) (Z_to_bv 64 k) (Z_to_bv 64 99)
                    (Z_to_bv 64 r) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31)
               F (Z_to_bv 64 AOPNEW) fc None m' (seg_rom asegs)
      /\ winv H e ff fp XS sk LBk m' /\ wfc2 H e ff m' /\ rw_cells asegs m' (wS1 e + 48) [C8 (Z_to_bv 64 (ff + 176))]
      /\ state_repA LBk m' (ff + 176) cP /\ state_sh m' cP
      /\ wtst0 (wS1 e) m' (vtrip u 500) Z24 Z24 /\ wblk m' u 500.

  Lemma wv1 : forall (e : went H) ff fp XS sk LBk (pu : bptr) (cP : stateC) k r u m (F : bvmap 5 word) (fc : bv 32)
      t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    wpre H e -> winv H e ff fp XS sk LBk m -> In (pu, u, 500) LBk ->
    (forall bb, In bb (w_LB e) -> In bb LBk /\ blk_id bb <> pu) ->
    (forall p n, In (p, n) (state_blocks cP) -> In (p, n) (lbl LBk) /\ p <> u) ->
    wfc2 H e ff m -> rw_cells asegs m (wS1 e + 48) [C8 (Z_to_bv 64 (ff + 176))] ->
    state_repA LBk m (ff + 176) cP -> state_sh m cP ->
    wtst0 (wS1 e) m Z24 Z24 Z24 -> addressable m u 500 -> wr_at asegs m u 500 ->
    evt asegs (wv1_post e ff fp XS sk LBk cP k r u F fc)
      (MS (mkR (Z_to_bv 64 WO_ON7_RA) (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) t0 t1 t2 (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
               (Z_to_bv 64 u) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) (Z_to_bv 64 0x3f800000) (Z_to_bv 64 k) (Z_to_bv 64 99)
               (Z_to_bv 64 r) (Z_to_bv 64 (k + 100)) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (ff + 128)) t3 t4 t5 t6)
          F (Z_to_bv 64 WO_ON7_RA) fc None m (seg_rom asegs)).
  Proof.
    intros e ff fp XS sk LBk pu cP k r u m F fc t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 HP HI IN LBI BLK WC C48 R S TS AD WRu.
    pose proof (wpre_geo H e HP) as (CE & LO & SSHI & SHIH & SP16 & TP).
    pose proof (wS1_facts H e HP) as (S32 & S1SP & S1L & SPH & LOS1 & _).
    pose proof (wframe_z H _ _ _ (winv_ff H _ _ _ _ _ _ _ HI)) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & FAPP & FSH).
    pose proof (wblk_geo H HB e ff fp XS sk LBk m pu u 500 HP HI IN) as (G0 & G16 & Gn & GC & GH & GSA & GSC & GLO & GLS & GF & GSF & GSS & GSB & GSH).
    pose proof aceil_facts as ACF.
    assert (Zv : forall mm a j a', rw_cells asegs mm a Z24 -> 0 <= j <= 16 -> a' = a + j -> rw_cells asegs mm a' [CB 8 (poison_bytes 8 0)])
      by (intros mm a j a' X Hj Ea; subst a'; exact (zero_cells_sub mm a 24 j 8 X ltac:(lia) ltac:(lia))).
    pose proof TS as (_ & _ & _ & TV2 & TV3).
    assert (BL : forall p n, In (p, n) (state_blocks cP) -> In (p, n) (lbl LBk)) by (intros p n Hin; exact (proj1 (BLK p n Hin))).

    eapply evt_cut.
    { exact (wg1a (w_gp e) (w_tp e) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m (wSP e) (wS1 e) ff (w_lo e) k r u
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) F3 ltac:(lia) ltac:(lia) FSH FAPP
                  ltac:(lia) (winv_stk H _ _ _ _ _ _ _ HI) (winv_mi H _ _ _ _ _ _ _ HI)). }
    intros ms1 (u5 & u6 & u7 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & m1 & EQ1 & MU1 & WM1 & MI1 & ST1 & CV1). subst ms1.
    assert (HI1 : winv H e ff fp XS sk LBk m1).
    { eapply (winv_munch H HB); [exact HP | exact HI | exact MU1 | exact WM1 | exact MI1 | exact ST1 |].
      unfold wwin, WO_SAVED. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]. left. lia. }

    assert (SB1 : SHAD m1 u (shadow_of 500)).
    { destruct AD as [_ SB]. eapply SHAD_transport; [exact SB | exact MU1 | exact WM1 | rewrite shadow_of_length by lia; cbn; lia]. }
    eapply (wann H HB e ff fp XS sk LBk m1); [exact HHb | exact HP | exact HI1 | exact IN | exact LBI | exact SB1 | lia |].
    intros m2 w0 w1 w2 w10 w11 w12 w13 w14 w15 w16 w17 w28 w29 w30 w31 HI2 MU2 WM2 SB2.
    rewrite (ret_pc_even WO_AN7_RA ltac:(unfold WO_AN7_RA; lia) eq_refl).

    assert (TV2' : rw_cells asegs m2 (wS1 e + 264) Z24).
    { eapply rw_cells_transport; [| exact MU2 | exact WM2 | cbn; unfold AINTRIN_STACK; lia].
      eapply rw_cells_transport; [exact TV2 | exact MU1 | exact WM1 | cbn; lia]. }
    eapply evt_cut.
    { exact (wg1b (w_gp e) (w_tp e) w0 w1 w2 w10 w11 w12 w13 w14 w15 w16 w17 w28 w29 w30 w31 F fc m2 (wSP e) (wS1 e) ff (w_lo e) k r
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) F3 ltac:(lia) ltac:(lia) FSH FAPP
                  ltac:(exact (Zv m2 (wS1 e + 264) 0 (wS1 e + 264) TV2' ltac:(lia) ltac:(lia)))
                  ltac:(exact (Zv m2 (wS1 e + 264) 16 (wS1 e + 280) TV2' ltac:(lia) ltac:(lia)))
                  ltac:(exact (Zv m2 (wS1 e + 264) 8 (wS1 e + 272) TV2' ltac:(lia) ltac:(lia)))
                  (winv_stk H _ _ _ _ _ _ _ HI2) (winv_mi H _ _ _ _ _ _ _ HI2)). }
    intros ms3 (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m3 & EQ3 & MU3 & WM3 & MI3 & ST3). subst ms3.
    pose proof (munch_nil_eqG m2 m3 MU3) as EM3. subst m3.
    apply evt_done.
    exists y5, y6, y7, y11, y12, y13, y14, y15, y16, y17, y28, y29, y30, y31, m2. split; [reflexivity|].
    split; [exact HI2|].
    pose proof (munch_app _ _ _ _ _ MU1 MU2) as M1. pose proof (wmono_trans asegs _ _ _ WM1 WM2) as V1.
    cbn [app] in M1.
    split; [eapply (wfc2_munch H e ff m m2); [exact WC | exact M1 | exact V1 |]; unfold wfc2_apart, AINTRIN_STACK;
            repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; zdj|].
    split; [eapply rw_cells_transport; [exact C48 | exact M1 | exact V1 | cbn; unfold AINTRIN_STACK; zdj]|].
    destruct (wstate_mu H HB e ff fp XS sk LBk m m2 _ cP HP HI M1 V1
                ltac:(unfold wsw, AINTRIN_STACK; apply Forall_cons; [left; cbn [fst snd]; lia|];
                      apply Forall_cons; [right; right; exists pu, u, 500; split; [exact IN|]; split; [intros p n Hin; exact (proj2 (BLK p n Hin)) | cbn [fst snd]; lia]|];
                      apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil])
                BL R S) as [R' S'].
    split; [exact R'|]. split; [exact S'|].
    split; [eapply (wtst0_upd (wS1 e) m m2); [exact TS | exact M1 | exact V1 | unfold AINTRIN_STACK; repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia
              | eapply rw_cells_transport; [exact CV1 | exact MU2 | exact WM2 | cbn; unfold AINTRIN_STACK; lia]
              | exact TV2'
              | eapply rw_cells_transport; [| exact MU2 | exact WM2 | cbn; unfold AINTRIN_STACK; lia]; eapply rw_cells_transport; [exact TV3 | exact MU1 | exact WM1 | cbn; lia]]|].
    split; [exact (wr_at_wmono _ _ _ _ WRu V1)|]. exact SB2.
  Qed.

  Definition wv2_post (e : went H) (ff fp : Z) (XS : list (Z * Z)) (sk : as_St H) (LBk : list block) (cP : stateC) (r u v : Z)
      (F : bvmap 5 word) (fc : bv 32) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m',
      ms' = MS (mkR (Z_to_bv 64 WO_ON9_RA) (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) x5 x6 x7 (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
                    (Z_to_bv 64 100) x11 x12 x13 x14 x15 x16 x17
                    (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) (Z_to_bv 64 0) (Z_to_bv 64 v) (Z_to_bv 64 99)
                    (Z_to_bv 64 r) (Z_to_bv 64 0) (Z_to_bv 64 (v + 100)) (Z_to_bv 64 0) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31)
               F (Z_to_bv 64 AOPNEW) fc None m' (seg_rom asegs)
      /\ winv H e ff fp XS sk LBk m' /\ wfc2 H e ff m' /\ rw_cells asegs m' (wS1 e + 48) [C8 (Z_to_bv 64 (ff + 176))]
      /\ state_repA LBk m' (ff + 176) cP /\ state_sh m' cP
      /\ wtst0 (wS1 e) m' (vtrip u 500) (vtrip v 100) Z24 /\ wblk m' u 500 /\ wblk m' v 100.

  Lemma wv2 : forall (e : went H) ff fp XS sk LBk (pu pv : bptr) (cP : stateC) k r u v m (F : bvmap 5 word) (fc : bv 32)
      t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    wpre H e -> winv H e ff fp XS sk LBk m -> In (pu, u, 500) LBk -> In (pv, v, 100) LBk -> pu <> pv ->
    (forall bb, In bb (w_LB e) -> In bb LBk /\ blk_id bb <> pv) ->
    (forall p n, In (p, n) (state_blocks cP) -> In (p, n) (lbl LBk) /\ p <> v) ->
    wfc2 H e ff m -> rw_cells asegs m (wS1 e + 48) [C8 (Z_to_bv 64 (ff + 176))] ->
    state_repA LBk m (ff + 176) cP -> state_sh m cP ->
    wtst0 (wS1 e) m (vtrip u 500) Z24 Z24 -> wblk m u 500 -> addressable m v 100 -> wr_at asegs m v 100 ->
    evt asegs (wv2_post e ff fp XS sk LBk cP r u v F fc)
      (MS (mkR (Z_to_bv 64 WO_ON8_RA) (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) t0 t1 t2 (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
               (Z_to_bv 64 v) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) (Z_to_bv 64 0x3f800000) (Z_to_bv 64 k) (Z_to_bv 64 99)
               (Z_to_bv 64 r) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (ff + 128)) t3 t4 t5 t6)
          F (Z_to_bv 64 WO_ON8_RA) fc None m (seg_rom asegs)).
  Proof.
    intros e ff fp XS sk LBk pu pv cP k r u v m F fc t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 HP HI INu IN NE LBI BLK WC C48 R S TS WU AD WRv.
    pose proof (wpre_geo H e HP) as (CE & LO & SSHI & SHIH & SP16 & TP).
    pose proof (wS1_facts H e HP) as (S32 & S1SP & S1L & SPH & LOS1 & _).
    pose proof (wframe_z H _ _ _ (winv_ff H _ _ _ _ _ _ _ HI)) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & FAPP & FSH).
    pose proof (wblk_geo H HB e ff fp XS sk LBk m pv v 100 HP HI IN) as (G0 & G16 & Gn & GC & GH & GSA & GSC & GLO & GLS & GF & GSF & GSS & GSB & GSH).
    pose proof (wblk_geo H HB e ff fp XS sk LBk m pu u 500 HP HI INu) as (_ & _ & _ & _ & _ & J1 & _).
    pose proof (wblk2_geo H HB _ _ _ pu u 500 pv v 100 (winv_rh H _ _ _ _ _ _ _ HI) INu IN NE) as (_ & _ & _ & X1).
    pose proof aceil_facts as ACF.
    assert (Zv : forall mm a j a', rw_cells asegs mm a Z24 -> 0 <= j <= 16 -> a' = a + j -> rw_cells asegs mm a' [CB 8 (poison_bytes 8 0)])
      by (intros mm a j a' X Hj Ea; subst a'; exact (zero_cells_sub mm a 24 j 8 X ltac:(lia) ltac:(lia))).
    pose proof TS as (_ & _ & TV1 & TV2 & TV3).
    assert (BL : forall p n, In (p, n) (state_blocks cP) -> In (p, n) (lbl LBk)) by (intros p n Hin; exact (proj1 (BLK p n Hin))).

    eapply evt_cut.
    { exact (wg2a (w_gp e) (w_tp e) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m (wSP e) (wS1 e) ff (w_lo e) k r v
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) F3 ltac:(lia) ltac:(lia) FSH FAPP
                  ltac:(exact (Zv m (wS1 e + 264) 0 (wS1 e + 264) TV2 ltac:(lia) ltac:(lia)))
                  ltac:(exact (Zv m (wS1 e + 264) 8 (wS1 e + 272) TV2 ltac:(lia) ltac:(lia)))
                  ltac:(lia) (winv_stk H _ _ _ _ _ _ _ HI) (winv_mi H _ _ _ _ _ _ _ HI)). }
    intros ms1 (u5 & u6 & u7 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & m1 & EQ1 & MU1 & WM1 & MI1 & ST1). subst ms1.
    pose proof (munch_nil_eqG m m1 MU1) as EM1. subst m1.

    eapply (wmc0 H HB e ff fp XS sk LBk m); [exact HP | exact HI | exact IN | exact LBI |].
    intros m2 v0 v1 v2 v11 v12 v13 v14 v15 v16 v17 v28 v29 v30 v31 HI2 MU2 WM2.
    apply munch_drop0 in MU2.
    rewrite (ret_pc_even WO_MC8_RA ltac:(unfold WO_MC8_RA; lia) eq_refl).

    assert (TV2' : rw_cells asegs m2 (wS1 e + 264) Z24)
      by (eapply rw_cells_transport; [exact TV2 | exact MU2 | exact WM2 | cbn; unfold AINTRIN_STACK; lia]).
    eapply evt_cut.
    { exact (wg2b (w_gp e) (w_tp e) v0 v1 v2 v11 v12 v13 v14 v15 v16 v17 v28 v29 v30 v31 F fc m2 (wSP e) (wS1 e) ff (w_lo e) r v
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) F3 ltac:(lia) ltac:(lia) FSH FAPP
                  ltac:(exact (Zv m2 (wS1 e + 264) 16 (wS1 e + 280) TV2' ltac:(lia) ltac:(lia)))
                  ltac:(lia) (winv_stk H _ _ _ _ _ _ _ HI2) (winv_mi H _ _ _ _ _ _ _ HI2)). }
    intros ms3 (k5 & k6 & k7 & k14 & k15 & k16 & k17 & k28 & k29 & k30 & k31 & m3 & EQ3 & MU3 & WM3 & MI3 & ST3 & CV3). subst ms3.
    assert (HI3 : winv H e ff fp XS sk LBk m3).
    { eapply (winv_munch H HB); [exact HP | exact HI2 | exact MU3 | exact WM3 | exact MI3 | exact ST3 |].
      unfold wwin, WO_SAVED. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]. left. lia. }

    assert (SB3 : SHAD m3 v (shadow_of 100)).
    { destruct AD as [_ SB]. eapply SHAD_transport; [| exact MU3 | exact WM3 | rewrite shadow_of_length by lia; cbn; lia].
      eapply SHAD_transport; [exact SB | exact MU2 | exact WM2 | rewrite shadow_of_length by lia; cbn; unfold AINTRIN_STACK; lia]. }
    eapply (wann H HB e ff fp XS sk LBk m3); [exact HHb | exact HP | exact HI3 | exact IN | exact LBI | exact SB3 | lia |].
    intros m4 w0 w1 w2 w10 w11 w12 w13 w14 w15 w16 w17 w28 w29 w30 w31 HI4 MU4 WM4 SB4.
    rewrite (ret_pc_even WO_AN8_RA ltac:(unfold WO_AN8_RA; lia) eq_refl).

    pose proof (munch_app _ _ _ _ _ MU3 MU4) as N3. pose proof (wmono_trans asegs _ _ _ WM3 WM4) as W3.
    pose proof (munch_app _ _ _ _ _ MU2 N3) as N2. pose proof (wmono_trans asegs _ _ _ WM2 W3) as W2.
    cbn [app] in N2, N3.
    assert (TV3' : rw_cells asegs m4 (wS1 e + 288) Z24) by (eapply rw_cells_transport; [exact TV3 | exact N2 | exact W2 | cbn; unfold AINTRIN_STACK; lia]).
    eapply evt_cut.
    { exact (wg2c (w_gp e) (w_tp e) w0 w1 w2 w10 w11 w12 w13 w14 w15 w16 w17 w28 w29 w30 w31 F fc m4 (wSP e) (wS1 e) ff (w_lo e) r v
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) F3 ltac:(lia) ltac:(lia) FSH FAPP
                  ltac:(exact (Zv m4 (wS1 e + 288) 0 (wS1 e + 288) TV3' ltac:(lia) ltac:(lia)))
                  ltac:(exact (Zv m4 (wS1 e + 288) 16 (wS1 e + 304) TV3' ltac:(lia) ltac:(lia)))
                  ltac:(exact (Zv m4 (wS1 e + 288) 8 (wS1 e + 296) TV3' ltac:(lia) ltac:(lia)))
                  (winv_stk H _ _ _ _ _ _ _ HI4) (winv_mi H _ _ _ _ _ _ _ HI4)). }
    intros ms5 (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m5 & EQ5 & MU5 & WM5 & MI5 & ST5). subst ms5.
    pose proof (munch_nil_eqG m4 m5 MU5) as EM5. subst m5.
    apply evt_done.
    exists y5, y6, y7, y11, y12, y13, y14, y15, y16, y17, y28, y29, y30, y31, m4. split; [reflexivity|].
    split; [exact HI4|].
    split; [eapply (wfc2_munch H e ff m m4); [exact WC | exact N2 | exact W2 |]; unfold wfc2_apart, AINTRIN_STACK;
            repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; zdj|].
    split; [eapply rw_cells_transport; [exact C48 | exact N2 | exact W2 | cbn; unfold AINTRIN_STACK; zdj]|].
    destruct (wstate_mu H HB e ff fp XS sk LBk m m4 _ cP HP HI N2 W2
                ltac:(unfold wsw, AINTRIN_STACK; apply Forall_cons; [left; cbn [fst snd]; lia|];
                      apply Forall_cons; [left; cbn [fst snd]; lia|];
                      apply Forall_cons; [right; right; exists pv, v, 100; split; [exact IN|]; split; [intros p n Hin; exact (proj2 (BLK p n Hin)) | cbn [fst snd]; lia]|];
                      apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil])
                BL R S) as [R' S'].
    split; [exact R'|]. split; [exact S'|].
    split; [eapply (wtst0_upd (wS1 e) m m4); [exact TS | exact N2 | exact W2 | unfold AINTRIN_STACK; repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia
              | eapply rw_cells_transport; [exact TV1 | exact N2 | exact W2 | cbn; unfold AINTRIN_STACK; zdj]
              | eapply rw_cells_transport; [exact CV3 | exact MU4 | exact WM4 | cbn; unfold AINTRIN_STACK; lia]
              | exact TV3']|].
    split; [eapply wblk_munch; [exact WU | exact N2 | exact W2 | lia | unfold AINTRIN_STACK; zdj]|].
    split; [exact (wr_at_wmono _ _ _ _ WRv W2)|]. exact SB4.
  Qed.

  Definition wv3_post (e : went H) (ff fp : Z) (XS : list (Z * Z)) (sk : as_St H) (LBk : list block) (cP : stateC) (r u v w : Z)
      (F : bvmap 5 word) (fc : bv 32) : machine_state -> Prop :=
    fun ms' => exists x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m',
      ms' = MS (mkR (Z_to_bv 64 WO_MVA2_RA) (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) x5 x6 x7 (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
                    (Z_to_bv 64 (ff + 176)) (Z_to_bv 64 (wS1 e + 72)) x12 x13 x14 x15 x16 x17
                    (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) (Z_to_bv 64 (ff + 176)) (Z_to_bv 64 w) (Z_to_bv 64 99)
                    (Z_to_bv 64 r) (Z_to_bv 64 w) (Z_to_bv 64 (w + 100)) (Z_to_bv 64 0) (Z_to_bv 64 (ff + 128)) x28 x29 x30 x31)
               F (Z_to_bv 64 AST_MVA) fc None m' (seg_rom asegs)
      /\ winv H e ff fp XS sk LBk m' /\ wfc2 H e ff m' /\ rw_cells asegs m' (wS1 e + 48) [C8 (Z_to_bv 64 (ff + 176))]
      /\ state_repA LBk m' (ff + 176) cP /\ state_sh m' cP
      /\ wtst0 (wS1 e) m' (vtrip u 500) (vtrip v 100) (vtrip w 100) /\ wblk m' u 500 /\ wblk m' v 100 /\ wblk m' w 100.

  Lemma wv3 : forall (e : went H) ff fp XS sk LBk (pu pv pw : bptr) (cP : stateC) r u v w m (F : bvmap 5 word) (fc : bv 32)
      t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    wpre H e -> winv H e ff fp XS sk LBk m -> In (pu, u, 500) LBk -> In (pv, v, 100) LBk -> In (pw, w, 100) LBk -> pu <> pw -> pv <> pw ->
    (forall bb, In bb (w_LB e) -> In bb LBk /\ blk_id bb <> pw) ->
    (forall p n, In (p, n) (state_blocks cP) -> In (p, n) (lbl LBk) /\ p <> w) ->
    wfc2 H e ff m -> rw_cells asegs m (wS1 e + 48) [C8 (Z_to_bv 64 (ff + 176))] ->
    state_repA LBk m (ff + 176) cP -> state_sh m cP ->
    wtst0 (wS1 e) m (vtrip u 500) (vtrip v 100) Z24 -> wblk m u 500 -> wblk m v 100 -> addressable m w 100 -> wr_at asegs m w 100 ->
    evt asegs (wv3_post e ff fp XS sk LBk cP r u v w F fc)
      (MS (mkR (Z_to_bv 64 WO_ON9_RA) (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) t0 t1 t2 (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e))
               (Z_to_bv 64 w) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) (Z_to_bv 64 0) (Z_to_bv 64 v) (Z_to_bv 64 99)
               (Z_to_bv 64 r) (Z_to_bv 64 0) (Z_to_bv 64 (v + 100)) (Z_to_bv 64 0) (Z_to_bv 64 (ff + 128)) t3 t4 t5 t6)
          F (Z_to_bv 64 WO_ON9_RA) fc None m (seg_rom asegs)).
  Proof.
    intros e ff fp XS sk LBk pu pv pw cP r u v w m F fc t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 HP HI INu INv IN NEu NEv LBI BLK WC C48 R S TS WU WV AD WRw.
    pose proof (wpre_geo H e HP) as (CE & LO & SSHI & SHIH & SP16 & TP).
    pose proof (wS1_facts H e HP) as (S32 & S1SP & S1L & SPH & LOS1 & _).
    pose proof (wframe_z H _ _ _ (winv_ff H _ _ _ _ _ _ _ HI)) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & FAPP & FSH).
    pose proof (wblk_geo H HB e ff fp XS sk LBk m pw w 100 HP HI IN) as (G0 & G16 & Gn & GC & GH & GSA & GSC & GLO & GLS & GF & GSF & GSS & GSB & GSH).
    pose proof (wblk_geo H HB e ff fp XS sk LBk m pu u 500 HP HI INu) as (_ & _ & _ & _ & _ & J1 & _).
    pose proof (wblk_geo H HB e ff fp XS sk LBk m pv v 100 HP HI INv) as (_ & _ & _ & _ & _ & J2 & _).
    pose proof (wblk2_geo H HB _ _ _ pu u 500 pw w 100 (winv_rh H _ _ _ _ _ _ _ HI) INu IN NEu) as (_ & _ & _ & X1).
    pose proof (wblk2_geo H HB _ _ _ pv v 100 pw w 100 (winv_rh H _ _ _ _ _ _ _ HI) INv IN NEv) as (_ & _ & _ & X2).
    pose proof aceil_facts as ACF.
    assert (Zv : forall mm a j a', rw_cells asegs mm a Z24 -> 0 <= j <= 16 -> a' = a + j -> rw_cells asegs mm a' [CB 8 (poison_bytes 8 0)])
      by (intros mm a j a' X Hj Ea; subst a'; exact (zero_cells_sub mm a 24 j 8 X ltac:(lia) ltac:(lia))).
    pose proof TS as (_ & _ & TV1 & TV2 & TV3).
    assert (BL : forall p n, In (p, n) (state_blocks cP) -> In (p, n) (lbl LBk)) by (intros p n Hin; exact (proj1 (BLK p n Hin))).

    eapply evt_cut.
    { exact (wg3a (w_gp e) (w_tp e) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m (wSP e) (wS1 e) ff (w_lo e) r v w
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) F3 ltac:(lia) ltac:(lia) FSH FAPP
                  ltac:(exact (Zv m (wS1 e + 288) 0 (wS1 e + 288) TV3 ltac:(lia) ltac:(lia)))
                  ltac:(exact (Zv m (wS1 e + 288) 8 (wS1 e + 296) TV3 ltac:(lia) ltac:(lia)))
                  ltac:(lia) (winv_stk H _ _ _ _ _ _ _ HI) (winv_mi H _ _ _ _ _ _ _ HI)). }
    intros ms1 (u5 & u6 & u7 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & m1 & EQ1 & MU1 & WM1 & MI1 & ST1). subst ms1.
    pose proof (munch_nil_eqG m m1 MU1) as EM1. subst m1.

    eapply (wmc0 H HB e ff fp XS sk LBk m); [exact HP | exact HI | exact IN | exact LBI |].
    intros m2 v0 v1 v2 v11 v12 v13 v14 v15 v16 v17 v28 v29 v30 v31 HI2 MU2 WM2.
    apply munch_drop0 in MU2.
    rewrite (ret_pc_even WO_MC9_RA ltac:(unfold WO_MC9_RA; lia) eq_refl).

    assert (TV3' : rw_cells asegs m2 (wS1 e + 288) Z24)
      by (eapply rw_cells_transport; [exact TV3 | exact MU2 | exact WM2 | cbn; unfold AINTRIN_STACK; lia]).
    eapply evt_cut.
    { exact (wg3b (w_gp e) (w_tp e) v0 v1 v2 v11 v12 v13 v14 v15 v16 v17 v28 v29 v30 v31 F fc m2 (wSP e) (wS1 e) ff (w_lo e) r w
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) F3 ltac:(lia) ltac:(lia) FSH FAPP
                  ltac:(exact (Zv m2 (wS1 e + 288) 16 (wS1 e + 304) TV3' ltac:(lia) ltac:(lia)))
                  ltac:(lia) (winv_stk H _ _ _ _ _ _ _ HI2) (winv_mi H _ _ _ _ _ _ _ HI2)). }
    intros ms3 (k5 & k6 & k7 & k14 & k15 & k16 & k17 & k28 & k29 & k30 & k31 & m3 & EQ3 & MU3 & WM3 & MI3 & ST3 & CV3). subst ms3.
    assert (HI3 : winv H e ff fp XS sk LBk m3).
    { eapply (winv_munch H HB); [exact HP | exact HI2 | exact MU3 | exact WM3 | exact MI3 | exact ST3 |].
      unfold wwin, WO_SAVED. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]. left. lia. }

    assert (SB3 : SHAD m3 w (shadow_of 100)).
    { destruct AD as [_ SB]. eapply SHAD_transport; [| exact MU3 | exact WM3 | rewrite shadow_of_length by lia; cbn; lia].
      eapply SHAD_transport; [exact SB | exact MU2 | exact WM2 | rewrite shadow_of_length by lia; cbn; unfold AINTRIN_STACK; lia]. }
    eapply (wann H HB e ff fp XS sk LBk m3); [exact HHb | exact HP | exact HI3 | exact IN | exact LBI | exact SB3 | lia |].
    intros m4 w0 w1 w2 w10 w11 w12 w13 w14 w15 w16 w17 w28 w29 w30 w31 HI4 MU4 WM4 SB4.
    rewrite (ret_pc_even WO_AN9_RA ltac:(unfold WO_AN9_RA; lia) eq_refl).

    pose proof (munch_app _ _ _ _ _ MU3 MU4) as N3. pose proof (wmono_trans asegs _ _ _ WM3 WM4) as W3.
    pose proof (munch_app _ _ _ _ _ MU2 N3) as N2. pose proof (wmono_trans asegs _ _ _ WM2 W3) as W2.
    cbn [app] in N2, N3.
    assert (C48' : rw_cells asegs m4 (wS1 e + 48) [C8 (Z_to_bv 64 (ff + 176))])
      by (eapply rw_cells_transport; [exact C48 | exact N2 | exact W2 | cbn; unfold AINTRIN_STACK; zdj]).
    eapply evt_cut.
    { exact (wg3c (w_gp e) (w_tp e) w0 w1 w2 w10 w11 w12 w13 w14 w15 w16 w17 w28 w29 w30 w31 F fc m4 (wSP e) (wS1 e) ff (w_lo e) r w
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) F3 ltac:(lia) ltac:(lia) FSH FAPP C48'
                  (winv_stk H _ _ _ _ _ _ _ HI4) (winv_mi H _ _ _ _ _ _ _ HI4)). }
    intros ms5 (y5 & y6 & y7 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m5 & EQ5 & MU5 & WM5 & MI5 & ST5). subst ms5.
    pose proof (munch_nil_eqG m4 m5 MU5) as EM5. subst m5.
    apply evt_done.
    exists y5, y6, y7, y12, y13, y14, y15, y16, y17, y28, y29, y30, y31, m4. split; [reflexivity|].
    split; [exact HI4|].
    split; [eapply (wfc2_munch H e ff m m4); [exact WC | exact N2 | exact W2 |]; unfold wfc2_apart, AINTRIN_STACK;
            repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; zdj|].
    split; [exact C48'|].
    destruct (wstate_mu H HB e ff fp XS sk LBk m m4 _ cP HP HI N2 W2
                ltac:(unfold wsw, AINTRIN_STACK; apply Forall_cons; [left; cbn [fst snd]; lia|];
                      apply Forall_cons; [left; cbn [fst snd]; lia|];
                      apply Forall_cons; [right; right; exists pw, w, 100; split; [exact IN|]; split; [intros p n Hin; exact (proj2 (BLK p n Hin)) | cbn [fst snd]; lia]|];
                      apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil])
                BL R S) as [R' S'].
    split; [exact R'|]. split; [exact S'|].
    split; [eapply (wtst0_upd (wS1 e) m m4); [exact TS | exact N2 | exact W2 | unfold AINTRIN_STACK; repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia
              | eapply rw_cells_transport; [exact TV1 | exact N2 | exact W2 | cbn; unfold AINTRIN_STACK; zdj]
              | eapply rw_cells_transport; [exact TV2 | exact N2 | exact W2 | cbn; unfold AINTRIN_STACK; zdj]
              | eapply rw_cells_transport; [exact CV3 | exact MU4 | exact WM4 | cbn; unfold AINTRIN_STACK; lia]]|].
    split; [eapply wblk_munch; [exact WU | exact N2 | exact W2 | lia | unfold AINTRIN_STACK; zdj]|].
    split; [eapply wblk_munch; [exact WV | exact N2 | exact W2 | lia | unfold AINTRIN_STACK; zdj]|].
    split; [exact (wr_at_wmono _ _ _ _ WRw W2)|]. exact SB4.
  Qed.
End WoG.
