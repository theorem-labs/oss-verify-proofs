(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame BCells BStep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 BsWalk RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_SR LbB_Conv LbB_Bridge.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_MILB LbB_PrsStmt LbB_StateStmt LbB_Own LbB_RtOwn LbB_DStat.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_WoGen LbB_WoDefs LbB_WoKit LbB_WoKit2 LbB_WoKit3 LbB_WoSt LbB_WoSt2 LbB_WoMs LbB_WoCall LbB_WoCut LbB_WoZ.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_WoR2 LbB_WoR6 LbB_WoR7 LbB_WoE0 LbB_WoE0b LbB_WoS4 LbB_WoS5 LbB_WoUR.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section WoEnd.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHb : asan_rt_hyps_bp H.
  Let HB := rt_bp_base H HHb.

  Definition wpost (e : went H) : config -> Prop :=
    po_post H LINV_P5 (w_ra e) (w_sp e) (w_gp e) (w_tp e) (w_s0 e) (w_s1 e) (w_s2 e) (w_s3 e) (w_s4 e) (w_s5 e) (w_s6 e)
      (w_s7 e) (w_s8 e) (w_s9 e) (w_s10 e) (w_s11 e) (w_F e) (w_fc e) (w_s e) (w_LB e) (w_LF e) (w_n e) (w_lo e) (w_B e)
      (w_shi e) (w_m e) (w_mo e).

  Lemma seg_fin : forall (e : went H) ff fp msF mo sk LBk XS r (F : bvmap 5 word) (fc : bv 32) (m : mem)
      (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s1 s2 s3 s4 s5 s6 s7 s9 s10 s11 : word),
    wpre H e -> as_AKREL H sk (mkCfg msF mo) -> as_MPRES H (w_mo e) mo -> as_AL H sk >= as_AL H (w_s e) - po_cost (w_n e) ->
    Permutation LBk (w_LB e) -> frm_zero fc -> winv H e ff fp XS sk LBk m -> -2 ^ 31 <= r < 2 ^ 31 ->
    as_VIS H sk msF = MS (mkR (Z_to_bv 64 WO_FS6_RA) (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) t0 t1 t2 (Z_to_bv 64 (wSP e)) s1
                              (Z_to_bv 64 ff) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 (Z_to_bv 64 r) s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 AFS_FREE_6) fc None m (seg_rom asegs) ->
    as_SR H (wpost e) (mkCfg msF mo).
  Proof.
    intros e ff fp msF mo sk LBk XS r F fc m t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s1 s2 s3 s4 s5 s6 s7 s9 s10 s11
      HP KR MP AL PERM FZ HI RR VIS.
    pose proof (wS1_facts H e HP) as (S32 & S1SP & S1L & SPH & LOS1 & CEL).
    pose proof (wpre_geo H e HP) as (CE & LO & SSHI & SHIH & SP16 & TP).
    pose proof (winv_ff H _ _ _ _ _ _ _ HI) as FFR.
    pose proof (wframe_z H _ _ _ FFR) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & FAPP & FSH).
    pose proof aceil_facts as ACF.
    destruct (rt_bp_ext H HHb) as (_ & _ & _ & _ & _ & _ & _ & SF6 & _).
    unfold stack_free_stmt in SF6. cbn [Z.eqb Pos.eqb] in SF6.
    assert (AL0 : po_cost (w_n e) <= as_AL H (w_s e))
      by (clear - HP; unfold wpre in HP; repeat (let X := fresh in destruct HP as [X HP]); exact HP).
    set (SP := wSP e) in *. set (S1 := wS1 e) in *. set (lo := w_lo e) in *.
    set (WT := [(S1 - AFS_STACK, S1); (fp, fp + 1); (sh ff, sh ff + 512)]).
    assert (WOK : Forall (fun iv : Z * Z => (forall LB0, aclient_write_ok H LB0 iv) /\ stack0_ok iv
                           /\ ((aceil <= fst iv /\ snd iv <= SP) \/ (forall a, fst iv <= a < snd iv -> rin_ivs (XW H ff fp ++ XS) a))
                           /\ (snd iv <= ATP - 164 \/ ATP - 160 <= fst iv)
                           /\ (snd iv <= SP - WO_SAVED \/ SP <= fst iv)) WT).
    { unfold WT, WO_SAVED, AFS_STACK, ATP.
      apply Forall_cons.
      { cbn beta. split; [intros LB0; left; cbn [fst snd]; lia|]. split; [left; cbn [fst snd]; unfold AHI_LO; lia|].
        split; [left; cbn [fst snd]; lia|]. cbn [fst snd]. split; [right; lia | left; lia]. }
      apply Forall_cons.
      { cbn beta. split; [intros LB0; right; right; right; right; left; cbn [fst snd]; unfold AFS_SIZE in *; lia|].
        split; [eapply (stack0_ok_aapp (as_FSB H) AFS_SIZE); [exact F10 | cbn [fst snd]; lia | cbn [fst snd]; unfold AFS_SIZE in *; lia]|].
        split; [right; intros a Ha; cbn [fst snd] in Ha; apply rin_ivs_app; left; unfold XW; cbn [rin_ivs fst snd]; right; left; lia|].
        cbn [fst snd]. split; [right; lia | left; lia]. }
      apply Forall_cons; [| apply Forall_nil].
      { cbn beta. split; [intros LB0; right; right; right; right; right; left; cbn [fst snd]; lia|].
        split; [right; cbn [fst snd]; assert (sh (ff + 4096) <= sh aceil) by (apply sh_mono; lia); lia|].
        split; [right; intros a Ha; cbn [fst snd] in Ha; apply rin_ivs_app; left; unfold XW; cbn [rin_ivs fst snd]; right; right; right; left; change (fshn 6) with 512; lia|].
        cbn [fst snd]. split; [right; lia | left; lia]. } }
    assert (DJ : forall A n, (forall iv, In iv WT -> snd iv <= A \/ A + n <= fst iv) -> disjoint_from WT A n).
    { intros A n K. clear - K. induction WT as [|[x y] W IH]; cbn; [exact I|].
      split; [destruct (K (x, y) (or_introl eq_refl)); cbn in *; lia | apply IH; intros iv Hiv; apply K; right; exact Hiv]. }
    assert (ST0 : stk asegs m lo S1).
    { destruct (winv_stk H _ _ _ _ _ _ _ HI) as (X1 & X2 & X3). split; [lia|]. split; [lia|]. intros a Ha. apply X3. lia. }

    eapply (ahh_evt_then H HB (fun ms => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m3,
              ms = MS (mkR (w_ra e) (Z_to_bv 64 SP) (w_gp e) (w_tp e) t0 t1 t2 (w_s0 e) (w_s1 e) (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7
                           (w_s2 e) (w_s3 e) (w_s4 e) (w_s5 e) (w_s6 e) (w_s7 e) (w_s8 e) (w_s9 e) (w_s10 e) (w_s11 e) t3 t4 t5 t6)
                      F (ret_pc (w_ra e)) fc None m3 (seg_rom asegs)
              /\ munch WT m m3 /\ wmono asegs m m3 /\ mem_inv asegs m3 /\ stk asegs m3 lo SP
              /\ as_RFS H (w_LF e) m3 /\ ACONST m3));
      [exact KR | exact VIS | |].
    {
      eapply evt_cut.
      { eapply SF6 with (LF := (6, ff, fp) :: w_LF e) (ff := ff) (fp := fp) (lo := lo);
          [ exact (winv_rf H _ _ _ _ _ _ _ HI) | left; reflexivity | reflexivity
          | change (fsz 6) with 4096; replace (ff + 4096 - 8) with (ff + WO_FLAGP) by (unfold WO_FLAGP; lia); exact (winv_sf H _ _ _ _ _ _ _ HI)
          | rewrite HLib.u64_of_Z by lia; exact ST0 | lia | rewrite HLib.u64_of_Z by lia; unfold AFS_STACK; lia
          | exact (winv_mi H _ _ _ _ _ _ _ HI) | exact (winv_ac H _ _ _ _ _ _ _ HI) ]. }
      intros ms1 P1. destruct P1 as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & EQ1 & MU1 & WM1 & MI1 & ST1 & RF1 & SH1 & AC1).
      subst ms1. rewrite (ret_pc_even WO_FS6_RA ltac:(unfold WO_FS6_RA; lia) eq_refl).
      rewrite HLib.u64_of_Z in MU1 by lia. change (fshn 6) with 512 in MU1. rewrite lf_remove_head in RF1.
      assert (SV1 : rw_cells asegs m1 (SP - 104) (wsaved e)).
      { eapply rw_cells_transport; [exact (winv_sv H _ _ _ _ _ _ _ HI) | exact MU1 | exact WM1 |].
        cbn [cells_size wsaved csize Nat.add]. unfold WO_SAVED. apply DJ. intros iv Hiv.
        pose proof (proj1 (Forall_forall _ _) WOK iv Hiv) as (_ & _ & _ & _ & X). unfold WO_SAVED in X. lia. }
      unfold wsaved in SV1.
      destruct (we2 (Z_to_bv 64 WO_FS6_RA) (Z_to_bv 64 S1) u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 (w_gp e) (w_tp e)
                  s1 s2 s3 s4 s5 s6 s7 s9 s10 s11
                  (w_ra e) (w_s0 e) (w_s1 e) (w_s2 e) (w_s3 e) (w_s4 e) (w_s5 e) (w_s6 e) (w_s7 e) (w_s8 e) (w_s9 e) (w_s10 e) (w_s11 e)
                  F fc m1 (seg_rom asegs) SP r ltac:(lia) ltac:(lia) RR SV1) as (R3 & RUN3 & HR3).
      eapply evt_of_msteps; [exact RUN3|]. subst R3. unfold WO_RET. step. apply evt_done.
      do 14 eexists. exists m1. split; [reflexivity|].
      split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1|].
      split; [eapply stk_wmono; [exact (winv_stk H _ _ _ _ _ _ _ HI) | exact WM1 | lia]|].
      split; [exact RF1 | exact AC1]. }

    intros msF2 mo2 KR2 MP2 P2. destruct P2 as (y0 & y1 & y2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & y3 & y4 & y5 & y6 & m3 & VIS3 & MU & WM & MI3 & ST3 & RF3 & AC3).
    apply (ah_done H HB). unfold wpost, po_post.
    pose proof (wlinv H HB e ff fp XS sk LBk m HP HI) as LV0.
    destruct HI as (RF & _ & RH & AC & _ & S0 & RA & (errv & ER) & _ & _ & _ & _ & _ & XP & FS & _).
    hnf. exists y0, y1, y2, (Z_to_bv 64 r), c1, c2, c3, c4, c5, c6, c7, y3, y4, y5, y6, m3, errv, sk, LBk, (XW H ff fp ++ XS), F, fc.
    cbn [cfg_ms cfg_model]. rewrite VIS3.
    assert (ESP : Z_to_bv 64 SP = w_sp e) by (unfold SP, wSP; apply Z_to_bv_bv_unsigned).
    rewrite ESP.
    split; [reflexivity|]. split; [exact FZ|]. split; [exact KR2|].
    split; [exact (ah_mpres_trans H HB (w_mo e) mo mo2 MP MP2)|].
    split; [exact MI3|]. split; [unfold SP in ST3; exact ST3|].
    split; [eapply rw_cells_transport; [exact ER | exact MU | exact WM |]; rewrite (werrno_ATP H e TP);
            cbn [cells_size csize]; apply DJ; intros iv Hiv; pose proof (proj1 (Forall_forall _ _) WOK iv Hiv) as X;
            destruct X as (_ & _ & _ & X & _); lia|].
    assert (A1 : Forall (aclient_write_ok H LBk) WT) by (eapply Forall_impl; [| exact WOK]; intros iv X; apply X).
    split; [eapply (ah_rauxv_frame H HB); [exact RA | exact MU | exact WM | exact A1]|].
    split; [eapply (ah_RHEAP_frame H HB); [exact RH | exact MU | exact WM | exact A1]|].
    split; [exact PERM|].
    split; [apply Forall_app; split; [exact (fs_scratch_of_fresh H (w_LF e) 6 ff fp FFR) | exact FS]|].
    split.
    { eapply xpres_trans; [exact XP|]. eapply (xpres_of_munch H (w_s e) (w_LB e) SP _ WT (w_m e)); [exact HB | exact (wpre_RH0 H e HP) | exact MU | exact WM |].
      eapply Forall_impl; [| exact WOK]. intros iv (_ & _ & [X|X] & _). - left. exact X. - right. intros a Ha. right. apply X. exact Ha. }
    split; [exact RF3|].
    split; [exact AC3|].
    split; [eapply stack0_transport; [exact S0 | exact MU | exact WM |]; eapply Forall_impl; [| exact WOK]; intros iv X; apply X|].
    split.
    { eapply LINV_P5_cl; [exact LV0|].
      intros a Ha Hc. apply MU. rewrite HLib.u64_of_Z by lia.
      clear - Hc F1 F4 F8 F14 S1L S1SP LOS1 CEL ACF. unfold aimg_client in Hc. unfold WT, AFS_STACK. cbn. lia. }
    lia.
  Qed.
  Lemma seg_end : forall (e : went H) ff fp msF mo s LB XS m r
      (y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 s2 s5 s6 s7 s9 s10 s11 y28 y29 y30 y31 : word) (F : bvmap 5 word) (fc : bv 32),
    wpre H e -> as_AKREL H s (mkCfg msF mo) -> as_MPRES H (w_mo e) mo -> as_AL H s >= as_AL H (w_s e) - po_cost (w_n e) ->
    frm_zero fc -> ww3 H e ff fp XS s LB m -> -2 ^ 31 <= r < 2 ^ 31 ->
    as_VIS H s msF = MS (mkR (Z_to_bv 64 WO_DT3_RA) (Z_to_bv 64 (wS1 e)) (w_gp e) (w_tp e) y5 y6 y7
                           (Z_to_bv 64 (wSP e)) (Z_to_bv 64 (wS1 e)) y10 y11 y12 y13 y14 y15 y16 y17
                           s2 (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) s5 s6 s7 (Z_to_bv 64 r) s9 s10 s11 y28 y29 y30 y31)
                        F (Z_to_bv 64 WO_DT3_RA) fc None m (seg_rom asegs) ->
    as_SR H (wpost e) (mkCfg msF mo).
  Proof.
    intros e ff fp msF mo s LB XS m r y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 s2 s5 s6 s7 s9 s10 s11 y28 y29 y30 y31 F fc
      HP KR MP AL FZ (HI & (C1 & C2 & C3 & C4 & WS) & PERM) RR VIS.
    pose proof (wframe_bounds H e ff fp XS s LB m HP HI) as (F0 & F64 & FLO & FH & FL & FS1 & SH1 & SH2 & S1L & S1SP & SPH & LOS1).
    pose proof (winv_wf H _ _ _ _ _ _ _ HI) as WF.
    assert (WF0 : wr_at asegs m ff 8).
    { destruct WF as (W0 & W1 & W). unfold WO_FLAGP in *. split; [lia|]. split; [lia|]. intros i Hi. apply W. lia. }
    unfold WO_FLAGP, AINTRIN_STACK, AIMG_TOP, AFS_HDR in *.
    eapply (ahh_evt_then H HB (we1_post (w_gp e) (w_tp e) s5 s6 s7 s9 s10 s11 F fc (wSP e) (wS1 e) ff r (w_lo e) m)
              (wpost e) s msF _ mo);
      [exact KR | exact VIS
      | exact (we1 (Z_to_bv 64 WO_DT3_RA) (w_gp e) (w_tp e) y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 s2 s5 s6 s7 s9 s10 s11
                   y28 y29 y30 y31 F fc m (wSP e) (wS1 e) ff r (w_lo e) S1L ltac:(lia) SPH LOS1 F64 ltac:(lia) ltac:(lia) SH1
                   C1 C2 C3 C4 WF0 WS (winv_stk H _ _ _ _ _ _ _ HI) (winv_mi H _ _ _ _ _ _ _ HI)) |].
    intros msF2 mo2 KR2 MP2 (x5 & x6 & x7 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m1 & EQ & MU & WM & MI & STK).
    assert (HI1 : winv H e ff fp XS s LB m1).
    { eapply (winv_munch H HB); [exact HP | exact HI | exact MU | exact WM | exact MI | exact STK |].
      unfold wwin. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
        unfold WO_FLAGP; first [right; left; lia | right; right; lia]. }
    eapply (seg_fin e ff fp msF2 mo2 s LB XS r F fc m1 x5 x6 x7 (Z_to_bv 64 3808) x12 x13 x14 x15 x16 x17 x28 x29 x30 x31
              (Z_to_bv 64 (wS1 e)) (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) s5 s6 s7 s9 s10 s11 HP KR2
              ltac:(eapply (ah_mpres_trans H HB); [exact MP | exact MP2]) AL PERM FZ HI1 RR EQ).
  Qed.

End WoEnd.
