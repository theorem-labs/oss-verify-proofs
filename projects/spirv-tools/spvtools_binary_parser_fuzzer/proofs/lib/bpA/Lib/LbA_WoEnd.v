(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HeapCeil.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HTac HArr HSysStep HExec CellsX TacX HMem HMState HLFrame HCells HStep.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HPrelim.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import ASegs AsShadow AsConst AsIface AsCXXHeap CXXRep AsStack0 AsWalk RtA_Iface.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec LibIface FPSteps.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require HLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbA_SR LbA_Conv LbA_Bridge.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require Import LbA_MILB LbA_PrsStmt LbA_StateStmt LbA_Own LbA_RtOwn LbA_DStat.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbA_WoGen LbA_WoDefs LbA_WoKit LbA_WoKit2 LbA_WoKit3 LbA_WoSt LbA_WoSt2 LbA_WoMs LbA_WoCall LbA_WoCut LbA_WoZ.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbA_WoR2 LbA_WoR6 LbA_WoR7 LbA_WoE0 LbA_WoE0b LbA_WoS1 LbA_WoPm LbA_WoS5.
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

  Lemma seg_end : forall (e : went H) ff fp msF mo s16 LB16 XS16 r w,
    wpre H e -> as_AKREL H s16 (mkCfg msF mo) -> as_MPRES H (w_mo e) mo -> as_AL H s16 >= as_AL H (w_s e) - po_cost (w_n e) ->
    Permutation LB16 (w_LB e) ->
    ww3_post H e ff fp XS16 s16 LB16 r w (as_VIS H s16 msF) ->
    as_SR H (wpost e) (mkCfg msF mo).
  Proof.
    intros e ff fp msF mo s16 LB16 XS16 r w HP KR MP AL16 PERM P17.
    destruct P17 as (x5 & x6 & x7 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & F & fc & m0 & VIS & FZ & HI & WC).
    pose proof (wS1_facts H e HP) as (S32 & S1SP & S1L & SPH & LOS1 & CEL).
    pose proof (wpre_geo H e HP) as (CE & LO & SSHI & SHIH & SP16 & TP).
    pose proof (winv_ff H _ _ _ _ _ _ _ HI) as FFR.
    pose proof (wframe_z H _ _ _ FFR) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & FAPP & FSH).
    pose proof (wframe_facts H _ _ _ FFR) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G16).
    pose proof aceil_facts as ACF.
    destruct WC as (Wc1 & Wc2 & Wc3 & Wc6 & Wc7 & Wc8 & Wc9).

    pose proof Wc8 as C8'.
    change [C8 (Z_to_bv 64 (ff + 32)); C8 (Z_to_bv 64 0x7fff8000); C8 (Z_to_bv 64 ff)]
      with ([C8 (Z_to_bv 64 (ff + 32))] ++ [C8 (Z_to_bv 64 0x7fff8000)] ++ [C8 (Z_to_bv 64 ff)]) in C8'.
    apply rw_cells_app in C8' as [C24 C8']. apply rw_cells_app in C8' as [C32 C40]. cbn [cells_size csize Nat.add] in C32, C40.
    replace (wS1 e + 24 + Z.of_nat 8) with (wS1 e + 32) in C32 by lia.
    replace (wS1 e + 24 + Z.of_nat 8 + Z.of_nat 8) with (wS1 e + 40) in C40 by lia.
    pose proof Wc9 as C9'.
    change [C8 (Z_to_bv 64 (ff + 48)); C8 (Z_to_bv 64 ff)] with ([C8 (Z_to_bv 64 (ff + 48))] ++ [C8 (Z_to_bv 64 ff)]) in C9'.
    apply rw_cells_app in C9' as [C56 _].
    pose proof (winv_wf H _ _ _ _ _ _ _ HI) as WF. unfold WO_FLAGP in WF.
    assert (WF0 : wr_at asegs m0 (ff + 0) 8).
    { destruct WF as (W0 & W1 & W). split; [lia|]. split; [lia|]. intros i Hi. replace (ff + 0 + i) with (ff + i) by lia. apply W. lia. }
    assert (WSH : wr_at asegs m0 (sh ff + 4) 48).
    { destruct Wc6 as [_ (W0 & W1 & W)]. rewrite length_map in W1, W. cbn [length WO_SH2C app repeat] in W1, W.
      split; [lia|]. split; [lia|]. intros i Hi. replace (sh ff + 4 + i) with (sh ff + (4 + i)) by lia. apply W. lia. }
    set (SP := wSP e) in *. set (S1 := wS1 e) in *. set (lo := w_lo e) in *.

    set (WT := [(sh ff + 4, sh ff + 52); (ff, ff + 8); (sh ff, sh ff + 64); (fp, fp + 1)]).
    assert (WOK : Forall (fun iv => (afs_write_ok H ((3, ff, fp) :: w_LF e) iv \/ (fst iv = fp /\ snd iv = fp + 1))
                           /\ (forall LB0, aclient_write_ok H LB0 iv) /\ aconst_ok iv /\ stack0_ok iv
                           /\ (forall a, fst iv <= a < snd iv -> rin_ivs (XW H ff fp ++ XS16) a)
                           /\ (snd iv <= ATP - 164 \/ ATP - 160 <= fst iv)
                           /\ (snd iv <= SP - WO_SAVED \/ SP <= fst iv)
                           /\ snd iv <= lo) WT).
    { unfold WT, WO_SAVED.
      assert (K1 : forall iv, wwin H e ff iv -> (forall a, fst iv <= a < snd iv -> rin_ivs (XW H ff fp ++ XS16) a) -> (snd iv <= lo) ->
                (afs_write_ok H ((3, ff, fp) :: w_LF e) iv \/ (fst iv = fp /\ snd iv = fp + 1))
                /\ (forall LB0, aclient_write_ok H LB0 iv) /\ aconst_ok iv /\ stack0_ok iv
                /\ (forall a, fst iv <= a < snd iv -> rin_ivs (XW H ff fp ++ XS16) a)
                /\ (snd iv <= ATP - 164 \/ ATP - 160 <= fst iv) /\ (snd iv <= SP - 104 \/ SP <= fst iv) /\ snd iv <= lo).
      { intros iv HW Hrin Hlo. destruct (wwin_ok H e ff fp XS16 iv FFR CE ltac:(unfold WO_SAVED; fold lo SP; lia) ltac:(fold SP; lia) HW)
          as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
        split; [left; exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [exact B4|].
        split; [exact Hrin|]. split; [exact B8|]. split; [unfold WO_SAVED in B6; exact B6 | exact Hlo]. }
      apply Forall_cons; [apply K1; [right; right; cbn; lia | intros a Ha; apply rin_ivs_app; left; cbn in Ha |- *; right; right; right; left; change (fshn 3) with 64; lia | cbn; lia]|].
      apply Forall_cons; [apply K1; [right; left; cbn; unfold WO_FLAGP; lia | intros a Ha; apply rin_ivs_app; left; cbn in Ha |- *; right; right; left; change (fsz 3) with 512; lia | cbn; lia]|].
      apply Forall_cons; [apply K1; [right; right; cbn; lia | intros a Ha; apply rin_ivs_app; left; cbn in Ha |- *; right; right; right; left; change (fshn 3) with 64; lia | cbn; lia]|].
      apply Forall_cons; [| apply Forall_nil]. cbn [fst snd].
      split; [right; split; reflexivity|].
      split; [intros LB0; right; right; right; right; left; cbn; unfold AFS_SIZE in *; lia|].
      split; [eapply (LbA_SR.aconst_ok_app (as_FSB H) AFS_SIZE); [exact F10 | cbn; lia | cbn; unfold AFS_SIZE in *; lia]|].
      split; [eapply (stack0_ok_aapp (as_FSB H) AFS_SIZE); [exact F10 | lia | unfold AFS_SIZE in *; lia]|].
      split; [intros a Ha; apply rin_ivs_app; left; cbn; right; left; lia|].
      split; [right; unfold ATP; lia|]. split; [left; lia | lia]. }
    assert (DJ : forall A n, (forall iv, In iv WT -> snd iv <= A \/ A + n <= fst iv) -> disjoint_from WT A n).
    { intros A n K. clear - K. induction WT as [|[x y] W IH]; cbn; [exact I|].
      split; [destruct (K (x, y) (or_introl eq_refl)); cbn in *; lia | apply IH; intros iv Hiv; apply K; right; exact Hiv]. }

    eapply (ahh_evt_then H HB (fun ms => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m3,
              ms = MS (mkR (w_ra e) (Z_to_bv 64 SP) (w_gp e) (w_tp e) t0 t1 t2 (w_s0 e) (w_s1 e) (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7
                           (w_s2 e) (w_s3 e) (w_s4 e) (w_s5 e) (w_s6 e) (w_s7 e) (w_s8 e) (w_s9 e) (w_s10 e) (w_s11 e) t3 t4 t5 t6)
                      F (ret_pc (w_ra e)) fc None m3 (seg_rom asegs)
              /\ munch WT m0 m3 /\ wmono asegs m0 m3 /\ mem_inv asegs m3 /\ stk asegs m3 lo SP /\ mrd asegs m3 (wa fp) = Some (b8 0)));
      [exact KR | exact VIS | |].
    {
      eapply evt_cut.
      { exact (we1 (w_gp e) (w_tp e) x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc m0 SP S1 ff lo r w
                 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) F3 ltac:(lia) ltac:(lia) FSH FAPP WF0 C24 Wc3 C56 C40 C32 WSH
                 (winv_stk H _ _ _ _ _ _ _ HI) (winv_mi H _ _ _ _ _ _ _ HI)). }
      intros ms1 (u5 & u6 & u7 & u12 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & m1 & EQ1 & MU1 & WM1 & MI1 & ST1). subst ms1.
      assert (AC1 : ACONST m1).
      { eapply ACONST_frame; [exact (winv_ac H _ _ _ _ _ _ _ HI) | exact MU1 | exact WM1 |].
        apply Forall_cons; [exact (proj1 (proj2 (proj2 (Forall_inv WOK))))|].
        apply Forall_cons; [exact (proj1 (proj2 (proj2 (Forall_inv (Forall_inv_tail WOK)))))| apply Forall_nil]. }
      destruct (wr_at_rw_cells m1 (sh ff) 64 (wr_at_wmono _ _ _ _ (proj2 Wc6) WM1) ltac:(lia) ltac:(lia)) as (junk & CSH).

      eapply evt_cut.
      { eapply (ah_setf5 H HB) with (sa := sh ff) (n := 64); [reflexivity | reflexivity | lia | exact CSH | exact MI1 | exact AC1]. }
      intros ms2 P2. destruct P2 as (v0 & v1 & v2 & v10 & v11 & v12 & v13 & v14 & v15 & v16 & v17 & v28 & v29 & v30 & v31 & m2 & EQ2 & MU2 & WM2 & MI2 & SH2).
      subst ms2. rewrite (ret_pc_even WO_SF5_RA ltac:(unfold WO_SF5_RA; lia) eq_refl).
      pose proof (munch_app _ _ _ _ _ MU1 MU2) as MU12. pose proof (wmono_trans asegs _ _ _ WM1 WM2) as WM12. cbn [app] in MU12.
      assert (SV2 : rw_cells asegs m2 (SP - 104) (wsaved e)).
      { eapply rw_cells_transport; [exact (winv_sv H _ _ _ _ _ _ _ HI) | exact MU12 | exact WM12 | cbn; unfold WO_SAVED; lia]. }
      assert (SF2 : rw_cells asegs m2 (ff + 504) [C8 (Z_to_bv 64 fp)]).
      { eapply rw_cells_transport; [exact (winv_sf H _ _ _ _ _ _ _ HI) | exact MU12 | exact WM12 | cbn; unfold WO_FLAGP; lia]. }
      assert (WP2 : wr_at asegs m2 fp 1) by exact (wr_at_wmono _ _ _ _ (winv_wfp H _ _ _ _ _ _ _ HI) WM12).

      unfold wsaved in SV2.
      destruct (we2 (Z_to_bv 64 WO_SF5_RA) v0 v1 v2 v10 v11 v12 v13 v14 v15 v16 v17 v28 v29 v30 v31 (w_gp e) (w_tp e)
                  (w_ra e) (w_s0 e) (w_s1 e) (w_s2 e) (w_s3 e) (w_s4 e) (w_s5 e) (w_s6 e) (w_s7 e) (w_s8 e) (w_s9 e) (w_s10 e) (w_s11 e)
                  F fc m2 (seg_rom asegs) ff fp SP S1 r w F3 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                  SV2 SF2 WP2 MI2) as (R3 & m3 & RUN3 & HR3 & MU3 & WM3 & MI3 & ST3 & FL3).
      eapply evt_of_msteps; [exact RUN3|]. subst R3. unfold WO_RET. step. apply evt_done.
      do 14 eexists. exists m3. split; [reflexivity|].
      split; [pose proof (munch_app _ _ _ _ _ MU12 MU3) as MU13; eapply munch_eqW; [exact MU13 | unfold WT; reflexivity]|].
      split; [exact (wmono_trans asegs _ _ _ WM12 WM3)|]. split; [exact MI3|].
      split; [apply ST3; eapply stk_wmono; [exact ST1 | exact WM2 | lia] | exact FL3]. }

    intros msF2 mo2 KR2 MP2 P2. destruct P2 as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m3 & VIS3 & MU & WM & MI3 & ST3 & FL3).
    apply (ah_done H HB). unfold wpost, po_post.
    pose proof (wlinv H HB e ff fp XS16 s16 LB16 m0 HP HI) as LV0.
    destruct HI as (RF & _ & RH & AC & _ & S0 & RA & (errv & ER) & _ & _ & _ & _ & _ & XP & FS & _).
    hnf. exists t0, t1, t2, (Z_to_bv 64 r), a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m3, errv, s16, LB16, (XW H ff fp ++ XS16), F, fc.
    cbn [cfg_ms cfg_model]. rewrite VIS3.
    assert (ESP : Z_to_bv 64 SP = w_sp e) by (unfold SP, wSP; apply Z_to_bv_bv_unsigned).
    rewrite ESP.
    split; [reflexivity|]. split; [exact FZ|]. split; [exact KR2|].
    split; [exact (ah_mpres_trans H HB (w_mo e) mo mo2 MP MP2)|].
    split; [exact MI3|]. split; [unfold SP in ST3; exact ST3|].
    split; [eapply rw_cells_transport; [exact ER | exact MU | exact WM |]; rewrite (werrno_ATP H e TP);
            cbn [cells_size csize]; apply DJ; intros iv Hiv; pose proof (proj1 (Forall_forall _ _) WOK iv Hiv) as X;
            destruct X as (_ & _ & _ & _ & _ & X & _); lia|].
    assert (A1 : Forall (aclient_write_ok H LB16) WT) by (eapply Forall_impl; [| exact WOK]; intros iv X; apply X).
    split; [eapply (ah_rauxv_frame H HB); [exact RA | exact MU | exact WM | exact A1]|].
    split; [eapply (ah_RHEAP_frame H HB); [exact RH | exact MU | exact WM | exact A1]|].
    split; [exact PERM|].
    split; [apply Forall_app; split; [exact (fs_scratch_of_fresh H (w_LF e) 3 ff fp FFR) | exact FS]|].
    split.
    { eapply xpres_trans; [exact XP|]. eapply (xpres_of_munch H (w_s e) (w_LB e) SP _ WT (w_m e)); [exact HB | exact (wpre_RH0 H e HP) | exact MU | exact WM |].
      eapply Forall_impl; [| exact WOK]. intros iv X. right. intros a Ha. right. apply X. exact Ha. }
    split.
    { pose proof (ah_release H HB ((3, ff, fp) :: w_LF e) m0 m3 WT 3 ff fp RF (or_introl eq_refl) MU WM) as K.
      rewrite lf_remove_head in K. apply K; [| exact FL3]. eapply Forall_impl; [| exact WOK]. intros iv X. apply X. }
    split; [eapply ACONST_frame; [exact AC | exact MU | exact WM |]; eapply Forall_impl; [| exact WOK]; intros iv X; apply X|].
    split; [eapply stack0_transport; [exact S0 | exact MU | exact WM |]; eapply Forall_impl; [| exact WOK]; intros iv X; apply X|].
    split.
    { eapply LINV_P5_cl; [exact LV0|].
      intros a Ha Hc. apply MU. rewrite HLib.u64_of_Z by lia.
      clear - Hc F1 F4 F8 F14. unfold aimg_client in Hc. unfold WT. cbn. lia. }
    pose proof (wpre_budget H e HP) as (_ & _ & _ & _ & AL0). lia.
  Qed.
End WoEnd.
