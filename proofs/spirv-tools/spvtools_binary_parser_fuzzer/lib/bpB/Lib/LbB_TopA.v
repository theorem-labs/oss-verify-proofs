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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import DvB_FuzzStmt LbB_PrsStmt LbB_DStat LbB_SR LbB_Conv.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_TopDefs LbB_TopKit LbB_TopH1 LbB_TopH2.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section TopA.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps_bp H.

  Definition hF8_post (e : hent H) : machine_state -> Prop :=
    fun ms' => exists (ff fp : Z) x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m',
      ms' = MS (mkR (Z_to_bv 64 TOP_F8_RA) (Z_to_bv 64 (eS1 e)) (e_gp e) (e_tp e) x5 x6 x7 (Z_to_bv 64 (eSP e))
                    (Z_to_bv 64 (eS1 e)) x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff + 4)) (Z_to_bv 64 ff)
                    (Z_to_bv 64 (sh ff)) (Z_to_bv 64 0x7fff8000) (e_s7 e) (e_s8 e) (e_s9 e) (e_s10 e) (Z_to_bv 64 (e_N e)) x28 x29
                    x30 x31) (e_F e) (Z_to_bv 64 TOP_F8_RA) (e_fc e) None m' (seg_rom asegs)
      /\ hinv H e ff fp [] (e_s e) (e_LB e) m'
       /\ rw_cells asegs m' (eS1 e + 88) [C8 (Z_to_bv 64 (e_D e))]
      /\ rw_cells asegs m' (sh ff + 4) [CB 313 (poison_bytes 313 0xf8)]
      /\ wr_at asegs m' (sh ff + 317) 27
      /\ wr_at asegs m' (ff + 32) 2504
      /\ (exists jv, rw_cells asegs m' (ff + 2672) [CB 24 jv]).

  Lemma tA0 : forall (e : hent H) (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    hpre H e ->
    evt asegs (hF8_post e)
      (MS (mkR (e_ra e) (e_sp e) (e_gp e) (e_tp e) t0 t1 t2 (e_s0 e) (e_s1 e) (Z_to_bv 64 (e_D e)) (Z_to_bv 64 (e_N e))
               a2 a3 a4 a5 a6 a7 (e_s2 e) (e_s3 e) (e_s4 e) (e_s5 e) (e_s6 e) (e_s7 e) (e_s8 e) (e_s9 e) (e_s10 e) (e_s11 e)
               t3 t4 t5 t6) (e_F e) (Z_to_bv 64 TOP_ENTRY) (e_fc e) None (e_m e) (seg_rom asegs)).
Proof.
    intros e t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 HP.
    pose proof (rt_bp_base H HH) as HB.
    pose proof (rt_bp_ext H HH) as (_ & _ & _ & _ & SM6 & _ & _ & _ & _ & _ & SSF8).
    pose proof (eS1_facts H e HP) as (S32 & S1SP & S1L & SPH & LOS1 & _).
    pose proof (hpre_geo H e HP) as (CE & LO & SSHI & SHIH & SP16 & TP).
    pose proof (hpre_D H e HP) as DR.
    pose proof HP as (_ & _ & _ & NR & _ & _ & _ & RH0 & _ & _ & _ & RA & _ & _ & _ & ST & _ & _ & (errv & ER) & MI & _ & LV & _ & AC
                      & _ & RF & LFL & S0 & _).
    pose proof aceil_facts as ACF.
    assert (WSUB : forall m a n i k, wr_at asegs m a n -> 0 <= i -> 0 <= k -> i + k <= n -> wr_at asegs m (a + i) k).
    { intros m a n i k (W0 & W1 & W) Hi Hk Hik. split; [lia|]. split; [lia|]. intros j Hj. rewrite <- Z.add_assoc. apply W. lia. }
    set (SP := eSP e) in *. set (S1 := eS1 e) in *. set (lo := e_lo e) in *.

    eapply evt_cut.
    { eapply (h1a (e_ra e) (e_sp e) (e_gp e) (e_tp e) t0 t1 t2 (e_s0 e) (e_s1 e) (Z_to_bv 64 (e_D e)) (Z_to_bv 64 (e_N e))
                  a2 a3 a4 a5 a6 a7 (e_s2 e) (e_s3 e) (e_s4 e) (e_s5 e) (e_s6 e) (e_s7 e) (e_s8 e) (e_s9 e) (e_s10 e) (e_s11 e)
                  t3 t4 t5 t6 (e_F e) (e_fc e) (e_m e) (e_D e) (e_N e) lo);
        try change (bv_unsigned (e_sp e)) with SP; [reflexivity | reflexivity | exact DR | exact NR | exact SP16 | lia | exact ST
        | exact CE | lia | exact MI | exact AC]. }
    intros ms1 P1.
    destruct P1 as (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m1 & EQ1 & MU1 & WM1 & MI1 & ST1 & SV1 & DC1).
    subst ms1. change (bv_unsigned (e_sp e)) with SP in *. change (SP - 224 - SP mod 32) with S1 in *.

    assert (X1 : aceil <= SP - 224) by lia.
    assert (X2 : as_FSB H + AFS_SIZE <= aceil) by (pose proof (ah_RFS_range H HB _ _ RF) as [(_ & X & _) _]; exact X).
    pose proof (stack_window_ok H (e_LB e) (e_LF e) (SP - 224) SP X1 X2) as (W1a & W1b & W1c). clear X1 X2.
    assert (RF1 : as_RFS H (e_LF e) m1)
      by (eapply (ah_RFS_frame H HB); [exact RF | exact MU1 | exact WM1 | apply Forall_cons; [exact W1b | apply Forall_nil]]).
    assert (RH1 : as_RHEAP H (e_s e) (e_LB e) m1)
      by (eapply (ah_RHEAP_frame H HB); [exact RH0 | exact MU1 | exact WM1 | apply Forall_cons; [exact W1a | apply Forall_nil]]).
    assert (AC1 : ACONST m1)
      by (eapply ACONST_frame; [exact AC | exact MU1 | exact WM1 | apply Forall_cons; [exact W1c | apply Forall_nil]]).

    eapply evt_cut.
    { eapply (SM6 (Z_to_bv 64 TOP_SM_RET) (Z_to_bv 64 S1)) with (LF := e_LF e) (lo := lo);
        [exact RF1 | lia | rewrite HLib.u64_of_Z by lia; exact (proj1 (stk_split asegs m1 lo S1 SP ST1 ltac:(lia)))
        | exact CE | rewrite HLib.u64_of_Z by lia; unfold AFS_STACK; lia | exact MI1 | exact TP | exact AC1 | exact (ah_thr H HB _ _ _ RH1)]. }
    intros ms2 P2.
    destruct P2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & ff & fp & k1 & k2
                    & EQ2 & MU2 & WM2 & MI2 & ST2 & RF2 & CF2 & SF2 & FP2 & AC2).
    subst ms2. rewrite HLib.u64_of_Z in MU2, ST2 by lia. unfold AFS_STACK in MU2.
    rewrite (ret_pc_even TOP_SM_RET ltac:(unfold TOP_SM_RET; lia) eq_refl).
    pose proof (fresh_of_RFS H HB (e_LF e) 6 ff fp m2 RF2) as FFR.
    pose proof (hframe_facts H _ _ _ FFR) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16).
    change (fsz 6) with 4096 in *. change (fshn 6) with 512 in *. change (Z.to_nat (4096 - 40)) with 4056%nat in CF2.
    assert (WFF : wr_at asegs m2 ff 4096) by (eapply rw_cells_wr_at; [exact CF2 | cbn; lia]).
    assert (SF0 : rw_cells asegs m2 (ff + 4088) [C8 (Z_to_bv 64 fp)]).
    { destruct (proj1 (rw_cells_app asegs m2 ff [CB 24 k1; C8 (Z_to_bv 64 S1); CB 4056 k2] [C8 (Z_to_bv 64 fp)]) CF2) as [_ CFb].
      cbn [cells_size csize] in CFb. change (Z.of_nat (24 + (8 + (4056 + 0)))) with 4088 in CFb. exact CFb. }
    assert (CJ : exists jv, rw_cells asegs m2 (ff + 2672) [CB 24 jv]).
    { destruct (proj1 (rw_cells_app asegs m2 ff [CB 24 k1; C8 (Z_to_bv 64 S1)] [CB 4056 k2; C8 (Z_to_bv 64 fp)]) CF2) as [_ CFm].
      destruct (proj1 (rw_cells_app asegs m2 _ [CB 4056 k2] [C8 (Z_to_bv 64 fp)]) CFm) as [CFk _].
      destruct (rw_cells_CB_sub m2 _ 4056 k2 2640 24 CFk ltac:(lia) ltac:(lia) ltac:(lia)) as (jv & CJ).
      exists jv. replace (ff + 2672) with (ff + Z.of_nat (cells_size [CB 24 k1; C8 (Z_to_bv 64 S1)]) + 2640) by (cbn; lia). exact CJ. }
    pose proof SF2 as (_ & _ & U2).
    pose proof SF2 as (_ & _ & _ & WSH).
    pose proof (WSUB m2 ff 4096 0 24 WFF ltac:(lia) ltac:(lia) ltac:(lia)) as W24. rewrite Z.add_0_r in W24.
    pose proof (WSUB m2 (sh ff) 512 0 4 WSH ltac:(lia) ltac:(lia) ltac:(lia)) as WS4. rewrite Z.add_0_r in WS4.
    assert (U4 : u8arr asegs m2 (sh ff + 4) (repeat (b8 0) (Z.to_nat 313)))
      by exact (u8arr_repeat_sub m2 (sh ff) (b8 0) 512%nat 4 313 U2 ltac:(lia) ltac:(lia) ltac:(lia)).

    assert (ST2f : stk asegs m2 lo SP).
    { destruct (stk_split asegs m1 lo S1 SP ST1 ltac:(lia)) as [_ STu].
      assert (STu2 : stk asegs m2 S1 SP)
        by (eapply stk_transport_disjoint; [exact STu | exact MU2 | exact WM2 | cbn; unfold AFS_FLAGS; lia]).
      exact (stk_merge asegs m2 lo S1 SP ST2 STu2 ltac:(lia)). }
    assert (HI2 : hinv H e ff fp [] (e_s e) (e_LB e) m2).
    { assert (WL2 : Forall (fun iv => aclient_write_ok H (e_LB e) iv /\ stack0_ok iv)
                      [(S1 - 1024, S1); (as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1); (ff, ff + 4096); (sh ff, sh ff + 512)]).
      { repeat apply Forall_cons; try apply Forall_nil; (split; [unfold aclient_write_ok; cbn [fst snd] | ]).
        - left. lia.
        - apply stack0_ok_app. unfold AHI_LO. lia.
        - right; right; right; right; left. unfold AFS_FLAGS, AFS_SIZE. lia.
        - eapply (stack0_ok_aapp (as_FSB H) AFS_SIZE); [exact F10 | lia | unfold AFS_FLAGS, AFS_SIZE; lia].
        - right; right; right; right; left. unfold AFS_SIZE in *. lia.
        - eapply (stack0_ok_aapp (as_FSB H) AFS_SIZE); [exact F10 | lia | unfold AFS_SIZE in *; lia].
        - right; right; right; right; left. lia.
        - eapply (stack0_ok_aapp (as_FSB H) AFS_SIZE); [exact F10 | lia | lia].
        - right; right; right; right; right; left. lia.
        - right. cbn. assert (sh (ff + 4096) <= sh aceil) by (apply sh_mono; lia). lia. }
      apply Forall_and_inv in WL2 as [WL2a WL2b].
      unfold hinv. fold SP lo. rewrite (errno_ATP H e TP) in ER |- *.
      split; [exact RF2|]. split; [exact FFR|].
      split; [eapply (ah_RHEAP_frame H HB); [exact RH1 | exact MU2 | exact WM2 | exact WL2a]|].
      split; [exact AC2|]. split; [exact MI2|].
      split.
      { eapply stack0_transport; [| exact MU2 | exact WM2 | exact WL2b].
        eapply stack0_transport; [exact S0 | exact MU1 | exact WM1 | apply Forall_cons; [apply stack0_ok_app; unfold AHI_LO; lia | apply Forall_nil]]. }
      split.
      { eapply (ah_rauxv_frame H HB); [| exact MU2 | exact WM2 | exact WL2a].
        eapply (ah_rauxv_frame H HB); [exact RA | exact MU1 | exact WM1 | apply Forall_cons; [exact W1a | apply Forall_nil]]. }
      split.
      { exists errv. eapply rw_cells_transport; [| exact MU2 | exact WM2 | cbn; unfold ATP, AFS_FLAGS; lia].
        eapply rw_cells_transport; [exact ER | exact MU1 | exact WM1 | cbn; unfold ATP; lia]. }
      split; [exact ST2f|].
      split; [eapply rw_cells_transport; [exact SV1 | exact MU2 | exact WM2 | cbn; unfold AFS_FLAGS; lia]|].
      split; [exact SF0|].
      split; [destruct WFF as (W0 & W1 & W); split; [lia|]; split; [lia|]; intros i Hi; apply W; lia|].
      split; [| split; [apply Forall_nil|]].
      2: {
        eapply LbB_TdKit.LINV_P5_munch_hi; [exact LV | exact (munch_app _ _ _ _ _ MU1 MU2) |].
        repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; unfold AIMG_TOP, AFS_FLAGS in *; lia. }
      rewrite app_nil_r.
      eapply (xpres_of_munch H (e_s e) (e_LB e) SP ((RtB_Td.ATDLOC, RtB_Td.ATDLOC + 8) :: XH H ff fp)
                ([(SP - 224, SP)] ++ [(S1 - 1024, S1); (as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1); (ff, ff + 4096); (sh ff, sh ff + 512)])
                (e_m e));
        [exact HB | exact RH0 | exact (munch_app _ _ _ _ _ MU1 MU2) | exact (wmono_trans asegs _ _ _ WM1 WM2) |].
      unfold XH. change (fsz 6) with 4096. change (fshn 6) with 512.
      repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd app].
      - left. lia.
      - left. lia.
      - right. intros a Ha. cbn. right; left. lia.
      - right. intros a Ha. cbn. right; right; left. lia.
      - right. intros a Ha. cbn. right; right; right; left. lia.
      - right. intros a Ha. cbn. right; right; right; right; left. lia. }

    eapply evt_cut.
    { eapply (h2a (e_gp e) (e_tp e) u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 (e_s2 e) (e_s3 e) (e_s4 e) (e_s6 e) (e_s7 e) (e_s8 e) (e_s9 e) (e_s10 e)
                  u3 u4 u5 u6 (e_F e) (e_fc e) m2 SP S1 ff (e_N e) lo);
        [exact S32 | exact S1L | lia | exact SPH | lia | exact F3 | lia | lia | exact W24 | exact WS4 | exact ST2f | exact MI2]. }
    intros ms3 P3.
    destruct P3 as (y5 & y6 & y7 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m3 & EQ3 & MU3 & WM3 & MI3 & ST3).
    subst ms3.
    assert (HI3 : hinv H e ff fp [] (e_s e) (e_LB e) m3).
    { eapply (hinv_munch H HB e ff fp [] (e_s e) (e_LB e) m2 m3); [exact HP | exact HI2 | exact MU3 | exact WM3 | exact MI3 | exact ST3 |].
      repeat apply Forall_cons; try apply Forall_nil; unfold hwin; cbn [fst snd]; fold SP lo; lia. }
    assert (U5 : u8arr asegs m3 (sh ff + 4) (repeat (b8 0) (Z.to_nat 313))).
    { eapply u8arr_transport; [exact U4 | exact MU3 | exact WM3 |]. rewrite repeat_length. cbn [disjoint_from fst snd]. lia. }

    eapply evt_cut.
    { eapply (SSF8 (Z_to_bv 64 TOP_F8_RA) (Z_to_bv 64 S1)) with (sa := sh ff + 4) (n := 313);
        [reflexivity | reflexivity | lia | exact (rw_cells_of_u8arr asegs m3 _ _ U5) | exact MI3 | exact (hinv_ac H _ _ _ _ _ _ _ HI3)]. }
    intros ms4 P4.
    destruct P4 as (c0 & c1 & c2 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & c3 & c4 & c5 & c6 & m4 & EQ4 & MU4 & WM4 & MI4 & SH4).
    subst ms4. rewrite (ret_pc_even TOP_F8_RA ltac:(unfold TOP_F8_RA; lia) eq_refl).
    apply evt_done. unfold hF8_post.
    exists ff, fp, c0, c1, c2, d0, d1, d2, d3, d4, d5, d6, d7, c3, c4, c5, c6, m4. split; [reflexivity|].
    split.
    { eapply (hinv_munch H HB e ff fp [] (e_s e) (e_LB e) m3 m4); [exact HP | exact HI3 | exact MU4 | exact WM4 | exact MI4 | |].
      - eapply stk_transport_disjoint; [exact ST3 | exact MU4 | exact WM4 |]. fold SP lo. cbn [disjoint_from fst snd]. lia.
      - repeat apply Forall_cons; try apply Forall_nil; unfold hwin; cbn [fst snd]; fold SP lo; lia. }
    split.
    { fold S1.
      eapply rw_cells_transport; [| exact MU4 | exact WM4 | cbn [disjoint_from fst snd cells_size csize]; lia].
      eapply rw_cells_transport; [| exact MU3 | exact WM3 | cbn [disjoint_from fst snd cells_size csize]; lia].
      eapply rw_cells_transport; [exact DC1 | exact MU2 | exact WM2 | cbn [disjoint_from fst snd cells_size csize]; unfold AFS_FLAGS; lia]. }
    split; [exact SH4|].
    split.
    { pose proof (WSUB m2 (sh ff) 512 317 27 WSH ltac:(lia) ltac:(lia) ltac:(lia)) as X.
      exact (wr_at_wmono _ _ _ _ (wr_at_wmono _ _ _ _ X WM3) WM4). }
    split.
    { pose proof (WSUB m2 ff 4096 32 2504 WFF ltac:(lia) ltac:(lia) ltac:(lia)) as X.
      exact (wr_at_wmono _ _ _ _ (wr_at_wmono _ _ _ _ X WM3) WM4). }
    destruct CJ as (jv & CJ). exists jv.
    eapply rw_cells_transport; [| exact MU4 | exact WM4 | cbn [disjoint_from fst snd cells_size csize]; lia].
    eapply rw_cells_transport; [exact CJ | exact MU3 | exact WM3 | cbn [disjoint_from fst snd cells_size csize]; lia].
Qed.
End TopA.
