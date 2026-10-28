(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Sj Require Import SjTape SjTapeList SjTapeTile.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.P Require Import Str_tac Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface RT_iface2 RT_iface3 D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_num_akit Atp_fzwA Atp_defsA Atp_kitA Pj_rtkA Pj_defsA Pj_os_defsA El_defsA El_os_defsA El_ins_ifaceA Dmp_hdefsA Dmp_pj_ifaceA Dmp_insbA Dmp_pj_kitA Dmp_pj_leafA Dmp_pj_strA Dmp_pj_aevtA Dmp_pj_entryA Dmp_pj_getdA Dmp_pj_svhA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Local Ltac ulx := unfold DMP_PJ_LEAF_A, DMP_PJ_FRAME_A, EL_PUT_STACK_A, EL_INS_STACK_A, EL_INSD_STACK_A, SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, SHB in *; lia.

Local Ltac acc_in := unfold ACC_LITS; cbn [In]; repeat (try (left; reflexivity); right).

Section Cases.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis SM2 : stack_malloc2_contract RT.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.
Hypothesis PUT : os_put_cpsA RT PMc.
Hypothesis INSB : ins_b_cpsA RT PMc.
Hypothesis INSL : ins_l_cpsA RT PMc.
Hypothesis INSUL : ins_ul_cpsA RT PMc.
Hypothesis INSD : ins_d_cpsA RT PMc.
Notation aevt := (aevt RT PMc).
Notation PINVA := (PINVA RT).
Notation KEXITA := (KEXITA RT PMc).

Variable G : pctx.
Hypothesis GOK : pctx_ok G.
Hypothesis AI0 : AINV_A (g_E G) (g_m0 G).
Hypothesis IOS0 : io_ssp (g_m0 G).
Notation E := (g_E G).

Let facts : aenvA_ok E /\ 0x6d5000 <= g_q G - 256 /\ g_q G < 2^63 /\ 0 <= g_OS G + 128 < 2^64 /\ 0 < g_ff G /\ ae_n E < 2^32 /\ 0 <= ae_sn E < 2^56.
Proof.
  destruct GOK as [(Q32 & QT & LQ) (LO1 & LO2) (SP1 & SP2) (OK & _) (EIN & ELO & EHI & _) (F0 & _) _ _ RFR _ _ _].
  pose proof (RFR _ _ EIN) as (_ & ESEG & EL & _). pose proof (pj_needA_0 (g_d G)) as ND. pose proof (Atp_defsA.ok_wf E OK) as (NR & SNR & _).
  assert (0 <= fs_size (g_kO G)) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
  split; [exact OK|]. repeat split; try assumption; ulx.
Qed.

Lemma pc_null : forall (jA jB jC : list byte) (sv : list cell) (k kx : Z) (Σ : rts RT) (K : config -> Prop) (i : Z)
    (ra gp a1 a2 a3 a4 a5 a6 a7 s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  PINVA G (pj_frD jA (g_OS G + 128) jB (g_ff G) jC (ae_DOC E) i sv) k Σ m -> frm0 fc ->
  0 <= i < ae_n E -> ae_T E i = tword t_null 0 -> k + 4 <= kx -> kx <= g_cr G ->
  (forall LC : list cell, cells_size LC = 152%nat -> KEXITA G (LC ++ sv) kx K gp) ->
  aevt Σ K (MS (pjR (g_q G) (g_ff G) gp ra (wz (ae_TAPE E + 8 * i)) a1 a2 a3 a4 a5 a6 a7 (wz (ae_DOC E)) (wz i) s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6) F (wz DMP_PJ_DISP_A) fc None m (seg_rom bsegs)).
Proof using AF FDO MST PUT GOK AI0 facts.
  intros until m. intros GI FRM IR TI KB KX HK. pose proof facts as (OK & QLO & QH & OR & F0 & NR & SNR).
  pose proof GI as (_ & MI & _ & _ & _ & _ & ST & _ & _ & _ & _ & (FR & _) & _).
  pose proof (pj_frD_80 _ _ _ _ _ _ _ _ _ _ FR) as (j80 & F80).
  pose proof (PINVA_shz RT AF G GOK _ _ _ _ AI0 GI) as (SHZT & _ & _). pose proof (PINVA_ainv RT AF G GOK _ _ _ _ AI0 GI) as AI.
  assert (TIR : 0 <= ae_T E i < 2^64) by (rewrite TI; apply tword_range; unfold t_null; lia).
  assert (TY : ttype (ae_T E i) = 110) by (rewrite TI, ttype_tword by lia; reflexivity).
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (pj_null1 E (g_q G) (g_ff G) (g_OS G + 128) i j80 gp ra a1 a2 a3 a4 a5 a6 a7 s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6 F fc m OK IR TIR TY QLO QH OR AI SHZT F80 MI)|].
  cbv beta. intros ms1 (m1 & -> & MU1 & WM1 & MI1 & _). apply evt_done.
  assert (ST1 : stk bsegs m1 (g_lo G) (g_S1 G)).
  { apply (stk_agree bsegs m m1 _ _ ST); [| exact WM1]. apply (agree_of_munch _ _ _ _ MU1). intros x Hx. cbn [outside]. clear - Hx. split; [lia| exact I]. }
  destruct (PINVA_leafD RT AF G jA (g_OS G + 128) jB (g_ff G) jC (ae_DOC E) i sv k Σ m m1 [(g_q G - 176, g_q G - 168)] GOK GI MU1 WM1 MI1 ST1)
    as (jA1 & jC1 & GI1).
  { intros a. destruct (Z_lt_dec a (g_q G - 176)) as [L|L]; [left; cbn [outside]; split; [lia| exact I]|].
    destruct (Z_lt_dec a (g_q G - 168)) as [L2|L2]; [right; right; left; lia| left; cbn [outside]; split; [lia| exact I]]. }
  clear GI. rename GI1 into GI. unfold pjR, DMP_LIT_NULL_A.
  eapply (p_put_lit RT AF PMc FDO MST G GOK _ k Σ K 0x234c0 4 5 4%nat); [exact PUT| exact GI| acc_in| vm_compute; reflexivity| vm_compute; reflexivity
    | cbn; lia| cbn; lia| lia| unfold SEGTOP_A; lia| clear - KB KX; lia|].
  intros Σ2 u0 u1 u2 e1 e2 e3 e4 e5 e6 e7 u3 u4 u5 u6 F2 m2 GI2. rewrite (ret_pc_even (pj_endl_pc 1)) by (cbn [pj_endl_pc]; lia).
  eapply (p_endl RT AF PMc FDO MST G 1 _ (k + 2) Σ2 K); [exact GOK| exact PUT| exact GI2| lia| clear - KB KX; lia|].
  intros Σ3 b0 b1 b2 b3 b4 b5 b6 b7 v0 v1 v2 v3 v4 v5 v6 F3 m3 GI3.
  unfold pj_frD in GI3. unfold pjR. eapply HK; [| exact GI3| clear - KB; lia| exact FRM]. reflexivity.
Qed.

Lemma pc_bool : forall (jA jB jC : list byte) (sv : list cell) (k kx : Z) (Σ : rts RT) (K : config -> Prop) (i : Z)
    (ra gp a1 a2 a3 a4 a5 a6 a7 s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  PINVA G (pj_frD jA (g_OS G + 128) jB (g_ff G) jC (ae_DOC E) i sv) k Σ m -> frm0 fc ->
  0 <= i < ae_n E -> (ae_T E i = tword t_true 0 \/ ae_T E i = tword t_false 0) -> k + 3 <= kx -> kx <= g_cr G ->
  (forall LC : list cell, cells_size LC = 152%nat -> KEXITA G (LC ++ sv) kx K gp) ->
  aevt Σ K (MS (pjR (g_q G) (g_ff G) gp ra (wz (ae_TAPE E + 8 * i)) a1 a2 a3 a4 a5 a6 a7 (wz (ae_DOC E)) (wz i) s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6) F (wz DMP_PJ_DISP_A) fc None m (seg_rom bsegs)).
Proof using AF FDO MST PUT INSB GOK AI0 IOS0 facts.
  intros until m. intros GI FRM IR TI KB KX HK. pose proof facts as (OK & QLO & QH & OR & F0 & NR & SNR).
  pose proof GI as (HA & MI & _ & _ & _ & _ & ST & _ & _ & _ & _ & (FR & _) & _).
  pose proof GOK as GK. destruct GK as [(_ & QT & LQ) _ _ _ _ _ _ _ _ _ _ _].
  pose proof (pj_needA_0 (g_d G)) as ND. unfold DMP_PJ_FRAME_A, DMP_PJ_LEAF_A, RT_STACK in ND.
  assert (SLO : g_lo G <= g_q G - 272) by (clear - LQ ND; lia).
  pose proof (pj_frD_80 _ _ _ _ _ _ _ _ _ _ FR) as (j80 & F80). pose proof (pj_frD_di _ _ _ _ _ _ _ _ _ _ FR) as FD.
  pose proof (PINVA_shz RT AF G GOK _ _ _ _ AI0 GI) as (SHZT & _ & _). pose proof (PINVA_ainv RT AF G GOK _ _ _ _ AI0 GI) as AI.
  assert (TIR : 0 <= ae_T E i < 2^64) by (destruct TI as [TI|TI]; rewrite TI; apply tword_range; unfold t_true, t_false; lia).
  assert (TY : ttype (ae_T E i) = 116 \/ ttype (ae_T E i) = 102) by (destruct TI as [TI|TI]; rewrite TI, ttype_tword by lia; [left| right]; reflexivity).
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (pj_bool1 E (g_q G) (g_ff G) (g_OS G + 128) i j80 gp ra a1 a2 a3 a4 a5 a6 a7 s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6 F fc m
    OK IR TIR TY QLO QH OR AI SHZT (af_client_consts RT AF Σ m HA) ST SLO F80 FD MI)|].
  cbv beta. intros ms1 (m1 & a2x & a3x & a4x & s5x & s9x & -> & MU1 & WM1 & MI1 & ST1 & _). apply evt_done.
  destruct (PINVA_leafD RT AF G jA (g_OS G + 128) jB (g_ff G) jC (ae_DOC E) i sv k Σ m m1 [(g_q G - 272, g_q G - 256); (g_q G - 176, g_q G - 168)]
              GOK GI MU1 WM1 MI1 ST1) as (jA1 & jC1 & GI1).
  { intros a. destruct (Z_lt_dec a (g_q G - 272)); [left; cbn [outside]; repeat split; try exact I; lia|].
    destruct (Z_lt_dec a (g_q G - 256)); [right; left; lia|].
    destruct (Z_lt_dec a (g_q G - 176)); [left; cbn [outside]; repeat split; try exact I; lia|].
    destruct (Z_lt_dec a (g_q G - 168)); [right; right; left; lia| left; cbn [outside]; repeat split; try exact I; lia]. }
  clear GI. rename GI1 into GI. unfold pjR, DMP_INS_B_A.
  pose proof INSB as INSB'. unfold ins_b_cpsA in INSB'.
  eapply (p_ins RT AF PMc FDO MST G GOK _ _ _ _ k Σ K (pj_boolv (ae_T E i))); [exact INSB'| exact GI| exact IOS0| unfold pj_boolv; destruct (Z.eqb _ _); [right| left]; reflexivity
    | exact FRM| ulx| clear - KB KX; lia|].
  intros Σ2 u0 u1 u2 e1 e2 e3 e4 e5 e6 e7 u3 u4 u5 u6 F2 fc2 m2 GI2 FRM2. rewrite (ret_pc_even (pj_endl_pc 2)) by (cbn [pj_endl_pc]; lia).
  eapply (p_endl RT AF PMc FDO MST G 2 _ (k + 1) Σ2 K); [exact GOK| exact PUT| exact GI2| lia| clear - KB KX; lia|].
  intros Σ3 b0 b1 b2 b3 b4 b5 b6 b7 v0 v1 v2 v3 v4 v5 v6 F3 m3 GI3.
  unfold pj_frD in GI3. unfold pjR. eapply HK; [| exact GI3| clear - KB; lia| exact FRM2]. reflexivity.
Qed.

Lemma pc_num : forall (jA jB jC : list byte) (sv : list cell) (k kx : Z) (Σ : rts RT) (K : config -> Prop) (i : Z)
    (ra gp a1 a2 a3 a4 a5 a6 a7 s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  PINVA G (pj_frD jA (g_OS G + 128) jB (g_ff G) jC (ae_DOC E) i sv) k Σ m -> frm0 fc ->
  0 <= i -> i + 1 < ae_n E -> (ae_T E i = tword t_i64 0 \/ ae_T E i = tword t_u64 0) -> k + 3 <= kx -> kx <= g_cr G ->
  (forall LC : list cell, cells_size LC = 152%nat -> KEXITA G (LC ++ sv) kx K gp) ->
  aevt Σ K (MS (pjR (g_q G) (g_ff G) gp ra (wz (ae_TAPE E + 8 * i)) a1 a2 a3 a4 a5 a6 a7 (wz (ae_DOC E)) (wz i) s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6) F (wz DMP_PJ_DISP_A) fc None m (seg_rom bsegs)).
Proof using AF FDO MST PUT INSL INSUL GOK AI0 IOS0 facts.
  intros until m. intros GI FRM I0 IN TI KB KX HK. pose proof facts as (OK & QLO & QH & OR & F0 & NR & SNR).
  pose proof GI as (HA & MI & _ & _ & _ & _ & ST & _ & _ & _ & _ & (FR & _) & _).
  pose proof GOK as GK. destruct GK as [(_ & QT & LQ) _ _ _ _ _ _ _ _ _ _ _].
  pose proof (pj_needA_0 (g_d G)) as ND. unfold DMP_PJ_FRAME_A, DMP_PJ_LEAF_A, RT_STACK in ND.
  assert (SLO : g_lo G <= g_q G - 272) by (clear - LQ ND; lia).
  pose proof (pj_frD_80 _ _ _ _ _ _ _ _ _ _ FR) as (j80 & F80). pose proof (pj_frD_di _ _ _ _ _ _ _ _ _ _ FR) as FD.
  pose proof (PINVA_shz RT AF G GOK _ _ _ _ AI0 GI) as (SHZT & _ & _). pose proof (PINVA_ainv RT AF G GOK _ _ _ _ AI0 GI) as AI.
  assert (LEAF : forall m1, munch [(g_q G - 272, g_q G - 256); (g_q G - 176, g_q G - 168)] m m1 -> wmono bsegs m m1 -> mem_inv bsegs m1 ->
            stk bsegs m1 (g_lo G) (g_S1 G) -> exists jA1 jC1, PINVA G (pj_frD jA1 (g_OS G + 128) jB (g_ff G) jC1 (ae_DOC E) i sv) k Σ m1).
  { intros m1 MU1 WM1 MI1 ST1. apply (PINVA_leafD RT AF G jA (g_OS G + 128) jB (g_ff G) jC (ae_DOC E) i sv k Σ m m1 _ GOK GI MU1 WM1 MI1 ST1).
    intros a. destruct (Z_lt_dec a (g_q G - 272)); [left; cbn [outside]; repeat split; try exact I; lia|].
    destruct (Z_lt_dec a (g_q G - 256)); [right; left; lia|].
    destruct (Z_lt_dec a (g_q G - 176)); [left; cbn [outside]; repeat split; try exact I; lia|].
    destruct (Z_lt_dec a (g_q G - 168)); [right; right; left; lia| left; cbn [outside]; repeat split; try exact I; lia]. }
  clear GI. destruct TI as [TI|TI].
  -
    assert (TW : ae_T E i = 108 * 2^56) by (rewrite TI; unfold tword, t_i64; lia).
    apply (aevt_evt RT AF PMc MST).
    eapply evt_cut; [eapply (pj_num1 E 108 (g_q G) (g_ff G) (g_OS G + 128) i j80 gp ra a1 a2 a3 a4 a5 a6 a7 s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6 F fc m
      OK I0 IN ltac:(left; reflexivity) TW QLO QH OR AI SHZT (af_client_consts RT AF Σ m HA) ST SLO F80 FD MI)|].
    cbv beta. intros ms1 (m1 & a2x & a3x & a4x & s5x & s9x & -> & MU1 & WM1 & MI1 & ST1 & _). apply evt_done.
    destruct (LEAF m1 MU1 WM1 MI1 ST1) as (jA1 & jC1 & GI).
    unfold pjR, pj_num_ins, pj_num_slot. cbn [Z.eqb Pos.eqb]. unfold DMP_INS_L_A.
    pose proof INSL as INSL'. unfold ins_l_cpsA in INSL'.
    replace (Z_to_bv 64 (ae_T E (i + 1))) with (Z_to_bv 64 ((ae_T E (i + 1) + 2 ^ 63) mod 2 ^ 64 - 2 ^ 63))
      by (apply Z_to_bv64_eqm; rewrite Zminus_mod_idemp_l; f_equal; lia).
    eapply (p_ins RT AF PMc FDO MST G GOK _ _ _ _ k Σ K); [exact INSL'| exact GI| exact IOS0| cbv beta; pose proof (Z.mod_pos_bound (ae_T E (i + 1) + 2 ^ 63) (2 ^ 64) ltac:(lia)); lia
      | exact FRM| ulx| clear - KB KX; lia|].
    intros Σ2 u0 u1 u2 e1 e2 e3 e4 e5 e6 e7 u3 u4 u5 u6 F2 fc2 m2 GI2 FRM2. rewrite (ret_pc_even (pj_endl_pc 6)) by (cbn [pj_endl_pc]; lia).
    eapply (p_endl RT AF PMc FDO MST G 6 _ (k + 1) Σ2 K); [exact GOK| exact PUT| exact GI2| lia| clear - KB KX; lia|].
    intros Σ3 b0 b1 b2 b3 b4 b5 b6 b7 v0 v1 v2 v3 v4 v5 v6 F3 m3 GI3.
    unfold pj_frD in GI3. unfold pjR. eapply HK; [| exact GI3| clear - KB; lia| exact FRM2]. reflexivity.
  -
    assert (TW : ae_T E i = 117 * 2^56) by (rewrite TI; unfold tword, t_u64; lia).
    apply (aevt_evt RT AF PMc MST).
    eapply evt_cut; [eapply (pj_num1 E 117 (g_q G) (g_ff G) (g_OS G + 128) i j80 gp ra a1 a2 a3 a4 a5 a6 a7 s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6 F fc m
      OK I0 IN ltac:(right; reflexivity) TW QLO QH OR AI SHZT (af_client_consts RT AF Σ m HA) ST SLO F80 FD MI)|].
    cbv beta. intros ms1 (m1 & a2x & a3x & a4x & s5x & s9x & -> & MU1 & WM1 & MI1 & ST1 & _). apply evt_done.
    destruct (LEAF m1 MU1 WM1 MI1 ST1) as (jA1 & jC1 & GI).
    unfold pjR, pj_num_ins, pj_num_slot. cbn [Z.eqb Pos.eqb]. unfold DMP_INS_UL_A.
    pose proof INSUL as INSUL'. unfold ins_ul_cpsA in INSUL'.
    replace (Z_to_bv 64 (ae_T E (i + 1))) with (Z_to_bv 64 ((ae_T E (i + 1)) mod 2 ^ 64)) by (apply Z_to_bv64_eqm; rewrite Z.mod_mod by lia; reflexivity).
    eapply (p_ins RT AF PMc FDO MST G GOK _ _ _ _ k Σ K); [exact INSUL'| exact GI| exact IOS0| cbv beta; pose proof (Z.mod_pos_bound (ae_T E (i + 1)) (2 ^ 64) ltac:(lia)); lia
      | exact FRM| ulx| clear - KB KX; lia|].
    intros Σ2 u0 u1 u2 e1 e2 e3 e4 e5 e6 e7 u3 u4 u5 u6 F2 fc2 m2 GI2 FRM2. rewrite (ret_pc_even (pj_endl_pc 5)) by (cbn [pj_endl_pc]; lia).
    eapply (p_endl RT AF PMc FDO MST G 5 _ (k + 1) Σ2 K); [exact GOK| exact PUT| exact GI2| lia| clear - KB KX; lia|].
    intros Σ3 b0 b1 b2 b3 b4 b5 b6 b7 v0 v1 v2 v3 v4 v5 v6 F3 m3 GI3.
    unfold pj_frD in GI3. unfold pjR. eapply HK; [| exact GI3| clear - KB; lia| exact FRM2]. reflexivity.
Qed.

Lemma pc_dbl : forall (jA jB jC : list byte) (sv : list cell) (k kx : Z) (Σ : rts RT) (K : config -> Prop) (i : Z)
    (ra gp a1 a2 a3 a4 a5 a6 a7 s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  PINVA G (pj_frD jA (g_OS G + 128) jB (g_ff G) jC (ae_DOC E) i sv) k Σ m -> frm0 fc ->
  0 <= i -> i + 1 < ae_n E -> ae_T E i = tword t_dbl 0 -> k + 3 <= kx -> kx <= g_cr G ->
  (forall LC : list cell, cells_size LC = 152%nat -> KEXITA G (LC ++ sv) kx K gp) ->
  aevt Σ K (MS (pjR (g_q G) (g_ff G) gp ra (wz (ae_TAPE E + 8 * i)) a1 a2 a3 a4 a5 a6 a7 (wz (ae_DOC E)) (wz i) s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6) F (wz DMP_PJ_DISP_A) fc None m (seg_rom bsegs)).
Proof using AF FDO MST PUT INSD GOK AI0 IOS0 facts.
  intros until m. intros GI FRM I0 IN TI KB KX HK. pose proof facts as (OK & QLO & QH & OR & F0 & NR & SNR).
  pose proof GI as (_ & MI & _ & _ & _ & _ & ST & _ & _ & _ & _ & (FR & _) & _).
  pose proof GOK as GK. destruct GK as [(Q32 & QT & LQ) (LO1 & LO2) _ _ _ _ _ _ _ _ _ _].
  pose proof (pj_needA_0 (g_d G)) as ND. unfold DMP_PJ_FRAME_A, DMP_PJ_LEAF_A, RT_STACK in ND.
  pose proof (pj_frD_80 _ _ _ _ _ _ _ _ _ _ FR) as (j80 & F80).
  pose proof (PINVA_shz RT AF G GOK _ _ _ _ AI0 GI) as (SHZT & _ & _). pose proof (PINVA_ainv RT AF G GOK _ _ _ _ AI0 GI) as AI.
  assert (TW : ae_T E i = 100 * 2^56) by (rewrite TI; unfold tword, t_dbl; lia).
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (pj_dbl1 E (g_q G) (g_ff G) (g_OS G + 128) i j80 gp ra a1 a2 a3 a4 a5 a6 a7 s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6 F fc m OK I0 IN TW QLO QH OR AI SHZT F80 MI)|].
  cbv beta. intros ms1 (m1 & a1x & a2x & a3x & -> & MU1 & WM1 & MI1 & F176).
  assert (ST1 : stk bsegs m1 (g_lo G) (g_S1 G)).
  { apply (stk_agree bsegs m m1 _ _ ST); [| exact WM1]. apply (agree_of_munch _ _ _ _ MU1). intros x Hx. cbn [outside]. clear - Hx. split; [lia| exact I]. }
  destruct (PINVA_leafD RT AF G jA (g_OS G + 128) jB (g_ff G) jC (ae_DOC E) i sv k Σ m m1 [(g_q G - 176, g_q G - 168)] GOK GI MU1 WM1 MI1 ST1)
    as (jA1 & jC1 & GI1).
  { intros a. destruct (Z_lt_dec a (g_q G - 176)) as [L|L]; [left; cbn [outside]; split; [lia| exact I]|].
    destruct (Z_lt_dec a (g_q G - 168)) as [L2|L2]; [right; right; left; lia| left; cbn [outside]; split; [lia| exact I]]. }
  clear GI.
  pose proof GI1 as (HA1 & _ & _ & _ & SP01 & _ & _ & _ & _ & _ & _ & (FR1 & _) & _).
  pose proof (pj_frD_di _ _ _ _ _ _ _ _ _ _ FR1) as FD1.
  pose proof (PINVA_shz RT AF G GOK _ _ _ _ AI0 GI1) as (SHZT1 & _ & _). pose proof (PINVA_ainv RT AF G GOK _ _ _ _ AI0 GI1) as AI1.
  assert (SHEL : shz m1 (g_q G - 256 + 136) 16).
  { apply (Atp_defsA.shz_stack RT AF Σ m1 _ 16 HA1); [rewrite SP01; clear - LO2 LQ ND; lia| clear - QT; lia| clear - Q32; Z.div_mod_to_equations; lia| reflexivity| lia]. }
  unfold pjR.
  eapply evt_cut; [eapply (getd_walk E (g_q G - 256) (g_q G - 256 + 136) i); [exact OK| exact AI1| exact (af_client_consts RT AF Σ m1 HA1)| exact MI1| exact ST1
      | clear - LQ ND; lia| clear - QT; lia| clear - Q32; Z.div_mod_to_equations; lia| exact SHZT1| exact FD1| clear - Q32; Z.div_mod_to_equations; lia| exact SHEL
      | right; lia| clear - QLO; lia| clear - QT; lia| exact I0| exact IN| exact TI]|].
  cbv beta. intros ms2 (x0 & x1 & x2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & mg & -> & MU2 & WM2 & MI2 & ST2 & _).
  rewrite ret_pc_even by lia.
  assert (F176' : rw_cells bsegs mg (g_q G - 176) [C8 (wz SHB); C8 (wz (g_OS G + 128))]).
  { apply (D_kit.rw_cells_agree_nw bsegs m1 mg _ _ F176). apply (agree_of_munch _ _ _ _ MU2). intros x (Hx & _). cbn [outside]. split; [lia| exact I]. }
  destruct (PINVA_leafD RT AF G jA1 (g_OS G + 128) jB (g_ff G) jC1 (ae_DOC E) i sv k Σ m1 mg [(g_q G - 256 - 64, g_q G - 256)] GOK GI1 MU2 WM2 MI2 ST2)
    as (jA2 & jC2 & GI).
  { intros a. destruct (Z_lt_dec a (g_q G - 256 - 64)) as [L|L]; [left; cbn [outside]; split; [lia| exact I]|].
    destruct (Z_lt_dec a (g_q G - 256)) as [L2|L2]; [right; left; clear - L L2 LQ ND; lia| left; cbn [outside]; split; [lia| exact I]]. }
  clear GI1.
  eapply evt_cut; [eapply (pj_dbl2 (g_q G) (g_ff G) (g_OS G + 128)); [exact QLO| exact QH| exact OR| exact F176'| exact MI2]|].
  cbv beta. intros ms3 ->. apply evt_done. unfold pjR.
  eapply (p_insd RT AF PMc FDO MST G GOK _ k Σ K); [exact INSD| exact GI| exact IOS0| exact FRM| clear - KB KX; lia|].
  intros Σ2 u0 u1 u2 e1 e2 e3 e4 e5 e6 e7 u3 u4 u5 u6 F2 fc2 m2 GI2 FRM2. rewrite (ret_pc_even (pj_endl_pc 4)) by (cbn [pj_endl_pc]; lia).
  eapply (p_endl RT AF PMc FDO MST G 4 _ (k + 1) Σ2 K); [exact GOK| exact PUT| exact GI2| lia| clear - KB KX; lia|].
  intros Σ3 b0 b1 b2 b3 b4 b5 b6 b7 v0 v1 v2 v3 v4 v5 v6 F3 m3 GI3.
  unfold pj_frD in GI3. unfold pjR. eapply HK; [| exact GI3| clear - KB; lia| exact FRM2]. reflexivity.
Qed.

Lemma pc_str : forall (jA jB jC : list byte) (sv : list cell) (k kx : Z) (Σ : rts RT) (K : config -> Prop) (i : Z)
    (ra gp a1 a2 a3 a4 a5 a6 a7 s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  PINVA G (pj_frD jA (g_OS G + 128) jB (g_ff G) jC (ae_DOC E) i sv) k Σ m -> frm0 fc ->
  0 <= i < ae_n E -> is_str (ae_T E) (ae_S E) (ae_sn E) i -> k + 4 <= kx -> kx <= g_cr G ->
  (forall LC : list cell, cells_size LC = 152%nat -> KEXITA G (LC ++ sv) kx K gp) ->
  aevt Σ K (MS (pjR (g_q G) (g_ff G) gp ra (wz (ae_TAPE E + 8 * i)) a1 a2 a3 a4 a5 a6 a7 (wz (ae_DOC E)) (wz i) s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6) F (wz DMP_PJ_DISP_A) fc None m (seg_rom bsegs)).
Proof using AF FDO MST PUT GOK AI0 facts.
  intros until m. intros GI FRM IR STR KB KX HK. pose proof facts as (OK & QLO & QH & OR & F0 & NR & SNR).
  pose proof GI as (_ & MI & _ & _ & _ & _ & ST & _ & _ & _ & _ & (FR & _) & _).
  pose proof GOK as GK. destruct GK as [(Q32 & QT & LQ) (LO1 & LO2) _ _ _ _ _ _ _ _ _ _].
  pose proof (pj_needA_0 (g_d G)) as ND. unfold DMP_PJ_FRAME_A, DMP_PJ_LEAF_A, RT_STACK in ND.
  pose proof (pj_frD_80 _ _ _ _ _ _ _ _ _ _ FR) as (j80 & F80).
  pose proof (PINVA_shz RT AF G GOK _ _ _ _ AI0 GI) as (SHZT & _ & _). pose proof (PINVA_ainv RT AF G GOK _ _ _ _ AI0 GI) as AI.
  destruct (is_str_read _ _ _ (proj2 SNR) _ STR) as [KT _].
  destruct STR as (o & l & TO & SA).
  assert (TIR : 0 <= ae_T E i < 2^64) by (rewrite TO; apply tword_range; [unfold t_str; lia| pose proof (str_at_bounds _ _ (proj2 SNR) _ _ SA); lia]).
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (pj_str1 E (g_q G) (g_ff G) (g_OS G + 128) i j80 gp ra a1 a2 a3 a4 a5 a6 a7 s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6 F fc m OK IR TIR KT QLO QH AI SHZT F80 MI)|].
  cbv beta. intros ms1 (m1 & -> & MU1 & WM1 & MI1 & _).
  assert (ST1 : stk bsegs m1 (g_lo G) (g_S1 G)).
  { apply (stk_agree bsegs m m1 _ _ ST); [| exact WM1]. apply (agree_of_munch _ _ _ _ MU1). intros x Hx. cbn [outside]. clear - Hx. split; [lia| exact I]. }
  destruct (PINVA_leafD RT AF G jA (g_OS G + 128) jB (g_ff G) jC (ae_DOC E) i sv k Σ m m1 _ GOK GI MU1 WM1 MI1 ST1) as (jA1 & jC1 & GI1).
  { intros a. destruct (Z_lt_dec a (g_q G - 256 + 80)) as [L|L]; [left; cbn [outside]; split; [lia| exact I]|].
    destruct (Z_lt_dec a (g_q G - 256 + 88)) as [L2|L2]; [right; right; left; lia| left; cbn [outside]; split; [lia| exact I]]. }
  clear GI.
  pose proof GI1 as (HA1 & _ & _ & _ & SP01 & _ & _ & _ & _ & _ & _ & (FR1 & _) & _).
  pose proof (pj_frD_di _ _ _ _ _ _ _ _ _ _ FR1) as FD1.
  assert (FRC : rw_cells bsegs m1 (g_q G - 256 + 112) [CB 24 jC1]).
  { unfold pj_frD in FR1.
    pose proof (rw_cells_mid m1 (g_q G - 256) [CB 88 jA1; C8 (wz (g_OS G + 128)); CB 8 jB; C8 (wz (g_ff G))] [CB 24 jC1] ([C8 (wz (ae_DOC E)); C8 (wz i)] ++ sv) FR1) as X.
    change (Z.of_nat (cells_size [CB 88 jA1; C8 (wz (g_OS G + 128)); CB 8 jB; C8 (wz (g_ff G))])) with 112 in X. exact X. }
  pose proof (PINVA_shz RT AF G GOK _ _ _ _ AI0 GI1) as (SHZT1 & SHZS1 & _). pose proof (PINVA_ainv RT AF G GOK _ _ _ _ AI0 GI1) as AI1.
  assert (SHEL : shz m1 (g_q G - 256 + 136) 16).
  { apply (Atp_defsA.shz_stack RT AF Σ m1 _ 16 HA1); [rewrite SP01; clear - LO2 LQ ND; lia| clear - QT; lia| clear - Q32; Z.div_mod_to_equations; lia| reflexivity| lia]. }
  assert (SHR : shz m1 (g_q G - 256 + 112) 24).
  { apply (Atp_defsA.shz_stack RT AF Σ m1 _ 24 HA1); [rewrite SP01; clear - LO2 LQ ND; lia| clear - QT; lia| clear - Q32; Z.div_mod_to_equations; lia| reflexivity| lia]. }
  unfold pjR. change DMP_PJ_SCALL_A with DMP_PJ_SVH_A.
  eapply evt_cut; [eapply (svh_walk E (g_q G - 256) (g_q G - 256 + 112) (g_q G - 256 + 136) i o l); [exact OK| exact AI1| exact (af_client_consts RT AF Σ m1 HA1)| exact MI1| exact ST1
      | clear - LQ ND; lia| clear - Q32; Z.div_mod_to_equations; lia| exact SHZT1| exact SHZS1| lia| exact TO| exact SA
      | exact FD1| clear - Q32; Z.div_mod_to_equations; lia| exact SHEL| right; lia| clear - QLO; lia| clear - QT; lia
      | exact FRC| clear - Q32; Z.div_mod_to_equations; lia| exact SHR| lia| clear - QT; lia| right; lia]|].
  cbv beta. intros ms2 (x0 & x1 & x2 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & e4 & mg & -> & RC & MU2 & WM2 & MI2 & ST2 & _).
  rewrite ret_pc_even by (unfold DMP_PJ_SRET_A; lia).
  destruct (PINVA_leafD RT AF G jA1 (g_OS G + 128) jB (g_ff G) jC1 (ae_DOC E) i sv k Σ m1 mg _ GOK GI1 MU2 WM2 MI2 ST2) as (jA2 & jC2 & GI).
  { intros a. destruct (Z_lt_dec a (g_q G - 256 - 96)) as [L|L]; [left; cbn [outside]; repeat split; try exact I; lia|].
    destruct (Z_lt_dec a (g_q G - 256)) as [L2|L2]; [right; left; clear - L L2 LQ ND; lia|].
    destruct (Z_lt_dec a (g_q G - 256 + 112)) as [L3|L3]; [left; cbn [outside]; repeat split; try exact I; lia|].
    destruct (Z_lt_dec a (g_q G - 256 + 112 + 24)) as [L4|L4]; [right; right; right; lia| left; cbn [outside]; repeat split; try exact I; lia]. }
  clear GI1.
  pose proof GI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (FR2 & _) & _).
  pose proof (pj_frD_osp _ _ _ _ _ _ _ _ _ _ FR2) as FO2.
  pose proof (rw_cells_mid mg (g_q G - 256 + 112) [] [C8 (wz (ae_SBUF E + o + 4)); C8 (wz l)] [C4 (wz 0); CB 4 e4] RC) as RPL.
  change (Z.of_nat (cells_size [])) with 0 in RPL. rewrite Z.add_0_r in RPL.
  eapply evt_cut; [eapply (pj_str2 (g_q G) (g_ff G) (g_OS G + 128) (ae_SBUF E + o + 4) l); [exact QLO| exact QH| exact FO2| exact RPL| exact MI2]|].
  cbv beta. intros ms3 ->. apply evt_done. unfold pjR.
  eapply (p_put_live RT AF PMc FDO MST G GOK _ k Σ K o l); [exact PUT| exact GI| exact AI0| exact SA| clear - KB KX; lia|].
  intros Σ2 u0 u1 u2 e1 e2 e3 e4' e5 e6 e7 u3 u4 u5 u6 F2 m2 GI2.
  rewrite (ret_pc_even DMP_PJ_SPUT_A) by (unfold DMP_PJ_SPUT_A; lia). change DMP_PJ_SPUT_A with (pj_endl_pc 3).
  eapply (p_endl RT AF PMc FDO MST G 3 _ (k + 2) Σ2 K); [exact GOK| exact PUT| exact GI2| lia| clear - KB KX; lia|].
  intros Σ3 b0 b1 b2 b3 b4 b5 b6 b7 v0 v1 v2 v3 v4 v5 v6 F3 m3 GI3.
  unfold pj_frD in GI3. unfold pjR. eapply HK; [| exact GI3| clear - KB; lia| exact FRM]. reflexivity.
Qed.
End Cases.
