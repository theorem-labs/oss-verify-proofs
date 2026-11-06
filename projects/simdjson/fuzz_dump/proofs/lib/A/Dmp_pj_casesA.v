(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Spec Require Import Prelim.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Sj Require Import SjTape SjTapeList SjTapeTile.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.P Require Import Str_tac Sj_stage1_kit.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.A Require Import Layout Shadow RT_iface RT_iface2 RT_iface3 D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_rtf Sj_akit Sj_acps Sj_hkit
     Sj_num_akit Atp_fzwA Atp_defsA Atp_kitA Pj_rtkA Pj_defsA Pj_os_defsA El_defsA El_os_defsA El_ins_ifaceA Dmp_hdefsA Dmp_pj_ifaceA Dmp_insbA Dmp_pj_kitA Dmp_pj_leafA
     Dmp_pj_strA Dmp_pj_aevtA Dmp_pj_entryA.
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

Let facts : aenvA_ok E /\ 0x6c9000 <= g_q G - 256 /\ g_q G < 2^63 /\ 0 <= g_OS G + 128 < 2^64 /\ 0 < g_ff G /\ ae_n E < 2^32 /\ 0 <= ae_sn E < 2^56.
Proof.
  destruct GOK as [(Q32 & QT & LQ) (LO1 & LO2) (SP1 & SP2) (OK & _) (EIN & ELO & EHI & _) (F0 & _) _ _ RFR _ _ _].
  pose proof (RFR _ _ EIN) as (_ & ESEG & EL & _). pose proof (pj_needA_0 (g_d G)) as ND. pose proof (Atp_defsA.ok_wf E OK) as (NR & SNR & _).
  assert (0 <= fs_size (g_kO G)) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
  split; [exact OK|]. repeat split; try assumption; ulx.
Qed.

Lemma pc_null : forall (jA jB : list byte) (sv : list cell) (k kx : Z) (Σ : rts RT) (K : config -> Prop) (i : Z)
    (ra gp a0 a1 a2 a3 a4 a5 a6 a7 s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  PINVA G (pj_frD jA (g_OS G + 128) jB (g_ff G) sv) k Σ m -> frm0 fc ->
  0 <= i < ae_n E -> ae_T E i = tword t_null 0 -> k + 4 <= kx -> kx <= g_cr G ->
  KEXITA G (pj_frD jA (g_OS G + 128) jB (g_ff G) sv) kx K gp ->
  aevt Σ K (MS (pjR (g_q G) (g_ff G) gp ra a0 a1 a2 a3 a4 a5 a6 a7 (wz (ae_DOC E)) (wz i) s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6) F (wz DMP_PJ_DISP_A) fc None m (seg_rom asegs)).
Proof using AF FDO MST PUT GOK AI0 facts.
  intros until m. intros GI FRM IR TI KB KX HK. pose proof facts as (OK & QLO & QH & OR & F0 & NR & SNR).
  pose proof GI as (_ & MI & _ & _ & _ & _ & _ & _ & _ & _ & _ & (FR & _) & _). pose proof (pj_frD_osp _ _ _ _ _ _ _ FR) as FO.
  pose proof (PINVA_shz RT AF G GOK _ _ _ _ AI0 GI) as (SHZT & _ & _). pose proof (PINVA_ainv RT AF G GOK _ _ _ _ AI0 GI) as AI.
  assert (TIR : 0 <= ae_T E i < 2^64) by (rewrite TI; apply tword_range; unfold t_null; lia).
  assert (TY : ttype (ae_T E i) = 110) by (rewrite TI, ttype_tword by lia; reflexivity).
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (pj_null1 E (g_q G) (g_ff G) (g_OS G + 128) i gp ra a0 a1 a2 a3 a4 a5 a6 a7 s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6 F fc m OK IR TIR TY QLO QH OR AI SHZT FO MI)|].
  cbv beta. intros ms1 ->. apply evt_done. unfold pjR, DMP_LIT_NULL_A.
  eapply (p_put_lit RT AF PMc FDO MST G GOK _ k Σ K 0x23460 4 5 4%nat); [exact PUT| exact GI| acc_in| vm_compute; reflexivity| vm_compute; reflexivity
    | cbn; lia| cbn; lia| lia| unfold SEGTOP_A; lia| clear - KB KX; lia|].
  intros Σ2 u0 u1 u2 e1 e2 e3 e4 e5 e6 e7 u3 u4 u5 u6 F2 m2 GI2. rewrite (ret_pc_even (pj_endl_pc 1)) by (cbn [pj_endl_pc]; lia).
  eapply (p_endl RT AF PMc FDO MST G 1 _ (k + 2) Σ2 K); [exact GOK| exact PUT| exact GI2| lia| clear - KB KX; lia|].
  intros Σ3 b0 b1 b2 b3 b4 b5 b6 b7 v0 v1 v2 v3 v4 v5 v6 F3 m3 GI3.
  eapply HK; [exact GI3| clear - KB; lia| exact FRM].
Qed.

Lemma pc_bool : forall (jA jB : list byte) (sv : list cell) (k kx : Z) (Σ : rts RT) (K : config -> Prop) (i : Z)
    (ra gp a0 a1 a2 a3 a4 a5 a6 a7 s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  PINVA G (pj_frD jA (g_OS G + 128) jB (g_ff G) sv) k Σ m -> frm0 fc ->
  0 <= i < ae_n E -> (ae_T E i = tword t_true 0 \/ ae_T E i = tword t_false 0) -> k + 3 <= kx -> kx <= g_cr G ->
  KEXITA G (pj_frD jA (g_OS G + 128) jB (g_ff G) sv) kx K gp ->
  aevt Σ K (MS (pjR (g_q G) (g_ff G) gp ra a0 a1 a2 a3 a4 a5 a6 a7 (wz (ae_DOC E)) (wz i) s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6) F (wz DMP_PJ_DISP_A) fc None m (seg_rom asegs)).
Proof using AF FDO MST PUT INSB GOK AI0 IOS0 facts.
  intros until m. intros GI FRM IR TI KB KX HK. pose proof facts as (OK & QLO & QH & OR & F0 & NR & SNR).
  pose proof GI as (_ & MI & _ & _ & _ & _ & _ & _ & _ & _ & _ & (FR & _) & _). pose proof (pj_frD_osp _ _ _ _ _ _ _ FR) as FO.
  pose proof (PINVA_shz RT AF G GOK _ _ _ _ AI0 GI) as (SHZT & _ & _). pose proof (PINVA_ainv RT AF G GOK _ _ _ _ AI0 GI) as AI.
  assert (TIR : 0 <= ae_T E i < 2^64) by (destruct TI as [TI|TI]; rewrite TI; apply tword_range; unfold t_true, t_false; lia).
  assert (TY : ttype (ae_T E i) = 116 \/ ttype (ae_T E i) = 102) by (destruct TI as [TI|TI]; rewrite TI, ttype_tword by lia; [left| right]; reflexivity).
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (pj_bool1 E (g_q G) (g_ff G) (g_OS G + 128) i gp ra a0 a1 a2 a3 a4 a5 a6 a7 s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6 F fc m OK IR TIR TY QLO QH OR AI SHZT FO MI)|].
  cbv beta. intros ms1 ->. apply evt_done. unfold pjR, DMP_INS_B_A.
  pose proof INSB as INSB'. unfold ins_b_cpsA in INSB'.
  eapply (p_ins RT AF PMc FDO MST G GOK _ _ _ _ k Σ K (pj_boolv (ae_T E i))); [exact INSB'| exact GI| exact IOS0| unfold pj_boolv; destruct (Z.eqb _ _); [right| left]; reflexivity
    | exact FRM| ulx| clear - KB KX; lia|].
  intros Σ2 u0 u1 u2 e1 e2 e3 e4 e5 e6 e7 u3 u4 u5 u6 F2 fc2 m2 GI2 FRM2. rewrite (ret_pc_even (pj_endl_pc 2)) by (cbn [pj_endl_pc]; lia).
  eapply (p_endl RT AF PMc FDO MST G 2 _ (k + 1) Σ2 K); [exact GOK| exact PUT| exact GI2| lia| clear - KB KX; lia|].
  intros Σ3 b0 b1 b2 b3 b4 b5 b6 b7 v0 v1 v2 v3 v4 v5 v6 F3 m3 GI3.
  eapply HK; [exact GI3| clear - KB; lia| exact FRM2].
Qed.

Lemma pc_num : forall (jA jB : list byte) (sv : list cell) (k kx : Z) (Σ : rts RT) (K : config -> Prop) (i : Z)
    (ra gp a0 a1 a2 a3 a4 a5 a6 a7 s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  PINVA G (pj_frD jA (g_OS G + 128) jB (g_ff G) sv) k Σ m -> frm0 fc ->
  0 <= i -> i + 1 < ae_n E -> (ae_T E i = tword t_i64 0 \/ ae_T E i = tword t_u64 0) -> k + 3 <= kx -> kx <= g_cr G ->
  KEXITA G (pj_frD jA (g_OS G + 128) jB (g_ff G) sv) kx K gp ->
  aevt Σ K (MS (pjR (g_q G) (g_ff G) gp ra a0 a1 a2 a3 a4 a5 a6 a7 (wz (ae_DOC E)) (wz i) s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6) F (wz DMP_PJ_DISP_A) fc None m (seg_rom asegs)).
Proof using AF FDO MST PUT INSL INSUL GOK AI0 IOS0 facts.
  intros until m. intros GI FRM I0 IN TI KB KX HK. pose proof facts as (OK & QLO & QH & OR & F0 & NR & SNR).
  pose proof GI as (_ & MI & _ & _ & _ & _ & _ & _ & _ & _ & _ & (FR & _) & _). pose proof (pj_frD_osp _ _ _ _ _ _ _ FR) as FO.
  pose proof (PINVA_shz RT AF G GOK _ _ _ _ AI0 GI) as (SHZT & _ & _). pose proof (PINVA_ainv RT AF G GOK _ _ _ _ AI0 GI) as AI.
  destruct TI as [TI|TI].
  -
    assert (TW : ae_T E i = 108 * 2^56) by (rewrite TI; unfold tword, t_i64; lia).
    apply (aevt_evt RT AF PMc MST).
    eapply evt_cut; [eapply (pj_num1 E 108 (g_q G) (g_ff G) (g_OS G + 128) i gp ra a0 a1 a2 a3 a4 a5 a6 a7 s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6 F fc m OK I0 IN ltac:(left; reflexivity) TW QLO QH OR AI SHZT FO MI)|].
    cbv beta. intros ms1 (a2x & a3x & ->). apply evt_done. unfold pjR, pj_num_ins, pj_num_slot. cbn [Z.eqb Pos.eqb]. unfold DMP_INS_L_A.
    pose proof INSL as INSL'. unfold ins_l_cpsA in INSL'.
    replace (Z_to_bv 64 (ae_T E (i + 1))) with (Z_to_bv 64 ((ae_T E (i + 1) + 2 ^ 63) mod 2 ^ 64 - 2 ^ 63))
      by (apply Z_to_bv64_eqm; rewrite Zminus_mod_idemp_l; f_equal; lia).
    eapply (p_ins RT AF PMc FDO MST G GOK _ _ _ _ k Σ K); [exact INSL'| exact GI| exact IOS0| cbv beta; pose proof (Z.mod_pos_bound (ae_T E (i + 1) + 2 ^ 63) (2 ^ 64) ltac:(lia)); lia
      | exact FRM| ulx| clear - KB KX; lia|].
    intros Σ2 u0 u1 u2 e1 e2 e3 e4 e5 e6 e7 u3 u4 u5 u6 F2 fc2 m2 GI2 FRM2. rewrite (ret_pc_even (pj_endl_pc 6)) by (cbn [pj_endl_pc]; lia).
    eapply (p_endl RT AF PMc FDO MST G 6 _ (k + 1) Σ2 K); [exact GOK| exact PUT| exact GI2| lia| clear - KB KX; lia|].
    intros Σ3 b0 b1 b2 b3 b4 b5 b6 b7 v0 v1 v2 v3 v4 v5 v6 F3 m3 GI3.
    eapply HK; [exact GI3| clear - KB; lia| exact FRM2].
  -
    assert (TW : ae_T E i = 117 * 2^56) by (rewrite TI; unfold tword, t_u64; lia).
    apply (aevt_evt RT AF PMc MST).
    eapply evt_cut; [eapply (pj_num1 E 117 (g_q G) (g_ff G) (g_OS G + 128) i gp ra a0 a1 a2 a3 a4 a5 a6 a7 s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6 F fc m OK I0 IN ltac:(right; reflexivity) TW QLO QH OR AI SHZT FO MI)|].
    cbv beta. intros ms1 (a2x & a3x & ->). apply evt_done. unfold pjR, pj_num_ins, pj_num_slot. cbn [Z.eqb Pos.eqb]. unfold DMP_INS_UL_A.
    pose proof INSUL as INSUL'. unfold ins_ul_cpsA in INSUL'.
    replace (Z_to_bv 64 (ae_T E (i + 1))) with (Z_to_bv 64 ((ae_T E (i + 1)) mod 2 ^ 64)) by (apply Z_to_bv64_eqm; rewrite Z.mod_mod by lia; reflexivity).
    eapply (p_ins RT AF PMc FDO MST G GOK _ _ _ _ k Σ K); [exact INSUL'| exact GI| exact IOS0| cbv beta; pose proof (Z.mod_pos_bound (ae_T E (i + 1)) (2 ^ 64) ltac:(lia)); lia
      | exact FRM| ulx| clear - KB KX; lia|].
    intros Σ2 u0 u1 u2 e1 e2 e3 e4 e5 e6 e7 u3 u4 u5 u6 F2 fc2 m2 GI2 FRM2. rewrite (ret_pc_even (pj_endl_pc 5)) by (cbn [pj_endl_pc]; lia).
    eapply (p_endl RT AF PMc FDO MST G 5 _ (k + 1) Σ2 K); [exact GOK| exact PUT| exact GI2| lia| clear - KB KX; lia|].
    intros Σ3 b0 b1 b2 b3 b4 b5 b6 b7 v0 v1 v2 v3 v4 v5 v6 F3 m3 GI3.
    eapply HK; [exact GI3| clear - KB; lia| exact FRM2].
Qed.

Lemma pc_dbl : forall (jA jB : list byte) (sv : list cell) (k kx : Z) (Σ : rts RT) (K : config -> Prop) (i : Z)
    (ra gp a0 a1 a2 a3 a4 a5 a6 a7 s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  PINVA G (pj_frD jA (g_OS G + 128) jB (g_ff G) sv) k Σ m -> frm0 fc ->
  0 <= i -> i + 1 < ae_n E -> ae_T E i = tword t_dbl 0 -> k + 3 <= kx -> kx <= g_cr G ->
  KEXITA G (pj_frD jA (g_OS G + 128) jB (g_ff G) sv) kx K gp ->
  aevt Σ K (MS (pjR (g_q G) (g_ff G) gp ra a0 a1 a2 a3 a4 a5 a6 a7 (wz (ae_DOC E)) (wz i) s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6) F (wz DMP_PJ_DISP_A) fc None m (seg_rom asegs)).
Proof using AF FDO MST PUT INSD GOK AI0 IOS0 facts.
  intros until m. intros GI FRM I0 IN TI KB KX HK. pose proof facts as (OK & QLO & QH & OR & F0 & NR & SNR).
  pose proof GI as (_ & MI & _ & _ & _ & _ & _ & _ & _ & _ & _ & (FR & _) & _). pose proof (pj_frD_osp _ _ _ _ _ _ _ FR) as FO.
  pose proof (PINVA_shz RT AF G GOK _ _ _ _ AI0 GI) as (SHZT & _ & _). pose proof (PINVA_ainv RT AF G GOK _ _ _ _ AI0 GI) as AI.
  assert (TW : ae_T E i = 100 * 2^56) by (rewrite TI; unfold tword, t_dbl; lia).
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (pj_dbl1 E (g_q G) (g_ff G) (g_OS G + 128) i gp ra a0 a1 a2 a3 a4 a5 a6 a7 s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6 F fc m OK I0 IN TW QLO QH OR AI SHZT FO MI)|].
  cbv beta. intros ms1 (a1x & a2x & a3x & ->). apply evt_done. unfold pjR.
  eapply (p_insd RT AF PMc FDO MST G GOK _ k Σ K); [exact INSD| exact GI| exact IOS0| exact FRM| clear - KB KX; lia|].
  intros Σ2 u0 u1 u2 e1 e2 e3 e4 e5 e6 e7 u3 u4 u5 u6 F2 fc2 m2 GI2 FRM2. rewrite (ret_pc_even (pj_endl_pc 4)) by (cbn [pj_endl_pc]; lia).
  eapply (p_endl RT AF PMc FDO MST G 4 _ (k + 1) Σ2 K); [exact GOK| exact PUT| exact GI2| lia| clear - KB KX; lia|].
  intros Σ3 b0 b1 b2 b3 b4 b5 b6 b7 v0 v1 v2 v3 v4 v5 v6 F3 m3 GI3.
  eapply HK; [exact GI3| clear - KB; lia| exact FRM2].
Qed.

Lemma pc_str : forall (jA jB : list byte) (sv : list cell) (k kx : Z) (Σ : rts RT) (K : config -> Prop) (i : Z)
    (ra gp a0 a1 a2 a3 a4 a5 a6 a7 s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  PINVA G (pj_frD jA (g_OS G + 128) jB (g_ff G) sv) k Σ m -> frm0 fc ->
  0 <= i < ae_n E -> is_str (ae_T E) (ae_S E) (ae_sn E) i -> k + 4 <= kx -> kx <= g_cr G ->
  KEXITA G (pj_frD jA (g_OS G + 128) jB (g_ff G) sv) kx K gp ->
  aevt Σ K (MS (pjR (g_q G) (g_ff G) gp ra a0 a1 a2 a3 a4 a5 a6 a7 (wz (ae_DOC E)) (wz i) s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6) F (wz DMP_PJ_DISP_A) fc None m (seg_rom asegs)).
Proof using AF FDO MST PUT GOK AI0 facts.
  intros until m. intros GI FRM IR STR KB KX HK. pose proof facts as (OK & QLO & QH & OR & F0 & NR & SNR).
  pose proof GI as (_ & MI & _ & _ & _ & _ & _ & _ & _ & _ & _ & (FR & _) & _). pose proof (pj_frD_osp _ _ _ _ _ _ _ FR) as FO.
  pose proof (PINVA_shz RT AF G GOK _ _ _ _ AI0 GI) as (SHZT & SHZS & _). pose proof (PINVA_ainv RT AF G GOK _ _ _ _ AI0 GI) as AI.
  destruct (is_str_read _ _ _ (proj2 SNR) _ STR) as [KT (l & SA)].
  assert (TIR : 0 <= ae_T E i < 2^64).
  { destruct STR as (o0 & l0 & X & SA0). rewrite X. apply tword_range; [unfold t_str; lia| pose proof (str_at_bounds _ _ (proj2 SNR) _ _ SA0); lia]. }
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (pj_str1 E (g_q G) (g_ff G) (g_OS G + 128) i (tval (ae_T E i)) l gp ra a0 a1 a2 a3 a4 a5 a6 a7 s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6 F fc m
                             OK IR TIR KT eq_refl SA QLO QH OR AI SHZT SHZS FO MI)|].
  cbv beta. intros ms1 (a3x & a4x & ->). apply evt_done. unfold pjR.
  eapply (p_put_live RT AF PMc FDO MST G GOK _ k Σ K (tval (ae_T E i)) l); [exact PUT| exact GI| exact AI0| exact SA| clear - KB KX; lia|].
  intros Σ2 u0 u1 u2 e1 e2 e3 e4 e5 e6 e7 u3 u4 u5 u6 F2 m2 GI2. rewrite (ret_pc_even (pj_endl_pc 3)) by (cbn [pj_endl_pc]; lia).
  eapply (p_endl RT AF PMc FDO MST G 3 _ (k + 2) Σ2 K); [exact GOK| exact PUT| exact GI2| lia| clear - KB KX; lia|].
  intros Σ3 b0 b1 b2 b3 b4 b5 b6 b7 v0 v1 v2 v3 v4 v5 v6 F3 m3 GI3.
  eapply HK; [exact GI3| clear - KB; lia| exact FRM].
Qed.
End Cases.
