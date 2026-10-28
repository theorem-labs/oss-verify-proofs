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
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface RT_iface2 RT_iface3 D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_num_akit Atp_fzwA Atp_defsA Atp_kitA Pj_rtkA Pj_defsA Pj_os_defsA El_defsA El_os_defsA El_ins_ifaceA Dmp_hdefsA Dmp_pj_ifaceA Dmp_insbA Dmp_pj_kitA Dmp_pj_leafA Dmp_pj_strA Dmp_pj_arrA Dmp_pj_objA Dmp_pj_aevtA Dmp_pj_entryA Dmp_pj_casesA Dmp_pj_loopsA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Lemma elem_casesA : forall T S sn d i j, elem T S sn ck_any d i j ->
  (j = i + 1 /\ (T i = tword t_true 0 \/ T i = tword t_false 0 \/ T i = tword t_null 0))
  \/ (j = i + 2 /\ (T i = tword t_i64 0 \/ T i = tword t_u64 0 \/ T i = tword t_dbl 0))
  \/ (j = i + 1 /\ is_str T S sn i)
  \/ (exists d' e c cv, d = Datatypes.S d' /\ j = e + 1 /\ 0 <= cv <= CNT_MAX /\
        ((T i = cword t_arr (e + 1) cv /\ T e = tword t_arr_end i /\ tiles (elem T S sn ck_any d') (i + 1) e c)
         \/ (T i = cword t_obj (e + 1) cv /\ T e = tword t_obj_end i /\ tiles (field T S sn (elem T S sn ck_any d')) (i + 1) e c))).
Proof.
  intros T S sn d i j EL.
  assert (SC : scalar T S sn i j -> (j = i + 1 /\ (T i = tword t_true 0 \/ T i = tword t_false 0 \/ T i = tword t_null 0))
    \/ (j = i + 2 /\ (T i = tword t_i64 0 \/ T i = tword t_u64 0 \/ T i = tword t_dbl 0)) \/ (j = i + 1 /\ is_str T S sn i)
    \/ (exists d' e c cv, d = Datatypes.S d' /\ j = e + 1 /\ 0 <= cv <= CNT_MAX /\
        ((T i = cword t_arr (e + 1) cv /\ T e = tword t_arr_end i /\ tiles (elem T S sn ck_any d') (i + 1) e c)
         \/ (T i = cword t_obj (e + 1) cv /\ T e = tword t_obj_end i /\ tiles (field T S sn (elem T S sn ck_any d')) (i + 1) e c)))).
  { intros [[-> H]|[[-> H]|[-> H]]]; [left; auto| right; left; auto| right; right; left; auto]. }
  destruct d as [|d']; cbn [elem] in EL.
  - destruct EL as [X|[]]. exact (SC X).
  - destruct EL as [X|CO]; [exact (SC X)|]. right; right; right.
    destruct CO as (e & c & cv & -> & CK & HC). unfold ck_any in CK. exists d', e, c, cv.
    split; [reflexivity|]. split; [reflexivity|]. split; [exact CK|]. exact HC.
Qed.

Section Level.
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

Lemma pj_levelA : forall d, (forall d', d = Datatypes.S d' -> Dmp_pj_ifaceA.pj_cpsA RT PMc d') -> Dmp_pj_ifaceA.pj_cpsA RT PMc d.
Proof using AF SM2 FDO MST PUT INSB INSL INSUL INSD.
  intros d IH. unfold Dmp_pj_ifaceA.pj_cpsA. intros until m.
  intros FDO' MST' OK EL I0 JN AL AI INF FLO FHI O16 DJ OXF HULL LB TPL IOS FRM HA MI ST NEED QT Q32 LEN CRB HK.
  pose proof (elem_lt _ _ _ _ _ _ _ EL) as IJ. pose proof (Atp_defsA.ok_wf E OK) as (NR & SNR & _).
  assert (CR1 : 1 <= rt_credit RT Σ) by (unfold pj_costE, DMP_PJ_CW in CRB; clear - CRB IJ; lia).
  eapply (p_enter RT AF SM2 PMc FDO MST d Σ K E OS q fO kO i j); [exact OK| exact EL| exact I0| exact JN| exact AL| exact AI| exact INF| exact FLO| exact FHI| exact O16| exact DJ
    | exact OXF| exact HULL| exact LB| exact TPL| exact HA| exact MI| exact ST| exact NEED| exact QT| exact Q32| exact LEN| exact CR1|].
  intros f Σ1 m2 jA jB jC t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' G GOK GI1.
  assert (GC : g_cr G = rt_credit RT Σ) by reflexivity. assert (GDd : g_d G = d) by reflexivity.
  assert (AI0 : AINV_A (g_E G) (g_m0 G)) by exact AI. assert (IOS0 : io_ssp (g_m0 G)) by exact IOS.

  assert (KX : forall LC, cells_size LC = 152%nat -> KEXITA RT PMc G (LC ++ pj_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) (pj_costE i j) K gp).
  { intros LC SZ. unfold KEXITA. intros Σ' m' rax b0 b1 b2 b3 b4 b5 b6 b7 x2 x4 x5 x6 x8 x9 x10 u0 u1 u2 u3 u4 u5 u6 F2 fc2 k' GI' LE FRM2.
    eapply (p_exit RT AF PMc FDO MST G LC k' Σ' K ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11); [exact GOK| exact GI'| exact SZ| exact AI0|].
    intros Σ'' v0 v1 v2 c0 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 F3 m'' HA'' MI'' ST'' OX'' HULL'' LB'' TPL'' AI'' LV'' FRS'' SP0'' CR'' REL''.
    eapply (HK Σ'' v0 v1 v2 c0 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 F3 fc2 m''); try eassumption. clear - CR'' LE GC. rewrite GC in CR''. lia. }
  destruct (elem_casesA _ _ _ _ _ _ EL) as [[-> TY]|[[-> TY]|[[-> STRI]|(d' & e & c & cv & Hd & -> & CV & CO)]]].
  -
    destruct TY as [TI|[TI|TI]].
    + eapply (pc_bool RT AF PMc FDO MST PUT INSB G GOK AI0 IOS0 jA jB jC _ 1 (pj_costE i (i + 1))); [exact GI1| exact FRM| change (g_E G) with E; clear - I0 JN; lia| left; exact TI
        | unfold pj_costE, DMP_PJ_CW; clear; lia| rewrite GC; exact CRB| exact KX].
    + eapply (pc_bool RT AF PMc FDO MST PUT INSB G GOK AI0 IOS0 jA jB jC _ 1 (pj_costE i (i + 1))); [exact GI1| exact FRM| change (g_E G) with E; clear - I0 JN; lia| right; exact TI
        | unfold pj_costE, DMP_PJ_CW; clear; lia| rewrite GC; exact CRB| exact KX].
    + eapply (pc_null RT AF PMc FDO MST PUT G GOK AI0 jA jB jC _ 1 (pj_costE i (i + 1))); [exact GI1| exact FRM| change (g_E G) with E; clear - I0 JN; lia| exact TI
        | unfold pj_costE, DMP_PJ_CW; clear; lia| rewrite GC; exact CRB| exact KX].
  -
    destruct TY as [TI|[TI|TI]].
    + eapply (pc_num RT AF PMc FDO MST PUT INSL INSUL G GOK AI0 IOS0 jA jB jC _ 1 (pj_costE i (i + 2))); [exact GI1| exact FRM| exact I0| change (g_E G) with E; clear - JN; lia| left; exact TI
        | unfold pj_costE, DMP_PJ_CW; clear; lia| rewrite GC; exact CRB| exact KX].
    + eapply (pc_num RT AF PMc FDO MST PUT INSL INSUL G GOK AI0 IOS0 jA jB jC _ 1 (pj_costE i (i + 2))); [exact GI1| exact FRM| exact I0| change (g_E G) with E; clear - JN; lia| right; exact TI
        | unfold pj_costE, DMP_PJ_CW; clear; lia| rewrite GC; exact CRB| exact KX].
    + eapply (pc_dbl RT AF PMc FDO MST PUT INSD G GOK AI0 IOS0 jA jB jC _ 1 (pj_costE i (i + 2))); [exact GI1| exact FRM| exact I0| change (g_E G) with E; clear - JN; lia| exact TI
        | unfold pj_costE, DMP_PJ_CW; clear; lia| rewrite GC; exact CRB| exact KX].
  -
    eapply (pc_str RT AF PMc FDO MST PUT G GOK AI0 jA jB jC _ 1 (pj_costE i (i + 1))); [exact GI1| exact FRM| change (g_E G) with E; clear - I0 JN; lia| exact STRI
      | unfold pj_costE, DMP_PJ_CW; clear; lia| rewrite GC; exact CRB| exact KX].
  -
    pose proof (IH d' Hd) as PJ'. rewrite <- GDd in Hd.
    assert (LT : i < e).
    { destruct CO as [(_ & _ & HT)|(_ & _ & HT)].
      - pose proof (tiles_le _ (elem_lt _ _ _ _ d') _ _ _ HT). lia.
      - pose proof (tiles_le _ (field_lt _ _ _ _ (elem_lt _ _ _ _ d')) _ _ _ HT). lia. }
    destruct CO as [(TI & TE & HT)|(TI & TE & HT)].
    + eapply (pj_arr_caseA RT AF PMc FDO MST PUT G GOK AI0 IOS0 d' Hd PJ' jA jB jC _ (pj_costE i (e + 1)) Σ1 K i e c cv);
        [exact GI1| exact FRM| exact I0| exact LT| exact JN| exact CV| exact TI| exact HT| clear; lia| rewrite GC; exact CRB| exact KX].
    + eapply (pj_obj_caseA RT AF PMc FDO MST PUT G GOK AI0 IOS0 d' Hd PJ' jA jB jC _ (pj_costE i (e + 1)) Σ1 K i e c cv);
        [exact GI1| exact FRM| exact I0| exact LT| exact JN| exact CV| exact TI| exact HT| clear; lia| rewrite GC; exact CRB| exact KX].
Qed.

Theorem pj_okA : forall d, Dmp_pj_ifaceA.pj_cpsA RT PMc d.
Proof using AF SM2 FDO MST PUT INSB INSL INSUL INSD.
  induction d as [|d IHd]; apply pj_levelA; intros d' Hd; [discriminate Hd| injection Hd as <-; exact IHd].
Qed.

Theorem pj_rootA : pj_root_cpsA RT PMc.
Proof using AF SM2 FDO MST PUT INSB INSL INSUL INSD. exact (pj_root_ofA RT PMc (pj_okA TAPE_MAX_DEPTH)). Qed.
End Level.
