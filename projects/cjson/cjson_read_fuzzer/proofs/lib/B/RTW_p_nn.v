(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Arr Bytes ITree Nodes SysStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import Spin SRealizes LMeasure LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.LStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LSCPS LSCPS2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LRz.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LRz.LNodes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Exit_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import BImg RT_defs RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_wf RT_rep CJ_iface RT_art RT_kit RT_fp RT_artF.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_cost.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_cost.RT_artG.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_fp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp.RT_artB.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_front.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_common_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import Drv_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_kit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit.RT_shlem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_malloc_leaves_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_leaves_memset.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_leaves_memset.RTW_leaves_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RTW_depot_n2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_leaves_memset.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_leaves_memset.RTW_depot_mmap.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import AShadow ICPT_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_poison8.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_poison8.RT_poison_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_poison8.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_poison8.RT_poison3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_sec_mmapN.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_mmapN.RTW_sec_mmap.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_q_drainw.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_drainw.RTW_m_leaves2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_p_abs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_p_abs.RTW_m_lib3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RTW_kit RTW_p_map.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_p_pop1.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_p_pop1.RTW_p_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RTW_p_loops.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_p_pop1.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_p_pop1.RTW_p_efa.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RTW_p_pop1.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_p_finx.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_p_finx.RTW_p_pop2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_p_pop1.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_p_pop1.RTW_p_gfa.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_p_pop1.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_p_pop1.RTW_p_refillw.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RTW_p_zone RTW_p_abs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_cd_main.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_cd_main.RTW_p_absf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_m_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RTW_m_pop RTW_m_tpz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_sec_lib.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_lib.RTW_sec_alloc5.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_cost RTW_primary_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_sec.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_sec.RTW_q_needs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_p_finx.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_p_finx.RTW_p_refillA.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RTW_p_refill RTW_nn_specs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.ABand.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_bandtac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_bandtac2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_bandtac3 RT_bandtac4.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_p_pop1.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_p_pop1.RTW_p_libo.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_kitL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

(* [comment removed for export] *)
Local Ltac djlr := first [left; lia | right; lia | lia].

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.


Theorem refill_nn_proof : refill_nn_stmt.
Proof.
  unfold refill_nn_stmt, refill_room.
  intros ra sp gp tp x5 x6 x7 s0 s1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 F fc m mo g st0 cls lo.
  intros HRTS Hc HC0 -> -> -> -> TP HPV HPRE ST HCE LO2 MI.
  destruct g as [G R]. cbn [g_res] in HPV. destruct HRTS as (HR & WF & HM & HG & HFR & HSW).
  destruct st0 as [z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 y1 y2 y3 y4 y5].
  set (st := mkRT z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 y1 y2 y3 y4 y5) in *.
  assert (Hcls : 0 <= cls < KNUMCLASSES) by (unfold KNUMCLASSES; lia).
  set (r := rg st cls) in *. set (nf := num_freed st cls) in *. set (n := nrefill cls) in *. set (S := csize cls).
  set (alloc := r_allocated r). set (mapped := r_mapped r) in *. set (fam := r_mapped_fa r).
  set (pop := nf <? n). set (um := pop && (mapped <? alloc + S * (n - nf))).
  set (Nv := if pop then (mapped + (if um then 262144 else 0) - alloc) / S else 0).
  set (fm := pop && (fam <? 4 * (nf + Nv))). set (nm := (4 * (nf + Nv) + 262143) / 262144 * 262144).
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. pose proof HCE as HCEn. idtac. unfold AREFILL_STACK in LO2.
  destruct (refill_cells st m cls HR WF Hc HC0) as (jr & je & js & _ & _ & _ & _ & _ & _ & _ & _ & _ & RIb & _). fold r alloc mapped in RIb.
  assert (NAV : navail st cls = nf) by (unfold navail, avail_cptrs; fold r; rewrite HC0, app_nil_r; reflexivity).
  pose proof (nrefill_eq cls ltac:(lia)) as [_ NR]. fold n in NR.
  pose proof (wf_class_ok st WF cls Hcls) as WC.
  pose proof (wc_alloc_mapped st cls WC) as AM. pose proof (wc_fa_nonneg st cls WC) as FA0. pose proof (wc_fa_align st cls WC) as FAL. pose proof (wc_num_freed st cls WC) as NFF. pose proof (wc_residue st cls WC) as RES.
  fold r in AM, FA0, FAL, NFF, RES. fold alloc mapped in AM. fold fam in FA0, FAL, NFF. fold alloc mapped in RES. unfold num_freed in NFF. fold r nf in NFF. change (zlen (r_fa r)) with nf in NFF.
  pose proof (csize_pos cls ltac:(lia)) as CP. fold S in CP.
  assert (G8 : 0 <= nf) by (unfold nf, num_freed; apply zlen_nonneg).
  (* [comment removed for export] *)
  assert (FAM0 : fm = true -> fam = 0 /\ nm = 262144).
  { intros Efm. unfold fm in Efm. apply andb_true_iff in Efm as [Ep Ef]. apply Z.ltb_lt in Ef.
    assert (NVB : Nv <= 16385).
    { unfold Nv. rewrite Ep. apply Z.div_le_upper_bound; [lia|]. assert (32 * 16384 <= S * 16384) by (apply Z.mul_le_mono_nonneg_r; lia). destruct um; lia. }
    unfold pop in Ep. apply Z.ltb_lt in Ep.
    assert (fam = 0) by (clear -Ef FAL FA0 NVB G8 Ep NR; Z.div_mod_to_equations; nia). split; [exact H|]. unfold nm. clear -NVB G8 Ep NR H Ef. Z.div_mod_to_equations. nia. }
  assert (HRR : (if um then LUMP else 0) + (if fm then LUMP else 0) <= R).
  { pose proof (prov_cls_le st cls WF Hc) as PC.
    assert (PU : um = true -> LUMP <= provU st cls).
    { intros Eum. unfold um in Eum. apply andb_true_iff in Eum as [Ep Eu]. unfold pop in Ep. apply Z.ltb_lt in Ep. apply Z.ltb_lt in Eu.
      unfold LUMP. apply (lumpU_ok st cls WF Hc HC0); [exact Ep| exact Eu]. }
    assert (PF : fm = true -> LUMP <= provF st cls) by (intros Efm; destruct (FAM0 Efm) as [FZ _]; unfold LUMP; apply (lumpF_ok st cls WF Hc); exact FZ).
    pose proof (prov_classes_nonneg st). assert (0 <= provU st cls /\ 0 <= provF st cls) by (unfold provU, provF; lia).
    destruct um; destruct fm; try specialize (PU eq_refl); try specialize (PF eq_refl); lia. }
  apply lscps_assume. intros NWX HOK HBINV.
  eapply (refill_walk ra sp gp tp x5 x6 x7 s0 s1 xa4 xa5 xa6 xa7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 F fc m mo G R st cls lo
            HR WF HM HG Hc HC0 TP MI ST ltac:(split; [exact HCE| unfold AREFILL_STACK; clear -LO2; lia]) pop um fm false _ jr je js RIb eq_refl eq_refl eq_refl HRR).
  - (* [comment removed for export] *)
    intros Ep Eu _ EM. exfalso. unfold pop in Ep. apply Z.ltb_lt in Ep. rewrite NAV in HPRE. specialize (HPRE Ep). subst mapped r. unfold KFREEARRAY_OFF in *. clear -HPRE EM. lia.
  - intros Ep Eu _ EM. exfalso. unfold pop in Ep. apply Z.ltb_lt in Ep. rewrite NAV in HPRE. specialize (HPRE Ep). subst mapped r. unfold KFREEARRAY_OFF in *. clear -HPRE EM. lia.
  - (* [comment removed for export] *) exact I.
  - (* [comment removed for export] *) exact I.
  - (* [comment removed for export] *)
    intros NEX w5 w6 w7 w11 w12 w13 w14 w15 w16 w17 w28 w29 w30 w31 m' js' fa MI' MU' WM' ST' RIa' RI24' RIb' VFA' FILL' VU' VF' FL FN CHU' PCH' PCO'.
    apply lscps_done. unfold refill2_post, rt_post_std.
    exists w5, w6, w7, (wz 1), w11, w12, w13, w14, w15, w16, w17, w28, w29, w30, w31, m'.
    eexists (mkRT z1 z2 z3 (updz z4 cls (r_new z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 y1 y2 y3 y4 y5 cls n Nv nm um fm pop)) true
                   (updz z6 cls (skipn (Z.to_nat (nf + Nv - n)) (r_fa r ++ newc cls (ncarved st cls) Nv))) z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 y1 y2 y3 y4 y5).
    pose proof (csize_le64k' cls Hc) as CL. fold S in CL. pose proof (slack_ok' cls Hc) as (SL & _ & _). fold n S in SL.
    assert (SQ : S * (n - nf) <= 262144).
    { assert (S * (n - nf) <= S * n) by (apply Z.mul_le_mono_nonneg_l; clear -CP NR G8; lia). clear -H CL SL CP NR. nia. }
    assert (NvQ : pop = true -> n - nf <= Nv).
    { intros Ep. unfold Nv. rewrite Ep. apply Z.div_le_lower_bound; [clear -CP; lia|]. unfold um. rewrite Ep. cbn [andb].
      destruct (Z.ltb_spec0 mapped (alloc + S * (n - nf))) as [LTm|GEm]; [clear -SQ AM LTm| clear -SQ AM GEm]; lia. }
    assert (HNv : 0 <= Nv /\ n <= nf + Nv).
    { unfold Nv in *. destruct pop eqn:Ep.
      - split; [apply Z.div_pos; [destruct um; lia| lia]| specialize (NvQ eq_refl); rewrite Ep in NvQ || idtac; lia].
      - unfold pop in Ep. apply Z.ltb_ge in Ep. lia. }
    assert (HPOP : pop = true -> nf < n /\ Nv = (r_mapped r + (if um then 262144 else 0) - r_allocated r) / S
        /\ um = (r_mapped r <? r_allocated r + (n - nf) * S) /\ (um = true -> r_mapped r + 262144 <= KFREEARRAY_OFF)
        /\ fm = (r_mapped_fa r <? 4 * (nf + Nv)) /\ nm = (4 * (nf + Nv) + 262143) / 262144 * 262144).
    { intros Ep. split; [unfold pop in Ep; apply Z.ltb_lt in Ep; exact Ep|]. split; [unfold Nv; rewrite Ep; reflexivity|].
      split; [unfold um; rewrite Ep; cbn [andb]; fold alloc mapped; rewrite (Z.mul_comm (n - nf) S); reflexivity|].
      split; [exact NEX|]. split; [unfold fm; rewrite Ep; reflexivity| reflexivity]. }
    assert (HHAVE : pop = false -> Nv = 0 /\ um = false /\ fm = false) by (intros Ep; unfold fm, Nv, um; rewrite Ep; cbn [andb]; repeat split; reflexivity).
    assert (NVB : Nv <= 16385).
    { unfold Nv. destruct pop; [| lia]. apply Z.div_le_upper_bound; [lia|]. assert (32 * 16384 <= S * 16384) by (apply Z.mul_le_mono_nonneg_r; lia). destruct um; lia. }
    pose proof (conj FL FN) as Hfa. clear FL FN RIb.
    split; [reflexivity|]. split; [exact MI'|]. split; [reflexivity|].
    split; [eapply rel_fins; (first [eassumption| exact I| idtac]); unfold CEIL; lia|].
    split; [eapply RTS_fins; (first [eassumption| exact I| idtac]); unfold CEIL; lia|].
    split; [exact ST'|].
    split; [eapply (cli_pres_fins z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 y1 y2 y3 y4 y5 cls) with (um := um); (first [eassumption| exact I| idtac]); unfold CEIL; lia|].
    split; [eapply rt_frame_fins'; (first [eassumption| exact I| idtac]); unfold CEIL; lia|].
    split; [eapply gmono_fins with (lo := lo) (SP := bv_unsigned sp); (first [eassumption| exact I| idtac]); unfold CEIL; lia|].
    eapply budget_fins; (first [eassumption| exact I| idtac]); unfold CEIL; lia.
Qed.

End CeilWrap.
