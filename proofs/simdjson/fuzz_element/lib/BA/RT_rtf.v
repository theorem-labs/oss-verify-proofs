(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface D_defs D_libiface Sj_rtf.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section RTF.
Variable RT : rt_sig.

Lemma rsF_w : forall {fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms},
  ret_stF fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms -> ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms.
Proof. intros until ms. intros H. exact (proj1 (ret_stF_weak fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms H)). Qed.
Lemma rsF_fc : forall {fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms},
  ret_stF fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms -> ms_fcsr ms = fc.
Proof. intros until ms. intros H. exact (proj2 (ret_stF_weak fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms H)). Qed.

Lemma cps_f_of_strong : forall Σ PMc ms (QF Q : config -> Prop),
  cps asegs (ASTA RT Σ PMc (eq ms)) QF ->
  (forall c, QF c -> frm0 (ms_fcsr ms) -> Q c /\ cfrm0 c) ->
  cps_f (ASTA RT Σ PMc (eq ms)) Q.
Proof.
  intros Σ PMc ms QF Q H HW T c (Hc & FC) Hk. apply (H T c Hc). intros c' Hc'. apply Hk. apply (HW c' Hc').
  unfold cfrm0 in FC. rewrite (asta_eq_fcsr RT Σ PMc ms c Hc) in FC. exact FC.
Qed.

Lemma asta_F_weak : forall Σ PMc fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (V : word -> Prop) (R : word -> mem -> Prop) c,
  ASTA RT Σ PMc (fun ms => exists v m', V v /\ ret_stF fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms /\ R v m') c -> frm0 fc ->
  ASTA RT Σ PMc (fun ms => exists v m', V v /\ ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms /\ R v m') c /\ cfrm0 c.
Proof.
  intros until c. intros H F0. split.
  - eapply (ASTA_conseq RT); [exact H|]. intros ms (v & m' & HV & RS & HR). exists v, m'. split; [exact HV|]. split; [|exact HR].
    exact (rsF_w RS).
  - apply (asta_cfrm0 RT Σ PMc _ c H). intros ms (v & m' & _ & RS & _). rewrite (rsF_fc RS). exact F0.
Qed.

Lemma icpt_postF_weak : forall fc Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v lo d n m Q c,
  icpt_postF fc RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v lo d n m Q c -> frm0 fc ->
  icpt_post RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v lo d n m Q c /\ cfrm0 c.
Proof.
  intros until c. intros H F0. unfold icpt_postF, icpt_post in *. split.
  - eapply (ASTA_conseq RT); [exact H|]. intros ms (m' & RS & X). exists m'. split; [|exact X].
    exact (rsF_w RS).
  - apply (asta_cfrm0 RT Σ PMc _ c H). intros ms (m' & RS & _). rewrite (rsF_fc RS). exact F0.
Qed.

Lemma asta_m_weak : forall Σ PMc fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v (X : mem -> Prop) c,
  ASTA RT Σ PMc (fun ms => exists m', ret_stF fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms /\ X m') c -> frm0 fc ->
  ASTA RT Σ PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms /\ X m') c /\ cfrm0 c.
Proof.
  intros until c. intros H F0. split.
  - eapply (ASTA_conseq RT); [exact H|]. intros ms (m' & RS & HX). exists m'. split; [|exact HX].
    exact (rsF_w RS).
  - apply (asta_cfrm0 RT Σ PMc _ c H). intros ms (m' & RS & _). rewrite (rsF_fc RS). exact F0.
Qed.

Local Ltac fc_red := cbn [ms_fcsr entry_st]; unfold entry_st; cbn [ms_fcsr].

Lemma sm_f : forall k, stack_malloc_contract RT k -> stack_malloc_contract_f RT k.
Proof.
  intros k SM Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.
  eapply cps_f_of_strong; [exact (SM Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo H1 H2 H3 H4 H5 H6 H7 H8 H9 H10)|].
  intros c (Σ' & f & HA & REST) F0. change (frm0 fc) in F0.
  destruct (asta_m_weak Σ' PMc fc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ c HA F0) as (HW & FCc).
  split; [exists Σ', f; split; [exact HW| exact REST] | exact FCc].
Qed.

Theorem rtf_of_rt : rt_contracts RT -> rt_contracts_f RT.
Proof.
  intros RC. constructor.
  -
    intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n lo
      H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11.
    eapply cps_f_of_strong; [exact (rc_malloc RT RC Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n lo H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11)|].
    intros c (Σ' & p & HA & REST) F0. change (frm0 fc) in F0.
    destruct (asta_m_weak Σ' PMc fc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ c HA F0) as (HW & FCc).
    split; [exists Σ', p; split; [exact HW| exact REST] | exact FCc].
  -
    intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p n lo
      H1 H2 H3 H4 H5 H6 H7 H8 H9.
    eapply cps_f_of_strong; [exact (rc_free RT RC Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p n lo H1 H2 H3 H4 H5 H6 H7 H8 H9)|].
    intros c (Σ' & v & HA & REST) F0. change (frm0 fc) in F0.
    destruct (asta_m_weak Σ' PMc fc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ c HA F0) as (HW & FCc).
    split; [exists Σ', v; split; [exact HW| exact REST] | exact FCc].
  -
    intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
      H1 H2 H3 H4 H5 H6 H7 H8.
    eapply cps_f_of_strong; [exact (rc_free_null RT RC Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo H1 H2 H3 H4 H5 H6 H7 H8)|].
    intros c (v & HA) F0. change (frm0 fc) in F0.
    destruct (icpt_postF_weak fc Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ c HA F0) as (HW & FCc).
    split; [exists v; exact HW | exact FCc].
  -
    intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d s bs lo
      H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15.
    eapply cps_f_of_strong; [exact (rc_asan_memcpy RT RC Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d s bs lo H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15)|].
    intros c HA F0. change (frm0 fc) in F0. exact (icpt_postF_weak fc Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ c HA F0).
  -
    intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d n cb lo
      H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11.
    eapply cps_f_of_strong; [exact (rc_asan_memset RT RC Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d n cb lo H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11)|].
    intros c HA F0. change (frm0 fc) in F0. exact (icpt_postF_weak fc Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ c HA F0).
  -
    intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d s bs lo
      H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14.
    eapply cps_f_of_strong; [exact (rc_asan_memmove RT RC Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d s bs lo H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14)|].
    intros c HA F0. change (frm0 fc) in F0. exact (icpt_postF_weak fc Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ c HA F0).
  -
    intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p q bp bq lo
      H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17.
    eapply cps_f_of_strong; [exact (rc_memcmp RT RC Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p q bp bq lo H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17)|].
    intros c (r & HR & HA) F0. change (frm0 fc) in F0.
    destruct (icpt_postF_weak fc Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ c HA F0) as (HW & FCc).
    split; [exists r; split; [exact HR| exact HW] | exact FCc].
  - exact (sm_f 0%nat (rc_stack_malloc_0 RT RC)).
  - exact (sm_f 4%nat (rc_stack_malloc_4 RT RC)).
  - exact (sm_f 5%nat (rc_stack_malloc_5 RT RC)).
  -
    intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m f fr lo
      H1 H2 H3 H4 H5 H6 H7 H8 H9.
    eapply cps_f_of_strong; [exact (rc_stack_free_5 RT RC Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m f fr lo H1 H2 H3 H4 H5 H6 H7 H8 H9)|].
    intros c (Σ' & v & HA & REST) F0. change (frm0 fc) in F0.
    destruct (asta_m_weak Σ' PMc fc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ c HA F0) as (HW & FCc).
    split; [exists Σ', v; split; [exact HW| exact REST] | exact FCc].
  -
    intros v Hv Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d n lo
      H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11.
    eapply cps_f_of_strong; [exact (rc_set_shadow RT RC v Hv Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d n lo H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11)|].
    intros c (v0 & HA) F0. change (frm0 fc) in F0.
    destruct (icpt_postF_weak fc Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ c HA F0) as (HW & FCc).
    split; [exists v0; exact HW | exact FCc].
Qed.

End RTF.
