(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface RT_iface2 RT_iface3 RT_iface4 Pj_rtkA Pj_defsA Pj_cpsA Pj_ser_defsA Pj_ser_objkA
     Pj_ser_armsA Pj_ser_arrA Pj_ser_objA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section Closed.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Hypothesis RC2 : rt_contracts2 RT.
Hypothesis SM3W : stack_malloc3w_contract RT.
Hypothesis SM1Z : stack_malloc1z_contract RT.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.
Hypothesis GROW : grow_cpsA RT PMc.
Hypothesis TOCHARS : tochars_cpsA RT PMc.
Hypothesis OKEY1 : okey1_stmtA RT PMc.
Hypothesis OKEY2 : okey2_stmtA RT PMc.

Lemma cont_of_serA : forall d, ser_cpsA RT PMc d -> forall k, cont_cpsA RT PMc k d.
Proof using AF SM1Z GROW OKEY1 OKEY2.
  intros d SER [|]; [exact (obj_proofA RT AF SM1Z PMc GROW OKEY1 OKEY2 d SER)| exact (arr_proofA RT AF PMc GROW d SER)].
Qed.

Theorem ser_closedA : forall d, ser_cpsA RT PMc d.
Proof using AF RC RC2 SM3W SM1Z FDO MST GROW TOCHARS OKEY1 OKEY2.
  intros d. induction d as [d IH] using (well_founded_induction Wf_nat.lt_wf).
  apply (ser_of_rec_armsA RT AF RC RC2 SM3W PMc FDO MST GROW TOCHARS). intros k d' Hd'.
  apply cont_of_serA. apply IH. lia.
Qed.

Corollary cont_closedA : forall k d, cont_cpsA RT PMc k d.
Proof using AF RC RC2 SM3W SM1Z FDO MST GROW TOCHARS OKEY1 OKEY2. intros k d. apply cont_of_serA, ser_closedA. Qed.
End Closed.
