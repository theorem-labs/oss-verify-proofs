(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface RT_iface2 RT_iface3 Pj_rtkA Pj_defsA Pj_cpsA Pj_ser_defsA Pj_ser_numdefsA
     Pj_ser_strA Pj_ser_keyA Pj_ser_atomA Pj_ser_intA Pj_ser_ncallsA Pj_ser_dblA Pj_ser_itoaA Pj_ser_utoaA Pj_ser_topA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section Arms.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Hypothesis RC2 : rt_contracts2 RT.
Hypothesis SM3W : stack_malloc3w_contract RT.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.
Hypothesis GROW : grow_cpsA RT PMc.
Hypothesis TOCHARS : tochars_cpsA RT PMc.

Theorem ser_of_rec_armsA : forall D, rec_okA RT PMc D -> ser_cpsA RT PMc D.
Proof using AF RC RC2 SM3W FDO MST GROW TOCHARS.
  exact (ser_of_recA RT AF RC SM3W PMc GROW
           (str_okA RT AF RC PMc FDO MST GROW)
           (i64_okA RT AF RC PMc FDO MST GROW (itoa_okA RT AF RC RC2 PMc FDO MST))
           (u64_okA RT AF RC PMc FDO MST GROW (utoa_okA RT AF RC RC2 PMc FDO MST))
           (dbl_okA RT AF RC PMc FDO MST GROW TOCHARS)
           (true_okA RT AF RC PMc FDO MST GROW)
           (false_okA RT AF RC PMc FDO MST GROW)
           (null_okA RT AF RC PMc FDO MST GROW)
           (key_okA RT AF RC PMc FDO MST GROW)).
Qed.
End Arms.
