(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim StrFun.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface5. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_num_akit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Pj_rtkA El_sncA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section Snc2.
Variable RT : rt_sig.

Lemma sncW_of_icontractB : strncasecmp_icontract RT -> sncW_stmt RT.
Proof.
  intros SC Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p q n bp bq lo
    FDO MST E0 E1 E2 HP HQ HN BP BQ FP FQ LP LQ CP CQ HA MI COK.
  set (k := Z.min n (Z.of_nat (scase_idx bp bq (Z.to_nat n)) + 1)).
  assert (K : 0 < k <= n) by (subst k; lia).
  eapply cps_conseq; [eapply (SC Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p q n bp bq lo
      FDO MST E0 E1 E2 HP HQ ltac:(lia) BP BQ FP FQ); [subst k; lia| subst k; lia| exact (checked_src_shrink _ _ _ _ _ _ _ _ CP K)| exact (checked_src_shrink _ _ _ _ _ _ _ _ CQ K)
      | exact HA| exact MI| exact COK]| intros c Hc; exact Hc|].
  intros c Hc. first [destruct Hc as (r & _ & H); exists r; exact H | eexists; exact Hc].
Qed.

Lemma snc0_of_icontract0B : strncasecmp0_icontract RT -> snc0_stmt RT.
Proof.
  intros SC Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo FDO MST E2 HA MI COK.
  eapply cps_conseq; [eapply (SC Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo FDO MST E2 HA MI COK)
    | intros c Hc; exact Hc|].
  intros c Hc. first [eexists; exact Hc| destruct Hc as (r & H); exists r; exact H].
Qed.
End Snc2.
