(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import PropExec ShapeAlg AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import CertRefl CxRel CxPlan CxPlanSound CxGlue CxBatch.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import HUPlanImage HUAtable H0Sinv HUCheckG HUChain HUChain2 HUHop HUBatch HUFam.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import HUBatch2 UK0BS0 UK0MBDe21 UK0MBe21_bAll.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import CAP. Import CXS.
Open Scope Z_scope.
Lemma bA0 : (let it := APC.mk_itab_ranges HSEGS K0B_ranges in hbatch_ok LIM 100000 400 it (map jA0 a0s)) = true.
Proof. exact (proj1 (hbatch_app LIM 100000 400 K0B_ranges _ _ bAll)). Qed.
Lemma bRest_1 : (let it := APC.mk_itab_ranges HSEGS K0B_ranges in hbatch_ok LIM 100000 400 it ((map jB ops) ++ (map jC2 (flat_map od_holes ops)) ++ (map jA1 leaves_0) ++ (map jC1 (list_prod leaves_0 (classes TCs))))) = true.
Proof. exact (proj2 (hbatch_app LIM 100000 400 K0B_ranges _ _ bAll)). Qed.
Lemma bB : (let it := APC.mk_itab_ranges HSEGS K0B_ranges in hbatch_ok LIM 100000 400 it (map jB ops)) = true.
Proof. exact (proj1 (hbatch_app LIM 100000 400 K0B_ranges _ _ bRest_1)). Qed.
Lemma bRest_2 : (let it := APC.mk_itab_ranges HSEGS K0B_ranges in hbatch_ok LIM 100000 400 it ((map jC2 (flat_map od_holes ops)) ++ (map jA1 leaves_0) ++ (map jC1 (list_prod leaves_0 (classes TCs))))) = true.
Proof. exact (proj2 (hbatch_app LIM 100000 400 K0B_ranges _ _ bRest_1)). Qed.
Lemma bC2 : (let it := APC.mk_itab_ranges HSEGS K0B_ranges in hbatch_ok LIM 100000 400 it (map jC2 (flat_map od_holes ops))) = true.
Proof. exact (proj1 (hbatch_app LIM 100000 400 K0B_ranges _ _ bRest_2)). Qed.
Lemma bRest_3 : (let it := APC.mk_itab_ranges HSEGS K0B_ranges in hbatch_ok LIM 100000 400 it ((map jA1 leaves_0) ++ (map jC1 (list_prod leaves_0 (classes TCs))))) = true.
Proof. exact (proj2 (hbatch_app LIM 100000 400 K0B_ranges _ _ bRest_2)). Qed.
Lemma bA1_0 : (let it := APC.mk_itab_ranges HSEGS K0B_ranges in hbatch_ok LIM 100000 400 it (map jA1 leaves_0)) = true.
Proof. exact (proj1 (hbatch_app LIM 100000 400 K0B_ranges _ _ bRest_3)). Qed.
Lemma bRest_4 : (let it := APC.mk_itab_ranges HSEGS K0B_ranges in hbatch_ok LIM 100000 400 it ((map jC1 (list_prod leaves_0 (classes TCs))))) = true.
Proof. exact (proj2 (hbatch_app LIM 100000 400 K0B_ranges _ _ bRest_3)). Qed.
Lemma bC1_0 : (let it := APC.mk_itab_ranges HSEGS K0B_ranges in hbatch_ok LIM 100000 400 it (map jC1 (list_prod leaves_0 (classes TCs)))) = true.
Proof. exact bRest_4. Qed.
Lemma allA0 : allok LIM 100000 400 K0B_ranges _ jA0 a0s.
Proof. exact (hbatch_map LIM 100000 400 _ jA0 K0B_ranges a0s bA0). Qed.
Lemma allB : allok LIM 100000 400 K0B_ranges _ jB ops.
Proof. exact (hbatch_map LIM 100000 400 _ jB K0B_ranges ops bB). Qed.
Lemma allC2 : allok LIM 100000 400 K0B_ranges _ jC2 (flat_map od_holes ops).
Proof. exact (hbatch_map LIM 100000 400 _ jC2 K0B_ranges _ bC2). Qed.
Lemma allA1_0 : allok LIM 100000 400 K0B_ranges _ jA1 leaves_0.
Proof. exact (hbatch_map LIM 100000 400 _ jA1 K0B_ranges _ bA1_0). Qed.
Lemma allC1_0 : allok LIM 100000 400 K0B_ranges _ jC1 (list_prod leaves_0 (classes TCs)).
Proof. exact (hbatch_map LIM 100000 400 _ jC1 K0B_ranges _ bC1_0). Qed.
Lemma allA1 : allok LIM 100000 400 K0B_ranges _ jA1 leaves.
Proof. exact allA1_0. Qed.
Lemma allC1 : allok LIM 100000 400 K0B_ranges _ jC1 (list_prod leaves (classes TCs)).
Proof. exact allC1_0. Qed.
Lemma SIDE : side_ok N0 78 200 1100 1300 68 110 1000 1200 K0B_cs TA1 TB TCs TDs a0s leaves ops shapeB sC2s = true.
Proof. vm_compute. reflexivity. Qed.
Section G.
  Variables (sp : word) (STR0 : Z) (fs : Fs.Fs).
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hstr : bv_unsigned sp + 192 <= STR0 < 2 ^ 47 - 32.
  Hypothesis Hstr8 : STR0 mod 8 = 0.
  Definition grp_sound := fam_sound sp STR0 LIM fs Hsp Hstr Hstr8 100000 400 K0B_ranges N0 78 200 1100 1300 68 110 1000 1200 K0B_cs TA1 TB TCs TDs a0s leaves ops shapeB sC2s
    allA0 allA1 allB allC1 allC2 SIDE.
End G.
Check grp_sound.
