(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import PropExec ShapeAlg AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import CertRefl CxRel CxPlan CxPlanSound CxGlue CxBatch.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import HUPlanImage HUAtable H0Sinv HUCheckG HUChain HUChain2 HUHop HUBatch HUFam.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import HUBatch2 HUFam2 UK0AS0 UK0ACDc2 UK0ACc2_bA0 UK0ACc2_bB UK0ACc2_bC2 UK0ACc2_bA1_0 UK0ACc2_bC1_0 UK0ACc2_bA1_1 UK0ACc2_bC1_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import CAP. Import CXS.
Open Scope Z_scope.
Lemma allA0 : allok LIM 100000 400 K0A_ranges _ jA0 a0s.
Proof. exact (hbatch_map LIM 100000 400 _ jA0 K0A_ranges a0s bA0). Qed.
Lemma allB : allok LIM 100000 400 K0A_ranges _ jB ops.
Proof. exact (hbatch_map LIM 100000 400 _ jB K0A_ranges ops bB). Qed.
Lemma allC2 : allok LIM 100000 400 K0A_ranges _ jC2 (flat_map od_holes ops).
Proof. exact (hbatch_map LIM 100000 400 _ jC2 K0A_ranges _ bC2). Qed.
Lemma allA1_0 : allok LIM 100000 400 K0A_ranges _ jA1 leaves2_0.
Proof. exact (hbatch_map LIM 100000 400 _ jA1 K0A_ranges _ bA1_0). Qed.
Lemma allC1_0 : allok LIM 100000 400 K0A_ranges _ jC1 (list_prod (arms leaves2_0) (classes TCs)).
Proof. exact (hbatch_map LIM 100000 400 _ jC1 K0A_ranges _ bC1_0). Qed.
Lemma allA1_1 : allok LIM 100000 400 K0A_ranges _ jA1 leaves2_1.
Proof. exact (hbatch_map LIM 100000 400 _ jA1 K0A_ranges _ bA1_1). Qed.
Lemma allC1_1 : allok LIM 100000 400 K0A_ranges _ jC1 (list_prod (arms leaves2_1) (classes TCs)).
Proof. exact (hbatch_map LIM 100000 400 _ jC1 K0A_ranges _ bC1_1). Qed.
Lemma allA1 : allok LIM 100000 400 K0A_ranges _ jA1 leaves2.
Proof. exact (allok_app LIM 100000 400 K0A_ranges _ jA1 _ _ allA1_0 allA1_1). Qed.
Lemma allC1 : allok LIM 100000 400 K0A_ranges _ jC1 (list_prod (arms leaves2) (classes TCs)).
Proof. unfold leaves2, arms. rewrite ?flat_map_app. exact (allok_prod_app LIM 100000 400 K0A_ranges _ _ jC1 _ _ (classes TCs) allC1_0 allC1_1). Qed.
Lemma SIDE : side_ok N0 78 200 1100 1300 68 110 1000 1200 K0A_cs TA1 TB TCs TDs a0s (arms leaves2) ops shapeB sC2s = true.
Proof. vm_compute. reflexivity. Qed.
Section G.
  Variables (sp : word) (STR0 : Z) (fs : Fs.Fs).
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hstr : bv_unsigned sp + 192 <= STR0 < 2 ^ 47 - 32.
  Hypothesis Hstr8 : STR0 mod 8 = 0.
  Definition grp_sound := fam_sound2_view sp STR0 LIM fs Hsp Hstr Hstr8 100000 400 K0A_ranges N0 78 200 1100 1300 68 110 1000 1200 K0A_cs TA1 TB TCs TDs a0s leaves2 ops shapeB sC2s
    allA0 allA1 allB allC1 allC2 SIDE.
End G.
Check grp_sound.
