(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import PropExec ShapeAlg AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import CertRefl CxRel CxPlan CxPlanSound CxGlue CxBatch.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import H0PlanImage H0Atable H0Sinv H0CheckG H0Chain H0Chain2 H0Hop H0Batch H0Fam.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import H0Batch2 H0Fam2 R2BS0 R2BCDc0 R2BCc0_bA0 R2BCc0_bB R2BCc0_bC2 R2BCc0_bA1_0 R2BCc0_bC1_0 R2BCc0_bA1_1 R2BCc0_bC1_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import CAP. Import CXS.
Open Scope Z_scope.
Lemma allA0 : allok LIM 100000 400 R2B_ranges _ jA0 a0s.
Proof. exact (hbatch_map LIM 100000 400 _ jA0 R2B_ranges a0s bA0). Qed.
Lemma allB : allok LIM 100000 400 R2B_ranges _ jB ops.
Proof. exact (hbatch_map LIM 100000 400 _ jB R2B_ranges ops bB). Qed.
Lemma allC2 : allok LIM 100000 400 R2B_ranges _ jC2 (flat_map od_holes ops).
Proof. exact (hbatch_map LIM 100000 400 _ jC2 R2B_ranges _ bC2). Qed.
Lemma allA1_0 : allok LIM 100000 400 R2B_ranges _ jA1 leaves2_0.
Proof. exact (hbatch_map LIM 100000 400 _ jA1 R2B_ranges _ bA1_0). Qed.
Lemma allC1_0 : allok LIM 100000 400 R2B_ranges _ jC1 (list_prod (arms leaves2_0) (classes TCs)).
Proof. exact (hbatch_map LIM 100000 400 _ jC1 R2B_ranges _ bC1_0). Qed.
Lemma allA1_1 : allok LIM 100000 400 R2B_ranges _ jA1 leaves2_1.
Proof. exact (hbatch_map LIM 100000 400 _ jA1 R2B_ranges _ bA1_1). Qed.
Lemma allC1_1 : allok LIM 100000 400 R2B_ranges _ jC1 (list_prod (arms leaves2_1) (classes TCs)).
Proof. exact (hbatch_map LIM 100000 400 _ jC1 R2B_ranges _ bC1_1). Qed.
Lemma allA1 : allok LIM 100000 400 R2B_ranges _ jA1 leaves2.
Proof. exact (allok_app LIM 100000 400 R2B_ranges _ jA1 _ _ allA1_0 allA1_1). Qed.
Lemma allC1 : allok LIM 100000 400 R2B_ranges _ jC1 (list_prod (arms leaves2) (classes TCs)).
Proof. unfold leaves2, arms. rewrite ?flat_map_app. exact (allok_prod_app LIM 100000 400 R2B_ranges _ _ jC1 _ _ (classes TCs) allC1_0 allC1_1). Qed.
Lemma SIDE : side_ok N0 74 200 1100 1300 64 110 1000 1200 R2B_cs TA1 TB TCs TDs a0s (arms leaves2) ops shapeB sC2s = true.
Proof. vm_compute. reflexivity. Qed.
Section G.
  Variables (sp : word) (STR0 : Z) (fs : Fs.Fs).
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hstr : bv_unsigned sp + 192 <= STR0 < 2 ^ 47 - 32.
  Hypothesis Hstr8 : STR0 mod 8 = 0.
  Definition grp_sound := fam_sound2_view sp STR0 LIM fs Hsp Hstr Hstr8 100000 400 R2B_ranges N0 74 200 1100 1300 64 110 1000 1200 R2B_cs TA1 TB TCs TDs a0s leaves2 ops shapeB sC2s
    allA0 allA1 allB allC1 allC2 SIDE.
End G.
Check grp_sound.
