From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import State.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CfgGlue CursorGlue.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Init.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L7 Require Import S_r2 r2_cuts.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.
Import ListNotations.
Import R2C.
Open Scope Z_scope.

Lemma check_r2 : check_cfg segsU FUEL_r2 cutpcs_r2 NF cuts_r2 exits_r2 = true.
Proof. apply OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.check_cfg_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma cuts_r2_strict : existsb ss_lenient cuts_r2 = false.
Proof. reflexivity. Qed.

Theorem r2_sum : r2_sum_stmt_U.
Proof.
  intros ok K rho Hok.
  apply (cfg_sound segsU FUEL_r2 cutpcs_r2 NF cuts_r2 exits_r2
           (fun rho' => agree_below NF rho rho') ok K (LQ segsU K NF rho Posts_r2U) Hok).
  - rewrite cuts_r2_strict. intros; discriminate.
  - intros r1 r2 H1 H2. eapply agree_below_trans; eauto.
  - exact check_r2.
  - intros E rhoE HinE HagE.
    destruct HinE as [<-|[]]; revert HagE; apply exit_post.
    in_nth 0.
  - left; reflexivity.
  - apply agree_below_refl.
Qed.
