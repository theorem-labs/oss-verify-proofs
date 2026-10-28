From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CfgGlue CursorGlue.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Init.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L5 Require Import S_bw.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import BwAddr.

Definition FUEL_bw : nat := 40%nat.
Definition cuts_bw : list sstate := [Pre_bw].
Definition exits_bw : list sstate := [P_bw].
Definition cutpcs_bw : list Z := [da_entry].

Lemma check_bw : check_cfg segsU FUEL_bw cutpcs_bw NF cuts_bw exits_bw = true.
Proof. apply SymCFGFast.check_cfg_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma cuts_bw_strict : existsb ss_lenient cuts_bw = false.
Proof. vm_compute. reflexivity. Qed.

Theorem bw_sum : bw_sum_stmt.
Proof.
  intros ok K rho Hok.
  apply (cfg_sound segsU FUEL_bw cutpcs_bw NF cuts_bw exits_bw
           (fun rho' => agree_below NF rho rho') ok K (LQ segsU K NF rho Posts_bw) Hok).
  - rewrite cuts_bw_strict. intros; discriminate.
  - intros r1 r2 H1 H2. eapply agree_below_trans; eauto.
  - exact check_bw.
  - intros E rhoE HinE HagE.
    destruct HinE as [<-|[]]; revert HagE.
    apply exit_post. in_nth 0.
  - left; reflexivity.
  - apply agree_below_refl.
Qed.

Definition vcuts_bw : list vnode := [mkVN Pre_bw 30 (SLit 0)].
Definition vexits_bw : list vnode := [mkVN P_bw 1 vTop].

Lemma echeck_bw : check_ecfgI segsU FUEL_bw cutpcs_bw NF vcuts_bw vexits_bw = true.
Proof. apply CfgFast.check_ecfgI_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.

Theorem bw_sum_ex : bw_sum_ex_stmt.
Proof.
  intros K rho.
  change Pre_bw with (vn_state (mkVN Pre_bw 30 (SLit 0))).
  apply (cfg_complete_autoI segsU FUEL_bw cutpcs_bw NF vcuts_bw vexits_bw
           (fun rho' => agree_below NF rho rho') K (LQ segsU K NF rho Posts_bw)).
  - intros r1 r2 H1 H2. eapply agree_below_trans; eauto.
  - exact echeck_bw.
  - intros E rhoE HinE HgE.
    destruct HinE as [<-|[]]; revert HgE.
    apply (eexit_post_I0 segsU K NF rho vcuts_bw Posts_bw (mkVN P_bw 1 vTop)). in_nth 0.
  - left; reflexivity.
  - apply agree_below_refl.
Qed.
