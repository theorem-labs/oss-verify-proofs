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
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L11 Require Import S_sc.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScAddr.

Definition FUEL_sc : nat := 300%nat.

Definition notP : sv := SAlu ALU_XOR SC.vP (SLit 18446744073709551615).

Definition C1_U : sstate :=
  add_facts SC.inv (SC.sc_state sc_L1 [(11%nat, SC.v120); (12%nat, notP); (13%nat, SC.v121)] [] []).

Definition cuts_sc : list sstate := [Pre_sc_U; C1_U].
Definition exits_sc : list sstate := [P_sc_U].
Definition cutpcs_sc : list Z := [sc_L1].

Lemma check_sc : check_cfg segsU FUEL_sc cutpcs_sc NF cuts_sc exits_sc = true.
Proof. apply SymCFGFast.check_cfg_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma cuts_sc_strict : existsb ss_lenient cuts_sc = false.
Proof. vm_compute. reflexivity. Qed.

Theorem scale2d_sum_U : scale2d_sum_stmt_U.
Proof.
  intros ok K rho Hok.
  apply (cfg_sound segsU FUEL_sc cutpcs_sc NF cuts_sc exits_sc
           (fun rho' => agree_below NF rho rho') ok K (LQ segsU K NF rho Posts_sc_U) Hok).
  - rewrite cuts_sc_strict. intros; discriminate.
  - intros r1 r2 H1 H2. eapply agree_below_trans; eauto.
  - exact check_sc.
  - intros E rhoE HinE HagE.
    destruct HinE as [<-|[]]; revert HagE. apply exit_post. in_nth 0.
  - left; reflexivity.
  - apply agree_below_refl.
Qed.

Definition vcuts_sc : list vnode := [mkVN Pre_sc_U 30 (SLit 0); mkVN C1_U 20 SC.v121].
Definition vexits_sc : list vnode := [mkVN P_sc_U 1 vTop].

Lemma echeck_sc : check_ecfgI segsU FUEL_sc cutpcs_sc NF vcuts_sc vexits_sc = true.
Proof. apply CfgFast.check_ecfgI_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.

Theorem scale2d_sum_ex_U : scale2d_sum_ex_stmt_U.
Proof.
  intros K rho.
  change Pre_sc_U with (vn_state (mkVN Pre_sc_U 30 (SLit 0))).
  apply (cfg_complete_autoI segsU FUEL_sc cutpcs_sc NF vcuts_sc vexits_sc
           (fun rho' => agree_below NF rho rho') K (LQ segsU K NF rho Posts_sc_U)).
  - intros r1 r2 H1 H2. eapply agree_below_trans; eauto.
  - exact echeck_sc.
  - intros E rhoE HinE HgE.
    destruct HinE as [<-|[]]; revert HgE.
    apply (eexit_post_I0 segsU K NF rho vcuts_sc Posts_sc_U (mkVN P_sc_U 1 vTop)). in_nth 0.
  - left; reflexivity.
  - apply agree_below_refl.
Qed.
