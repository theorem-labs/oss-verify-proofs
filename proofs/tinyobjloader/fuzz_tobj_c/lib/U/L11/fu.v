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
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L11 Require Import S_fu.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import FuAddr.

Definition FUEL_fu : nat := 100%nat.
Definition cuts_fu : list sstate := [Pre_fu_U].
Definition exits_fu : list sstate := [P_fu_U].
Definition cutpcs_fu : list Z := [].

Lemma check_fu : check_cfg segsU FUEL_fu cutpcs_fu NF cuts_fu exits_fu = true.
Proof. apply SymCFGFast.check_cfg_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma cuts_fu_strict : existsb ss_lenient cuts_fu = false.
Proof. vm_compute. reflexivity. Qed.

Theorem finalize_unknowns_sum_U : finalize_unknowns_sum_stmt_U.
Proof.
  intros ok K rho Hok.
  apply (cfg_sound segsU FUEL_fu cutpcs_fu NF cuts_fu exits_fu
           (fun rho' => agree_below NF rho rho') ok K (LQ segsU K NF rho Posts_fu_U) Hok).
  - rewrite cuts_fu_strict. intros; discriminate.
  - intros r1 r2 H1 H2. eapply agree_below_trans; eauto.
  - exact check_fu.
  - intros E rhoE HinE HagE.
    destruct HinE as [<-|[]]; revert HagE. apply exit_post. in_nth 0.
  - left; reflexivity.
  - apply agree_below_refl.
Qed.

Definition vcuts_fu : list vnode := [mkVN Pre_fu_U 30 (SLit 0)].
Definition vexits_fu : list vnode := [mkVN P_fu_U 1 vTop].

Lemma echeck_fu : check_ecfgI segsU FUEL_fu cutpcs_fu NF vcuts_fu vexits_fu = true.
Proof. apply CfgFast.check_ecfgI_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.

Theorem finalize_unknowns_sum_ex_U : finalize_unknowns_sum_ex_stmt_U.
Proof.
  intros K rho.
  change Pre_fu_U with (vn_state (mkVN Pre_fu_U 30 (SLit 0))).
  apply (cfg_complete_autoI segsU FUEL_fu cutpcs_fu NF vcuts_fu vexits_fu
           (fun rho' => agree_below NF rho rho') K (LQ segsU K NF rho Posts_fu_U)).
  - intros r1 r2 H1 H2. eapply agree_below_trans; eauto.
  - exact echeck_fu.
  - intros E rhoE HinE HgE.
    destruct HinE as [<-|[]]; revert HgE.
    apply (eexit_post_I0 segsU K NF rho vcuts_fu Posts_fu_U (mkVN P_fu_U 1 vTop)). in_nth 0.
  - left; reflexivity.
  - apply agree_below_refl.
Qed.
