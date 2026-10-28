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
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L8 Require Import S_ml.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition FUEL_ml : nat := 400%nat.
Definition cuts_ml : list sstate := [Pre_ml].
Definition exits_ml : list sstate := [P_ml].
Definition cutpcs_ml : list Z := [].

Lemma check_ml : check_cfg segsU FUEL_ml cutpcs_ml NF cuts_ml exits_ml = true.
Proof. apply SymCFGFast.check_cfg_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma cuts_ml_strict : existsb ss_lenient cuts_ml = false.
Proof. vm_compute. reflexivity. Qed.

Theorem ml_sum : ml_stmt_U.
Proof.
  intros ok K rho Hok.
  apply (cfg_sound segsU FUEL_ml cutpcs_ml NF cuts_ml exits_ml
           (fun rho' => agree_below NF rho rho') ok K (LQ segsU K NF rho Posts_ml) Hok).
  - rewrite cuts_ml_strict. intros; discriminate.
  - intros r1 r2 H1 H2. eapply agree_below_trans; eauto.
  - exact check_ml.
  - intros E rhoE HinE HagE.
    destruct HinE as [<-|[]]; revert HagE.
    apply exit_post. in_nth 0.
  - left; reflexivity.
  - apply agree_below_refl.
Qed.

Definition vcuts_ml : list vnode := [mkVN Pre_ml 30 (SLit 0)].
Definition vexits_ml : list vnode := [mkVN P_ml 1 vTop].

Lemma echeck_ml : check_ecfgI segsU FUEL_ml cutpcs_ml NF vcuts_ml vexits_ml = true.
Proof. apply CfgFast.check_ecfgI_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.

Theorem ml_sum_ex : ml_ex_stmt_U.
Proof.
  intros K rho.
  change Pre_ml with (vn_state (mkVN Pre_ml 30 (SLit 0))).
  apply (cfg_complete_autoI segsU FUEL_ml cutpcs_ml NF vcuts_ml vexits_ml
           (fun rho' => agree_below NF rho rho') K (LQ segsU K NF rho Posts_ml)).
  - intros r1 r2 H1 H2. eapply agree_below_trans; eauto.
  - exact echeck_ml.
  - intros E rhoE HinE HgE.
    destruct HinE as [<-|[]]; revert HgE.
    apply (eexit_post_I0 segsU K NF rho vcuts_ml Posts_ml (mkVN P_ml 1 vTop)). in_nth 0.
  - left; reflexivity.
  - apply agree_below_refl.
Qed.
