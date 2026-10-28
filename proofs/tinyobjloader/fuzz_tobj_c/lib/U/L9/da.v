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
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L9 Require Import S_da.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition FUEL_da : nat := 200%nat.
Definition cuts_da : list sstate := [Pre_da].
Definition exits_da : list sstate := [P_da].
Definition cutpcs_da : list Z := [].

Lemma check_da : check_cfg segsU FUEL_da cutpcs_da NF cuts_da exits_da = true.
Proof. apply SymCFGFast.check_cfg_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma cuts_da_strict : existsb ss_lenient cuts_da = false.
Proof. vm_compute. reflexivity. Qed.

Theorem da_sum : da_stmt_U.
Proof.
  intros ok K rho Hok.
  apply (cfg_sound segsU FUEL_da cutpcs_da NF cuts_da exits_da
           (fun rho' => agree_below NF rho rho') ok K (LQ segsU K NF rho Posts_da) Hok).
  - rewrite cuts_da_strict. intros; discriminate.
  - intros r1 r2 H1 H2. eapply agree_below_trans; eauto.
  - exact check_da.
  - intros E rhoE HinE HagE.
    destruct HinE as [<-|[]]; revert HagE.
    apply exit_post. in_nth 0.
  - left; reflexivity.
  - apply agree_below_refl.
Qed.

Definition vcuts_da : list vnode := [mkVN Pre_da 30 (SLit 0)].
Definition vexits_da : list vnode := [mkVN P_da 1 vTop].

Lemma echeck_da : check_ecfgI segsU FUEL_da cutpcs_da NF vcuts_da vexits_da = true.
Proof. apply CfgFast.check_ecfgI_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.

Theorem da_sum_ex : da_ex_stmt_U.
Proof.
  intros K rho.
  change Pre_da with (vn_state (mkVN Pre_da 30 (SLit 0))).
  apply (cfg_complete_autoI segsU FUEL_da cutpcs_da NF vcuts_da vexits_da
           (fun rho' => agree_below NF rho rho') K (LQ segsU K NF rho Posts_da)).
  - intros r1 r2 H1 H2. eapply agree_below_trans; eauto.
  - exact echeck_da.
  - intros E rhoE HinE HgE.
    destruct HinE as [<-|[]]; revert HgE.
    apply (eexit_post_I0 segsU K NF rho vcuts_da Posts_da (mkVN P_da 1 vTop)). in_nth 0.
  - left; reflexivity.
  - apply agree_below_refl.
Qed.
