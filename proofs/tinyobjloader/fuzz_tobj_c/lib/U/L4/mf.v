From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CfgGlue CursorGlue.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Init.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L4 Require Import S_mf.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition FUEL_mf : nat := 400%nat.
Definition cuts_mf : list sstate := [Pre_mf].
Definition exits_mf : list sstate := [P_mf].
Definition cutpcs_mf : list Z := [].

Lemma check_mf : check_cfg U.Init.segsU FUEL_mf cutpcs_mf NF cuts_mf exits_mf = true.
Proof. vm_compute. reflexivity. Qed.

Lemma cuts_mf_strict : existsb ss_lenient cuts_mf = false.
Proof. reflexivity. Qed.

Theorem mat_find_sum_U : mat_find_sum_stmt_U.
Proof.
  intros ok K rho Hok.
  apply (cfg_sound U.Init.segsU FUEL_mf cutpcs_mf NF cuts_mf exits_mf
           (fun rho' => agree_below NF rho rho') ok K (LQ U.Init.segsU K NF rho Posts_mf) Hok).
  - rewrite cuts_mf_strict. intros; discriminate.
  - intros r1 r2 H1 H2. eapply agree_below_trans; eauto.
  - exact check_mf.
  - intros E rhoE HinE HagE.
    destruct HinE as [<-|[]]; revert HagE.
    apply exit_post. in_nth 0.
  - left; reflexivity.
  - apply agree_below_refl.
Qed.

Definition vcuts_mf : list vnode := [mkVN Pre_mf 30 (SLit 0)].
Definition vexits_mf : list vnode := [mkVN P_mf 1 vTop].

Lemma echeck_mf : check_ecfgI U.Init.segsU FUEL_mf cutpcs_mf NF vcuts_mf vexits_mf = true.
Proof. vm_compute. reflexivity. Qed.

Theorem mat_find_sum_ex_U : mat_find_sum_ex_stmt_U.
Proof.
  intros K rho.
  change Pre_mf with (vn_state (mkVN Pre_mf 30 (SLit 0))).
  apply (cfg_complete_autoI U.Init.segsU FUEL_mf cutpcs_mf NF vcuts_mf vexits_mf
           (fun rho' => agree_below NF rho rho') K (LQ U.Init.segsU K NF rho Posts_mf)).
  - intros r1 r2 H1 H2. eapply agree_below_trans; eauto.
  - exact echeck_mf.
  - intros E rhoE HinE HgE.
    destruct HinE as [<-|[]]; revert HgE.
    apply (eexit_post_I0 U.Init.segsU K NF rho vcuts_mf Posts_mf (mkVN P_mf 1 vTop)). in_nth 0.
  - left; reflexivity.
  - apply agree_below_refl.
Qed.
