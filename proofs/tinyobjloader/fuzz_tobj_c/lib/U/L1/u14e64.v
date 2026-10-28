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
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L1 Require Import S_u14e64.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CfgFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import BinitAddr.

Definition FUEL_bi : nat := 200%nat.
Definition cuts_bi : list sstate := [Pre_bi].
Definition exits_bi : list sstate := [P_bi].
Definition cutpcs_bi : list Z := [].

Lemma check_bi : check_cfg segsU FUEL_bi cutpcs_bi NF cuts_bi exits_bi = true.
Proof. apply SymCFGFast.check_cfg_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma cuts_bi_strict : existsb ss_lenient cuts_bi = false.
Proof. vm_compute. reflexivity. Qed.

Theorem builder_init_sum_U : builder_init_sum_stmt_U.
Proof.
  intros ok K rho Hok.
  apply (cfg_sound segsU FUEL_bi cutpcs_bi NF cuts_bi exits_bi
           (fun rho' => agree_below NF rho rho') ok K (LQ segsU K NF rho Posts_bi) Hok).
  - rewrite cuts_bi_strict. intros; discriminate.
  - intros r1 r2 H1 H2. eapply agree_below_trans; eauto.
  - exact check_bi.
  - intros E rhoE HinE HagE.
    destruct HinE as [<-|[]]; revert HagE.
    apply exit_post. in_nth 0.
  - left; reflexivity.
  - apply agree_below_refl.
Qed.

Definition vcuts_bi : list vnode := [mkVN Pre_bi 30 (SLit 0)].
Definition vexits_bi : list vnode := [mkVN P_bi 1 vTop].

Lemma echeck_bi : check_ecfgI segsU FUEL_bi cutpcs_bi NF vcuts_bi vexits_bi = true.
Proof. apply CfgFast.check_ecfgI_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.

Theorem builder_init_sum_ex_U : builder_init_sum_ex_stmt_U.
Proof.
  intros K rho.
  change Pre_bi with (vn_state (mkVN Pre_bi 30 (SLit 0))).
  apply (cfg_complete_autoI segsU FUEL_bi cutpcs_bi NF vcuts_bi vexits_bi
           (fun rho' => agree_below NF rho rho') K (LQ segsU K NF rho Posts_bi)).
  - intros r1 r2 H1 H2. eapply agree_below_trans; eauto.
  - exact echeck_bi.
  - intros E rhoE HinE HgE.
    destruct HinE as [<-|[]]; revert HgE.
    apply (eexit_post_I0 segsU K NF rho vcuts_bi Posts_bi (mkVN P_bi 1 vTop)). in_nth 0.
  - left; reflexivity.
  - apply agree_below_refl.
Qed.
