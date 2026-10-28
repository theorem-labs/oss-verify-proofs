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
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L6 Require Import S_pg S_pgB pg_cuts.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFGFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import PGC.

Definition FUEL_pg : nat := 3000%nat.
Definition cutpcs_pg : list Z := [0x1dd0c; 0x1dea8; 0x1defc; 0x1e0e0; 0x1e288; 0x1e458; 0x1e534].
Definition cuts_pg : list sstate := [Pre_pg_U []; Kfin; Kcm; Knw; Kext; Kbbp; Kproj].
Definition exits_pg : list sstate := [P_inv_U; P_ok_U; B_U].

Lemma check_pg : check_cfg segsU FUEL_pg cutpcs_pg NF cuts_pg exits_pg = true.
Proof. apply SymCFGFast.check_cfg_fast_ok. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma cuts_pg_strict : existsb ss_lenient cuts_pg = false.
Proof. vm_compute. reflexivity. Qed.

Section PG.
Hypothesis PGB : pgB_sum_stmt_U.

Theorem tess_polygon_sum_U : tess_polygon_sum_stmt_U.
Proof.
  intros ok K rho Hok.
  apply (cfg_sound segsU FUEL_pg cutpcs_pg NF cuts_pg exits_pg
           (fun rho' => agree_below NF rho rho') ok K (LQ segsU K NF rho Posts_pg_U) Hok).
  - rewrite cuts_pg_strict. intros; discriminate.
  - intros r1 r2 H1 H2. eapply agree_below_trans; eauto.
  - exact check_pg.
  - intros E rhoE HinE HagE.
    destruct HinE as [<-|[<-|[<-|[]]]].
    + revert HagE. apply exit_post. in_nth 0.
    + revert HagE. apply exit_post. in_nth 1.
    + eapply triple_conseq; [intros w Hw; exact Hw | intros w Hw; right; exact Hw |].
      exact (PGB ok K rho rhoE Hok HagE).
  - left; reflexivity.
  - apply agree_below_refl.
Qed.
End PG.
