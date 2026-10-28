From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocModel MallocInv MallocLayout MallocIface MallocLaws.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundR SymSummary.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Contract.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv TobjJV TobjJVA.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Init.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L8 Require Import S_fs.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

(* fs tail region: from the join J at fs+852 (arena head SVar h) to fs's posts; J and h are t-L3's
   fs_st.J852 / fs_st.hJ852 (U/L3/fs_st.v), whose fs proof discharges its exit at J with these. *)
Definition fsB_stmt (J : sstate) (h : positive) : Prop :=
  forall (ok : world -> Prop) (Kc : list event -> Model -> Prop) (FB : list (Z * Z)) (rho0 rho : valuation),
    ok_sideK segsU ok Kc -> malloc_laws segsU C_U -> malloc_contracts segsU C_U EC_U ->
    triple segsU ok (SPJ segsU (JGA segsU C_U FD.NP Kc rho0 (P0_fs FB) FB tv0 (AHead (SVar h))) J rho)
      (LQP segsU FD.NP rho0 (Posts_fs Kc FB)).

Definition fsB_ex_stmt (J : sstate) (h : positive) : Prop :=
  forall (Kc : list event -> Model -> Prop) (FB : list (Z * Z)) (rho0 rho : valuation),
    vm_insensitive Kc -> malloc_laws segsU C_U -> malloc_contracts_ex segsU C_U EC_U ->
    etriple segsU (SPJ segsU (JGA segsU C_U FD.NP Kc rho0 (P0_fs FB) FB tv0 (AHead (SVar h))) J rho)
      (LQP segsU FD.NP rho0 (Posts_fs Kc FB)).
