From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType State.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymSoundR SymSummary.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocLayout MallocLaws Contract.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import TobjJV BuilderDispose.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Init.
Import ListNotations.
Open Scope Z_scope.

Definition bcU : bd_code := BDC 0x15be4 0x167f0
  [0x15c50; 0x15cac; 0x15d08; 0x15d64; 0x15dc0; 0x15e1c; 0x15e78; 0x15ed4; 0x15f30; 0x15f8c; 0x15fe8;
   0x16044; 0x160a0; 0x160fc; 0x16158; 0x161b4; 0x16210; 0x1626c; 0x162c8; 0x16324; 0x16380; 0x163dc;
   0x16438; 0x16494; 0x164f0; 0x1654c; 0x165a8; 0x16604; 0x16660; 0x166bc; 0x16718; 0x16774; 0x167d0]
  0x13928 0x13934 0x13948 [SPAlign 12 3; SPAlign 16 3].

Definition Pre_bd : sstate := BuilderDispose.Pre_bd bcU.
Definition Posts_bd (Kc : list event -> Model -> Prop) (FB : list (Z * Z)) : list (sstate * jpost) :=
  BuilderDispose.Posts_bd U.Init.segsU bcU C_U Kc FB.

Definition builder_dispose_sum_stmt_U : Prop :=
  forall (ok : world -> Prop) (Kc : list event -> Model -> Prop) (FB : list (Z * Z)) (rho0 : valuation),
    malloc_laws U.Init.segsU C_U -> ok_sideK U.Init.segsU ok Kc -> malloc_contracts U.Init.segsU C_U EC_U ->
    triple U.Init.segsU ok
      (SPJ U.Init.segsU (JG_pre U.Init.segsU C_U Kc P0_bd FB (tvL 0)) Pre_bd rho0)
      (LQP U.Init.segsU NP rho0 (Posts_bd Kc FB)).

Definition builder_dispose_sum_ex_stmt_U : Prop :=
  forall (Kc : list event -> Model -> Prop) (FB : list (Z * Z)) (rho0 : valuation),
    malloc_laws U.Init.segsU C_U -> vm_insensitive Kc -> malloc_contracts_ex U.Init.segsU C_U EC_U ->
    etriple U.Init.segsU
      (SPJ U.Init.segsU (JG_pre U.Init.segsU C_U Kc P0_bd FB (tvL 0)) Pre_bd rho0)
      (LQP U.Init.segsU NP rho0 (Posts_bd Kc FB)).
