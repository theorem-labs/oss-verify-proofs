From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLayout MallocIface MallocLaws Contract.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv TobjJV.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Init.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_defs.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition HF_U : hf_consts :=
  HFC 0x19308 0x19f04 272 0x167f8 0x18abc 0x1dbbc 0x1dbf0 0 0 0x1bf5c 0x1c0c8
      0x13928 0x13934 0x13948
      0x16874 0x18c64 0x18c64 0x1dcc8.

Definition PD_hf_U : list pdesc := [(HP_ret HF_U, tvH); (HP_degen HF_U, tvH)].

Definition Posts_hf_U (Kc : list event -> Model -> Prop) (FB : list (Z * Z)) : list (sstate * jpost) :=
  PostsC segsU C_U Kc P0_hf PD_hf_U FB.

Definition handle_f_sum_stmt_U : Prop :=
  forall (ok : world -> Prop) (Kc : list event -> Model -> Prop) (FB : list (Z * Z)) (rho0 : valuation),
    ok_sideK segsU ok Kc -> malloc_contracts segsU C_U EC_U -> malloc_laws segsU C_U ->
    triple segsU ok (SPJ segsU (JG_pre segsU C_U Kc (P0_hf FB) FB tv_pre) (Pre_hf HF_U) rho0)
      (LQP segsU NP rho0 (Posts_hf_U Kc FB)).

Definition handle_f_sum_ex_stmt_U : Prop :=
  forall (Kc : list event -> Model -> Prop) (FB : list (Z * Z)) (rho0 : valuation),
    vm_insensitive Kc -> malloc_contracts_ex segsU C_U EC_U -> malloc_laws segsU C_U ->
    etriple segsU (SPJ segsU (JG_pre segsU C_U Kc (P0_hf FB) FB tv_pre) (Pre_hf HF_U) rho0)
      (LQP segsU NP rho0 (Posts_hf_U Kc FB)).
