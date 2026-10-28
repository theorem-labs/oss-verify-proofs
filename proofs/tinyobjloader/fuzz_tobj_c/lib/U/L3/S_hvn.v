From Stdlib Require Import ZArith NArith List Bool PArith.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocModel MallocInv MallocLayout MallocIface MallocLaws.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundR SymSummary.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Contract.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv TobjJV.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Init.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P Require Lib_handle__G1.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Module HV := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_vn.

Module HandleVnAddrU.
  Definition hvnU_entry : Z := 0x1914c.
  Definition hvnU_ret1 : Z := 0x19260.
  Definition hvnU_ret2 : Z := 0x1927c.
  Definition hvnU_ret3 : Z := 0x19300.
End HandleVnAddrU.
Import HandleVnAddrU.

Definition O_al_U : sobj :=
  mkObj HV.vAL (SLit 0) (SLit 48)
    [HV.c8 0 (SLit 0x13928); HV.c8 8 (SLit 0x13934); HV.c8 16 (SLit 0);
     HV.c8 24 (SLit 0x13948); HV.c8 32 (SLit 0); HV.c8 40 (SLit 0)] DUnknown.

Definition objs_pre_U : list sobj :=
  [HV.O_F []; HV.O_D; HV.P_alloc; HV.P_st HV.vERR; HV.V184 HV.vND HV.vNC HV.vNK; O_al_U;
   HV.O_c0 OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_scan__G1.Lib_scan_double.vI; HV.O_c8; HV.O_text;
   HV.O_dat HV.vND HV.vNK].

Definition hvn_facts_U : list sprop :=
  SPUle OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_scan__G1.Lib_scan_double.vL (SLit (2 ^ 26)) :: HV.hvn_facts.

Definition Pre_hvn_U : sstate :=
  mkSS hvnU_entry pre_regs pre_fregs FcsrFrm0 None objs_pre_U hvn_facts_U NF false.

Definition objs_post_U : list sobj :=
  [HV.O_F []; HV.O_D; HV.P_alloc; HV.P_st HV.pERR; HV.V184 HV.pD HV.pC HV.pK; O_al_U; HV.O_c0 HV.pI; HV.O_c8;
   HV.O_text; HV.O_dat HV.pD HV.pK].

Definition P_ret_U (pc : Z) : sstate :=
  mkSS pc (post_regs NF) HV.post_fregs_hvn FcsrFrm0 None objs_post_U HV.post_facts 177 false.

Definition PD_hvn_U : list (sstate * list (sv * sv)) :=
  [(P_ret_U hvnU_ret1, HV.tvP); (P_ret_U hvnU_ret2, HV.tvP); (P_ret_U hvnU_ret3, HV.tvP)].

Definition Posts_hvn_U (Kc : list event -> Model -> Prop) (FB : list (Z * Z)) : list (sstate * jpost) :=
  PostsC segsU C_U Kc HV.P0_hvn PD_hvn_U FB.

Definition handle_vn_stmt_U : Prop :=
  forall (ok : world -> Prop) (Kc : list event -> Model -> Prop) (FB : list (Z * Z)) (rho0 : valuation),
    ok_sideK segsU ok Kc -> malloc_laws segsU C_U -> malloc_contracts segsU C_U EC_U ->
    triple segsU ok (SPJ segsU (JG_pre segsU C_U Kc (HV.P0_hvn FB) FB HV.tv0) Pre_hvn_U rho0)
      (LQP segsU NF rho0 (Posts_hvn_U Kc FB)).

Definition handle_vn_ex_stmt_U : Prop :=
  forall (Kc : list event -> Model -> Prop) (FB : list (Z * Z)) (rho0 : valuation),
    vm_insensitive Kc -> malloc_laws segsU C_U -> malloc_contracts_ex segsU C_U EC_U ->
    etriple segsU (SPJ segsU (JG_pre segsU C_U Kc (HV.P0_hvn FB) FB HV.tv0) Pre_hvn_U rho0)
      (LQP segsU NF rho0 (Posts_hvn_U Kc FB)).
