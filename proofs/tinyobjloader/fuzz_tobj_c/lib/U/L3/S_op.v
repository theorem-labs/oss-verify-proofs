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
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P Require Lib_vec__G1 Lib_opt__G1.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Module OP1 := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_opt__G1.Lib_opt_push1.
Module VR := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_vec__G1.Lib_vec_reserve.

Module OptPushAddrU.
  Definition opU_entry : Z := 0x1bd78.
  Definition opU_ret : Z := 0x1bf54.
End OptPushAddrU.
Import OptPushAddrU.

Definition O_al_U : sobj :=
  mkObj OP1.vAL (SLit 0) (SLit 48)
    [OP1.c8 0 (SLit 0x13928); OP1.c8 8 (SLit 0x13934); OP1.c8 16 (SLit 0);
     OP1.c8 24 (SLit 0x13948); OP1.c8 32 (SLit 0); OP1.c8 40 (SLit 0)] DUnknown.

Definition O_vals_U (cm : Z) : sobj := mkObj OP1.vVALS (SLit 0) (SLit (4 * cm)) [] DUnknown.
Definition O_deflt_U (cm : Z) : sobj := mkObj OP1.vDEF (SLit 0) (SLit (4 * cm)) [] DUnknown.

Definition objs_of_U (cm : Z) (d c k : sv) : list sobj :=
  [OP1.O_F []; OP1.O_D; OP1.O_vec4 d c k; O_al_U; O_vals_U cm; O_deflt_U cm; OP1.O_dat d k].

Definition Pre_op_U (cm : Z) : sstate :=
  mkSS opU_entry (setregs pre_regs [(11%nat, SLit cm)]) pre_fregs FcsrFrm0 None
    (objs_of_U cm VR.vD VR.vC VR.vK) OP1.op_facts NF false.

Definition P_ret_U (cm : Z) : sstate :=
  mkSS opU_ret (setregs (post_regs NF) [(10%nat, SVar 143)]) pre_fregs FcsrFrm0 None
    (objs_of_U cm (SVar 140) (SVar 141) (SVar 142))
    (SPUle (SVar 143) (SLit 1) :: OP1.vec_facts (SVar 140) (SVar 141) (SVar 142) 140 ++ OP1.op_facts) 144 false.

Definition PD_op_U (cm : Z) : list (sstate * list (sv * sv)) := [(P_ret_U cm, OP1.tvP)].

Definition Posts_op_U (cm : Z) (Kc : list event -> Model -> Prop) (FB : list (Z * Z)) : list (sstate * jpost) :=
  PostsC segsU C_U Kc OP1.P0_op (PD_op_U cm) FB.

Definition op_cms : list Z := [1; 3].

Definition opt_push_stmt_U (cm : Z) : Prop :=
  forall (ok : world -> Prop) (Kc : list event -> Model -> Prop) (FB : list (Z * Z)) (rho0 : valuation),
    ok_sideK segsU ok Kc -> malloc_laws segsU C_U -> malloc_contracts segsU C_U EC_U ->
    triple segsU ok (SPJ segsU (JG_pre segsU C_U Kc (OP1.P0_op FB) FB OP1.tv0) (Pre_op_U cm) rho0)
      (LQP segsU NF rho0 (Posts_op_U cm Kc FB)).

Definition opt_push_ex_stmt_U (cm : Z) : Prop :=
  forall (Kc : list event -> Model -> Prop) (FB : list (Z * Z)) (rho0 : valuation),
    vm_insensitive Kc -> malloc_laws segsU C_U -> malloc_contracts_ex segsU C_U EC_U ->
    etriple segsU (SPJ segsU (JG_pre segsU C_U Kc (OP1.P0_op FB) FB OP1.tv0) (Pre_op_U cm) rho0)
      (LQP segsU NF rho0 (Posts_op_U cm Kc FB)).
