From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocModel MallocInv MallocLayout MallocIface MallocLaws.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundR SymSummary.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Contract.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv TobjJV.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Init.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L9 Require Import S_vr.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition vp_entry : Z := 0x18a20.
Definition vp_ret : Z := 0x18ab4.

Definition vAl : sv := SVar 13.

Definition vp_facts : list sprop :=
  [ SPAlign 10 4;
    SPBranch BC_GE (SLit (-864)) vDp;
    SPBranch BC_GE vDp (SLit (- 2 ^ 40));
    SPUle (SVar 30) (SAlu ALU_ADD (spo (-16)) vDp);
    SPUle (SAlu ALU_ADD (SVar 30) (SLit 16)) (SVar 10);
    SPUle (SVar 10) (SLit two47);
    SPUle vC vK;
    SPUle (kbytes vK) (SLit two47);
    SPUle vK (SLit two47);
    SPUle (SLit 1) vE;
    SPUle vE (SLit 4096);
    SPUle (SVar 30) vV;
    SPUle vV (SLit two47);
    SPUle (SVar 30) vAl;
    SPUle vAl (SLit two47);
    SPUle vD (SLit two47);
    SPUle (SLit loS) (SVar 30);
    SPUle (SVar 30) (SLit hiA);
    SPAlign 12 3;
    SPAlign 13 3 ].

Definition O_Fp (cells : list cell) : sobj := mkObj (SVar 10) (SLit (-16)) (SLit 0) cells DUnknown.
Definition O_Dp : sobj := mkObj (spo (-16)) vDp (SLit 0) [] DUnknown.
Definition O_alp : sobj := mkObj vAl (SLit 0) (SLit 48) al_cells DUnknown.

Definition Pre_vp : sstate :=
  mkSS vp_entry pre_regs pre_fregs FcsrFrm0 None
    [O_Fp []; O_Dp; O_vec vD vC vK vE; O_alp; O_data vD (kbytes vK)] vp_facts NF false.

Definition slot_of (d : sv) : sv := SAlu ALU_ADD d (kbytes vC).
Definition vC1 : sv := SAlu ALU_ADD vC (SLit 1).

Definition P_push_fail : sstate :=
  mkSS vp_ret (setregs (post_regs NF) [(10%nat, SLit 0)]) pre_fregs FcsrFrm0 None
    [O_Dp; O_vec vD vC vK vE; O_alp; O_data vD (kbytes vK); O_Fp []] vp_facts NPOSTM false.

Definition P_push_keep : sstate :=
  mkSS vp_ret (setregs (post_regs NF) [(10%nat, slot_of vD)]) pre_fregs FcsrFrm0 None
    [O_Dp; O_data vD (kbytes vK); O_vec vD vC1 vK vE; O_alp; O_Fp []]
    (SPUle vC1 vK :: vp_facts) NPOSTM false.

Definition push_grown_facts : list sprop :=
  [ SPUle vC1 vKn;
    SPAlign 140 4;
    SPNot (SPBranch BC_EQ vDn (SLit 0));
    SPUle (SLit 4096) vDn;
    SPUle vDn (SLit hiA);
    SPUle (kbytes vKn) (SLit hiA);
    SPUle (SAlu ALU_ADD vDn (kbytes vKn)) (SLit hiA);
    SPUle vKn (SLit hiA) ].

Definition P_push_grown : sstate :=
  mkSS vp_ret (setregs (post_regs NF) [(10%nat, slot_of vDn)]) pre_fregs FcsrFrm0 None
    [O_Dp; O_data vDn (kbytes vKn); O_vec vDn vC1 vKn vE; O_alp; O_Fp []]
    (push_grown_facts ++ vp_facts) 142 false.

Definition PD_vp : list (sstate * list (sv * sv)) :=
  [(P_push_fail, tv0); (P_push_keep, tv0); (P_push_grown, tv_post)].

Definition Posts_vp (Kc : list event -> Model -> Prop) (FB : list (Z * Z)) : list (sstate * jpost) :=
  PostsC segsU C_U Kc (fun _ => P0_vr) PD_vp FB.

Definition vp_stmt_U : Prop :=
  forall (ok : world -> Prop) (Kc : list event -> Model -> Prop) (FB : list (Z * Z)) (rho0 : valuation),
    ok_sideK segsU ok Kc -> malloc_laws segsU C_U -> malloc_contracts segsU C_U EC_U ->
    triple segsU ok (SPJ segsU (JG_pre segsU C_U Kc P0_vr FB tv0) Pre_vp rho0)
      (LQP segsU NF rho0 (Posts_vp Kc FB)).

Definition vp_ex_stmt_U : Prop :=
  forall (Kc : list event -> Model -> Prop) (FB : list (Z * Z)) (rho0 : valuation),
    vm_insensitive Kc -> malloc_laws segsU C_U -> malloc_contracts_ex segsU C_U EC_U ->
    etriple segsU (SPJ segsU (JG_pre segsU C_U Kc P0_vr FB tv0) Pre_vp rho0)
      (LQP segsU NF rho0 (Posts_vp Kc FB)).
