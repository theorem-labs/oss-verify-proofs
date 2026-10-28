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
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L9 Require S_vr.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition ra_entry : Z := 0x1c0cc.
Definition ra_ret : Z := 0x1c1b0.

Definition vA : sv := SVar 12.  Definition vP : sv := SVar 13.  Definition vOS : sv := SVar 14.
Definition vDp : sv := SVar 19.  Definition vNS : sv := SVar 33.  Definition vPn : sv := SVar 140.

Definition spo (k : Z) : sv := SAlu ALU_ADD (SVar 10) (SLit k).
Definition two47 : Z := 2 ^ 47.
Definition hiA : Z := S_vr.hiA.
Definition loS : Z := S_vr.loS.

Definition ra_facts : list sprop :=
  [ SPAlign 10 4;
    SPBranch BC_GE (SLit (-784)) vDp;
    SPBranch BC_GE vDp (SLit (- 2 ^ 40));
    SPUle (SVar 30) (SAlu ALU_ADD (spo (-48)) vDp);
    SPUle (SVar 30) (SVar 10);
    SPUle (SVar 10) (SLit two47);
    SPUle (SLit loS) (SVar 30);
    SPUle (SVar 30) (SLit hiA);
    SPUle (SVar 30) vA;
    SPUle vA (SLit two47);
    SPAlign 12 3;
    SPUle (SLit 4096) vP;
    SPUle vP (SLit hiA);
    SPUle vOS (SLit hiA);
    SPUle (SAlu ALU_ADD vP vOS) (SLit hiA);
    SPUle (SLit 1) vOS;
    SPUle vOS vNS ].

Definition O_F (cells : list cell) : sobj := mkObj (SVar 10) (SLit (-48)) (SLit 0) cells DUnknown.
Definition O_D : sobj := mkObj (spo (-48)) vDp (SLit 0) [] DUnknown.
Definition O_al : sobj := mkObj vA (SLit 0) (SLit 48) S_vr.al_cells DUnknown.
Definition O_blk (p n : sv) : sobj := mkObj p (SLit 0) n [] DUnknown.

Definition pre_regs_ra : list sv := setregs pre_regs [(14%nat, SLit 16)].

Definition Pre_ra : sstate :=
  mkSS ra_entry pre_regs_ra pre_fregs FcsrFrm0 None
    [O_F []; O_D; O_al; O_blk vP vOS] ra_facts NF false.

Definition P_fail : sstate :=
  mkSS ra_ret (setregs (post_regs NF) [(10%nat, SLit 0)]) pre_fregs FcsrFrm0 None
    [O_F []; O_D; O_al; O_blk vP vOS] ra_facts NPOSTM false.

Definition ok_facts : list sprop :=
  [ SPAlign 140 4;
    SPNot (SPBranch BC_EQ vPn (SLit 0));
    SPUle (SLit 4096) vPn;
    SPUle vPn (SLit hiA);
    SPUle (SAlu ALU_ADD vPn vNS) (SLit hiA);
    SPUle vNS (SLit hiA) ].

Definition P_ok : sstate :=
  mkSS ra_ret (setregs (post_regs NF) [(10%nat, vPn)]) pre_fregs FcsrFrm0 None
    [O_F []; O_D; O_al; O_blk vPn vNS] (ok_facts ++ ra_facts) 141 false.

Definition tv0 : list (sv * sv) := [(vP, vOS)].
Definition tvP : list (sv * sv) := [(vPn, vNS)].

Definition P0_ra (r : valuation) : Prop := True.

Definition PD_ra : list (sstate * list (sv * sv)) := [(P_fail, tv0); (P_ok, tvP)].

Definition Posts_ra (Kc : list event -> Model -> Prop) (FB : list (Z * Z)) : list (sstate * jpost) :=
  PostsC segsU C_U Kc (fun _ => P0_ra) PD_ra FB.

Definition ra_stmt_U : Prop :=
  forall (ok : world -> Prop) (Kc : list event -> Model -> Prop) (FB : list (Z * Z)) (rho0 : valuation),
    ok_sideK segsU ok Kc -> malloc_laws segsU C_U -> malloc_contracts segsU C_U EC_U ->
    triple segsU ok (SPJ segsU (JG_pre segsU C_U Kc P0_ra FB tv0) Pre_ra rho0)
      (LQP segsU NF rho0 (Posts_ra Kc FB)).

Definition ra_ex_stmt_U : Prop :=
  forall (Kc : list event -> Model -> Prop) (FB : list (Z * Z)) (rho0 : valuation),
    vm_insensitive Kc -> malloc_laws segsU C_U -> malloc_contracts_ex segsU C_U EC_U ->
    etriple segsU (SPJ segsU (JG_pre segsU C_U Kc P0_ra FB tv0) Pre_ra rho0)
      (LQP segsU NF rho0 (Posts_ra Kc FB)).
