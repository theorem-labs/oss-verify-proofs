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

Definition vr_entry : Z := S_vr.vr_entry.
Definition vr_ret : Z := S_vr.vr_ret.

Definition vV : sv := S_vr.vV.  Definition vW : sv := S_vr.vW.  Definition vA : sv := S_vr.vA.
Definition vD : sv := S_vr.vD.  Definition vC : sv := S_vr.vC.  Definition vK : sv := S_vr.vK.
Definition vDp : sv := S_vr.vDp.  Definition vDn : sv := S_vr.vDn.  Definition vKn : sv := S_vr.vKn.
Definition vL : sv := SVar 52.

Definition spo (k : Z) : sv := S_vr.spo k.
Definition kb16 (k : sv) : sv := SMd M_MUL (SLit 16) k.
Definition two47 : Z := S_vr.two47.
Definition two48 : Z := S_vr.two48.
Definition hiA : Z := S_vr.hiA.
Definition loS : Z := S_vr.loS.

Definition flds : list (Z * Z) := [(0, 8); (8, 8)].
Definition tmpl : list tfact := [TF2le false 0 1 vL].
Definition darr (c : sv) : odefault := DArr 16 c flds tmpl.

Definition base_facts : list sprop :=
  [ SPAlign 10 4;
    SPBranch BC_GE (SLit (-832)) vDp;
    SPBranch BC_GE vDp (SLit (- 2 ^ 40));
    SPUle (SVar 30) (SAlu ALU_ADD (spo (-32)) vDp);
    SPUle (SVar 30) (SVar 10);
    SPUle (SVar 10) (SLit two47);
    SPUle vC vK;
    SPUle (kb16 vK) (SLit two47);
    SPUle vK (SLit two47);
    SPUle (SVar 30) vV;
    SPUle vV (SLit two47);
    SPUle (SVar 30) vA;
    SPUle vA (SLit two47);
    SPUle vD (SLit two47);
    SPUle vW (SLit two48);
    SPUle vW (SAlu ALU_ADD vC (SLit 1));
    SPUle (SLit loS) (SVar 30);
    SPUle (SVar 30) (SLit hiA);
    SPAlign 12 3;
    SPAlign 14 3 ].

Definition O_F (cells : list cell) : sobj := S_vr.O_F cells.
Definition O_D : sobj := S_vr.O_D.
Definition O_vec (d c k : sv) : sobj := S_vr.O_vec d c k (SLit 16).
Definition O_al : sobj := S_vr.O_al.
Definition O_data (d bytes c : sv) : sobj := mkObj d (SLit 0) bytes [] (darr c).

Definition Pre_vr : sstate :=
  mkSS vr_entry pre_regs pre_fregs FcsrFrm0 None
    [O_F []; O_D; O_vec vD vC vK; O_al; O_data vD (kb16 vK) vC]
    base_facts NF false.

Definition post_objs (d k : sv) : list sobj :=
  [O_F []; O_D; O_vec d vC k; O_al; O_data d (kb16 k) vC].

Definition P_keep : sstate :=
  mkSS vr_ret (setregs (post_regs NF) [(10%nat, SLit 1)]) pre_fregs FcsrFrm0 None
    (post_objs vD vK) (SPUle vW vK :: base_facts) NPOSTM false.

Definition P_fail : sstate :=
  mkSS vr_ret (setregs (post_regs NF) [(10%nat, SLit 0)]) pre_fregs FcsrFrm0 None
    (post_objs vD vK) base_facts NPOSTM false.

Definition grown_facts : list sprop :=
  [ SPUle vW vKn;
    SPUle vC vKn;
    SPAlign 140 4;
    SPNot (SPBranch BC_EQ vDn (SLit 0));
    SPUle (SLit 4096) vDn;
    SPUle vDn (SLit hiA);
    SPUle (kb16 vKn) (SLit hiA);
    SPUle (SAlu ALU_ADD vDn (kb16 vKn)) (SLit hiA);
    SPUle vKn (SLit hiA) ].

Definition P_grown : sstate :=
  mkSS vr_ret (setregs (post_regs NF) [(10%nat, SLit 1)]) pre_fregs FcsrFrm0 None
    [O_D; O_data vDn (kb16 vKn) vC; O_F []; O_vec vDn vC vKn; O_al]
    (grown_facts ++ base_facts) 142 false.

Definition tv0 : list (sv * sv) := [(vD, kb16 vK)].
Definition tv_post : list (sv * sv) := [(vDn, kb16 vKn)].

Definition P0_vr (r : valuation) : Prop := S_vr.P0_vr r.

Definition PD_vr : list (sstate * list (sv * sv)) :=
  [(P_keep, tv0); (P_fail, tv0); (P_grown, tv_post)].

Definition Posts_vr (Kc : list event -> Model -> Prop) (FB : list (Z * Z)) : list (sstate * jpost) :=
  PostsC segsU C_U Kc (fun _ => P0_vr) PD_vr FB.

Definition vr_darr_stmt_U : Prop :=
  forall (ok : world -> Prop) (Kc : list event -> Model -> Prop) (FB : list (Z * Z)) (rho0 : valuation),
    ok_sideK segsU ok Kc -> malloc_laws segsU C_U -> malloc_contracts segsU C_U EC_U ->
    triple segsU ok (SPJ segsU (JG_pre segsU C_U Kc P0_vr FB tv0) Pre_vr rho0)
      (LQP segsU NF rho0 (Posts_vr Kc FB)).

Definition vr_darr_ex_stmt_U : Prop :=
  forall (Kc : list event -> Model -> Prop) (FB : list (Z * Z)) (rho0 : valuation),
    vm_insensitive Kc -> malloc_laws segsU C_U -> malloc_contracts_ex segsU C_U EC_U ->
    etriple segsU (SPJ segsU (JG_pre segsU C_U Kc P0_vr FB tv0) Pre_vr rho0)
      (LQP segsU NF rho0 (Posts_vr Kc FB)).
