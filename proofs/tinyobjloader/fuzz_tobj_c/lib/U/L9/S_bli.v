From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocModel MallocInv MallocLayout MallocIface MallocLaws.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundR SymSummary SymCFG.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Contract.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv TobjJV.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Init.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L9 Require S_vr.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition bli_entry : Z := 0x150b0.
Definition bli_ret : Z := 0x152a0.
Definition FR : Z := 96.

Definition vBUF : sv := SVar 12.  Definition vLEN : sv := SVar 13.  Definition vV : sv := SVar 14.
Definition vAL : sv := SVar 33.
Definition vD : sv := S_vr.vD.  Definition vC : sv := S_vr.vC.  Definition vK : sv := S_vr.vK.
Definition vDp : sv := S_vr.vDp.

Definition spo (k : Z) : sv := S_vr.spo k.
Definition two47 : Z := S_vr.two47.
Definition kb16 (k : sv) : sv := SMd M_MUL (SLit 16) k.
Definition c8 (o : Z) (v : sv) : cell := S_vr.c8 o v.

Definition O_F (cells : list cell) : sobj := mkObj (SVar 10) (SLit (- FR)) (SLit 0) cells DUnknown.
Definition O_D : sobj := mkObj (spo (- FR)) vDp (SLit 0) [] DUnknown.
Definition O_vec16 (d c k : sv) : sobj :=
  mkObj vV (SLit 0) (SLit 32) [c8 0 d; c8 8 c; c8 16 k; c8 24 (SLit 16)] DUnknown.
Definition O_al : sobj := mkObj vAL (SLit 0) (SLit 48) S_vr.al_cells DUnknown.
Definition O_txt : sobj := mkObj vBUF (SLit 0) vLEN [] DUnknown.

Definition vec_facts (d c k : sv) (dv : positive) : list sprop :=
  [SPUle c k; SPUle (kb16 k) (SLit two47); SPUle k (SLit two47); SPUle d (SLit two47); SPAlign dv 4].

Definition bli_facts : list sprop :=
  [ SPAlign 10 4;
    SPBranch BC_GE (SLit (-864)) vDp;
    SPBranch BC_GE vDp (SLit (- 2 ^ 40));
    SPUle (SVar 30) (SAlu ALU_ADD (spo (- FR)) vDp);
    SPUle (SAlu ALU_ADD (SVar 30) (SLit FR)) (SVar 10);
    SPUle (SVar 10) (SLit two47);
    SPUle vLEN (SLit (2 ^ 26));
    SPUle (SLit 1) vBUF;
    SPUle vBUF (SLit two47);
    SPUle (SVar 30) vV;
    SPUle vV (SLit two47);
    SPAlign 14 3;
    SPUle (SVar 30) vAL;
    SPUle vAL (SLit two47);
    SPAlign 33 3;
    SPUle (SLit S_vr.loS) (SVar 30);
    SPUle (SVar 30) (SLit S_vr.hiA) ] ++ vec_facts vD vC vK 15.

Definition lines_tmpl : list tfact := [TF2le false 0 1 vLEN].
Definition O_dat (d k : sv) : sobj := mkObj d (SLit 0) (kb16 k) [] DUnknown.
Definition O_dat_darr (d c k : sv) : sobj :=
  mkObj d (SLit 0) (kb16 k) [] (DArr 16 c [(0, 8); (8, 8)] lines_tmpl).

Definition objs_of (fcells : list cell) (d c k : sv) : list sobj :=
  [O_F fcells; O_D; O_vec16 d c k; O_al; O_txt; O_dat d k].
Definition objs_of_darr (fcells : list cell) (d c k : sv) : list sobj :=
  [O_F fcells; O_D; O_vec16 d c k; O_al; O_txt; O_dat_darr d c k].

Definition Pre_bli : sstate :=
  mkSS bli_entry pre_regs pre_fregs FcsrFrm0 None (objs_of [] vD vC vK) bli_facts NF false.
Definition Pre_bli0 : sstate := add_facts [SPUle vC (SLit 0)] Pre_bli.

Definition P_ret_darr : sstate :=
  mkSS bli_ret (setregs (post_regs NF) [(10%nat, SVar 143)]) pre_fregs FcsrFrm0 None
    (objs_of_darr [] (SVar 140) (SVar 141) (SVar 142))
    ([SPUle (SVar 143) (SLit 1); SPUle (SVar 141) vLEN] ++ vec_facts (SVar 140) (SVar 141) (SVar 142) 140 ++ bli_facts)
    144 false.

Definition tv0 : list (sv * sv) := [(vD, kb16 vK)].
Definition tvP : list (sv * sv) := [(SVar 140, kb16 (SVar 142))].

Definition P0_bli (FB : list (Z * Z)) (r : valuation) : Prop :=
  bv_unsigned (rw r 13) = 0 \/
  exists b n, In (b, n) FB /\ b <= bv_unsigned (rw r 12) /\ bv_unsigned (rw r 12) + bv_unsigned (rw r 13) <= b + n.

Definition PD_bli_darr : list (sstate * list (sv * sv)) := [(P_ret_darr, tvP)].

Definition Posts_bli_darr (Kc : list event -> Model -> Prop) (FB : list (Z * Z)) : list (sstate * jpost) :=
  PostsC segsU C_U Kc P0_bli PD_bli_darr FB.

Definition bli_darr_stmt_U : Prop :=
  forall (ok : world -> Prop) (Kc : list event -> Model -> Prop) (FB : list (Z * Z)) (rho0 : valuation),
    ok_sideK segsU ok Kc -> malloc_laws segsU C_U -> malloc_contracts segsU C_U EC_U ->
    triple segsU ok (SPJ segsU (JG_pre segsU C_U Kc (P0_bli FB) FB tv0) Pre_bli0 rho0)
      (LQP segsU NF rho0 (Posts_bli_darr Kc FB)).

Definition bli_darr_ex_stmt_U : Prop :=
  forall (Kc : list event -> Model -> Prop) (FB : list (Z * Z)) (rho0 : valuation),
    malloc_laws segsU C_U -> vm_insensitive Kc -> malloc_contracts_ex segsU C_U EC_U ->
    etriple segsU (SPJ segsU (JG_pre segsU C_U Kc (P0_bli FB) FB tv0) Pre_bli0 rho0)
      (LQP segsU NF rho0 (Posts_bli_darr Kc FB)).
