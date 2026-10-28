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
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L9 Require S_ra.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Module RA := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L9.S_ra.

Definition ra_entry : Z := RA.ra_entry.
Definition ra_ret : Z := RA.ra_ret.

Definition vA : sv := RA.vA.  Definition vP : sv := RA.vP.  Definition vOS : sv := RA.vOS.
Definition vNS : sv := RA.vNS.  Definition vPn : sv := RA.vPn.
Definition vL : sv := SVar 52.
Definition vK : sv := SVar 53.
Definition two47 : Z := RA.two47.

Definition kb16 (k : sv) : sv := SMd M_MUL (SLit 16) k.
Definition flds : list (Z * Z) := [(0, 8); (8, 8)].
Definition tmpl : list tfact := [TF2le false 0 1 vL].
Definition darr (c : sv) : odefault := DArr 16 c flds tmpl.

Definition rad_facts : list sprop :=
  RA.ra_facts ++ [SPUle (kb16 vK) vOS; SPUle vK (SLit two47); SPBranch BC_LTU vOS vNS].

Definition O_old : sobj := mkObj vP (SLit 0) vOS [] (darr vK).
Definition O_new : sobj := mkObj vPn (SLit 0) vNS [] (darr vK).

Definition Pre_rad : sstate :=
  mkSS ra_entry RA.pre_regs_ra pre_fregs FcsrFrm0 None
    [RA.O_F []; RA.O_D; RA.O_al; O_old] rad_facts NF false.

Definition P_fail_d : sstate :=
  mkSS ra_ret (setregs (post_regs NF) [(10%nat, SLit 0)]) pre_fregs FcsrFrm0 None
    [RA.O_F []; RA.O_D; RA.O_al; O_old] rad_facts NPOSTM false.

Definition P_ok_d : sstate :=
  mkSS ra_ret (setregs (post_regs NF) [(10%nat, vPn)]) pre_fregs FcsrFrm0 None
    [RA.O_F []; RA.O_D; RA.O_al; O_new] (RA.ok_facts ++ rad_facts) 141 false.

Definition tv0 : list (sv * sv) := RA.tv0.
Definition tvP : list (sv * sv) := RA.tvP.
Definition P0_rad (r : valuation) : Prop := True.

Definition PD_rad : list (sstate * list (sv * sv)) := [(P_fail_d, tv0); (P_ok_d, tvP)].

Definition Posts_rad (Kc : list event -> Model -> Prop) (FB : list (Z * Z)) : list (sstate * jpost) :=
  PostsC segsU C_U Kc (fun _ => P0_rad) PD_rad FB.

Definition ra_darr_stmt_U : Prop :=
  forall (ok : world -> Prop) (Kc : list event -> Model -> Prop) (FB : list (Z * Z)) (rho0 : valuation),
    ok_sideK segsU ok Kc -> malloc_laws segsU C_U -> malloc_contracts segsU C_U EC_U ->
    triple segsU ok (SPJ segsU (JG_pre segsU C_U Kc P0_rad FB tv0) Pre_rad rho0)
      (LQP segsU NF rho0 (Posts_rad Kc FB)).

Definition ra_darr_ex_stmt_U : Prop :=
  forall (Kc : list event -> Model -> Prop) (FB : list (Z * Z)) (rho0 : valuation),
    vm_insensitive Kc -> malloc_laws segsU C_U -> malloc_contracts_ex segsU C_U EC_U ->
    etriple segsU (SPJ segsU (JG_pre segsU C_U Kc P0_rad FB tv0) Pre_rad rho0)
      (LQP segsU NF rho0 (Posts_rad Kc FB)).
