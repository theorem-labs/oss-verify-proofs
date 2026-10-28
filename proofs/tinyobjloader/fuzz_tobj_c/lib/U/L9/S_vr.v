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
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition vr_entry : Z := 0x167f8.
Definition vr_ret : Z := 0x16874.

Definition thunk_alloc : Z := 0x13928.
Definition thunk_calloc : Z := 0x13934.
Definition thunk_free : Z := 0x13948.

Definition vV : sv := SVar 12.  Definition vW : sv := SVar 13.  Definition vA : sv := SVar 14.
Definition vD : sv := SVar 15.  Definition vC : sv := SVar 16.  Definition vK : sv := SVar 17.
Definition vE : sv := SVar 18.  Definition vDp : sv := SVar 19.
Definition vDn : sv := SVar 140.  Definition vKn : sv := SVar 141.

Definition spo (k : Z) : sv := SAlu ALU_ADD (SVar 10) (SLit k).
Definition kbytes (k : sv) : sv := SMd M_MUL vE k.
Definition two47 : Z := 2 ^ 47.
Definition two48 : Z := 2 ^ 48.
Definition hiA : Z := 140737479966720.
Definition loS : Z := 140735332483072.

Definition c8 (o : Z) (v : sv) : cell := mkCell (SLit o) 8 v.

Definition base_facts : list sprop :=
  [ SPAlign 10 4;
    SPBranch BC_GE (SLit (-832)) vDp;
    SPBranch BC_GE vDp (SLit (- 2 ^ 40));
    SPUle (SVar 30) (SAlu ALU_ADD (spo (-32)) vDp);
    SPUle (SVar 30) (SVar 10);
    SPUle (SVar 10) (SLit two47);
    SPUle vC vK;
    SPUle (kbytes vK) (SLit two47);
    SPUle vK (SLit two47);
    SPUle (SLit 1) vE;
    SPUle vE (SLit 4096);
    SPUle (SVar 30) vV;
    SPUle vV (SLit two47);
    SPUle (SVar 30) vA;
    SPUle vA (SLit two47);
    SPUle vD (SLit two47);
    SPUle vW (SLit two48);
    SPUle (SLit loS) (SVar 30);
    SPUle (SVar 30) (SLit hiA);
    SPAlign 12 3;
    SPAlign 14 3 ].

Definition O_F (cells : list cell) : sobj := mkObj (SVar 10) (SLit (-32)) (SLit 0) cells DUnknown.
Definition O_D : sobj := mkObj (spo (-32)) vDp (SLit 0) [] DUnknown.
Definition O_vec (d c k e : sv) : sobj :=
  mkObj vV (SLit 0) (SLit 32) [c8 0 d; c8 8 c; c8 16 k; c8 24 e] DUnknown.
Definition al_cells : list cell :=
  [c8 0 (SLit thunk_alloc); c8 8 (SLit thunk_calloc); c8 16 (SLit 0);
   c8 24 (SLit thunk_free); c8 32 (SLit 0); c8 40 (SLit 0)].
Definition O_al : sobj := mkObj vA (SLit 0) (SLit 48) al_cells DUnknown.
Definition O_data (d bytes : sv) : sobj := mkObj d (SLit 0) bytes [] DUnknown.

Definition Pre_vr : sstate :=
  mkSS vr_entry pre_regs pre_fregs FcsrFrm0 None
    [O_F []; O_D; O_vec vD vC vK vE; O_al; O_data vD (kbytes vK)]
    base_facts NF false.

Definition post_objs (d k : sv) : list sobj :=
  [O_F []; O_D; O_vec d vC k vE; O_al; O_data d (kbytes k)].

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
    SPUle (kbytes vKn) (SLit hiA);
    SPUle (SAlu ALU_ADD vDn (kbytes vKn)) (SLit hiA);
    SPUle vKn (SLit hiA) ].

Definition P_grown : sstate :=
  mkSS vr_ret (setregs (post_regs NF) [(10%nat, SLit 1)]) pre_fregs FcsrFrm0 None
    [O_D; O_data vDn (kbytes vKn); O_F []; O_vec vDn vC vKn vE; O_al]
    (grown_facts ++ base_facts) 142 false.

Definition tv0 : list (sv * sv) := [(vD, kbytes vK)].
Definition tv_post : list (sv * sv) := [(vDn, kbytes vKn)].

Definition P0_vr (r : valuation) : Prop :=
  bv_unsigned (rw r 17) <> 0 -> bv_unsigned (rw r 15) <> 0.

Definition PD_vr : list (sstate * list (sv * sv)) :=
  [(P_keep, tv0); (P_fail, tv0); (P_grown, tv_post)].

Definition Posts_vr (Kc : list event -> Model -> Prop) (FB : list (Z * Z)) : list (sstate * jpost) :=
  PostsC segsU C_U Kc (fun _ => P0_vr) PD_vr FB.

Definition vr_stmt_U : Prop :=
  forall (ok : world -> Prop) (Kc : list event -> Model -> Prop) (FB : list (Z * Z)) (rho0 : valuation),
    ok_sideK segsU ok Kc -> malloc_laws segsU C_U -> malloc_contracts segsU C_U EC_U ->
    triple segsU ok (SPJ segsU (JG_pre segsU C_U Kc P0_vr FB tv0) Pre_vr rho0)
      (LQP segsU NF rho0 (Posts_vr Kc FB)).

Definition vr_ex_stmt_U : Prop :=
  forall (Kc : list event -> Model -> Prop) (FB : list (Z * Z)) (rho0 : valuation),
    vm_insensitive Kc -> malloc_laws segsU C_U -> malloc_contracts_ex segsU C_U EC_U ->
    etriple segsU (SPJ segsU (JG_pre segsU C_U Kc P0_vr FB tv0) Pre_vr rho0)
      (LQP segsU NF rho0 (Posts_vr Kc FB)).
