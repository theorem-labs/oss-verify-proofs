From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocModel MallocInv MallocLayout MallocIface MallocLaws.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundR SymSummary.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Contract.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv TobjJV TobjJVA.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Init.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L9 Require S_vr.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition aa_entry : Z := 0x18f80.
Definition aa_ret : Z := 0x190c4.

Definition vAR : sv := SVar 12.  Definition vSZ : sv := SVar 13.
Definition vHD : sv := SVar 15.  Definition vDp : sv := SVar 19.
Definition vP : sv := SVar 140.  Definition vH : sv := SVar 141.  Definition vNX : sv := SVar 142.
Definition vCAP : sv := SVar 143.  Definition vU : sv := SVar 144.

Definition spo (k : Z) : sv := SAlu ALU_ADD (SVar 10) (SLit k).
Definition two47 : Z := 2 ^ 47.
Definition hiA : Z := S_vr.hiA.
Definition loS : Z := S_vr.loS.

Definition base_facts : list sprop :=
  [ SPAlign 10 4;
    SPBranch BC_GE (SLit (-784)) vDp;
    SPBranch BC_GE vDp (SLit (- 2 ^ 40));
    SPUle (SVar 30) (SAlu ALU_ADD (spo (-48)) vDp);
    SPUle (SVar 30) (spo (-48));
    SPUle (SVar 30) (SVar 10);
    SPUle (SVar 10) (SLit two47);
    SPUle vSZ (SLit two47);
    SPUle (SLit 4096) vAR;
    SPUle (SAlu ALU_ADD vAR (SLit 64)) (SLit hiA);
    SPUle vAR (SLit hiA);
    SPAlign 12 4;
    SPUle vHD (SLit hiA);
    SPUle (SLit loS) (SVar 30);
    SPUle (SVar 30) (SLit hiA) ].

Definition O_F (cells : list cell) : sobj := mkObj (SVar 10) (SLit (-48)) (SLit 0) cells DUnknown.
Definition O_D : sobj := mkObj (spo (-48)) vDp (SLit 0) [] DUnknown.
Definition ar_cells (hd : sv) : list cell :=
  S_vr.al_cells ++ [S_vr.c8 48 hd; S_vr.c8 56 (SLit 65536)].
Definition O_ar (hd : sv) : sobj := mkObj vAR (SLit 0) (SLit 64) (ar_cells hd) DUnknown.
Definition O_hdr (hd nx cap u : sv) : sobj :=
  mkObj hd (SLit 0) (SLit 24) [S_vr.c8 0 nx; S_vr.c8 8 cap; S_vr.c8 16 u] DUnknown.
Definition O_slot (p : sv) : sobj := mkObj p (SLit 0) vSZ [] DUnknown.

Definition pre_regs_aa (al : Z) : list sv := setregs pre_regs [(12%nat, SLit al)].

Definition Pre_aa (al : Z) : sstate :=
  mkSS aa_entry (pre_regs_aa al) pre_fregs FcsrFrm0 None [O_F []; O_D; O_ar vHD] base_facts NF false.

Definition P_fail : sstate :=
  mkSS aa_ret (setregs (post_regs NF) [(10%nat, SLit 0)]) pre_fregs FcsrFrm0 None
    [O_F []; O_D; O_ar vHD] base_facts NPOSTM false.

Definition al_facts (al : Z) : list sprop := if Z.eqb al 16 then [SPAlign 140 4] else [].

Definition ok_facts (al : Z) : list sprop :=
  al_facts al ++
  [ SPUle vU vCAP;
    SPUle vCAP (SLit hiA);
    SPUle vCAP (SLit (two47 + 65536));
    SPAlign 141 4;
    SPUle (SLit 4096) vH;
    SPUle (SAlu ALU_ADD (SAlu ALU_ADD vH (SLit 32)) vCAP) (SLit hiA);
    SPUle (SAlu ALU_ADD vH (SLit 24)) vP;
    SPUle (SAlu ALU_ADD vP vSZ) (SAlu ALU_ADD (SAlu ALU_ADD vH (SLit 32)) vCAP);
    SPUle (SLit 4096) vP;
    SPUle vP (SLit hiA);
    SPUle (SAlu ALU_ADD vP vSZ) (SLit hiA);
    SPUle vH (SLit hiA) ].

Definition P_ok (al : Z) : sstate :=
  mkSS aa_ret (setregs (post_regs NF) [(10%nat, vP)]) pre_fregs FcsrFrm0 None
    [O_F []; O_D; O_ar vH; O_hdr vH vNX vCAP vU; O_slot vP] (ok_facts al ++ base_facts) 145 false.

Definition tv0 : list (sv * sv) := [(vAR, SLit 64)].

Definition P0_aa (FB : list (Z * Z)) (r : valuation) : Prop := True.

Definition PDA_aa (al : Z) : list (sstate * (list (sv * sv) * amode)) :=
  [(P_fail, (tv0, AHead vHD)); (P_ok al, (tv0, AOpen vH vNX vCAP [(vP, vSZ)]))].

Definition Posts_aa (al : Z) (Kc : list event -> Model -> Prop) (FB : list (Z * Z)) : list (sstate * jpost) :=
  PostsCA segsU C_U Kc P0_aa (PDA_aa al) FB.

Definition aa_stmt_U : Prop :=
  forall (al : Z), (al = 1 \/ al = 16) ->
  forall (ok : world -> Prop) (Kc : list event -> Model -> Prop) (FB : list (Z * Z)) (rho0 : valuation),
    ok_sideK segsU ok Kc -> malloc_laws segsU C_U -> malloc_contracts segsU C_U EC_U ->
    triple segsU ok (SPJ segsU (JGA_pre segsU C_U Kc (P0_aa FB) FB tv0 (AHead vHD)) (Pre_aa al) rho0)
      (LQP segsU NF rho0 (Posts_aa al Kc FB)).

Definition aa_ex_stmt_U : Prop :=
  forall (al : Z), (al = 1 \/ al = 16) ->
  forall (Kc : list event -> Model -> Prop) (FB : list (Z * Z)) (rho0 : valuation),
    vm_insensitive Kc -> malloc_laws segsU C_U -> malloc_contracts_ex segsU C_U EC_U ->
    etriple segsU (SPJ segsU (JGA_pre segsU C_U Kc (P0_aa FB) FB tv0 (AHead vHD)) (Pre_aa al) rho0)
      (LQP segsU NF rho0 (Posts_aa al Kc FB)).
