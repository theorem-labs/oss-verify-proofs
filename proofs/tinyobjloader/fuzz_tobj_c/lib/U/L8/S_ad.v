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
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L9 Require S_vr S_aa.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition ad_entry : Z := 0x1cc20.
Definition ad_ret : Z := 0x1cc8c.

Definition vAR : sv := SVar 12.  Definition vSRC : sv := SVar 13.  Definition vSZ : sv := SVar 14.
Definition vHD : sv := SVar 15.  Definition vLS : sv := SVar 16.  Definition vDp : sv := SVar 19.

Definition spo (k : Z) : sv := SAlu ALU_ADD (SVar 10) (SLit k).
Definition sp1 : sv := spo (-32).
Definition sp2 : sv := spo (-80).
Definition dlo : sv := SAlu ALU_ADD vDp (SLit 48).
Definition two47 : Z := 2 ^ 47.
Definition hiA : Z := S_vr.hiA.
Definition loS : Z := S_vr.loS.

Definition base_facts : list sprop :=
  [ SPAlign 10 4;
    SPBranch BC_GE (SLit (-832)) vDp;
    SPBranch BC_GE vDp (SLit (- 2 ^ 40));
    SPBranch BC_GE (SLit (-784)) dlo;
    SPBranch BC_GE dlo (SLit (- 2 ^ 40));
    SPUle (SVar 30) (SAlu ALU_ADD sp2 dlo);
    SPUle (SVar 30) sp2;
    SPUle (SVar 30) sp1;
    SPUle (SVar 30) (SVar 10);
    SPUle sp1 (SLit two47);
    SPUle (SVar 10) (SLit two47);
    SPUle (SLit 1) vSZ;
    SPUle vSZ vLS;
    SPUle vSZ (SLit (2 ^ 40));
    SPUle vLS (SLit two47);
    SPUle (SLit 1) vSRC;
    SPUle vSRC (SLit two47);
    SPUle (SLit 4096) vAR;
    SPUle (SAlu ALU_ADD vAR (SLit 64)) (SLit hiA);
    SPUle vAR (SLit hiA);
    SPAlign 12 4;
    SPUle vHD (SLit hiA);
    SPUle (SLit loS) (SVar 30);
    SPUle (SVar 30) (SLit hiA) ].

Definition O_F (cells : list cell) : sobj := mkObj (SVar 10) (SLit (-32)) (SLit 0) cells DUnknown.
Definition O_AF : sobj := mkObj sp1 (SLit (-48)) (SLit 0) [] DUnknown.
Definition O_DD : sobj := mkObj sp2 dlo (SLit 0) [] DUnknown.
Definition O_ar (hd : sv) : sobj := mkObj vAR (SLit 0) (SLit 64) (S_aa.ar_cells hd) DUnknown.
Definition O_src : sobj := mkObj vSRC (SLit 0) vLS [] DUnknown.

Definition post_objs (hd : sv) : list sobj := [O_F []; O_AF; O_DD; O_ar hd; O_src].

Definition Pre_ad : sstate :=
  mkSS ad_entry pre_regs pre_fregs FcsrFrm0 None (post_objs vHD) base_facts NF false.

Definition P_fail : sstate :=
  mkSS ad_ret (setregs (post_regs NF) [(10%nat, SLit 0)]) pre_fregs FcsrFrm0 None
    (post_objs vHD) base_facts NPOSTM false.

Definition ok_facts : list sprop :=
  [ SPUle (SLit 4096) (SVar 140);
    SPUle (SVar 140) (SLit hiA);
    SPUle (SLit 4096) (SVar 141);
    SPUle (SVar 141) (SLit hiA) ].

Definition P_ok : sstate :=
  mkSS ad_ret (setregs (post_regs NF) [(10%nat, SVar 140)]) pre_fregs FcsrFrm0 None
    (post_objs (SVar 141)) (ok_facts ++ base_facts) 142 false.

Definition tv0 : list (sv * sv) := [(vAR, SLit 64)].
Definition ahd : amode := AHead vHD.
Definition am_ok : amode := AHead (SVar 141).

Definition P0_ad (FB : list (Z * Z)) (r : valuation) : Prop :=
  exists b n, In (b, n) FB /\ b <= bv_unsigned (rw r 13) /\
    bv_unsigned (rw r 13) + bv_unsigned (rw r 16) <= b + n.

Definition PDA_ad : list (sstate * (list (sv * sv) * amode)) :=
  [(P_fail, (tv0, ahd)); (P_ok, (tv0, am_ok))].

Definition Posts_ad (Kc : list event -> Model -> Prop) (FB : list (Z * Z)) : list (sstate * jpost) :=
  PostsCA segsU C_U Kc P0_ad PDA_ad FB.

Definition ad_stmt_U : Prop :=
  forall (ok : world -> Prop) (Kc : list event -> Model -> Prop) (FB : list (Z * Z)) (rho0 : valuation),
    ok_sideK segsU ok Kc -> malloc_laws segsU C_U -> malloc_contracts segsU C_U EC_U ->
    triple segsU ok (SPJ segsU (JGA_pre segsU C_U Kc (P0_ad FB) FB tv0 ahd) Pre_ad rho0)
      (LQP segsU NF rho0 (Posts_ad Kc FB)).

Definition ad_ex_stmt_U : Prop :=
  forall (Kc : list event -> Model -> Prop) (FB : list (Z * Z)) (rho0 : valuation),
    vm_insensitive Kc -> malloc_laws segsU C_U -> malloc_contracts_ex segsU C_U EC_U ->
    etriple segsU (SPJ segsU (JGA_pre segsU C_U Kc (P0_ad FB) FB tv0 ahd) Pre_ad rho0)
      (LQP segsU NF rho0 (Posts_ad Kc FB)).
