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
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P Require Lib_finalize__G1.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Module FD := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_finalize__G1.Lib_finalize_shape_defs.

Definition fs_entry : Z := 0x152cc.
Definition fs_ret : Z := 0x15838.
Definition FR : Z := 192.

Definition sp1 : sv := FD.spo (- FR).
Definition sp2 : sv := SAlu ALU_ADD sp1 (SLit (-48)).
Definition dlo : sv := SAlu ALU_ADD FD.vDp (SLit 48).
Definition two47 : Z := 2 ^ 47.
Definition hiA : Z := S_vr.hiA.
Definition loS : Z := S_vr.loS.

Definition O_F (cells : list cell) : sobj := mkObj (SVar 10) (SLit (- FR)) (SLit 0) cells DUnknown.
Definition O_AF : sobj := mkObj sp1 (SLit (-48)) (SLit 0) [] DUnknown.
Definition O_DD : sobj := mkObj sp2 dlo (SLit 0) [] DUnknown.
Definition O_al : sobj := mkObj FD.xAL (SLit 0) (SLit 48) S_vr.al_cells DUnknown.
Definition O_ar (hd : sv) : sobj := mkObj FD.xAR (SLit 0) (SLit 64) (S_aa.ar_cells hd) DUnknown.

Definition objs (fcells : list cell) (err hp hd : sv) (v : FD.vecs) : list sobj :=
  [O_F fcells; O_AF; O_DD; FD.P_alloc; FD.P_hdr; FD.P_caps; FD.P_st err;
   FD.V 448 (FD.v_sh v) 128; FD.P_cur hp;
   FD.V 496 (FD.v_mi v) 12; FD.V 528 (FD.v_fv v) 4; FD.V 560 (FD.v_mm v) 4; FD.V 592 (FD.v_sg v) 4;
   FD.V 624 (FD.v_li v) 12; FD.V 656 (FD.v_lc v) 4; FD.V 688 (FD.v_pi v) 12;
   FD.P_ff; FD.Vdead 1160 56; FD.Vdead 1192 48; FD.Vdead 1224 128;
   O_al; O_ar hd;
   FD.O_data (FD.v_mi v) 12; FD.O_data (FD.v_fv v) 4; FD.O_data (FD.v_mm v) 4; FD.O_data (FD.v_sg v) 4;
   FD.O_data (FD.v_li v) 12; FD.O_data (FD.v_lc v) 4; FD.O_data (FD.v_pi v) 12; FD.O_data (FD.v_sh v) 128].

Definition base_facts : list sprop :=
  [ SPAlign 10 4;
    SPBranch BC_GE (SLit (-880)) FD.vDp;
    SPBranch BC_GE FD.vDp (SLit (- 2 ^ 40));
    SPUle (SVar 30) (SAlu ALU_ADD sp1 FD.vDp);
    SPUle (SVar 30) (SAlu ALU_ADD sp2 dlo);
    SPUle (SVar 30) sp2;
    SPUle (SVar 30) sp1;
    SPUle sp1 (SLit two47);
    SPUle (SAlu ALU_ADD (SVar 30) (SLit (FR + 48))) (SVar 10);
    SPUle (SVar 10) (SLit two47);
    SPUle (SVar 30) FD.vb;
    SPUle FD.vb (SLit (two47 - 2048));
    SPAlign 12 3;
    SPUle (SVar 30) FD.xAL;
    SPUle FD.xAL (SLit two47);
    SPAlign 100 3;
    SPUle (SLit 4096) FD.xAR;
    SPUle (SAlu ALU_ADD FD.xAR (SLit 64)) (SLit hiA);
    SPUle FD.xAR (SLit hiA);
    SPAlign 101 4;
    SPUle FD.xHASPRIM (SLit 1);
    SPUle FD.xCURNAME (SLit two47);
    SPUle (SLit loS) (SVar 30);
    SPUle (SVar 30) (SLit hiA);
    SPUle (SLit loS) (SVar 10) ].

Definition pre_facts : list sprop := FD.hd_facts FD.xHD ++ base_facts ++ FD.vecs_facts FD.vs0.

Definition Pre_fs : sstate :=
  mkSS fs_entry pre_regs pre_fregs FcsrFrm0 None (objs [] FD.xERR FD.xHASPRIM FD.xHD FD.vs0) pre_facts FD.NP false.

Definition HP (a0 err hp hd : sv) (v : FD.vecs) (facts : list sprop) : sstate :=
  mkSS fs_ret (FD.post_regs_fs a0) pre_fregs FcsrFrm0 None (objs [] err hp hd v)
    (facts ++ FD.hd_facts hd ++ base_facts ++ FD.vecs_facts v) FD.NPOST false.

Definition P_nop : sstate := HP (SLit 1) FD.xERR FD.xHASPRIM FD.xHD FD.vs0 [].
Definition P_ok : sstate := HP (SLit 1) FD.xERR (SLit 0) FD.qH FD.vsOK [].
Definition P_fail : sstate := HP (SLit 0) FD.xERR FD.xHASPRIM FD.qH FD.vsFq [].
Definition P_failz : sstate :=
  HP FD.errw FD.qERR FD.xHASPRIM FD.qH FD.vsFq [SPBranch BC_EQ FD.errw (SLit 0)].

Definition tv0 : list (sv * sv) := FD.tv0.
Definition tvOK : list (sv * sv) := FD.tvOK.
Definition ahd : amode := FD.ahd.
Definition amq : amode := FD.amq.

Definition P0_fs (FB : list (Z * Z)) (r : valuation) : Prop := True.

Definition PDA_fs : list (sstate * (list (sv * sv) * amode)) :=
  [(P_nop, (tv0, ahd)); (P_ok, (tvOK, amq)); (P_fail, (tv0, amq)); (P_failz, (tv0, amq))].

Definition Posts_fs (Kc : list event -> Model -> Prop) (FB : list (Z * Z)) : list (sstate * jpost) :=
  PostsCA segsU C_U Kc P0_fs PDA_fs FB.

Definition fs_stmt_U : Prop :=
  forall (ok : world -> Prop) (Kc : list event -> Model -> Prop) (FB : list (Z * Z)) (rho0 : valuation),
    ok_sideK segsU ok Kc -> malloc_laws segsU C_U -> malloc_contracts segsU C_U EC_U ->
    triple segsU ok (SPJ segsU (JGA_pre segsU C_U Kc (P0_fs FB) FB tv0 ahd) Pre_fs rho0)
      (LQP segsU FD.NP rho0 (Posts_fs Kc FB)).

Definition fs_ex_stmt_U : Prop :=
  forall (Kc : list event -> Model -> Prop) (FB : list (Z * Z)) (rho0 : valuation),
    vm_insensitive Kc -> malloc_laws segsU C_U -> malloc_contracts_ex segsU C_U EC_U ->
    etriple segsU (SPJ segsU (JGA_pre segsU C_U Kc (P0_fs FB) FB tv0 ahd) Pre_fs rho0)
      (LQP segsU FD.NP rho0 (Posts_fs Kc FB)).
