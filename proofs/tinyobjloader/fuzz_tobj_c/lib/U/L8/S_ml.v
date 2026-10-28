From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundR.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Init.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L9 Require S_vr S_da.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition ml_entry : Z := 0x1a6b4.
Definition ml_exit : Z := S_da.da_ret.

Definition vb : sv := SVar 12.
Definition xAL : sv := SVar 15.  Definition xAR : sv := SVar 16.  Definition xCFG : sv := SVar 17.
Definition xLINE : sv := SVar 18.  Definition vERR : sv := SVar 19.
Definition two47 : Z := 2 ^ 47.

Definition c8 (o : Z) (v : sv) : cell := mkCell (SLit o) 8 v.
Definition c4 (o : Z) (v : sv) : cell := mkCell (SLit o) 4 v.
Definition c1 (o : Z) (v : sv) : cell := mkCell (SLit o) 1 v.
Definition piece (lo hi : Z) (cells : list cell) : sobj := mkObj vb (SLit lo) (SLit hi) cells DUnknown.

Definition O_F : sobj := mkObj (SVar 10) (SLit (-112)) (SLit 0) [] DUnknown.
Definition P_alloc : sobj := piece 0 8 [c8 0 xAL].
Definition P_hdr : sobj := piece 8 32 [c8 8 xAR; c8 16 (SLit 0); c8 24 xCFG].
Definition P_st : sobj := piece 96 120 [c4 96 vERR; c8 104 xLINE; c1 112 (SLit 1)].
Definition O_cfg : sobj :=
  mkObj xCFG (SLit 0) (SLit 144) [mkCell (SLit 48) 4 (SLit 65793); mkCell (SLit 56) 4 (SLit 4294967295)] DZero.

Definition objs_ml : list sobj := [O_F; P_alloc; P_hdr; P_st; O_cfg].

Definition base_facts : list sprop :=
  [ SPAlign 10 4;
    SPUle (SVar 30) (SAlu ALU_ADD (SVar 10) (SLit (-112)));
    SPUle (SVar 30) (SVar 10);
    SPUle (SVar 10) (SLit two47);
    SPAlign 12 3;
    SPUle (SVar 30) vb;
    SPUle vb (SLit (two47 - 2048));
    SPAlign 17 3;
    SPUle (SVar 30) xCFG;
    SPUle xCFG (SLit two47);
    SPUle (SLit S_vr.loS) (SVar 30);
    SPUle (SVar 30) (SLit S_vr.hiA) ].

Definition Pre_ml : sstate :=
  mkSS ml_entry pre_regs pre_fregs FcsrFrm0 None objs_ml base_facts NF false.

Definition P_ml : sstate :=
  mkSS ml_exit (setregs (post_regs NF) [(10%nat, SLit 0)]) pre_fregs FcsrFrm0 None objs_ml base_facts NPOST false.

Definition Posts_ml : list leaf := [mkLeaf P_ml RsSymJump].

Definition ml_stmt_U : Prop :=
  forall (ok : world -> Prop) (K : list event -> Model -> Prop) (rho : valuation),
    ok_frame segsU ok K -> triple segsU ok (SP segsU K Pre_ml rho) (LQ segsU K NF rho Posts_ml).

Definition ml_ex_stmt_U : Prop :=
  forall (K : list event -> Model -> Prop) (rho : valuation),
    etriple segsU (SP segsU K Pre_ml rho) (LQ segsU K NF rho Posts_ml).
