From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundR.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Init.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition da_entry : Z := 0x1bf5c.
Definition da_ret : Z := 0x1c0c8.

Definition O_F (cells : list cell) : sobj := mkObj (SVar 10) (SLit (-64)) (SLit 0) cells DUnknown.

Definition Pre_da : sstate :=
  mkSS da_entry (setregs pre_regs [(10%nat, SLit 0)]) pre_fregs FcsrFrm0 None [O_F []] [] NF false.

Definition P_da : sstate :=
  mkSS da_ret (post_regs NF) pre_fregs FcsrFrm0 None [O_F []] [] NPOST false.

Definition Posts_da : list leaf := [mkLeaf P_da RsSymJump].

Definition da_stmt_U : Prop :=
  forall (ok : world -> Prop) (K : list event -> Model -> Prop) (rho : valuation),
    ok_frame segsU ok K -> triple segsU ok (SP segsU K Pre_da rho) (LQ segsU K NF rho Posts_da).

Definition da_ex_stmt_U : Prop :=
  forall (K : list event -> Model -> Prop) (rho : valuation),
    etriple segsU (SP segsU K Pre_da rho) (LQ segsU K NF rho Posts_da).
