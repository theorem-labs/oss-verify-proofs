From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Init.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G1.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Module ScAddr.
  Definition sc_entry : Z := 0x1ea8c.
  Definition sc_L1 : Z := 0x1eabc.
  Definition sc_ret : Z := 0x1eb58.
End ScAddr.
Import ScAddr.

Module SC := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G1.Lib_tess_scale2d.

Definition Pre_sc_U : sstate :=
  mkSS sc_entry pre_regs pre_fregs FcsrFrm0 None [SC.O_pts] SC.base_facts NF false.

Definition P_sc_U : sstate :=
  mkSS sc_ret (post_regs NF) SC.post_fregs FcsrFrm0 None [SC.O_pts] SC.base_facts SC.NXP false.

Definition Posts_sc_U : list leaf := [mkLeaf P_sc_U RsSymJump].

Definition scale2d_sum_stmt_U : Prop :=
  forall ok K rho, ok_frame segsU ok K ->
    triple segsU ok (SP segsU K Pre_sc_U rho) (LQ segsU K NF rho Posts_sc_U).

Definition scale2d_sum_ex_stmt_U : Prop :=
  forall K rho, etriple segsU (SP segsU K Pre_sc_U rho) (LQ segsU K NF rho Posts_sc_U).
