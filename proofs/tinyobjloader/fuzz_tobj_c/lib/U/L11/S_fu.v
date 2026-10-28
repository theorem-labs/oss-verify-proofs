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
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Module FuAddr.
  Definition fu_entry : Z := 0x158f4.
  Definition fu_ret : Z := 0x15bdc.
End FuAddr.
Import FuAddr.

Definition FR_fu : Z := 112.
Definition vb : sv := SVar 12.
Definition vUD : sv := SVar 15.
Definition vUK : sv := SVar 16.
Definition c8 (o : Z) (v : sv) : cell := mkCell (SLit o) 8 v.

Definition O_fstk : sobj := mkObj (SVar 10) (SLit (- FR_fu)) (SLit 0) [] DUnknown.
Definition O_unk : sobj :=
  mkObj vb (SLit 416) (SLit 448) [c8 416 vUD; c8 424 (SLit 0); c8 432 vUK; c8 440 (SLit 24)] DUnknown.

Definition fu_facts : list sprop :=
  [SPAlign 12 3; SPUle (SLit 4096) vb; SPUle (SAlu ALU_ADD vb (SLit 1304)) (SLit (2 ^ 47))].

Definition Pre_fu_U : sstate :=
  mkSS fu_entry pre_regs pre_fregs FcsrFrm0 None [O_fstk; O_unk] fu_facts NF false.

Definition P_fu_U : sstate :=
  mkSS fu_ret (setregs (post_regs NF) [(10%nat, SLit 0)]) pre_fregs FcsrFrm0 None [O_fstk; O_unk] fu_facts NPOST false.

Definition Posts_fu_U : list leaf := [mkLeaf P_fu_U RsSymJump].

Definition finalize_unknowns_sum_stmt_U : Prop :=
  forall ok K rho, ok_frame segsU ok K ->
    triple segsU ok (SP segsU K Pre_fu_U rho) (LQ segsU K NF rho Posts_fu_U).

Definition finalize_unknowns_sum_ex_stmt_U : Prop :=
  forall K rho, etriple segsU (SP segsU K Pre_fu_U rho) (LQ segsU K NF rho Posts_fu_U).
