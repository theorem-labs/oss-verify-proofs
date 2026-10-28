From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Init.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Module MatFindAddrU.
  Definition mf_entry : Z := 0x18d80.
  Definition mf_ret : Z := 0x18e60.
End MatFindAddrU.
Import MatFindAddrU.

Definition vb : sv := SVar 12.
Definition two47 : Z := 2 ^ 47.

Definition mvec (o e : Z) : sobj :=
  mkObj vb (SLit o) (SLit (o + 32))
    [mkCell (SLit o) 8 (SLit 0); mkCell (SLit (o + 8)) 8 (SLit 0);
     mkCell (SLit (o + 16)) 8 (SLit 0); mkCell (SLit (o + 24)) 8 (SLit e)] DUnknown.

Definition mf_objs : list sobj := [mvec 352 8; mvec 384 4].

Definition mf_facts : list sprop :=
  [SPAlign 12 3; SPUle (SLit 4096) vb; SPUle (SAlu ALU_ADD vb (SLit 1304)) (SLit two47)].

Definition Pre_mf : sstate :=
  mkSS mf_entry pre_regs pre_fregs FcsrFrm0 None mf_objs mf_facts NF false.

Definition P_mf : sstate :=
  mkSS mf_ret (setregs (post_regs NF) [(10%nat, SLit (2 ^ 64 - 1))]) pre_fregs FcsrFrm0 None
    mf_objs mf_facts NPOST false.

Definition Posts_mf : list leaf := [mkLeaf P_mf RsSymJump].

Definition mat_find_sum_stmt_U : Prop :=
  forall (ok : world -> Prop) (K : list event -> Model -> Prop) (rho : valuation),
    ok_frame U.Init.segsU ok K ->
    triple U.Init.segsU ok (SP U.Init.segsU K Pre_mf rho) (LQ U.Init.segsU K NF rho Posts_mf).

Definition mat_find_sum_ex_stmt_U : Prop :=
  forall (K : list event -> Model -> Prop) (rho : valuation),
    etriple U.Init.segsU (SP U.Init.segsU K Pre_mf rho) (LQ U.Init.segsU K NF rho Posts_mf).
