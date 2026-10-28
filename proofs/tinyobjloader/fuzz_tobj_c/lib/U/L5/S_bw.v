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

Module BwAddr.
  Definition bw_entry : Z := 0x1a690.
  Definition da_entry : Z := 0x1bf5c.
End BwAddr.
Import BwAddr.

Definition bB : sv := SVar 12.
Definition bAL : sv := SVar 15.
Definition bAR : sv := SVar 16.
Definition bW : sv := SVar 17.
Definition bCFG : sv := SVar 18.
Definition bERR : sv := SVar 19.
Definition bLINE : sv := SVar 52.
Definition bFLG : sv := SVar 53.

Definition bpiece (lo hi : Z) (cells : list cell) : sobj := mkObj bB (SLit lo) (SLit hi) cells DUnknown.

Definition bw_objs : list sobj :=
  [bpiece 0 8 [mkCell (SLit 0) 8 bAL];
   bpiece 8 32 [mkCell (SLit 8) 8 bAR; mkCell (SLit 16) 8 bW; mkCell (SLit 24) 8 bCFG];
   bpiece 96 120 [mkCell (SLit 96) 4 bERR; mkCell (SLit 104) 8 bLINE; mkCell (SLit 112) 1 bFLG]].

Definition bw_facts : list sprop := [SPAlign 12 3].

Definition Pre_bw : sstate :=
  mkSS bw_entry pre_regs pre_fregs FcsrFrm0 None bw_objs bw_facts NF false.

Definition P_bw : sstate :=
  mkSS da_entry
    (setregs (post_regs NF) [(10%nat, bW); (11%nat, bAL); (12%nat, bLINE); (13%nat, SVar 13)])
    pre_fregs FcsrFrm0 None bw_objs bw_facts NPOST false.

Definition Posts_bw : list leaf := [mkLeaf P_bw RsSymJump].

Definition bw_sum_stmt : Prop :=
  forall ok K rho, ok_frame segsU ok K ->
    triple segsU ok (SP segsU K Pre_bw rho) (LQ segsU K NF rho Posts_bw).

Definition bw_sum_ex_stmt : Prop :=
  forall K rho, etriple segsU (SP segsU K Pre_bw rho) (LQ segsU K NF rho Posts_bw).
