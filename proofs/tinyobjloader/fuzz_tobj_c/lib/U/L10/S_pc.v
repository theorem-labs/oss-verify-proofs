From Stdlib Require Import ZArith NArith List Bool PArith.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundR.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Init.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P Require Lib_parse_corner.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Module ParseCornerAddrU.
  Definition pcU_entry : Z := 0x18abc.
  Definition pcU_ret : Z := 0x18c64.
  Definition fixU_entry : Z := 0x1c270.
End ParseCornerAddrU.
Import ParseCornerAddrU.

Module PC := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_parse_corner.

Definition O_stk_U (cells : list cell) : sobj := mkObj (SVar 10) (SLit (-64)) (SLit 0) cells DUnknown.
Definition O_out12_U : sobj := mkObj PC.vOut (SLit 0) (SLit 12) [] DUnknown.

Definition pc_facts_U : list sprop :=
  PC.base_facts ++
  [SPUle (SVar 14) (SLit PC.two47); SPUle (SVar 33) (SLit PC.two47); SPUle (SVar 34) (SLit PC.two47);
   SPAlign 10 4; SPUle (SLit 65536) (SVar 10); SPUle (SVar 10) (SLit PC.two47);
   SPUle PC.vOut (SLit PC.two47)].

Definition Pre_pc_U : sstate :=
  mkSS pcU_entry (setregs pre_regs [(10%nat, PC.pB PC.vT)]) pre_fregs FcsrFrm0 None
    [O_stk_U []; PC.O_txt []; O_out12_U] pc_facts_U NF false.

Definition P_ret_U : sstate :=
  mkSS pcU_ret (setregs (post_regs NF) [(10%nat, SVar 140)]) pre_fregs FcsrFrm0 None
    [O_stk_U []; PC.O_txt []; O_out12_U] pc_facts_U 150 false.

Definition Posts_pc_U : list leaf := [mkLeaf P_ret_U RsSymJump].

Definition parse_corner_sum_stmt_U : Prop :=
  forall ok K rho, ok_frame segsU ok K ->
    triple segsU ok (SP segsU K Pre_pc_U rho) (LQ segsU K NF rho Posts_pc_U).

Definition parse_corner_sum_ex_stmt_U : Prop :=
  forall K rho, etriple segsU (SP segsU K Pre_pc_U rho) (LQ segsU K NF rho Posts_pc_U).
