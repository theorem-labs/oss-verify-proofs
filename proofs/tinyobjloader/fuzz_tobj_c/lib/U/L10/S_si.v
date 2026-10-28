From Stdlib Require Import ZArith NArith List Bool PArith.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundR SymCFG.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Init.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P Require Lib_scan__G1.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Module ScanIntAddrU.
  Definition siU_entry : Z := 0x1a54c.
  Definition siU_ret_num : Z := 0x1a680.
  Definition siU_ret_none : Z := 0x1a688.
End ScanIntAddrU.
Import ScanIntAddrU.

Module SI := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_scan__G1.Lib_scan_int.

Definition Pre_si_U : sstate :=
  mkSS siU_entry (setregs pre_regs [(11%nat, SI.pB SI.vE)]) pre_fregs FcsrFrm0 None
    [SI.O_pp (SI.pB SI.vI); SI.O_txt []; SI.O_out []] SI.base_facts NF false.

Definition P_none_U : sstate :=
  add_facts SI.F_si
    (mkSS siU_ret_none (post_regs NF) pre_fregs FcsrFrm0 None
       [SI.O_pp (SI.pB SI.v141); SI.O_txt []; SI.O_out []] SI.base_facts 143 false).

Definition P_num_U : sstate :=
  add_facts SI.F_si
    (mkSS siU_ret_num (post_regs NF) pre_fregs FcsrFrm0 None
       [SI.O_pp (SI.pB SI.v141); SI.O_txt []; SI.O_out [mkCell (SLit 0) 4 (SVar 142)]] SI.base_facts 143 false).

Definition Posts_si_U : list leaf := [mkLeaf P_none_U RsSymJump; mkLeaf P_num_U RsSymJump].

Definition scan_int_sum_stmt_U : Prop :=
  forall ok K rho, ok_frame segsU ok K ->
    triple segsU ok (SP segsU K Pre_si_U rho) (LQ segsU K NF rho Posts_si_U).

Definition scan_int_sum_ex_stmt_U : Prop :=
  forall K rho, etriple segsU (SP segsU K Pre_si_U rho) (LQ segsU K NF rho Posts_si_U).
