From Stdlib Require Import ZArith NArith List Bool PArith.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundR.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Init.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P Require Lib_scan__G1.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Module ScanDoubleAddrU.
  Definition sdU_entry : Z := 0x183d0.
  Definition sdU_ret_nan : Z := 0x18540.
  Definition sdU_ret0 : Z := 0x18898.
  Definition sdU_ret_num : Z := 0x189e4.
  Definition sdU_ret_inf : Z := 0x18a1c.
End ScanDoubleAddrU.
Import ScanDoubleAddrU.

Module SD := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_scan__G1.Lib_scan_double.

Definition two26 : Z := 2 ^ 26.

Definition base_facts_U : list sprop :=
  [SPUle SD.vI SD.vE; SPUle SD.vE SD.vL; SPUle SD.vL (SLit two26); SPUle SD.vB (SLit SD.two47); SPUle (SLit 1) SD.vB;
   SPAlign 12 3; SPAlign 14 3; SPAlign 10 4].

Definition Pre_sd_U : sstate :=
  mkSS sdU_entry (setregs pre_regs [(11%nat, SD.pB SD.vE)]) pre_fregs FcsrFrm0 None
    [SD.O_stk []; SD.O_pp (SD.pB SD.vI); SD.O_txt []; SD.O_out []] base_facts_U NF false.

Definition P_none_U : sstate :=
  mkSS sdU_ret0 (setregs (post_regs NF) [(10%nat, SLit 0)]) SD.post_fregs FcsrFrm0 None
    [SD.O_stk []; SD.O_pp (SD.pB SD.v172); SD.O_txt []; SD.O_out []] (SD.F_sd ++ SD.base_facts) SD.NXP false.

Definition P_num_U (pc : Z) : sstate := SD.P_num pc.

Definition Posts_sd_U : list leaf :=
  [mkLeaf P_none_U RsSymJump; mkLeaf (P_num_U sdU_ret_nan) RsSymJump;
   mkLeaf (P_num_U sdU_ret_num) RsSymJump; mkLeaf (P_num_U sdU_ret_inf) RsSymJump].

Definition scan_double_sum_stmt_U : Prop :=
  forall ok K rho, ok_frame segsU ok K ->
    triple segsU ok (SP segsU K Pre_sd_U rho) (LQ segsU K NF rho Posts_sd_U).

Definition scan_double_sum_ex_stmt_U : Prop :=
  forall K rho, etriple segsU (SP segsU K Pre_sd_U rho) (LQ segsU K NF rho Posts_sd_U).
