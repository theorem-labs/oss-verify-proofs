From Stdlib Require Import ZArith NArith List Bool PArith.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundR.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Init.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P Require Lib_next_token.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Module NextTokenAddrU.
  Definition ntU_entry : Z := 0x18298.
  Definition ntU_L1 : Z := 0x182c0.
  Definition ntU_L2 : Z := 0x18300.
  Definition ntU_ret_nf : Z := 0x182dc.
  Definition ntU_ret_found : Z := 0x18348.
End NextTokenAddrU.
Import NextTokenAddrU.

Module NT := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_next_token.

Definition Pre_nt_U : sstate :=
  mkSS ntU_entry pre_regs pre_fregs FcsrFrm0 None
    [NT.O_cur (NT.pB NT.vI); NT.O_txt []; NT.O_tok []; NT.O_tl []] NT.base_facts NF false.

Definition P_nf_U : sstate :=
  mkSS ntU_ret_nf (setregs (post_regs NF) [(10%nat, SLit 0); (14%nat, NT.pB NT.v141)]) pre_fregs FcsrFrm0 None
    [NT.O_cur (NT.pB NT.v141); NT.O_txt []; NT.O_tok []; NT.O_tl []] (NT.F_nf ++ NT.base_facts) 144 false.

Definition P_found_U : sstate :=
  mkSS ntU_ret_found (setregs (post_regs NF) [(10%nat, SLit 1); (14%nat, NT.pB NT.v141)]) pre_fregs FcsrFrm0 None
    [NT.O_cur (NT.pB NT.v143); NT.O_txt []; NT.O_tok [mkCell (SLit 0) 8 (NT.pB NT.v141)];
     NT.O_tl [mkCell (SLit 0) 8 NT.v142]] (NT.F_found ++ NT.base_facts) 144 false.

Definition Posts_nt_U : list leaf := [mkLeaf P_nf_U RsSymJump; mkLeaf P_found_U RsSymJump].

Definition next_token_sum_stmt_U : Prop :=
  forall ok K rho, ok_frame segsU ok K ->
    triple segsU ok (SP segsU K Pre_nt_U rho) (LQ segsU K NF rho Posts_nt_U).

Definition next_token_sum_ex_stmt_U : Prop :=
  forall K rho, etriple segsU (SP segsU K Pre_nt_U rho) (LQ segsU K NF rho Posts_nt_U).
