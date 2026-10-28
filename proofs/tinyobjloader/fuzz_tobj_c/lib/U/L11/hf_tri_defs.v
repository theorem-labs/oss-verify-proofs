From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymFrame SymEntail SymCFG SymSummary.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjUnbase ObjXform TobjJV.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TobjJVx.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Init.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L5 Require Import S_hf hf_defs.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L9 Require S_vr.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_defs.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition tri_K1 : Z := 0x19854.
Definition tri_ra : Z := 0x198c0.
Definition tri_K2 : Z := 0x19900.
Definition tri_J9 : Z := 0x1996c.

Definition pK : sv := pR.
Definition n3U (x : sv) : sv := SAlu ALU_ADD (SAlu ALU_SLL x (SLit 1)) x.
Definition snotU (v : sv) : sv := SAlu ALU_XOR v (SLit (2 ^ 64 - 1)).

Definition K1_regs : list (nat * sv) :=
  [(9%nat, xb 528); (10%nat, av_nv); (11%nat, am1); (12%nat, SLit 12);
   (13%nat, SAlu ALU_ADD (t_d co1) (SMd M_MUL pK (SLit 12))); (15%nat, pK); (21%nat, t_d co1);
   (22%nat, SAlu ALU_XOR (t_d co1) (SLit (2 ^ 64 - 1))); (24%nat, pA); (25%nat, am2)].

Definition K1_facts : list sprop :=
  [SPNot (SPBranch BC_EQ (t_d co1) (SLit 0)); SPNot (SPBranch BC_EQ pA (SLit 3)); SPBranch BC_LTU (SLit 2) pA;
   SPUle pA (SLit (2 ^ 20)); SPBranch BC_LTU pK pA; SPUle pK (SLit (2 ^ 20)); hint12 pK;
   SPUle xP0 pP; SPUle pP xE0].

Definition K1_fcells : list cell := F_saved ++ [c8 (-208) (xb 528)].

Definition K1_U : sstate :=
  HSX_U tri_K1 K1_regs K1_fcells pP coA rp1 (coK pK) DUnknown [] K1_facts.

Definition tri_facts0 : list sprop :=
  [SPNot (SPBranch BC_EQ (t_d co1) (SLit 0)); SPNot (SPBranch BC_EQ pA (SLit 3)); SPBranch BC_LTU (SLit 2) pA;
   SPUle pA (SLit (2 ^ 20)); SPUle xP0 pP; SPUle pP xE0].

Definition nz_tr_k : list (positive * Z * positive) := [(318%positive, 4, 320%positive)].
Definition nz_tr : list sprop := TobjJVx.nz_facts nz_tr_k.

Definition KT_regs (r10 : sv) : list (nat * sv) :=
  [(1%nat, SLit tri_ra); (9%nat, am2); (10%nat, r10); (18%nat, xb 784); (19%nat, pS2); (21%nat, t_d co1);
   (22%nat, snotU (t_d co1)); (24%nat, pA); (25%nat, am2)].

Definition KTbad_U : sstate :=
  HSX_U S_vr.vr_ret (KT_regs (SLit 1)) K1_fcells pP coA rp1 DUnknown DUnknown []
    (tri_facts0 ++ [SPUle (n3U am2) (t_k tr1); SPBranch BC_NE pS2 (SLit 0)] ++ nz_tr).

Definition KTok_U : sstate :=
  HSX_U S_vr.vr_ret (KT_regs (SLit 1)) K1_fcells pP coA rp1 (coK pA) DUnknown []
    (tri_facts0 ++ [SPUle (n3U am2) (t_k tr1); SPNot (SPBranch BC_NE pS2 (SLit 0))] ++ nz_tr ++
     [SPUle (SLit 1) av_k]).

Definition FT_U : sstate :=
  HSX_U S_vr.vr_ret (KT_regs (SLit 0)) K1_fcells pP coA rp1 DUnknown DUnknown [] tri_facts0.

Definition K2_regs : list (nat * sv) :=
  [(9%nat, am2); (10%nat, snotU (t_d tr1)); (11%nat, SAlu ALU_ADD (SLit 1) pI);
   (12%nat, SAlu ALU_SUB am2 pI); (13%nat, SAlu ALU_ADD (SMd M_MUL (SLit 3) pI) (SLit 2)); (18%nat, xb 784);
   (21%nat, t_d co1); (22%nat, snotU (t_d co1)); (23%nat, t_d tr1); (24%nat, pA); (25%nat, am2)].

Definition K2_facts : list sprop :=
  tri_facts0 ++ [SPUle (n3U am2) (t_k tr1)] ++ nz_tr ++ [SPUlt pI am2; SPUle pI (SLit (2 ^ 20)); hint12 pI].

Definition K2_U : sstate :=
  HSX_U tri_K2 K2_regs K1_fcells pP coA rp1 DUnknown (trK pI) [] K2_facts.

Definition J9_regs : list (nat * sv) :=
  [(9%nat, pNT); (21%nat, t_d co1); (22%nat, snotU (t_d co1));
   (23%nat, t_d tr1); (24%nat, pA); (25%nat, am2)].

Definition J9_facts : list sprop :=
  tri_facts0 ++ [SPUle (n3U am2) (t_k tr1)] ++ nz_tr ++ [SPUle pNT am2].

Definition J9c_U : sstate :=
  HSX_U tri_J9 J9_regs K1_fcells pP coA rp1 DUnknown (trK pNT) [] J9_facts.
