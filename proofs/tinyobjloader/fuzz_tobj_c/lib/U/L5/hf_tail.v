From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymFrame SymEntail SymCFG SymSummary.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjUnbase ObjXform TobjJV.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Init.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L5 Require Import S_hf hf_defs.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_defs.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_nodes.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition pc_L14_U : Z := 0x19b88.

Definition snot (v : sv) : sv := SAlu ALU_XOR v (SLit (2 ^ 64 - 1)).
Definition sneg (v : sv) : sv := SAlu ALU_SUB (SLit 0) v.
Definition div3_U : Z := (2 ^ 64 - 1) / 3.

Definition L14_regs : list (nat * sv) :=
  [(9%nat, snot (xb 1256)); (13%nat, pI); (16%nat, snot (t_d tr1)); (18%nat, xb 1256);
   (19%nat, sneg (spo (-176))); (20%nat, snot (xb 1260)); (21%nat, t_d co1); (22%nat, snot (t_d co1));
   (23%nat, t_d tr1); (24%nat, spo (-200)); (25%nat, spo (-176)); (26%nat, sneg (spo (-200)));
   (27%nat, xb 1260)].

Definition L14_fcells : list cell :=
  F_saved ++ [c8 (-208) (xb 528); c8 (-224) pNT; c8 (-232) (xb 496); c8 (-240) (SLit div3_U);
              c8 (-248) (xb 560); c8 (-256) (xb 592); c8 (-264) (snot (t_d tr1))].

Definition tr_bound (i : sv) : sprop :=
  SPUle (SAlu ALU_ADD (SMd M_MUL (SLit 12) i) (SLit 12)) (SMd M_MUL (SLit 4) (t_k tr1)).

Definition L14_facts : list sprop :=
  [SPUle xP0 pP; SPUle pP xE0; SPUle pA (SLit (2 ^ 20)); SPUle pA (t_k co1); SPUlt pI pNT;
   SPUle pI (SLit (2 ^ 20)); hint12 pI; SPUle (SLit 1) pNT; SPUle (SMd M_MUL (SLit 12) pNT) (kb 4 (t_k tr1));
   tr_bound pI;
   SPUle pNT (SLit (2 ^ 20))].

Definition L14_U : sstate := HSt_U pc_L14_U L14_regs L14_fcells (trK pNT) L14_facts.

Definition L14_tv : list (sv * sv) := tvH.
Definition L14_rv : Z * sv := (40, VL 9).
