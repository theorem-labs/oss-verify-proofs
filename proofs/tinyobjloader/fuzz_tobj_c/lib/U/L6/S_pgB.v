From Stdlib Require Import ZArith NArith List Bool PArith.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundR.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Init.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L6 Require Import S_pg.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition pgU_B : Z := 0x1e534.

Definition pspU : sv := SAlu ALU_ADD (SVar 10) (SLit (- pgU_frame)).

Definition stk_cells_U : list cell :=
  [mkCell (SLit (-136)) 8 (SVar 79); mkCell (SLit (-128)) 8 (SVar 78); mkCell (SLit (-120)) 8 (SVar 69);
   mkCell (SLit (-112)) 8 (SVar 68); mkCell (SLit (-104)) 8 (SVar 47); mkCell (SLit (-96)) 8 (SVar 46);
   mkCell (SLit (-88)) 8 (SVar 45); mkCell (SLit (-80)) 8 (SVar 44); mkCell (SLit (-72)) 8 (SVar 43);
   mkCell (SLit (-64)) 8 (SVar 42); mkCell (SLit (-56)) 8 (SVar 41); mkCell (SLit (-48)) 8 (SVar 40);
   mkCell (SLit (-40)) 8 (SVar 39); mkCell (SLit (-32)) 8 (SVar 38); mkCell (SLit (-24)) 8 (SVar 29);
   mkCell (SLit (-16)) 8 (SVar 28); mkCell (SLit (-8)) 8 (SVar 11)].

Definition w_cells_U : list cell :=
  [mkCell (SLit (-2288)) 8 PGD.pSCR; mkCell (SLit (-2280)) 8 PGD.pNXT;
   mkCell (SLit (-2272)) 8 PGD.pPRV; mkCell (SLit (-2264)) 8 PGD.pRFX].

Definition pregs_U (l : list (nat * sv)) : list sv :=
  setregs (cut_regs NF) ([(2%nat, pspU); (10%nat, SVar 12)] ++ l).

Definition pfregs_U (l : list (nat * sv)) : list sv :=
  setregs R2.cut_fregs ([(8%nat, SVar 172); (9%nat, SVar 173)] ++ l).

Definition pcut_U (pc : Z) (regs fregs : list (nat * sv)) (objs : list sobj) (facts : list sprop) : sstate :=
  mkSS pc (pregs_U regs) (pfregs_U fregs) FcsrFrm0 None objs (facts ++ pg_base_facts_U) R2.NXC false.

Definition regsB_U : list (nat * sv) :=
  [(8%nat, PGD.pOUT); (9%nat, PGD.pSCR); (13%nat, SLit 0); (18%nat, PGD.pN); (19%nat, SVar 119);
   (20%nat, SAlu ALU_ADD (SVar 10) (SLit (-208))); (21%nat, SVar 121); (22%nat, SVar 13);
   (23%nat, SAlu ALU_ADD PGD.pN (SLit (-2))); (24%nat, SLit 0); (25%nat, SLit 1); (26%nat, SVar 127)].

Definition B_U : sstate :=
  pcut_U pgU_B regsB_U []
    (pobjs_U (PGD.poutK (SLit 0)) DUnknown DUnknown [] PGD.res0 (w_cells_U ++ stk_cells_U))
    [SPUle (SVar 127) (SLit 1)].

Definition pgB_sum_stmt_U : Prop :=
  forall (ok : world -> Prop) (K : list event -> Model -> Prop) (rho0 rho : valuation),
    ok_frame segsU ok K -> agree_below NF rho0 rho ->
    triple segsU ok (SP segsU K B_U rho) (LQ segsU K NF rho0 Posts_pg_U).

Definition pgB_sum_ex_stmt_U : Prop :=
  forall (K : list event -> Model -> Prop) (rho0 rho : valuation),
    agree_below NF rho0 rho ->
    etriple segsU (SP segsU K B_U rho) (LQ segsU K NF rho0 Posts_pg_U).
