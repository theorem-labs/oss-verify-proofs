From Stdlib Require Import ZArith NArith List Bool PArith.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundR.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Init.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P Require Lib_tess__G1.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Module PGD := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G1.Lib_tess_polygon_defs.
Module R2 := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_tess__G1.Lib_tess_run2d.

Module TessPolygonAddrU.
  Definition pgU_entry : Z := 0x1dbf0.
  Definition pgU_ret : Z := 0x1dcc8.
End TessPolygonAddrU.
Import TessPolygonAddrU.

Definition pgU_frame : Z := 2304.
Definition pgU_below : Z := 128.

Definition O_pstk_U (cells : list cell) : sobj := mkObj (SVar 10) (SLit (- pgU_frame)) (SLit 0) cells DUnknown.
Definition O_pbelow_U : sobj :=
  mkObj (SAlu ALU_ADD (SVar 10) (SLit (- pgU_frame))) (SVar R2.V_DEPTH) (SLit 0) [] DUnknown.

Definition pobjs_U (dout dn dp : odefault) (outc resc stkc : list cell) : list sobj :=
  [O_pstk_U stkc; O_pbelow_U; PGD.O_desc; PGD.O_res resc; PGD.O_pts; PGD.O_pout dout outc; PGD.O_pp2d;
   PGD.O_pnxt dn; PGD.O_pprv dp; PGD.O_prfx].

Definition pg_head_facts_U : list sprop :=
  [SPUle (SLit 3) PGD.pN; SPUle PGD.pN (SLit R2.two20);
   SPBranch BC_GE (SLit (- pgU_below)) (SVar R2.V_DEPTH);
   SPBranch BC_GE (SVar R2.V_DEPTH) (SLit (- 2 ^ 40))].

Lemma pg_base_facts_P_head :
  firstn 4 PGD.pg_base_facts =
  [SPUle (SLit 3) PGD.pN; SPUle PGD.pN (SLit R2.two20);
   SPBranch BC_GE (SLit (-80)) (SVar R2.V_DEPTH);
   SPBranch BC_GE (SVar R2.V_DEPTH) (SLit (- 2 ^ 40))].
Proof. reflexivity. Qed.

Definition pg_base_facts_U : list sprop := pg_head_facts_U ++ skipn 4 PGD.pg_base_facts.

Definition Pre_pg_U (extra : list sprop) : sstate :=
  mkSS pgU_entry (setregs pre_regs [(12%nat, SVar 22)]) pre_fregs FcsrFrm0 None
    (pobjs_U (PGD.poutK (SLit 0)) DUnknown DUnknown [] [] []) (extra ++ pg_base_facts_U) NF false.

Definition P_inv_U : sstate :=
  mkSS pgU_ret (setregs (post_regs NF) [(10%nat, SLit 2)]) R2.cut_fregs FcsrFrm0 None
    (pobjs_U (PGD.poutK (SLit 0)) DUnknown DUnknown [] PGD.res0 []) pg_base_facts_U R2.NXC false.

Definition res_ok_U : list cell :=
  [mkCell (SLit 0) 8 PGD.pOUT; mkCell (SLit 8) 4 (SAlu ALU_ADD PGD.pN (SLit (-2)));
   mkCell (SLit 12) 4 (SLit 0); mkCell (SLit 16) 4 (SVar 110)].

Definition P_ok_U : sstate :=
  mkSS pgU_ret (post_regs NF) R2.cut_fregs FcsrFrm0 None
    (pobjs_U (PGD.poutK (SAlu ALU_ADD PGD.pN (SLit (-2)))) DUnknown DUnknown [] res_ok_U [])
    pg_base_facts_U R2.NXC false.

Definition Posts_pg_U : list leaf := [mkLeaf P_inv_U RsSymJump; mkLeaf P_ok_U RsSymJump].

Definition tess_polygon_sum_stmt_U : Prop :=
  forall (ok : world -> Prop) (K : list event -> Model -> Prop) (rho : valuation),
    ok_frame segsU ok K -> triple segsU ok (SP segsU K (Pre_pg_U []) rho) (LQ segsU K NF rho Posts_pg_U).

Definition tess_polygon_sum_ex_stmt_U : Prop :=
  forall (K : list event -> Model -> Prop) (rho : valuation),
    etriple segsU (SP segsU K (Pre_pg_U []) rho) (LQ segsU K NF rho Posts_pg_U).
