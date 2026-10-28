From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv RingBuf.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L7 Require Import S_r2.
Import ListNotations.
Open Scope Z_scope.

Module R2X.

Definition vN : sv := r2_N.
Definition LN : positive := 10%positive.
Definition LP : positive := 11%positive.
Definition NXT (e : sv) : sv := LD4 LN e.
Definition PRV (e : sv) : sv := LD4 LP e.

Definition I4 : sv := SAlu ALU_SLL (SVar 123) (SLit 2).
Definition SEL : sv :=
  SAlu ALU_AND
    (SAlu ALU_ADD
       (SAlu ALU_SLTU (SAlu ALU_ADD (SAlu ALU_SUB (SLit 0) (SVar 13)) (SAlu ALU_ADD (SVar 123) (SLit 1))) (SLit 1))
       (SLit (-1)))
    (SAlu ALU_ADD (SVar 123) (SLit 1)).
Definition REMP : sv := SMdW M_REMU (SAlu ALU_ADD (SAlu ALU_ADD (SVar 13) (SLit (-1))) (SVar 123)) (SVar 13).
Definition TESTV : sv := SAlu ALU_ADD (SAlu ALU_SUB (SLit 0) (SVar 13)) (SAlu ALU_ADD (SVar 123) (SLit 2)).
Definition TEST_r : sprop := SPBranch BC_NE TESTV (SLit 1).
Definition cellN : cell := mkCell I4 4 SEL.
Definition cellP : cell := mkCell I4 4 REMP.
Definition inv_r : list sprop := [SPUlt (SVar 123) vN; SPUle (SVar 127) (SLit 1)].

End R2X.
