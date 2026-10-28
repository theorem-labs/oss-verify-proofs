From Stdlib Require Import ZArith NArith List Bool PArith.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L6 Require Import S_pg S_pgB.
Import ListNotations.
Open Scope Z_scope.

Module PGC.

Definition V (i : positive) : sv := SVar i.
Definition M1 : sv := SLit 18446744073709551615.
Definition pN := PGD.pN.
Definition pPTS := PGD.pPTS.
Definition n3 : sv := SAlu ALU_ADD (SAlu ALU_SLL pN (SLit 1)) pN.
Definition n12 : sv := SAlu ALU_SLL n3 (SLit 2).
Definition notPTS : sv := SAlu ALU_XOR pPTS M1.
Definition s4U : sv := SAlu ALU_ADD (SVar 10) (SLit (-208)).

Definition objs0 : list sobj := pobjs_U (PGD.poutK (SLit 0)) DUnknown DUnknown [] PGD.res0 stk_cells_U.

Definition regs1 : list (nat * sv) :=
  [(11%nat, SVar 13); (18%nat, pN); (19%nat, SLit 2); (20%nat, s4U); (21%nat, pN); (26%nat, n3)].

Definition Kfin : sstate :=
  pcut_U 0x1dd0c
    (regs1 ++ [(12%nat, SAlu ALU_ADD pPTS (V 120)); (13%nat, V 120); (14%nat, notPTS); (15%nat, SLit 0);
               (16%nat, n12)])
    [] objs0
    [SPUlt (V 120) n12; SPAlign 120 2; SPUle (V 120) (SLit (2 ^ 24))].

Definition regs2 : list (nat * sv) :=
  [(8%nat, PGD.pOUT); (9%nat, PGD.pSCR); (11%nat, SAlu ALU_XOR PGD.pSCR M1); (12%nat, pPTS); (13%nat, SLit 0);
   (14%nat, notPTS); (15%nat, SLit 0); (18%nat, pN); (19%nat, SAlu ALU_SLL pN (SLit 4)); (20%nat, s4U);
   (21%nat, pN); (22%nat, SVar 13); (23%nat, SAlu ALU_ADD pN (SLit (-2))); (24%nat, SLit 0); (25%nat, SLit 1)].

Definition objs2 : list sobj :=
  pobjs_U (PGD.poutK (SLit 0)) DUnknown DUnknown [] PGD.res0 (w_cells_U ++ stk_cells_U).

Definition Kcm : sstate :=
  pcut_U 0x1dea8 (regs2 ++ [(16%nat, V 120); (26%nat, n12)]) [] objs2
    [SPUlt (V 120) n12; SPAlign 120 2; SPUle (V 120) (SLit (2 ^ 24))].


Definition Knw : sstate :=
  pcut_U 0x1defc (regs2 ++ [(15%nat, V 122); (16%nat, V 123); (26%nat, n12)]) [] objs2
    [SPEq (SAlu ALU_ADD (V 122) (SMd M_MUL (V 123) (SLit 3))) n3; SPUle (SLit 1) (V 123); SPUle (V 123) pN;
     SPUle (V 122) (SLit (2 ^ 22))].

Definition Kext : sstate :=
  pcut_U 0x1e0e0 (regs2 ++ [(15%nat, V 122); (16%nat, V 123); (26%nat, n12)]) [] objs2
    [SPEq (SAlu ALU_ADD (V 122) (SMd M_MUL (V 123) (SLit 3))) (SAlu ALU_ADD n3 (SLit 2));
     SPUle (SLit 1) (V 123); SPUle (V 123) pN; SPUle (SLit 2) (V 122); SPUle (V 122) (SLit (2 ^ 22))].

Definition Kbbp : sstate :=
  pcut_U 0x1e288
    (regs2 ++ [(15%nat, V 122); (16%nat, V 124); (17%nat, SAlu ALU_ADD (SLit 1) (V 126)); (21%nat, V 123);
               (26%nat, n12)]) [] objs2
    [SPEq (SAlu ALU_ADD (V 126) (SAlu ALU_SLL (V 123) (SLit 1))) (SAlu ALU_SLL pN (SLit 1));
     SPUle (SMd M_MUL (V 126) (SLit 3)) (SAlu ALU_SLL (V 122) (SLit 1));
     SPUle (SAlu ALU_SLL (V 122) (SLit 1)) (SAlu ALU_ADD (SMd M_MUL (V 126) (SLit 3)) (SLit 2));
     SPUle (SAlu ALU_ADD (SMd M_MUL (V 126) (SLit 3)) (SLit 2)) (SAlu ALU_SLL (V 124) (SLit 1));
     SPUle (SAlu ALU_SLL (V 124) (SLit 1)) (SAlu ALU_ADD (SMd M_MUL (V 126) (SLit 3)) (SLit 4));
     SPUle (SAlu ALU_ADD (V 126) (SLit 2)) (SAlu ALU_SLL pN (SLit 1));
     SPUle (SLit 1) (V 123); SPUle (V 123) pN; SPAlign 126 1; SPUle (V 126) (SLit (2 ^ 21));
     SPUle (SAlu ALU_ADD (V 122) (V 123)) (SAlu ALU_ADD (SAlu ALU_ADD (V 126) pN) (SLit 1));
     SPUle (V 122) (SAlu ALU_ADD (SAlu ALU_ADD (V 126) pN) (SLit 1));
     SPUle (SAlu ALU_ADD (V 124) (V 123)) (SAlu ALU_ADD (SAlu ALU_ADD (V 126) pN) (SLit 2));
     SPUle (V 124) (SAlu ALU_ADD (SAlu ALU_ADD (V 126) pN) (SLit 2))].

Definition Kproj : sstate :=
  pcut_U 0x1e458
    (regs2 ++ [(15%nat, SAlu ALU_ADD (SLit 1) (V 126)); (16%nat, V 124); (21%nat, V 123); (26%nat, n12)])
    [] objs2
    [SPEq (SAlu ALU_ADD (V 124) (SMd M_MUL (V 123) (SLit 3))) (SAlu ALU_ADD n3 (SLit 2));
     SPEq (SAlu ALU_ADD (V 126) (SAlu ALU_SLL (V 123) (SLit 1))) (SAlu ALU_SLL pN (SLit 1));
     SPUle (SLit 1) (V 123); SPUle (V 123) pN; SPAlign 126 1; SPUle (SLit 2) (V 124);
     SPUle (V 124) (SLit (2 ^ 22)); SPUle (V 126) (SLit (2 ^ 22))].

End PGC.
