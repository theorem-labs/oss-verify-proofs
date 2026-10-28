(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan AsanNodesIO BKInv BKW7A0Lit BKE8a.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition ke8a0_S_ (_ : unit) : acs := kcompact kw7a0_hs108.
Abbreviation ke8a0_S := (ke8a0_S_ tt).
(* [comment removed for export] *)
Definition ke8a0_inv_ (_ : unit) : acs :=
  kinv ke8a0_S (kn0 ke8a0_S + 2) [(19%nat, 65536)] [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 23; 28; 29; 30; 31]%nat
    (FdFile 32 (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EVar 66)) (EVar 67)) (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EVar 68)) (ELit 8388608)))
    [(KRange (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EVar 66)) (EVar 67)) 8388608 16777215);
     (KRange (EAlu ALU_OR (EAlu ALU_SRL (EMd M_MUL (ELit 144115188075855872) (EBlob true 32 1 1)) (ELit 49)) (EBlob false 32 0 1)) 0 32767);
     (KRange (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EVar 66)) (EAlu ALU_ADD (EVar 67) (EMd M_MUL (ELit (-1)) (EAlu ALU_OR (EAlu ALU_SRL (EMd M_MUL (ELit 144115188075855872) (EBlob true 32 1 1)) (ELit 49)) (EBlob false 32 0 1))))) (ELit (-6))) 0 16777209);
     (KRange (EVar 67) 0 65535);
     (KRange (EVar 66) 128 255);
     (KRange (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EVar 66)) (EVar 67)) 8388608 16777215);
     (KRange (EAlu ALU_OR (EAlu ALU_SRL (EMd M_MUL (ELit 144115188075855872) (EBlob true 32 1 1)) (ELit 49)) (EBlob false 32 0 1)) 0 32767)]
    [69; 105; 170; 229; 287; 341; 395; 448; 694]%nat.
Abbreviation ke8a0_inv := (ke8a0_inv_ tt).
Definition ke8a0_pl_ (_ : unit) : plan := (ke8a_plan (kn0 ke8a0_S) (kvp ke8a0_S) (kvb ke8a0_S) (kvl ke8a0_S) ke8a0_inv PNext).
Abbreviation ke8a0_pl := (ke8a0_pl_ tt).
