(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan AsanNodesIO BKInv BKW3B3Lit BKE4b.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition ke4b3_S_ (_ : unit) : acs := kcompact kw3b3_hs104.
Abbreviation ke4b3_S := (ke4b3_S_ tt).
(* [comment removed for export] *)
Definition ke4b3_inv_ (_ : unit) : acs :=
  kinv ke4b3_S (kn0 ke4b3_S + 2) [(19%nat, 65536)] [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 23; 28; 29; 30; 31]%nat
    (FdFile 32 (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EVar 62)) (EVar 63)) (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EVar 64)) (ELit 524288)))
    [(KRange (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EVar 62)) (EVar 63)) 524288 1048575);
     (KRange (EAlu ALU_OR (EAlu ALU_SRL (EMd M_MUL (ELit 144115188075855872) (EBlob true 32 1 1)) (ELit 49)) (EBlob false 32 0 1)) 0 32767);
     (KRange (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EVar 62)) (EAlu ALU_ADD (EVar 63) (EMd M_MUL (ELit (-1)) (EAlu ALU_OR (EAlu ALU_SRL (EMd M_MUL (ELit 144115188075855872) (EBlob true 32 1 1)) (ELit 49)) (EBlob false 32 0 1))))) (ELit (-6))) 0 1048569);
     (KRange (EVar 63) 0 65535);
     (KRange (EVar 62) 8 15);
     (KRange (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EVar 62)) (EVar 63)) 524288 1048575);
     (KRange (EAlu ALU_OR (EAlu ALU_SRL (EMd M_MUL (ELit 144115188075855872) (EBlob true 32 1 1)) (ELit 49)) (EBlob false 32 0 1)) 0 32767)]
    [53; 85; 144; 197; 441]%nat.
Abbreviation ke4b3_inv := (ke4b3_inv_ tt).
Definition ke4b3_pl_ (_ : unit) : plan := (ke4b_plan (kn0 ke4b3_S) (kvp ke4b3_S) (kvb ke4b3_S) (kvl ke4b3_S) ke4b3_inv PNext).
Abbreviation ke4b3_pl := (ke4b3_pl_ tt).
