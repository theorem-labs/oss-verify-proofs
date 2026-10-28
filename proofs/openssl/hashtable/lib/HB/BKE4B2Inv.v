(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan AsanNodesIO BKInv BKW3B2Lit BKE4a.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition ke4b2_S_ (_ : unit) : acs := kcompact kw3b2_hs104.
Abbreviation ke4b2_S := (ke4b2_S_ tt).
(* [comment removed for export] *)
Definition ke4b2_inv_ (_ : unit) : acs :=
  kinv ke4b2_S (kn0 ke4b2_S + 2) [(19%nat, 65536)] [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 23; 28; 29; 30; 31]%nat
    (FdFile 32 (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EVar 62)) (EVar 63)) (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EVar 64)) (ELit 524288)))
    [(KRange (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EVar 62)) (EVar 63)) 524288 1048575);
     (KRange (EAlu ALU_OR (EAlu ALU_SRL (EMd M_MUL (ELit 144115188075855872) (EBlob true 32 1 1)) (ELit 49)) (EBlob false 32 0 1)) 0 32767);
     (KRange (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EVar 62)) (EAlu ALU_ADD (EVar 63) (EMd M_MUL (ELit (-1)) (EAlu ALU_OR (EAlu ALU_SRL (EMd M_MUL (ELit 144115188075855872) (EBlob true 32 1 1)) (ELit 49)) (EBlob false 32 0 1))))) (ELit (-6))) 0 1048569);
     (KRange (EVar 63) 0 65535);
     (KRange (EVar 62) 8 15);
     (KRange (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EVar 62)) (EVar 63)) 524288 1048575);
     (KRange (EAlu ALU_OR (EAlu ALU_SRL (EMd M_MUL (ELit 144115188075855872) (EBlob true 32 1 1)) (ELit 49)) (EBlob false 32 0 1)) 0 32767)]
    [53; 85; 144; 197; 450]%nat.
Abbreviation ke4b2_inv := (ke4b2_inv_ tt).
Definition ke4b2_pl_ (_ : unit) : plan := (ke4a_plan (kn0 ke4b2_S) (kvp ke4b2_S) (kvb ke4b2_S) (kvl ke4b2_S) ke4b2_inv PNext).
Abbreviation ke4b2_pl := (ke4b2_pl_ tt).
