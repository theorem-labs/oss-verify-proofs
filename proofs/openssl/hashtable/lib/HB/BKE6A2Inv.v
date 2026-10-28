(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan AsanNodesIO BKInv BKW5A2Lit BKE6a.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition ke6a2_S_ (_ : unit) : acs := kcompact kw5a2_hs106.
Abbreviation ke6a2_S := (ke6a2_S_ tt).
(* [comment removed for export] *)
Definition ke6a2_inv_ (_ : unit) : acs :=
  kinv ke6a2_S (kn0 ke6a2_S + 2) [(19%nat, 65536)] [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 23; 28; 29; 30; 31]%nat
    (FdFile 32 (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EVar 64)) (EVar 65)) (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EVar 66)) (ELit 2097152)))
    [(KRange (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EVar 64)) (EVar 65)) 2097152 4194303);
     (KRange (EAlu ALU_OR (EAlu ALU_SRL (EMd M_MUL (ELit 144115188075855872) (EBlob true 32 1 1)) (ELit 49)) (EBlob false 32 0 1)) 0 32767);
     (KRange (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EVar 64)) (EAlu ALU_ADD (EVar 65) (EMd M_MUL (ELit (-1)) (EAlu ALU_OR (EAlu ALU_SRL (EMd M_MUL (ELit 144115188075855872) (EBlob true 32 1 1)) (ELit 49)) (EBlob false 32 0 1))))) (ELit (-6))) 0 4194297);
     (KRange (EVar 65) 0 65535);
     (KRange (EVar 64) 32 63);
     (KRange (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EVar 64)) (EVar 65)) 2097152 4194303);
     (KRange (EAlu ALU_OR (EAlu ALU_SRL (EMd M_MUL (ELit 144115188075855872) (EBlob true 32 1 1)) (ELit 49)) (EBlob false 32 0 1)) 0 32767)]
    [69; 103; 166; 220; 274; 327; 571]%nat.
Abbreviation ke6a2_inv := (ke6a2_inv_ tt).
Definition ke6a2_pl_ (_ : unit) : plan := (ke6a_plan (kn0 ke6a2_S) (kvp ke6a2_S) (kvb ke6a2_S) (kvl ke6a2_S) ke6a2_inv PNext).
Abbreviation ke6a2_pl := (ke6a2_pl_ tt).
