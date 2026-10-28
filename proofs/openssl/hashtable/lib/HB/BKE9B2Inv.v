(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan AsanNodesIO BKInv BKW8B2Lit BKE9a.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition ke9b2_S_ (_ : unit) : acs := kcompact kw8b2_hs109.
Abbreviation ke9b2_S := (ke9b2_S_ tt).
(* [comment removed for export] *)
Definition ke9b2_inv_ (_ : unit) : acs :=
  kinv ke9b2_S (kn0 ke9b2_S + 2) [(19%nat, 65536)] [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 23; 28; 29; 30; 31]%nat
    (FdFile 32 (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EVar 67)) (EVar 68)) (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EVar 69)) (ELit 16777216)))
    [(KRange (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EVar 67)) (EVar 68)) 16777216 33554431);
     (KRange (EAlu ALU_OR (EAlu ALU_SRL (EMd M_MUL (ELit 144115188075855872) (EBlob true 32 1 1)) (ELit 49)) (EBlob false 32 0 1)) 0 32767);
     (KRange (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EVar 67)) (EAlu ALU_ADD (EVar 68) (EMd M_MUL (ELit (-1)) (EAlu ALU_OR (EAlu ALU_SRL (EMd M_MUL (ELit 144115188075855872) (EBlob true 32 1 1)) (ELit 49)) (EBlob false 32 0 1))))) (ELit (-6))) 0 33554425);
     (KRange (EVar 68) 0 65535);
     (KRange (EVar 67) 256 511);
     (KRange (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EVar 67)) (EVar 68)) 16777216 33554431);
     (KRange (EAlu ALU_OR (EAlu ALU_SRL (EMd M_MUL (ELit 144115188075855872) (EBlob true 32 1 1)) (ELit 49)) (EBlob false 32 0 1)) 0 32767)]
    [69; 106; 172; 232; 291; 349; 403; 457; 510; 757]%nat.
Abbreviation ke9b2_inv := (ke9b2_inv_ tt).
Definition ke9b2_pl_ (_ : unit) : plan := (ke9a_plan (kn0 ke9b2_S) (kvp ke9b2_S) (kvb ke9b2_S) (kvl ke9b2_S) ke9b2_inv PNext).
Abbreviation ke9b2_pl := (ke9b2_pl_ tt).
