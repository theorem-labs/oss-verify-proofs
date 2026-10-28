(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan AsanNodesIO BKInv BKW2A2Lit BKE3a.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition ke3a2_S_ (_ : unit) : acs := kcompact kw2a2_hs103.
Abbreviation ke3a2_S := (ke3a2_S_ tt).
(* [comment removed for export] *)
Definition ke3a2_inv_ (_ : unit) : acs :=
  kinv ke3a2_S (kn0 ke3a2_S + 2) [(19%nat, 65536)] [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 23; 28; 29; 30; 31]%nat
    (FdFile 32 (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EVar 61)) (EVar 62)) (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EVar 63)) (ELit 262144)))
    [(KRange (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EVar 61)) (EVar 62)) 262144 524287);
     (KRange (EAlu ALU_OR (EAlu ALU_SRL (EMd M_MUL (ELit 144115188075855872) (EBlob true 32 1 1)) (ELit 49)) (EBlob false 32 0 1)) 0 32767);
     (KRange (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EVar 61)) (EAlu ALU_ADD (EVar 62) (EMd M_MUL (ELit (-1)) (EAlu ALU_OR (EAlu ALU_SRL (EMd M_MUL (ELit 144115188075855872) (EBlob true 32 1 1)) (ELit 49)) (EBlob false 32 0 1))))) (ELit (-6))) 0 524281);
     (KRange (EVar 62) 0 65535);
     (KRange (EVar 61) 4 7);
     (KRange (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EVar 61)) (EVar 62)) 262144 524287);
     (KRange (EAlu ALU_OR (EAlu ALU_SRL (EMd M_MUL (ELit 144115188075855872) (EBlob true 32 1 1)) (ELit 49)) (EBlob false 32 0 1)) 0 32767)]
    [53; 85; 143; 396]%nat.
Abbreviation ke3a2_inv := (ke3a2_inv_ tt).
Definition ke3a2_pl_ (_ : unit) : plan := (ke3a_plan (kn0 ke3a2_S) (kvp ke3a2_S) (kvb ke3a2_S) (kvl ke3a2_S) ke3a2_inv PNext).
Abbreviation ke3a2_pl := (ke3a2_pl_ tt).
