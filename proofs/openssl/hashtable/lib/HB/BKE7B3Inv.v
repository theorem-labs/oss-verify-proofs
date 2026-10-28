(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan AsanNodesIO BKInv BKW6B3Lit BKE7b.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition ke7b3_S_ (_ : unit) : acs := kcompact kw6b3_hs107.
Abbreviation ke7b3_S := (ke7b3_S_ tt).
(* [comment removed for export] *)
Definition ke7b3_inv_ (_ : unit) : acs :=
  kinv ke7b3_S (kn0 ke7b3_S + 2) [(19%nat, 65536)] [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 23; 28; 29; 30; 31]%nat
    (FdFile 32 (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EVar 65)) (EVar 66)) (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EVar 67)) (ELit 4194304)))
    [(KRange (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EVar 65)) (EVar 66)) 4194304 8388607);
     (KRange (EAlu ALU_OR (EAlu ALU_SRL (EMd M_MUL (ELit 144115188075855872) (EBlob true 32 1 1)) (ELit 49)) (EBlob false 32 0 1)) 0 32767);
     (KRange (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EVar 65)) (EAlu ALU_ADD (EVar 66) (EMd M_MUL (ELit (-1)) (EAlu ALU_OR (EAlu ALU_SRL (EMd M_MUL (ELit 144115188075855872) (EBlob true 32 1 1)) (ELit 49)) (EBlob false 32 0 1))))) (ELit (-6))) 0 8388601);
     (KRange (EVar 66) 0 65535);
     (KRange (EVar 65) 64 127);
     (KRange (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EVar 65)) (EVar 66)) 4194304 8388607);
     (KRange (EAlu ALU_OR (EAlu ALU_SRL (EMd M_MUL (ELit 144115188075855872) (EBlob true 32 1 1)) (ELit 49)) (EBlob false 32 0 1)) 0 32767)]
    [69; 104; 168; 226; 280; 334; 387; 623]%nat.
Abbreviation ke7b3_inv := (ke7b3_inv_ tt).
Definition ke7b3_pl_ (_ : unit) : plan := (ke7b_plan (kn0 ke7b3_S) (kvp ke7b3_S) (kvb ke7b3_S) (kvl ke7b3_S) ke7b3_inv PNext).
Abbreviation ke7b3_pl := (ke7b3_pl_ tt).
