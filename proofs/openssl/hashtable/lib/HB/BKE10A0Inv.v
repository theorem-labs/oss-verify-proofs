(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan AsanNodesIO BKInv BKW9A0Lit BKE10a.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition ke10a0_S_ (_ : unit) : acs := kcompact kw9a0_hs110.
Abbreviation ke10a0_S := (ke10a0_S_ tt).
(* [comment removed for export] *)
Definition ke10a0_inv_ (_ : unit) : acs :=
  kinv ke10a0_S (kn0 ke10a0_S + 2) [(19%nat, 65536)] [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 23; 28; 29; 30; 31]%nat
    (FdFile 32 (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EVar 68)) (EVar 69)) (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EVar 70)) (ELit 33554432)))
    [(KRange (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EVar 68)) (EVar 69)) 33554432 67108863);
     (KRange (EAlu ALU_OR (EAlu ALU_SRL (EMd M_MUL (ELit 144115188075855872) (EBlob true 32 1 1)) (ELit 49)) (EBlob false 32 0 1)) 0 32767);
     (KRange (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EVar 68)) (EAlu ALU_ADD (EVar 69) (EMd M_MUL (ELit (-1)) (EAlu ALU_OR (EAlu ALU_SRL (EMd M_MUL (ELit 144115188075855872) (EBlob true 32 1 1)) (ELit 49)) (EBlob false 32 0 1))))) (ELit (-6))) 0 67108857);
     (KRange (EVar 69) 0 65535);
     (KRange (EVar 68) 512 1023);
     (KRange (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EVar 68)) (EVar 69)) 33554432 67108863);
     (KRange (EAlu ALU_OR (EAlu ALU_SRL (EMd M_MUL (ELit 144115188075855872) (EBlob true 32 1 1)) (ELit 49)) (EBlob false 32 0 1)) 0 32767)]
    [69; 107; 174; 235; 295; 354; 412; 466; 520; 573; 821]%nat.
Abbreviation ke10a0_inv := (ke10a0_inv_ tt).
Definition ke10a0_pl_ (_ : unit) : plan := (ke10a_plan (kn0 ke10a0_S) (kvp ke10a0_S) (kvb ke10a0_S) (kvl ke10a0_S) ke10a0_inv PNext).
Abbreviation ke10a0_pl := (ke10a0_pl_ tt).
