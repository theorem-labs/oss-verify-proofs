(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan AsanNodesIO BKInv BKW9A1Lit BKRa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition kra1_S_ (_ : unit) : acs := kcompact kw9a1_hs110.
Abbreviation kra1_S := (kra1_S_ tt).
(* [comment removed for export] *)
Definition kra1_inv_ (_ : unit) : acs :=
  kinv kra1_S (kn0 kra1_S + 0) [(19%nat, 65536)] [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 23; 28; 29; 30; 31]%nat
    (FdFile 32 (EVar 59) (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EVar 68)) (ELit 33554432)))
    [(KRange (EVar 59) 67108864 67108864)]
    [69]%nat.
Abbreviation kra1_inv := (kra1_inv_ tt).
Definition kra1_pl_ (_ : unit) : plan := (kra_plan (kn0 kra1_S) (kvp kra1_S) (kvb kra1_S) (kvl kra1_S) kra1_inv PNext).
Abbreviation kra1_pl := (kra1_pl_ tt).
