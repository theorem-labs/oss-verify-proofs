(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan AsanNodesIO BKInv BKW8B0Lit BKW9a.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition kw9b0_S_ (_ : unit) : acs := kcompact kw8b0_hs109.
Abbreviation kw9b0_S := (kw9b0_S_ tt).
(* [comment removed for export] *)
Definition kw9b0_inv_ (_ : unit) : acs :=
  kinv kw9b0_S (kn0 kw9b0_S + 0) [(19%nat, 65536)] [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 23; 28; 29; 30; 31]%nat
    (FdFile 32 (EVar 58) (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EVar 67)) (ELit 16777216)))
    [(KRange (EVar 58) 33554432 67108864)]
    [69]%nat.
Abbreviation kw9b0_inv := (kw9b0_inv_ tt).
Definition kw9b0_pl_ (_ : unit) : plan := (kw9a_plan (kn0 kw9b0_S) (kvp kw9b0_S) (kvb kw9b0_S) (kvl kw9b0_S) kw9b0_inv PNext).
Abbreviation kw9b0_pl := (kw9b0_pl_ tt).
