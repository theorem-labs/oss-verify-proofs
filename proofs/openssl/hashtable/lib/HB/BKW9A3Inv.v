(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan AsanNodesIO BKInv BKW8A3Lit BKW9b.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition kw9a3_S_ (_ : unit) : acs := kcompact kw8a3_hs109.
Abbreviation kw9a3_S := (kw9a3_S_ tt).
(* [comment removed for export] *)
Definition kw9a3_inv_ (_ : unit) : acs :=
  kinv kw9a3_S (kn0 kw9a3_S + 0) [(19%nat, 65536)] [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 23; 28; 29; 30; 31]%nat
    (FdFile 32 (EVar 58) (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EVar 67)) (ELit 16777216)))
    [(KRange (EVar 58) 33554432 67108864)]
    [69]%nat.
Abbreviation kw9a3_inv := (kw9a3_inv_ tt).
Definition kw9a3_pl_ (_ : unit) : plan := (kw9b_plan (kn0 kw9a3_S) (kvp kw9a3_S) (kvb kw9a3_S) (kvl kw9a3_S) kw9a3_inv PNext).
Abbreviation kw9a3_pl := (kw9a3_pl_ tt).
