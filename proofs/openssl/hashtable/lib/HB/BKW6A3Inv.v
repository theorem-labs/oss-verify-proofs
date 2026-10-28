(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan AsanNodesIO BKInv BKW5A3Lit BKW6b.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition kw6a3_S_ (_ : unit) : acs := kcompact kw5a3_hs106.
Abbreviation kw6a3_S := (kw6a3_S_ tt).
(* [comment removed for export] *)
Definition kw6a3_inv_ (_ : unit) : acs :=
  kinv kw6a3_S (kn0 kw6a3_S + 0) [(19%nat, 65536)] [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 23; 28; 29; 30; 31]%nat
    (FdFile 32 (EVar 55) (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EVar 64)) (ELit 2097152)))
    [(KRange (EVar 55) 4194304 67108864)]
    [69]%nat.
Abbreviation kw6a3_inv := (kw6a3_inv_ tt).
Definition kw6a3_pl_ (_ : unit) : plan := (kw6b_plan (kn0 kw6a3_S) (kvp kw6a3_S) (kvb kw6a3_S) (kvl kw6a3_S) kw6a3_inv PNext).
Abbreviation kw6a3_pl := (kw6a3_pl_ tt).
