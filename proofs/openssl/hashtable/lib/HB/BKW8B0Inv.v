(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan AsanNodesIO BKInv BKW7B0Lit BKW8a.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition kw8b0_S_ (_ : unit) : acs := kcompact kw7b0_hs108.
Abbreviation kw8b0_S := (kw8b0_S_ tt).
(* [comment removed for export] *)
Definition kw8b0_inv_ (_ : unit) : acs :=
  kinv kw8b0_S (kn0 kw8b0_S + 0) [(19%nat, 65536)] [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 23; 28; 29; 30; 31]%nat
    (FdFile 32 (EVar 57) (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EVar 66)) (ELit 8388608)))
    [(KRange (EVar 57) 16777216 67108864)]
    [69]%nat.
Abbreviation kw8b0_inv := (kw8b0_inv_ tt).
Definition kw8b0_pl_ (_ : unit) : plan := (kw8a_plan (kn0 kw8b0_S) (kvp kw8b0_S) (kvb kw8b0_S) (kvl kw8b0_S) kw8b0_inv PNext).
Abbreviation kw8b0_pl := (kw8b0_pl_ tt).
