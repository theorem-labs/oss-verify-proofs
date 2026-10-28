(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan AsanNodesIO BKInv BKW6B3Lit BKW7b.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition kw7b3_S_ (_ : unit) : acs := kcompact kw6b3_hs107.
Abbreviation kw7b3_S := (kw7b3_S_ tt).
(* [comment removed for export] *)
Definition kw7b3_inv_ (_ : unit) : acs :=
  kinv kw7b3_S (kn0 kw7b3_S + 0) [(19%nat, 65536)] [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 23; 28; 29; 30; 31]%nat
    (FdFile 32 (EVar 56) (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EVar 65)) (ELit 4194304)))
    [(KRange (EVar 56) 8388608 67108864)]
    [69]%nat.
Abbreviation kw7b3_inv := (kw7b3_inv_ tt).
Definition kw7b3_pl_ (_ : unit) : plan := (kw7b_plan (kn0 kw7b3_S) (kvp kw7b3_S) (kvb kw7b3_S) (kvl kw7b3_S) kw7b3_inv PNext).
Abbreviation kw7b3_pl := (kw7b3_pl_ tt).
