(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan AsanNodesIO BKInv BKW6A1Lit BKW7a.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition kw7a1_S_ (_ : unit) : acs := kcompact kw6a1_hs107.
Abbreviation kw7a1_S := (kw7a1_S_ tt).
(* [comment removed for export] *)
Definition kw7a1_inv_ (_ : unit) : acs :=
  kinv kw7a1_S (kn0 kw7a1_S + 0) [(19%nat, 65536)] [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 23; 28; 29; 30; 31]%nat
    (FdFile 32 (EVar 56) (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EVar 65)) (ELit 4194304)))
    [(KRange (EVar 56) 8388608 67108864)]
    [69]%nat.
Abbreviation kw7a1_inv := (kw7a1_inv_ tt).
Definition kw7a1_pl_ (_ : unit) : plan := (kw7a_plan (kn0 kw7a1_S) (kvp kw7a1_S) (kvb kw7a1_S) (kvl kw7a1_S) kw7a1_inv PNext).
Abbreviation kw7a1_pl := (kw7a1_pl_ tt).
