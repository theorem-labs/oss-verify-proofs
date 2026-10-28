(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan AsanNodesIO BKInv BKW6B2Lit BKW7a.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition kw7b2_S_ (_ : unit) : acs := kcompact kw6b2_hs107.
Abbreviation kw7b2_S := (kw7b2_S_ tt).
(* [comment removed for export] *)
Definition kw7b2_inv_ (_ : unit) : acs :=
  kinv kw7b2_S (kn0 kw7b2_S + 0) [(19%nat, 65536)] [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 23; 28; 29; 30; 31]%nat
    (FdFile 32 (EVar 56) (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EVar 65)) (ELit 4194304)))
    [(KRange (EVar 56) 8388608 67108864)]
    [69]%nat.
Abbreviation kw7b2_inv := (kw7b2_inv_ tt).
Definition kw7b2_pl_ (_ : unit) : plan := (kw7a_plan (kn0 kw7b2_S) (kvp kw7b2_S) (kvb kw7b2_S) (kvl kw7b2_S) kw7b2_inv PNext).
Abbreviation kw7b2_pl := (kw7b2_pl_ tt).
