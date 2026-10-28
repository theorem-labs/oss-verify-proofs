(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan AsanNodesIO BKInv BKW5B2Lit BKW6a.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition kw6b2_S_ (_ : unit) : acs := kcompact kw5b2_hs106.
Abbreviation kw6b2_S := (kw6b2_S_ tt).
(* [comment removed for export] *)
Definition kw6b2_inv_ (_ : unit) : acs :=
  kinv kw6b2_S (kn0 kw6b2_S + 0) [(19%nat, 65536)] [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 23; 28; 29; 30; 31]%nat
    (FdFile 32 (EVar 55) (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EVar 64)) (ELit 2097152)))
    [(KRange (EVar 55) 4194304 67108864)]
    [69]%nat.
Abbreviation kw6b2_inv := (kw6b2_inv_ tt).
Definition kw6b2_pl_ (_ : unit) : plan := (kw6a_plan (kn0 kw6b2_S) (kvp kw6b2_S) (kvb kw6b2_S) (kvl kw6b2_S) kw6b2_inv PNext).
Abbreviation kw6b2_pl := (kw6b2_pl_ tt).
