(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan AsanNodesIO BKInv BKW2B2Lit BKW3a.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition kw3b2_S_ (_ : unit) : acs := kcompact kw2b2_hs103.
Abbreviation kw3b2_S := (kw3b2_S_ tt).
(* [comment removed for export] *)
Definition kw3b2_inv_ (_ : unit) : acs :=
  kinv kw3b2_S (kn0 kw3b2_S + 0) [(19%nat, 65536)] [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 23; 28; 29; 30; 31]%nat
    (FdFile 32 (EVar 52) (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EVar 61)) (ELit 262144)))
    [(KRange (EVar 52) 524288 67108864)]
    [53]%nat.
Abbreviation kw3b2_inv := (kw3b2_inv_ tt).
Definition kw3b2_pl_ (_ : unit) : plan := (kw3a_plan (kn0 kw3b2_S) (kvp kw3b2_S) (kvb kw3b2_S) (kvl kw3b2_S) kw3b2_inv PNext).
Abbreviation kw3b2_pl := (kw3b2_pl_ tt).
