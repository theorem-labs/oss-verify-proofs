(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan AsanNodesIO BKInv BKW2A0Lit BKW3a.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition kw3a0_S_ (_ : unit) : acs := kcompact kw2a0_hs103.
Abbreviation kw3a0_S := (kw3a0_S_ tt).
(* [comment removed for export] *)
Definition kw3a0_inv_ (_ : unit) : acs :=
  kinv kw3a0_S (kn0 kw3a0_S + 0) [(19%nat, 65536)] [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 23; 28; 29; 30; 31]%nat
    (FdFile 32 (EVar 52) (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EVar 61)) (ELit 262144)))
    [(KRange (EVar 52) 524288 67108864)]
    [53]%nat.
Abbreviation kw3a0_inv := (kw3a0_inv_ tt).
Definition kw3a0_pl_ (_ : unit) : plan := (kw3a_plan (kn0 kw3a0_S) (kvp kw3a0_S) (kvb kw3a0_S) (kvl kw3a0_S) kw3a0_inv PNext).
Abbreviation kw3a0_pl := (kw3a0_pl_ tt).
