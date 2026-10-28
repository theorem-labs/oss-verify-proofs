(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan AsanNodesIO BKInv BKW3B1Lit BKW4a.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition kw4b1_S_ (_ : unit) : acs := kcompact kw3b1_hs104.
Abbreviation kw4b1_S := (kw4b1_S_ tt).
(* [comment removed for export] *)
Definition kw4b1_inv_ (_ : unit) : acs :=
  kinv kw4b1_S (kn0 kw4b1_S + 0) [(19%nat, 65536)] [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 23; 28; 29; 30; 31]%nat
    (FdFile 32 (EVar 53) (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EVar 62)) (ELit 524288)))
    [(KRange (EVar 53) 1048576 67108864)]
    [53]%nat.
Abbreviation kw4b1_inv := (kw4b1_inv_ tt).
Definition kw4b1_pl_ (_ : unit) : plan := (kw4a_plan (kn0 kw4b1_S) (kvp kw4b1_S) (kvb kw4b1_S) (kvl kw4b1_S) kw4b1_inv PNext).
Abbreviation kw4b1_pl := (kw4b1_pl_ tt).
