(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan AsanNodesIO BKInv BKW3A3Lit BKW4b.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition kw4a3_S_ (_ : unit) : acs := kcompact kw3a3_hs104.
Abbreviation kw4a3_S := (kw4a3_S_ tt).
(* [comment removed for export] *)
Definition kw4a3_inv_ (_ : unit) : acs :=
  kinv kw4a3_S (kn0 kw4a3_S + 0) [(19%nat, 65536)] [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 23; 28; 29; 30; 31]%nat
    (FdFile 32 (EVar 53) (EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EVar 62)) (ELit 524288)))
    [(KRange (EVar 53) 1048576 67108864)]
    [53]%nat.
Abbreviation kw4a3_inv := (kw4a3_inv_ tt).
Definition kw4a3_pl_ (_ : unit) : plan := (kw4b_plan (kn0 kw4a3_S) (kvp kw4a3_S) (kvb kw4a3_S) (kvl kw4a3_S) kw4a3_inv PNext).
Abbreviation kw4a3_pl := (kw4a3_pl_ tt).
