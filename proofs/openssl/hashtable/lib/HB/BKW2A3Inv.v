(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan AsanNodesIO BKInv BKW1A3Lit BKW2b.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition kw2a3_S_ (_ : unit) : acs := kcompact kw1a3_hs102.
Abbreviation kw2a3_S := (kw2a3_S_ tt).
Definition kw2a3_pl_ (_ : unit) : plan := (kw2b_plan (kn0 kw2a3_S) (kvp kw2a3_S) (kvb kw2a3_S) (kvl kw2a3_S) kw2a3_S PNext).
Abbreviation kw2a3_pl := (kw2a3_pl_ tt).
