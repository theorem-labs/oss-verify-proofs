(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan AsanNodesIO BKInv BKW1B3Lit BKW2b.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition kw2b3_S_ (_ : unit) : acs := kcompact kw1b3_hs102.
Abbreviation kw2b3_S := (kw2b3_S_ tt).
Definition kw2b3_pl_ (_ : unit) : plan := (kw2b_plan (kn0 kw2b3_S) (kvp kw2b3_S) (kvb kw2b3_S) (kvl kw2b3_S) kw2b3_S PNext).
Abbreviation kw2b3_pl := (kw2b3_pl_ tt).
