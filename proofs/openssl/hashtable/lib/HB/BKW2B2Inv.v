(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan AsanNodesIO BKInv BKW1B2Lit BKW2a.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition kw2b2_S_ (_ : unit) : acs := kcompact kw1b2_hs102.
Abbreviation kw2b2_S := (kw2b2_S_ tt).
Definition kw2b2_pl_ (_ : unit) : plan := (kw2a_plan (kn0 kw2b2_S) (kvp kw2b2_S) (kvb kw2b2_S) (kvl kw2b2_S) kw2b2_S PNext).
Abbreviation kw2b2_pl := (kw2b2_pl_ tt).
