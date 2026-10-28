(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan AsanNodesIO BKInv BKW1A2Lit BKW2a.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition kw2a2_S_ (_ : unit) : acs := kcompact kw1a2_hs102.
Abbreviation kw2a2_S := (kw2a2_S_ tt).
Definition kw2a2_pl_ (_ : unit) : plan := (kw2a_plan (kn0 kw2a2_S) (kvp kw2a2_S) (kvb kw2a2_S) (kvl kw2a2_S) kw2a2_S PNext).
Abbreviation kw2a2_pl := (kw2a2_pl_ tt).
