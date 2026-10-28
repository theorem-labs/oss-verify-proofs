(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan AsanNodesIO BKInv BKPA1Lit BKW1a.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition kw1a1_S_ (_ : unit) : acs := kcompact kpa1_hs101.
Abbreviation kw1a1_S := (kw1a1_S_ tt).
Definition kw1a1_pl_ (_ : unit) : plan := (kw1a_plan (kn0 kw1a1_S) (kvp kw1a1_S) (kvb kw1a1_S) (kvl kw1a1_S) kw1a1_S PNext).
Abbreviation kw1a1_pl := (kw1a1_pl_ tt).
