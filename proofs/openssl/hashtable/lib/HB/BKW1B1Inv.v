(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan AsanNodesIO BKInv BKPB1Lit BKW1a.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition kw1b1_S_ (_ : unit) : acs := kcompact kpb1_hs101.
Abbreviation kw1b1_S := (kw1b1_S_ tt).
Definition kw1b1_pl_ (_ : unit) : plan := (kw1a_plan (kn0 kw1b1_S) (kvp kw1b1_S) (kvb kw1b1_S) (kvl kw1b1_S) kw1b1_S PNext).
Abbreviation kw1b1_pl := (kw1b1_pl_ tt).
