(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan AsanNodesIO BKInv BKPB0Lit BKW1a.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition kw1b0_S_ (_ : unit) : acs := kcompact kpb0_hs101.
Abbreviation kw1b0_S := (kw1b0_S_ tt).
Definition kw1b0_pl_ (_ : unit) : plan := (kw1a_plan (kn0 kw1b0_S) (kvp kw1b0_S) (kvb kw1b0_S) (kvl kw1b0_S) kw1b0_S PNext).
Abbreviation kw1b0_pl := (kw1b0_pl_ tt).
