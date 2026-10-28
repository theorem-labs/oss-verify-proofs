(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan AsanNodesIO BKInv BKPB3Lit BKW1b.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition kw1b3_S_ (_ : unit) : acs := kcompact kpb3_hs101.
Abbreviation kw1b3_S := (kw1b3_S_ tt).
Definition kw1b3_pl_ (_ : unit) : plan := (kw1b_plan (kn0 kw1b3_S) (kvp kw1b3_S) (kvb kw1b3_S) (kvl kw1b3_S) kw1b3_S PNext).
Abbreviation kw1b3_pl := (kw1b3_pl_ tt).
