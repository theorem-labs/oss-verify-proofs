(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan AsanNodesIO BKInv BKPA1Lit BKE1a.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition ke1a1_S_ (_ : unit) : acs := kcompact kpa1_hs101.
Abbreviation ke1a1_S := (ke1a1_S_ tt).
Definition ke1a1_pl_ (_ : unit) : plan := (ke1a_plan (kn0 ke1a1_S) (kvp ke1a1_S) (kvb ke1a1_S) (kvl ke1a1_S) ke1a1_S PNext).
Abbreviation ke1a1_pl := (ke1a1_pl_ tt).
