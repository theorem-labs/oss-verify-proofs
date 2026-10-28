(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan AsanNodesIO BKInv BKPA0Lit BKE1a.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition ke1a0_S_ (_ : unit) : acs := kcompact kpa0_hs101.
Abbreviation ke1a0_S := (ke1a0_S_ tt).
Definition ke1a0_pl_ (_ : unit) : plan := (ke1a_plan (kn0 ke1a0_S) (kvp ke1a0_S) (kvb ke1a0_S) (kvl ke1a0_S) ke1a0_S PNext).
Abbreviation ke1a0_pl := (ke1a0_pl_ tt).
