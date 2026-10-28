(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan AsanNodesIO BKInv BKPA3Lit BKE1b.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition ke1a3_S_ (_ : unit) : acs := kcompact kpa3_hs101.
Abbreviation ke1a3_S := (ke1a3_S_ tt).
Definition ke1a3_pl_ (_ : unit) : plan := (ke1b_plan (kn0 ke1a3_S) (kvp ke1a3_S) (kvb ke1a3_S) (kvl ke1a3_S) ke1a3_S PNext).
Abbreviation ke1a3_pl := (ke1a3_pl_ tt).
