(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan AsanNodesIO BKInv BKW1B2Lit BKE2a.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition ke2b2_S_ (_ : unit) : acs := kcompact kw1b2_hs102.
Abbreviation ke2b2_S := (ke2b2_S_ tt).
Definition ke2b2_pl_ (_ : unit) : plan := (ke2a_plan (kn0 ke2b2_S) (kvp ke2b2_S) (kvb ke2b2_S) (kvl ke2b2_S) ke2b2_S PNext).
Abbreviation ke2b2_pl := (ke2b2_pl_ tt).
