(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan AsanNodesIO BKInv BKW1A3Lit BKE2b.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition ke2a3_S_ (_ : unit) : acs := kcompact kw1a3_hs102.
Abbreviation ke2a3_S := (ke2a3_S_ tt).
Definition ke2a3_pl_ (_ : unit) : plan := (ke2b_plan (kn0 ke2a3_S) (kvp ke2a3_S) (kvb ke2a3_S) (kvl ke2a3_S) ke2a3_S PNext).
Abbreviation ke2a3_pl := (ke2a3_pl_ tt).
