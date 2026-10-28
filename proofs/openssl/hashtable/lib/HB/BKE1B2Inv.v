(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan AsanNodesIO BKInv BKPB2Lit BKE1a.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition ke1b2_S_ (_ : unit) : acs := kcompact kpb2_hs101.
Abbreviation ke1b2_S := (ke1b2_S_ tt).
Definition ke1b2_pl_ (_ : unit) : plan := (ke1a_plan (kn0 ke1b2_S) (kvp ke1b2_S) (kvb ke1b2_S) (kvl ke1b2_S) ke1b2_S PNext).
Abbreviation ke1b2_pl := (ke1b2_pl_ tt).
