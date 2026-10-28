(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan AsanNodesIO BKInv BKPB3Lit BKE1b.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition ke1b3_S_ (_ : unit) : acs := kcompact kpb3_hs101.
Abbreviation ke1b3_S := (ke1b3_S_ tt).
Definition ke1b3_pl_ (_ : unit) : plan := (ke1b_plan (kn0 ke1b3_S) (kvp ke1b3_S) (kvb ke1b3_S) (kvl ke1b3_S) ke1b3_S PNext).
Abbreviation ke1b3_pl := (ke1b3_pl_ tt).
