(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan AsanNodesIO BKInv BC3A1Lit BC3A1LitK BC4A1Lit BC4e BKPa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition kpa1_S_ (_ : unit) : acs := kcompact c3a1_hs98k.
Abbreviation kpa1_S := (kpa1_S_ tt).
Definition kpa1_pl_ (_ : unit) : plan := (PX XLayout [ELit 1] (kpa_plan 574 235 0 0)).
Abbreviation kpa1_pl := (kpa1_pl_ tt).
