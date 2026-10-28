(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan AsanNodesIO BKInv BC3A2Lit BC3A2LitK BC4A2Lit BC4e BKPa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition kpa2_S_ (_ : unit) : acs := kcompact c3a2_hs98k.
Abbreviation kpa2_S := (kpa2_S_ tt).
Definition kpa2_pl_ (_ : unit) : plan := (PX XLayout [ELit 1] (kpa_plan 574 235 0 0)).
Abbreviation kpa2_pl := (kpa2_pl_ tt).
