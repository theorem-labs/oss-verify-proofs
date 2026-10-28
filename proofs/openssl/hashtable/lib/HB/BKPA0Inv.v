(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan AsanNodesIO BKInv BC3A0Lit BC3A0LitK BC4A0Lit BC4e BKPa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition kpa0_S_ (_ : unit) : acs := kcompact c3a0_hs98k.
Abbreviation kpa0_S := (kpa0_S_ tt).
Definition kpa0_pl_ (_ : unit) : plan := (PX XLayout [ELit 1] (kpa_plan 574 235 0 0)).
Abbreviation kpa0_pl := (kpa0_pl_ tt).
