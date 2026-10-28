(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan AsanNodesIO BKInv BC3A3Lit BC3A3LitK BC4A3Lit BC4e BKPb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition kpa3_S_ (_ : unit) : acs := kcompact c3a3_hs98k.
Abbreviation kpa3_S := (kpa3_S_ tt).
Definition kpa3_pl_ (_ : unit) : plan := (PX XLayout [ELit 1] (kpb_plan 574 235 0 0)).
Abbreviation kpa3_pl := (kpa3_pl_ tt).
