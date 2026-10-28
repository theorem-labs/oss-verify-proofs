(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan AsanNodesIO BKInv BKE9B2Lit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition kc9b2_S_ (_ : unit) : acs := kcompact ke9b2_hs209.
Abbreviation kc9b2_S := (kc9b2_S_ tt).
Definition kc9b2_pl_ (_ : unit) : plan := (PCompact (PHandoff 309)).
Abbreviation kc9b2_pl := (kc9b2_pl_ tt).
