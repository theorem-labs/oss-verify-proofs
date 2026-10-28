(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan AsanNodesIO BKInv BKE4A1Lit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition kc4a1_S_ (_ : unit) : acs := kcompact ke4a1_hs204.
Abbreviation kc4a1_S := (kc4a1_S_ tt).
Definition kc4a1_pl_ (_ : unit) : plan := (PCompact (PHandoff 304)).
Abbreviation kc4a1_pl := (kc4a1_pl_ tt).
