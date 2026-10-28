(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan AsanNodesIO BKInv BKE4B0Lit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition kc4b0_S_ (_ : unit) : acs := kcompact ke4b0_hs204.
Abbreviation kc4b0_S := (kc4b0_S_ tt).
Definition kc4b0_pl_ (_ : unit) : plan := (PCompact (PHandoff 304)).
Abbreviation kc4b0_pl := (kc4b0_pl_ tt).
