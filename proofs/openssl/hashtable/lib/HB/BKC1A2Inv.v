(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan AsanNodesIO BKInv BKE1A2Lit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition kc1a2_S_ (_ : unit) : acs := kcompact ke1a2_hs201.
Abbreviation kc1a2_S := (kc1a2_S_ tt).
Definition kc1a2_pl_ (_ : unit) : plan := (PCompact (PHandoff 301)).
Abbreviation kc1a2_pl := (kc1a2_pl_ tt).
