(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan AsanNodesIO BKInv BKE7A2Lit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition kc7a2_S_ (_ : unit) : acs := kcompact ke7a2_hs207.
Abbreviation kc7a2_S := (kc7a2_S_ tt).
Definition kc7a2_pl_ (_ : unit) : plan := (PCompact (PHandoff 307)).
Abbreviation kc7a2_pl := (kc7a2_pl_ tt).
