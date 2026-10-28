(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan AsanNodesIO BKInv BKE5A0Lit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition kc5a0_S_ (_ : unit) : acs := kcompact ke5a0_hs205.
Abbreviation kc5a0_S := (kc5a0_S_ tt).
Definition kc5a0_pl_ (_ : unit) : plan := (PCompact (PHandoff 305)).
Abbreviation kc5a0_pl := (kc5a0_pl_ tt).
