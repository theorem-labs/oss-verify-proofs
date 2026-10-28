(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan AsanNodesIO BKInv BKE5B3Lit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition kc5b3_S_ (_ : unit) : acs := kcompact ke5b3_hs205.
Abbreviation kc5b3_S := (kc5b3_S_ tt).
Definition kc5b3_pl_ (_ : unit) : plan := (PCompact (PHandoff 305)).
Abbreviation kc5b3_pl := (kc5b3_pl_ tt).
