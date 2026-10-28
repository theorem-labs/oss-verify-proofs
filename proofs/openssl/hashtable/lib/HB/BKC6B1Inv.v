(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan AsanNodesIO BKInv BKE6B1Lit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition kc6b1_S_ (_ : unit) : acs := kcompact ke6b1_hs206.
Abbreviation kc6b1_S := (kc6b1_S_ tt).
Definition kc6b1_pl_ (_ : unit) : plan := (PCompact (PHandoff 306)).
Abbreviation kc6b1_pl := (kc6b1_pl_ tt).
