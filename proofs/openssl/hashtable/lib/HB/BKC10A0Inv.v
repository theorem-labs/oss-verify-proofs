(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan AsanNodesIO BKInv BKE10A0Lit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition kc10a0_S_ (_ : unit) : acs := kcompact ke10a0_hs210.
Abbreviation kc10a0_S := (kc10a0_S_ tt).
Definition kc10a0_pl_ (_ : unit) : plan := (PCompact (PHandoff 310)).
Abbreviation kc10a0_pl := (kc10a0_pl_ tt).
