(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan AsanNodesIO BKInv BKE10B3Lit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition kc10b3_S_ (_ : unit) : acs := kcompact ke10b3_hs210.
Abbreviation kc10b3_S := (kc10b3_S_ tt).
Definition kc10b3_pl_ (_ : unit) : plan := (PCompact (PHandoff 310)).
Abbreviation kc10b3_pl := (kc10b3_pl_ tt).
