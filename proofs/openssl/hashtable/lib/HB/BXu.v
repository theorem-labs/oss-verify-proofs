(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition xu_plan : plan :=
  PRun [] (* [comment removed for export] *)
  (PExit).

Definition xu_ranges : list (Z * nat) := [(0x1ee978, 1513%nat); (0x554b84, 1021%nat); (0x55bb78, 1024%nat); (0x561b78, 1024%nat)].
