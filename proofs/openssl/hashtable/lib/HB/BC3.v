(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan BC3m BC3m3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition c3_top_ (_ : unit) : plan := PSplit (EVar 1) 1 (PX XLayout [ELit 0] c3m_plan) (PSplit (EVar 1) 2 (PHandoff 98) (PX XLayout [ELit 1] c3m3_plan)).
Abbreviation c3_top := (c3_top_ tt).
Definition c3_plan_ (_ : unit) : plan := c3_top.
Abbreviation c3_plan := (c3_plan_ tt).
(* [comment removed for export] *)
Definition c3_ranges : list (Z * nat) := c3m_ranges ++ c3m3_ranges.
