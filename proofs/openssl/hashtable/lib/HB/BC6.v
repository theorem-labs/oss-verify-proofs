(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan BC4e BC6a BC6b BC6c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition c6_top0_ (_ : unit) : plan := PX XLayout [ELit 1] (PSplit (EVar 6) 6 c6a_plan c6b_plan).
Abbreviation c6_top0 := (c6_top0_ tt).
Definition c6_top1_ (_ : unit) : plan := PX XLayout [ELit 1] c6c_plan.
Abbreviation c6_top1 := (c6_top1_ tt).
Definition c6_ranges : list (Z * nat) := c6a_ranges ++ c6b_ranges ++ c6c_ranges ++ c4e_ranges.
