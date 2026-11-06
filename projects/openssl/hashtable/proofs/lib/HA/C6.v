(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan C4e C6a C6b C6c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition c6_top0_ (_ : unit) : plan := PX XLayout [ELit 1] (PSplit (EVar 6) 6 c6a_plan c6b_plan).
Abbreviation c6_top0 := (c6_top0_ tt).
Definition c6_top1_ (_ : unit) : plan := PX XLayout [ELit 1] c6c_plan.
Abbreviation c6_top1 := (c6_top1_ tt).
Definition c6_ranges : list (Z * nat) := c6a_ranges ++ c6b_ranges ++ c6c_ranges ++ c4e_ranges.
