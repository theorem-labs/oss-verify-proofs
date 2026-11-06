(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan C4e C7a C7b C7c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition c7_top0_ (_ : unit) : plan := PX XLayout [ELit 1] (PSplit (EVar 6) 6 c7a_plan c7b_plan).
Abbreviation c7_top0 := (c7_top0_ tt).
Definition c7_top1_ (_ : unit) : plan := PX XLayout [ELit 1] c7c_plan.
Abbreviation c7_top1 := (c7_top1_ tt).
Definition c7_ranges : list (Z * nat) := c7a_ranges ++ c7b_ranges ++ c7c_ranges ++ c4e_ranges.
