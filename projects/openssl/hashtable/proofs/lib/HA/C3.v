(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan C3m C3m3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.
Definition c3_top_ (_ : unit) : plan := PSplit (EVar 1) 1 (PX XLayout [ELit 0] c3m_plan) (PSplit (EVar 1) 2 (PHandoff 98) (PX XLayout [ELit 1] c3m3_plan)).
Abbreviation c3_top := (c3_top_ tt).
Definition c3_plan_ (_ : unit) : plan := c3_top.
Abbreviation c3_plan := (c3_plan_ tt).
(* [comment removed for export] *)
Definition c3_ranges : list (Z * nat) := c3m_ranges ++ c3m3_ranges.
