(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan BC3B2Lit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP. Open Scope Z_scope.
Definition lockw_fact : kentry := KWord (SA (ELit 0) 6940554) 2 (ELit 0).
Definition c3b2_hs98k_ (_ : unit) : acs := add_kn c3b2_hs98 [lockw_fact].
Abbreviation c3b2_hs98k := (c3b2_hs98k_ tt).
Definition C3B2K_HS (h : nat) : option acs := if Nat.eqb h 20 then Some c3b2_hs20 else if Nat.eqb h 98 then Some c3b2_hs98k else None.
