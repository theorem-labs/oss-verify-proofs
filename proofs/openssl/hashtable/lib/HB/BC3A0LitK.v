(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan BC3A0Lit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP. Open Scope Z_scope.
Definition lockw_fact : kentry := KWord (SA (ELit 0) 6940554) 2 (ELit 0).
Definition c3a0_hs98k_ (_ : unit) : acs := add_kn c3a0_hs98 [lockw_fact].
Abbreviation c3a0_hs98k := (c3a0_hs98k_ tt).
Definition C3A0K_HS (h : nat) : option acs := if Nat.eqb h 20 then Some c3a0_hs20 else if Nat.eqb h 98 then Some c3a0_hs98k else None.
