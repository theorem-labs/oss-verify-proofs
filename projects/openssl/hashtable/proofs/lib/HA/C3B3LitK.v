(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan C3B3Lit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP. Open Scope Z_scope.
Definition lockw_fact : kentry := KWord (SA (ELit 0) 6732618) 2 (ELit 0).
Definition c3b3_hs98k_ (_ : unit) : acs := add_kn c3b3_hs98 [lockw_fact].
Abbreviation c3b3_hs98k := (c3b3_hs98k_ tt).
Definition C3B3K_HS (h : nat) : option acs := if Nat.eqb h 20 then Some c3b3_hs20 else if Nat.eqb h 98 then Some c3b3_hs98k else None.
