(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan H0PlanImage H0Atable H0CheckG H0Batch.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import CAP.
Open Scope Z_scope.

Lemma hbatch_app : forall LIM BF FUEL rs a b,
  (let it := APC.mk_itab_ranges HSEGS rs in hbatch_ok LIM BF FUEL it (a ++ b)) = true ->
  (let it := APC.mk_itab_ranges HSEGS rs in hbatch_ok LIM BF FUEL it a) = true
  /\ (let it := APC.mk_itab_ranges HSEGS rs in hbatch_ok LIM BF FUEL it b) = true.
Proof.
  intros LIM BF FUEL rs a b H. cbv zeta in *. unfold hbatch_ok in *. rewrite forallb_app in H. apply andb_prop in H. exact H.
Qed.
