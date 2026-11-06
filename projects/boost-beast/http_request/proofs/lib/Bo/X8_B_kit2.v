(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ub Require Import XUbsan.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma lor_land7 : forall a b, a mod 8 = 0 -> b mod 8 = 0 -> Z.land (Z.lor a b) 7 = 0.
Proof.
  intros a b Ha Hb. rewrite Z.land_lor_distr_l, !land7_mod8, Ha, Hb. reflexivity.
Qed.

Ltac notrap_or7 A B :=
  let K := fresh "KT" in
  step; if_cases K; zify_cond K;
  [ exfalso; first [ rewrite (lor_land7 _ _ A B) in K; lia
                   | let t := type of K in fail 100 "notrap_or7: cannot refute the trap condition" t ]
  | clear K ].
