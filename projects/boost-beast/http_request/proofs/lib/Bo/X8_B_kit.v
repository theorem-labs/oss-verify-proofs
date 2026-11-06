(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ub Require Import XUbsan.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma nullbase_xor_1 : forall b s, 0 < b -> 0 < s -> Z.lxor (Z.b2z (0 <? b)) (Z.b2z (s <? 1)) = 1.
Proof.
  intros b s Hb Hs.
  replace (0 <? b) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (s <? 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

Ltac notrap15 :=
  let K := fresh "KT" in
  step; if_cases K; zify_cond K;
  [ exfalso; first [ rewrite land15_mod16 in K; lia
                   | let t := type of K in fail 100 "notrap15: cannot refute the trap condition" t ]
  | clear K ].

Ltac notrap_lit :=
  let K := fresh "KT" in
  step; if_cases K; zify_cond K;
  [ exfalso; rewrite ?unsigned_lit in K by lia; first [ lia | let t := type of K in fail 100 "notrap_lit: cannot refute the trap condition" t ]
  | clear K ].

Ltac nullbase1 b s := rewrite (nullbase_xor_1 b s) by lia.
