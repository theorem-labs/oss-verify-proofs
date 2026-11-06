(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac ZBridge TacX.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ub Require Import XUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma nullbase_xor_pos : forall b s, 0 < b -> 0 < s -> Z.lxor (Z.b2z (0 <? b)) (Z.b2z (s <? 1)) = 1.
Proof.
  intros b s Hb Hs. destruct (Z.ltb_spec 0 b); destruct (Z.ltb_spec s 1); cbn; first [reflexivity | exfalso; lia].
Qed.

(* [comment removed for export] *)
Lemma nullbase_xor1 : forall x, 0 <= x -> Z.lxor (Z.b2z (0 <? x)) (Z.b2z (x <? 1)) = 1.
Proof.
  intros x Hx. destruct (Z.ltb_spec 0 x); destruct (Z.ltb_spec x 1); cbn; first [reflexivity | exfalso; lia].
Qed.

(* [comment removed for export] *)
Lemma nullbase_xor : forall b s, 0 <= b <= s -> (0 < s -> 0 < b) -> Z.lxor (Z.b2z (0 <? b)) (Z.b2z (s <? 1)) = 1.
Proof.
  intros b s H1 H2. destruct (Z.ltb_spec 0 b); destruct (Z.ltb_spec s 1); cbn; first [reflexivity | exfalso; lia].
Qed.

Lemma m1_lit : Z_to_bv 64 (-1) = Z_to_bv 64 18446744073709551615.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Ltac notrap_ft :=
  let K := fresh "KT" in
  step; if_cases K; zify_cond K; [ clear K | exfalso; first [ lia | rewrite land7_mod8 in K; lia ] ].

Ltac at_pc PC WS :=
  lazymatch goal with |- evt ?S ?Q (MS ?r ?f _ ?fc ?sv ?mem ?rom) =>
    assert (WS : evt S Q (MS r f (Z_to_bv 64 PC) fc sv mem rom)) end.
