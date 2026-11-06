(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.openssl.bignum.lib.BgHXB Require HxbSqr4 HxbSqr8.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require Import ARun.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require Import AW_sqr_words AW_sqr_normal AW_sqr_recursive.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition CSQ4A : Z := 112.
Definition CSQ8A : Z := 352.
Definition CSLA : Z := 352.

Lemma sqr_comba4_okA : sqr_comba4_aspec CSQ4A.
Proof. exact HxbSqr4.sqr_comba4_okA. Qed.
Lemma sqr_comba8_okA : sqr_comba8_aspec CSQ8A.
Proof. exact HxbSqr8.sqr_comba8_okA. Qed.

Section Closed.
  Context {AR : ARun}.
  Theorem bn_sqr_recursive_closedA : forall k, sqr_rec_spec_atA CSLA k.
  Proof.
    exact (bn_sqr_recursive_aspec CSQ4A CSQ8A CSLA ltac:(unfold CSQ4A; lia) ltac:(unfold CSQ8A; lia) ltac:(unfold CSQ4A, CSLA; lia) ltac:(unfold CSQ8A, CSLA; lia)
             sqr_comba4_okA sqr_comba8_okA).
  Qed.
End Closed.
