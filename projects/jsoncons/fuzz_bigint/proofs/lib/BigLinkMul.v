(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import BigLinkBase BigLinkMulAlg.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require BigModel BigFactsBase BigFactsDigits.
Import -(notations) BigModel BigFactsBase BigFactsDigits.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module BM.
Import BMA.
Lemma nth_error_single {A} (x y : A) i : nth_error [x] i = Some y -> y = x.
Proof. destruct i; simpl. congruence. destruct i; discriminate. Qed.
Lemma step_vals V i : 0 <= V ->
  mlo (wordi V i) (mcarry 10 V i) = wordi (10 * V) i /\ mcar (wordi V i) (mcarry 10 V i) = mcarry 10 V (S i).
Proof. intros HV. exact (mul_limb_step 10 V i ltac:(unfold wordZ; rewrite M_val; lia) HV). Qed.
Lemma mcarry10_range V i : 0 <= mcarry 10 V i < 10.
Proof. pose proof (mcarry_bound 10 V i ltac:(lia)). lia. Qed.
Lemma wordi_bound V i : 0 <= wordi V i < 2 ^ 64.
Proof. pose proof (wordi_range V i) as H. unfold wordZ in H. rewrite M_val in H. exact H. Qed.
End BM.
