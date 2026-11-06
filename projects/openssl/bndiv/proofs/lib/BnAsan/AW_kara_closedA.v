(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From OSSVerify.Proofs.openssl.bndiv.lib.HXA Require HxaComba8.
From OSSVerify.Proofs.openssl.bndiv.lib.BnAsan Require Import ARun BnCallsKA AW_mul_recursive AW_mul_rec_top AW_mul_part_recursive.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition CS8A : Z := 528%Z.

Lemma CS8A_0 : (0 <= CS8A)%Z.
Proof. unfold CS8A. lia. Qed.

Lemma comba8_okA : comba8_aspec CS8A.
Proof. exact HxaComba8.comba8_okA. Qed.

Section Closed.
  Context {AR : ARun}.

  (* [comment removed for export] *)
  Theorem bn_mul_recursive_closedA : forall k, rec_spec_atA CS8A k.
  Proof. exact (bn_mul_recursive_aspec CS8A CS8A_0 comba8_okA). Qed.

  (* [comment removed for export] *)
  Theorem bn_mul_part_recursive_closedA : forall fuel, part_spec_atA CS8A fuel.
  Proof. exact (bn_mul_part_recursive_aspec CS8A CS8A_0 comba8_okA). Qed.
End Closed.

(* [comment removed for export] *)
