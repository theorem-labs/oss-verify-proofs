(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.

From Stdlib Require Import ZArith Lia.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnW Require Import BnCalls W_mul_recursive W_mul_part_recursive HxComba8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma cs8_288_0 : (0 <= 288)%Z. Proof. lia. Qed.

Theorem bn_mul_recursive_closed : forall k, rec_spec_at 288 k.
Proof. exact (bn_mul_recursive_spec 288 cs8_288_0 comba8_ok). Qed.

Theorem bn_mul_part_recursive_closed : forall fuel, part_spec_at 288 fuel.
Proof. exact (bn_mul_part_recursive_spec 288 cs8_288_0 comba8_ok). Qed.
