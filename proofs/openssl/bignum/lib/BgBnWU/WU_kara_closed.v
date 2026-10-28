(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.

From Stdlib Require Import ZArith Lia.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnWU Require Import BnCallsU WU_mul_recursive WU_mul_part_recursive HxComba8U WU_kara_final.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma cs8_0 : (0 <= CS8)%Z. Proof. unfold CS8. lia. Qed.

Theorem bn_mul_recursive_closed : forall k, rec_uspec_at (kara_uleaf CS8) k.
Proof. exact (bn_mul_recursive_ufinal CS8 cs8_0 comba8_uok). Qed.

Theorem bn_mul_part_recursive_closed : forall fuel, part_uspec_at (kara_uleaf CS8) fuel.
Proof. exact (bn_mul_part_recursive_ufinal CS8 cs8_0 comba8_uok). Qed.
