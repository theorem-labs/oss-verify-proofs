(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma p5u_sw : forall e d, -342 <= e <= 308 -> 684 <= d <= 685 ->
  bv_swrap 32 (Z.shiftl (e mod 18446744073709551616) 1 mod 18446744073709551616 + d) mod 18446744073709551616 = 2 * e + d.
Proof.
  intros e d HE Hd. rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with 4294967296. change (4294967296 / 2) with 2147483648.
  lia.
Qed.

Lemma p5u_sw' : forall e d, -342 <= e <= 308 -> 684 <= d <= 685 ->
  bv_swrap 32 (Z.shiftl (e mod 18446744073709551616) 1 + d) mod 18446744073709551616 = 2 * e + d.
Proof.
  intros e d HE Hd. rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with 4294967296. change (4294967296 / 2) with 2147483648.
  lia.
Qed.
