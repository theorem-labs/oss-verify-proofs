(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac ZBridge.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface InflateState RefInflateA_HEAD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma mod31_clang : forall x, 0 <= x < 2 ^ 64 ->
  ((x * 17256631552825064415) mod 2 ^ 64 < 595056260442243601 <-> x mod 31 = 0).
Proof.
  intros x Hx. change (2 ^ 64) with 18446744073709551616 in *.
  pose proof (Z.div_mod (x * 17256631552825064415) 18446744073709551616 ltac:(lia)) as DM.
  pose proof (Z.mod_pos_bound (x * 17256631552825064415) 18446744073709551616 ltac:(lia)) as RV.
  set (v := (x * 17256631552825064415) mod 18446744073709551616) in *.
  set (mq := (x * 17256631552825064415) / 18446744073709551616) in *.
  assert (E : 31 * v = x + 18446744073709551616 * (29 * x - 31 * mq)) by lia.
  set (n := 29 * x - 31 * mq) in *.
  assert (Rn : 0 <= n <= 30) by lia.
  pose proof (Z.div_mod x 31 ltac:(lia)) as DX. pose proof (Z.mod_pos_bound x 31 ltac:(lia)) as RX.
  split.
  - intros Hv. assert (n = 0 \/ n = 1) as [N0|N1] by lia.
    + lia.
    + exfalso. lia.
  - intros E0. rewrite E0 in DX.
    assert (N0 : n = 0).
    { assert (H16 : 31 * (v - x / 31 - 595056260442243600 * n) = 16 * n) by lia. lia. }
    lia.
Qed.

Lemma hd_x_clang : forall h, 0 <= h < 2 ^ 64 ->
  Z.land (Z.shiftr (Z.land (Z.shiftl h 56) 18446744073709551615) 48 + Z.shiftr h 8) 18446744073709551615 = hd_x h.
Proof.
  intros h Hh. unfold hd_x. change 18446744073709551615 with (Z.ones 64). rewrite !Z.land_ones by lia.
  rewrite Z.shiftl_mul_pow2, !Z.shiftr_div_pow2 by lia.
  change (2 ^ 56) with 72057594037927936. change (2 ^ 64) with 18446744073709551616 in *. change (2 ^ 48) with 281474976710656. change (2 ^ 8) with 256.
  Z.to_euclidean_division_equations. lia.
Qed.

Lemma land_pow2 : forall x k, 0 <= k -> Z.land x (2 ^ k) = (x / 2 ^ k) mod 2 * 2 ^ k.
Proof.
  intros x k Hk. change 2 with (2 ^ 1) at 3. rewrite <- Z.shiftr_div_pow2, <- Z.land_ones, <- Z.shiftl_mul_pow2 by lia.
  apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.pow2_bits_eqb by lia.
  destruct (Z.eqb_spec k n) as [->|NE].
  - rewrite Z.shiftl_spec by lia. rewrite Z.land_spec, Z.shiftr_spec by lia. replace (n - n) with 0 by lia.
    rewrite Z.ones_spec_low by lia. rewrite Z.add_0_l. rewrite !andb_true_r. reflexivity.
  - rewrite andb_false_r. symmetry. destruct (Z.ltb_spec n k).
    + apply Z.shiftl_spec_low. lia.
    + rewrite Z.shiftl_spec by lia. rewrite Z.land_spec. rewrite Z.ones_spec_high by lia. apply andb_false_r.
Qed.

Lemma fdict_clang : forall h, 0 <= h < 2 ^ 64 ->
  (Z.land (Z.shiftl h 50) 18446744073709551615 < 9223372036854775808 <-> Z.land (Z.shiftr h 4) 512 = 0).
Proof.
  intros h Hh. change 512 with (2 ^ 9). rewrite land_pow2 by lia.
  change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia.
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  change (2 ^ 50) with 1125899906842624. change (2 ^ 64) with 18446744073709551616 in *. change (2 ^ 4) with 16. change (2 ^ 9) with 512.
  Z.to_euclidean_division_equations. lia.
Qed.

Lemma dmax_clang : forall l, 0 <= l <= 7 -> bv_swrap 32 (Z.shiftl 256 (l mod 32)) = shl32 1 (l + 8).
Proof.
  intros l Hl. assert (C : l = 0 \/ l = 1 \/ l = 2 \/ l = 3 \/ l = 4 \/ l = 5 \/ l = 6 \/ l = 7) by lia.
  destruct C as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]; reflexivity.
Qed.
