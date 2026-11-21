(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import MState Mem Cells ZBridge.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma lor_disj_add : forall a b k, 0 <= k -> 0 <= b < 2 ^ k -> 0 <= a -> Z.lor (Z.shiftl a k) b = a * 2 ^ k + b.
Proof.
  intros a b k Hk Hb Ha. rewrite Z.shiftl_mul_pow2 by lia.
  assert (LAND : Z.land (a * 2 ^ k) b = 0).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.ltb_spec n k).
    - rewrite Z.mul_pow2_bits_low by lia. reflexivity.
    - replace (Z.testbit b n) with false; [apply Bool.andb_false_r|]. symmetry.
      destruct (Z.eq_dec b 0) as [->|NZ]; [apply Z.bits_0|]. apply Z.bits_above_log2; [lia|].
      apply Z.lt_le_trans with k; [apply Z.log2_lt_pow2; lia| lia]. }
  rewrite <- (Z.lxor_lor _ _ LAND). symmetry. apply Z.add_nocarry_lxor. exact LAND.
Qed.

Lemma lor_code_pack : forall op hb val, 0 <= op < 256 -> 0 <= hb < 256 -> 0 <= val < 65536 ->
  Z.lor (Z.shiftl val 16) (Z.lor op (Z.shiftl hb 8)) = code_pack op hb val.
Proof.
  intros op hb val Ho Hh Hv. rewrite (Z.lor_comm op), (lor_disj_add hb op 8) by lia.
  rewrite (lor_disj_add val (hb * 2 ^ 8 + op) 16) by lia.
  unfold code_pack, wrap8, wrap16. change 255 with (Z.ones 8). change 65535 with (Z.ones 16). rewrite !Z.land_ones by lia.
  rewrite !Z.mod_small by lia. change (2 ^ 8) with 256. change (2 ^ 16) with 65536. lia.
Qed.

Lemma zbv8_congr' : forall x y, (x - y) mod 256 = 0 -> Z_to_bv 8 x = Z_to_bv 8 y.
Proof.
  intros x y H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
  apply Z.mod_divide in H; [|lia]. destruct H as [q Hq]. replace x with (y + q * 256) by lia. apply Z.mod_add. lia.
Qed.

Lemma entry_halves : forall h, 0 <= h < 4294967296 ->
  cells_bytes [C2 (Z_to_bv 64 h); C2 (Z_to_bv 64 (Z.shiftr h 16))] = le4 (Z_to_bv 64 h).
Proof.
  intros h Hh. assert (HS : 0 <= Z.shiftr h 16 < 65536) by (rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 16) with 65536; Z.div_mod_to_equations; lia).
  cbn [cells_bytes cbytes app]. unfold le4, le2. rewrite !unsigned_lit by lia.
  cbn [Z_to_le_bytes]. rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256. change (2 ^ 16) with 65536.
  cbn [app].
  f_equal. f_equal.
  f_equal; [apply zbv8_congr'; Z.div_mod_to_equations; lia|].
  f_equal. apply zbv8_congr'; Z.div_mod_to_equations; lia.
Qed.
