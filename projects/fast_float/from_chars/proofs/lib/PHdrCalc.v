(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec MuslStrlen.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Lemma hdr_calc : forall d0 d1 : byte,
  bv_unsigned (v_or (alu64 ALU_SRL (alu64 ALU_SLL (v_lb d1) (zext 64 (57 : bv 6))) (zext 64 (49 : bv 6))) (Z_to_bv 64 (bv_unsigned d0)))
  = bv_unsigned d0 + 256 * (bv_unsigned d1 mod 128).
Proof.
  intros d0 d1. pose proof (bv_unsigned_in_range _ d0) as R0. pose proof (bv_unsigned_in_range _ d1) as R1.
  unfold bv_modulus in R0, R1. change (2 ^ Z.of_N 8) with 256 in R0, R1.
  unfold alu64, alu.
  replace (bv_and (zext 64 (57 : bv 6)) (Z_to_bv 64 63)) with (Z_to_bv 64 57 : word) by (apply bv_eq; reflexivity).
  replace (bv_and (zext 64 (49 : bv 6)) (Z_to_bv 64 63)) with (Z_to_bv 64 49 : word) by (apply bv_eq; reflexivity).
  set (u0 := bv_unsigned d0) in *. set (u1 := bv_unsigned d1) in *.
  assert (Hs : exists q, bv_signed d1 = u1 - 256 * q).
  { exists ((u1 + 128) / 256). unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. fold u1.
    change (2 ^ Z.of_N 8) with 256. change (256 `div` 2) with 128. rewrite Z.mod_eq by lia. lia. }
  destruct Hs as (q & Hq).
  set (x := bv_unsigned (v_lb d1)).
  assert (Hx : x mod 128 = u1 mod 128).
  { unfold x, v_lb. rewrite Z_to_bv_unsigned, Hq. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616.
    rewrite (Z.mod_eq (u1 - 256 * q) 18446744073709551616) by lia.
    replace (u1 - 256 * q - 18446744073709551616 * ((u1 - 256 * q) / 18446744073709551616))
      with (u1 + (- 2 * q - 144115188075855872 * ((u1 - 256 * q) / 18446744073709551616)) * 128) by lia.
    apply Z_mod_plus_full. }
  assert (Hx0 : 0 <= x < 2^64) by (unfold x; apply bv_unsigned_in_range).
  assert (Hsl : bv_unsigned (bv_shiftl (v_lb d1) (Z_to_bv 64 57)) = (u1 mod 128) * 2^57).
  { rewrite bv_shiftl_unsigned. fold x. replace (bv_unsigned (Z_to_bv 64 57 : word)) with 57 by reflexivity.
    rewrite Z.shiftl_mul_pow2 by lia. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (128 * 2^57).
    rewrite Z.mul_mod_distr_r by lia. rewrite Hx. reflexivity. }
  assert (Hsr : bv_unsigned (bv_shiftr (bv_shiftl (v_lb d1) (Z_to_bv 64 57)) (Z_to_bv 64 49)) = (u1 mod 128) * 256).
  { rewrite bv_shiftr_unsigned, Hsl. replace (bv_unsigned (Z_to_bv 64 49 : word)) with 49 by reflexivity.
    rewrite Z.shiftr_div_pow2 by lia. replace ((u1 mod 128) * 2^57) with ((u1 mod 128) * 256 * 2^49) by (change (2^57) with (256 * 2^49); lia).
    apply Z.div_mul. lia. }
  unfold v_or. rewrite Z_to_bv_unsigned. rewrite Hsr. replace (bv_unsigned (Z_to_bv 64 u0 : word)) with u0 by (rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 64) with 18446744073709551616; symmetry; apply Z.mod_small; lia).
  rewrite Z.lor_comm. replace ((u1 mod 128) * 256) with (Z.shiftl (u1 mod 128) 8) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
  rewrite lor_shiftl8 by (pose proof (Z.mod_pos_bound u1 128); lia).
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616. apply Z.mod_small. pose proof (Z.mod_pos_bound u1 128). lia.
Qed.
