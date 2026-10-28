(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzDefs. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope bv_scope.

(* [comment removed for export] *)
Lemma zn_maskF : forall g, (1 <= g <= 20)%Z ->
  Z.lxor (Z.land (bv_swrap 32 (Z.shiftl 18446744073709551615 (g mod 32))) 18446744073709551615) 18446744073709551615 = (2 ^ g - 1)%Z.
Proof.
  intros g Hg.
  assert (H : forallb (fun n => Z.eqb (Z.lxor (Z.land (bv_swrap 32 (Z.shiftl 18446744073709551615 (Z.of_nat n mod 32))) 18446744073709551615) 18446744073709551615)
                                      (2 ^ Z.of_nat n - 1)) (seq 1 20) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in H. specialize (H (Z.to_nat g)). rewrite Z2Nat.id in H by lia.
  apply Z.eqb_eq. apply H. apply in_seq. lia.
Qed.

(* [comment removed for export] *)
Lemma lor2_bitF : forall z b, (0 <= z)%Z -> (0 <= b <= 1)%Z -> Z.lor (z * 2) b = (2 * z + b)%Z.
Proof. intros z b Hz Hb. rewrite <- (lor_shiftl1_bit z b Hz Hb). rewrite Z.shiftl_mul_pow2 by lia. reflexivity. Qed.
Lemma lor2_bitF' : forall z b, (0 <= z)%Z -> (0 <= b <= 1)%Z -> Z.lor (2 * z) b = (2 * z + b)%Z.
Proof. intros z b Hz Hb. rewrite <- (lor_shiftl1_bit z b Hz Hb). rewrite Z.shiftl_mul_pow2 by lia. f_equal. lia. Qed.

(* [comment removed for export] *)
Lemma swrap32_sub_land64F : forall a b, bv_swrap 32 (a - Z.land b 18446744073709551615) = bv_swrap 32 (a - b).
Proof.
  intros a b. change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia.
  unfold bv_swrap, bv_wrap. f_equal.
  change (bv_modulus 32) with 4294967296%Z.
  rewrite (Z.div_mod b (2^64)) at 2 by lia.
  replace (a - (2 ^ 64 * (b / 2 ^ 64) + b mod 2 ^ 64) + bv_half_modulus 32)%Z
     with ((a - b mod 2 ^ 64 + bv_half_modulus 32) + (- (4294967296 * (b / 2 ^ 64))) * 4294967296)%Z by lia.
  rewrite Z_mod_plus_full. reflexivity.
Qed.
Lemma swrap32_sub_mod64 : forall a b, bv_swrap 32 (a - b mod 18446744073709551616) = bv_swrap 32 (a - b).
Proof.
  intros a b. unfold bv_swrap, bv_wrap. f_equal. change (bv_modulus 32) with 4294967296%Z.
  rewrite (Z.div_mod b 18446744073709551616) at 2 by lia.
  replace (a - (18446744073709551616 * (b / 18446744073709551616) + b mod 18446744073709551616) + bv_half_modulus 32)%Z
     with ((a - b mod 18446744073709551616 + bv_half_modulus 32) + (- (4294967296 * (b / 18446744073709551616))) * 4294967296)%Z by lia.
  rewrite Z_mod_plus_full. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma sx32_lit : forall v, (- 2147483648 <= v < 2147483648)%Z -> sx32 (Z_to_bv 64 v) = Z_to_bv 64 v.
Proof.
  intros v Hv. unfold sx32. f_equal. rewrite unsigned_lit_wrap.
  unfold bv_swrap, bv_wrap. change (bv_modulus 32) with 4294967296%Z. change (bv_half_modulus 32) with 2147483648%Z.
  change (2 ^ 64)%Z with 18446744073709551616%Z.
  rewrite (Z.add_mod (v mod 18446744073709551616) 2147483648 4294967296) by lia.
  rewrite (Z.mod_mod_divide v 18446744073709551616 4294967296) by (exists 4294967296%Z; reflexivity).
  rewrite <- (Z.add_mod v 2147483648 4294967296) by lia.
  rewrite Z.mod_small by lia. lia.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
