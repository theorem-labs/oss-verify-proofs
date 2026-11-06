(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import PropExec MState Mem Cells Step Image Arr.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.B9 Require Import ImageA RT_iface Lept_iface LeptL_kit Ed_iface.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition JT_GETPIXEL : Z := 0x317ac.
Definition JT_GETPIXEL_0 : Z := 0xc5388.

(* [comment removed for export] *)
Lemma ro_cells_lit : forall (m : mem) A (cs : list cell),
  mem_inv asegs m -> cells_wf cs -> ro_bytes_b asegs A (cells_bytes cs) = true -> 0 <= A ->
  A + Z.of_nat (length (cells_bytes cs)) <= 2^64 ->
  ro_cells asegs m A cs.
Proof.
  intros m A cs MI WF RB HA HL. split; [exact WF|].
  apply ro_bytes_at; [exact MI| lia| exact HL| apply ro_bytes_b_sound; exact RB].
Qed.

Lemma jt_getpixel : forall m : mem, mem_inv asegs m -> ro_cells asegs m JT_GETPIXEL [C4 (Z_to_bv 64 JT_GETPIXEL_0)].
Proof.
  intros m MI. apply (ro_cells_lit m JT_GETPIXEL _ MI); [cbn; tauto| vm_compute; reflexivity| unfold JT_GETPIXEL; lia| cbn; unfold JT_GETPIXEL; lia].
Qed.

(* [comment removed for export] *)
Definition raster_word (dbs : list byte) (k : Z) : word :=
  Z_to_bv 64 (bytes_le_to_Z (firstn 4 (skipn (Z.to_nat (4 * k)) dbs)) mod 2^32).

Lemma raster_word_le4 : forall dbs k, 0 <= k -> 4 * k + 4 <= Z.of_nat (length dbs) ->
  le4 (raster_word dbs k) = firstn 4 (skipn (Z.to_nat (4 * k)) dbs).
Proof.
  intros dbs k Hk Hl. unfold raster_word, le4. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
  rewrite (Z_to_le_bytes_mod 4 _ 64) by lia. rewrite (Z_to_le_bytes_mod 4 _ 32) by lia.
  remember (firstn 4 (skipn (Z.to_nat (4 * k)) dbs)) as l eqn:El.
  assert (L : length l = 4%nat) by (subst l; rewrite firstn_length_le; [reflexivity| rewrite length_skipn; lia]).
  rewrite <- L. exact (le_bytes_roundtrip l).
Qed.

Lemma raster_word_range : forall dbs k, 0 <= bv_unsigned (raster_word dbs k) < 2^32.
Proof.
  intros dbs k. unfold raster_word. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64).
  pose proof (Z.mod_pos_bound (bytes_le_to_Z (firstn 4 (skipn (Z.to_nat (4 * k)) dbs))) (2^32) ltac:(lia)) as B.
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma bytes_at_mid : forall (m : mem) A bs (k n : nat), bytes_at asegs m A bs -> (k + n <= length bs)%nat ->
  bytes_at asegs m (A + Z.of_nat k) (firstn n (skipn k bs)).
Proof.
  intros m A bs k n (Ha & Hl & H) Hk. split; [lia|]. split.
  - rewrite firstn_length_le by (rewrite length_skipn; lia). lia.
  - intros i Hi. rewrite firstn_length_le in Hi by (rewrite length_skipn; lia).
    replace (A + Z.of_nat k + Z.of_nat i) with (A + Z.of_nat (k + i)) by lia. rewrite (H (k + i)%nat) by lia.
    rewrite nth_error_firstn. replace (PeanoNat.Nat.ltb i n) with true by (symmetry; apply PeanoNat.Nat.ltb_lt; exact Hi).
    rewrite nth_error_skipn. reflexivity.
Qed.

Lemma wr_at_sub : forall (m : mem) A n a k, wr_at asegs m A n -> A <= a -> a + k <= A + n -> 0 <= k -> wr_at asegs m a k.
Proof.
  intros m A n a k (HA & Hn & H) H1 H2 Hk. split; [lia|]. split; [lia|].
  intros i Hi. replace (a + i) with (A + (a - A + i)) by lia. apply H. lia.
Qed.

(* [comment removed for export] *)
Lemma raster_read : forall (m : mem) A dbs k a, bytes_at asegs m A dbs -> 0 <= k -> 4 * k + 4 <= Z.of_nat (length dbs) ->
  a = wa (A + 4 * k) -> ov_read_bytes asegs m a 4 = Some (le4 (raster_word dbs k)).
Proof.
  intros m A dbs k a Hb Hk Hl ->. rewrite (raster_word_le4 dbs k Hk Hl).
  pose proof (bytes_at_ov_read asegs m A dbs (Z.to_nat (4 * k)) 4 Hb ltac:(lia)) as R. rewrite Z2Nat.id in R by lia. exact R.
Qed.

(* [comment removed for export] *)
Lemma raster_cell : forall (m : mem) A n dbs k, rw_cells asegs m A [CB n dbs] -> 0 <= k -> 4 * k + 4 <= Z.of_nat n ->
  rw_cells asegs m (A + 4 * k) [C4 (raster_word dbs k)].
Proof.
  intros m A n dbs k H Hk Hl. pose proof (u8arr_of_rw_cells asegs m A n dbs H) as [Hb Hw].
  pose proof H as [[[L _] _] _]. cbn in L.
  split.
  - split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. rewrite (raster_word_le4 dbs k Hk ltac:(lia)).
    replace (A + 4 * k) with (A + Z.of_nat (Z.to_nat (4 * k))) by lia.
    apply (bytes_at_mid m A dbs (Z.to_nat (4 * k)) 4 Hb). lia.
  - cbn [cells_size csize Nat.add]. apply (wr_at_sub m A (Z.of_nat (length dbs))); [exact Hw| lia| lia| lia].
Qed.

(* [comment removed for export] *)
Lemma getbit_eq : forall (wd : word) (x : Z), 0 <= bv_unsigned wd < 2^32 -> 0 <= x < 2^31 ->
  Z.land (bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (sx32 wd))) (Z.lxor x 18446744073709551615 mod 32)) mod 18446744073709551616) 1
  = Z.b2z (Z.testbit (bv_unsigned wd) (31 - x mod 32)).
Proof.
  intros wd x Hu Hx. set (u := bv_unsigned wd) in *.
  assert (HS : Z.lxor x 18446744073709551615 mod 32 = 31 - x mod 32).
  { pose proof (Z.add_lxor_2land x 18446744073709551615) as E.
    change (Z.land x 18446744073709551615) with (Z.land x (Z.ones 64)) in E.
    rewrite Z.land_ones in E by lia. rewrite Z.mod_small in E by lia.
    replace (Z.lxor x 18446744073709551615) with (18446744073709551615 - x) by lia.
    Z.div_mod_to_equations. lia. }
  rewrite HS. set (s := 31 - x mod 32).
  assert (HSR : 0 <= s < 32) by (subst s; Z.div_mod_to_equations; lia).
  assert (HW : bv_wrap 32 (bv_unsigned (sx32 wd)) = u).
  { unfold sx32. rewrite Z_to_bv_unsigned. fold u. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
    change (2 ^ Z.of_N 32) with 4294967296. change (2 ^ Z.of_N 64) with 18446744073709551616. change (4294967296 / 2) with 2147483648.
    Z.div_mod_to_equations. lia. }
  rewrite HW. rewrite (Z.shiftr_div_pow2 u s) by lia. rewrite Z.testbit_spec' by lia.
  assert (P0 : 0 < 2 ^ s) by (apply Z.pow_pos_nonneg; lia).
  set (q := u / 2 ^ s) in *.
  assert (HQ : 0 <= q < 4294967296).
  { subst q. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. nia. }
  change (Z.land (bv_swrap 32 q mod 18446744073709551616) 1) with (Z.land (bv_swrap 32 q mod 18446744073709551616) (Z.ones 1)).
  rewrite Z.land_ones by lia. change (2 ^ 1) with 2.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with 4294967296. change (4294967296 / 2) with 2147483648.
  clearbody q. clear - HQ. Z.div_mod_to_equations. lia.
Qed.
