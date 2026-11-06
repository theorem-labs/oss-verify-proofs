(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes PropExec MState Mem Cells Step Frame.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import BImg RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import CJ_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Lemma rw_cells_rebytes : forall m a cs cs', cells_wf cs' -> cells_bytes cs = cells_bytes cs' -> cells_size cs = cells_size cs' ->
  rw_cells bsegs m a cs -> rw_cells bsegs m a cs'.
Proof.
  intros m a cs cs' WF' EB ES [[Hwf HB] HW]. split; [split; [exact WF'| rewrite <- EB; exact HB]| rewrite <- ES; exact HW].
Qed.

Lemma zb8_eq : forall x y, x mod 256 = y mod 256 -> Z_to_bv 8 x = Z_to_bv 8 y.
Proof. intros x y H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. exact H. Qed.

(* [comment removed for export] *)
Lemma hdr_word_bytes : forall s (b : byte) h, 0 <= s < 256 -> 0 <= h < 65536 ->
  cells_bytes [C1 (zb s); C1 b; C2 (wz h)] = cells_bytes [C4 (wz (s + 256 * (bv_unsigned b + 256 * h)))].
Proof.
  intros s b h Hs Hh. pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb. cbn in Rb.
  cbn [cells_bytes cbytes app]. unfold le2, le4, wz, zb. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
  rewrite (Z.mod_small h), (Z.mod_small (s + 256 * (bv_unsigned b + 256 * h))) by lia.
  cbn [Z_to_le_bytes]. rewrite !Z.shiftr_shiftr by lia. cbn [Z.add Pos.add Pos.succ]. rewrite !Z.shiftr_div_pow2 by lia.
  change (2^8) with 256. change (2^(8+8)) with 65536. change (2^(8+8+8)) with 16777216.
  set (v := s + 256 * (bv_unsigned b + 256 * h)).
  replace (Z_to_bv 8 v) with (Z_to_bv 8 s) by (apply zb8_eq; subst v; Z.div_mod_to_equations; nia).
  replace (Z_to_bv 8 (v / 256)) with b.
  2:{ rewrite <- (stdpp.bitvector.definitions.Z_to_bv_bv_unsigned 8 b) at 1. apply zb8_eq. subst v. Z.div_mod_to_equations. nia. }
  replace (Z_to_bv 8 (v / 65536)) with (Z_to_bv 8 h) by (apply zb8_eq; subst v; Z.div_mod_to_equations; nia).
  replace (Z_to_bv 8 (v / 16777216)) with (Z_to_bv 8 (h / 256)) by (apply zb8_eq; subst v; Z.div_mod_to_equations; nia).
  reflexivity.
Qed.

Lemma hdr_word_join : forall m p s (b : byte) h, 0 <= s < 256 -> 0 <= h < 65536 ->
  rw_cells bsegs m p [C1 (zb s); C1 b; C2 (wz h)] -> rw_cells bsegs m p [C4 (wz (s + 256 * (bv_unsigned b + 256 * h)))].
Proof.
  intros m p s b h Hs Hh H. eapply rw_cells_rebytes; [cbn; tauto| apply hdr_word_bytes; assumption| reflexivity| exact H].
Qed.
Lemma hdr_word_split : forall m p s (b : byte) h, 0 <= s < 256 -> 0 <= h < 65536 ->
  rw_cells bsegs m p [C4 (wz (s + 256 * (bv_unsigned b + 256 * h)))] -> rw_cells bsegs m p [C1 (zb s); C1 b; C2 (wz h)].
Proof.
  intros m p s b h Hs Hh H. eapply rw_cells_rebytes; [cbn; tauto| symmetry; apply hdr_word_bytes; assumption| reflexivity| exact H].
Qed.

(* [comment removed for export] *)
Lemma land_hi_lo : forall q k, 0 <= q -> 0 <= k < 256 -> Z.land (256 * q) k = 0.
Proof.
  intros q k Hq Hk. apply Z.bits_inj_0. intros i.
  destruct (Z.lt_ge_cases i 0) as [Hi|Hi]; [apply Z.testbit_neg_r; lia|].
  rewrite Z.land_spec. destruct (Z.lt_ge_cases i 8) as [H8|H8].
  - replace (256 * q) with (q * 2^8) by lia. rewrite Z.mul_pow2_bits_low by lia. reflexivity.
  - rewrite (testbit_high_false k 8 i) by lia. apply andb_false_r.
Qed.
Lemma cas_word : forall q, 0 <= q ->
  Z.land (2 + 256 * q) 255 = 2 /\ Z.lxor (2 + 256 * q) (Z.land (Z.lxor (2 + 256 * q) 3) 255) = 3 + 256 * q.
Proof.
  intros q Hq.
  assert (M : forall k, 0 <= k < 256 -> Z.land (256 * q + k) 255 = k).
  { intros k Hk. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. change (2^8) with 256. Z.div_mod_to_equations. nia. }
  assert (X : forall k, 0 <= k < 256 -> 256 * q + k = Z.lxor (256 * q) k).
  { intros k Hk. rewrite <- Z.add_nocarry_lxor by (apply land_hi_lo; lia). reflexivity. }
  replace (2 + 256 * q) with (256 * q + 2) by lia. replace (3 + 256 * q) with (256 * q + 3) by lia.
  split; [apply M; lia|].
  rewrite (X 2) at 2 by lia. rewrite Z.lxor_assoc. change (Z.lxor 2 3) with 1. rewrite <- (X 1) by lia. rewrite M by lia.
  rewrite (X 2) by lia. rewrite Z.lxor_assoc. change (Z.lxor 2 1) with 3. rewrite <- (X 3) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma hdr_b1_type : forall b, Z.land b 127 = 17 -> Z.land b 3 = 1.
Proof. intros b H. transitivity (Z.land (Z.land b 127) 3); [rewrite <- Z.land_assoc; reflexivity| rewrite H; reflexivity]. Qed.

(* [comment removed for export] *)
Lemma land_align4' : forall x, 0 <= x < 2^64 -> x mod 4 = 0 -> Z.land x 18446744073709551612 = x.
Proof.
  intros x Hx Ha.
  replace 18446744073709551612 with (Z.lxor (Z.ones 64) (Z.ones 2)) by reflexivity.
  transitivity (Z.shiftl (Z.shiftr x 2) 2).
  2:{ rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. Z.div_mod_to_equations. lia. }
  apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, Z.lxor_spec, Z.shiftl_spec by lia.
  destruct (Z.lt_ge_cases i 2) as [Hi3|Hi3].
  - rewrite (Z.testbit_neg_r (Z.shiftr x 2)) by lia. rewrite !Z.ones_spec_low by lia. cbn. apply andb_false_r.
  - rewrite Z.shiftr_spec by lia. replace (i - 2 + 2) with i by lia. rewrite (Z.ones_spec_high 2 i) by lia.
    destruct (Z.lt_ge_cases i 64) as [Hi64|Hi64].
    + rewrite Z.ones_spec_low by lia. cbn. apply andb_true_r.
    + rewrite Z.ones_spec_high by lia. cbn.
      replace (Z.testbit x i) with false; [reflexivity|]. symmetry.
      destruct (Z.eq_dec x 0) as [->|Hx0]; [apply Z.bits_0|].
      apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 64; [apply Z.log2_lt_pow2; lia| lia].
Qed.

(* [comment removed for export] *)
Lemma size_hilo : forall n, 0 <= n < 2^40 -> 0 <= size_hi n < 256 /\ 0 <= size_lo n < 2^32 /\ size_hi n * 2^32 + size_lo n = usz n.
Proof.
  intros n Hn. unfold size_hi, size_lo, usz. split; [| split]; Z.div_mod_to_equations; lia.
Qed.

(* [comment removed for export] *)
Lemma zx16_lit : forall z, 0 <= z < 2^16 -> zx16 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof. intros z Hz. unfold zx16. rewrite (unsigned_lit z) by lia. rewrite Z.mod_small by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma sxb_zb_small' : forall v, 0 <= v < 128 -> sxb (zb v) = Z_to_bv 64 v.
Proof.
  intros v Hv. unfold sxb, zb. f_equal. rewrite Z_to_bv_signed. apply bv_swrap_small.
  unfold bv_half_modulus, bv_modulus. cbn. lia.
Qed.

(* [comment removed for export] *)
Lemma land_shl32 : forall h l, 0 <= h -> 0 <= l < 2^32 -> Z.land (h * 2^32) l = 0.
Proof.
  intros h l Hh Hl. apply Z.bits_inj_0. intros i.
  destruct (Z.lt_ge_cases i 0) as [Hi|Hi]; [apply Z.testbit_neg_r; lia|].
  rewrite Z.land_spec. destruct (Z.lt_ge_cases i 32) as [H8|H8].
  - rewrite Z.mul_pow2_bits_low by lia. reflexivity.
  - rewrite (testbit_high_false l 32 i) by lia. apply andb_false_r.
Qed.
Lemma size_join : forall n, 0 <= n < 2^40 -> Z.lor ((Z.shiftl (size_hi n) 32) mod 2^64) (size_lo n) = usz n.
Proof.
  intros n Hn. pose proof (size_hilo n Hn) as (H1 & H2 & H3). rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.mod_small by lia.
  rewrite <- Z.lxor_lor by (apply land_shl32; lia). rewrite <- Z.add_nocarry_lxor by (apply land_shl32; lia). lia.
Qed.


End CeilWrap.
