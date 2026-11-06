(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatSim SeqExec StoreOk ArtMem EatUnwind EatCellJoin.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Lemma art_b1_small : forall b1 n, 0 <= b1 < 2 ^ 24 -> b1 / 256 = n / 2 ^ 32 -> 0 <= n < 2 ^ 32 -> 0 <= b1 < 256.
Proof. intros b1 n Hb E Hn. rewrite (Z.div_small n) in E by lia. lia. Qed.

Lemma art_b1_hi0 : forall b1 n, 0 <= b1 < 256 -> 0 <= n < 2 ^ 32 -> b1 / 256 = n / 2 ^ 32.
Proof. intros b1 n Hb Hn. rewrite !Z.div_small by lia. reflexivity. Qed.

Lemma art_b1_bound : forall b1 n, 0 <= b1 -> b1 / 256 = n / 2 ^ 32 -> 0 <= n < 2 ^ 40 -> 0 <= b1 < 2 ^ 16.
Proof.
  intros b1 n Hb E Hn. assert (n / 2 ^ 32 < 2 ^ 8) by (apply Z.div_lt_upper_bound; lia). change (2 ^ 8) with 256 in H. lia.
Qed.

Lemma art_hdrw_mod256 : forall st b1, 0 <= st < 256 -> 0 <= b1 -> (st + 256 * b1) mod 256 = st.
Proof. intros st b1 Hst Hb. replace (st + 256 * b1) with (st + b1 * 256) by lia. rewrite Z_mod_plus_full. apply Z.mod_small. lia. Qed.

Lemma art_hdrw_b1 : forall st b1, 0 <= st < 256 -> 0 <= b1 -> (st + 256 * b1) / 256 = b1.
Proof. intros st b1 Hst Hb. replace (st + 256 * b1) with (st + b1 * 256) by lia. rewrite Z_div_plus_full, (Z.div_small st) by lia. lia. Qed.

Lemma art_hdrw_tb : forall st b1, 0 <= st < 256 -> 0 <= b1 -> (st + 256 * b1) / 256 mod 256 = b1 mod 256.
Proof. intros st b1 Hst Hb. rewrite art_hdrw_b1 by lia. reflexivity. Qed.

Lemma art_hdrw_hi : forall st b1, 0 <= st < 256 -> 0 <= b1 -> (st + 256 * b1) / 65536 = b1 / 256.
Proof.
  intros st b1 Hst Hb. change 65536 with (256 * 256). rewrite <- Z.div_div by lia. rewrite art_hdrw_b1 by lia. reflexivity.
Qed.

Lemma art_b1_mod256_mod4 : forall b1, 0 <= b1 -> (b1 mod 256) mod 4 = b1 mod 4.
Proof.
  intros b1 Hb. rewrite (Z.div_mod b1 256) at 2 by lia. replace (256 * (b1 / 256) + b1 mod 256) with (b1 mod 256 + (64 * (b1 / 256)) * 4) by lia.
  rewrite Z_mod_plus_full. reflexivity.
Qed.

Lemma art_land3_mod256 : forall b1, 0 <= b1 -> Z.land (b1 mod 256) 3 = b1 mod 4.
Proof.
  intros b1 Hb. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. change (2 ^ 2) with 4. apply art_b1_mod256_mod4. exact Hb.
Qed.

Lemma art_land3 : forall b1, 0 <= b1 -> Z.land b1 3 = b1 mod 4.
Proof. intros b1 Hb. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma art_lor_disjoint32 : forall hi lo, 0 <= hi -> 0 <= lo < 2 ^ 32 -> Z.lor (hi * 2 ^ 32) lo = hi * 2 ^ 32 + lo.
Proof.
  intros hi lo Hhi Hlo.
  assert (Hand : Z.land (hi * 2 ^ 32) lo = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 32) as [L|G].
    - rewrite <- Z.shiftl_mul_pow2 by lia. rewrite Z.shiftl_spec_low by lia. reflexivity.
    - assert (T : Z.testbit lo i = false).
      { destruct (Z.eq_dec lo 0) as [->|NZ]; [apply Z.testbit_0_l|]. apply Z.bits_above_log2; [lia|].
        apply Z.lt_le_trans with (m := 32); [apply Z.log2_lt_pow2; lia|lia]. }
      rewrite T. apply Bool.andb_false_r. }
  pose proof (Z.add_lor_land (hi * 2 ^ 32) lo) as E. rewrite Hand in E. lia.
Qed.

Lemma art_or_hilo : forall n, 0 <= n -> Z.lor (n / 2 ^ 32 * 2 ^ 32) (n mod 2 ^ 32) = n.
Proof.
  intros n Hn. rewrite art_lor_disjoint32; [|apply Z.div_pos; lia|apply Z.mod_pos_bound; lia].
  pose proof (Z.div_mod n (2 ^ 32) ltac:(lia)). lia.
Qed.

Lemma art_or_lohi : forall n, 0 <= n -> Z.lor (n mod 2 ^ 32) (n / 2 ^ 32 * 2 ^ 32) = n.
Proof. intros n Hn. rewrite Z.lor_comm. apply art_or_hilo. exact Hn. Qed.

Lemma art_or_b1lo : forall b1 n, 0 <= b1 -> 0 <= n -> b1 / 256 = n / 2 ^ 32 -> Z.lor (b1 / 256 * 2 ^ 32) (n mod 2 ^ 32) = n.
Proof. intros b1 n Hb Hn ->. apply art_or_hilo. exact Hn. Qed.

Lemma art_hilo_sum : forall n, 0 <= n -> n / 2 ^ 32 * 2 ^ 32 + n mod 2 ^ 32 = n.
Proof. intros n Hn. pose proof (Z.div_mod n (2 ^ 32) ltac:(lia)). lia. Qed.

Lemma art_hi_bound : forall n k, 0 <= n < 2 ^ (32 + k) -> 0 <= k -> 0 <= n / 2 ^ 32 < 2 ^ k.
Proof.
  intros n k Hn Hk. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. rewrite <- Z.pow_add_r by lia. replace (32 + k) with (32 + k) by lia. lia.
Qed.

Lemma word_to_le_bytes4_mod : forall v, word_to_le_bytes 4 (Z_to_bv 64 v) = word_to_le_bytes 4 (Z_to_bv 64 (v mod 2 ^ 32)).
Proof.
  intros v. unfold word_to_le_bytes. rewrite !Z_to_bv_unsigned.
  rewrite <- (Z_to_le_bytes_wrap 4 (N.of_nat (8 * 4)) (bv_wrap 64 v)) by lia.
  rewrite <- (Z_to_le_bytes_wrap 4 (N.of_nat (8 * 4)) (bv_wrap 64 (v mod 2 ^ 32))) by lia. f_equal.
  unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). change (bv_modulus (N.of_nat (8 * 4))) with (2 ^ 32).
  pose proof (Z.mod_pos_bound v (2 ^ 32) ltac:(lia)) as B.
  rewrite (Z.mod_small (v mod 2 ^ 32) (2 ^ 64)) by lia. rewrite Z.mod_mod by lia.
  rewrite Z.mod_mod_divide; [reflexivity|]. exists (2 ^ 32). reflexivity.
Qed.

Lemma cell4_mod : forall (M : word -> option byte) a v, cellA M a 4 v -> cellA M a 4 (v mod 2 ^ 32).
Proof. intros M a v C. unfold cell in *. rewrite <- word_to_le_bytes4_mod. exact C. Qed.

Lemma cell4_of_mod : forall (M : word -> option byte) a v, cellA M a 4 (v mod 2 ^ 32) -> cellA M a 4 v.
Proof. intros M a v C. unfold cell in *. rewrite word_to_le_bytes4_mod. exact C. Qed.

Lemma Wn4_mod : forall (M : word -> option byte) a v, Wn 4 M a v = Wn 4 M a (v mod 2 ^ 32).
Proof. intros M a v. unfold Wn. rewrite word_to_le_bytes4_mod. reflexivity. Qed.

Lemma art_hdr_word_w : forall (M : word -> option byte) h st tb hi, 0 <= h -> h + 4 < 2 ^ 64 -> 0 <= st < 256 -> 0 <= tb < 256 -> 0 <= hi < 2 ^ 16 ->
  cellA M h 1 st -> cellA M (h + 1) 1 tb -> cellA M (h + 2) 2 hi -> cellA M h 4 (st + 256 * (tb + 256 * hi)).
Proof.
  intros M h st tb hi Hh Hh' Hst Htb Hhi C0 C1 C2.
  assert (C12 : cellA M (h + 1) 3 (tb + hi * 2 ^ (8 * Z.of_nat 1))).
  { apply (art_cell_join M (h + 1) 1 2 tb hi); [lia|cbn; lia|lia|cbn; lia|cbn; lia|exact C1|]. replace (h + 1 + Z.of_nat 1) with (h + 2) by lia. exact C2. }
  replace (st + 256 * (tb + 256 * hi)) with (st + (tb + hi * 2 ^ (8 * Z.of_nat 1)) * 2 ^ (8 * Z.of_nat 1)) by (cbn; lia).
  apply (art_cell_join M h 1 3 st (tb + hi * 2 ^ (8 * Z.of_nat 1))); [lia|cbn; lia|lia|cbn; lia|cbn; lia|exact C0|].
  replace (h + Z.of_nat 1) with (h + 1) by lia. exact C12.
Qed.

Lemma art_b1w_facts : forall tb n, 0 <= tb < 256 -> tb mod 4 = 1 -> 0 <= n < 2 ^ 40 ->
  let b1 := tb + 256 * (n / 2 ^ 32) in 0 <= b1 < 2 ^ 24 /\ b1 mod 4 = 1 /\ b1 / 256 = n / 2 ^ 32 /\ b1 mod 256 = tb.
Proof.
  intros tb n Htb Htb4 Hn b1. pose proof (art_hi_bound n 8 ltac:(change (32 + 8) with 40; lia) ltac:(lia)) as Hhi. change (2 ^ 8) with 256 in Hhi.
  subst b1. split; [lia|]. split; [|split]; lia.
Qed.

Lemma art_masked_byte0 : forall w d, 0 <= w -> 0 <= d < 256 -> Z.lxor w (Z.land (Z.lxor w d) 255) = w / 256 * 256 + d.
Proof.
  intros w d Hw Hd.
  assert (Hdb : forall i, 8 <= i -> Z.testbit d i = false).
  { intros i Hi. destruct (Z.eq_dec d 0) as [->|NZ]; [apply Z.testbit_0_l|]. apply Z.bits_above_log2; [lia|].
    apply Z.lt_le_trans with (m := 8); [apply Z.log2_lt_pow2; lia|lia]. }
  assert (E : w / 256 * 256 + d = Z.lxor (Z.shiftl (w / 256) 8) d).
  { rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256. apply Z.add_nocarry_lxor.
    apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 8) as [L|G].
    - change 256 with (2 ^ 8). rewrite <- Z.shiftl_mul_pow2 by lia. rewrite Z.shiftl_spec_low by lia. reflexivity.
    - rewrite (Hdb i G). apply Bool.andb_false_r. }
  rewrite E. apply Z.bits_inj'. intros i Hi.
  rewrite !Z.lxor_spec, Z.land_spec, Z.lxor_spec.
  destruct (Z.lt_ge_cases i 8) as [L|G].
  - rewrite Z.shiftl_spec_low by lia. change 255 with (Z.ones 8). rewrite Z.testbit_ones_nonneg by lia.
    replace (i <? 8) with true by (symmetry; apply Z.ltb_lt; exact L). rewrite Bool.andb_true_r.
    destruct (Z.testbit w i), (Z.testbit d i); reflexivity.
  - rewrite Z.shiftl_spec_high by lia. change 256 with (2 ^ 8). rewrite Z.div_pow2_bits by lia.
    replace (i - 8 + 8) with i by lia.
    change 255 with (Z.ones 8). rewrite Z.testbit_ones_nonneg by lia.
    replace (i <? 8) with false by (symmetry; apply Z.ltb_ge; exact G). rewrite Bool.andb_false_r, (Hdb i G).
    destruct (Z.testbit w i); reflexivity.
Qed.

Lemma art_lxor_lt_pow2 : forall a b n, 0 <= a < 2 ^ n -> 0 <= b < 2 ^ n -> 0 < n -> 0 <= Z.lxor a b < 2 ^ n.
Proof.
  intros a b n Ha Hb Hn. split; [apply Z.lxor_nonneg; lia|].
  destruct (Z.eq_dec (Z.lxor a b) 0) as [->|NZ]; [lia|].
  assert (Hl : Z.log2 (Z.lxor a b) < n).
  { pose proof (Z.log2_lxor a b ltac:(lia) ltac:(lia)) as HX. eapply Z.le_lt_trans; [exact HX|]. apply Z.max_lub_lt.
    - destruct (Z.eq_dec a 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia.
    - destruct (Z.eq_dec b 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia. }
  apply Z.log2_lt_pow2 in Hl; [exact Hl|]. pose proof (Z.lxor_nonneg a b). lia.
Qed.

Lemma art_casw_xor : forall st st' b1, 0 <= st < 256 -> 0 <= st' < 256 -> 0 <= b1 < 2 ^ 50 ->
  v_xor (Z_to_bv 64 (st + 256 * b1)) (v_and (v_xor (Z_to_bv 64 (st + 256 * b1)) (Z_to_bv 64 st')) (Z_to_bv 64 255)) = Z_to_bv 64 (st' + 256 * b1).
Proof.
  intros st st' b1 Hst Hst' Hb.
  pose proof (art_lxor_lt_pow2 (st + 256 * b1) st' 64 ltac:(lia) ltac:(lia) ltac:(lia)) as R1.
  assert (R2 : 0 <= Z.land (Z.lxor (st + 256 * b1) st') 255 < 2 ^ 64).
  { change 255 with (Z.ones 8). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound (Z.lxor (st + 256 * b1) st') (2 ^ 8) ltac:(lia)). lia. }
  unfold v_xor, v_and. rewrite (art_u_lit (st + 256 * b1)), (art_u_lit st') by lia. rewrite (art_u_lit (Z.lxor _ _)) by lia.
  rewrite (art_u_lit 255) by lia. rewrite (art_u_lit (Z.land _ _)) by lia.
  rewrite art_masked_byte0 by lia. rewrite art_hdrw_b1 by lia. f_equal. lia.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
