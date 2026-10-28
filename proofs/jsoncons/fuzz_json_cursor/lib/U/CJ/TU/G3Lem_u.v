(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib Require Import Tac ZBridge FP Image.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.TU Require Import G3Pure_u.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition M2 : Z := 18446744065119617025.
Lemma prod32b : forall a b, 0 <= a < 2 ^ 32 -> 0 <= b < 2 ^ 32 -> 0 <= a * b <= 18446744065119617025.
Proof. intros a b Ha Hb. split; [apply Z.mul_nonneg_nonneg; lia|]. change 18446744065119617025 with ((2 ^ 32 - 1) * (2 ^ 32 - 1)). apply Z.mul_le_mono_nonneg; lia. Qed.
Lemma shr32_range : forall x, 0 <= x <= 18446744065119617025 -> 0 <= Z.shiftr x 32 < 4294967295.
Proof. intros x Hx. rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. Qed.
Lemma mult_code_shr : forall xh xl ch cl, 0 <= xh < 2 ^ 32 -> 0 <= xl < 2 ^ 32 -> 0 <= ch < 2 ^ 32 -> 0 <= cl < 2 ^ 32 ->
  ch * xh + Z.shiftr (cl * xh) 32 + Z.shiftr (ch * xl) 32 + Z.shiftr ((cl * xh) mod 2 ^ 32 + Z.shiftr (cl * xl) 32 + (ch * xl) mod 2 ^ 32 + 2 ^ 31) 32
  = MULT (xh * 2 ^ 32 + xl) (ch * 2 ^ 32 + cl).
Proof.
  intros xh xl ch cl Hxh Hxl Hch Hcl. rewrite <- mult_code by assumption.
  assert (0 <= cl * xl) by (apply Z.mul_nonneg_nonneg; lia). assert (0 <= cl * xh) by (apply Z.mul_nonneg_nonneg; lia). assert (0 <= ch * xl) by (apply Z.mul_nonneg_nonneg; lia).
  rewrite !Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma wr_at_app : forall m a n1 n2, 0 <= n1 -> 0 <= n2 ->
  wr_at rsegs m a (n1 + n2) <-> wr_at rsegs m a n1 /\ wr_at rsegs m (a + n1) n2.
Proof.
  intros m a n1 n2 H1 H2. unfold wr_at. split.
  - intros (Ha & Hl & H). split; [split; [lia | split; [lia | intros i Hi; apply H; lia]] |].
    split; [lia | split; [lia | intros i Hi; replace (a + n1 + i) with (a + (n1 + i)) by lia; apply H; lia]].
  - intros ((Ha & Hl1 & Ha1) & (Hb & Hl2 & Hb2)). split; [lia | split; [lia |]].
    intros i Hi. destruct (Z.lt_ge_cases i n1); [apply Ha1; lia |].
    replace (a + i) with (a + n1 + (i - n1)) by lia. apply Hb2. lia.
Qed.
Lemma u8arr_app : forall m A bs1 bs2,
  u8arr rsegs m A (bs1 ++ bs2) <-> u8arr rsegs m A bs1 /\ u8arr rsegs m (A + Z.of_nat (length bs1)) bs2.
Proof.
  intros m A bs1 bs2. unfold u8arr. rewrite bytes_at_app, length_app, Nat2Z.inj_add, wr_at_app by lia. tauto.
Qed.
Lemma rw_cells_app : forall m A cs1 cs2,
  rw_cells rsegs m A (cs1 ++ cs2) <-> rw_cells rsegs m A cs1 /\ rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2. unfold rw_cells, cells_at. rewrite cells_wf_app, cells_bytes_app, cells_size_app, Nat2Z.inj_add, wr_at_app by lia.
  split.
  - intros (((W1 & W2) & B) & Wa & Wb). apply bytes_at_app in B as (B1 & B2). rewrite cells_bytes_length in B2 by assumption. tauto.
  - intros (((W1 & B1) & Wa) & ((W2 & B2) & Wb)). split; [split; [tauto|] | tauto].
    apply bytes_at_app. rewrite cells_bytes_length by assumption. tauto.
Qed.
Lemma zbv_signed : forall w : word, Z_to_bv 64 (bv_signed w) = w.
Proof. intros w. rewrite <- Z_to_bv_mod64, <- u_of_signed. apply Z_to_bv_bv_unsigned. Qed.

Definition mcode (ac ad bc bd : Z) : Z :=
  Z.shiftr ad 32 + (ac + Z.shiftr bc 32) + Z.shiftr (ad mod 4294967296 + (Z.shiftr bd 32 + bc mod 4294967296) + 2147483648) 32.
Lemma mcode_mult : forall xh xl ch cl, 0 <= xh < 2 ^ 32 -> 0 <= xl < 2 ^ 32 -> 0 <= ch < 2 ^ 32 -> 0 <= cl < 2 ^ 32 ->
  mcode (ch * xh) (cl * xh) (ch * xl) (cl * xl) = MULT (xh * 2 ^ 32 + xl) (ch * 2 ^ 32 + cl).
Proof.
  intros xh xl ch cl Hxh Hxl Hch Hcl. rewrite <- mult_code_shr by assumption. unfold mcode.
  change 4294967296 with (2 ^ 32). change 2147483648 with (2 ^ 31).
  rewrite (Z.add_assoc ((cl * xh) mod 2 ^ 32) (Z.shiftr (cl * xl) 32)). ring.
Qed.

Lemma ezext : forall s k, 56 <= s <= 59 -> ((- s - k + k) mod 18446744073709551616) mod 4294967296 = 2 ^ 32 - s.
Proof.
  intros s k Hs. replace (- s - k + k) with (- s) by lia.
  rewrite <- (Z.mod_unique (- s) 18446744073709551616 (-1) (18446744073709551616 - s)) by lia.
  symmetry. apply (Z.mod_unique _ _ 4294967295); lia.
Qed.

Lemma mulhu_lo32 : forall c x, 0 <= c -> 0 <= x ->
  Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl c 32)) * bv_unsigned (Z_to_bv 64 (Z.shiftl x 32))) 64 = (c mod 4294967296) * (x mod 4294967296).
Proof.
  intros c x Hc Hx. rewrite !unsigned_lit_wrap, !Z.shiftl_mul_pow2 by lia.
  replace (2 ^ 64) with (2 ^ 32 * 2 ^ 32) by reflexivity. rewrite !Z.mul_mod_distr_r by lia.
  rewrite Z.shiftr_div_pow2 by lia. change 4294967296 with (2 ^ 32).
  replace (c mod 2 ^ 32 * 2 ^ 32 * (x mod 2 ^ 32 * 2 ^ 32)) with ((c mod 2 ^ 32 * (x mod 2 ^ 32)) * 2 ^ 64) by ring.
  apply Z.div_mul. lia.
Qed.
Lemma split32 : forall x, 0 <= x -> Z.shiftr x 32 * 2 ^ 32 + x mod 4294967296 = x.
Proof. intros x Hx. rewrite Z.shiftr_div_pow2 by lia. change 4294967296 with (2 ^ 32). pose proof (Z.div_mod x (2 ^ 32)). lia. Qed.

Lemma exp_bits : forall b, 0 <= b < 2 ^ 63 -> Z.shiftr ((Z.shiftl b 1) mod 18446744073709551616) 53 = Z.shiftr b 52.
Proof.
  intros b Hb. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.mod_small by lia. rewrite !Z.shiftr_div_pow2 by lia.
  replace (2 ^ 53) with (2 ^ 1 * 2 ^ 52) by reflexivity. rewrite <- Z.div_div by lia. rewrite Z.div_mul by lia. reflexivity.
Qed.
Lemma mant_bits : forall b, Z.land b 4503599627370495 = b mod 2 ^ 52.
Proof. intros b. change 4503599627370495 with (2 ^ 52 - 1). apply zb_land_mask. lia. Qed.
Lemma lor_hidden : forall x, 0 <= x < 2 ^ 52 -> Z.lor x 4503599627370496 = x + 2 ^ 52.
Proof.
  intros x Hx. change 4503599627370496 with (2 ^ 52). rewrite <- Z.lxor_lor by (apply zb_land_pow2_small; lia).
  apply zb_lxor_pow2_small; lia.
Qed.
Lemma land_bit : forall x k, 0 <= k -> 0 <= x < 2 ^ (k + 1) -> (Z.land x (2 ^ k) = 0 <-> x < 2 ^ k).
Proof.
  intros x k Hk Hx. split.
  - intros H. destruct (Z_lt_le_dec x (2 ^ k)) as [L|L]; [exact L | exfalso].
    assert (T : Z.testbit x k = true).
    { apply Z.testbit_true; [lia|]. rewrite Z.pow_add_r in Hx by lia.
      replace (x / 2 ^ k) with 1; [reflexivity|]. apply Z.div_unique with (x - 2 ^ k); lia. }
    assert (T2 : Z.testbit (Z.land x (2 ^ k)) k = true) by (rewrite Z.land_spec, T, Z.pow2_bits_true by lia; reflexivity).
    rewrite H, Z.bits_0 in T2. discriminate.
  - intros H. apply zb_land_pow2_small; lia.
Qed.

Lemma nrm_unique : forall m ka kb, 1 <= m -> 0 <= ka -> 0 <= kb -> 2 ^ 53 <= (2 * m + 1) * 2 ^ ka < 2 ^ 54 -> 2 ^ 52 <= m * 2 ^ kb < 2 ^ 53 -> ka = kb.
Proof.
  intros m ka kb Hm Ha Hb [A1 A2] [B1 B2].
  assert (P0 : 0 < 2 ^ kb) by (apply Z.pow_pos_nonneg; lia). assert (P0a : 0 < 2 ^ ka) by (apply Z.pow_pos_nonneg; lia).
  assert (Hkb : kb < 53).
  { destruct (Z_lt_le_dec kb 53) as [?|L]; [lia|]. assert (2 ^ 53 <= 2 ^ kb) by (apply Z.pow_le_mono_r; lia). nia. }
  assert (Pm : 2 ^ 53 = 2 ^ (53 - kb) * 2 ^ kb) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  assert (Mlt : m < 2 ^ (53 - kb)) by nia.
  assert (C1 : (2 * m + 1) * 2 ^ kb < 2 ^ 54) by (replace (2 ^ 54) with (2 * 2 ^ 53) by reflexivity; nia).
  assert (C2 : 2 ^ 53 <= (2 * m + 1) * 2 ^ kb) by nia.
  destruct (Z.lt_trichotomy ka kb) as [H|[H|H]]; [exfalso | exact H | exfalso].
  - assert (E : 2 ^ (ka + 1) <= 2 ^ kb) by (apply Z.pow_le_mono_r; lia). rewrite Z.pow_add_r in E by lia.
    replace (2 ^ 54) with (2 * 2 ^ 53) in C1 by reflexivity. nia.
  - assert (E : 2 ^ (kb + 1) <= 2 ^ ka) by (apply Z.pow_le_mono_r; lia). rewrite Z.pow_add_r in E by lia.
    replace (2 ^ 54) with (2 * 2 ^ 53) in A2 by reflexivity. nia.
Qed.
