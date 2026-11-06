(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MemSplit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma art_u_lit : forall a, 0 <= a < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 a) = a.
Proof. intros a H. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2^64). lia. Qed.

Lemma art_zb_eq : forall x y, x mod 2 ^ 64 = y mod 2 ^ 64 -> Z_to_bv 64 x = Z_to_bv 64 y.
Proof. intros x y H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64). exact H. Qed.

Lemma art_zb_addi : forall x k, v_addi (Z_to_bv 64 x) k = Z_to_bv 64 (x + k).
Proof.
  intros x k. unfold v_addi. rewrite Z_to_bv_unsigned. apply art_zb_eq. unfold bv_wrap. change (bv_modulus 64) with (2^64).
  rewrite Zplus_mod_idemp_l. reflexivity.
Qed.
Lemma art_zb_add : forall x y, v_add (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x + y).
Proof.
  intros x y. unfold v_add. rewrite !Z_to_bv_unsigned. apply art_zb_eq. unfold bv_wrap. change (bv_modulus 64) with (2^64).
  rewrite <- Zplus_mod. reflexivity.
Qed.
Lemma art_zb_sub : forall x y, v_sub (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x - y).
Proof.
  intros x y. unfold v_sub. rewrite !Z_to_bv_unsigned. apply art_zb_eq. unfold bv_wrap. change (bv_modulus 64) with (2^64).
  rewrite <- Zminus_mod. reflexivity.
Qed.
Lemma art_zb_mul : forall x y, v_mul (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x * y).
Proof.
  intros x y. unfold v_mul. rewrite !Z_to_bv_unsigned. apply art_zb_eq. unfold bv_wrap. change (bv_modulus 64) with (2^64).
  rewrite <- Zmult_mod. reflexivity.
Qed.
Lemma art_zb_slli : forall x k, 0 <= k -> v_slli (Z_to_bv 64 x) k = Z_to_bv 64 (x * 2 ^ k).
Proof.
  intros x k Hk. unfold v_slli. rewrite Z_to_bv_unsigned, Z.shiftl_mul_pow2 by lia. apply art_zb_eq. unfold bv_wrap.
  change (bv_modulus 64) with (2^64). rewrite Zmult_mod_idemp_l. reflexivity.
Qed.
Lemma art_zb_srli : forall x k, 0 <= x < 2 ^ 64 -> 0 <= k -> v_srli (Z_to_bv 64 x) k = Z_to_bv 64 (x / 2 ^ k).
Proof. intros x k Hx Hk. unfold v_srli. rewrite art_u_lit by lia. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.
Lemma art_zb_srli_exact : forall x k y, 0 <= k -> 0 <= y -> x = y * 2 ^ k -> y < 2 ^ 64 -> y * 2 ^ k < 2 ^ 64 ->
  v_srli (Z_to_bv 64 x) k = Z_to_bv 64 y.
Proof.
  intros x k y Hk Hy Hx Hy' Hyk. subst x. rewrite art_zb_srli by lia. f_equal. apply Z.div_mul. pose proof (Z.pow_pos_nonneg 2 k). lia.
Qed.
Lemma art_zb_and : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> v_and (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (Z.land x y).
Proof. intros x y Hx Hy. unfold v_and. rewrite !art_u_lit by lia. reflexivity. Qed.
Lemma art_zb_andi : forall x k, 0 <= x < 2 ^ 64 -> 0 <= k < 2 ^ 64 -> v_andi (Z_to_bv 64 x) k = Z_to_bv 64 (Z.land x k).
Proof. intros x k Hx Hk. unfold v_andi. rewrite art_u_lit by lia. rewrite bv_wrap_small by (change (bv_modulus 64) with (2^64); lia). reflexivity. Qed.

Lemma art_v_lw_small : forall z, 0 <= z < 2 ^ 31 -> v_lw (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold v_lw. rewrite art_u_lit by lia. f_equal. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32). rewrite Z.mod_small by lia. lia.
Qed.

Lemma art_v_lh_small : forall z, 0 <= z < 2 ^ 15 -> v_lh (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold v_lh. rewrite art_u_lit by lia. f_equal. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 16) with (2^15). change (bv_modulus 16) with (2^16). rewrite Z.mod_small by lia. lia.
Qed.
Lemma art_bytes2 : forall z, 0 <= z < 2 ^ 16 -> bytes_le_to_Z (word_to_le_bytes 2 (Z_to_bv 64 z)) = bv_unsigned (Z_to_bv 64 z).
Proof.
  intros z Hz. rewrite bytes_le_N. change (2 ^ (8 * Z.of_nat 2)) with (2^16). rewrite art_u_lit by lia. apply Z.mod_small. lia.
Qed.
Lemma art_land_m8 : forall x, 0 <= x < 2 ^ 64 -> Z.land x 18446744073709551608 = x / 8 * 8.
Proof.
  intros x Hx. change 18446744073709551608 with (Z.shiftl (Z.ones 61) 3).
  change 8 with (2 ^ 3). rewrite <- Z.shiftr_div_pow2, <- Z.shiftl_mul_pow2 by lia.
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
  destruct (Z.lt_ge_cases i 3) as [L|G].
  - rewrite !Z.shiftl_spec_low by lia. apply Bool.andb_false_r.
  - rewrite !Z.shiftl_spec_high by lia. rewrite Z.shiftr_spec by lia. rewrite Z.testbit_ones by lia.
    replace (i - 3 + 3) with i by lia.
    destruct (Z.lt_ge_cases i 64) as [L2|G2].
    + replace ((0 <=? i - 3) && (i - 3 <? 61))%bool with true by (symmetry; apply Bool.andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
      apply Bool.andb_true_r.
    + assert (Tf : Z.testbit x i = false).
      { destruct (Z.eq_dec x 0) as [->|NZ]. apply Z.testbit_0_l. apply Z.bits_above_log2; [lia|].
        apply Z.lt_le_trans with (m := 64); [|lia]. apply Z.log2_lt_pow2; lia. }
      rewrite Tf. reflexivity.
Qed.
Lemma art_v_lb_small : forall z, 0 <= z < 128 -> v_lb (Z_to_bv 8 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold v_lb. f_equal. rewrite Z_to_bv_signed. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 8) with 128. change (bv_modulus 8) with 256. rewrite Z.mod_small by lia. lia.
Qed.
Lemma art_bytes1 : forall z, 0 <= z < 2 ^ 64 -> word_to_le_bytes 1 (Z_to_bv 64 z) = [Z_to_bv 8 z].
Proof.
  intros z Hz. unfold word_to_le_bytes. cbn. f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 8) with 256. change (bv_modulus 64) with (2^64). rewrite (Z.mod_small z (2^64)) by lia. reflexivity.
Qed.
Lemma art_u8_lit : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256. lia. Qed.
Lemma art_bytes4 : forall z, 0 <= z < 2 ^ 32 -> bytes_le_to_Z (word_to_le_bytes 4 (Z_to_bv 64 z)) = bv_unsigned (Z_to_bv 64 z).
Proof.
  intros z Hz. rewrite bytes_le_N. change (2 ^ (8 * Z.of_nat 4)) with (2^32). rewrite art_u_lit by lia. apply Z.mod_small. lia.
Qed.

Lemma art_land_full_l : forall x, 0 <= x < 2 ^ 64 -> Z.land 18446744073709551615 x = x.
Proof. intros x Hx. rewrite Z.land_comm. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.
Lemma art_land_full_r : forall x, 0 <= x < 2 ^ 64 -> Z.land x 18446744073709551615 = x.
Proof. intros x Hx. rewrite Z.land_comm. apply art_land_full_l. exact Hx. Qed.

Lemma art_c_eq_zb : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> c_eq (Z_to_bv 64 x) (Z_to_bv 64 y) = Z.eqb x y.
Proof. intros x y Hx Hy. unfold c_eq, bv_eqb. rewrite !art_u_lit by lia. reflexivity. Qed.
Lemma art_c_ltu_zb : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> c_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = Z.ltb x y.
Proof. intros x y Hx Hy. unfold c_ltu, bv_ltu. rewrite !art_u_lit by lia. reflexivity. Qed.

Lemma art_zb_xori_m1 : forall x, 0 <= x < 2 ^ 64 -> v_xori (Z_to_bv 64 x) (-1) = Z_to_bv 64 (2 ^ 64 - 1 - x).
Proof.
  intros x Hx. unfold v_xori. rewrite art_u_lit by lia. change (bv_wrap 64 (-1)) with (Z.ones 64). f_equal.
  rewrite <- Z.ldiff_ones_l_low; [| lia |].
  - rewrite Z.ldiff_land. rewrite <- Z.sub_land_same_l. rewrite Z.land_comm, Z.land_ones, Z.mod_small by lia. rewrite Z.ones_equiv. lia.
  - destruct (Z.eq_dec x 0) as [->|Hz]; [cbn; lia|]. apply Z.log2_lt_pow2; lia.
Qed.
Lemma art_zb_sltiu : forall x k, 0 <= x < 2 ^ 64 -> 0 <= k < 2 ^ 64 ->
  v_sltiu (Z_to_bv 64 x) k = Z_to_bv 64 (if x <? k then 1 else 0).
Proof.
  intros x k Hx Hk. unfold v_sltiu. rewrite art_u_lit by lia. rewrite bv_wrap_small by (change (bv_modulus 64) with (2^64); lia).
  destruct (x <? k); reflexivity.
Qed.
Lemma art_zb_sltu : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  v_sltu (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (if x <? y then 1 else 0).
Proof. intros x y Hx Hy. unfold v_sltu. rewrite art_c_ltu_zb by lia. destruct (x <? y); reflexivity. Qed.

Section WithSegs.
Variable segs : list Segment.

Definition cell (M : word -> option byte) (a : Z) (n : nat) (v : Z) : Prop :=
  rdn segs M (Z_to_bv 64 a) n = Some (word_to_le_bytes n (Z_to_bv 64 v)).
Definition Wn (n : nat) (M : word -> option byte) (a : Z) (v : Z) : word -> option byte :=
  wbytes M (Z_to_bv 64 a) (word_to_le_bytes n (Z_to_bv 64 v)).
Definition wok (M : word -> option byte) (a : Z) (n : nat) : Prop := store_ok segs M (Z_to_bv 64 a) n = true.
Definition apart (a n b m : Z) : Prop := a + n <= b \/ b + m <= a.

Lemma apart_sym : forall a n b m, apart a n b m -> apart b m a n.
Proof. unfold apart. lia. Qed.

Lemma rdn_Wn_other : forall n M a v b m,
  0 <= a -> a + Z.of_nat n < 2 ^ 64 -> 0 <= b -> b + Z.of_nat m < 2 ^ 64 -> apart a (Z.of_nat n) b (Z.of_nat m) ->
  rdn segs (Wn n M a v) (Z_to_bv 64 b) m = rdn segs M (Z_to_bv 64 b) m.
Proof.
  intros n M a v b m Ha Han Hb Hbm Hap. unfold Wn.
  apply rdn_wbytes_out; rewrite ?length_N_to_le_bytes; rewrite ?(art_u_lit a) by lia; rewrite ?(art_u_lit b) by lia; unfold apart in Hap; lia.
Qed.

Lemma cell_Wn_other : forall n M a v b m u,
  0 <= a -> a + Z.of_nat n < 2 ^ 64 -> 0 <= b -> b + Z.of_nat m < 2 ^ 64 -> apart a (Z.of_nat n) b (Z.of_nat m) ->
  cell M b m u -> cell (Wn n M a v) b m u.
Proof. intros n M a v b m u Ha Han Hb Hbm Hap H. unfold cell. rewrite rdn_Wn_other by assumption. exact H. Qed.

Lemma cell_Wn_hit : forall n M a v, 0 <= a -> a + Z.of_nat n < 2 ^ 64 -> cell (Wn n M a v) a n v.
Proof.
  intros n M a v Ha Han. unfold cell, Wn.
  pose proof (rdn_wbytes_hit segs (word_to_le_bytes n (Z_to_bv 64 v)) M (Z_to_bv 64 a)) as H.
  rewrite length_N_to_le_bytes in H. apply H. rewrite art_u_lit by lia. lia.
Qed.

Lemma Wn_grows : forall n M a v, mem_grows M (Wn n M a v).
Proof. intros. unfold Wn. apply wbytes_grows. Qed.

Lemma wok_Wn : forall n M a v b m, wok M b m -> wok (Wn n M a v) b m.
Proof. intros n M a v b m H. unfold wok. eapply store_ok_mono; [apply Wn_grows | exact H]. Qed.

Lemma wok_grows : forall M M' b m, mem_grows M M' -> wok M b m -> wok M' b m.
Proof. intros M M' b m G H. unfold wok. eapply store_ok_mono; [exact G | exact H]. Qed.

Definition wr (M : word -> option byte) (a n : Z) : Prop :=
  forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok segs M (Z_to_bv 64 (a + d)) k = true.
Lemma wr_wok : forall M a n, wr M a n -> forall b k, a <= b -> b + Z.of_nat k <= a + n -> wok M b k.
Proof. intros M a n W b k H1 H2. unfold wok. replace b with (a + (b - a)) by lia. apply W; lia. Qed.
Lemma wr_grows : forall M M' a n, mem_grows M M' -> wr M a n -> wr M' a n.
Proof. intros M M' a n G W d k Hd Hk. eapply store_ok_mono; [exact G | apply W; assumption]. Qed.
Lemma wr_Wn : forall n M a v b m, wr M b m -> wr (Wn n M a v) b m.
Proof. intros. eapply wr_grows; [apply Wn_grows | assumption]. Qed.
Lemma wr_sub : forall M a n a' n', wr M a n -> a <= a' -> a' + n' <= a + n -> wr M a' n'.
Proof. intros M a n a' n' W H1 H2 d k Hd Hk. replace (a' + d) with (a + (a' - a + d)) by lia. apply W; lia. Qed.

Lemma Wn_outside : forall n M a v (x : word),
  0 <= a -> a + Z.of_nat n < 2 ^ 64 ->
  ~ (a <= bv_unsigned x < a + Z.of_nat n) -> Wn n M a v x = M x.
Proof.
  intros n M a v x Ha Han Hx. unfold Wn.
  destruct (Z_lt_le_dec (bv_unsigned x) a) as [L|G].
  - apply wbytes_below; rewrite ?length_N_to_le_bytes, art_u_lit by lia; lia.
  - apply wbytes_above. rewrite length_N_to_le_bytes, art_u_lit by lia. lia.
Qed.

Definition Wf (M : word -> option byte) (a : Z) (k : nat) (b : Z) : word -> option byte :=
  wbytes M (Z_to_bv 64 a) (repeat (Z_to_bv 8 b) k).
Lemma Wf_grows : forall M a k b, mem_grows M (Wf M a k b).
Proof. intros. unfold Wf. apply wbytes_grows. Qed.
Lemma wok_Wf : forall M a k b c m, wok M c m -> wok (Wf M a k b) c m.
Proof. intros. eapply wok_grows; [apply Wf_grows | assumption]. Qed.
Lemma wr_Wf : forall M a k b c m, wr M c m -> wr (Wf M a k b) c m.
Proof. intros. eapply wr_grows; [apply Wf_grows | assumption]. Qed.
Lemma rdn_Wf_other : forall M a k b c m,
  0 <= a -> a + Z.of_nat k < 2 ^ 64 -> 0 <= c -> c + Z.of_nat m < 2 ^ 64 -> apart a (Z.of_nat k) c (Z.of_nat m) ->
  rdn segs (Wf M a k b) (Z_to_bv 64 c) m = rdn segs M (Z_to_bv 64 c) m.
Proof.
  intros M a k b c m Ha Hk Hc Hm Hap. unfold Wf.
  apply rdn_wbytes_out; rewrite ?repeat_length; rewrite ?(art_u_lit a) by lia; rewrite ?(art_u_lit c) by lia; unfold apart in Hap; lia.
Qed.
Lemma cell_Wf_other : forall M a k b c m u,
  0 <= a -> a + Z.of_nat k < 2 ^ 64 -> 0 <= c -> c + Z.of_nat m < 2 ^ 64 -> apart a (Z.of_nat k) c (Z.of_nat m) ->
  cell M c m u -> cell (Wf M a k b) c m u.
Proof. intros M a k b c m u Ha Hk Hc Hm Hap H. unfold cell. rewrite rdn_Wf_other by assumption. exact H. Qed.
Lemma Wf_outside : forall M a k b (x : word),
  0 <= a -> a + Z.of_nat k < 2 ^ 64 -> ~ (a <= bv_unsigned x < a + Z.of_nat k) -> Wf M a k b x = M x.
Proof.
  intros M a k b x Ha Hk Hx. unfold Wf.
  destruct (Z_lt_le_dec (bv_unsigned x) a) as [L|G].
  - apply wbytes_below; rewrite ?repeat_length, art_u_lit by lia; lia.
  - apply wbytes_above. rewrite repeat_length, art_u_lit by lia. lia.
Qed.
Lemma Wf_inside : forall M a k b i, 0 <= a -> a + Z.of_nat k < 2 ^ 64 -> 0 <= i < Z.of_nat k ->
  Wf M a k b (Z_to_bv 64 (a + i)) = Some (Z_to_bv 8 b).
Proof.
  intros M a k b i Ha Hk Hi. unfold Wf.
  rewrite wbytes_inside; rewrite ?repeat_length, ?art_u_lit by lia; try lia.
  rewrite nth_repeat_lt by lia. reflexivity.
Qed.

Lemma Wn_eq : forall n M M' a a' v v', M = M' -> a = a' -> v = v' -> Wn n M a v = Wn n M' a' v'.
Proof. intros; subst; reflexivity. Qed.
Lemma Wf_eq : forall M M' a a' k k' b b', M = M' -> a = a' -> k = k' -> b = b' -> Wf M a k b = Wf M' a' k' b'.
Proof. intros; subst; reflexivity. Qed.

Lemma cell_rdn8 : forall M a v, cell M a 8 v ->
  rdn segs M (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 v)) /\ bytes_le_to_Z (word_to_le_bytes 8 (Z_to_bv 64 v)) = bv_unsigned (Z_to_bv 64 v).
Proof. intros M a v H. split; [exact H | apply bytes_le_to_Z_8]. Qed.
Lemma cell_rdn1 : forall M a v, 0 <= v < 256 -> cell M a 1 v -> rdn segs M (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v].
Proof. intros M a v Hv H. unfold cell in H. rewrite art_bytes1 in H by lia. exact H. Qed.
Lemma cell_rdn4 : forall M a v, 0 <= v < 2 ^ 32 -> cell M a 4 v ->
  rdn segs M (Z_to_bv 64 a) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 v)) /\ bytes_le_to_Z (word_to_le_bytes 4 (Z_to_bv 64 v)) = bv_unsigned (Z_to_bv 64 v).
Proof. intros M a v Hv H. split; [exact H | apply art_bytes4; exact Hv]. Qed.

End WithSegs.
