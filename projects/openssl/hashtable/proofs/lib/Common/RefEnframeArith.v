(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import PropExec SeqExec AgentLib MallocDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma v_and_lit : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
  v_and (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (Z.land a b).
Proof. intros. unfold v_and. rewrite !u64_lit by lia. reflexivity. Qed.

Lemma v_or_lit : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
  v_or (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (Z.lor a b).
Proof. intros. unfold v_or. rewrite !u64_lit by lia. reflexivity. Qed.

Lemma v_andi_lit : forall a i, 0 <= a < 2 ^ 64 -> 0 <= i < 2 ^ 64 ->
  v_andi (Z_to_bv 64 a) i = Z_to_bv 64 (Z.land a i).
Proof.
  intros. unfold v_andi. rewrite u64_lit by lia. rewrite bv_wrap64_mod, Z.mod_small by lia.
  reflexivity.
Qed.

Lemma v_srli_lit : forall a s, 0 <= a < 2 ^ 64 -> 0 <= s ->
  v_srli (Z_to_bv 64 a) s = Z_to_bv 64 (a / 2 ^ s).
Proof. intros. unfold v_srli. rewrite u64_lit by lia. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.

Lemma v_slli_lit : forall a s, 0 <= a -> 0 <= s -> a * 2 ^ s < 2 ^ 64 ->
  v_slli (Z_to_bv 64 a) s = Z_to_bv 64 (a * 2 ^ s).
Proof.
  intros. unfold v_slli. pose proof (Z.pow_pos_nonneg 2 s ltac:(lia) ltac:(lia)).
  rewrite u64_lit by nia. rewrite Z.shiftl_mul_pow2 by lia. reflexivity.
Qed.

Lemma v_mul_lit : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
  v_mul (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a * b).
Proof. intros. unfold v_mul. rewrite !u64_lit by lia. reflexivity. Qed.

Lemma v_sltu_lit : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
  v_sltu (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (if a <? b then 1 else 0).
Proof.
  intros. unfold v_sltu, c_ltu, bv_ltu. rewrite !u64_lit by lia.
  destruct (a <? b); reflexivity.
Qed.

(* [comment removed for export] *)
Lemma land_range : forall a b, 0 <= a -> 0 <= b -> 0 <= Z.land a b <= a.
Proof.
  intros a b Ha Hb. split; [apply Z.land_nonneg; lia|].
  pose proof (Z.add_lor_land a b). pose proof (Z.lor_nonneg a b).
  assert (Z.land a b <= Z.lor a b).
  { (* [comment removed for export] *)
    apply Z.ldiff_le; [apply Z.lor_nonneg; lia|].
    apply Z.bits_inj'. intros i Hi. rewrite Z.ldiff_spec, Z.land_spec, Z.lor_spec, Z.bits_0.
    destruct (Z.testbit a i), (Z.testbit b i); reflexivity. }
  (* [comment removed for export] *)
  pose proof (Z.add_lor_land a b).
  assert (Z.land a b = Z.land b a) by apply Z.land_comm.
  assert (b <= Z.lor a b).
  { apply Z.ldiff_le; [apply Z.lor_nonneg; lia|].
    apply Z.bits_inj'. intros i Hi. rewrite Z.ldiff_spec, Z.lor_spec, Z.bits_0.
    destruct (Z.testbit a i), (Z.testbit b i); reflexivity. }
  lia.
Qed.

Lemma lor_range : forall a b k, 0 <= k -> 0 <= a < 2 ^ k -> 0 <= b < 2 ^ k -> 0 <= Z.lor a b < 2 ^ k.
Proof.
  intros a b k Hk Ha Hb. split; [apply Z.lor_nonneg; lia|].
  apply Z_bounded_by_bits; [lia | apply Z.lor_nonneg; lia |].
  intros i Hi. rewrite Z.lor_spec.
  rewrite (Z_testbit_high k a i) by lia. rewrite (Z_testbit_high k b i) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma u_not : forall s, 0 <= s < 2 ^ 64 ->
  bv_unsigned (v_xori (Z_to_bv 64 s) (-1)) = 2 ^ 64 - 1 - s.
Proof.
  intros s Hs. unfold v_xori. rewrite (u64_lit s) by lia.
  change (bv_wrap 64 (-1)) with (Z.ones 64).
  assert (E : Z.lxor s (Z.ones 64) = 2 ^ 64 - 1 - s).
  { rewrite <- Z.ldiff_ones_l_low; [| lia |].
    - rewrite Z.ldiff_land.
      rewrite <- Z.sub_land_same_l. rewrite Z.land_comm, Z.land_ones, Z.mod_small by lia.
      rewrite Z.ones_equiv. lia.
    - destruct (Z.eq_dec s 0) as [->|Hz]; [cbn; lia|]. apply Z.log2_lt_pow2; lia. }
  rewrite E. apply u64_lit. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma swrap32_small : forall x, - 2 ^ 31 <= x < 2 ^ 31 -> bv_swrap 32 x = x.
Proof.
  intros x Hx. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  replace (2 ^ Z.of_N 32) with (2 ^ 32) by reflexivity.
  replace (2 ^ 32 `div` 2) with (2 ^ 31) by reflexivity. lia.
Qed.

Lemma swrap32_add_mod : forall x k, bv_swrap 32 (x + k * 2 ^ 32) = bv_swrap 32 x.
Proof.
  intros x k. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  replace (2 ^ Z.of_N 32) with (2 ^ 32) by reflexivity. lia.
Qed.

Lemma v_subw_lit : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
  - 2 ^ 31 <= a - b < 2 ^ 31 ->
  v_subw (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a - b).
Proof. intros. unfold v_subw. rewrite !u64_lit by lia. rewrite swrap32_small by lia. reflexivity. Qed.

Lemma v_slliw_lit : forall a s, 0 <= a -> 0 <= s -> a * 2 ^ s < 2 ^ 31 ->
  v_slliw (Z_to_bv 64 a) s = Z_to_bv 64 (a * 2 ^ s).
Proof.
  intros. unfold v_slliw. pose proof (Z.pow_pos_nonneg 2 s ltac:(lia) ltac:(lia)).
  rewrite u64_lit by nia. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite swrap32_small by nia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma v_addw_small : forall (x y : word) r,
  - 2 ^ 31 <= r < 2 ^ 31 ->
  (exists k, bv_unsigned x + bv_unsigned y = r + k * 2 ^ 32) ->
  v_addw x y = Z_to_bv 64 r.
Proof.
  intros x y r Hr [k Hk]. unfold v_addw. rewrite Hk, swrap32_add_mod, swrap32_small by lia.
  reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma fld_lastidx : forall W, Z.land W 31 = W mod 32.
Proof. intros W. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma land_126_check :
  zall (N.to_nat 128%N) (fun r => Z.land r 126 =? 2 * ((r / 2) mod 64)) 0 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma land_126 : forall x, 0 <= x -> Z.land x 126 = 2 * ((x / 2) mod 64).
Proof.
  intros x Hx.
  transitivity (Z.land (x mod 128) 126).
  { change 128 with (2 ^ 7). rewrite <- (Z.land_ones x 7) by lia.
    rewrite <- Z.land_assoc. reflexivity. }
  pose proof (zallN_spec _ _ land_126_check (x mod 128) ltac:(cbn; lia)) as E.
  apply Z.eqb_eq in E. rewrite E. f_equal. lia.
Qed.

Lemma fld_sizeclass2 : forall W, 0 <= W -> Z.land (W / 32) 126 = 2 * ((W / 64) mod 64).
Proof. intros W HW. rewrite land_126 by lia. f_equal. f_equal. lia. Qed.

(* [comment removed for export] *)
Lemma fld_hi : forall W, 0 <= W < 2 ^ 64 -> Z.land W (2 ^ 64 - 4096) = 4096 * (W / 4096).
Proof.
  intros W HW.
  apply Z.bits_inj'. intros i Hi.
  change (2 ^ 64 - 4096) with (Z.ones 52 * 2 ^ 12).
  rewrite Z.land_spec, Z.mul_pow2_bits, Z.testbit_ones by lia.
  replace (4096 * (W / 4096)) with ((W / 2 ^ 12) * 2 ^ 12) by (change (2 ^ 12) with 4096; lia).
  rewrite Z.mul_pow2_bits by lia.
  destruct (Z.lt_ge_cases i 12) as [Hlt|Hge].
  - rewrite (Z.testbit_neg_r (W / 2 ^ 12)) by lia.
    replace ((0 <=? i - 12) && (i - 12 <? 52))%bool with false
      by (symmetry; apply andb_false_iff; left; apply Z.leb_gt; lia).
    apply andb_false_r.
  - rewrite Z.div_pow2_bits by lia. replace (i - 12 + 12) with i by lia.
    destruct (Z.lt_ge_cases i 64) as [Hlt'|Hge'].
    + replace ((0 <=? i - 12) && (i - 12 <? 52))%bool with true
        by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
      apply andb_true_r.
    + rewrite (Z_testbit_high 64 W i) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma lor_shift5 : forall rc l, 0 <= rc -> 0 <= l < 32 -> Z.lor (rc * 2 ^ 5) l = l + 32 * rc.
Proof.
  intros rc l Hrc Hl.
  pose proof (Z.add_lor_land (rc * 2 ^ 5) l) as E.
  assert (Z : Z.land (rc * 2 ^ 5) l = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0, Z.mul_pow2_bits by lia.
    destruct (Z.lt_ge_cases i 5) as [Hlt|Hge].
    - rewrite (Z.testbit_neg_r rc) by lia. reflexivity.
    - rewrite (Z_testbit_high 5 l i) by lia. apply andb_false_r. }
  change (2 ^ 5) with 32 in *. lia.
Qed.

Lemma land_31_small : forall l, 0 <= l < 32 -> Z.land l 31 = l.
Proof. intros. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. lia. Qed.

Lemma land_255 : forall a, 0 <= a -> Z.land a 255 = a mod 256.
Proof. intros. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma enframe_off_check :
  zall (N.to_nat 65536%N)
    (fun i => let slack := i / 256 in let off0 := i mod 256 in
              let r := enframe_off slack off0 in (0 <=? r) && (r <=? slack))%bool 0 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma enframe_off_bound : forall slack off0,
  0 <= slack -> 0 <= off0 < 256 -> 0 <= enframe_off slack off0 <= Z.max slack off0
  /\ (enframe_off slack off0 <= slack \/ enframe_off slack off0 = off0).
Proof.
  intros slack off0 Hs Ho.
  destruct (Z.lt_ge_cases slack 256) as [Hl|Hg].
  - pose proof (zallN_spec _ _ enframe_off_check (slack * 256 + off0) ltac:(cbn; lia)) as E.
    cbv beta zeta in E.
    replace ((slack * 256 + off0) / 256) with slack in E by lia.
    replace ((slack * 256 + off0) mod 256) with off0 in E by lia.
    apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2. lia.
  - unfold enframe_off. rewrite (proj2 (Z.leb_le off0 slack)) by lia. lia.
Qed.

Lemma enframe_off_le : forall slack off0,
  0 <= slack -> 0 <= off0 < 256 -> 0 <= enframe_off slack off0 <= slack.
Proof.
  intros slack off0 Hs Ho.
  destruct (Z.lt_ge_cases slack 256) as [Hl|Hg].
  - pose proof (zallN_spec _ _ enframe_off_check (slack * 256 + off0) ltac:(cbn; lia)) as E.
    cbv beta zeta in E.
    replace ((slack * 256 + off0) / 256) with slack in E by lia.
    replace ((slack * 256 + off0) mod 256) with off0 in E by lia.
    apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2. lia.
  - unfold enframe_off. rewrite (proj2 (Z.leb_le off0 slack)) by lia. lia.
Qed.

Lemma smear_range : forall slack, 0 <= slack < 2 ^ 64 -> 0 <= smear slack < 2 ^ 64.
Proof.
  intros slack Hs. unfold smear.
  assert (H1 : 0 <= Z.lor slack (slack / 2) < 2 ^ 64) by (apply lor_range; lia).
  assert (H2 : 0 <= Z.lor (Z.lor slack (slack / 2)) (Z.lor slack (slack / 2) / 4) < 2 ^ 64)
    by (apply lor_range; lia).
  apply lor_range; lia.
Qed.

Lemma enframe_off_255 : forall slack off0,
  0 <= slack -> 0 <= off0 < 256 -> enframe_off slack off0 <= 255.
Proof.
  intros slack off0 Hs Ho.
  destruct (Z.le_gt_cases off0 slack) as [Hle|Hgt].
  - unfold enframe_off. rewrite (proj2 (Z.leb_le off0 slack) Hle). lia.
  - pose proof (enframe_off_le slack off0 Hs Ho). lia.
Qed.

Lemma div_range64 : forall a d, 0 <= a < 2 ^ 64 -> 0 < d -> 0 <= a / d < 2 ^ 64.
Proof. intros a d Ha Hd. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. nia. Qed.

Lemma div_le_self : forall a d, 0 <= a -> 0 < d -> 0 <= a / d <= a.
Proof.
  intros a d Ha Hd. split; [apply Z.div_pos; lia|].
  destruct (Z.eq_dec d 1) as [->|Hne]; [rewrite Z.div_1_r; lia|].
  destruct (Z.eq_dec a 0) as [->|Hz]; [rewrite Z.div_0_l by lia; lia|].
  apply Z.lt_le_incl. apply Z.div_lt; lia.
Qed.

Lemma u8_lit : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof. intros z Hz. apply Z_to_bv_small. unfold bv_modulus. cbn. lia. Qed.

Lemma v_andi_255 : forall x : word, v_andi x 255 = Z_to_bv 64 (bv_unsigned x mod 256).
Proof.
  intros x. unfold v_andi. change (bv_wrap 64 255) with (Z.ones 8).
  rewrite Z.land_ones by lia. reflexivity.
Qed.

Lemma v_andi_31 : forall x : word, v_andi x 31 = Z_to_bv 64 (bv_unsigned x mod 32).
Proof.
  intros x. unfold v_andi. change (bv_wrap 64 31) with (Z.ones 5).
  rewrite Z.land_ones by lia. reflexivity.
Qed.

Lemma v_not_lit : forall s, 0 <= s < 2 ^ 64 ->
  v_xori (Z_to_bv 64 s) (-1) = Z_to_bv 64 (2 ^ 64 - 1 - s).
Proof.
  intros s Hs. rewrite <- (Z_to_bv_bv_unsigned 64 (v_xori (Z_to_bv 64 s) (-1))).
  rewrite u_not by lia. reflexivity.
Qed.

Lemma smear_via_regs : forall S, 0 <= S ->
  let m1 := Z.lor S (S / 2) in
  let m2 := Z.lor (m1 / 4) m1 in
  Z.lor (m2 / 16) m2 = smear S.
Proof.
  intros S HS. cbv zeta. unfold smear.
  rewrite (Z.lor_comm (Z.lor S (S / 2) / 4)).
  rewrite (Z.lor_comm (_ / 16)). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma neg_mask : forall (b : bool) K, 0 <= K < 2 ^ 64 ->
  v_and (v_subw (Z_to_bv 64 0) (Z_to_bv 64 (if b then 1 else 0))) (Z_to_bv 64 K)
  = Z_to_bv 64 (if b then K else 0).
Proof.
  intros b K HK. destruct b.
  - rewrite v_subw_lit by lia. rewrite (Z_to_bv_64_mod (0 - 1)).
    change ((0 - 1) mod 2 ^ 64) with (2 ^ 64 - 1).
    rewrite v_and_lit by lia. change (2 ^ 64 - 1) with (Z.ones 64).
    rewrite Z.land_comm, Z.land_ones, Z.mod_small by lia. reflexivity.
  - rewrite v_subw_lit by lia. rewrite v_and_lit by lia. rewrite Z.land_0_l. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma addw_mask : forall (b : bool) S om,
  0 <= S < 2 ^ 64 -> 0 <= om < 2 ^ 31 -> (b = true -> S < om) ->
  v_addw (Z_to_bv 64 (if b then 2 ^ 64 - 1 - S else 0)) (Z_to_bv 64 om)
  = Z_to_bv 64 (if b then om - S - 1 else om).
Proof.
  intros b S om HS Hom Hb. destruct b.
  - specialize (Hb eq_refl). apply v_addw_small; [lia|]. exists (2 ^ 32). rewrite !u64_lit by lia.
    change (2 ^ 32 * 2 ^ 32) with (2 ^ 64). lia.
  - apply v_addw_small; [lia|]. exists 0. rewrite !u64_lit by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma v_add_neg : forall e r, 0 <= r <= e -> e < 2 ^ 64 ->
  v_add (Z_to_bv 64 e) (Z_to_bv 64 (0 - r)) = Z_to_bv 64 (e - r).
Proof.
  intros e r Hr He. unfold v_add. rewrite (u64_lit e) by lia.
  rewrite (Z_to_bv_unsigned 64 (0 - r)), bv_wrap64_mod.
  rewrite (Z_to_bv_64_mod (e + (0 - r) mod 2 ^ 64)). rewrite Z.add_mod_idemp_r by lia.
  rewrite <- Z_to_bv_64_mod. f_equal; lia.
Qed.

Lemma c_lts_lit : forall a b, 0 <= a < 2 ^ 63 -> 0 <= b < 2 ^ 63 ->
  c_lts (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof. intros a b Ha Hb. unfold c_lts, bv_lts. rewrite !bv_signed_small by lia. reflexivity. Qed.
