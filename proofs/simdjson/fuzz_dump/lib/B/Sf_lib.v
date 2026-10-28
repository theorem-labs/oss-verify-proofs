(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Export SFModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Export FX_lib.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Spec Require Export SoftFloat.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Lemma b2z_Zb2z : b2z = Z.b2z. Proof. reflexivity. Qed.

Ltac unfold_sf_in H :=
  cbv beta delta [add64 sub64 mul64 shl64 not64 ltu64 eqz64 nez64 zext32 sext32 srliw mulhu
         is_neg64 sra63 lt_s64 lo64 hi64 wrap64 b2z
         ONES64 M32 SIGN64 MASK48 MASKLO ABS_HI INF_HI QUIET_HI QNAN_HI IMPLICIT_HI] in H.
Ltac unfold_sf :=
  cbv beta delta [add64 sub64 mul64 shl64 not64 ltu64 eqz64 nez64 zext32 sext32 srliw mulhu
         is_neg64 sra63 lt_s64 lo64 hi64 wrap64 b2z
         ONES64 M32 SIGN64 MASK48 MASKLO ABS_HI INF_HI QUIET_HI QNAN_HI IMPLICIT_HI].

Ltac norm_model H := unfold_sf_in H; zb_fold_lits_in H.

Ltac get_head t := lazymatch t with ?g _ => get_head g | _ => t end.

Tactic Notation "model_hyp" ident(HR) constr(t) :=
  assert (HR : t = t) by reflexivity;
  let h := get_head t in unfold h in HR at 2;
  norm_model HR.

Lemma lo64_mk128' : forall hi lo, (0 <= lo < 2^64)%Z -> (0 <= hi)%Z -> lo64 (mk128 hi lo) = lo.
Proof.
  intros hi lo Hlo Hhi. unfold lo64, mk128. rewrite wrap64_mod.
  rewrite <- Z.land_ones by lia. apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, Z.lor_spec, Z.shiftl_spec by lia.
  destruct (Z.lt_ge_cases i 64).
  - rewrite Z.ones_spec_low, (Z.testbit_neg_r _ (i - 64)) by lia. cbn. apply andb_true_r.
  - rewrite Z.ones_spec_high by lia. rewrite andb_false_r.
    symmetry. destruct (Z.eq_dec lo 0) as [->|]; [apply Z.bits_0|].
    apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 64%Z; [apply Z.log2_lt_pow2; lia|lia].
Qed.

Lemma lo64_mk128 : forall hi lo, (0 <= lo < 2^64)%Z -> (0 <= hi < 2^64)%Z -> lo64 (mk128 hi lo) = lo.
Proof. intros. apply lo64_mk128'; lia. Qed.

Lemma hi64_mk128 : forall hi lo, (0 <= lo < 2^64)%Z -> (0 <= hi < 2^64)%Z -> hi64 (mk128 hi lo) = hi.
Proof.
  intros hi lo Hlo Hhi. unfold hi64, mk128. rewrite wrap64_mod.
  rewrite Z.shiftr_lor, Z.shiftr_shiftl_l, Z.sub_diag, Z.shiftl_0_r by lia.
  rewrite (Z.shiftr_div_pow2 lo), Z.div_small, Z.lor_0_r by lia. apply Z.mod_small. lia.
Qed.

Lemma mk128_regs : forall hi lo, (0 <= lo < 2^64)%Z -> (0 <= hi < 2^64)%Z ->
  Z_to_bv 64 (lo64 (mk128 hi lo)) = Z_to_bv 64 lo /\ Z_to_bv 64 (hi64 (mk128 hi lo)) = Z_to_bv 64 hi.
Proof. intros. rewrite lo64_mk128, hi64_mk128 by lia. split; reflexivity. Qed.

Ltac sf_finish :=
  apply evt_done;
  lazymatch goal with |- ?P ?ms => try unfold P end; hnf;
  rewrite ?lo64_mk128, ?hi64_mk128 by zrange;
  repeat (lazymatch goal with |- ex _ => eexists end);
  split; [ ms_eq | repeat match goal with |- _ /\ _ => split end; try assumption ].

Local Open Scope Z_scope.

Lemma zb_land_pow2_bit0 : forall x k, 0 <= k -> Z.testbit x k = false -> Z.land x (2^k) = 0.
Proof.
  intros x k Hk Hb. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0, Z.pow2_bits_eqb by lia.
  destruct (Z.eqb_spec k i) as [<-|]; [rewrite Hb; reflexivity| apply Bool.andb_false_r].
Qed.

Lemma zb_lxor_pow2 : forall x k, 0 <= k ->
  Z.lxor x (2^k) = x + 2^k - 2 * 2^k * ((x / 2^k) mod 2).
Proof.
  intros x k Hk.
  destruct (Z.testbit x k) eqn:Hb.
  - pose proof (proj1 (Z.testbit_true x k Hk) Hb) as Hm. rewrite Hm.
    set (y := Z.lxor x (2^k)).
    assert (Hy : Z.testbit y k = false).
    { subst y. rewrite Z.lxor_spec, Hb, Z.pow2_bits_true by lia. reflexivity. }
    assert (E : Z.lxor y (2^k) = y + 2^k).
    { symmetry. apply Z.add_nocarry_lxor. apply zb_land_pow2_bit0; assumption. }
    subst y. rewrite Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_r in E. lia.
  - pose proof (proj1 (Z.testbit_false x k Hk) Hb) as Hm. rewrite Hm.
    rewrite <- Z.add_nocarry_lxor by (apply zb_land_pow2_bit0; assumption). lia.
Qed.

Lemma zb_lxor_b31 : forall x, Z.lxor x 2147483648 = x + 2147483648 - 4294967296 * ((x / 2147483648) mod 2).
Proof. intros x. change 2147483648 with (2^31). rewrite zb_lxor_pow2 by lia. lia. Qed.

Lemma bv_wrap32_eq : forall z, bv_wrap 32 z = z mod 4294967296.
Proof. reflexivity. Qed.

Lemma swrap32_eq : forall z, bv_swrap 32 z = (z + 2147483648) mod 4294967296 - 2147483648.
Proof. reflexivity. Qed.

Lemma swrap32_small : forall z, - 2147483648 <= z < 2147483648 -> bv_swrap 32 z = z.
Proof. intros z Hz. rewrite swrap32_eq. rewrite Z.mod_small by lia. lia. Qed.

Lemma sext32_eq : forall z, sext32 z = ((z + 2147483648) mod 4294967296 - 2147483648) mod 18446744073709551616.
Proof.
  intros z. unfold sext32, sub64, M32. rewrite wrap64_mod. change (2^64) with 18446744073709551616. f_equal.
  change 4294967295 with (2^32 - 1). rewrite zb_land_mask by lia. change 2147483648 with (2^31).
  rewrite zb_lxor_pow2 by lia. change 4294967296 with (2^32).
  Z.div_mod_to_equations. nia.
Qed.

Lemma land_swrap32_sext32 : forall z, Z.land (bv_swrap 32 z) 18446744073709551615 = sext32 z.
Proof. intros z. rewrite land_W64, sext32_eq, swrap32_eq. reflexivity. Qed.

Lemma mod_swrap32_sext32 : forall z, (bv_swrap 32 z) mod 18446744073709551616 = sext32 z.
Proof. intros z. rewrite sext32_eq, swrap32_eq. reflexivity. Qed.

Lemma Z_to_bv_swrap32 : forall z, Z_to_bv 64 (bv_swrap 32 z) = Z_to_bv 64 (sext32 z).
Proof. intros z. rewrite <- land_swrap32_sext32. symmetry. apply Z_to_bv_land64. Qed.

Lemma sext32_range : forall z, 0 <= sext32 z < 18446744073709551616.
Proof. intros z. rewrite sext32_eq. apply Z.mod_pos_bound. lia. Qed.

Lemma sext32_small : forall z, 0 <= z < 2147483648 -> sext32 z = z.
Proof. intros z Hz. rewrite sext32_eq. rewrite (Z.mod_small (z + _)) by lia. rewrite Z.mod_small by lia. lia. Qed.

Lemma sext32_mod32 : forall z, sext32 (z mod 4294967296) = sext32 z.
Proof.
  intros z. rewrite !sext32_eq. f_equal. f_equal.
  rewrite Z.add_mod_idemp_l by lia. reflexivity.
Qed.

Lemma sext32_land64 : forall z, sext32 (Z.land z 18446744073709551615) = sext32 z.
Proof.
  intros z. rewrite land_W64, <- (sext32_mod32 (z mod 2^64)), <- (sext32_mod32 z). f_equal.
  change (2^64) with (4294967296 * 4294967296). rewrite Z.rem_mul_r by lia.
  rewrite Z.mul_comm, Z.mod_add by lia. apply Z.mod_mod. lia.
Qed.

Lemma sext32_landM32 : forall z, sext32 (Z.land z 4294967295) = sext32 z.
Proof.
  intros z. change 4294967295 with (2^32 - 1). rewrite zb_land_mask by lia. apply sext32_mod32.
Qed.

Lemma sext32_low : forall z, (sext32 z) mod 4294967296 = z mod 4294967296.
Proof.
  intros z. rewrite sext32_eq. change 18446744073709551616 with (4294967296 * 4294967296).
  rewrite Z.rem_mul_r by lia. rewrite Z.mul_comm, Z.mod_add by lia.
  Z.div_mod_to_equations. lia.
Qed.

Lemma zext32_eq : forall z, zext32 z = z mod 4294967296.
Proof. intros z. unfold zext32, M32. change 4294967295 with (2^32 - 1). rewrite zb_land_mask by lia. reflexivity. Qed.

Lemma zext32_small : forall z, 0 <= z < 4294967296 -> zext32 z = z.
Proof. intros z Hz. rewrite zext32_eq. apply Z.mod_small. lia. Qed.

Lemma zext32_sext32 : forall z, zext32 (sext32 z) = z mod 4294967296.
Proof. intros z. rewrite zext32_eq. apply sext32_low. Qed.

Lemma srliw_pos : forall x k, 0 < k -> srliw x k = Z.shiftr (x mod 4294967296) k.
Proof.
  intros x k Hk. unfold srliw. unfold M32. change 4294967295 with (2^32 - 1). rewrite zb_land_mask by lia.
  change (2^32) with 4294967296.
  apply sext32_small. pose proof (Z.mod_pos_bound x 4294967296 ltac:(lia)) as Hr.
  rewrite Z.shiftr_div_pow2 by lia. split. { apply Z.div_pos; lia. }
  apply Z.div_lt_upper_bound; [lia|]. apply Z.lt_le_trans with 4294967296; [lia|].
  assert (2^1 <= 2^k) by (apply Z.pow_le_mono_r; lia). change (2^1) with 2 in *. lia.
Qed.

Lemma walk_srliw : forall x k, 0 < k -> 0 <= x ->
  bv_swrap 32 (Z.shiftr (bv_wrap 32 x) k) = Z.shiftr (x mod 4294967296) k.
Proof.
  intros x k Hk Hx. rewrite bv_wrap32_eq. apply swrap32_small.
  pose proof (Z.mod_pos_bound x 4294967296 ltac:(lia)) as Hr.
  rewrite Z.shiftr_div_pow2 by lia. split. { apply Z.le_trans with 0; [lia|]. apply Z.div_pos; lia. }
  apply Z.div_lt_upper_bound; [lia|]. apply Z.lt_le_trans with 4294967296; [lia|].
  assert (2^1 <= 2^k) by (apply Z.pow_le_mono_r; lia). change (2^1) with 2 in *. lia.
Qed.

Lemma land_mask_small : forall x k, 0 <= k -> 0 <= x < 2^k -> Z.land x (2^k - 1) = x.
Proof. intros x k Hk Hx. rewrite zb_land_mask by lia. apply Z.mod_small. lia. Qed.

Lemma land_W64_small : forall x, 0 <= x < 18446744073709551616 -> Z.land x 18446744073709551615 = x.
Proof. intros x Hx. change 18446744073709551615 with (2^64 - 1). apply land_mask_small; [lia|]. change (2^64) with 18446744073709551616. lia. Qed.

Lemma land_M32_small : forall x, 0 <= x < 4294967296 -> Z.land x 4294967295 = x.
Proof. intros x Hx. change 4294967295 with (2^32 - 1). apply land_mask_small; [lia|]. change (2^32) with 4294967296. lia. Qed.

Lemma land63_small : forall x, 0 <= x < 64 -> Z.land x 63 = x.
Proof. intros x Hx. change 63 with (2^6 - 1). apply land_mask_small; [lia|]. change (2^6) with 64. lia. Qed.

Lemma land63_64_128 : forall x, 64 <= x < 128 -> Z.land x 63 = x - 64.
Proof.
  intros x Hx. change 63 with (2^6 - 1). rewrite zb_land_mask by lia. change (2^6) with 64.
  rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma shiftr63_small : forall x, 0 <= x < 9223372036854775808 -> Z.shiftr x 63 = 0.
Proof. intros x Hx. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. change (2^63) with 9223372036854775808. lia. Qed.

Lemma shiftr_bound : forall x k, 0 <= x < 18446744073709551616 -> 0 <= k <= 64 ->
  0 <= Z.shiftr x k < 2^(64 - k).
Proof.
  intros x k Hx Hk. rewrite Z.shiftr_div_pow2 by lia. split. { apply Z.div_pos; lia. }
  apply Z.div_lt_upper_bound; [lia|]. rewrite <- Z.pow_add_r by lia. replace (k + (64 - k)) with 64 by lia.
  change (2^64) with 18446744073709551616. lia.
Qed.

Lemma sext32_gcc : forall v, sext32 (Z.lxor v 2147483648 - 2147483648) = sext32 v.
Proof.
  intros v. rewrite <- (sext32_mod32 (Z.lxor v _ - _)), <- (sext32_mod32 v). f_equal.
  rewrite zb_lxor_b31. Z.div_mod_to_equations. lia.
Qed.

Lemma gcc_sext_low32 : forall v, (Z.lxor v 2147483648 - 2147483648) mod 4294967296 = v mod 4294967296.
Proof. intros v. rewrite zb_lxor_b31. Z.div_mod_to_equations. lia. Qed.

Lemma gcc_sext_low6 : forall v, Z.land (Z.lxor v 2147483648 - 2147483648) 63 = Z.land v 63.
Proof.
  intros v. change 63 with (2^6 - 1). rewrite !zb_land_mask by lia. rewrite zb_lxor_b31.
  change (2^6) with 64. Z.div_mod_to_equations. lia.
Qed.

Lemma gcc_sext_small : forall v, 0 <= v < 2147483648 ->
  Z.land (Z.lxor v 2147483648 - 2147483648) 18446744073709551615 = v.
Proof.
  intros v Hv. rewrite zb_lxor_b31, (Z.div_small v) by lia. change (0 mod 2) with 0.
  rewrite land_W64. rewrite Z.mod_small; lia.
Qed.

Lemma shiftr_mod32_bound : forall x k, 0 < k -> 0 <= Z.shiftr (x mod 4294967296) k < 2147483648.
Proof.
  intros x k Hk. pose proof (Z.mod_pos_bound x 4294967296 ltac:(lia)) as Hr.
  rewrite Z.shiftr_div_pow2 by lia. split. { apply Z.div_pos; lia. }
  apply Z.div_lt_upper_bound; [lia|]. apply Z.lt_le_trans with 4294967296; [lia|].
  assert (2^1 <= 2^k) by (apply Z.pow_le_mono_r; lia). change (2^1) with 2 in *. lia.
Qed.

Lemma lxor31_sub_small : forall v, 0 <= v < 2147483648 -> Z.lxor v 2147483648 - 2147483648 = v.
Proof. intros v Hv. rewrite zb_lxor_b31, (Z.div_small v) by lia. change (0 mod 2) with 0. lia. Qed.

Ltac fix32 :=
  repeat first
  [ rewrite walk_srliw by (first [lia | zrange_nonneg])
  | match goal with
    | |- context [Z.lxor (Z.shiftr (?x mod 4294967296) ?k) 2147483648 - 2147483648] =>
        rewrite (lxor31_sub_small (Z.shiftr (x mod 4294967296) k)) by (apply shiftr_mod32_bound; lia)
    | |- context [Z.land (Z.lxor (Z.shiftr (?x mod 4294967296) ?k) 2147483648 - 2147483648) 18446744073709551615] =>
        rewrite (gcc_sext_small (Z.shiftr (x mod 4294967296) k)) by (apply shiftr_mod32_bound; lia)
    end ].
Ltac wstep := zstep; fix32.

Lemma clz32_mirror_range : forall r, 0 <= clz32_mirror r < 18446744073709551616.
Proof. intros r. unfold clz32_mirror. cbv zeta. unfold srliw at 1. apply sext32_range. Qed.

Lemma land63_mod : forall x, Z.land x 63 = x mod 64.
Proof. intros. change 63 with (2^6 - 1). rewrite zb_land_mask by lia. reflexivity. Qed.

Lemma land63_congr32 : forall x y, x mod 4294967296 = y mod 4294967296 -> Z.land x 63 = Z.land y 63.
Proof.
  intros x y H. rewrite !land63_mod.
  rewrite <- (Z.mod_mod_divide x 4294967296 64), <- (Z.mod_mod_divide y 4294967296 64) by (exists 67108864; reflexivity).
  now rewrite H.
Qed.

Lemma land63_sext32 : forall x, Z.land (sext32 x) 63 = Z.land x 63.
Proof. intros. apply land63_congr32. apply sext32_low. Qed.

Lemma land63_zext32 : forall x, Z.land (zext32 x) 63 = Z.land x 63.
Proof. intros. apply land63_congr32. rewrite zext32_eq. apply Z.mod_mod. lia. Qed.

Lemma land63_gcc : forall x,
  Z.land (Z.land (Z.lxor x 2147483648 - 2147483648) 18446744073709551615) 63 = Z.land x 63.
Proof.
  intros. apply land63_congr32. rewrite land_W64. change (2^64) with 18446744073709551616.
  rewrite Z.mod_mod_divide by (exists 4294967296; reflexivity).
  apply gcc_sext_low32.
Qed.

Lemma landM32_gcc : forall x,
  Z.land (Z.land (Z.lxor x 2147483648 - 2147483648) 18446744073709551615) 4294967295 = zext32 (sext32 x).
Proof.
  intros. rewrite zext32_sext32. change 4294967295 with (2^32 - 1). rewrite zb_land_mask, land_W64 by lia.
  change (2^32) with 4294967296. change (2^64) with 18446744073709551616.
  rewrite Z.mod_mod_divide by (exists 4294967296; reflexivity).
  apply gcc_sext_low32.
Qed.

Lemma land63_not_congr : forall x y, 0 <= x < 18446744073709551616 -> 0 <= y < 18446744073709551616 ->
  x mod 4294967296 = y mod 4294967296 ->
  Z.land (Z.lxor x 18446744073709551615) 63 = Z.land (Z.lxor y 18446744073709551615) 63.
Proof.
  intros x y Hx Hy H. rewrite !zb_lxor_ones by lia. apply land63_congr32.
  Z.div_mod_to_equations. lia.
Qed.

Lemma shl48_congr : forall x y, x mod 4294967296 = y mod 4294967296 ->
  Z.land (Z.shiftl x 48) 18446744073709551615 = Z.land (Z.shiftl y 48) 18446744073709551615.
Proof.
  intros x y H. rewrite !land_W64, !Z.shiftl_mul_pow2 by lia.
  change (2^64) with (65536 * 2^48). rewrite !Z.mul_mod_distr_r by lia. f_equal.
  rewrite <- (Z.mod_mod_divide x 4294967296 65536), <- (Z.mod_mod_divide y 4294967296 65536) by (exists 65536; reflexivity).
  now rewrite H.
Qed.

Lemma shl48_sext32 : forall x,
  Z.land (Z.shiftl (sext32 x) 48) 18446744073709551615 = Z.land (Z.shiftl x 48) 18446744073709551615.
Proof. intros. apply shl48_congr. apply sext32_low. Qed.

Lemma srai63_word : forall x, 0 <= x < 18446744073709551616 ->
  Z_to_bv 64 (Z.shiftr (bv_signed (Z_to_bv 64 x)) 63) = Z_to_bv 64 (if 9223372036854775808 <=? x then 18446744073709551615 else 0).
Proof.
  intros x Hx. rewrite zb_signed, unsigned_lit by (change (2^64) with 18446744073709551616; lia).
  change (2^63) with 9223372036854775808. change (2^64) with 18446744073709551616.
  destruct (Z.ltb_spec0 x 9223372036854775808); destruct (Z.leb_spec0 9223372036854775808 x); try (exfalso; lia).
  - rewrite Z.shiftr_div_pow2, Z.div_small by lia. reflexivity.
  - apply Z_to_bv_eqm. rewrite Z.shiftr_div_pow2 by lia. change (2^63) with 9223372036854775808.
    Z.div_mod_to_equations. lia.
Qed.

Lemma half_land : forall x, 0 <= x -> Z.land (Z.shiftr x 1) 2147483647 = Z.shiftr (x mod 4294967296) 1.
Proof.
  intros x Hx. change 2147483647 with (2^31 - 1). rewrite zb_land_mask, !Z.shiftr_div_pow2 by lia.
  change (2^31) with 2147483648. change (2^1) with 2. Z.div_mod_to_equations. lia.
Qed.

Ltac name_as_by_tac X e tac :=
  set (X := e) in *;
  let RX := fresh "R" X in
  assert (RX : 0 <= X < 18446744073709551616) by (subst X; tac).
Tactic Notation "name_as_by" ident(X) constr(e) tactic3(tac) := name_as_by_tac X e tac.

Lemma sext32_cases : forall u, 0 <= sext32 u < 2147483648 \/ 18446744071562067968 <= sext32 u < 18446744073709551616.
Proof. intros u. rewrite sext32_eq. Z.div_mod_to_equations. lia. Qed.

Lemma shiftr_const : forall x k c, 0 <= k -> c * 2^k <= x < (c + 1) * 2^k -> Z.shiftr x k = c.
Proof.
  intros x k c Hk Hx. rewrite Z.shiftr_div_pow2 by lia.
  pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk).
  apply Z.le_antisymm.
  - apply Z.lt_succ_r. apply Z.div_lt_upper_bound; [lia|]. rewrite Z.mul_comm. lia.
  - apply Z.div_le_lower_bound; [lia|]. rewrite Z.mul_comm. lia.
Qed.

Lemma land_signmask_shl : forall x, 0 <= x < 18446744073709551616 ->
  Z.land x 18446744071562067968 = Z.shiftl (Z.shiftr x 31) 31.
Proof.
  intros x Hx. change 18446744071562067968 with (Z.shiftl (Z.ones 33) 31).
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
  destruct (Z.lt_ge_cases i 31).
  - rewrite !Z.shiftl_spec_low by lia. apply Bool.andb_false_r.
  - rewrite !Z.shiftl_spec_high, Z.shiftr_spec by lia. replace (i - 31 + 31) with i by lia.
    destruct (Z.lt_ge_cases i 64).
    + rewrite Z.ones_spec_low by lia. apply Bool.andb_true_r.
    + rewrite Z.ones_spec_high by lia. rewrite Bool.andb_false_r. symmetry.
      destruct (Z.eq_dec x 0) as [->|]; [apply Z.bits_0|].
      apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 64; [|lia].
      apply Z.log2_lt_pow2; [lia|]. change (2^64) with 18446744073709551616. lia.
Qed.

Lemma land_signmask : forall x, 0 <= x < 18446744073709551616 ->
  Z.land x 18446744071562067968 = x - x mod 2147483648.
Proof.
  intros x Hx. rewrite land_signmask_shl, zb_shr_shl by lia. reflexivity.
Qed.

Lemma srai63_var : forall a : bv 64,
  Z_to_bv 64 (Z.shiftr (bv_signed a) 63) = Z_to_bv 64 (if 9223372036854775808 <=? bv_unsigned a then 18446744073709551615 else 0).
Proof.
  intros a. rewrite <- srai63_word by (pose proof (zr_word a) as H; unfold inr64 in H; change (2^64) with 18446744073709551616 in H; lia).
  rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma signhi_pos : forall x, 0 <= x < 2147483648 ->
  Z.land (Z.shiftl (Z.land x 18446744071562067968) 32) 18446744073709551615 = 0.
Proof.
  intros x Hx. rewrite land_signmask, Z.mod_small by lia. rewrite Z.sub_diag. reflexivity.
Qed.

Lemma signhi_neg : forall x, 18446744071562067968 <= x < 18446744073709551616 ->
  Z.land (Z.shiftl (Z.land x 18446744071562067968) 32) 18446744073709551615 = 9223372036854775808.
Proof.
  intros x Hx. rewrite land_signmask by lia.
  replace (x - x mod 2147483648) with 18446744071562067968 by (Z.div_mod_to_equations; lia).
  reflexivity.
Qed.

Lemma negabs_model : forall x, 0 <= x < 18446744073709551616 ->
  Z.land (Z.lxor x 18446744073709551615 - 18446744073709551615) 18446744073709551615 = (18446744073709551616 - x) mod 18446744073709551616.
Proof.
  intros x Hx. rewrite zb_lxor_ones, land_W64 by lia. change (2^64) with 18446744073709551616.
  Z.div_mod_to_equations. lia.
Qed.

Lemma negabs_code : forall x, 0 <= x < 18446744073709551616 ->
  Z.lxor 18446744073709551615 x + 1 = 18446744073709551616 - x.
Proof. intros x Hx. rewrite Z.lxor_comm, zb_lxor_ones by lia. lia. Qed.

Lemma sraiw31_word : forall x, 0 <= x < 18446744073709551616 ->
  Z_to_bv 64 (bv_swrap 32 (Z.shiftr (bv_swrap 32 x) 31)) =
  Z_to_bv 64 (Z.land (0 - Z.land (Z.shiftr x 31) 1) 18446744073709551615).
Proof.
  intros x Hx. apply Z_to_bv_eqm. rewrite land_W64, !swrap32_eq, land_1, !Z.shiftr_div_pow2 by lia.
  change (2^31)%Z with 2147483648%Z. change (2^64)%Z with 18446744073709551616%Z.
  Z.div_mod_to_equations. lia.
Qed.

Ltac model_reg_w_tac n X mexpr :=
  let w := getreg n in
  lazymatch w with
  | Z_to_bv 64 ?e =>
      replace (Z_to_bv 64 e) with (Z_to_bv 64 mexpr)
        by (rewrite ?srliw_pos by lia; first [ f_equal; zeq | rewrite Z_to_bv_land64; f_equal; zeq ]);
      set (X := mexpr) in *;
      let RX := fresh "R" X in
      assert (RX : 0 <= X < 18446744073709551616) by (subst X; rewrite ?srliw_pos by lia; zrange)
  | _ => fail "model_reg_w: register" n "holds" w
  end.
Tactic Notation "model_reg_w" constr(n) ident(X) constr(mexpr) := model_reg_w_tac n X mexpr.

Lemma clz64_mirror_range : forall x, 0 <= clz64_mirror x < 18446744073709551616.
Proof.
  intros x. unfold clz64_mirror. cbv zeta. unfold mul64.
  match goal with |- context [Z.shiftr (wrap64 ?p) 56] =>
    pose proof (wrap64_range p) as Hr; rewrite (Z.shiftr_div_pow2 (wrap64 p)) by lia end.
  change (2^64) with 18446744073709551616 in Hr.
  split. { apply Z.div_pos; lia. } apply Z.div_lt_upper_bound; lia.
Qed.

Lemma zb_land_pow2 : forall x k, 0 <= k -> Z.land x (2^k) = 2^k * ((x / 2^k) mod 2).
Proof.
  intros x k Hk. destruct (Z.testbit x k) eqn:Hb.
  - pose proof (proj1 (Z.testbit_true x k Hk) Hb) as Hm. rewrite Hm, Z.mul_1_r.
    apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.pow2_bits_eqb by lia.
    destruct (Z.eqb_spec k i) as [<-|]; [rewrite Hb; reflexivity | apply Bool.andb_false_r].
  - pose proof (proj1 (Z.testbit_false x k Hk) Hb) as Hm. rewrite Hm, Z.mul_0_r.
    apply zb_land_pow2_bit0; assumption.
Qed.

Lemma signbit63 : forall x, 0 <= x < 18446744073709551616 ->
  Z.land (Z.shiftl (Z.shiftr x 63) 63) 18446744073709551615 = Z.land 9223372036854775808 x.
Proof.
  intros x Hx. rewrite zb_shr_shl, land_W64 by lia. rewrite Z.land_comm.
  change 9223372036854775808 with (2^63). rewrite zb_land_pow2 by lia.
  change (2^63) with 9223372036854775808. change (2^64) with 18446744073709551616.
  Z.div_mod_to_equations. lia.
Qed.

Lemma lor_rot_asx : forall a s x, Z.lor (Z.lor a s) x = Z.lor (Z.lor x a) s.
Proof.
  intros. apply Z.bits_inj'. intros i Hi. rewrite !Z.lor_spec.
  destruct (Z.testbit a i), (Z.testbit s i), (Z.testbit x i); reflexivity.
Qed.
Lemma lor_rot_dsg : forall d s g, Z.lor (Z.lor d s) g = Z.lor (Z.lor d g) s.
Proof.
  intros. apply Z.bits_inj'. intros i Hi. rewrite !Z.lor_spec.
  destruct (Z.testbit d i), (Z.testbit s i), (Z.testbit g i); reflexivity.
Qed.

Ltac reg_rewrite n lem :=
  let w := getreg n in
  lazymatch w with
  | Z_to_bv 64 ?e =>
      let e' := fresh "e" in let E := fresh "E" in
      remember e as e' eqn:E in |- *;
      rewrite lem in E; subst e'
  end.

Lemma sra63_leb : forall x, 0 <= x < 18446744073709551616 ->
  (if negb (Z.shiftr x 63 =? 0) then 18446744073709551615 else 0) =
  (if 9223372036854775808 <=? x then 18446744073709551615 else 0).
Proof.
  intros x Hx. rewrite Z.shiftr_div_pow2 by lia. change (2^63) with 9223372036854775808.
  destruct (Z.leb_spec0 9223372036854775808 x).
  - rewrite (proj2 (Z.eqb_neq _ _)); [reflexivity|]. Z.div_mod_to_equations. lia.
  - rewrite Z.div_small by lia. reflexivity.
Qed.

Lemma ltb1_eqb0 : forall x, 0 <= x -> (x <? 1) = (x =? 0).
Proof. intros x Hx. destruct (Z.ltb_spec0 x 1); destruct (Z.eqb_spec x 0); try reflexivity; exfalso; lia. Qed.

Lemma sext32_congr : forall x y, x mod 4294967296 = y mod 4294967296 -> sext32 x = sext32 y.
Proof. intros x y H. rewrite <- (sext32_mod32 x), <- (sext32_mod32 y), H. reflexivity. Qed.

Lemma nez_sub_lxor : forall a b, 0 <= a < 18446744073709551616 -> 0 <= b < 18446744073709551616 ->
  (0 <? Z.land (a - b) 18446744073709551615) = (0 <? Z.lxor b a).
Proof.
  intros a b Ha Hb. rewrite land_W64. change (2^64) with 18446744073709551616.
  assert (Hn : 0 <= Z.lxor b a) by (apply Z.lxor_nonneg; split; intros; lia).
  destruct (Z.eq_dec a b) as [->|Hne].
  - rewrite Z.sub_diag, Z.lxor_nilpotent. reflexivity.
  - assert (Z.lxor b a <> 0) by (intros E; apply (proj1 (Z.lxor_eq_0_iff b a)) in E; lia).
    apply eq_true_iff_eq. rewrite !Z.ltb_lt. split; intros _; [lia|]. Z.div_mod_to_equations. lia.
Qed.

Lemma land63_lxor63 : forall x, Z.land (Z.lxor x 63) 63 = Z.land (Z.lxor x 18446744073709551615) 63.
Proof.
  intros x. change 63 with (Z.ones 6). change 18446744073709551615 with (Z.ones 64).
  apply Z.bits_inj'. intros i Hi. rewrite !Z.land_spec, !Z.lxor_spec.
  destruct (Z.lt_ge_cases i 6).
  - rewrite !Z.ones_spec_low by lia. reflexivity.
  - rewrite (Z.ones_spec_high 6) by lia. rewrite !Bool.andb_false_r. reflexivity.
Qed.

Lemma exp0_gcc : forall s, Z_to_bv 64 (s + -15360) =
  Z_to_bv 64 (Z.land (Z.land (s + 18446744073709536255) 18446744073709551615 + 1) 18446744073709551615).
Proof.
  intros s. apply Z_to_bv_eqm. rewrite !land_W64. change (2^64) with 18446744073709551616.
  Z.div_mod_to_equations. lia.
Qed.

Definition to_d_pack (dE dS a_hi : Z) : Z := Z.lor (Z.lor (shl64 dE 52) (shl64 (shr64 a_hi 63) 63)) dS.

Definition to_d_normD (sig1 exp0 : Z) : Z * Z :=
  let carry := shr64 sig1 52 in (add64 carry exp0, Z.land (sub64 carry 1) sig1).

Definition to_d_normal (a_lo sigHi candM1 : Z) : Z * Z :=
  let sig0 := Z.lor (shr64 a_lo 60) (shl64 sigHi 4) in
  let roundBits := shr64 (shl64 a_lo 4) 4 in
  let exp0 := add64 candM1 1 in
  let sig1 := trunc_round sig0 roundBits in
  to_d_normD sig1 exp0.

Definition to_d_subD (sig1 : Z) : Z * Z :=
  let carry := nez64 (shr64 sig1 52) in (carry, Z.lxor sig1 (shl64 carry 52)).

Definition to_d_subC (srLo sigHi1 shift mM64 sticky : Z) : Z * Z :=
  let srHi0 := shr64 sigHi1 (Z.land shift 63) in
  let srHi := Z.land (sra63 mM64) srHi0 in
  let sig0 := Z.lor (shr64 srLo 60) (shl64 srHi 4) in
  let roundBits := Z.lor (shr64 (shl64 srLo 4) 4) sticky in
  let sig1 := trunc_round sig0 roundBits in
  to_d_subD sig1.

Definition to_d_subB (a_lo sigHi1 shift shNZ slLo slHi : Z) : Z * Z :=
  let stickySrc := Z.lor slLo slHi in
  let m := zext32 shift in
  let sticky0 := nez64 stickySrc in
  let mM64 := sub64 m 64 in
  let sticky := Z.land shNZ sticky0 in
  let srLo := if negb (is_neg64 mM64) then shr64 sigHi1 (Z.land m 63)
              else Z.lor (shr64 a_lo (Z.land shift 63)) (shl64 (shl64 sigHi1 1) (Z.land (not64 m) 63)) in
  to_d_subC srLo sigHi1 shift mM64 sticky.

Definition to_d_subA (a_lo sigHi srcExp k shift : Z) : Z * Z :=
  let expNZ := nez64 srcExp in
  let shNZ0 := Z.lxor k srcExp in
  let negsh := sext32 (sub64 0 shift) in
  let implicit := shl64 expNZ 48 in
  let shNZ := nez64 shNZ0 in
  let nW := sext32 (sub64 128 shift) in
  let t0 := shl64 a_lo (Z.land negsh 63) in
  let sigHi1 := Z.lor sigHi implicit in
  let n := zext32 nW in
  let nM64 := sub64 n 64 in
  let slLo := Z.land (sra63 nM64) t0 in
  let slHi := if negb (is_neg64 nM64) then shl64 a_lo (Z.land n 63)
              else Z.lor (shl64 sigHi1 (Z.land negsh 63)) (shr64 (shr64 a_lo 1) (Z.land (not64 n) 63)) in
  to_d_subB a_lo sigHi1 shift shNZ slLo slHi.

Definition to_d_range (a_lo sigHi srcExp : Z) : Z * Z :=
  if negb (srcExp <=? 0x43fe) then (2047, 0)
  else
    let expZ := eqz64 srcExp in
    let k := Z.lxor expZ 0x3c01 in
    let shift := sub64 k srcExp in
    if lt_s64 112 shift then (0, 0)
    else to_d_subA a_lo sigHi srcExp k shift.

Definition to_d_core (a_lo a_hi : Z) : Z * Z :=
  let srcExp := shr64 (shl64 a_hi 1) 49 in
  let sigHi := shr64 (shl64 a_hi 16) 16 in
  let candM1 := add64 srcExp 0xffffffffffffc3ff in
  if negb (2045 <? candM1) then to_d_normal a_lo sigHi candM1
  else
    let isNaN := if Z.lor a_lo sigHi =? 0 then false else negb (negb (srcExp =? 0x7fff)) in
    if isNaN then (2047, Z.lor (Z.lor (shr64 a_lo 60) DQUIET) (shl64 sigHi 4))
    else to_d_range a_lo sigHi srcExp.

Lemma lo64_words : forall lo hi, (0 <= lo < 2^64)%Z -> lo64 (lo + 2^64 * hi) = lo.
Proof.
  intros lo hi H. unfold lo64. rewrite wrap64_mod.
  rewrite Z.mul_comm, Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma hi64_words : forall lo hi, (0 <= lo < 2^64)%Z -> (0 <= hi < 2^64)%Z -> hi64 (lo + 2^64 * hi) = hi.
Proof.
  intros lo hi Hl Hh. unfold hi64. rewrite wrap64_mod, Z.shiftr_div_pow2 by lia.
  rewrite Z.mul_comm, Z.div_add, Z.div_small by lia. apply Z.mod_small. lia.
Qed.

Lemma f128_to_d_split : forall a_lo a_hi, (0 <= a_lo < 2^64)%Z -> (0 <= a_hi < 2^64)%Z ->
  f128_to_d (a_lo + 2^64 * a_hi) = (let '(dE, dS) := to_d_core a_lo a_hi in to_d_pack dE dS a_hi).
Proof. intros. unfold f128_to_d. rewrite lo64_words, hi64_words by lia. reflexivity. Qed.

Definition to_d_pack_g (dE dS sgn : Z) : Z := Z.lor (shl64 dE 52) (Z.lor dS sgn).

Lemma f128_to_d_split_g : forall a_lo a_hi, (0 <= a_lo < 2^64)%Z -> (0 <= a_hi < 2^64)%Z ->
  f128_to_d (a_lo + 2^64 * a_hi) =
  (let '(dE, dS) := to_d_core a_lo a_hi in to_d_pack_g dE dS (Z.land a_hi 9223372036854775808)).
Proof.
  intros a_lo a_hi Hl Hh. rewrite f128_to_d_split by assumption.
  destruct (to_d_core a_lo a_hi) as [dE dS]. unfold to_d_pack, to_d_pack_g.
  unfold shl64 at 2. rewrite wrap64_mod. change (2^64) with 18446744073709551616.
  rewrite <- land_W64, signbit63 by (change (2^64) with 18446744073709551616 in Hh; lia).
  rewrite (Z.land_comm 9223372036854775808 a_hi).
  apply Z.bits_inj'. intros i Hi. rewrite !Z.lor_spec.
  destruct (Z.testbit (shl64 dE 52) i), (Z.testbit dS i), (Z.testbit (Z.land a_hi 9223372036854775808) i); reflexivity.
Qed.

Lemma round_even_g : forall x, 0 <= x ->
  Z_to_bv 64 (Z.land (Z.land (x + 1) 18446744073709551615) 18446744073709551614) =
  Z_to_bv 64 (Z.land (Z.land x 1 + x) 18446744073709551615).
Proof.
  intros x Hx. apply Z_to_bv_eqm. rewrite land_even_mask, !land_W64, !land_1.
  change (2^64) with 18446744073709551616.
  rewrite (Z.mod_mod_divide (x + 1) 18446744073709551616 2) by (exists 9223372036854775808; reflexivity).
  Z.div_mod_to_equations. lia.
Qed.

Lemma to_d_shift_facts : forall srcExp, 0 <= srcExp <= 15360 ->
  Z.lxor (Z.land (Z.lxor (Z.b2z (srcExp =? 0)) 15361 - srcExp) 18446744073709551615) 9223372036854775808
    <= 9223372036854775920 ->
  Z.b2z (srcExp =? 0) = 0 /\ Z.land (Z.lxor (Z.b2z (srcExp =? 0)) 15361 - srcExp) 18446744073709551615 = 15361 - srcExp
  /\ 1 <= 15361 - srcExp <= 112.
Proof.
  intros srcExp Hs. destruct (Z.eqb_spec srcExp 0) as [E|E].
  - subst srcExp. intros K. exfalso. apply K. vm_compute. reflexivity.
  - cbn [Z.b2z]. change (Z.lxor 0 15361) with 15361.
    rewrite land_W64_small by lia. change 9223372036854775808 with (2^63). rewrite zb_lxor_pow2 by lia.
    rewrite (Z.div_small (15361 - srcExp)) by lia. change (2^63) with 9223372036854775808. change (0 mod 2) with 0. lia.
Qed.

Lemma lxor1_b2z : forall b, Z.lxor (Z.b2z b) 1 = Z.b2z (negb b).
Proof. intros [|]; reflexivity. Qed.

Lemma landM32_swrap_land64 : forall x,
  Z.land (Z.land (bv_swrap 32 x) 18446744073709551615) 4294967295 = Z.land (Z.land x 18446744073709551615) 4294967295.
Proof.
  intros x. rewrite land_swrap32_sext32. change 4294967295 with (2^32 - 1). rewrite !zb_land_mask, land_W64 by lia.
  change (2^32) with 4294967296. rewrite sext32_low. change (2^64) with 18446744073709551616.
  rewrite Z.mod_mod_divide by (exists 4294967296; reflexivity). reflexivity.
Qed.

Lemma shl13_shr16 : forall x, 0 <= x < 18446744073709551616 ->
  Z.shiftr (Z.land (Z.shiftl x 13) 18446744073709551615) 16 = Z.land (Z.shiftr x 3) 281474976710655.
Proof.
  intros x Hx. rewrite land_W64, Z.shiftl_mul_pow2, !Z.shiftr_div_pow2 by lia.
  change 281474976710655 with (2^48 - 1). rewrite zb_land_mask by lia.
  change (2^64) with (2251799813685248 * 8192). change (2^13) with 8192. change (2^16) with (8192 * 8).
  change (2^3) with 8. change (2^48) with 281474976710656.
  rewrite Z.mul_mod_distr_r by lia.
  rewrite <- Z.div_div, Z.div_mul by lia.
  Z.div_mod_to_equations. lia.
Qed.

Lemma lor_rot_bsa : forall b s a, Z.lor (Z.lor b s) a = Z.lor (Z.lor a s) b.
Proof.
  intros. apply Z.bits_inj'. intros i Hi. rewrite !Z.lor_spec.
  destruct (Z.testbit b i), (Z.testbit s i), (Z.testbit a i); reflexivity.
Qed.

Lemma b2z_ltb1 : forall b, (Z.b2z b <? 1) = negb b.
Proof. intros [|]; reflexivity. Qed.

Lemma signbit63' : forall x, 0 <= x < 18446744073709551616 ->
  Z.land (Z.shiftl (Z.shiftr x 63) 63) 18446744073709551615 = Z.land x 9223372036854775808.
Proof. intros. rewrite signbit63 by assumption. apply Z.land_comm. Qed.
