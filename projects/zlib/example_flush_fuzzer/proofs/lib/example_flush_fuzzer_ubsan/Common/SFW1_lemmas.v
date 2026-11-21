(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Common Require Export SFModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
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



Lemma zext32_eq : forall z, zext32 z = z mod 4294967296.
Proof. intros z. unfold zext32, M32. change 4294967295 with (2^32 - 1). rewrite zb_land_mask by lia. reflexivity. Qed.

Lemma zext32_small : forall z, 0 <= z < 4294967296 -> zext32 z = z.
Proof. intros z Hz. rewrite zext32_eq. apply Z.mod_small. lia. Qed.


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


Ltac name_as_by_tac X e tac :=
  set (X := e) in *;
  let RX := fresh "R" X in
  assert (RX : 0 <= X < 18446744073709551616) by (subst X; tac).
Tactic Notation "name_as_by" ident(X) constr(e) tactic3(tac) := name_as_by_tac X e tac.












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



Ltac reg_rewrite n lem :=
  let w := getreg n in
  lazymatch w with
  | Z_to_bv 64 ?e =>
      let e' := fresh "e" in let E := fresh "E" in
      remember e as e' eqn:E in |- *;
      rewrite lem in E; subst e'
  end.















Lemma lxor1_b2z : forall b, Z.lxor (Z.b2z b) 1 = Z.b2z (negb b).
Proof. intros [|]; reflexivity. Qed.






