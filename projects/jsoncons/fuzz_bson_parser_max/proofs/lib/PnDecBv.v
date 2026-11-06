(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia Bool.
From stdpp Require Import base.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec PnDecFacts.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNDBV.

(* [comment removed for export] *)
Lemma land_ones14 x : Z.land x 16383 = x mod 2 ^ 14.
Proof. change 16383 with (Z.ones 14). apply Z.land_ones. lia. Qed.
Lemma mod32_lor a b : 0 <= a -> 0 <= b -> (Z.lor a b) mod 2 ^ 32 = Z.lor (a mod 2 ^ 32) (b mod 2 ^ 32).
Proof. intros Ha Hb. rewrite <- !Z.land_ones by lia. apply Z.land_lor_distr_l. Qed.
Lemma lor_zero_iff a b : Z.lor a b = 0 <-> a = 0 /\ b = 0.
Proof. apply Z.lor_eq_0_iff. Qed.

(* [comment removed for export] *)
Lemma hi_fields hi : 0 <= hi < 2 ^ 64 ->
  exists a b c d, hi = 2 ^ 49 * a + 2 ^ 46 * b + 2 ^ 32 * c + d /\ 0 <= a < 2 ^ 15 /\ 0 <= b < 8 /\ 0 <= c < 2 ^ 14 /\ 0 <= d < 2 ^ 32.
Proof.
  intros H. exists (hi / 2 ^ 49), ((hi / 2 ^ 46) mod 8), ((hi / 2 ^ 32) mod 2 ^ 14), (hi mod 2 ^ 32).
  pose proof (Z.div_mod hi (2 ^ 32) ltac:(lia)). pose proof (Z.mod_pos_bound hi (2 ^ 32) ltac:(lia)).
  pose proof (Z.div_mod (hi / 2 ^ 32) (2 ^ 14) ltac:(lia)). pose proof (Z.mod_pos_bound (hi / 2 ^ 32) (2 ^ 14) ltac:(lia)).
  pose proof (Z.div_mod (hi / 2 ^ 46) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (hi / 2 ^ 46) 8 ltac:(lia)).
  rewrite (Z.div_div hi (2 ^ 32) (2 ^ 14)) in * by lia. change (2 ^ 32 * 2 ^ 14) with (2 ^ 46) in *.
  rewrite (Z.div_div hi (2 ^ 46) 8) in * by lia. change (2 ^ 46 * 8) with (2 ^ 49) in *.
  assert (0 <= hi / 2 ^ 49 < 2 ^ 15).
  { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. change (2 ^ 49 * 2 ^ 15) with (2 ^ 64). lia. }
  lia.
Qed.

Section Fields.
Variables (hi a b c d : Z).
Hypothesis E : hi = 2 ^ 49 * a + 2 ^ 46 * b + 2 ^ 32 * c + d.
Hypothesis Ha : 0 <= a < 2 ^ 15. Hypothesis Hb : 0 <= b < 8. Hypothesis Hc : 0 <= c < 2 ^ 14. Hypothesis Hd : 0 <= d < 2 ^ 32.

Lemma f_hi32 : hi / 4294967296 = 2 ^ 17 * a + 2 ^ 14 * b + c.
Proof. symmetry. apply (Z.div_unique_pos hi 4294967296 _ d); lia. Qed.
Lemma f_msb : (32768 * hi) mod 2 ^ 64 / 2305843009213693952 = b.
Proof.
  assert (M : (32768 * hi) mod 2 ^ 64 = 2 ^ 61 * b + 2 ^ 47 * c + 2 ^ 15 * d).
  { symmetry. apply (Z.mod_unique_pos (32768 * hi) (2 ^ 64) a); lia. }
  rewrite M. symmetry. apply (Z.div_unique_pos _ 2305843009213693952 b (2 ^ 47 * c + 2 ^ 15 * d)); lia.
Qed.
Lemma f_low14 : Z.land (hi / 4294967296) 16383 = c.
Proof. rewrite land_ones14, f_hi32. symmetry. apply (Z.mod_unique_pos _ (2 ^ 14) (8 * a + b)); lia. Qed.
Lemma f_parts0 : ((16384 * ((32768 * hi) mod 2 ^ 64 / 2305843009213693952)) mod 2 ^ 64 + Z.land (hi / 4294967296) 16383) mod 2 ^ 64 = 2 ^ 14 * b + c.
Proof. rewrite f_msb, f_low14. rewrite (Z.mod_small (16384 * b)) by lia. apply Z.mod_small. lia. Qed.
Lemma f_p0 lo : 0 <= lo < 2 ^ 64 -> (hi mod 2 ^ 49 * 2 ^ 64 + lo) / 2 ^ 96 = 2 ^ 14 * b + c.
Proof.
  intros Hlo. assert (M : hi mod 2 ^ 49 = 2 ^ 46 * b + 2 ^ 32 * c + d) by (symmetry; apply (Z.mod_unique_pos hi (2 ^ 49) a); lia).
  rewrite M. symmetry. apply (Z.div_unique_pos _ (2 ^ 96) _ (d * 2 ^ 64 + lo)); lia.
Qed.
Lemma f_mod49 : hi mod 2 ^ 49 = 2 ^ 46 * b + 2 ^ 32 * c + d.
Proof. symmetry; apply (Z.mod_unique_pos hi (2 ^ 49) a); lia. Qed.
Lemma f_mod32 : hi mod 2 ^ 32 = d.
Proof. symmetry; apply (Z.mod_unique_pos hi (2 ^ 32) (2 ^ 17 * a + 2 ^ 14 * b + c)); lia. Qed.
Lemma f_e : 0 <= Z.land (hi / 4294967296 / 131072) 16383 <= 16383.
Proof. rewrite land_ones14. pose proof (Z.mod_pos_bound (hi / 4294967296 / 131072) (2 ^ 14) ltac:(lia)). lia. Qed.
End Fields.

(* [comment removed for export] *)
Lemma rot_lo lo : 0 <= lo < 2 ^ 64 ->
  Z.lor ((4294967296 * lo) mod 2 ^ 64) (lo / 4294967296) = (lo / 2 ^ 32) mod 2 ^ 32 + 4294967296 * (lo mod 2 ^ 32).
Proof.
  intros H. pose proof (Z.div_mod lo (2 ^ 32) ltac:(lia)) as E. pose proof (Z.mod_pos_bound lo (2 ^ 32) ltac:(lia)) as B.
  assert (Q : 0 <= lo / 2 ^ 32 < 2 ^ 32). { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. change (2 ^ 32 * 2 ^ 32) with (2 ^ 64); lia. }
  assert (M : (4294967296 * lo) mod 2 ^ 64 = 4294967296 * (lo mod 2 ^ 32)).
  { symmetry. apply (Z.mod_unique_pos _ (2 ^ 64) (lo / 2 ^ 32)); lia. }
  rewrite M. change 4294967296 with (2 ^ 32) at 3. rewrite (Z.mod_small (lo / 2 ^ 32)) by lia.
  rewrite PNDF.lor_hi_lo by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma bvu_if (c : bool) : bv_unsigned (if c then Z_to_bv 64 1 else Z_to_bv 64 0) = (if c then 1 else 0).
Proof. destruct c; reflexivity. Qed.
Lemma bv_sub_0 (x : bv 64) : (x - Z_to_bv 64 0)%bv = x.
Proof. apply bv_eq. rewrite bv_sub_unsigned. rewrite Z_to_bv_unsigned. change (bv_wrap 64 0) with 0. rewrite Z.sub_0_r. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.
Lemma ltu1 (x : bv 64) : bv_ltu x (Z_to_bv 64 1) = (bv_unsigned x =? 0).
Proof.
  unfold bv_ltu. rewrite Z_to_bv_unsigned. change (bv_wrap 64 1) with 1. pose proof (bv_unsigned_in_range _ x).
  destruct (Z.ltb_spec (bv_unsigned x) 1), (Z.eqb_spec (bv_unsigned x) 0); try reflexivity; lia.
Qed.
(* [comment removed for export] *)
Lemma sextw_zero (X : bv 64) : (bv_unsigned (sext 64 (low32 X + low32 (Z_to_bv 64 0))) =? 0) = (bv_unsigned X mod 2 ^ 32 =? 0).
Proof.
  rewrite sext32_unsigned. rewrite bv_add_unsigned, !low32_unsigned, Z_to_bv_unsigned.
  change (bv_wrap 64 0) with 0. change (bv_wrap 32 0) with 0. rewrite Z.add_0_r, bv_wrap_bv_wrap by lia.
  unfold bv_wrap, bv_swrap. change (bv_modulus 32) with (2 ^ 32). change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 64) with (2 ^ 64).
  unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32).
  set (y := bv_unsigned X mod 2 ^ 32). pose proof (Z.mod_pos_bound (bv_unsigned X) (2 ^ 32) ltac:(lia)) as B. fold y in B.
  destruct (Z.eqb_spec y 0) as [E|NE].
  - rewrite E. reflexivity.
  - apply Z.eqb_neq. intros Z0.
    destruct (Z_lt_le_dec y (2 ^ 31)) as [LT|GE].
    + rewrite (Z.mod_small (y + 2 ^ 31)) in Z0 by lia. replace (y + 2 ^ 31 - 2 ^ 31) with y in Z0 by lia. rewrite Z.mod_small in Z0 by lia. lia.
    + replace ((y + 2 ^ 31) mod 2 ^ 32) with (y + 2 ^ 31 - 2 ^ 32) in Z0.
      2:{ apply (Z.mod_unique_pos _ _ 1); lia. }
      replace (y + 2 ^ 31 - 2 ^ 32 - 2 ^ 31) with (y - 2 ^ 32) in Z0 by lia.
      replace ((y - 2 ^ 32) mod 2 ^ 64) with (y - 2 ^ 32 + 2 ^ 64) in Z0; [lia|]. apply (Z.mod_unique_pos _ _ (-1)); lia.
Qed.

(* [comment removed for export] *)
Lemma u_lit z : 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros H. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia. Qed.
Ltac bvz := repeat first [ rewrite bv_add_unsigned | rewrite bv_mul_unsigned | rewrite bv_shiftr_unsigned | rewrite bv_and_unsigned | rewrite bv_or_unsigned ];
  rewrite ?u_lit by lia; change (Z.land 61 63) with 61; change (Z.land 32 63) with 32; rewrite ?Z.shiftr_div_pow2 by lia;
  unfold bv_wrap; change (bv_modulus 64) with (2 ^ 64).

Section Test.
Variables (hi lo : Z).
Hypothesis Fhi : 0 <= hi < 2 ^ 64.
Hypothesis Flo : 0 <= lo < 2 ^ 64.
Let H : bv 64 := Z_to_bv 64 hi.
Let L : bv 64 := Z_to_bv 64 lo.
Definition Xbv : bv 64 :=
  bv_or (Z_to_bv 64 16384 * ((Z_to_bv 64 32768 * H) ≫ bv_and (Z_to_bv 64 61) (Z_to_bv 64 63)) + bv_and (H ≫ bv_and (Z_to_bv 64 32) (Z_to_bv 64 63)) (Z_to_bv 64 16383))
        (bv_or (bv_or H (L ≫ bv_and (Z_to_bv 64 32) (Z_to_bv 64 63))) L).
Definition parts0 : Z := ((16384 * ((32768 * hi) mod 2 ^ 64 / 2305843009213693952)) mod 2 ^ 64 + Z.land (hi / 4294967296) 16383) mod 2 ^ 64.

Lemma parts0_bv : bv_unsigned (Z_to_bv 64 16384 * ((Z_to_bv 64 32768 * H) ≫ bv_and (Z_to_bv 64 61) (Z_to_bv 64 63)) + bv_and (H ≫ bv_and (Z_to_bv 64 32) (Z_to_bv 64 63)) (Z_to_bv 64 16383))%bv = parts0.
Proof.
  unfold parts0. subst H L. bvz. change (2 ^ 61) with 2305843009213693952. change (2 ^ 32) with 4294967296. reflexivity.
Qed.
Lemma X_val : bv_unsigned Xbv = Z.lor parts0 (Z.lor (Z.lor hi (lo / 2 ^ 32)) lo).
Proof.
  unfold Xbv. rewrite bv_or_unsigned, parts0_bv. subst H L. bvz. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma zero_test : (bv_unsigned Xbv mod 2 ^ 32 =? 0) = ((hi mod 2 ^ 49) * 2 ^ 64 + lo =? 0).
Proof.
  destruct (hi_fields hi Fhi) as (a & b & c & d & E & Ha & Hb & Hc & Hd).
  rewrite X_val. unfold parts0. rewrite (f_parts0 hi a b c d E Ha Hb Hc Hd), (f_mod49 hi a b c d E Ha Hb Hc Hd).
  pose proof (Z.div_mod lo (2 ^ 32) ltac:(lia)) as EL. pose proof (Z.mod_pos_bound lo (2 ^ 32) ltac:(lia)) as BL.
  assert (QL : 0 <= lo / 2 ^ 32 < 2 ^ 32). { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. change (2 ^ 32 * 2 ^ 32) with (2 ^ 64); lia. }
  assert (NN : forall x y, 0 <= x -> 0 <= y -> 0 <= Z.lor x y) by (intros x y Hx Hy; apply Z.lor_nonneg; split; assumption).
  rewrite (mod32_lor (2 ^ 14 * b + c)); [| clear -Hb Hc; lia| apply NN; [apply NN|]; clear -Fhi Flo QL; lia].
  rewrite (mod32_lor (Z.lor hi (lo / 2 ^ 32)) lo); [| apply NN; clear -Fhi Flo QL; lia| clear -Flo; lia].
  rewrite (mod32_lor hi (lo / 2 ^ 32)); [| clear -Fhi; lia| clear -QL; lia].
  rewrite (Z.mod_small (2 ^ 14 * b + c)) by (clear -Hb Hc; lia). rewrite (f_mod32 hi a b c d E Ha Hb Hc Hd). rewrite (Z.mod_small (lo / 2 ^ 32)) by (clear -QL; lia).
  destruct (Z.eqb_spec (Z.lor (2 ^ 14 * b + c) (Z.lor (Z.lor d (lo / 2 ^ 32)) (lo mod 2 ^ 32))) 0) as [Z0|NZ];
  destruct (Z.eqb_spec ((2 ^ 46 * b + 2 ^ 32 * c + d) * 2 ^ 64 + lo) 0) as [W0|WN]; try reflexivity; exfalso.
  - rewrite !lor_zero_iff in Z0. lia.
  - apply NZ. rewrite !lor_zero_iff. lia.
Qed.
End Test.
End PNDBV.
