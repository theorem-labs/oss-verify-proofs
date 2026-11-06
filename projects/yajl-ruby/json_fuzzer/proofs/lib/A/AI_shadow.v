(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA AImages.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition al8 (x : Z) : Z := x - x mod 8.

Lemma al8_le : forall x, al8 x <= x.
Proof. intros x. unfold al8. pose proof (Z.mod_pos_bound x 8). lia. Qed.
Lemma al8_gt : forall x, x - 8 < al8 x.
Proof. intros x. unfold al8. pose proof (Z.mod_pos_bound x 8). lia. Qed.
Lemma al8_mod : forall x, al8 x mod 8 = 0.
Proof. intros x. unfold al8. rewrite Zminus_mod, Z.mod_mod by lia. rewrite Z.sub_diag. reflexivity. Qed.
Lemma al8_mono : forall x y, x <= y -> al8 x <= al8 y.
Proof. intros x y H. unfold al8. Z.div_mod_to_equations. nia. Qed.
Lemma al8_id : forall x, x mod 8 = 0 -> al8 x = x.
Proof. intros x H. unfold al8. lia. Qed.

(* [comment removed for export] *)
Lemma not64 : forall a, 0 <= a < 2^64 -> Z.lxor a 18446744073709551615 = 18446744073709551615 - a.
Proof.
  intros a H. rewrite lnot_mod64 by lia. unfold Z.lnot. rewrite <- Z.sub_1_r.
  replace (- a - 1) with ((18446744073709551615 - a) + (-1) * 2^64) by lia.
  rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)
Lemma mod64_neg_small : forall x, - 2^64 <= x < 0 -> x mod 18446744073709551616 = x + 18446744073709551616.
Proof.
  intros x H. change 18446744073709551616 with (2^64).
  replace x with ((x + 2^64) + (-1) * 2^64) at 1 by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)
Lemma land_m8 : forall x, 0 <= x < 2^64 ->
  Z.land (x mod 18446744073709551616) 18446744073709551608 = al8 x.
Proof.
  intros x H. rewrite Z.mod_small by (change 18446744073709551616 with (2^64); lia).
  change 18446744073709551608 with (Z.land 18446744073709551615 (-8)).
  rewrite Z.land_assoc. change 18446744073709551615 with (Z.ones 64).
  rewrite Z.land_ones, Z.mod_small by lia.
  change (Z.land x (-8)) with (Z.ldiff x (Z.ones 3)).
  rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  unfold al8. change (2^3) with 8. Z.div_mod_to_equations. lia.
Qed.

Lemma land_m8' : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551608 = al8 x.
Proof. intros x H. rewrite <- (Z.mod_small x 18446744073709551616) at 1 by (change 18446744073709551616 with (2^64); lia). apply land_m8. exact H. Qed.

(* [comment removed for export] *)
Lemma shr3_bounds : forall a, 0 <= a -> 0 <= Z.shiftr a 3 /\ 8 * Z.shiftr a 3 <= a < 8 * Z.shiftr a 3 + 8.
Proof. intros a H. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia. Qed.
Lemma shr3_mod : forall a, 0 <= a -> a mod 8 = a - 8 * Z.shiftr a 3.
Proof. intros a H. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia. Qed.
Lemma land7_mod : forall a, Z.land a 7 = a mod 8.
Proof. intros a. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

(* [comment removed for export] *)
Definition aip_expr (z r : Z) : Z :=
  Z.land (Z.b2z (0 <? z)) (Z.lxor (Z.b2z (Z.lxor r 9223372036854775808 <? Z.lxor z 9223372036854775808)) 1).

Lemma aip_core : forall z r, 0 <= z < 128 -> 0 <= r < 8 -> (z = 0 \/ r < z) -> aip_expr z r = 0.
Proof.
  intros z r Hz Hr H.
  pose proof (forallb_zseq 1024 (fun c => implb (orb (c / 8 =? 0) (c mod 8 <? c / 8)) (aip_expr (c / 8) (c mod 8) =? 0))
                ltac:(vm_compute; reflexivity) (z * 8 + r) ltac:(cbn; lia)) as E.
  cbv beta in E.
  replace ((z * 8 + r) / 8) with z in E by (Z.div_mod_to_equations; lia).
  replace ((z * 8 + r) mod 8) with r in E by (Z.div_mod_to_equations; lia).
  destruct (orb _ _) eqn:O.
  - cbn in E. apply Z.eqb_eq. exact E.
  - exfalso. apply orb_false_iff in O. destruct O as [O1 O2]. apply Z.eqb_neq in O1. apply Z.ltb_ge in O2. lia.
Qed.

Lemma sxb_unsigned_nonneg : forall k : byte, 0 <= bv_signed k -> bv_unsigned (sxb k) = bv_signed k.
Proof.
  intros k H. unfold sxb. pose proof (bv_signed_in_range 8 k ltac:(discriminate)) as R.
  unfold bv_half_modulus, bv_modulus in R. cbn in R. apply unsigned_lit. lia.
Qed.

Lemma signed_small64 : forall z, - 2^63 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof. intros z H. rewrite Z_to_bv_signed. apply bv_swrap_small. unfold bv_half_modulus, bv_modulus. cbn. lia. Qed.

Lemma sxb_signed : forall k : byte, bv_signed (sxb k) = bv_signed k.
Proof.
  intros k. unfold sxb. pose proof (bv_signed_in_range 8 k ltac:(discriminate)) as R.
  unfold bv_half_modulus, bv_modulus in R. cbn in R. apply signed_small64. lia.
Qed.

Lemma sxb_zero_iff : forall k : byte, bv_eqb (sxb k) (Z_to_bv 64 0) = true <-> bv_signed k = 0.
Proof.
  intros k. unfold bv_eqb. rewrite Z.eqb_eq. pose proof (bv_signed_in_range 8 k ltac:(discriminate)) as R.
  unfold bv_half_modulus, bv_modulus in R. cbn in R. unfold sxb. rewrite Z_to_bv_unsigned.
  change (bv_unsigned (Z_to_bv 64 0)) with 0. unfold bv_wrap, bv_modulus. cbn -[Z.modulo Z.pow].
  change (2^64)%Z with 18446744073709551616. split; intros H; Z.div_mod_to_equations; lia.
Qed.

(* [comment removed for export] *)
Lemma aip_last_clean : forall (k : byte) last,
  0 <= last -> (bv_signed k = 0 \/ last mod 8 < bv_signed k) ->
  aip_expr (bv_unsigned (sxb k)) (Z.land last 7) = 0.
Proof.
  intros k last Hl K. pose proof (bv_signed_in_range 8 k ltac:(discriminate)) as R.
  unfold bv_half_modulus, bv_modulus in R. cbn in R.
  rewrite sxb_unsigned_nonneg by lia. rewrite land7_mod. pose proof (Z.mod_pos_bound last 8).
  apply aip_core; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition shw_lo (SB A : Z) : Z := al8 (SB + Z.shiftr A 3).
Definition shw_hi (SB A n : Z) : Z := al8 (SB + Z.shiftr (A + n + -1) 3) + 8.

Section WithSegs.
Variable segs : list MemImageType.Segment.

Definition shadow_window (m : mem) (SB A n : Z) (ws : list byte) : Prop :=
  bytes_at segs m (shw_lo SB A) ws /\ Z.of_nat (length ws) = shw_hi SB A n - shw_lo SB A.

End WithSegs.

(* [comment removed for export] *)
Definition granule_ok (SB A n : Z) (ws : list byte) (g : Z) : Prop :=
  exists k, nth_error ws (Z.to_nat (SB + g - shw_lo SB A)) = Some k /\
            (bv_signed k = 0 \/ (g = Z.shiftr (A + n + -1) 3 /\ (A + n + -1) mod 8 < bv_signed k < 8)).

Definition range_clean (SB A n : Z) (ws : list byte) : Prop :=
  forall g, Z.shiftr A 3 <= g <= Z.shiftr (A + n + -1) 3 -> granule_ok SB A n ws g.

(* [comment removed for export] *)
Lemma shw_geom : forall SB A n, 0 <= SB -> 0 <= A -> 1 <= n ->
  let g1 := Z.shiftr A 3 in let g2 := Z.shiftr (A + n + -1) 3 in
  0 <= g1 /\ g1 <= g2 /\ 8 * g1 <= A < 8 * g1 + 8 /\ 8 * g2 <= A + n + -1 < 8 * g2 + 8 /\
  shw_lo SB A <= SB + g1 /\ SB + g1 < shw_lo SB A + 8 /\ shw_lo SB A mod 8 = 0 /\
  shw_hi SB A n - 8 <= SB + g2 /\ SB + g2 < shw_hi SB A n /\ shw_hi SB A n mod 8 = 0 /\
  shw_lo SB A + 8 <= shw_hi SB A n.
Proof.
  intros SB A n HSB HA Hn. cbv zeta.
  pose proof (shr3_bounds A HA). pose proof (shr3_bounds (A + n + -1) ltac:(lia)).
  assert (Z.shiftr A 3 <= Z.shiftr (A + n + -1) 3) by (rewrite !Z.shiftr_div_pow2 by lia; apply Z.div_le_mono; lia).
  unfold shw_lo, shw_hi.
  pose proof (al8_le (SB + Z.shiftr A 3)). pose proof (al8_gt (SB + Z.shiftr A 3)). pose proof (al8_mod (SB + Z.shiftr A 3)).
  pose proof (al8_le (SB + Z.shiftr (A + n + -1) 3)). pose proof (al8_gt (SB + Z.shiftr (A + n + -1) 3)).
  pose proof (al8_mod (SB + Z.shiftr (A + n + -1) 3)).
  pose proof (al8_mono (SB + Z.shiftr A 3) (SB + Z.shiftr (A + n + -1) 3) ltac:(lia)).
  repeat split; try lia.
  all: Z.div_mod_to_equations; lia.
Qed.

(* [comment removed for export] *)
Lemma shw_small : forall SB A n, 0 <= SB -> 0 <= A -> 1 <= n <= 64 ->
  shw_hi SB A n <= shw_lo SB A + 16 + 8 * 8.
Proof.
  intros SB A n HSB HA Hn. unfold shw_lo, shw_hi.
  pose proof (shr3_bounds A HA). pose proof (shr3_bounds (A + n + -1) ltac:(lia)).
  pose proof (al8_le (SB + Z.shiftr A 3)). pose proof (al8_gt (SB + Z.shiftr A 3)).
  pose proof (al8_le (SB + Z.shiftr (A + n + -1) 3)). pose proof (al8_gt (SB + Z.shiftr (A + n + -1) 3)).
  lia.
Qed.

(* [comment removed for export] *)
Lemma range_clean_byte : forall SB A n ws g,
  range_clean SB A n ws -> Z.shiftr A 3 <= g <= Z.shiftr (A + n + -1) 3 ->
  exists k, nth_error ws (Z.to_nat (SB + g - shw_lo SB A)) = Some k /\
            (bv_signed k = 0 \/ (g = Z.shiftr (A + n + -1) 3 /\ (A + n + -1) mod 8 < bv_signed k < 8)).
Proof. intros SB A n ws g RC Hg. exact (RC g Hg). Qed.

(* [comment removed for export] *)
Lemma byte_signed0_unsigned0 : forall k : byte, bv_signed k = 0 -> bv_unsigned k = 0.
Proof.
  intros k K. pose proof (bv_unsigned_in_range 8 k) as U.
  unfold bv_signed, bv_swrap, bv_wrap, bv_modulus, bv_half_modulus in *. cbn -[Z.modulo Z.add Z.sub] in K.
  cbn in U. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma range_clean_full : forall SB A n ws g,
  range_clean SB A n ws -> 0 <= A -> 1 <= n -> Z.shiftr A 3 <= g -> 8 * g + 8 <= A + n ->
  nth_error ws (Z.to_nat (SB + g - shw_lo SB A)) = Some (Z_to_bv 8 0).
Proof.
  intros SB A n ws g RC HA Hn Hg1 Hg2.
  pose proof (shr3_bounds (A + n + -1) ltac:(lia)) as B2.
  assert (g <= Z.shiftr (A + n + -1) 3) by lia.
  destruct (RC g ltac:(lia)) as (k & Hk & [K|[K1 K2]]).
  - rewrite Hk. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. cbn. apply byte_signed0_unsigned0. exact K.
  - exfalso. rewrite (shr3_mod (A + n + -1)) in K2 by lia. subst g. lia.
Qed.

Lemma range_clean_inner : forall SB A n ws g,
  range_clean SB A n ws -> Z.shiftr A 3 <= g < Z.shiftr (A + n + -1) 3 ->
  nth_error ws (Z.to_nat (SB + g - shw_lo SB A)) = Some (Z_to_bv 8 0).
Proof.
  intros SB A n ws g RC Hg. destruct (RC g ltac:(lia)) as (k & Hk & [K|[K _]]); [|lia].
  rewrite Hk. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned.
  pose proof (bv_unsigned_in_range 8 k) as U.
  unfold bv_signed, bv_swrap, bv_wrap, bv_modulus, bv_half_modulus in *. cbn -[Z.modulo Z.add Z.sub] in K.
  cbn in U. cbn. Z.div_mod_to_equations. lia.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition A_GOT_SBPTR   : Z := 0xa49b0.  (* [comment removed for export] *)
Definition A_SBVAR       : Z := 0xadb78.  (* [comment removed for export] *)
Definition A_GOT_MIDBEG  : Z := 0xa49b8.  (* [comment removed for export] *)
Definition A_MIDBEG      : Z := 0xae868.  (* [comment removed for export] *)
Definition A_GOT_MIDEND  : Z := 0xa49c0.  (* [comment removed for export] *)
Definition A_MIDEND      : Z := 0xae870.  (* [comment removed for export] *)
Definition A_GOT_HIGHEND : Z := 0xa49c8.  (* [comment removed for export] *)
Definition A_HIGHEND     : Z := 0xae860.  (* [comment removed for export] *)
Definition A_GOT_RIC     : Z := 0xa5518.  (* [comment removed for export] *)
Definition A_RIC         : Z := 0xae859.  (* [comment removed for export] *)
Definition A_INITED      : Z := 0xae858.  (* [comment removed for export] *)
Definition A_REAL_MEMCPY : Z := 0xa6820.  (* [comment removed for export] *)
Definition A_REAL_MEMSET : Z := 0xa6828.  (* [comment removed for export] *)
Definition A_MUSL_MEMCPY : Z := 0x9dcdc.
Definition A_MUSL_MEMSET : Z := 0x9e0e0.
Definition A_HIGHEND_VAL : Z := 0x7fffffffffff.

Lemma disjoint_from_sub : forall W lo n A k,
  disjoint_from W lo n -> lo <= A -> A + k <= lo + n -> disjoint_from W A k.
Proof.
  induction W as [|[l h] W IH]; cbn; intros lo n A k D H1 H2; [exact I|].
  destruct D as [D1 D2]. split; [lia| eapply IH; eauto].
Qed.

Section Globals.
Variable segs : list MemImageType.Segment.

(* [comment removed for export] *)
Definition icp_globals (m : mem) (SB : Z) : Prop :=
     rw_cells segs m A_GOT_SBPTR [C8 (Z_to_bv 64 A_SBVAR)]
  /\ rw_cells segs m A_SBVAR [C8 (Z_to_bv 64 SB)]
  /\ rw_cells segs m A_GOT_RIC [C8 (Z_to_bv 64 A_RIC)]
  /\ rw_cells segs m A_RIC [C1 (Z_to_bv 8 1)]
  /\ rw_cells segs m A_REAL_MEMCPY [C8 (Z_to_bv 64 A_MUSL_MEMCPY)]
  /\ rw_cells segs m A_REAL_MEMSET [C8 (Z_to_bv 64 A_MUSL_MEMSET)]
  /\ rw_cells segs m A_GOT_MIDBEG [C8 (Z_to_bv 64 A_MIDBEG)]
  /\ rw_cells segs m A_MIDBEG [C8 (Z_to_bv 64 0)]
  /\ rw_cells segs m A_GOT_MIDEND [C8 (Z_to_bv 64 A_MIDEND)]
  /\ rw_cells segs m A_MIDEND [C8 (Z_to_bv 64 0)]
  /\ rw_cells segs m A_GOT_HIGHEND [C8 (Z_to_bv 64 A_HIGHEND)]
  /\ rw_cells segs m A_HIGHEND [C8 (Z_to_bv 64 A_HIGHEND_VAL)]
  /\ rw_cells segs m A_INITED [C1 (Z_to_bv 8 1)]
  /\ 2^24 <= SB < 2^32.

Lemma icp_globals_transport : forall W m m' SB,
  icp_globals m SB -> munch W m m' -> wmono segs m m' ->
  disjoint_from W 0xa4000 (0xaee00 - 0xa4000) ->
  icp_globals m' SB.
Proof.
  intros W m m' SB G MU WM D.
  unfold icp_globals, A_GOT_SBPTR, A_SBVAR, A_GOT_RIC, A_RIC, A_REAL_MEMCPY, A_REAL_MEMSET, A_GOT_MIDBEG, A_MIDBEG,
    A_GOT_MIDEND, A_MIDEND, A_GOT_HIGHEND, A_HIGHEND, A_INITED in *.
  assert (DD : forall A k, 0xa4000 <= A -> A + Z.of_nat k <= 0xaee00 -> disjoint_from W A (Z.of_nat k)).
  { intros A k H1 H2. eapply disjoint_from_sub; [exact D| lia | lia]. }
  destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & SBR).
  repeat match goal with
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | apply DD; cbn; lia ]
  end.
  repeat (split; [assumption|]). exact SBR.
Qed.
End Globals.

End RC__1.
Ltac icp_globals_open G :=
  unfold icp_globals, A_GOT_SBPTR, A_SBVAR, A_GOT_RIC, A_RIC, A_REAL_MEMCPY, A_REAL_MEMSET, A_GOT_MIDBEG, A_MIDBEG,
    A_GOT_MIDEND, A_MIDEND, A_GOT_HIGHEND, A_HIGHEND, A_INITED, A_MUSL_MEMCPY, A_MUSL_MEMSET, A_HIGHEND_VAL in G;
  let SBR := fresh "SBR" in
  destruct G as (?GSBP & ?GSB & ?GRICP & ?GRIC & ?GRCPY & ?GRSET & ?GMBP & ?GMB & ?GMEP & ?GME & ?GHEP & ?GHE & ?GINI & SBR).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section RC__2.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section Shrink.
Variable segs : list MemImageType.Segment.

Lemma bytes_at_firstn : forall m a bs k, bytes_at segs m a bs -> bytes_at segs m a (firstn k bs).
Proof.
  intros m a bs k (H1 & H2 & H3). pose proof (firstn_le_length k bs).
  split; [lia|]. split; [rewrite length_firstn; lia|].
  intros i Hi. rewrite length_firstn in Hi. rewrite H3 by lia.
  rewrite nth_error_firstn. destruct (Nat.ltb_spec i k); [reflexivity| lia].
Qed.

Lemma shadow_window_shrink : forall m SB A n n' ws,
  0 <= SB -> 0 <= A -> 1 <= n' <= n ->
  shadow_window segs m SB A n ws -> range_clean SB A n ws ->
  let ws' := firstn (Z.to_nat (shw_hi SB A n' - shw_lo SB A)) ws in
  shadow_window segs m SB A n' ws' /\ range_clean SB A n' ws'.
Proof.
  intros m SB A n n' ws HSB HA Hn [WB WL] RC. cbv zeta.
  pose proof (shw_geom SB A n HSB HA ltac:(lia)) as G. pose proof (shw_geom SB A n' HSB HA ltac:(lia)) as G'.
  cbv zeta in G, G'.
  assert (M : shw_hi SB A n' <= shw_hi SB A n).
  { unfold shw_hi. apply Z.add_le_mono_r. apply al8_mono.
    rewrite !Z.shiftr_div_pow2 by lia. apply Z.add_le_mono_l. apply Z.div_le_mono; lia. }
  split.
  - split; [apply bytes_at_firstn; exact WB|]. rewrite length_firstn. lia.
  - intros g Hg.
    assert (Hg2 : Z.shiftr (A + n' + -1) 3 <= Z.shiftr (A + n + -1) 3).
    { rewrite !Z.shiftr_div_pow2 by lia. apply Z.div_le_mono; lia. }
    destruct (RC g ltac:(lia)) as (k & Hk & K).
    exists k. split.
    + rewrite nth_error_firstn. rewrite Hk. destruct (Nat.ltb_spec (Z.to_nat (SB + g - shw_lo SB A)) (Z.to_nat (shw_hi SB A n' - shw_lo SB A))); [reflexivity|].
      exfalso. lia.
    + destruct K as [K|[K1 K2]]; [left; exact K| right].
      assert (g = Z.shiftr (A + n' + -1) 3) by lia. split; [assumption|].
      rewrite (shr3_mod (A + n' + -1)) by lia. rewrite (shr3_mod (A + n + -1)) in K2 by lia. lia.
Qed.
End Shrink.
End RC__2.
