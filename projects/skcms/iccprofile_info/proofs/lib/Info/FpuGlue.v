(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia Bool Reals Psatz SpecFloat.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem Fpu.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec PropExecFP FpuFacts.
Unset Nia Cache.  (* [comment removed for export] *)
Unset Lia Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bv_modulus_32 : bv_modulus 32 = 2^32. Proof. reflexivity. Qed.
Lemma bv_modulus_64 : bv_modulus 64 = 2^64. Proof. reflexivity. Qed.
Lemma u32_range' (v : bv 32) : 0 <= bv_unsigned v < 2^32.
Proof. pose proof (bv_unsigned_in_range _ v) as H. rewrite bv_modulus_32 in H. lia. Qed.
Lemma low32_unsigned' (a : word) : bv_unsigned (low32 a) = bv_unsigned a mod 2^32.
Proof.
  unfold low32. rewrite bv_extract_unsigned. change (Z.of_N 0) with 0. rewrite Z.shiftr_0_r.
  unfold bv_wrap. rewrite bv_modulus_32. reflexivity.
Qed.
Lemma low32_Z_to_bv z : low32 (Z_to_bv 64 z) = Z_to_bv 32 z.
Proof.
  apply bv_eq. rewrite low32_unsigned', !Z_to_bv_unsigned. unfold bv_wrap.
  rewrite bv_modulus_32, bv_modulus_64.
  symmetry. apply Znumtheory.Zmod_div_mod; try lia. exists (2^32). reflexivity.
Qed.
(* [comment removed for export] *)
Lemma land_high_low (a b k : Z) : 0 <= a -> 0 <= b < 2^k -> 0 <= k -> Z.land (a * 2^k) b = 0.
Proof.
intros Ha Hb Hk. apply Z.bits_inj'; intros n Hn. rewrite Z.land_spec, Z.bits_0.
destruct (Z_lt_le_dec n k) as [L|L].
- rewrite Z.mul_pow2_bits_low by lia. reflexivity.
- replace (Z.testbit b n) with false; [apply andb_false_r|].
  symmetry. apply Z.testbit_false; [lia|]. rewrite Z.div_small; [reflexivity|]. split; [lia|].
  eapply Z.lt_le_trans; [apply (proj2 Hb)|]. apply Z.pow_le_mono_r; lia.
Qed.
Lemma lor_disjoint_add (a b k : Z) : 0 <= a -> 0 <= b < 2^k -> 0 <= k -> Z.lor (a * 2^k) b = a * 2^k + b.
Proof.
  intros Ha Hb Hk. rewrite <- Z.lxor_lor by (apply land_high_low; lia).
  symmetry. apply Z.add_nocarry_lxor. apply land_high_low; lia.
Qed.
Lemma nan_box_unsigned (v : bv 32) :
  bv_unsigned (nan_box v) = (2^32 - 1) * 2^32 + bv_unsigned v.
Proof.
  unfold nan_box. rewrite bv_concat_unsigned by reflexivity.
  rewrite Z_to_bv_unsigned. change (bv_wrap 32 (-1)) with (2^32 - 1).
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ Z.of_N 32) with (2^32).
  apply lor_disjoint_add; try lia. apply u32_range'.
Qed.
Lemma unbox_nan_box (v : bv 32) : unbox_s (nan_box v) = v.
Proof.
  unfold unbox_s.
  assert (E : bv_unsigned (bv_extract 32 32 (nan_box v)) = Z.ones 32).
  { rewrite bv_extract_unsigned. rewrite nan_box_unsigned. unfold bv_wrap. rewrite bv_modulus_32.
    rewrite Z.shiftr_div_pow2 by lia. change (2 ^ Z.of_N 32) with (2^32).
    pose proof (u32_range' v).
    rewrite Z.div_add_l by lia. rewrite Z.div_small by lia. reflexivity. }
  rewrite E. rewrite Z.eqb_refl.
  apply bv_eq. rewrite low32_unsigned', nan_box_unsigned.
  pose proof (u32_range' v). rewrite Z.add_comm, Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma low32_nan_box (v : bv 32) : low32 (nan_box v) = v.
Proof.
  apply bv_eq. rewrite low32_unsigned', nan_box_unsigned.
  pose proof (u32_range' v). rewrite Z.add_comm, Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma sgnj_val_same (a : bv 32) : sgnj_val F_SGNJ a a = a.
Proof.
  unfold sgnj_val. apply bv_eq. rewrite bv_concat_unsigned by reflexivity.
  rewrite bv_extract_unsigned. change (Z.of_N 0) with 0. rewrite Z.shiftr_0_r.
  unfold bv_wrap. change (bv_modulus (32 - 1)) with (2^31). change (Z.of_N (32 - 1)) with 31.
  rewrite Z_to_bv_unsigned. pose proof (u32_range' a) as R.
  unfold bit. change (Z.of_N (32 - 1)) with 31.
  pose proof (Z.div_mod (bv_unsigned a) (2^31) ltac:(lia)) as DM.
  assert (B : bv_unsigned a / 2^31 = (if Z.testbit (bv_unsigned a) 31 then 1 else 0)).
  { rewrite Z.testbit_odd, Z.shiftr_div_pow2 by lia.
    assert (0 <= bv_unsigned a / 2^31 < 2) by (split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; lia]).
    destruct (Z.odd (bv_unsigned a / 2 ^ 31)) eqn:O.
    - destruct (Z.eq_dec (bv_unsigned a / 2^31) 0) as [Z0|]; [rewrite Z0 in O; discriminate|lia].
    - destruct (Z.eq_dec (bv_unsigned a / 2^31) 1) as [Z1|]; [rewrite Z1 in O; discriminate|lia]. }
  rewrite Z.shiftl_mul_pow2 by lia.
  assert (M : 0 <= bv_unsigned a mod 2^31 < 2^31) by (apply Z.mod_pos_bound; lia).
  destruct (Z.testbit (bv_unsigned a) 31).
  - change (bv_wrap 1 1) with 1. rewrite lor_disjoint_add by lia. lia.
  - change (bv_wrap 1 0) with 0. rewrite Z.mul_0_l, Z.lor_0_l. lia.
Qed.
Lemma sext64_of_small (v : bv 32) : bv_unsigned v < 2^31 -> sext 64 v = Z_to_bv 64 (bv_unsigned v).
Proof.
  intros H. pose proof (u32_range' v). apply bv_eq. unfold sext. rewrite bv_sign_extend_unsigned.
  rewrite Z_to_bv_unsigned. f_equal.
  unfold bv_signed. apply bv_swrap_small. change (bv_half_modulus 32) with (2^31). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma fval_S (x : word) : fval FMT_S x = bv_unsigned (unbox_s x). Proof. reflexivity. Qed.
Lemma fword_S (v : Z) : fword FMT_S v = nan_box (Z_to_bv 32 v). Proof. reflexivity. Qed.

Lemma fval_fword_S (z : Z) : 0 <= z < 2^32 -> fval FMT_S (fword FMT_S z) = z.
Proof.
  intros Hz. rewrite fval_S, fword_S, unbox_nan_box, Z_to_bv_unsigned. apply bv_wrap_small.
  rewrite bv_modulus_32. lia.
Qed.

Lemma fval_fmv_fx_S (z : Z) : fval FMT_S (fmv_fx_res FMT_S (Z_to_bv 64 z)) = z mod 2^32.
Proof.
  rewrite fval_S. unfold fmv_fx_res. rewrite low32_Z_to_bv, unbox_nan_box, Z_to_bv_unsigned.
  unfold bv_wrap. now rewrite bv_modulus_32.
Qed.

Lemma fval_fsgnj_same_S (x : word) : fval FMT_S (fsgnj_res F_SGNJ FMT_S x x) = fval FMT_S x.
Proof. rewrite !fval_S. unfold fsgnj_res. rewrite sgnj_val_same, unbox_nan_box. reflexivity. Qed.

Lemma fminmax_res_S op (x y : word) :
  fminmax_res op FMT_S x y = fword FMT_S (fst (fp_minmax fmt_single (minmax_is_max op) (fval FMT_S x) (fval FMT_S y))).
Proof. reflexivity. Qed.
Lemma fari_res_S op md (x y : word) :
  fari_res op FMT_S md x y = fword FMT_S (fst (fari_raw op fmt_single md (fval FMT_S x) (fval FMT_S y))).
Proof. reflexivity. Qed.
Lemma fcmp_bool_S op (x y : word) :
  fcmp_bool op FMT_S x y = fst (fcmp_raw op fmt_single (fval FMT_S x) (fval FMT_S y)).
Proof. reflexivity. Qed.
Lemma fcvt_if_res_S sgn bits md (x : word) :
  fcvt_if_res FMT_S sgn bits md x = fword FMT_S (fst (fp_of_int fmt_single md sgn bits (bv_unsigned x))).
Proof. reflexivity. Qed.
Lemma fcvt_fi_res_32 sf sgn md (x : word) :
  fcvt_fi_res sf sgn 32 md x = sext 64 (Z_to_bv 32 (fst (fp_to_int (fp_format sf) md sgn 32 (fval sf x)))).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma fcvt_fi_res_32_small sf sgn md (x : word) (v : Z) :
  fst (fp_to_int (fp_format sf) md sgn 32 (fval sf x)) = v -> 0 <= v < 2^31 ->
  fcvt_fi_res sf sgn 32 md x = Z_to_bv 64 v /\ bv_unsigned (fcvt_fi_res sf sgn 32 md x) = v.
Proof.
  intros Hv Hr. rewrite fcvt_fi_res_32, Hv.
  assert (U : bv_unsigned (Z_to_bv 32 v) = v).
  { rewrite Z_to_bv_unsigned. apply bv_wrap_small. rewrite bv_modulus_32. lia. }
  rewrite sext64_of_small by (rewrite U; lia). rewrite U. split; [reflexivity|].
  rewrite Z_to_bv_unsigned. apply bv_wrap_small. rewrite bv_modulus_64. lia.
Qed.

(* [comment removed for export] *)
Lemma fcvt_fi_res_32_wrap sf sgn md (x : word) (v : Z) :
  fst (fp_to_int (fp_format sf) md sgn 32 (fval sf x)) = int_wrap 32 v -> - 2^31 <= v < 2^31 ->
  fcvt_fi_res sf sgn 32 md x = Z_to_bv 64 v.
Proof.
  intros Hv Hr. rewrite fcvt_fi_res_32, Hv.
  apply bv_eq. unfold sext. rewrite bv_sign_extend_unsigned, !Z_to_bv_unsigned. f_equal.
  rewrite Z_to_bv_signed. unfold int_wrap. rewrite Z.land_ones by lia.
  change (v mod 2 ^ 32) with (bv_wrap 32 v). rewrite bv_swrap_wrap. apply bv_swrap_small.
  change (bv_half_modulus 32) with (2^31). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section eval_curve_words.
  (* [comment removed for export] *)
  Variables (X N1 w1 w0 : word) (m : Z).
  Hypothesis Hm  : 1 <= m <= 2^24 - 1.
  Hypothesis HN1 : bv_unsigned N1 = m.
  Hypothesis Hw1 : fval FMT_S w1 = 0x3f800000.
  Hypothesis Hw0 : fval FMT_S w0 = 0.

  (* [comment removed for export] *)
  Definition ec_t  : word := fminmax_res F_MIN FMT_S X w1.                         (* [comment removed for export] *)
  Definition ec_b  : bool := fcmp_bool F_LT FMT_S ec_t w0.                          (* [comment removed for export] *)
  Definition ec_c  : word := if ec_b then w0 else fsgnj_res F_SGNJ FMT_S ec_t ec_t. (* [comment removed for export] *)
  Definition ec_F  : word := fcvt_if_res FMT_S false 32 RNE N1.                     (* [comment removed for export] *)
  Definition ec_ix : word := fari_res F_MUL FMT_S RNE ec_c ec_F.                    (* [comment removed for export] *)
  Definition ec_lo : word := fcvt_fi_res FMT_S true 32 RTZ ec_ix.                   (* [comment removed for export] *)
  Definition ec_s  : word := fari_res F_ADD FMT_S RNE ec_ix w1.                      (* [comment removed for export] *)
  Definition ec_xs : word := fmv_xf_res FMT_S ec_s.                                 (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variable p : word.
  Hypothesis Hp : bv_unsigned p = bv_unsigned ec_xs - 1.
  Definition ec_wp : word := fmv_fx_res FMT_S p.                                    (* [comment removed for export] *)
  Definition ec_hi : word := fcvt_fi_res FMT_S true 32 RTZ ec_wp.                   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Let Xz := fval FMT_S X.
  Let t := fst (fp_minmax fmt_single false Xz one32).
  Let c := if fst (fp_lt fmt_single t 0) then 0 else t.
  Let F := fst (fp_of_int fmt_single RNE false 32 m).
  Let ix := fst (fp_mul fmt_single RNE c F).
  Let lo := fst (fp_to_int fmt_single RTZ true 32 ix).
  Let s := fst (fp_add fmt_single RNE ix one32).
  Let pz := s - 1.
  Let hi := fst (fp_to_int fmt_single RTZ true 32 pz).

  Lemma Xz_range : 0 <= Xz < 2^32.
  Proof. unfold Xz. rewrite fval_S. apply u32_range'. Qed.

  Lemma t_range : 0 <= t < 2^32.
  Proof.
    pose proof (fp_min_one_cases Xz) as TC. cbv zeta in TC. fold t in TC.
    destruct TC as [E | [E _]]; rewrite E; [unfold one32; lia| apply Xz_range].
  Qed.

  Lemma ec_t_val : fval FMT_S ec_t = t.
  Proof.
    unfold ec_t. rewrite fminmax_res_S, Hw1. cbn [minmax_is_max]. fold Xz. change 1065353216 with one32. fold t.
    apply fval_fword_S. apply t_range.
  Qed.

  Lemma ec_b_val : ec_b = fst (fp_lt fmt_single t 0).
  Proof. unfold ec_b. rewrite fcmp_bool_S, ec_t_val, Hw0. reflexivity. Qed.

  Lemma ec_c_val : fval FMT_S ec_c = c.
  Proof.
    unfold ec_c, c. rewrite ec_b_val. destruct (fst (fp_lt fmt_single t 0)).
    - exact Hw0.
    - rewrite fval_fsgnj_same_S. apply ec_t_val.
  Qed.

  Lemma ec_F_val : fval FMT_S ec_F = F.
  Proof.
    unfold ec_F. rewrite fcvt_if_res_S, HN1. fold F.
    pose proof (fp_of_int_u32_correct RNE m ltac:(lia)) as (_ & _ & _ & R & _).
    apply fval_fword_S. exact R.
  Qed.

  Lemma ec_ix_val : fval FMT_S ec_ix = ix.
  Proof.
    unfold ec_ix. rewrite fari_res_S, ec_c_val, ec_F_val. cbn [fari_raw]. fold ix.
    pose proof (ix_props Xz m Hm) as (_ & _ & R & _). fold t c F ix in R.
    apply fval_fword_S. exact R.
  Qed.

  (* [comment removed for export] *)
  Theorem ec_lo_range : ec_lo = Z_to_bv 64 lo /\ 0 <= bv_unsigned ec_lo <= m.
  Proof.
    pose proof (L3 Xz m Hm) as (R & _ & _). fold t c F ix in R. fold lo in R.
    assert (E : fst (fp_to_int (fp_format FMT_S) RTZ true 32 (fval FMT_S ec_ix)) = lo).
    { cbn [fp_format]. rewrite ec_ix_val. reflexivity. }
    pose proof (fcvt_fi_res_32_small FMT_S true RTZ ec_ix lo E ltac:(lia)) as [A B].
    unfold ec_lo. split; [exact A|]. rewrite B. lia.
  Qed.

  Lemma ec_s_val : fval FMT_S ec_s = s /\ 0 < s < 2139095040.
  Proof.
    pose proof (Ls Xz m Hm) as R. fold t c F ix in R. fold s in R.
    split; [|exact R].
    unfold ec_s. rewrite fari_res_S, ec_ix_val, Hw1. cbn [fari_raw]. change 1065353216 with one32. fold s.
    apply fval_fword_S. lia.
  Qed.

  (* [comment removed for export] *)
  Theorem ec_xs_val : ec_xs = Z_to_bv 64 s /\ bv_unsigned ec_xs = s /\ 0 < s < 2139095040.
  Proof.
    destruct ec_s_val as [V R].
    assert (U : bv_unsigned (unbox_s ec_s) = s) by (rewrite <- fval_S; exact V).
    assert (L : low32 ec_s = unbox_s ec_s).
    { unfold ec_s. rewrite fari_res_S, fword_S.
      (* [comment removed for export] *)
      rewrite unbox_nan_box, low32_nan_box. reflexivity. }
    unfold ec_xs, fmv_xf_res. rewrite L.
    rewrite sext64_of_small by (rewrite U; lia). rewrite U.
    split; [reflexivity|]. split; [|exact R].
    rewrite Z_to_bv_unsigned. apply bv_wrap_small. rewrite bv_modulus_64. lia.
  Qed.

  Lemma ec_wp_val : fval FMT_S ec_wp = pz.
  Proof.
    destruct ec_xs_val as (_ & U & R).
    unfold ec_wp. rewrite fval_S. unfold fmv_fx_res. rewrite unbox_nan_box, low32_unsigned', Hp, U.
    unfold pz. apply Z.mod_small. lia.
  Qed.

  (* [comment removed for export] *)
  Theorem ec_hi_range : ec_hi = Z_to_bv 64 hi /\ 0 <= bv_unsigned ec_hi <= m.
  Proof.
    pose proof (L4c Xz m Hm) as (R & _ & _). fold t c F ix s in R. fold pz in R. fold hi in R.
    assert (E : fst (fp_to_int (fp_format FMT_S) RTZ true 32 (fval FMT_S ec_wp)) = hi).
    { cbn [fp_format]. rewrite ec_wp_val. reflexivity. }
    pose proof (fcvt_fi_res_32_small FMT_S true RTZ ec_wp hi E ltac:(lia)) as [A B].
    unfold ec_hi. split; [exact A|]. rewrite B. lia.
  Qed.

  (* [comment removed for export] *)
  Theorem eval_curve_word_ranges (b : bool) (wc : word) :
    fcmp_bool F_LT FMT_S (fminmax_res F_MIN FMT_S X w1) w0 = b ->
    wc = (if b then w0 else fsgnj_res F_SGNJ FMT_S (fminmax_res F_MIN FMT_S X w1) (fminmax_res F_MIN FMT_S X w1)) ->
    let wix := fari_res F_MUL FMT_S RNE wc (fcvt_if_res FMT_S false 32 RNE N1) in
    let xs  := fmv_xf_res FMT_S (fari_res F_ADD FMT_S RNE wix w1) in
    (0 <= bv_unsigned (fcvt_fi_res FMT_S true 32 RTZ wix) <= m)%Z /\
    (0 < bv_unsigned xs < 2139095040)%Z /\ xs = ec_xs /\
    (0 <= bv_unsigned (fcvt_fi_res FMT_S true 32 RTZ (fmv_fx_res FMT_S p)) <= m)%Z.
  Proof.
    intros Hb Hwc.
    assert (Ec : wc = ec_c). { unfold ec_c, ec_b, ec_t. rewrite Hb. exact Hwc. }
    cbv zeta. rewrite Ec.
    change (fari_res F_MUL FMT_S RNE ec_c (fcvt_if_res FMT_S false 32 RNE N1)) with ec_ix.
    change (fmv_xf_res FMT_S (fari_res F_ADD FMT_S RNE ec_ix w1)) with ec_xs.
    change (fcvt_fi_res FMT_S true 32 RTZ ec_ix) with ec_lo.
    change (fmv_fx_res FMT_S p) with ec_wp. change (fcvt_fi_res FMT_S true 32 RTZ ec_wp) with ec_hi.
    pose proof ec_lo_range as [_ A].
    destruct ec_xs_val as (_ & U & B0).
    pose proof ec_hi_range as [_ C].
    rewrite U. repeat split; auto; lia.
  Qed.

  (* [comment removed for export] *)
  Variables (wK w31 : word).
  Hypothesis HwK : fval FMT_S wK = 0xcf000001.
  Hypothesis Hw31 : fval FMT_S w31 = 0x4f000000.

  Theorem ec_ub_checks :
    fcmp_bool F_LT FMT_S wK ec_ix = true /\ fcmp_bool F_LT FMT_S ec_ix w31 = true /\
    fcmp_bool F_LT FMT_S wK ec_wp = true /\ fcmp_bool F_LT FMT_S ec_wp w31 = true.
  Proof.
    rewrite !fcmp_bool_S, HwK, Hw31, ec_ix_val, ec_wp_val. cbn [fcmp_raw].
    change 3472883713 with K32. change 1325400064 with two31f.
    repeat split.
    - apply (L1 Xz m Hm).
    - apply (L2 Xz m Hm).
    - apply (L4a Xz m Hm).
    - apply (L4b Xz m Hm).
  Qed.

  (* [comment removed for export] *)
  Theorem eval_curve_word_checks (b : bool) (wc : word) :
    fcmp_bool F_LT FMT_S (fminmax_res F_MIN FMT_S X w1) w0 = b ->
    wc = (if b then w0 else fsgnj_res F_SGNJ FMT_S (fminmax_res F_MIN FMT_S X w1) (fminmax_res F_MIN FMT_S X w1)) ->
    let wix := fari_res F_MUL FMT_S RNE wc (fcvt_if_res FMT_S false 32 RNE N1) in
    fcmp_bool F_LT FMT_S wK wix = true /\ fcmp_bool F_LT FMT_S wix w31 = true /\
    fcmp_bool F_LT FMT_S wK (fmv_fx_res FMT_S p) = true /\ fcmp_bool F_LT FMT_S (fmv_fx_res FMT_S p) w31 = true.
  Proof.
    intros Hb Hwc.
    assert (Ec : wc = ec_c). { unfold ec_c, ec_b, ec_t. rewrite Hb. exact Hwc. }
    cbv zeta. rewrite Ec.
    change (fari_res F_MUL FMT_S RNE ec_c (fcvt_if_res FMT_S false 32 RNE N1)) with ec_ix.
    change (fmv_fx_res FMT_S p) with ec_wp.
    exact ec_ub_checks.
  Qed.
End eval_curve_words.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section classify_words.
  (* [comment removed for export] *)
  Variables (g w0 wm128 wK w31 : word).
  Hypothesis Hw0 : fval FMT_S w0 = 0.
  Hypothesis Hwm128 : fval FMT_S wm128 = 0xc3000000.
  Hypothesis HwK : fval FMT_S wK = 0xcf000001.
  Hypothesis Hw31 : fval FMT_S w31 = 0x4f000000.
  Hypothesis Hlt0 : fcmp_bool F_LT FMT_S g w0 = true.        (* [comment removed for export] *)
  Hypothesis Hge128 : fcmp_bool F_LT FMT_S g wm128 = false.  (* [comment removed for export] *)

  Theorem classify_words :
    fcmp_bool F_LT FMT_S wK g = true /\ fcmp_bool F_LT FMT_S g w31 = true /\
    exists v, -128 <= v <= 0 /\ fcvt_fi_res FMT_S true 32 RTZ g = Z_to_bv 64 v.
  Proof.
    rewrite !fcmp_bool_S, HwK, Hw31. rewrite fcmp_bool_S, Hw0 in Hlt0. rewrite fcmp_bool_S, Hwm128 in Hge128.
    cbn [fcmp_raw] in Hlt0, Hge128 |- *.
    change 3472883713 with K32. change 1325400064 with two31f. change 3271557120 with m128f in Hge128.
    destruct (classify_cast_ok (fval FMT_S g) Hlt0 Hge128) as (A & B & v & Hv & Hc & _).
    split; [exact A|]. split; [exact B|].
    exists v. split; [exact Hv|].
    apply (fcvt_fi_res_32_wrap FMT_S true RTZ g v); [exact Hc| lia].
  Qed.
End classify_words.
