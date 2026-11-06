(** reac-pw/fuzz_headamp image A (fuzz_headamp.asan): THE VALUE LAYER of the piece value_nearest of the checking
    segment M03 of LLVMFuzzerTestOneInput (0x83364 -> 0x83548 / 0x83454 / 0x83460: the inlined cell_value of
    fuzz_headamp.c:94-107 with the inlined pod_nearest(f, 0, 255) of pod.h:152-171, and the range test of
    expect_of, fuzz_headamp.c:123-148). Proves no function (kind: value layer). Pure values: no image, no segment,
    no walk.

    It joins the tests the machine makes to Pod/Headamp.v's [cell_value] and [expect_cell]:
    - the Bool and Int arms read the body word with `lw`, which leaves the sign-extended word [hvm_sx v] of the
      32-bit pattern v in the register; the Int arm then tests it unsigned against 0x100 (`bgeu s4,0x100`):
      [hvm_sx_*];
    - [cell_value] by entry type (Bool 2, Int 4, Float 6, any other type, size below 4): [hvm_cv_*];
    - expect_of's range test against the param's top value [hvm_top] (`bltu s2,a0` with s2 = the top):
      [hvm_cell_inr], [hvm_cell_inl], [hvm_valid];
    - the Float arm runs the same five soft-float calls with the same constants as the plain image, so its machine
      model is Prog/HeadCheck/NearVal.v's [hn_bin], already proved equal to [nearest] at (0, 255); the lemmas here
      restate its exits test by test ([hvm_hn_*]), the register pairs the calls pass ([hvm_w128] and the ranges),
      0.5L / -0.5L as the two high words the code loads with a zero low word ([hvm_half_rng]), and the NaN boxing
      that `flw` / `feq.s` / `flt.s` / `fcvt.l.s` / `fmv.s` go through ([hvm_unbox_box], [hvm_box_unsigned],
      [hvm_sgnj_self]).
    Its lemmas hvm_lor_shift_add, hvm_u32_lit, hvm_nan_box_word, hvm_unbox_box and hvm_sgnj_self are the proofs
    of lor_shift_add, u32_lit, nan_box_unsigned, unbox_nan_box and sgnj_self32 of Prog/HeadCheck/Near.v (a file
    with no licence lines), with the hvm_ prefix and two corollaries added; the rest of the file is new. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.Spec Require SoftFloat SFVal SFSub NearSF.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.RL.G Require C_extendsftf2 C_floatditf.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.HeadCheck Require Import NearVal.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Cursor Model Accessors Nearest Headamp.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

(** ** The words the code computes with *)
(** The top value of a param: HA_SENS_MAX for sens, 1 for phantom and pad (fuzz_headamp.c:141). *)
Definition hvm_top (p : Z) : Z := if p =? Headamp.HA_SENS then Headamp.HA_SENS_MAX else 1.
(** The 64-bit word an `lw` of the 32-bit pattern v leaves in a register. *)
Definition hvm_sx (v : Z) : Z := if v <? 2 ^ 31 then v else v + (2 ^ 64 - 2 ^ 32).

(** ** Sign extension (the Int and Bool arms read their value with `lw`) *)
Lemma hvm_sx_range : forall v, 0 <= v < 2^32 -> 0 <= hvm_sx v < 2^64.
Proof. intros v Hv. unfold hvm_sx. destruct (Z.ltb_spec v (2^31)); lia. Qed.

Lemma hvm_sx_id : forall v, 0 <= v < 2^31 -> hvm_sx v = v.
Proof. intros v Hv. unfold hvm_sx. destruct (Z.ltb_spec v (2^31)); lia. Qed.

Lemma hvm_sx_eq : forall v w, 0 <= v < 2^32 -> 0 <= w < 2^31 -> (hvm_sx v = w <-> v = w).
Proof. intros v w Hv Hw. unfold hvm_sx. destruct (Z.ltb_spec v (2^31)); lia. Qed.

Lemma hvm_sx_zero : forall v, 0 <= v < 2^32 -> (hvm_sx v = 0 <-> v = 0).
Proof. intros v Hv. unfold hvm_sx. destruct (Z.ltb_spec v (2^31)); lia. Qed.

(** The Int arm's `bgeu s4,0x100`: the unsigned test of the sign-extended word is the test of the pattern. *)
Lemma hvm_sx_256 : forall v, 0 <= v < 2^32 -> (256 <= hvm_sx v <-> 255 < v).
Proof. intros v Hv. unfold hvm_sx. destruct (Z.ltb_spec v (2^31)); lia. Qed.

Lemma hvm_sx_s32 : forall v, 0 <= v < 2^32 -> v <= 255 -> hvm_sx v = Accessors.s32 v /\ Accessors.s32 v = v.
Proof. intros v Hv Hl. unfold hvm_sx, Accessors.s32. destruct (Z.ltb_spec v (2^31)); lia. Qed.

(** ** cell_value by entry type *)
Lemma hvm_cv_bool : forall e, Model.ent_wf e -> Model.e_type e = Model.POD_BOOL -> 4 <= Model.e_size e ->
  Headamp.cell_value e = (if Cursor.rd32 (Model.e_body e) =? 0 then 0 else 1).
Proof.
  intros e _ Ht Hs. unfold Headamp.cell_value, Accessors.bool_of. rewrite Ht.
  rewrite (proj2 (Z.leb_le 4 (Model.e_size e)) Hs).
  change (Model.POD_BOOL =? Model.POD_BOOL) with true. cbn [andb].
  destruct (Cursor.rd32 (Model.e_body e) =? 0); reflexivity.
Qed.

Lemma hvm_cv_int : forall e, Model.ent_wf e -> Model.e_type e = Model.POD_INT -> 4 <= Model.e_size e ->
  Headamp.cell_value e = (if Cursor.rd32 (Model.e_body e) <=? 255 then Cursor.rd32 (Model.e_body e) else -1).
Proof.
  intros e _ Ht Hs. pose proof (Cursor.rd32_range (Model.e_body e)) as R.
  unfold Headamp.cell_value, Accessors.bool_of, Accessors.int_of. rewrite Ht.
  rewrite (proj2 (Z.leb_le 4 (Model.e_size e)) Hs).
  change (Model.POD_INT =? Model.POD_BOOL) with false. change (Model.POD_INT =? Model.POD_INT) with true.
  cbn [andb]. unfold Accessors.s32. revert R. generalize (Cursor.rd32 (Model.e_body e)). intros v R.
  repeat match goal with
  | |- context [?a <? ?b] => destruct (Z.ltb_spec a b)
  | |- context [?a <=? ?b] => destruct (Z.leb_spec a b)
  end; cbn [andb]; first [reflexivity | lia].
Qed.

Lemma hvm_cv_float : forall e, Model.ent_wf e -> Model.e_type e = Model.POD_FLOAT -> 4 <= Model.e_size e ->
  Headamp.cell_value e =
  match Nearest.nearest (Cursor.rd32 (Model.e_body e)) 0 255 with Some n => n | None => -1 end.
Proof.
  intros e _ Ht Hs. unfold Headamp.cell_value, Accessors.bool_of, Accessors.int_of, Accessors.float_of.
  rewrite Ht. rewrite (proj2 (Z.leb_le 4 (Model.e_size e)) Hs).
  change (Model.POD_FLOAT =? Model.POD_BOOL) with false. change (Model.POD_FLOAT =? Model.POD_INT) with false.
  change (Model.POD_FLOAT =? Model.POD_FLOAT) with true. cbn [andb]. reflexivity.
Qed.

Lemma hvm_cv_small : forall e, Model.ent_wf e -> Model.e_size e < 4 -> Headamp.cell_value e = -1.
Proof.
  intros e _ Hs. unfold Headamp.cell_value, Accessors.bool_of, Accessors.int_of, Accessors.float_of.
  rewrite (proj2 (Z.leb_gt 4 (Model.e_size e)) Hs). rewrite !andb_false_r. reflexivity.
Qed.

Lemma hvm_cv_other : forall e, Model.ent_wf e -> Model.e_type e <> Model.POD_BOOL -> Model.e_type e <> Model.POD_INT ->
  Model.e_type e <> Model.POD_FLOAT -> Headamp.cell_value e = -1.
Proof.
  intros e _ Hb Hi Hf. unfold Headamp.cell_value, Accessors.bool_of, Accessors.int_of, Accessors.float_of.
  rewrite (proj2 (Z.eqb_neq _ _) Hb), (proj2 (Z.eqb_neq _ _) Hi), (proj2 (Z.eqb_neq _ _) Hf).
  cbn [andb]. reflexivity.
Qed.

Lemma hvm_cv_range : forall e, Model.ent_wf e -> -1 <= Headamp.cell_value e <= 255.
Proof.
  intros e _. unfold Headamp.cell_value.
  destruct (Accessors.bool_of e) as [[|]|]; [lia | lia |].
  destruct (Accessors.int_of e) as [i|].
  - destruct ((0 <=? i) && (i <=? 255)) eqn:E; [|lia].
    apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2. lia.
  - destruct (Accessors.float_of e) as [f|]; [|lia].
    destruct (Nearest.nearest f 0 255) as [n|] eqn:EN; [|lia].
    apply Headamp.nearest_range in EN. lia.
Qed.

(** What [Model.ent_wf] gives: exactly these two bounds (and the body's length). *)
Lemma hvm_ent_bounds : forall e, Model.ent_wf e -> 0 <= Model.e_type e < 2^32 /\ 0 <= Model.e_size e <= 45.
Proof. intros e (Ht & _ & Hs). split; [exact Ht | exact Hs]. Qed.

(** ** expect_cell (fuzz_headamp.c:123-148) *)
Lemma hvm_key_cell : forall rest ch p, Headamp.expect_key rest = Headamp.KCell ch p ->
  0 <= ch < Headamp.HA_CHANNELS /\ (p = Headamp.HA_PHANTOM \/ p = Headamp.HA_PAD \/ p = Headamp.HA_SENS).
Proof.
  intros rest ch p H. rewrite <- Headamp.parse_key_expect_key in H.
  apply Headamp.parse_key_cell in H as [Hc Hp]. split; [|exact Hp].
  unfold Headamp.REAC_HEADAMP_MAX_CH in Hc. unfold Headamp.HA_CHANNELS. lia.
Qed.

Lemma hvm_top_range : forall p, p = Headamp.HA_PHANTOM \/ p = Headamp.HA_PAD \/ p = Headamp.HA_SENS ->
  hvm_top p = 1 \/ hvm_top p = Headamp.HA_SENS_MAX.
Proof. intros p [-> | [-> | ->]]; [left | left | right]; reflexivity. Qed.

Lemma hvm_top_bounds : forall p, 1 <= hvm_top p <= 0x37.
Proof. intros p. unfold hvm_top, Headamp.HA_SENS_MAX. destruct (p =? Headamp.HA_SENS); lia. Qed.

Lemma hvm_cell_inr : forall k v ch p,
  Headamp.expect_key (skipn (length Headamp.HA_PREFIX) k) = Headamp.KCell ch p ->
  0 <= Headamp.cell_value v -> Headamp.cell_value v <= hvm_top p ->
  Headamp.expect_cell k v = inr (ch, p, Headamp.cell_value v).
Proof.
  intros k v ch p H H0 H1. unfold Headamp.expect_cell. rewrite H. cbv beta iota zeta.
  unfold hvm_top in H1.
  rewrite (proj2 (Z.ltb_ge _ _) H0), (proj2 (Z.ltb_ge _ _) H1). reflexivity.
Qed.

Lemma hvm_cell_inl : forall k v ch p,
  Headamp.expect_key (skipn (length Headamp.HA_PREFIX) k) = Headamp.KCell ch p ->
  (Headamp.cell_value v < 0 \/ hvm_top p < Headamp.cell_value v) ->
  Headamp.expect_cell k v = inl Headamp.REFUSE_OUT_OF_RANGE.
Proof.
  intros k v ch p H H0. unfold Headamp.expect_cell. rewrite H. cbv beta iota zeta.
  unfold hvm_top in H0. destruct H0 as [L|L].
  - rewrite (proj2 (Z.ltb_lt _ _) L). reflexivity.
  - rewrite (proj2 (Z.ltb_lt _ _) L), orb_true_r. reflexivity.
Qed.

Lemma hvm_valid : forall ch p val, 0 <= ch < Headamp.HA_CHANNELS ->
  (p = Headamp.HA_PHANTOM \/ p = Headamp.HA_PAD \/ p = Headamp.HA_SENS) -> 0 <= val <= hvm_top p ->
  Headamp.cell_valid (ch, p, val).
Proof.
  intros ch p val Hc Hp Hv. unfold Headamp.cell_valid. cbv beta iota. unfold hvm_top in Hv.
  split; [exact Hc|]. split; [|exact Hv].
  destruct Hp as [-> | [-> | ->]]; unfold Headamp.HA_PHANTOM, Headamp.HA_PAD, Headamp.HA_SENS; lia.
Qed.

(** ** The inlined pod_nearest, from NearVal *)
Lemma hvm_pnt : forall b, NearVal.pn_t b = fst (fp_to_int fmt_single RTZ true 64 b).
Proof. intros b. reflexivity. Qed.

Lemma hvm_pnr_eq : forall b, 0 <= b < 2^32 ->
  NearVal.pn_r b =
  (if 0 <=? SF.f128_ge (SF.f128_sub (C_extendsftf2.f128_of_f32 b) (C_floatditf.f128_of_i64 (NearVal.pn_t b)))
                       NearSF.HALF_128 then NearVal.pn_t b + 1
   else if SF.f128_le (SF.f128_sub (C_extendsftf2.f128_of_f32 b) (C_floatditf.f128_of_i64 (NearVal.pn_t b)))
                      NearSF.MHALF_128 <? 0 then NearVal.pn_t b - 1
   else NearVal.pn_t b).
Proof. intros b Hb. exact (NearVal.pn_r_eq b Hb). Qed.

Lemma hvm_hn_nan : forall b, fst (fp_eq fmt_single b b) = false -> NearVal.hn_bin b = None.
Proof. intros b H. unfold NearVal.hn_bin. rewrite H. reflexivity. Qed.

Lemma hvm_hn_lo : forall b, fst (fp_lt fmt_single b 0xbf800000) = true -> NearVal.hn_bin b = None.
Proof.
  intros b H. unfold NearVal.hn_bin. rewrite H. destruct (negb (fst (fp_eq fmt_single b b))); reflexivity.
Qed.

Lemma hvm_hn_hi : forall b, fst (fp_lt fmt_single 0x43800000 b) = true -> NearVal.hn_bin b = None.
Proof.
  intros b H. unfold NearVal.hn_bin. rewrite H.
  destruct (negb (fst (fp_eq fmt_single b b))); [reflexivity|].
  destruct (fst (fp_lt fmt_single b 0xbf800000)); reflexivity.
Qed.

Lemma hvm_hn_body : forall b, fst (fp_eq fmt_single b b) = true -> fst (fp_lt fmt_single b 0xbf800000) = false ->
  fst (fp_lt fmt_single 0x43800000 b) = false ->
  NearVal.hn_bin b = (if 255 <? NearVal.pn_r b mod 2^64 then None else Some (NearVal.pn_r b mod 2^64)).
Proof. intros b H1 H2 H3. unfold NearVal.hn_bin. rewrite H1, H2, H3. reflexivity. Qed.

Lemma hvm_hn_nearest : forall b, 0 <= b < 2^32 -> NearVal.hn_bin b = Nearest.nearest b 0 255.
Proof. exact NearVal.hn_bin_nearest. Qed.

Lemma hvm_hn_range : forall b n, NearVal.hn_bin b = Some n -> 0 <= n <= 255.
Proof. exact NearVal.hn_bin_range. Qed.

(** ** The register pairs the soft-float calls pass (low word + 2^64 * high word) *)
Lemma hvm_w128 : forall x, 0 <= x < 2^128 -> SF.lo64 x + 2^64 * SF.hi64 x = x.
Proof. exact SFSub.words128. Qed.

Lemma hvm_lo64_rng : forall x, 0 <= SF.lo64 x < 2^64.
Proof. intros x. unfold SF.lo64. apply SF.wrap64_range. Qed.

Lemma hvm_hi64_rng : forall x, 0 <= SF.hi64 x < 2^64.
Proof. intros x. unfold SF.hi64. apply SF.wrap64_range. Qed.

Lemma hvm_ext_range : forall v, 0 <= C_extendsftf2.f128_of_f32 v < 2^128.
Proof. exact SFVal.f128_of_f32_range. Qed.

Lemma hvm_fd_range : forall t, 0 <= C_floatditf.f128_of_i64 t < 2^128.
Proof. exact SFVal.f128_of_i64_range. Qed.

Lemma hvm_sub_range : forall a b, 0 <= SF.f128_sub a b < 2^128.
Proof. exact SFSub.f128_sub_range. Qed.

(** 0.5L and -0.5L: the walk loads the two high words (R+0xb0, R+0xa8) and passes a2 = 0 as the low word. *)
Lemma hvm_half_rng :
  0 <= NearSF.HALF_128 < 2^128 /\ 0 <= NearSF.MHALF_128 < 2^128 /\
  SF.lo64 NearSF.HALF_128 = 0 /\ SF.lo64 NearSF.MHALF_128 = 0 /\
  SF.hi64 NearSF.HALF_128 = 0x3ffe000000000000 /\ SF.hi64 NearSF.MHALF_128 = 0xbffe000000000000.
Proof.
  split; [unfold NearSF.HALF_128; lia|]. split; [unfold NearSF.MHALF_128; lia|].
  refine (conj _ (conj _ (conj _ _))); vm_compute; reflexivity.
Qed.

Lemma hvm_f128_fbox : forall b, 0 <= b < 2^32 ->
  C_extendsftf2.f128_of_f32 (NearVal.fbox b) = C_extendsftf2.f128_of_f32 b.
Proof.
  intros b Hb. rewrite (SFVal.f128_of_f32_low (NearVal.fbox b)), (NearVal.fbox_mod b Hb). reflexivity.
Qed.

Lemma hvm_fd_wrap : forall q, C_floatditf.f128_of_i64 (int_wrap 64 q) = C_floatditf.f128_of_i64 q.
Proof. exact NearVal.i64_wrap. Qed.

(** ** NaN boxing (`flw` writes a NaN-boxed single; `feq.s`, `flt.s`, `fcvt.l.s` and `fmv.s` unbox it) *)
Lemma hvm_lor_shift_add : forall a v n, 0 <= n -> 0 <= v < 2^n -> Z.lor (a * 2^n) v = a * 2^n + v.
Proof.
  intros a v n Hn Hv.
  assert (L : Z.land (a * 2^n) v = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i n) as [H|H].
    - rewrite Z.mul_pow2_bits_low by lia. reflexivity.
    - rewrite <- (Z.mod_small v (2^n)) by lia. rewrite Z.mod_pow2_bits_high by lia. apply andb_false_r. }
  rewrite <- Z.lxor_lor by exact L. rewrite Z.add_nocarry_lxor by exact L. reflexivity.
Qed.

Lemma hvm_u32_lit : forall z, 0 <= z < 2^32 -> bv_unsigned (Z_to_bv 32 z) = z.
Proof.
  intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus.
  change (2 ^ Z.of_N 32) with (2^32). lia.
Qed.

Lemma hvm_nan_box_word : forall v : bv 32, bv_unsigned (Sem.nan_box v) = 4294967295 * 2^32 + bv_unsigned v.
Proof.
  intros v. unfold Sem.nan_box. rewrite bv_concat_unsigned by reflexivity.
  pose proof (bv_unsigned_in_range 32 v) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 32) with (2^32) in R.
  replace (bv_unsigned (Z_to_bv 32 (-1))) with 4294967295 by (vm_compute; reflexivity).
  change (Z.of_N 32) with 32. rewrite Z.shiftl_mul_pow2 by lia. apply hvm_lor_shift_add; lia.
Qed.

Lemma hvm_unbox_box : forall v : bv 32, Sem.unbox_s (Sem.nan_box v) = v.
Proof.
  intros v. pose proof (bv_unsigned_in_range 32 v) as R. unfold bv_modulus in R.
  change (2 ^ Z.of_N 32) with (2^32) in R.
  unfold Sem.unbox_s, Sem.low32. rewrite bv_extract_unsigned, hvm_nan_box_word. change (Z.of_N 32) with 32.
  rewrite Z.shiftr_div_pow2 by lia.
  replace ((4294967295 * 2^32 + bv_unsigned v) / 2^32) with 4294967295
    by (rewrite Z.div_add_l by lia; rewrite (Z.div_small (bv_unsigned v)) by lia; lia).
  replace (bv_wrap 32 4294967295 =? Z.ones 32) with true by (vm_compute; reflexivity).
  apply bv_eq. rewrite bv_extract_unsigned, hvm_nan_box_word. change (Z.of_N 0) with 0. rewrite Z.shiftr_0_r.
  unfold bv_wrap. change (bv_modulus 32) with (2^32).
  rewrite Z.add_comm, Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma hvm_box_unsigned : forall b, 0 <= b < 2^32 -> bv_unsigned (Sem.unbox_s (Sem.nan_box (Z_to_bv 32 b))) = b.
Proof. intros b Hb. rewrite hvm_unbox_box. apply hvm_u32_lit. exact Hb. Qed.

Lemma hvm_sgnj_self : forall v : bv 32, Sem.sgnj_val F_SGNJ v v = v.
Proof.
  intros v. pose proof (bv_unsigned_in_range 32 v) as R. unfold bv_modulus in R.
  change (2 ^ Z.of_N 32) with (2^32) in R.
  apply bv_eq. unfold Sem.sgnj_val, bit. cbv zeta.
  rewrite bv_concat_unsigned by reflexivity.
  rewrite bv_extract_unsigned, Z_to_bv_unsigned. change (Z.of_N 0) with 0. rewrite Z.shiftr_0_r.
  change (Z.of_N (32 - 1)) with 31.
  unfold bv_wrap. change (bv_modulus (32 - 1)) with (2^31). change (bv_modulus 1) with 2.
  apply Z.bits_inj'. intros i Hi. rewrite Z.lor_spec.
  destruct (Z.lt_ge_cases i 31) as [H1|H1].
  - rewrite Z.shiftl_spec_low by lia. rewrite Z.mod_pow2_bits_low by lia. reflexivity.
  - rewrite Z.mod_pow2_bits_high by lia. rewrite orb_false_r. rewrite Z.shiftl_spec by lia.
    destruct (Z.eqb_spec i 31) as [->|Hne].
    + destruct (Z.testbit (bv_unsigned v) 31); reflexivity.
    + assert (Hi31 : 0 < i - 31) by lia.
      assert (Hv : Z.testbit (bv_unsigned v) i = false).
      { rewrite <- (Z.mod_small (bv_unsigned v) (2^32)) by lia. apply Z.mod_pow2_bits_high. lia. }
      rewrite Hv. destruct (Z.testbit (bv_unsigned v) 31).
      * change ((if true then 1 else 0) mod 2) with 1.
        apply Z.bits_above_log2; [apply Z.le_0_1 | change (Z.log2 1) with 0; exact Hi31].
      * change ((if false then 1 else 0) mod 2) with 0. apply Z.bits_0.
Qed.

(** ** Assumptions *)
Print Assumptions hvm_sx_range.
Print Assumptions hvm_sx_id.
Print Assumptions hvm_sx_eq.
Print Assumptions hvm_sx_zero.
Print Assumptions hvm_sx_256.
Print Assumptions hvm_sx_s32.
Print Assumptions hvm_cv_bool.
Print Assumptions hvm_cv_int.
Print Assumptions hvm_cv_float.
Print Assumptions hvm_cv_small.
Print Assumptions hvm_cv_other.
Print Assumptions hvm_cv_range.
Print Assumptions hvm_ent_bounds.
Print Assumptions hvm_key_cell.
Print Assumptions hvm_top_range.
Print Assumptions hvm_top_bounds.
Print Assumptions hvm_cell_inr.
Print Assumptions hvm_cell_inl.
Print Assumptions hvm_valid.
Print Assumptions hvm_pnt.
Print Assumptions hvm_pnr_eq.
Print Assumptions hvm_hn_nan.
Print Assumptions hvm_hn_lo.
Print Assumptions hvm_hn_hi.
Print Assumptions hvm_hn_body.
Print Assumptions hvm_hn_nearest.
Print Assumptions hvm_hn_range.
Print Assumptions hvm_w128.
Print Assumptions hvm_lo64_rng.
Print Assumptions hvm_hi64_rng.
Print Assumptions hvm_ext_range.
Print Assumptions hvm_fd_range.
Print Assumptions hvm_sub_range.
Print Assumptions hvm_half_rng.
Print Assumptions hvm_f128_fbox.
Print Assumptions hvm_fd_wrap.
Print Assumptions hvm_lor_shift_add.
Print Assumptions hvm_u32_lit.
Print Assumptions hvm_nan_box_word.
Print Assumptions hvm_unbox_box.
Print Assumptions hvm_box_unsigned.
Print Assumptions hvm_sgnj_self.
