(** The value of the inlined pod_nearest(f, 0, 255) in the plain LLVMFuzzerTestOneInput (0x14548 -> 0x145e8 /
    0x1464c; pod.h:152-171 with lo = 0, hi = 255, cell_value at fuzz_headamp.c:105): [hn_bin], the result as the
    machine computes it register by register, equals Pod/Nearest.v's [nearest] at (0, 255): [hn_bin_nearest].

    The machine model: NaN by feq.s; the range test d < lo - 1 || d > hi + 1 made in binary32, f < -1.0f and
    256.0f < f by flt.s; d = __extendsftf2(f), t = fcvt.l.s rtz f, frac = d - __floatditf(t) (__subtf3), r = t + 1
    when frac >= 1/2 (__getf2 >= 0), t - 1 when frac < -1/2 (__lttf2 < 0), else t; then the unsigned test 255 < r
    of the 64-bit word r. fuzz_role's pod_nearest value layer (Prog/pod_nearest.v, at (INT32_MIN, INT32_MAX)) with
    its binary128 value facts taken from CJ/Spec/NearSF.v, SFVal.v and SFSub.v, and the range test in binary32. *)
From Stdlib Require Import ZArith NArith List Lia Bool SpecFloat.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.Spec Require SoftFloat SFVal SFSub NearSF.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.RL.G Require C_extendsftf2 C_floatditf.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Nearest.
From Flocq.IEEE754 Require BinarySingleNaN.
Import ListNotations.
Open Scope Z_scope.

Module SF := OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.Spec.SoftFloat.
Abbreviation f128_of_f32 := C_extendsftf2.f128_of_f32.
Abbreviation f128_of_i64 := C_floatditf.f128_of_i64.
(** 0.5L and -0.5L (low word + 2^64 * high word). *)
Abbreviation HALF_128 := NearSF.HALF_128.
Abbreviation MHALF_128 := NearSF.MHALF_128.

(** ** What the code computes, register by register *)
(** A binary128 value once split into a register pair (low, high) and read back as one number. *)
Definition W128 (x : Z) : Z := SF.lo64 x + 2^64 * SF.hi64 x.
(** fs0 / fa0 as a 64-bit word: the binary32 bits b, NaN-boxed (flw writes them so). *)
Definition fbox (b : Z) : Z := bv_unsigned (nan_box (Z_to_bv 32 b)).
(** t = fcvt.l.s rtz f: the 64-bit two's-complement word of trunc(f) (saturated outside the range). *)
Definition pn_t (b : Z) : Z := fst (fp_to_int fmt_single RTZ true 64 b).
(** d = __extendsftf2(f), as the register pair passes it on. *)
Definition pn_d (b : Z) : Z := W128 (f128_of_f32 (fbox b)).
(** r before the range test: frac = d - (long double)t, then t + 1 when frac >= 1/2, t - 1 when frac < -1/2, else
    t. *)
Definition pn_r (b : Z) : Z :=
  let t := pn_t b in
  let fr := W128 (SF.f128_sub (pn_d b) (W128 (f128_of_i64 t))) in
  if 0 <=? SF.f128_ge fr HALF_128 then t + 1
  else if SF.f128_le fr MHALF_128 <? 0 then t - 1 else t.
(** The inlined pod_nearest(f, 0, 255) as the machine reaches its exits: None (0x1464c) for a NaN (feq.s), for
    f < -1.0f (flt.s against 0xbf800000), for 256.0f < f (flt.s against 0x43800000), and for a 64-bit word r above
    255 unsigned (bltu); else Some r (0x145e8). *)
Definition hn_bin (b : Z) : option Z :=
  if negb (fst (fp_eq fmt_single b b)) then None
  else if fst (fp_lt fmt_single b 0xbf800000) then None
  else if fst (fp_lt fmt_single 0x43800000 b) then None
  else let r := pn_r b mod 2^64 in if 255 <? r then None else Some r.

(** ** Integer arithmetic *)
Lemma qdn : forall a c, 0 <= a -> 0 < c -> Z.quot a c = a / c.
Proof.
  intros a c Ha Hc. apply (Z.div_unique a c (Z.quot a c) (Z.rem a c)).
  - left. apply Z.rem_bound_pos; lia.
  - apply Z.quot_rem. lia.
Qed.

Lemma qopp : forall a c, 0 < c -> Z.quot (- a) c = - Z.quot a c.
Proof.
  intros a c Hc.
  pose proof (Z.quot_rem (- a) c ltac:(lia)) as H1. pose proof (Z.quot_rem a c ltac:(lia)) as H2.
  rewrite (Z.rem_opp_l a c) in H1 by lia.
  apply (Z.mul_reg_l _ _ c); lia.
Qed.

Lemma q1 : forall x, Z.quot x 1 = x.
Proof.
  intros x. destruct (Z.le_gt_cases 0 x) as [H|H].
  - rewrite qdn by lia. apply Z.div_1_r.
  - replace x with (- (- x)) by lia. rewrite qopp, qdn, Z.div_1_r by lia. reflexivity.
Qed.

(** trunc(N / D) for -2^31 - 1 <= N / D <= 2^31. *)
Lemma quot_rng : forall N D, 0 < D -> (INT32_MIN - 1) * D <= N <= (INT32_MAX + 1) * D ->
  - 2^31 - 1 <= Z.quot N D <= 2^31.
Proof.
  intros N D HD HB. unfold INT32_MIN, INT32_MAX in HB. destruct (Z.le_gt_cases 0 N) as [HN|HN].
  - rewrite qdn by lia. split.
    + pose proof (Z.div_pos N D HN HD). lia.
    + apply Z.div_le_upper_bound; lia.
  - replace N with (- (- N)) by lia. rewrite qopp, qdn by lia. split.
    + assert (- N / D <= 2^31 + 1) by (apply Z.div_le_upper_bound; lia). lia.
    + pose proof (Z.div_pos (- N) D ltac:(lia) HD). lia.
Qed.

(** ** Signed reading of a 64-bit word *)
Lemma swrap_eq : forall z, bv_swrap 64 z = (z + 2^63) mod 2^64 - 2^63.
Proof. intros z. reflexivity. Qed.

Lemma swrap_k : forall y k, - 2^63 <= y < 2^63 -> bv_swrap 64 (y + k * 2^64) = y.
Proof.
  intros y k H. rewrite swrap_eq.
  replace (y + k * 2^64 + 2^63) with (y + 2^63 + k * 2^64) by ring.
  rewrite Z.mod_add, Z.mod_small by lia. ring.
Qed.

Lemma iw_k : forall q, int_wrap 64 q = q + - (q / 2^64) * 2^64.
Proof. intros q. unfold int_wrap. rewrite Z.land_ones, Z.mod_eq by lia. ring. Qed.

Lemma swrap_iw : forall q c, - 2^63 <= q + c < 2^63 -> bv_swrap 64 (int_wrap 64 q + c) = q + c.
Proof.
  intros q c H. rewrite iw_k.
  replace (q + - (q / 2^64) * 2^64 + c) with (q + c + - (q / 2^64) * 2^64) by ring.
  apply swrap_k. exact H.
Qed.

Lemma swrap_iw0 : forall q, - 2^63 <= q < 2^63 -> bv_swrap 64 (int_wrap 64 q) = q.
Proof.
  intros q H. replace (int_wrap 64 q) with (int_wrap 64 q + 0) by ring. rewrite swrap_iw by lia. ring.
Qed.

(** The low 64 bits of a word are determined by its signed reading. *)
Lemma swrap_mod : forall x y, bv_swrap 64 x = y -> x mod 2^64 = y mod 2^64.
Proof.
  intros x y H. rewrite swrap_eq in H. subst y. rewrite Zminus_mod_idemp_l. f_equal. ring.
Qed.

(** ** The NaN-boxed register keeps b in its low word *)
Lemma fbox_mod : forall b, 0 <= b < 2^32 -> fbox b mod 2^32 = b.
Proof.
  intros b Hb. unfold fbox, nan_box. rewrite bv_concat_unsigned by reflexivity.
  rewrite !Z_to_bv_unsigned. change (bv_wrap 32 b) with (b mod 2^32). rewrite (Z.mod_small b) by lia.
  change (Z.of_N 32) with 32. generalize (bv_wrap 32 (-1)). intros X.
  apply Z.bits_inj'. intros i Hi. destruct (Z.lt_ge_cases i 32).
  - rewrite Z.mod_pow2_bits_low, Z.lor_spec, Z.shiftl_spec_low by lia. reflexivity.
  - rewrite Z.mod_pow2_bits_high by lia. rewrite <- (Z.mod_small b (2^32)) by lia.
    rewrite Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

(** ** The register pairs read back as the binary128 values *)
Lemma W128_id : forall x, 0 <= x < 2^128 -> W128 x = x.
Proof. intros x Hx. unfold W128. apply SFSub.words128. exact Hx. Qed.

Lemma pn_d_eq : forall b, 0 <= b < 2^32 -> pn_d b = f128_of_f32 b.
Proof.
  intros b Hb. unfold pn_d.
  rewrite (SFVal.f128_of_f32_low (fbox b)), (fbox_mod b Hb). apply W128_id. apply SFVal.f128_of_f32_range.
Qed.

Lemma i64_wrap : forall q, f128_of_i64 (int_wrap 64 q) = f128_of_i64 q.
Proof.
  intros q. assert (Iw : int_wrap 64 q = q mod 2^64) by (unfold int_wrap; apply Z.land_ones; lia).
  assert (E : SF.wrap64 (int_wrap 64 q) = SF.wrap64 q).
  { rewrite Iw, !SF.wrap64_mod. rewrite Z.mod_mod by lia. reflexivity. }
  unfold C_floatditf.f128_of_i64. rewrite E. reflexivity.
Qed.

Lemma pn_r_eq : forall b, 0 <= b < 2^32 ->
  pn_r b = (if 0 <=? SF.f128_ge (SF.f128_sub (f128_of_f32 b) (f128_of_i64 (pn_t b))) HALF_128 then pn_t b + 1
            else if SF.f128_le (SF.f128_sub (f128_of_f32 b) (f128_of_i64 (pn_t b))) MHALF_128 <? 0 then pn_t b - 1
            else pn_t b).
Proof.
  intros b Hb. unfold pn_r. cbv zeta.
  rewrite (pn_d_eq b Hb), (W128_id (f128_of_i64 (pn_t b))) by apply SFVal.f128_of_i64_range.
  rewrite (W128_id (SF.f128_sub _ _)) by apply SFSub.f128_sub_range. reflexivity.
Qed.

(** ** fp_decode of a binary32 pattern *)
Lemma dec_fin : forall b s m e, fp_decode fmt_single b = S754_finite s m e ->
  Zpos m < 16777216 /\ -149 <= e <= 104 /\ (e = -149 \/ 8388608 <= Zpos m).
Proof.
  intros b s m e. unfold fp_decode, fp_exp_field, fp_man_field. cbv zeta.
  change (fp_mw fmt_single) with 23. change (fp_ew fmt_single) with 8.
  change (fp_emin fmt_single) with (-149).
  rewrite !Z.land_ones by lia. change (Z.ones 8) with 255. change (Z.shiftl 1 23) with 8388608.
  pose proof (Z.mod_pos_bound (Z.shiftr b 23) (2^8) ltac:(lia)) as Hef.
  pose proof (Z.mod_pos_bound b (2^23) ltac:(lia)) as Hmf.
  set (ef := Z.shiftr b 23 mod 2^8) in *. set (mf := b mod 2^23) in *. clearbody ef mf.
  change (2^8) with 256 in Hef. change (2^23) with 8388608 in Hmf.
  destruct (Z.eqb_spec ef 0) as [E0|E0].
  - destruct mf as [|p|p]; intros H; try discriminate H.
    injection H as Hs Hp He. subst. lia.
  - destruct (Z.eqb_spec ef 255) as [E1|E1].
    + destruct (mf =? 0); intros H; discriminate H.
    + destruct (8388608 + mf) as [|p|p] eqn:Ep; intros H; try discriminate H.
      injection H as Hs Hp He. subst. lia.
Qed.

Lemma isnan_dec : forall b, fp_is_nan fmt_single b = true -> fp_decode fmt_single b = S754_nan.
Proof.
  intros b H. unfold fp_is_nan in H. apply andb_prop in H as [H1 H2].
  apply Z.eqb_eq in H1. apply negb_true_iff in H2.
  unfold fp_decode. cbv zeta. rewrite H1, H2. reflexivity.
Qed.

Lemma ratio_notnan : forall b N D, f32_ratio b = Some (N, D) -> fp_is_nan fmt_single b = false.
Proof.
  intros b N D HR. destruct (fp_is_nan fmt_single b) eqn:E; [|reflexivity].
  apply isnan_dec in E. unfold f32_ratio in HR. rewrite E in HR. discriminate HR.
Qed.

Lemma ratio_none : forall b, f32_ratio b = None ->
  fp_decode fmt_single b = S754_nan \/ fp_decode fmt_single b = S754_infinity true \/
  fp_decode fmt_single b = S754_infinity false.
Proof.
  intros b. unfold f32_ratio. cbv zeta.
  destruct (fp_decode fmt_single b) as [s|s| |s m e]; intros H; try discriminate H.
  - destruct s; [right; left | right; right]; reflexivity.
  - left. reflexivity.
Qed.

(** -1.0f and 256.0f as binary32. *)
Lemma Dm1 : fp_decode fmt_single 0xbf800000 = S754_finite true 8388608 (-23).
Proof. vm_compute. reflexivity. Qed.
Lemma D256 : fp_decode fmt_single 0x43800000 = S754_finite false 8388608 (-15).
Proof. vm_compute. reflexivity. Qed.

(** ** feq.s and flt.s *)
Lemma sfc_ff : forall m1 e1 m2 e2, SFcompare (S754_finite false m1 e1) (S754_finite false m2 e2) =
  Some (match Z.compare e1 e2 with Lt => Lt | Gt => Gt | Eq => Pos.compare m1 m2 end).
Proof. intros. reflexivity. Qed.
Lemma sfc_tt : forall m1 e1 m2 e2, SFcompare (S754_finite true m1 e1) (S754_finite true m2 e2) =
  Some (match Z.compare e1 e2 with Lt => Gt | Gt => Lt | Eq => CompOpp (Pos.compare m1 m2) end).
Proof. intros. reflexivity. Qed.

Lemma feq_nan : forall b, fp_decode fmt_single b = S754_nan -> fst (fp_eq fmt_single b b) = false.
Proof. intros b H. unfold fp_eq, fp_compare. rewrite H. reflexivity. Qed.

Lemma feq_inf : forall b s, fp_decode fmt_single b = S754_infinity s -> fst (fp_eq fmt_single b b) = true.
Proof. intros b s H. unfold fp_eq, fp_compare. rewrite H. destruct s; reflexivity. Qed.

Lemma feq_ratio : forall b N D, f32_ratio b = Some (N, D) -> fst (fp_eq fmt_single b b) = true.
Proof.
  intros b N D. unfold fp_eq, fp_compare, f32_ratio. cbn [fst]. cbv zeta.
  destruct (fp_decode fmt_single b) as [s|s| |s m e]; intros HR; try discriminate HR.
  - reflexivity.
  - destruct s; [rewrite sfc_tt | rewrite sfc_ff]; rewrite Z.compare_refl, Pos.compare_refl; reflexivity.
Qed.

(** flt.s f < -1.0f, for f = N / D. *)
Lemma flt_m1 : forall b N D, f32_ratio b = Some (N, D) ->
  fst (fp_lt fmt_single b 0xbf800000) = (N <? - D).
Proof.
  intros b N D. unfold fp_lt, fp_compare, f32_ratio. cbn [fst]. rewrite Dm1. cbv zeta.
  destruct (fp_decode fmt_single b) as [s|s| |s m e] eqn:Hd; intros HR; try discriminate HR.
  - injection HR as HN HD. subst N D. reflexivity.
  - pose proof (dec_fin b s m e Hd) as (Hm & He & Hn). clear Hd. revert HR.
    destruct s; destruct (Z.leb_spec 0 e) as [He0|He0]; cbv iota; intros HR; injection HR as HN HD; subst N D.
    + rewrite sfc_tt. destruct (Z.compare_spec e (-23)) as [E|E|E]; [exfalso; lia | exfalso; lia |]. cbv iota.
      symmetry. apply Z.ltb_lt.
      assert (1 <= 2^e) by (pose proof (Z.pow_pos_nonneg 2 e ltac:(lia) He0); lia). nia.
    + rewrite sfc_tt. destruct (Z.compare_spec e (-23)) as [E|E|E]; cbv iota.
      * subst e. change (2^(- -23)) with 8388608.
        destruct (Pos.compare_spec m 8388608) as [Em|Em|Em]; cbn [CompOpp]; cbv iota.
        -- subst m. reflexivity.
        -- assert (Em' : Zpos m < 8388608) by exact Em. clear Em. symmetry. apply Z.ltb_ge. lia.
        -- assert (Em' : 8388608 < Zpos m) by exact Em. clear Em. symmetry. apply Z.ltb_lt. lia.
      * symmetry. apply Z.ltb_ge.
        assert (16777216 <= 2^(-e)) by (change 16777216 with (2^24); apply Z.pow_le_mono_r; lia). lia.
      * symmetry. apply Z.ltb_lt.
        assert (2^(-e) <= 4194304) by (change 4194304 with (2^22); apply Z.pow_le_mono_r; lia). lia.
    + transitivity false; [reflexivity|]. symmetry. apply Z.ltb_ge.
      assert (0 <= Zpos m * 2^e) by (apply Z.mul_nonneg_nonneg; [lia | apply Z.pow_nonneg; lia]). lia.
    + transitivity false; [reflexivity|]. symmetry. apply Z.ltb_ge.
      assert (0 < 2^(-e)) by (apply Z.pow_pos_nonneg; lia). lia.
Qed.

(** flt.s 256.0f < f, for f = N / D. *)
Lemma flt_256 : forall b N D, f32_ratio b = Some (N, D) ->
  fst (fp_lt fmt_single 0x43800000 b) = (256 * D <? N).
Proof.
  intros b N D. unfold fp_lt, fp_compare, f32_ratio. cbn [fst]. rewrite D256. cbv zeta.
  destruct (fp_decode fmt_single b) as [s|s| |s m e] eqn:Hd; intros HR; try discriminate HR.
  - injection HR as HN HD. subst N D. reflexivity.
  - pose proof (dec_fin b s m e Hd) as (Hm & He & Hn). clear Hd. revert HR.
    destruct s; destruct (Z.leb_spec 0 e) as [He0|He0]; cbv iota; intros HR; injection HR as HN HD; subst N D.
    + transitivity false; [reflexivity|]. symmetry. apply Z.ltb_ge.
      assert (0 <= Zpos m * 2^e) by (apply Z.mul_nonneg_nonneg; [lia | apply Z.pow_nonneg; lia]). lia.
    + transitivity false; [reflexivity|]. symmetry. apply Z.ltb_ge.
      assert (0 < 2^(-e)) by (apply Z.pow_pos_nonneg; lia). lia.
    + rewrite sfc_ff. destruct (Z.compare_spec (-15) e) as [E|E|E]; [exfalso; lia | | exfalso; lia]. cbv iota.
      symmetry. apply Z.ltb_lt.
      assert (1 <= 2^e) by (pose proof (Z.pow_pos_nonneg 2 e ltac:(lia) He0); lia). nia.
    + rewrite sfc_ff. destruct (Z.compare_spec (-15) e) as [E|E|E]; cbv iota.
      * subst e. change (2^(- -15)) with 32768.
        destruct (Pos.compare_spec 8388608 m) as [Em|Em|Em]; cbv iota.
        -- subst m. reflexivity.
        -- assert (Em' : 8388608 < Zpos m) by exact Em. clear Em. symmetry. apply Z.ltb_lt. lia.
        -- assert (Em' : Zpos m < 8388608) by exact Em. clear Em. symmetry. apply Z.ltb_ge. lia.
      * symmetry. apply Z.ltb_lt.
        assert (2^(-e) <= 16384) by (change 16384 with (2^14); apply Z.pow_le_mono_r; lia). lia.
      * symmetry. apply Z.ltb_ge.
        assert (65536 <= 2^(-e)) by (change 65536 with (2^16); apply Z.pow_le_mono_r; lia). lia.
Qed.

(** The infinities: -inf < -1.0f; +inf is not below -1.0f, and 256.0f < +inf. *)
Lemma flt_minf_m1 : forall b, fp_decode fmt_single b = S754_infinity true ->
  fst (fp_lt fmt_single b 0xbf800000) = true.
Proof. intros b H. unfold fp_lt, fp_compare. rewrite Dm1, H. reflexivity. Qed.

Lemma flt_pinf_m1 : forall b, fp_decode fmt_single b = S754_infinity false ->
  fst (fp_lt fmt_single b 0xbf800000) = false.
Proof. intros b H. unfold fp_lt, fp_compare. rewrite Dm1, H. reflexivity. Qed.

Lemma flt_pinf_256 : forall b, fp_decode fmt_single b = S754_infinity false ->
  fst (fp_lt fmt_single 0x43800000 b) = true.
Proof. intros b H. unfold fp_lt, fp_compare. rewrite D256, H. reflexivity. Qed.

(** ** fcvt.l.s rtz *)
Lemma div_eucl_eq : forall a c, Z.div_eucl a c = (a / c, a mod c).
Proof. intros a c. unfold Z.div, Z.modulo. destruct (Z.div_eucl a c). reflexivity. Qed.

Lemma to_tail : forall q (p : Z * fflags) fl, - 2^63 <= q < 2^63 ->
  fst (if orb (q <? int_lo true 64) (int_hi true 64 <? q) then p else (int_wrap 64 q, fl)) = int_wrap 64 q.
Proof.
  intros q p fl Hq. change (int_lo true 64) with (- 2^63). change (int_hi true 64) with (2^63 - 1).
  rewrite (proj2 (Z.ltb_ge q (- 2^63))), (proj2 (Z.ltb_ge (2^63 - 1) q)) by lia. reflexivity.
Qed.

Lemma toint_ratio : forall b N D, f32_ratio b = Some (N, D) ->
  (INT32_MIN - 1) * D <= N <= (INT32_MAX + 1) * D -> pn_t b = int_wrap 64 (Z.quot N D).
Proof.
  intros b N D HR HB.
  pose proof (ratio_notnan b N D HR) as Hnn.
  pose proof (proj2 (near_f32_ratio b) N D HR) as HD.
  pose proof (quot_rng N D HD HB) as Hq.
  revert HR. unfold pn_t, fp_to_int, f32_ratio. cbv beta zeta. rewrite Hnn.
  cbv beta iota delta [BinarySingleNaN.choice_mode flocq_mode].
  destruct (fp_decode fmt_single b) as [s|s| |s m e] eqn:Hd; intros HR; try discriminate HR.
  - injection HR as HN HD'. subst N D. reflexivity.
  - revert HR. destruct (Z.leb_spec 0 e) as [He0|He0]; cbv iota; intros HR; injection HR as HN HD'; subst N D.
    + rewrite Z.shiftl_mul_pow2 by lia.
      assert (Hw : (if s then - (Zpos m * 2^e) else Zpos m * 2^e) =
                   Z.quot ((if s then - Zpos m else Zpos m) * 2^e) 1).
      { rewrite q1. destruct s; cbv iota; ring. }
      rewrite Hw. apply to_tail. lia.
    + rewrite Z.shiftl_1_l. rewrite div_eucl_eq. cbv iota.
      assert (Hw : (if s then - (Zpos m / 2^(-e)) else Zpos m / 2^(-e)) =
                   Z.quot (if s then - Zpos m else Zpos m) (2^(-e))).
      { destruct s; cbv iota; [rewrite qopp by lia|]; rewrite qdn by lia; reflexivity. }
      rewrite Hw. apply to_tail. lia.
Qed.

(** ** r: t + [frac >= 1/2] - [frac < -1/2] read as a signed 64-bit value is rhu_q *)
Lemma pn_r_val : forall b N D, 0 <= b < 2^32 -> f32_ratio b = Some (N, D) ->
  (INT32_MIN - 1) * D <= N <= (INT32_MAX + 1) * D -> bv_swrap 64 (pn_r b) = rhu_q N D.
Proof.
  intros b N D Hb HR HB.
  pose proof (proj2 (near_f32_ratio b) N D HR) as HD.
  pose proof (NearSF.near_sf_frac b N D Hb HR HB) as F9. cbv zeta in F9. destruct F9 as [G1 G2].
  rewrite (pn_r_eq b Hb), (toint_ratio b N D HR HB), i64_wrap, G1, G2.
  pose proof (quot_rng N D HD HB) as Hq.
  unfold rhu_q. set (q := Z.quot N D) in *.
  destruct (Z.leb_spec D (2 * (N - q * D))) as [C1|C1]; destruct (Z.ltb_spec (2 * (N - q * D)) (- D)) as [C2|C2];
    cbv iota.
  - exfalso. lia.
  - rewrite swrap_iw by lia. ring.
  - replace (int_wrap 64 q - 1) with (int_wrap 64 q + -1) by ring. rewrite swrap_iw by lia. ring.
  - rewrite swrap_iw0 by lia. ring.
Qed.

(** In the byte range's pre-filter -1 <= f <= 256, r mod 2^64 is rhu_q mod 2^64, and rhu_q lies in [-1, 256]. *)
Lemma pn_r_mod : forall b N D, 0 <= b < 2^32 -> f32_ratio b = Some (N, D) -> - D <= N <= 256 * D ->
  pn_r b mod 2^64 = rhu_q N D mod 2^64.
Proof.
  intros b N D Hb HR HB. pose proof (proj2 (near_f32_ratio b) N D HR) as HD.
  apply swrap_mod. apply pn_r_val; [exact Hb | exact HR |]. unfold INT32_MIN, INT32_MAX. lia.
Qed.

Lemma rhu_rng : forall N D, 0 < D -> - D <= N <= 256 * D -> -1 <= rhu_q N D <= 256.
Proof.
  intros N D HD HB. rewrite rhu_q_eq by exact HD. split.
  - apply Z.div_le_lower_bound; lia.
  - assert ((2 * N + D) / (2 * D) < 257) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.

(** The unsigned test 255 < r of the 64-bit word r against pod_nearest's range test 0 <= r <= 255. *)
Lemma byte_test : forall r, -1 <= r <= 256 ->
  (if 255 <? r mod 2^64 then None else Some (r mod 2^64)) =
  (if (0 <=? r) && (r <=? 255) then Some r else None).
Proof.
  intros r Hr. destruct (Z.eq_dec r (-1)) as [->|Hn].
  - reflexivity.
  - rewrite (Z.mod_small r) by lia.
    destruct (Z.ltb_spec 255 r); destruct (Z.leb_spec 0 r); destruct (Z.leb_spec r 255); cbn [andb];
      first [reflexivity | exfalso; lia].
Qed.

(** ** The theorem: the machine model is [nearest] at (0, 255) *)
Theorem hn_bin_nearest : forall b, 0 <= b < 2^32 -> hn_bin b = nearest b 0 255.
Proof.
  intros b Hb. rewrite <- pod_nearest_exact_eq. unfold hn_bin, pod_nearest_exact.
  destruct (f32_ratio b) as [[N D]|] eqn:HR; cbv beta iota.
  - pose proof (proj2 (near_f32_ratio b) N D HR) as HD.
    rewrite (feq_ratio b N D HR), (flt_m1 b N D HR), (flt_256 b N D HR). cbn [negb].
    replace ((0 - 1) * D) with (- D) by ring. replace ((255 + 1) * D) with (256 * D) by ring.
    destruct (Z.ltb_spec N (- D)) as [H1|H1]; [reflexivity|].
    destruct (Z.ltb_spec (256 * D) N) as [H2|H2]; [reflexivity|]. cbn [orb]. cbv zeta.
    rewrite (pn_r_mod b N D Hb HR (conj H1 H2)). apply byte_test. apply rhu_rng; lia.
  - destruct (ratio_none b HR) as [Hd|[Hd|Hd]].
    + rewrite (feq_nan b Hd). reflexivity.
    + rewrite (feq_inf b true Hd), (flt_minf_m1 b Hd). reflexivity.
    + rewrite (feq_inf b false Hd), (flt_pinf_m1 b Hd), (flt_pinf_256 b Hd). reflexivity.
Qed.

(** Some n of the machine model lies in [0, 255]. *)
Lemma hn_bin_range : forall b n, hn_bin b = Some n -> 0 <= n <= 255.
Proof.
  intros b n. unfold hn_bin.
  destruct (negb (fst (fp_eq fmt_single b b))); [discriminate|].
  destruct (fst (fp_lt fmt_single b 0xbf800000)); [discriminate|].
  destruct (fst (fp_lt fmt_single 0x43800000 b)); [discriminate|]. cbv zeta.
  pose proof (Z.mod_pos_bound (pn_r b) (2^64) ltac:(lia)) as R.
  destruct (Z.ltb_spec 255 (pn_r b mod 2^64)) as [L|L]; [discriminate|]. intros E. injection E as <-. lia.
Qed.
