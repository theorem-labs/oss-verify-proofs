(** pod_nearest of fuzz_rate's plain build (0x14884): proof of [pod_nearest_contract] (Prog/pod_nearest_c.v) from
    the contracts of its soft-float callees (__extendsftf2, __lttf2 = __cmptf2, __floatditf, __subtf3 with __addtf3,
    __getf2) and the binary128 value facts [near_sf_facts].

    The proof has two halves.
      - The value half: [pn_bin], the result as the machine computes it register by register (feq.s, flt.s, the
        binary128 mirrors, fcvt.l.s rtz, sext.w), equals Pod/Nearest.v's [nearest] at (INT32_MIN, INT32_MAX):
        [pn_bin_nearest]. [pn_traps] gives the three facts the UBSan build's sanitizer checks need
        (U/Prog/pod_nearest.v).
      - The walk: [body] steps the 67 instructions with this library's tactics, reaches the callees through the
        bridge from the CJ library's evt (CJBridge.v; [br_ext], [br_le], [br_ge], [br_fd], [br_sub]) and ends at the
        contract's post with [pn_bin b]; [pod_nearest_of_bin] turns it into the contract. *)
From Stdlib Require Import ZArith NArith List Lia Bool SpecFloat.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Spec Require SoftFloat.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.G Require C_extendsftf2 C_floatditf.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Nearest.
Import ListNotations.
Open Scope Z_scope.

Module SF := OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Spec.SoftFloat.
Abbreviation f128_of_f32 := C_extendsftf2.f128_of_f32.
Abbreviation f128_of_i64 := C_floatditf.f128_of_i64.

(** ** The binary128 constants pod_nearest loads (low word + 2^64 * high word) *)
(** (long double)INT32_MIN - 1 = -2147483649, the bound of the test d < lo - 1. *)
Definition C1_128 : Z := 2^64 * 0xc01e000000020000.
(** -2^63 - 1, the UBSan float-cast-overflow lower bound. *)
Definition C2_128 : Z := 0x0002000000000000 + 2^64 * 0xc03e000000000000.
(** 0.5L and -0.5L. *)
Definition HALF_128 : Z := 2^64 * 0x3ffe000000000000.
Definition MHALF_128 : Z := 2^64 * 0xbffe000000000000.

(** ** What the code computes, register by register *)
(** A binary128 value once split into a register pair (low, high) and read back as one number. *)
Definition W128 (x : Z) : Z := SF.lo64 x + 2^64 * SF.hi64 x.
(** fa0 as a 64-bit word: the binary32 bits b, NaN-boxed (flw writes them so). *)
Definition fbox (b : Z) : Z := bv_unsigned (nan_box (Z_to_bv 32 b)).
(** t = fcvt.l.s rtz f: the 64-bit two's-complement word of trunc(f) (saturated outside the range). *)
Definition pn_t (b : Z) : Z := fst (fp_to_int fmt_single RTZ true 64 b).
(** d = __extendsftf2(f), as the register pair passes it on. *)
Definition pn_d (b : Z) : Z := W128 (f128_of_f32 (fbox b)).
(** r before the range test: frac = d - (long double)t, then t + 1 when frac >= 1/2 (__getf2 >= 0), t - 1 when
    frac < -1/2 (__lttf2 < 0), else t; a 64-bit value read without wrapping. *)
Definition pn_r (b : Z) : Z :=
  let t := pn_t b in
  let fr := W128 (SF.f128_sub (pn_d b) (W128 (f128_of_i64 t))) in
  if 0 <=? SF.f128_ge fr HALF_128 then t + 1
  else if SF.f128_le fr MHALF_128 <? 0 then t - 1 else t.
(** pod_nearest's result as the machine reaches it: None for a NaN (feq.s), for 2^31 < f (flt.s), for d < C1
    (__lttf2), and for an r that does not fit in 32 bits (sext.w); else Some r, r read as a signed 64-bit value. *)
Definition pn_bin (b : Z) : option Z :=
  if negb (fst (fp_eq fmt_single b b)) then None
  else if fst (fp_lt fmt_single 0x4f000000 b) then None
  else if SF.f128_le (pn_d b) C1_128 <? 0 then None
  else let r := bv_swrap 64 (pn_r b) in
       if (-2^31 <=? r) && (r <? 2^31) then Some r else None.

(** ** The binary128 value facts the proof rests on (proved in lib/CJ/Spec/NearSF.v, SFVal.v, SFSub.v) *)
Definition near_sf_facts : Prop :=
  (forall x, f128_of_f32 x = f128_of_f32 (x mod 2^32)) /\
  (forall x, 0 <= f128_of_f32 x < 2^128) /\
  (forall x, 0 <= f128_of_i64 x < 2^128) /\
  (forall a c, 0 <= SF.f128_sub a c < 2^128) /\
  (forall x, 0 <= x < 2^128 -> SF.lo64 x + 2^64 * SF.hi64 x = x) /\
  (forall b, 0 <= b < 2^32 -> fp_decode fmt_single b = S754_infinity true ->
     SF.f128_le (f128_of_f32 b) C1_128 = -1) /\
  (forall b N D, 0 <= b < 2^32 -> f32_ratio b = Some (N, D) ->
     (SF.f128_le (f128_of_f32 b) C1_128 <? 0) = (N <? (INT32_MIN - 1) * D)) /\
  (forall b N D, 0 <= b < 2^32 -> f32_ratio b = Some (N, D) -> (INT32_MIN - 1) * D <= N ->
     SF.f128_ge (f128_of_f32 b) C2_128 = 1) /\
  (forall b N D, 0 <= b < 2^32 -> f32_ratio b = Some (N, D) -> (INT32_MIN - 1) * D <= N <= (INT32_MAX + 1) * D ->
     let t := Z.quot N D in let fr := SF.f128_sub (f128_of_f32 b) (f128_of_i64 t) in
     (0 <=? SF.f128_ge fr HALF_128) = (D <=? 2 * (N - t * D)) /\
     (SF.f128_le fr MHALF_128 <? 0) = (2 * (N - t * D) <? - D)).

From Flocq.IEEE754 Require BinarySingleNaN.

(** * pod_nearest's binary model is [nearest] at (INT32_MIN, INT32_MAX) *)

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

Lemma pw_ge : forall m e, 8388608 <= m -> 9 <= e -> 4294967296 <= m * 2^e.
Proof.
  intros m e Hm He. assert (H9 : 512 <= 2^e).
  { replace 512 with (2^9) by reflexivity. apply Z.pow_le_mono_r; lia. }
  apply Z.le_trans with (8388608 * 512); [lia|]. apply Z.mul_le_mono_nonneg; lia.
Qed.

Lemma pw_lt : forall m e, 0 < m < 16777216 -> 0 <= e <= 7 -> m * 2^e < 2147483648.
Proof.
  intros m e Hm He. assert (H7 : 2^e <= 128).
  { replace 128 with (2^7) by reflexivity. apply Z.pow_le_mono_r; lia. }
  assert (m * 2^e <= m * 128) by (apply Z.mul_le_mono_nonneg_l; lia). lia.
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
Lemma W128_id : near_sf_facts -> forall x, 0 <= x < 2^128 -> W128 x = x.
Proof. intros F x Hx. destruct F as (_ & _ & _ & _ & F5 & _). unfold W128. apply F5. exact Hx. Qed.

Lemma pn_d_eq : near_sf_facts -> forall b, 0 <= b < 2^32 -> pn_d b = f128_of_f32 b.
Proof.
  intros F b Hb. pose proof F as (F1 & F2 & _). unfold pn_d.
  rewrite (F1 (fbox b)), (fbox_mod b Hb). apply (W128_id F). apply F2.
Qed.

Lemma i64_wrap : forall q, f128_of_i64 (int_wrap 64 q) = f128_of_i64 q.
Proof.
  intros q. assert (Iw : int_wrap 64 q = q mod 2^64) by (unfold int_wrap; apply Z.land_ones; lia).
  assert (E : SF.wrap64 (int_wrap 64 q) = SF.wrap64 q).
  { rewrite Iw, !SF.wrap64_mod. rewrite Z.mod_mod by lia. reflexivity. }
  unfold C_floatditf.f128_of_i64. rewrite E. reflexivity.
Qed.

Lemma pn_r_eq : near_sf_facts -> forall b, 0 <= b < 2^32 ->
  pn_r b = (if 0 <=? SF.f128_ge (SF.f128_sub (f128_of_f32 b) (f128_of_i64 (pn_t b))) HALF_128 then pn_t b + 1
            else if SF.f128_le (SF.f128_sub (f128_of_f32 b) (f128_of_i64 (pn_t b))) MHALF_128 <? 0 then pn_t b - 1
            else pn_t b).
Proof.
  intros F b Hb. pose proof F as (F1 & F2 & F3 & F4 & _). unfold pn_r. cbv zeta.
  rewrite (pn_d_eq F b Hb), (W128_id F (f128_of_i64 (pn_t b))) by apply F3.
  rewrite (W128_id F (SF.f128_sub _ _)) by apply F4. reflexivity.
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

(** 2^31 and 2^63 as binary32. *)
Lemma D4f : fp_decode fmt_single 0x4f000000 = S754_finite false 8388608 8.
Proof. vm_compute. reflexivity. Qed.
Lemma D5f : fp_decode fmt_single 0x5f000000 = S754_finite false 8388608 40.
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

Lemma flt_pinf : forall b, fp_decode fmt_single b = S754_infinity false ->
  fst (fp_lt fmt_single 0x4f000000 b) = true.
Proof. intros b H. unfold fp_lt, fp_compare. rewrite D4f, H. reflexivity. Qed.

Lemma flt_minf : forall b, fp_decode fmt_single b = S754_infinity true ->
  fst (fp_lt fmt_single 0x4f000000 b) = false.
Proof. intros b H. unfold fp_lt, fp_compare. rewrite D4f, H. reflexivity. Qed.

(** flt.s 2^31 < f, for f = N / D. *)
Lemma flt_hi : forall b N D, f32_ratio b = Some (N, D) ->
  fst (fp_lt fmt_single 0x4f000000 b) = ((INT32_MAX + 1) * D <? N).
Proof.
  intros b N D. unfold fp_lt, fp_compare, f32_ratio. cbn [fst]. rewrite D4f. cbv zeta.
  change (INT32_MAX + 1) with 2147483648.
  destruct (fp_decode fmt_single b) as [s|s| |s m e] eqn:Hd; intros HR; try discriminate HR.
  - injection HR as HN HD. subst N D. reflexivity.
  - pose proof (dec_fin b s m e Hd) as (Hm & He & Hn). clear Hd. revert HR.
    destruct s; destruct (Z.leb_spec 0 e) as [He0|He0]; cbv iota; intros HR; injection HR as HN HD; subst N D.
    + transitivity false; [reflexivity|]. symmetry. apply Z.ltb_ge.
      assert (0 <= Zpos m * 2^e) by (apply Z.mul_nonneg_nonneg; [lia | apply Z.pow_nonneg; lia]). lia.
    + transitivity false; [reflexivity|]. symmetry. apply Z.ltb_ge.
      assert (0 < 2^(-e)) by (apply Z.pow_pos_nonneg; lia). lia.
    + rewrite sfc_ff. destruct (Z.compare_spec 8 e) as [E|E|E]; cbv iota.
      * subst e. change (2^8) with 256.
        destruct (Pos.compare_spec 8388608 m) as [Em|Em|Em]; cbv iota.
        -- subst m. reflexivity.
        -- symmetry. apply Z.ltb_lt. lia.
        -- exfalso. lia.
      * symmetry. apply Z.ltb_lt. pose proof (pw_ge (Zpos m) e ltac:(lia) ltac:(lia)). lia.
      * symmetry. apply Z.ltb_ge. pose proof (pw_lt (Zpos m) e ltac:(lia) ltac:(lia)). lia.
    + rewrite sfc_ff. destruct (Z.compare_spec 8 e) as [E|E|E]; cbv iota; [exfalso; lia | exfalso; lia |].
      symmetry. apply Z.ltb_ge. assert (0 < 2^(-e)) by (apply Z.pow_pos_nonneg; lia). lia.
Qed.

(** flt.s f < 2^63 for a finite f <= 2^31. *)
Lemma flt_lo : forall b N D, f32_ratio b = Some (N, D) -> N <= (INT32_MAX + 1) * D ->
  fst (fp_lt fmt_single b 0x5f000000) = true.
Proof.
  intros b N D. unfold fp_lt, fp_compare, f32_ratio. cbn [fst]. rewrite D5f. cbv zeta.
  change (INT32_MAX + 1) with 2147483648.
  destruct (fp_decode fmt_single b) as [s|s| |s m e] eqn:Hd; intros HR HN; try discriminate HR.
  - reflexivity.
  - pose proof (dec_fin b s m e Hd) as (Hm & He & Hn). clear Hd.
    destruct s; [reflexivity|].
    rewrite sfc_ff. destruct (Z.compare_spec e 40) as [E|E|E]; cbv iota; [exfalso | reflexivity | exfalso];
      revert HR HN; destruct (Z.leb_spec 0 e) as [He0|He0]; cbv iota; intros HR HN;
      injection HR as HN' HD'; subst N D; try lia;
      pose proof (pw_ge (Zpos m) e ltac:(lia) ltac:(lia)); lia.
Qed.

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
Lemma pn_r_val : near_sf_facts -> forall b N D, 0 <= b < 2^32 -> f32_ratio b = Some (N, D) ->
  (INT32_MIN - 1) * D <= N <= (INT32_MAX + 1) * D -> bv_swrap 64 (pn_r b) = rhu_q N D.
Proof.
  intros F b N D Hb HR HB. pose proof F as (_ & _ & _ & _ & _ & _ & _ & _ & F9).
  pose proof (proj2 (near_f32_ratio b) N D HR) as HD.
  specialize (F9 b N D Hb HR HB). cbv zeta in F9. destruct F9 as [G1 G2].
  rewrite (pn_r_eq F b Hb), (toint_ratio b N D HR HB), i64_wrap, G1, G2.
  pose proof (quot_rng N D HD HB) as Hq.
  unfold rhu_q. set (q := Z.quot N D) in *.
  destruct (Z.leb_spec D (2 * (N - q * D))) as [C1|C1]; destruct (Z.ltb_spec (2 * (N - q * D)) (- D)) as [C2|C2];
    cbv iota.
  - exfalso. lia.
  - rewrite swrap_iw by lia. ring.
  - replace (int_wrap 64 q - 1) with (int_wrap 64 q + -1) by ring. rewrite swrap_iw by lia. ring.
  - rewrite swrap_iw0 by lia. ring.
Qed.

(** ** The theorems *)
Theorem pn_bin_nearest : near_sf_facts -> forall b, 0 <= b < 2^32 -> pn_bin b = nearest b INT32_MIN INT32_MAX.
Proof.
  intros F b Hb. rewrite <- pod_nearest_exact_eq. unfold pn_bin, pod_nearest_exact.
  rewrite (pn_d_eq F b Hb).
  pose proof F as (_ & _ & _ & _ & _ & F6 & F7 & _).
  destruct (f32_ratio b) as [[N D]|] eqn:HR; cbv beta iota.
  - rewrite (feq_ratio b N D HR), (flt_hi b N D HR), (F7 b N D Hb HR).
    destruct (Z.ltb_spec ((INT32_MAX + 1) * D) N) as [H1|H1]; [rewrite orb_true_r; reflexivity|].
    destruct (Z.ltb_spec N ((INT32_MIN - 1) * D)) as [H2|H2]; [reflexivity|].
    rewrite (pn_r_val F b N D Hb HR (conj H2 H1)). cbv zeta.
    set (r := rhu_q N D). unfold INT32_MIN, INT32_MAX.
    destruct (Z.leb_spec (-2^31) r); destruct (Z.ltb_spec r (2^31)); destruct (Z.leb_spec r (2^31 - 1));
      first [reflexivity | exfalso; lia].
  - destruct (ratio_none b HR) as [Hd|[Hd|Hd]].
    + rewrite (feq_nan b Hd). reflexivity.
    + rewrite (feq_inf b true Hd), (flt_minf b Hd), (F6 b Hb Hd). reflexivity.
    + rewrite (feq_inf b false Hd), (flt_pinf b Hd). reflexivity.
Qed.

Theorem pn_traps : near_sf_facts -> forall b, 0 <= b < 2^32 ->
  fst (fp_eq fmt_single b b) = true -> fst (fp_lt fmt_single 0x4f000000 b) = false ->
  (SF.f128_le (pn_d b) C1_128 <? 0) = false ->
  fst (fp_lt fmt_single b 0x5f000000) = true /\ SF.f128_ge (pn_d b) C2_128 = 1 /\
  - 2^31 - 1 <= bv_swrap 64 (pn_t b) <= 2^31.
Proof.
  intros F b Hb Heq Hlt Hle. pose proof F as (_ & _ & _ & _ & _ & F6 & F7 & F8 & _).
  rewrite (pn_d_eq F b Hb) in Hle |- *.
  destruct (f32_ratio b) as [[N D]|] eqn:HR.
  - rewrite (flt_hi b N D HR) in Hlt. rewrite (F7 b N D Hb HR) in Hle.
    apply Z.ltb_ge in Hlt. apply Z.ltb_ge in Hle.
    pose proof (proj2 (near_f32_ratio b) N D HR) as HD.
    split; [|split].
    + exact (flt_lo b N D HR Hlt).
    + exact (F8 b N D Hb HR Hle).
    + rewrite (toint_ratio b N D HR (conj Hle Hlt)).
      pose proof (quot_rng N D HD (conj Hle Hlt)) as Hq.
      rewrite swrap_iw0 by lia. exact Hq.
  - exfalso. destruct (ratio_none b HR) as [Hd|[Hd|Hd]].
    + rewrite (feq_nan b Hd) in Heq. discriminate Heq.
    + rewrite (F6 b Hb Hd) in Hle. cbv in Hle. discriminate Hle.
    + rewrite (flt_pinf b Hd) in Hlt. discriminate Hlt.
Qed.

(** * The walk of the plain build's pod_nearest (0x14884, Prog/pod_nearest_c.v) *)
From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Instr Decode DecodeC.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame FP Tac.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib Require Import Img0 CJBridge.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.Reloc Require RStep.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.G Require G_letf2 G_getf2 G_subtf3.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.I Require IImgP.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Prog Require Import pod_nearest_c.
Import ListNotations.
Open Scope Z_scope.

(** ** Single-precision values in the 64-bit FP registers *)
Lemma lor_shift_add : forall a v n, 0 <= n -> 0 <= v < 2^n -> Z.lor (a * 2^n) v = a * 2^n + v.
Proof.
  intros a v n Hn Hv.
  assert (L : Z.land (a * 2^n) v = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i n) as [H|H].
    - rewrite Z.mul_pow2_bits_low by lia. reflexivity.
    - rewrite <- (Z.mod_small v (2^n)) by lia. rewrite Z.mod_pow2_bits_high by lia. apply andb_false_r. }
  rewrite <- Z.lxor_lor by exact L. rewrite Z.add_nocarry_lxor by exact L. reflexivity.
Qed.

Lemma u32_lit : forall z, 0 <= z < 2^32 -> bv_unsigned (Z_to_bv 32 z) = z.
Proof.
  intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus.
  change (2 ^ Z.of_N 32) with (2^32). lia.
Qed.

Lemma nan_box_unsigned : forall v : bv 32, bv_unsigned (nan_box v) = 4294967295 * 2^32 + bv_unsigned v.
Proof.
  intros v. unfold nan_box. rewrite bv_concat_unsigned by reflexivity.
  pose proof (bv_unsigned_in_range 32 v) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 32) with (2^32) in R.
  replace (bv_unsigned (Z_to_bv 32 (-1))) with 4294967295 by (vm_compute; reflexivity).
  change (Z.of_N 32) with 32. rewrite Z.shiftl_mul_pow2 by lia. apply lor_shift_add; lia.
Qed.

Lemma unbox_nan_box : forall v : bv 32, unbox_s (nan_box v) = v.
Proof.
  intros v. pose proof (bv_unsigned_in_range 32 v) as R. unfold bv_modulus in R.
  change (2 ^ Z.of_N 32) with (2^32) in R.
  unfold unbox_s, low32. rewrite bv_extract_unsigned, nan_box_unsigned. change (Z.of_N 32) with 32.
  rewrite Z.shiftr_div_pow2 by lia.
  replace ((4294967295 * 2^32 + bv_unsigned v) / 2^32) with 4294967295
    by (rewrite Z.div_add_l by lia; rewrite (Z.div_small (bv_unsigned v)) by lia; lia).
  replace (bv_wrap 32 4294967295 =? Z.ones 32) with true by (vm_compute; reflexivity).
  apply bv_eq. rewrite bv_extract_unsigned, nan_box_unsigned. change (Z.of_N 0) with 0. rewrite Z.shiftr_0_r.
  unfold bv_wrap. change (bv_modulus 32) with (2^32).
  rewrite Z.add_comm, Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma sgnj_self32 : forall v : bv 32, sgnj_val F_SGNJ v v = v.
Proof.
  intros v. pose proof (bv_unsigned_in_range 32 v) as R. unfold bv_modulus in R.
  change (2 ^ Z.of_N 32) with (2^32) in R.
  apply bv_eq. unfold sgnj_val, bit. cbv zeta.
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

Lemma reg_get_key : forall (R : bvmap 5 word) (r r' : bv 5),
  bv_unsigned r = bv_unsigned r' -> Sem.reg_get R r = Sem.reg_get R r'.
Proof. intros R r r' E. apply bv_eq in E. subst. reflexivity. Qed.

(** Rewrite every read of the FP register file [F] at index [k] with the hypothesis [HF] about index [k]. *)
Ltac fix_reg F HF k :=
  repeat match goal with
  | |- context [Sem.reg_get F ?r] =>
      let z := eval vm_compute in (bv_unsigned r) in
      lazymatch z with
      | k => rewrite (reg_get_key F r (Z_to_bv 5 k) eq_refl), HF
      end
  end.

(** ** The soft-float callees, through the bridge from the CJ library's evt to this library's *)
Lemma br_ext : forall (I : RStep.RImg) segs pc, @RStep.img_segs I = segs -> @RStep.sym I 0x200dc = pc ->
  @C_extendsftf2.extendsftf2_contract I ->
  forall (b : Z) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  Sem.reg_get F (Z_to_bv 5 10) = nan_box (Z_to_bv 32 b) ->
  mem_inv segs m -> MemNorm.task_mem segs m ->
  evt segs (fun ms' => exists (t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (SF.lo64 (f128_of_f32 (fbox b))))
                    (Z_to_bv 64 (SF.hi64 (f128_of_f32 (fbox b)))) a2' a3' a4' a5' a6' a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom segs) /\
      munch [] m m' /\ wmono segs m m' /\ mem_inv segs m' /\ MemNorm.task_mem segs m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom segs)).
Proof.
  intros I segs pc HI Hpc H b ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    t3 t4 t5 t6 F fc m HF MI TM.
  subst segs pc.
  pose proof (H ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
                (mem_inv_to_cj _ m MI TM)) as E.
  refine (evt_bridge _ _ _ _ _ E).
  intros ms' (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & Hms & MU & WM & MI').
  destruct (mem_inv_of_cj _ m' MI') as [MI2 TM2].
  exists t0', t1', t2', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
  refine (conj _ (conj MU (conj WM (conj MI2 TM2)))).
  rewrite Hms. fix_reg F HF 10%Z. reflexivity.
Qed.

Lemma br_le : forall (I : RStep.RImg) segs pc, @RStep.img_segs I = segs -> @RStep.sym I 0x1b24c = pc ->
  @G_letf2.letf2_contract I ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  mem_inv segs m -> MemNorm.task_mem segs m ->
  evt segs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1
                    (Z_to_bv 64 (SF.f128_le (bv_unsigned a0 + 2^64 * bv_unsigned a1)
                                             (bv_unsigned a2 + 2^64 * bv_unsigned a3)))
                    a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom segs) /\
      munch [] m m' /\ wmono segs m m' /\ mem_inv segs m' /\ MemNorm.task_mem segs m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom segs)).
Proof.
  intros I segs pc HI Hpc H ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    t3 t4 t5 t6 F fc m MI TM.
  subst segs pc.
  pose proof (H ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
                (mem_inv_to_cj _ m MI TM)) as E.
  refine (evt_bridge _ _ _ _ _ E).
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & Hms & MU & WM
              & MI').
  destruct (mem_inv_of_cj _ m' MI') as [MI2 TM2].
  exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
  exact (conj Hms (conj MU (conj WM (conj MI2 TM2)))).
Qed.

Lemma br_ge : forall (I : RStep.RImg) segs pc, @RStep.img_segs I = segs -> @RStep.sym I 0x1b314 = pc ->
  @G_getf2.getf2_contract I ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  mem_inv segs m -> MemNorm.task_mem segs m ->
  evt segs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1
                    (Z_to_bv 64 (SF.f128_ge (bv_unsigned a0 + 2^64 * bv_unsigned a1)
                                             (bv_unsigned a2 + 2^64 * bv_unsigned a3)))
                    a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom segs) /\
      munch [] m m' /\ wmono segs m m' /\ mem_inv segs m' /\ MemNorm.task_mem segs m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom segs)).
Proof.
  intros I segs pc HI Hpc H ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    t3 t4 t5 t6 F fc m MI TM.
  subst segs pc.
  pose proof (H ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
                (mem_inv_to_cj _ m MI TM)) as E.
  refine (evt_bridge _ _ _ _ _ E).
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & Hms & MU & WM
              & MI').
  destruct (mem_inv_of_cj _ m' MI') as [MI2 TM2].
  exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
  exact (conj Hms (conj MU (conj WM (conj MI2 TM2)))).
Qed.

Lemma br_fd : forall (I : RStep.RImg) segs pc, @RStep.img_segs I = segs -> @RStep.sym I 0x7f000900 = pc ->
  @C_floatditf.floatditf_contract I ->
  forall (t : Z) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  bv_unsigned a0 = SF.wrap64 t -> mem_inv segs m -> MemNorm.task_mem segs m ->
  evt segs (fun ms' => exists (t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (SF.lo64 (f128_of_i64 t)))
                    (Z_to_bv 64 (SF.hi64 (f128_of_i64 t))) a2' a3' a4' a5' a6' a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom segs) /\
      munch [] m m' /\ wmono segs m m' /\ mem_inv segs m' /\ MemNorm.task_mem segs m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom segs)).
Proof.
  intros I segs pc HI Hpc H t ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    t3 t4 t5 t6 F fc m Ht MI TM.
  subst segs pc.
  pose proof (H ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m t
                (mem_inv_to_cj _ m MI TM) Ht) as E.
  refine (evt_bridge _ _ _ _ _ E).
  intros ms' (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & Hms & MU & WM & MI').
  destruct (mem_inv_of_cj _ m' MI') as [MI2 TM2].
  exists t0', t1', t2', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
  exact (conj Hms (conj MU (conj WM (conj MI2 TM2)))).
Qed.

(** __subtf3 (and the __addtf3 it jumps to) uses the 48 bytes below its sp and rounds with frm. *)
Lemma br_sub : forall (I : RStep.RImg) segs pc, @RStep.img_segs I = segs -> @RStep.sym I 0x1bc70 = pc ->
  @G_subtf3.subtf3_contract I ->
  forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (S : Z) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  48 <= S < 2^64 -> stk segs m (S - 48) S -> mem_inv segs m -> MemNorm.task_mem segs m -> frm0 fc ->
  evt segs (fun ms' => exists (t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (fc' : bv 32)
                              (m' : word -> option byte),
      ms' = MS (mkR ra (Z_to_bv 64 S) gp tp t0' t1' t2' s0 s1
                    (Z_to_bv 64 (SF.lo64 (SF.f128_sub (bv_unsigned a0 + 2^64 * bv_unsigned a1)
                                                      (bv_unsigned a2 + 2^64 * bv_unsigned a3))))
                    (Z_to_bv 64 (SF.hi64 (SF.f128_sub (bv_unsigned a0 + 2^64 * bv_unsigned a1)
                                                      (bv_unsigned a2 + 2^64 * bv_unsigned a3))))
                    a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc' None m' (seg_rom segs) /\
      munch [(S - 48, S)] m m' /\ wmono segs m m' /\ mem_inv segs m' /\ MemNorm.task_mem segs m' /\
      frm0 fc' /\ stk segs m' (S - 48) S)
    (MS (mkR ra (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom segs)).
Proof.
  intros I segs pc HI Hpc H ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    t3 t4 t5 t6 S F fc m HSr ST MI TM FRM.
  subst segs pc.
  assert (ES : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; lia).
  assert (ST' : CJ.Lib.Frame.stk (@RStep.img_segs I) m (bv_unsigned (Z_to_bv 64 S) - 48) (bv_unsigned (Z_to_bv 64 S)))
    by (rewrite ES; exact ST).
  pose proof (H ra (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                t3 t4 t5 t6 F fc m ST' (mem_inv_to_cj _ m MI TM) FRM) as E.
  refine (evt_bridge _ _ _ _ _ E).
  intros ms' (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & fc' & m' & Hms & MU & WM
              & MI' & FRM' & ST2).
  rewrite ES in MU, ST2.
  destruct (mem_inv_of_cj _ m' MI') as [MI2 TM2].
  exists t0', t1', t2', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', fc', m'.
  exact (conj Hms (conj MU (conj WM (conj MI2 (conj TM2 (conj FRM' ST2)))))).
Qed.

(** task_mem survives a callee or store that changes only bytes writable at the start. *)
Lemma tm_munch : forall segs W (m0 m : word -> option byte), MemNorm.task_mem segs m0 -> munch W m0 m ->
  (forall a : word, ~ outside W (bv_unsigned a) -> wview segs m0 a <> None) -> MemNorm.task_mem segs m.
Proof.
  intros segs W m0 m T MU H a v E.
  destruct (m0 a) as [v0|] eqn:E0; [exact (T a v0 E0)|].
  assert (Hin : ~ outside W (bv_unsigned a)) by (intros Ho; rewrite (MU a Ho) in E; congruence).
  specialize (H a Hin). unfold wview in H. rewrite E0 in H. left.
  destruct (find_segment segs (bv_unsigned a) 1) eqn:Ef; [congruence | exfalso; apply H; reflexivity].
Qed.

(** ** Register-level facts the walk uses *)
Lemma u_lo64 : forall x, bv_unsigned (Z_to_bv 64 (SF.lo64 x)) = SF.lo64 x.
Proof. intros x. apply unsigned_lit. apply SF.wrap64_range. Qed.

Lemma u_hi64 : forall x, bv_unsigned (Z_to_bv 64 (SF.hi64 x)) = SF.hi64 x.
Proof. intros x. apply unsigned_lit. apply SF.wrap64_range. Qed.

Lemma f128_le_range : forall a c, -1 <= SF.f128_le a c <= 1.
Proof.
  intros a c. unfold SF.f128_le, SF.nez64, SF.b2z. cbv zeta.
  repeat match goal with |- context [if ?x then _ else _] => destruct x end; lia.
Qed.

Lemma f128_ge_range : forall a c, -1 <= SF.f128_ge a c <= 1.
Proof.
  intros a c. unfold SF.f128_ge, SF.nez64, SF.b2z. cbv zeta.
  repeat match goal with |- context [if ?x then _ else _] => destruct x end; lia.
Qed.

(** bltz / bgez on a comparison result in {-1, 0, 1}. *)
Lemma lts0 : forall v, -1 <= v <= 1 -> bv_lts (Z_to_bv 64 v) (Z_to_bv 64 0) = (v <? 0).
Proof.
  intros v Hv. assert (C : v = -1 \/ v = 0 \/ v = 1) by lia.
  destruct C as [ -> | [ -> | -> ] ]; vm_compute; reflexivity.
Qed.

(** sext.w then beq: the 64-bit word r is the sign extension of its low 32 bits exactly when r read as a signed
    64-bit value lies in [-2^31, 2^31). *)
Lemma fits32 : forall r, bv_eqb (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 r) + 0))) (Z_to_bv 64 r) =
  (-2^31 <=? bv_swrap 64 r) && (bv_swrap 64 r <? 2^31).
Proof.
  intros r. unfold bv_eqb. rewrite !unsigned_lit_wrap, Z.add_0_r.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
  change (bv_half_modulus 64) with (2^63). change (bv_modulus 64) with (2^64).
  rewrite (Z.add_mod r (2^63) (2^64)) by lia. rewrite (Z.mod_small (2^63) (2^64)) by lia.
  set (u := r mod 2^64). assert (Hu : 0 <= u < 2^64) by (apply Z.mod_pos_bound; lia). clearbody u.
  destruct (Z.eqb_spec (((u + 2^31) mod 2^32 - 2^31) mod 2^64) u) as [E|E];
  destruct (Z.leb_spec (-2^31) ((u + 2^63) mod 2^64 - 2^63)) as [L1|L1];
  destruct (Z.ltb_spec ((u + 2^63) mod 2^64 - 2^63) (2^31)) as [L2|L2]; cbn [andb]; try reflexivity;
  exfalso; revert E L1 L2; Z.div_mod_to_equations; lia.
Qed.

Lemma bvsw_lit : forall r, Z_to_bv 64 (bv_swrap 64 r) = Z_to_bv 64 r.
Proof.
  intros r. apply bv_eq. rewrite !unsigned_lit_wrap. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 64) with (2^63). change (bv_modulus 64) with (2^64).
  rewrite Zminus_mod_idemp_l. replace (r + 2^63 - 2^63) with r by lia. reflexivity.
Qed.

Lemma reg_get_set_ne : forall (R : bvmap 5 word) (k r : bv 5) v,
  bv_unsigned k <> bv_unsigned r -> Sem.reg_get (bvmap_set k v R) r = Sem.reg_get R r.
Proof. intros R k r v H. apply freg_get_other. unfold bv_eqb. apply Z.eqb_neq. exact H. Qed.

(** The FP registers pod_nearest writes before its epilogue (fs0 = f8, fa5 = f15) leave every other one as it
    was. *)
Ltac hfc :=
  let k := fresh "k" in let H15 := fresh "H15" in let H8 := fresh "H8" in
  intros k H15 H8;
  repeat (rewrite reg_get_set_ne;
          [ | let E := fresh "E" in intro E;
              first [ apply H15; rewrite <- E; reflexivity | apply H8; rewrite <- E; reflexivity ] ]);
  reflexivity.

(** fcvt.l.s, which the walk library's exec lemmas leave out. *)
Lemma exec_fcvt_l_s : forall sz rd rs1 rm c md, rmode_of_field (bv_unsigned rm) (frm_of c) = Some md ->
  exec sz (Fcvt FC_L FC_S rd rs1 rm) c =
  EDone (rset rd (Z_to_bv 64 (fst (fp_to_int fmt_single md true 64 (bv_unsigned (unbox_s (fget c rs1))))))
          (accrue (snd (fp_to_int fmt_single md true 64 (bv_unsigned (unbox_s (fget c rs1)))))
                  (with_pc (c_pc c + sz) c))).
Proof. intros until md; intros H. fcvt_tac H. Qed.

Local Ltac OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib.Step.exec_pre i ::=
  lazymatch goal with
  | |- context [exec ?sz _ ?c] =>
    lazymatch i with
    | Fcvt FC_L FC_S ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_l_s sz rd rs1 rm c _ H)
    | Fcmp ?op FMT_S ?rd ?rs1 ?rs2 => rewrite (exec_fcmp_s sz op rd rs1 rs2 c)
    | _ => idtac
    end
  end;
  try match goal with
  | FRM : frm0 ?f |- context [slice_get ?f' 5 3] => constr_eq f f'; rewrite (frm0_slice_get f FRM)
  end.

(** Fold the closed second operand of a binary128 compare into the named constant [c]. *)
Ltac fold_c128 c :=
  repeat match goal with
  | |- context [SF.f128_le ?x ?y] =>
      let v := eval vm_compute in y in let w := eval vm_compute in c in constr_eq v w;
      lazymatch y with c => fail | _ => replace y with c by (vm_compute; reflexivity) end
  | |- context [SF.f128_ge ?x ?y] =>
      let v := eval vm_compute in y in let w := eval vm_compute in c in constr_eq v w;
      lazymatch y with c => fail | _ => replace y with c by (vm_compute; reflexivity) end
  end.

(** The binary32 value of a closed NaN-boxed literal, as fmv.w.x leaves it in an FP register. *)
Ltac fold_unbox :=
  repeat match goal with
  | |- context [bv_unsigned (unbox_s (Z_to_bv 64 ?z))] =>
      lazymatch z with Zpos _ => idtac | Z0 => idtac end;
      let v := eval vm_compute in (bv_unsigned (unbox_s (Z_to_bv 64 z))) in
      replace (bv_unsigned (unbox_s (Z_to_bv 64 z))) with v by (vm_compute; reflexivity)
  end.
Lemma W128_def : forall x, SF.lo64 x + 2^64 * SF.hi64 x = W128 x.
Proof. reflexivity. Qed.
Lemma pn_d_def : forall b, W128 (f128_of_f32 (fbox b)) = pn_d b.
Proof. reflexivity. Qed.
Lemma pn_t_def : forall b, fst (fp_to_int fmt_single RTZ true 64 b) = pn_t b.
Proof. reflexivity. Qed.


Definition hold (P : Prop) : Prop := P.

Section Walk.
Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (m0 : word -> option byte)
  (b Sp out lo : Z).
Hypothesis HEX : @C_extendsftf2.extendsftf2_contract IImgP.N_img.
Hypothesis HLE : @G_letf2.letf2_contract IImgP.N_img.
Hypothesis HFD : @C_floatditf.floatditf_contract IImgP.N_img.
Hypothesis HSB : @G_subtf3.subtf3_contract IImgP.N_img.
Hypothesis HGE : @G_getf2.getf2_contract IImgP.N_img.
Hypothesis Hb : 0 <= b < 2^32.
Hypothesis HF10 : Sem.reg_get F (Z_to_bv 5 10) = nan_box (Z_to_bv 32 b).
Hypothesis Hout : 0 <= out /\ out + 8 <= 2^64.
Hypothesis Hal : out mod 8 = 0.
Hypothesis Hdj : hold (out + 8 <= Sp - 96 \/ Sp <= out).
Hypothesis Hlo : 0 <= lo.
Hypothesis HK : lo + 96 <= Sp.
Hypothesis HSp : Sp <= 2^64.
Hypothesis TM0 : MemNorm.task_mem rsegs m0.
Hypothesis WR0 : forall a : word, Sp - 96 <= bv_unsigned a < Sp \/ out <= bv_unsigned a < out + 8 ->
  wview rsegs m0 a <> None.

(** The contract's post, with the machine model [pn_bin] in place of [nearest]. *)
Definition Post : machine_state -> Prop := fun ms' =>
  exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32)
         (m' : word -> option byte),
    ms' = MS (mkR ra (Z_to_bv 64 Sp) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (pod_near_rc (pn_bin b)))
                  a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F' (ret_pc ra) fc' None m' (seg_rom rsegs) /\
    (forall k : bv 5, bv_unsigned k <> 15 -> Sem.reg_get F' k = Sem.reg_get F k) /\
    frm0 fc' /\
    pod_near_mem m0 m' Sp out (pn_bin b) /\
    wmono rsegs m0 m' /\ mem_inv rsegs m' /\ MemNorm.task_mem rsegs m' /\ stk rsegs m' lo Sp.

(** The frame between the prologue and the epilogue: the six saved registers at [sp - 48, sp), the stack below it,
    and the facts about memory every step keeps. *)
Definition frm4 (fv : word) (m : word -> option byte) : Prop :=
  rw_cells rsegs m (Sp + -48) [C8 fv; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] /\
  stk rsegs m lo (Sp + -48) /\ wmono rsegs m0 m /\ mem_inv rsegs m.
(** ... and, until the store of the result, nothing changed outside the 96 bytes below sp. *)
Definition frm (fv : word) (m : word -> option byte) : Prop := frm4 fv m /\ munch [(Sp - 96, Sp)] m0 m.

Lemma frm_mi : forall fv m, frm fv m -> mem_inv rsegs m.
Proof. intros fv m [(_ & _ & _ & MI) _]. exact MI. Qed.

Lemma tm_of : forall m, munch [(Sp - 96, Sp); (out, out + 8)] m0 m -> MemNorm.task_mem rsegs m.
Proof.
  intros m MU. apply (tm_munch rsegs _ m0 m TM0 MU). intros a Ha. apply WR0.
  cbn [outside] in Ha. lia.
Qed.

Lemma tm_frm : forall fv m, frm fv m -> MemNorm.task_mem rsegs m.
Proof.
  intros fv m [_ MU]. apply tm_of. eapply munch_weaken; [|exact MU].
  intros x Hx. cbn [outside] in *. tauto.
Qed.

Lemma frm_stk : forall fv m, frm fv m -> stk rsegs m (Sp + -48 - 48) (Sp + -48).
Proof.
  intros fv m [(_ & ST & _ & _) _].
  exact (proj2 (stk_split rsegs m lo (Sp + -48 - 48) (Sp + -48) ST ltac:(lia))).
Qed.

(** The leaf callees write nothing. *)
Lemma frm_call : forall fv m m', frm fv m -> munch [] m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> frm fv m'.
Proof.
  intros fv m m' [(FR & ST & WM & _) MU] MU' WM' MI'.
  split; [split|].
  - eapply rw_cells_transport; [exact FR | exact MU' | exact WM' | exact I].
  - split; [eapply stk_transport_disjoint; [exact ST | exact MU' | exact WM' | exact I]|].
    split; [exact (wmono_trans rsegs _ _ _ WM WM') | exact MI'].
  - eapply munch_trans; [exact MU | eapply munch_weaken; [|exact MU']]; intros x _; exact I.
Qed.

(** __subtf3/__addtf3 write the 48 bytes below pod_nearest's frame. *)
Lemma frm_sub : forall fv m m', frm fv m -> munch [(Sp + -48 - 48, Sp + -48)] m m' -> wmono rsegs m m' ->
  mem_inv rsegs m' -> stk rsegs m' (Sp + -48 - 48) (Sp + -48) -> frm fv m'.
Proof.
  intros fv m m' [(FR & ST & WM & _) MU] MU' WM' MI' ST'.
  split; [split|].
  - eapply rw_cells_transport; [exact FR | exact MU' | exact WM' |].
    cbn [disjoint_from cells_size csize]. split; [lia | exact I].
  - split.
    + destruct (stk_split rsegs m lo (Sp + -48 - 48) (Sp + -48) ST ltac:(lia)) as [STa _].
      pose proof (stk_transport_disjoint rsegs _ m m' lo (Sp + -48 - 48) STa MU' WM'
                    ltac:(cbn [disjoint_from]; split; [lia | exact I])) as STb.
      exact (stk_merge rsegs m' lo (Sp + -48 - 48) (Sp + -48) STb ST' ltac:(lia)).
    + split; [exact (wmono_trans rsegs _ _ _ WM WM') | exact MI'].
  - eapply munch_trans; [exact MU | eapply munch_weaken; [|exact MU']].
    intros x [Hx _]. split; [lia | exact I].
Qed.

(** The store of the result at out (0x14964 `sd s1,0(s0)`): out is writable (it was at the entry), outside the
    frame, and the store keeps the frame. *)
Lemma store_out : forall fv m (v : word), frm fv m ->
  frm4 fv (write_to_mem m (wa out) (le8 v)) /\
  munch [(Sp - 96, Sp); (out, out + 8)] m0 (write_to_mem m (wa out) (le8 v)) /\
  bytes_at rsegs (write_to_mem m (wa out) (le8 v)) out (le8 v) /\
  store_ok rsegs m (wa out) 8 = true.
Proof.
  intros fv m v [(FR & ST & WM & MI) MU].
  pose proof Hdj as D. unfold hold in D.
  assert (WR : wr_at rsegs m out 8).
  { split; [lia|]. split; [lia|]. intros i Hi. apply WM. apply WR0. right.
    unfold wa. rewrite unsigned_lit by lia. lia. }
  assert (HSt : store_ok rsegs m (wa out) 8 = true).
  { pose proof (wr_at_store_ok rsegs m out 8 0 8 WR ltac:(lia) ltac:(lia)) as H. rewrite Z.add_0_r in H. exact H. }
  assert (HSt' : store_ok rsegs m (wa out) (length (le8 v)) = true) by (rewrite length_le8; exact HSt).
  split; [|split; [|split]].
  - split; [|split; [|split]].
    + apply (rw_cells_frame rsegs m _ _ out (le8 v) FR); rewrite ?length_le8; cbn [cells_size csize]; lia.
    + apply (stk_write rsegs m lo (Sp + -48) out (le8 v) ST); rewrite ?length_le8; lia.
    + exact (wmono_write rsegs m0 m (wa out) (le8 v) WM).
    + exact (mem_inv_store rsegs m (wa out) (le8 v) MI HSt').
  - apply munch_write; rewrite ?length_le8; [| lia | lia | cbn [inside]; right; left; lia].
    eapply munch_weaken; [|exact MU]. intros x [H1 [H2 _]]. split; [exact H1 | exact I].
  - apply bytes_at_write_same; rewrite ?length_le8; lia.
  - exact HSt.
Qed.

(** The shared exit 0x1496c: a0 = s1, restore ra, s0-s3 and fs0, free the frame, return. *)
Lemma epi : forall fv (Fc : bvmap 5 word) (fc1 : bv 32) m rc
    (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 : word),
  fv = Sem.reg_get F (Z_to_bv 5 8) ->
  (forall k : bv 5, bv_unsigned k <> 15 -> bv_unsigned k <> 8 -> Sem.reg_get Fc k = Sem.reg_get F k) ->
  frm0 fc1 -> frm4 fv m -> pod_near_mem m0 m Sp out (pn_bin b) -> rc = pod_near_rc (pn_bin b) ->
  evt rsegs Post
    (MS (mkR x1 (Z_to_bv 64 (Sp + -48)) gp tp x5 x6 x7 x8 (Z_to_bv 64 rc) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19
             s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        Fc (Z_to_bv 64 0x1496c) fc1 None m (seg_rom rsegs)).
Proof.
  intros fv Fc fc1 m rc x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 Efv HFc FRM
    [FR [ST [WM MI]]] PM Erc.
  assert (TM : MemNorm.task_mem rsegs m).
  { apply tm_of. destruct (pn_bin b); cbn [pod_near_mem] in PM.
    - exact (proj1 PM).
    - eapply munch_weaken; [|exact PM]. intros x Hx. cbn [outside] in *. tauto. }
  do 9 step.
  match goal with |- evt _ _ (MS _ ?F' _ ?fc' _ ?m' _) =>
    apply evt_done; unfold Post;
    exists x5, x6, x7, x11, x12, x13, x14, x15, x16, x17, x28, x29, x30, x31, F', fc', m' end.
  split; [subst rc; unfold mkR; repeat f_equal; lia|].
  split.
  { intros k Hk. destruct (Z.eq_dec (bv_unsigned k) 8) as [E8|E8].
    - rewrite (freg_get_same Fc _ k fv) by (rewrite E8; reflexivity). rewrite Efv.
      apply reg_get_key. rewrite E8. reflexivity.
    - rewrite reg_get_set_ne by (intro E; apply E8; rewrite <- E; reflexivity). exact (HFc k Hk E8). }
  split; [exact FRM|]. split; [exact PM|]. split; [exact WM|]. split; [exact MI|]. split; [exact TM|].
  pose proof (stk_release rsegs m lo (Sp + -48) _ ST FR ltac:(lia)) as R. cbn [cells_size csize Nat.add] in R.
  replace (Sp + -48 + Z.of_nat 48) with Sp in R by lia. exact R.
Qed.

(** 0x14954: s1 = r; `sext.w a0,s1`, `beq a0,s1`: store r at out and return 1, else return 0. *)
Lemma tail : forall fv (Fc : bvmap 5 word) (fc1 : bv 32) m (r : Z)
    (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 : word),
  fv = Sem.reg_get F (Z_to_bv 5 8) ->
  (forall k : bv 5, bv_unsigned k <> 15 -> bv_unsigned k <> 8 -> Sem.reg_get Fc k = Sem.reg_get F k) ->
  frm0 fc1 -> frm fv m ->
  pn_bin b = (if (-2^31 <=? bv_swrap 64 r) && (bv_swrap 64 r <? 2^31) then Some (bv_swrap 64 r) else None) ->
  evt rsegs Post
    (MS (mkR x1 (Z_to_bv 64 (Sp + -48)) gp tp x5 x6 x7 (Z_to_bv 64 out) (Z_to_bv 64 r) x10 x11 x12 x13 x14 x15 x16
             x17 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        Fc (Z_to_bv 64 0x14954) fc1 None m (seg_rom rsegs)).
Proof.
  intros fv Fc fc1 m r x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 Efv HFc FRM FM Hpn.
  step. step.
  rewrite fits32.
  destruct ((-2^31 <=? bv_swrap 64 r) && (bv_swrap 64 r <? 2^31)) eqn:FIT.
  - destruct (store_out fv m (Z_to_bv 64 r) FM) as (F4 & MU2 & BY & HSt).
    cbv iota. step. step.
    eapply epi; [exact Efv | exact HFc | exact FRM | exact F4 | |].
    + rewrite Hpn. cbn [pod_near_mem]. split; [exact MU2|]. rewrite bvsw_lit. exact BY.
    + rewrite Hpn. reflexivity.
  - cbv iota. step. step.
    destruct FM as [F4 MU].
    eapply epi; [exact Efv | exact HFc | exact FRM | exact F4 | rewrite Hpn; exact MU | rewrite Hpn; reflexivity].
Qed.

Lemma body : forall (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (fc : bv 32),
  stk rsegs m0 lo Sp -> mem_inv rsegs m0 -> frm0 fc ->
  evt rsegs Post
    (MS (mkR ra (Z_to_bv 64 Sp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 out) a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 POD_NEAREST) fc None m0 (seg_rom rsegs)).
Proof.
  intros t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 fc ST MI FRM.
  pose proof (munch_refl [(Sp - 96, Sp)] m0) as MU. pose proof (wmono_refl rsegs m0) as WM.
  destruct (stk_carve rsegs m0 lo Sp 48 ST ltac:(lia)) as [ST1 [junk FR]]. clear ST.
  change (Z.of_nat 48) with 48 in ST1, FR.
  replace (Sp - 48) with (Sp + -48) in ST1, FR by lia.
  unfold POD_NEAREST.
  (* prologue: the frame, ra, s0-s3 and fs0 *)
  do 7 step.
  match type of FR with rw_cells _ ?m1 _ (C8 ?v :: _) =>
    assert (FM : frm v m1) by exact (conj (conj FR (conj ST1 (conj WM MI))) MU);
    assert (Efv : v = Sem.reg_get F (Z_to_bv 5 8)) by (apply reg_get_key; reflexivity) end.
  clear FR ST1 WM MU MI.
  (* 0x148a0 feq.s a1,fa0,fa0; beqz a1 *)
  step. fix_reg F HF10 10%Z. unfold feq_s. rewrite unbox_nan_box, (u32_lit b Hb).
  destruct (fst (fp_eq fmt_single b b)) eqn:FE; unfold bword; step.
  2:{ (* a NaN: s1 = 0, return 0 *)
      if_true. step. step.
      eapply epi; [exact Efv | intros k _ _; reflexivity | eassumption | exact (proj1 FM) | |].
      - assert (E : pn_bin b = None) by (unfold pn_bin; rewrite FE; reflexivity). rewrite E. exact (proj2 FM).
      - unfold pn_bin; rewrite FE; reflexivity. }
  if_false.
  (* 0x148a8 fmv.s fs0,fa0; mv s0,a0; jal __extendsftf2 *)
  step. fix_reg F HF10 10%Z. rewrite unbox_nan_box, sgnj_self32.
  step. step.
  eapply evt_cut.
  { eapply (br_ext IImgP.N_img rsegs 0x15050 eq_refl eq_refl HEX b);
      [ rewrite freg_get_other by reflexivity; exact HF10 | exact (frm_mi _ _ FM) | exact (tm_frm _ _ FM) ]. }
  intros ms' (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MU2 & WM2
              & MI2 & _).
  pose proof (frm_call _ _ _ FM MU2 WM2 MI2) as FM2. clear FM MU2 WM2 MI2.
  rewrite ret_pc_even by (try lia; reflexivity).
  (* 0x148b4 mv s2,a0; lui a0,0x4f000; fmv.w.x fa5,a0; flt.s a0,fa5,fs0 *)
  step. step. step. step.
  unfold flt_s. rewrite !unbox_nan_box, (u32_lit b Hb). fold_unbox.
  destruct (fst (fp_lt fmt_single 1325400064 b)) eqn:LT; unfold bword.
  { (* 2^31 < f: s1 = 0, return 0 *)
    step. step. if_true.
    eapply epi; [exact Efv | hfc | eassumption | exact (proj1 FM2) | |].
    - assert (E : pn_bin b = None) by (unfold pn_bin; rewrite FE, LT; reflexivity). rewrite E. exact (proj2 FM2).
    - unfold pn_bin; rewrite FE, LT; reflexivity. }
  step. step. if_false.
  (* 0x148cc mv s3,a1; a3 = high word of C1; mv a0,s2; mv a2,zero; jal __lttf2 *)
  do 8 step.
  eapply evt_cut.
  { eapply (br_le IImgP.N_img rsegs 0x14ecc eq_refl eq_refl HLE); [exact (frm_mi _ _ FM2) | exact (tm_frm _ _ FM2)]. }
  intros ms' (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m3
              & -> & MU3 & WM3 & MI3 & _).
  pose proof (frm_call _ _ _ FM2 MU3 WM3 MI3) as FM3. clear FM2 MU3 WM3 MI3.
  rewrite ret_pc_even by (try lia; reflexivity).
  rewrite !u_lo64, !u_hi64, !W128_def, pn_d_def. fold_c128 C1_128.
  (* 0x148ec bltz a0 *)
  step. rewrite lts0 by apply f128_le_range.
  destruct (SF.f128_le (pn_d b) C1_128 <? 0) eqn:LE; cbv iota.
  { (* d < C1: s1 = 0, return 0 *)
    eapply epi; [exact Efv | hfc | eassumption | exact (proj1 FM3) | |].
    - assert (E : pn_bin b = None) by (unfold pn_bin; rewrite FE, LT, LE; reflexivity). rewrite E. exact (proj2 FM3).
    - unfold pn_bin; rewrite FE, LT, LE; reflexivity. }
  (* 0x148f0 fcvt.l.s s1,fs0,rtz *)
  step. rewrite unbox_nan_box, (u32_lit b Hb), pn_t_def.
  (* 0x148f4 mv a0,s1; jal __floatditf *)
  step. step.
  eapply evt_cut.
  { eapply (br_fd IImgP.N_img rsegs 0x151ac eq_refl eq_refl HFD (pn_t b));
      [ rewrite unsigned_lit_wrap, SF.wrap64_mod; reflexivity | exact (frm_mi _ _ FM3) | exact (tm_frm _ _ FM3) ]. }
  intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m4 & -> & MU4 & WM4 & MI4 & _).
  pose proof (frm_call _ _ _ FM3 MU4 WM4 MI4) as FM4. clear FM3 MU4 WM4 MI4.
  rewrite ret_pc_even by (try lia; reflexivity).
  (* 0x148fc a2:a3 = (long double)t, a0:a1 = d; jal __subtf3 *)
  do 5 step.
  eapply evt_cut.
  { eapply (br_sub IImgP.N_img rsegs 0x152d0 eq_refl eq_refl HSB);
      [ lia | exact (frm_stk _ _ FM4) | exact (frm_mi _ _ FM4) | exact (tm_frm _ _ FM4) | eassumption ]. }
  intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & fc5 & m5 & -> & MU5 & WM5 & MI5 & _ & FRM5 & ST5).
  pose proof (frm_sub _ _ _ FM4 MU5 WM5 MI5 ST5) as FM5. clear FM4 MU5 WM5 MI5 ST5.
  rewrite ret_pc_even by (try lia; reflexivity).
  rewrite !u_lo64, !u_hi64, !W128_def, pn_d_def.
  (* 0x14910 s2:s3 = frac; a2:a3 = 0.5L; jal __getf2 *)
  do 6 step.
  eapply evt_cut.
  { eapply (br_ge IImgP.N_img rsegs 0x14f94 eq_refl eq_refl HGE); [exact (frm_mi _ _ FM5) | exact (tm_frm _ _ FM5)]. }
  intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m6 & -> & MU6 & WM6 & MI6 & _).
  pose proof (frm_call _ _ _ FM5 MU6 WM6 MI6) as FM6. clear FM5 MU6 WM6 MI6.
  rewrite ret_pc_even by (try lia; reflexivity).
  rewrite !u_lo64, !u_hi64, !W128_def. fold_c128 HALF_128.
  (* 0x14928 bgez a0 *)
  step. rewrite lts0 by apply f128_ge_range. rewrite Z.ltb_antisym, Bool.negb_involutive.
  destruct (0 <=? SF.f128_ge (W128 (SF.f128_sub (pn_d b) (W128 (f128_of_i64 (pn_t b))))) HALF_128) eqn:GE;
    cbv iota.
  { (* frac >= 1/2: 0x14950 r = t + 1 *)
    step.
    eapply tail; [exact Efv | hfc | eassumption | exact FM6 |].
    unfold pn_bin; rewrite FE, LT, LE. unfold pn_r. cbv zeta. rewrite GE. reflexivity. }
  (* 0x1492c a0:a1 = frac, a2:a3 = -0.5L; jal __lttf2 *)
  do 6 step.
  eapply evt_cut.
  { eapply (br_le IImgP.N_img rsegs 0x14ecc eq_refl eq_refl HLE); [exact (frm_mi _ _ FM6) | exact (tm_frm _ _ FM6)]. }
  intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m7 & -> & MU7 & WM7 & MI7 & _).
  pose proof (frm_call _ _ _ FM6 MU7 WM7 MI7) as FM7. clear FM6 MU7 WM7 MI7.
  rewrite ret_pc_even by (try lia; reflexivity).
  rewrite !u_lo64, !u_hi64, !W128_def. fold_c128 MHALF_128.
  (* 0x14944 bgez a0 *)
  step. rewrite lts0 by apply f128_le_range.
  destruct (SF.f128_le (W128 (SF.f128_sub (pn_d b) (W128 (f128_of_i64 (pn_t b))))) MHALF_128 <? 0) eqn:LM;
    cbn [negb]; cbv iota.
  - (* frac < -1/2: 0x14948 r = t - 1; j *)
    step. step.
    eapply tail; [exact Efv | hfc | eassumption | exact FM7 |].
    unfold pn_bin; rewrite FE, LT, LE. unfold pn_r. cbv zeta. rewrite GE, LM.
    replace (pn_t b - 1) with (pn_t b + -1) by lia. reflexivity.
  - (* r = t *)
    eapply tail; [exact Efv | hfc | eassumption | exact FM7 |].
    unfold pn_bin; rewrite FE, LT, LE. unfold pn_r. cbv zeta. rewrite GE, LM. reflexivity.
Qed.

End Walk.

(** ** The contract, from the callee contracts and the value of the machine model *)
Theorem pod_nearest_of_bin :
  (forall b, 0 <= b < 2^32 -> pn_bin b = nearest b INT32_MIN INT32_MAX) ->
  @C_extendsftf2.extendsftf2_contract IImgP.N_img -> @G_letf2.letf2_contract IImgP.N_img ->
  @C_floatditf.floatditf_contract IImgP.N_img -> @G_subtf3.subtf3_contract IImgP.N_img ->
  @G_getf2.getf2_contract IImgP.N_img ->
  pod_nearest_contract.
Proof.
  intros HV HEX HLE HFD HSB HGE. unfold pod_nearest_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo b
    Hb HF WR Hal Hdj ST HK HW FRM MI TM.
  replace (nearest b NEAR_LO NEAR_HI) with (pn_bin b) by (rewrite (HV b Hb); reflexivity).
  pose proof (Z_to_bv_lit_self sp) as Esp. pose proof (Z_to_bv_lit_self a0) as Ea0.
  set (Sp := bv_unsigned sp) in *. set (out := bv_unsigned a0) in *.
  rewrite <- Esp, <- Ea0. clearbody Sp out. clear Esp Ea0.
  unfold POD_NEAREST_STACK in *.
  pose proof ST as (Hlo & HSp & STw).
  assert (Hout : 0 <= out /\ out + 8 <= 2^64) by (destruct WR as (W1 & W2 & _); split; assumption).
  assert (Hdj' : hold (out + 8 <= Sp - 96 \/ Sp <= out)) by exact Hdj.
  assert (WR0 : forall x : word, Sp - 96 <= bv_unsigned x < Sp \/ out <= bv_unsigned x < out + 8 ->
                  wview rsegs m x <> None).
  { intros x [Hx|Hx].
    - rewrite <- (Z_to_bv_lit_self x). exact (proj1 (STw (bv_unsigned x) ltac:(lia))).
    - destruct WR as (_ & _ & W3). specialize (W3 (bv_unsigned x - out) ltac:(lia)).
      replace (out + (bv_unsigned x - out)) with (bv_unsigned x) in W3 by lia.
      unfold wa in W3. rewrite Z_to_bv_lit_self in W3. exact W3. }
  eapply evt_mono.
  { eapply (body ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m b Sp out lo); eassumption. }
  intros ms' H. exact H.
Qed.

(** The contract of the plain build's pod_nearest, from its five soft-float callees' contracts and the binary128
    value facts [near_sf_facts]. *)
Theorem pod_nearest_holds :
  near_sf_facts ->
  @C_extendsftf2.extendsftf2_contract IImgP.N_img -> @G_letf2.letf2_contract IImgP.N_img ->
  @C_floatditf.floatditf_contract IImgP.N_img -> @G_subtf3.subtf3_contract IImgP.N_img ->
  @G_getf2.getf2_contract IImgP.N_img ->
  pod_nearest_contract.
Proof. intros NS. exact (pod_nearest_of_bin (pn_bin_nearest NS)). Qed.
