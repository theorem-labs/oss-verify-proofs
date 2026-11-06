(** The nearest integer of a Float value, a half read upward: what pod_nearest (fuzz/pod.h:152-171) and
    reac_float_nearest (src/reac_float_near.h:24-34) both document, for a binary32 bit pattern. Shared by fuzz_role,
    fuzz_rate and fuzz_headamp. Statement text and computation: no function of a binary is proved here.

    [near_f32 b] is floor(f + 1/2) for the value f of b when b is finite (zero, subnormal or normal), and None for
    an infinity or a NaN. [nearest b lo hi] keeps it only when it lies in [lo, hi]: pod_nearest(f, lo, hi, &out)
    returns 1 with out = r exactly when [nearest b lo hi = Some r] (for hi < 2^63 - 1; long double holds d, t and
    frac exactly: [pod_nearest_exact_eq]). reac_float_nearest(f, lo, hi, &out) returns 0 with out = r exactly then
    when -2^53 <= lo and hi < 2^53, so that (double)lo and (double)hi + 1.0 are exact: the binary64 sum f + 0.5
    rounded to nearest-even has the floor of f + 1/2 for every finite float. Past those bounds it can differ
    (hi = 2^53 + 1, f = 2^53: nearest is 2^53, the function returns -1). The readers pass [INT_MIN, INT_MAX] and
    [0, 255]. *)
From Stdlib Require Import ZArith SpecFloat Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Fpu.
Open Scope Z_scope.

Definition near_f32 (b : Z) : option Z :=
  match fp_decode fmt_single b with
  | S754_zero _ => Some 0
  | S754_finite s m e =>
      let v := if s then - Zpos m else Zpos m in
      Some (if 0 <=? e then v * 2^e else (2 * v + 2^(-e)) / 2^(1 - e))   (* floor (v 2^e + 1/2) *)
  | _ => None
  end.

Definition nearest (b lo hi : Z) : option Z :=
  match near_f32 b with
  | Some r => if (lo <=? r) && (r <=? hi) then Some r else None
  | None => None
  end.

Definition INT32_MIN : Z := -2^31.
Definition INT32_MAX : Z := 2^31 - 1.

(** ** The value is floor(f + 1/2) *)
(** For e < 0 the formula is floor((v 2^e + 1/2)), written over integers: v 2^e + 1/2 = (2v + 2^-e) / 2^(1-e). *)
Lemma near_f32_floor : forall b s m e, fp_decode fmt_single b = S754_finite s m e -> e < 0 ->
  let v := if s then - Zpos m else Zpos m in
  exists r, near_f32 b = Some r /\ r * 2^(1 - e) <= 2 * v + 2^(-e) < (r + 1) * 2^(1 - e).
Proof.
  intros b s m e H He v. unfold near_f32. rewrite H. fold v.
  destruct (Z.leb_spec 0 e) as [He'|_]; [lia|].
  eexists. split; [reflexivity|].
  assert (P : 0 < 2^(1 - e)) by (apply Z.pow_pos_nonneg; lia).
  pose proof (Z.div_mod (2 * v + 2^(-e)) (2^(1 - e)) ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound (2 * v + 2^(-e)) (2^(1 - e)) P) as M. lia.
Qed.

(** ** pod.h's own computation, in exact arithmetic, is [nearest] *)
(** The value of a finite binary32 pattern as N / D with D a power of 2. *)
Definition f32_ratio (b : Z) : option (Z * Z) :=
  match fp_decode fmt_single b with
  | S754_zero _ => Some (0, 1)
  | S754_finite s m e =>
      let v := if s then - Zpos m else Zpos m in
      Some (if 0 <=? e then (v * 2^e, 1) else (v, 2^(-e)))
  | _ => None
  end.

(** t = trunc(N / D), frac = N / D - t; r = t + 1 when frac >= 1/2, t - 1 when frac < -1/2 (pod.h:160-165). *)
Definition rhu_q (N D : Z) : Z :=
  Z.quot N D + (if D <=? 2 * (N - Z.quot N D * D) then 1 else 0)
  - (if 2 * (N - Z.quot N D * D) <? - D then 1 else 0).

(** pod_nearest(f, lo, hi, &out) (pod.h:152-171) with long double read as exact: NaN and the infinities give none
    (f != f; an infinity fails d >= lo - 1 or d <= hi + 1), then the early range test, then r, then the range. *)
Definition pod_nearest_exact (b lo hi : Z) : option Z :=
  match f32_ratio b with
  | None => None
  | Some (N, D) =>
      if (N <? (lo - 1) * D) || ((hi + 1) * D <? N) then None
      else if (lo <=? rhu_q N D) && (rhu_q N D <=? hi) then Some (rhu_q N D) else None
  end.

Lemma rhu_q_eq : forall N D, 0 < D -> rhu_q N D = (2 * N + D) / (2 * D).
Proof.
  intros N D HD. unfold rhu_q. set (t := Z.quot N D).
  assert (Hq : N = D * t + Z.rem N D) by (apply Z.quot_rem; lia).
  set (fr := Z.rem N D) in *.
  replace (N - t * D) with fr by lia.
  assert (Hp : 0 <= N -> 0 <= fr < D) by (intros; subst fr; apply Z.rem_bound_pos; lia).
  assert (Hn : N <= 0 -> - D < fr <= 0).
  { intros HN. subst fr. assert (Eo : Z.rem (- N) D = - Z.rem N D) by (apply Z.rem_opp_l; lia).
    pose proof (Z.rem_bound_pos (- N) D ltac:(lia) HD). lia. }
  destruct (Z.leb_spec D (2 * fr)); destruct (Z.ltb_spec (2 * fr) (- D)); [lia| | |].
  - apply (Z.div_unique _ _ _ (2 * fr + D - 2 * D)); [lia | rewrite Hq; ring].
  - apply (Z.div_unique _ _ _ (2 * fr + D + 2 * D)); [lia | rewrite Hq; ring].
  - apply (Z.div_unique _ _ _ (2 * fr + D)); [lia | rewrite Hq; ring].
Qed.

Lemma prefilter_lo : forall N D lo, 0 < D -> N < (lo - 1) * D -> (2 * N + D) / (2 * D) < lo.
Proof. intros N D lo HD H. apply Z.div_lt_upper_bound; lia. Qed.

Lemma prefilter_hi : forall N D hi, 0 < D -> (hi + 1) * D < N -> hi < (2 * N + D) / (2 * D).
Proof.
  intros N D hi HD H. assert (hi + 1 <= (2 * N + D) / (2 * D)) by (apply Z.div_le_lower_bound; lia). lia.
Qed.

Lemma near_f32_ratio : forall b, near_f32 b = option_map (fun ND => (2 * fst ND + snd ND) / (2 * snd ND)) (f32_ratio b)
  /\ (forall N D, f32_ratio b = Some (N, D) -> 0 < D).
Proof.
  intros b. unfold near_f32, f32_ratio. destruct (fp_decode fmt_single b) as [s|s| |s m e]; cbn [option_map fst snd].
  - split; [reflexivity|]. intros N D H. injection H as <- <-. lia.
  - split; [reflexivity | discriminate].
  - split; [reflexivity | discriminate].
  - destruct (Z.leb_spec 0 e) as [He|He]; cbn [fst snd]; split.
    + f_equal. apply (Z.div_unique _ _ _ 1); lia.
    + intros N D H. injection H as <- <-. lia.
    + f_equal. replace (1 - e) with (1 + - e) by lia. rewrite Z.pow_add_r by lia. reflexivity.
    + intros N D H. injection H as <- <-. apply Z.pow_pos_nonneg; lia.
Qed.

(** pod.h's computation, read exactly, is [nearest]: the early test drops only values whose nearest integer is out
    of range, and t + [frac >= 1/2] - [frac < -1/2] is floor(f + 1/2) for both signs. *)
Theorem pod_nearest_exact_eq : forall b lo hi, pod_nearest_exact b lo hi = nearest b lo hi.
Proof.
  intros b lo hi. unfold pod_nearest_exact, nearest. destruct (near_f32_ratio b) as [E HD]. rewrite E.
  destruct (f32_ratio b) as [[N D]|]; cbn [option_map fst snd]; [|reflexivity].
  specialize (HD N D eq_refl). rewrite rhu_q_eq by exact HD.
  destruct (Z.ltb_spec N ((lo - 1) * D)) as [H1|H1]; cbn [orb].
  - pose proof (prefilter_lo N D lo HD H1). destruct (Z.leb_spec lo ((2 * N + D) / (2 * D))); [lia | reflexivity].
  - destruct (Z.ltb_spec ((hi + 1) * D) N) as [H2|H2]; cbn [orb]; [|reflexivity].
    pose proof (prefilter_hi N D hi HD H2).
    destruct (Z.leb_spec ((2 * N + D) / (2 * D)) hi); [lia|]. rewrite andb_false_r. reflexivity.
Qed.

(** ** Witnesses at the instance the harnesses use (INT32_MIN, INT32_MAX) *)
(** 0.5 -> 1 (a half reads upward). *)
Lemma nearest_half : nearest 0x3f000000 INT32_MIN INT32_MAX = Some 1.
Proof. vm_compute. reflexivity. Qed.
(** 0.49999997 -> 0 (the float just below a half). *)
Lemma nearest_below_half : nearest 0x3effffff INT32_MIN INT32_MAX = Some 0.
Proof. vm_compute. reflexivity. Qed.
(** -0.5 -> 0 (a half reads upward for a negative value too). *)
Lemma nearest_neg_half : nearest 0xbf000000 INT32_MIN INT32_MAX = Some 0.
Proof. vm_compute. reflexivity. Qed.
(** -0.7 -> -1. *)
Lemma nearest_neg_07 : nearest 0xbf333333 INT32_MIN INT32_MAX = Some (-1).
Proof. vm_compute. reflexivity. Qed.
(** -0.49999997 -> 0. *)
Lemma nearest_neg_below_half : nearest 0xbeffffff INT32_MIN INT32_MAX = Some 0.
Proof. vm_compute. reflexivity. Qed.
(** NaN, +inf, -inf -> None. *)
Lemma nearest_nan : nearest 0x7fc00000 INT32_MIN INT32_MAX = None.
Proof. vm_compute. reflexivity. Qed.
Lemma nearest_inf : nearest 0x7f800000 INT32_MIN INT32_MAX = None /\ nearest 0xff800000 INT32_MIN INT32_MAX = None.
Proof. vm_compute. split; reflexivity. Qed.
(** 2147483520.0 (the largest float below 2^31) is in range; 2147483648.0 = 2^31 is not; -2^31 is; the float below
    it is not. *)
Lemma nearest_range_ends :
  nearest 0x4effffff INT32_MIN INT32_MAX = Some 2147483520 /\
  nearest 0x4f000000 INT32_MIN INT32_MAX = None /\
  nearest 0xcf000000 INT32_MIN INT32_MAX = Some (-2147483648) /\
  nearest 0xcf000001 INT32_MIN INT32_MAX = None.
Proof. vm_compute. repeat split; reflexivity. Qed.
(** 0.0 and -0.0 -> 0; 1.4999999 -> 1; 0.5000001 -> 1; the smallest subnormal -> 0; 1e10 is out of range. *)
Lemma nearest_misc :
  nearest 0x00000000 INT32_MIN INT32_MAX = Some 0 /\
  nearest 0x80000000 INT32_MIN INT32_MAX = Some 0 /\
  nearest 0x3fbfffff INT32_MIN INT32_MAX = Some 1 /\
  nearest 0x3f000002 INT32_MIN INT32_MAX = Some 1 /\
  nearest 0x00000001 INT32_MIN INT32_MAX = Some 0 /\
  nearest 0x80000001 INT32_MIN INT32_MAX = Some 0 /\
  nearest 0x501502f9 INT32_MIN INT32_MAX = None.
Proof. vm_compute. repeat split; reflexivity. Qed.
(** The headamp instance [0, 255]: 255.4 -> 255, 255.5 -> None, -0.5 -> 0. *)
Lemma nearest_byte_range :
  nearest 0x437f6666 0 255 = Some 255 /\ nearest 0x437f8000 0 255 = None /\ nearest 0xbf000000 0 255 = Some 0.
Proof. vm_compute. repeat split; reflexivity. Qed.
