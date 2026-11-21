(** * Bridge.BrAdler — pair 37 of PAIRS.md: Adler-32, S5 model vs RT model.

    S5 (compress_fuzzer tree) computes Adler-32 in two spellings:
      - deflate's [read_buf] calls [Z.DeflateLz.adler32_upd], which takes the
        C's [len == 1] fast path ([adler32_len1]) and otherwise the
        mathematical [Z.ZChecksum.adler32_model] (reduce mod BASE per byte);
      - inflate's [UPDATE_CHECK] calls [Z.InflateState.iadler32_upd], which is
        [adler32_model] at every length.
    RT (round-trip campaign) has one C-faithful transcription,
    [Spec.PngModel.Checksum.adler32_z] (len-1 path, NMAX blocking, 16-byte
    unrolling), and the closed form [GtAdlerChunk.adler32_z_closed_form].

    Bridge style: EQUALITY of pure functions, stated at the call shapes both
    models use ([isnull = false]).  The deflate-side equation needs only that
    the chunk is bytes; the inflate-side one also needs the incoming check
    value canonical ([AdWf]: both 16-bit halves below 65521), which holds along
    every run (it starts at 1 and every result is canonical,
    [GtAdlerChunk.ad_closed_is_adwf]). *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require ZChecksum DeflateLz InflateState.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Checksum.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require GtAdlerChunk.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Definition bytes (bs : list Z) : Prop := forall b, In b bs -> 0 <= b < 256.

(* ------------------------------------------------------------------------- *)
(* 1.  S5's mathematical model is RT's closed form                           *)
(* ------------------------------------------------------------------------- *)

Lemma ad_run_adl_raw : forall bs s1 s2,
  Checksum.a_adler (Checksum.ad_run {| Checksum.a_adler := s1 ; Checksum.a_sum2 := s2 |} bs)
    = fst (ZChecksum.adl_raw bs s1 s2)
  /\ Checksum.a_sum2 (Checksum.ad_run {| Checksum.a_adler := s1 ; Checksum.a_sum2 := s2 |} bs)
    = snd (ZChecksum.adl_raw bs s1 s2).
Proof.
  induction bs as [|b bs IH]; intros s1 s2.
  - split; reflexivity.
  - exact (IH (s1 + b) (s2 + (s1 + b))).
Qed.

Lemma lor_shiftl_lxor : forall x y,
  0 <= x < 65536 -> 0 <= y ->
  Z.lor x (Z.shiftl y 16) = Z.lxor (Z.shiftl y 16) x.
Proof.
  intros x y Hx Hy. rewrite Z.lxor_comm.
  apply Z.bits_inj'. intros n Hn.
  rewrite Z.lor_spec, Z.lxor_spec.
  destruct (Z.ltb_spec n 16) as [Hlt|Hge].
  - rewrite (Z.shiftl_spec_low y 16 n) by lia. now destruct (Z.testbit x n).
  - rewrite (ZChecksum.testbit_high x 16 n) by lia.
    now destruct (Z.testbit (Z.shiftl y 16) n).
Qed.

Theorem ad_closed_s5_model : forall a bs,
  GtAdlerChunk.ad_closed a bs = ZChecksum.adler32_model a bs.
Proof.
  intros a bs. unfold GtAdlerChunk.ad_closed, GtAdlerChunk.ad_state0, ZChecksum.adler32_model.
  cbv zeta.
  destruct (ad_run_adl_raw bs (Z.land a 65535) (Z.land (Z.shiftr a 16) 65535)) as [E1 E2].
  rewrite E1, E2, ZChecksum.adl_raw_mod. cbv beta iota. cbn [fst snd].
  unfold Checksum.ADLER_BASE, ZChecksum.ABASE.
  apply lor_shiftl_lxor.
  - pose proof (Z.mod_pos_bound (fst (ZChecksum.adl_raw bs (Z.land a 65535)
                                       (Z.land (Z.shiftr a 16) 65535))) 65521 ltac:(lia)). lia.
  - pose proof (Z.mod_pos_bound (snd (ZChecksum.adl_raw bs (Z.land a 65535)
                                       (Z.land (Z.shiftr a 16) 65535))) 65521 ltac:(lia)). lia.
Qed.

(* ------------------------------------------------------------------------- *)
(* 2.  The len-1 fast paths agree for EVERY adler and byte                   *)
(* ------------------------------------------------------------------------- *)

Lemma mod16_land : forall x, x mod 2 ^ 16 = Z.land x 65535.
Proof.
  intros x. replace 65535 with (Z.ones 16) by reflexivity.
  rewrite Z.land_ones by lia. reflexivity.
Qed.

Lemma mod32_div16 : forall x, (x mod 2 ^ 32) / 2 ^ 16 = Z.land (Z.shiftr x 16) 65535.
Proof.
  intros x. replace 65535 with (Z.ones 16) by reflexivity.
  rewrite Z.land_ones, Z.shiftr_div_pow2 by lia.
  replace (2 ^ 32) with (2 ^ 16 * 2 ^ 16) by reflexivity.
  rewrite Z.rem_mul_r by lia.
  rewrite Z.mul_comm, Z.div_add by lia.
  rewrite Z.div_small by (apply Z.mod_pos_bound; lia). lia.
Qed.

Lemma csub_eq : forall x,
  DeflateLz.adler_csub x = (if Z.leb Checksum.ADLER_BASE x then x - Checksum.ADLER_BASE else x).
Proof.
  intros x. unfold DeflateLz.adler_csub, Checksum.ADLER_BASE.
  destruct (Z.ltb_spec 65520 x), (Z.leb_spec 65521 x); lia.
Qed.

Lemma csub_range : forall x, 0 <= x -> 0 <= DeflateLz.adler_csub x.
Proof. intros x Hx. unfold DeflateLz.adler_csub. destruct (Z.ltb_spec 65520 x); lia. Qed.

Theorem br_adler32_len1 : forall a c,
  DeflateLz.adler32_len1 a c = Checksum.adler32_z a false [c].
Proof.
  intros a c. unfold DeflateLz.adler32_len1, Checksum.adler32_z. cbn [length nth Z.of_nat Z.eqb].
  rewrite mod16_land, mod32_div16, !csub_eq.
  set (lo := if Z.leb Checksum.ADLER_BASE (Z.land a 65535 + c)
             then Z.land a 65535 + c - Checksum.ADLER_BASE else Z.land a 65535 + c).
  rewrite (Z.add_comm lo (Z.land (Z.shiftr a 16) 65535)).
  set (hi := if Z.leb Checksum.ADLER_BASE (Z.land (Z.shiftr a 16) 65535 + lo)
             then Z.land (Z.shiftr a 16) 65535 + lo - Checksum.ADLER_BASE
             else Z.land (Z.shiftr a 16) 65535 + lo).
  rewrite Z.lor_comm, <- Z.shiftl_mul_pow2 by lia. reflexivity.
Qed.

(* ------------------------------------------------------------------------- *)
(* 3.  The two call-site bridges                                             *)
(* ------------------------------------------------------------------------- *)

(** Deflate side ([read_buf], [deflateSetDictionary]): no hypothesis on the
    incoming adler — the len-1 paths agree unconditionally (§2) and off it RT's
    closed form needs none either ([adler32_z_closed_form_nn]). *)
Theorem br_adler32_upd : forall a bs,
  bytes bs -> DeflateLz.adler32_upd a bs = Checksum.adler32_z a false bs.
Proof.
  intros a bs Hb.
  destruct bs as [|c [|c' r]].
  - cbn [DeflateLz.adler32_upd].
    rewrite GtAdlerChunk.adler32_z_closed_form_nn.
    + symmetry. apply ad_closed_s5_model.
    + split; [exact Hb | discriminate].
    + cbn. discriminate.
  - apply br_adler32_len1.
  - change (DeflateLz.adler32_upd a (c :: c' :: r)) with (ZChecksum.adler32_model a (c :: c' :: r)).
    rewrite GtAdlerChunk.adler32_z_closed_form_nn.
    + symmetry. apply ad_closed_s5_model.
    + split; [exact Hb | discriminate].
    + cbn [length]. lia.
Qed.

(** Inflate side ([UPDATE_CHECK], [inflateSetDictionary]): S5 uses the
    mathematical model at every length, RT the C's [adler32] with its len-1
    path, so the incoming check must be canonical ([AdWf]). *)
Theorem br_iadler32_upd : forall a bs,
  GtAdlerChunk.AdWf a -> bytes bs ->
  InflateState.iadler32_upd a bs = Checksum.adler32_z a false bs.
Proof.
  intros a bs Ha Hb. unfold InflateState.iadler32_upd.
  rewrite GtAdlerChunk.adler32_z_closed_form by (exact Ha || (split; [exact Hb | discriminate])).
  symmetry. apply ad_closed_s5_model.
Qed.

(** The invariant that discharges [AdWf] along a run: every S5 result is
    canonical, whatever the incoming value. *)
Theorem s5_adler32_model_adwf : forall a bs, GtAdlerChunk.AdWf (ZChecksum.adler32_model a bs).
Proof. intros a bs. rewrite <- ad_closed_s5_model. apply GtAdlerChunk.ad_closed_is_adwf. Qed.

(** Initial values: S5's [adler32_init]/[iadler32_init] (the literal 1) are
    RT's [adler32_z 0 true []] (deflate_reset / inflate's HEAD arm). *)
Theorem br_adler32_init :
  DeflateLz.adler32_init = Checksum.adler32_z 0 true []
  /\ InflateState.iadler32_init = Checksum.adler32_z 0 true [].
Proof. split; vm_compute; reflexivity. Qed.

(* ------------------------------------------------------------------------- *)
(* 4.  Non-vacuity probes (computed, both sides)                             *)
(* ------------------------------------------------------------------------- *)

Example probe_check9 :
  DeflateLz.adler32_upd 1 [49;50;51;52;53;54;55;56;57] = 152961502
  /\ Checksum.adler32_z 1 false [49;50;51;52;53;54;55;56;57] = 152961502.
Proof. split; vm_compute; reflexivity. Qed.

(** A non-canonical incoming value: the len-1 paths still agree (§2), but S5's
    inflate spelling (the model) and RT's [adler32_z] DIFFER — so [AdWf] in
    [br_iadler32_upd] is a real hypothesis, not decoration.  Witness: sum2
    half 65535 (>= BASE), adler half 65300, byte 210, so the C's single
    conditional subtraction leaves sum2 = 65524 >= BASE while the model
    reduces it to 3. *)
Example probe_noncanonical :
  let a := Z.lor (Z.shiftl 65535 16) 65300 in
  DeflateLz.adler32_upd a [210] = Checksum.adler32_z a false [210]
  /\ InflateState.iadler32_upd a [210] <> Checksum.adler32_z a false [210].
Proof. cbv zeta. split; vm_compute; [reflexivity | discriminate]. Qed.

Print Assumptions br_adler32_upd.
Print Assumptions br_iadler32_upd.
Print Assumptions s5_adler32_model_adwf.
Print Assumptions br_adler32_init.
