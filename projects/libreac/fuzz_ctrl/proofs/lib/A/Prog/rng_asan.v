(* Footprint ranges for the ASan runs of this image (form (D), RECIPE.md step 1 (a working note, not in this delivery)).
   IMG_LO / IMG_LEN: the page-rounded LOAD range of the image (fuzz_ctrl.asan PT_LOAD segments 0x10000 .. 0x5fd0f0,
   rounded up to 0x5fe000). Relocated from fuzz_pcap (a working branch 0ce4d3317ea): namespace only.
   IMG_LO and IMG_HI are ImgBounds.v's (Require Export below); IMG_LEN is the notation IMG_HI - IMG_LO.
   [sh_lo p, sh_lo p + sh_len p n): the shadow bytes of the n bytes at p, widened to whole aligned 8-byte shadow
   words: from the word that holds shadow_addr p to the end of the word that holds shadow_addr (p + n - 1); empty
   when n = 0. The runtime's range check loads whole aligned 8-byte shadow words (omx-clap-core/fuzz_manifest lib/A/Prog/asan_memset.v qc_word; ported from a working branch 07c251d9c8d, namespace and IMG_LEN only),
   so a callee contract needs the widened range. An aligned 8-byte word lies in one 4096-byte page, so the widened
   range touches the same pages as the exact one. It is correct for an unaligned range too. *)
From Stdlib Require Import ZArith Lia.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Export ImgBounds.
Open Scope Z_scope.

Notation IMG_LEN := (IMG_HI - IMG_LO).

Definition sh_lo (p : Z) : Z := 8 * (shadow_addr p / 8).
Definition sh_len (p n : Z) : Z := if n =? 0 then 0 else 8 * (shadow_addr (p + n - 1) / 8) + 8 - sh_lo p.

Lemma sh_len_nonneg : forall p n, 0 <= n -> 0 <= sh_len p n.
Proof.
  intros p n Hn. unfold sh_len, sh_lo, shadow_addr. destruct (Z.eqb_spec n 0); cbv iota; [lia|].
  Z.div_mod_to_equations. lia.
Qed.

(* The widened shadow range of a sub-range [p', p' + n') of [p, p + n) lies in that of [p, p + n). *)
Lemma rng_sh_sub : forall RNG p n p' n', 0 <= n' -> p <= p' -> p' + n' <= p + n ->
  rng RNG (sh_lo p) (sh_len p n) -> rng RNG (sh_lo p') (sh_len p' n').
Proof.
  intros RNG p n p' n' Hn' Hp Hq (A & B & H).
  unfold sh_len, sh_lo, shadow_addr in *.
  destruct (Z.eqb_spec n' 0) as [E'|E']; destruct (Z.eqb_spec n 0) as [E|E]; cbv iota in *.
  - assert (p' = p) by lia. subst p'. split; [lia|]. split; [lia|]. exact H.
  - split; [Z.div_mod_to_equations; lia|]. split; [Z.div_mod_to_equations; lia|].
    intros b j Hb Hj. apply H; Z.div_mod_to_equations; lia.
  - lia.
  - split; [Z.div_mod_to_equations; lia|]. split; [Z.div_mod_to_equations; lia|].
    intros b j Hb Hj. apply H; Z.div_mod_to_equations; lia.
Qed.

(* One shadow byte of a byte a of [p, p + n) (an instrumented check of a) lies in the widened range. *)
Lemma rng_sh_byte : forall RNG p n a, p <= a < p + n ->
  rng RNG (sh_lo p) (sh_len p n) -> rng RNG (shadow_addr a) 1.
Proof.
  intros RNG p n a Ha (A & B & H). unfold sh_len, sh_lo, shadow_addr in *.
  destruct (Z.eqb_spec n 0) as [E|E]; cbv iota in *; [lia|].
  split; [Z.div_mod_to_equations; lia|]. split; [Z.div_mod_to_equations; lia|].
  intros b j Hb Hj. apply H; Z.div_mod_to_equations; lia.
Qed.

(* With the footprint that admits every access, the widened shadow range of any in-range buffer is a range. *)
Lemma rng_all_sh : forall p n, 0 <= p -> 0 <= n -> p + n <= 2 ^ 64 -> rng RNG_all (sh_lo p) (sh_len p n).
Proof.
  intros p n Hp Hn Hpn. apply rng_all; unfold sh_len, sh_lo, shadow_addr, ASAN_K;
    destruct (Z.eqb_spec n 0); cbv iota; Z.div_mod_to_equations; lia.
Qed.

(* ---- the 8-aligned shadow WORD span: the shadow premises of asan_memcpy_cF.v and asan_memset_cF.v ----
   One home for both statements (a Theorem Labs lane finding O3: each of the two files carried its own verbatim copy, so
   a file importing both saw two constants under each short name). The definitions, the lemmas and their proofs
   below are those copies verbatim; ExF.footprint / ExF.rng / ExF.RNG_all / ExF.rng_all there are the
   ExecF.footprint / ExecF.rng / ExecF.RNG_all / ExecF.rng_all imported here, so each definition unfolds to the
   same term as before. *)

(* The 8-aligned shadow WORD span of the byte range [p, p + n).

   The shadow BYTES of [p, p + n) are shadow_addr p .. shadow_addr (p + n - 1) (shadow_addr a = a / 8 + ASAN_K,
   one shadow byte per 8-byte granule). The quick check loads ALIGNED 8-byte shadow words, so it can touch up
   to 7 shadow bytes below shadow_addr p and up to 7 above shadow_addr (p + n - 1): the span below rounds the
   first shadow byte DOWN to a multiple of 8 and the last one UP, and so covers whole shadow words only.
   rewalk-F-policy.md: "the recipe's unaligned byte form is a lower bound the proof cannot use".

   In application bytes the span therefore covers the granules of at most 56 bytes before p and at most 56
   bytes after p + n - 1, on top of [p, p + n) itself.

   n = 0 is guarded: with n = 0 the helper checks nothing, and shadow_addr (p - 1) can sit below
   shadow_addr p, so the span is not even well formed (rewalk-F-policy.md, "N=0 guard ... wherever a size
   can be 0"). *)
Definition sh_al8_lo (p : Z) : Z := shadow_addr p / 8 * 8.
Definition sh_al8_hi (p n : Z) : Z := shadow_addr (p + n - 1) / 8 * 8 + 8.
Definition sh_word_rng (RNG : footprint) (p n : Z) : Prop :=
  n = 0 \/ rng RNG (sh_al8_lo p) (sh_al8_hi p n - sh_al8_lo p).

(* rng wants its upper bound against 2^64; keep the numeral available to lia. *)
Lemma two64 : (2^64)%Z = 18446744073709551616%Z.
Proof. reflexivity. Qed.

Lemma al8_bounds : forall x : Z, 0 <= x -> 0 <= x / 8 * 8 <= x.
Proof.
  intros x Hx.
  pose proof (Z.div_mod x 8 ltac:(lia)) as E.
  pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as B.
  pose proof (Z.div_pos x 8 Hx ltac:(lia)) as P.
  lia.
Qed.

Lemma shadow_addr_bounds : forall x : Z, 0 <= x -> 0 <= shadow_addr x <= x + ASAN_K.
Proof.
  intros x Hx. unfold shadow_addr.
  pose proof (Z.div_mod x 8 ltac:(lia)) as E.
  pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as B.
  pose proof (Z.div_pos x 8 Hx ltac:(lia)) as P.
  unfold ASAN_K. lia.
Qed.

Lemma sh_word_rng_all : forall p n : Z,
  0 <= p -> 0 <= n -> p + n <= APPMEM_END -> sh_word_rng RNG_all p n.
Proof.
  intros p n Hp Hn Hpn. unfold sh_word_rng.
  destruct (Z.eq_dec n 0) as [Hz|Hz]; [left; exact Hz| right].
  unfold sh_al8_lo, sh_al8_hi.
  assert (Hq : 0 <= p + n - 1) by lia.
  pose proof (shadow_addr_bounds p Hp) as Bp.
  pose proof (shadow_addr_bounds (p + n - 1) Hq) as Bq.
  pose proof (al8_bounds (shadow_addr p) (proj1 Bp)) as Ap.
  pose proof (al8_bounds (shadow_addr (p + n - 1)) (proj1 Bq)) as Aq.
  pose proof two64 as H64.
  apply rng_all; unfold ASAN_K, APPMEM_END in *; lia.
Qed.

(* The bridge between the two conventions of this file: the word span of [p, p + n) is the widened range
   [sh_lo p, sh_lo p + sh_len p n), with the same n = 0 guard. For n > 0 the bounds agree up to the order of a
   product (sh_lo p = 8 * (shadow_addr p / 8), sh_al8_lo p = shadow_addr p / 8 * 8), so the two sides are equal
   only propositionally, not by unfolding. With it, rng_sh_sub, rng_sh_byte and rng_all_sh apply to sh_word_rng
   spans. *)
Lemma sh_word_rng_iff_sh : forall RNG p n,
  sh_word_rng RNG p n <-> (n = 0 \/ rng RNG (sh_lo p) (sh_len p n)).
Proof.
  intros RNG p n. unfold sh_word_rng.
  destruct (Z.eqb_spec n 0) as [E|E]; [split; intros _; left; exact E|].
  replace (sh_lo p) with (sh_al8_lo p) by (unfold sh_lo, sh_al8_lo; ring).
  replace (sh_len p n) with (sh_al8_hi p n - sh_al8_lo p)
    by (unfold sh_len; destruct (Z.eqb_spec n 0); [lia|]; cbv iota; unfold sh_al8_hi, sh_al8_lo, sh_lo; ring).
  exact (iff_refl _).
Qed.
