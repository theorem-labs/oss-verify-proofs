(** * Spec.PngModel.ZBitsBridge — the reader/spec abstraction function.

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT.

    This file exists because the abstraction function between a
    transcription state and an L0 spec object belongs to NEITHER side.
    [ZBitsIn.v] is the bug-for-bug transcription of zlib's [hold]/[bits]
    register machine and must not depend on the declarative spec;
    [Bits.v] is L0's frozen surface and must not depend on the
    transcription.  A bridge that imports both keeps each of those true.
    (Layering call by the interface arbiter, 2026-08-16.)

    WHAT WAS WRONG BEFORE.  An earlier bridge expression circulated as

      skipn (8 * br_next b - br_bits b) (bytes_bits (br_bytes b))

    and it is WRONG against the [br_bytes] that shipped.  That formula is
    correct only over the WHOLE input buffer indexed from 0, where there
    is a consumed prefix to skip.  [ZBitsIn.br_bytes] returns only the
    [br_have] bytes from [br_next] on, so there is no prefix and the
    [skipn] cuts into live data; worse, the bits already in [br_hold] came
    from bytes at indices BELOW [br_next] ([br_pullbyte] reads
    [br_in b (br_next b)] and only then advances), so they are not in
    [br_bytes] at all and no amount of skipping recovers them.  Concretely,
    at [br_in = [10;20;30;40]], [br_next = 2], [br_have = 2], [br_bits = 4]
    the true unconsumed bit count is [br_bits + 8 * br_have = 20] and that
    formula yields 4.  (Caught by wp2-fpstep while building [Bits.v]; the
    wrong version was in the manifest, never in the code — [ZBitsIn.v]'s
    own header always stated the correct one.)

    The correct abstraction is the pending bits of [hold] followed by the
    unread bytes.  It is also strictly the nicer one, because it makes the
    refinement story true rather than aspirational: [br_pullbyte] moves a
    byte out of the list and into [hold], and the two changes CANCEL, so
    buffering is a no-op at spec level ([br_stream_pullbyte]);
    [br_dropbits], the operation that actually consumes, is exactly
    [skipn] ([br_stream_dropbits]). *)

From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Base Bits ZBitsIn.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** ** The abstraction function *)

Definition br_stream (b : BR) : list bool :=
  write_bits (Z.to_nat (br_bits b)) (br_hold b) ++ bytes_bits (br_bytes b).

(** ** Splitting a write

    The arithmetic fact the whole bridge rests on: a value that fits in
    [n] bits, with more value shifted in above it, writes as the
    concatenation of the two pieces. *)

Lemma write_bits_split :
  forall n m v w,
    0 <= v < 2 ^ Z.of_nat n ->
    write_bits (n + m) (v + w * 2 ^ Z.of_nat n) = write_bits n v ++ write_bits m w.
Proof.
  induction n as [|n IH]; intros m v w [Hlo Hhi].
  - cbn [Nat.add write_bits app] in *.
    assert (v = 0) by (cbn in Hhi; lia). subst v.
    now rewrite Z.mul_1_r, Z.add_0_l.
  - assert (Hp : 0 < 2 ^ Z.of_nat n) by (apply Z.pow_pos_nonneg; lia).
    assert (He : 2 ^ Z.of_nat (S n) = 2 * 2 ^ Z.of_nat n).
    { rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. ring. }
    rewrite He in *.
    cbn [Nat.add write_bits app].
    replace (v + w * (2 * 2 ^ Z.of_nat n))
      with (v + (w * 2 ^ Z.of_nat n) * 2) by ring.
    f_equal.
    + rewrite (Z.mul_comm (w * 2 ^ Z.of_nat n) 2). apply Z.odd_add_mul_2.
    + rewrite Z.div_add by lia.
      apply IH. split; [apply Z.div_pos; lia|].
      apply Z.div_lt_upper_bound; lia.
Qed.

(** ** Skipping a write *)

Lemma write_bits_skipn :
  forall k n v,
    0 <= v ->
    skipn k (write_bits n v) = write_bits (n - k) (v / 2 ^ Z.of_nat k).
Proof.
  induction k as [|k IH]; intros n v Hv.
  - cbn [skipn]. rewrite Nat.sub_0_r.
    change (Z.of_nat 0) with 0. rewrite Z.pow_0_r, Z.div_1_r. reflexivity.
  - destruct n as [|n]; cbn [write_bits skipn Nat.sub].
    + reflexivity.
    + rewrite IH by (apply Z.div_pos; lia).
      f_equal.
      rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
      rewrite Zdiv_Zdiv by lia. f_equal; try ring.
Qed.

(** ** The two refinement facts *)

Lemma br_stream_pullbyte :
  forall b b', br_wf b -> br_pullbyte b = Some b' -> br_stream b' = br_stream b.
Proof.
  intros b b' (Hbits & Hhold & Hhave & Hin) H.
  pose proof (br_pullbyte_step b b' H) as (Hh & Hn & Hb & Hi).
  assert (Hby : br_bytes b = br_in b (br_next b) :: br_bytes b')
    by (apply br_bytes_pullbyte; [lia|exact H]).
  assert (Hho : br_hold b' = br_hold b + br_in b (br_next b) * 2 ^ br_bits b).
  { unfold br_pullbyte in H.
    destruct (Z.eqb (br_have b) 0); [discriminate|].
    inversion H; cbn [br_hold]. rewrite Z.shiftl_mul_pow2 by lia. reflexivity. }
  assert (Hid : Z.of_nat (Z.to_nat (br_bits b)) = br_bits b) by lia.
  assert (Hsucc : Z.to_nat (br_bits b + 8) = (Z.to_nat (br_bits b) + 8)%nat) by lia.
  assert (Hrange : 0 <= br_hold b < 2 ^ Z.of_nat (Z.to_nat (br_bits b))).
  { rewrite Hid. rewrite Z.shiftl_mul_pow2 in Hhold by lia. lia. }
  unfold br_stream. rewrite Hby, Hho, Hb, Hsucc.
  rewrite <- Hid at 2.
  cbn [bytes_bits flat_map].
  rewrite write_bits_split by exact Hrange.
  rewrite <- byte_bits_write_bits, app_assoc. reflexivity.
Qed.

Lemma br_stream_dropbits :
  forall n b,
    0 <= n <= br_bits b -> 0 <= br_hold b ->
    br_stream (br_dropbits n b) = skipn (Z.to_nat n) (br_stream b).
Proof.
  intros n b [Hlo Hhi] Hho.
  unfold br_stream.
  rewrite br_bytes_dropbits, br_dropbits_bits.
  replace (br_hold (br_dropbits n b)) with (Z.shiftr (br_hold b) n) by reflexivity.
  rewrite skipn_app, write_bits_length.
  replace (Z.to_nat n - Z.to_nat (br_bits b))%nat with 0%nat by lia.
  cbn [skipn].
  rewrite write_bits_skipn by exact Hho.
  rewrite Z.shiftr_div_pow2 by lia.
  replace (Z.to_nat (br_bits b - n))
    with (Z.to_nat (br_bits b) - Z.to_nat n)%nat by lia.
  replace (2 ^ n) with (2 ^ Z.of_nat (Z.to_nat n)) by (f_equal; lia).
  reflexivity.
Qed.

(** [br_bytebits] is [br_dropbits] at a legal count, so it too is a
    [skipn] — the byte-alignment operation aligns the abstract stream. *)
Lemma br_stream_bytebits :
  forall b, br_wf b ->
    br_stream (br_bytebits b) = skipn (Z.to_nat (Z.land (br_bits b) 7)) (br_stream b).
Proof.
  intros b (Hbits & Hhold & _ & _). unfold br_bytebits.
  assert (Hl : Z.land (br_bits b) 7 = br_bits b mod 8).
  { replace 7 with (Z.ones 3) by reflexivity.
    rewrite Z.land_ones by lia. reflexivity. }
  rewrite Hl.
  apply br_stream_dropbits; [|lia].
  pose proof (Z.mod_pos_bound (br_bits b) 8 ltac:(lia)).
  split; [lia | apply Z.mod_le; lia].
Qed.
