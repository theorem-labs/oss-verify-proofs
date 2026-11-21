(** * Spec.PngModel.Bits — the declarative LSB-first bit view of a byte list.

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT.  Depends only on
    [Spec.PngModel.Base] and Stdlib.

    L0: the SINGLE serialization point of the round-trip proof.  The
    encoder half produces a [list Z] of bytes; the decoder half consumes a
    bit stream.  They meet in [bytes_bits], and nowhere else.

    SCOPE.  This file is the SPECIFICATION side.  The OPERATIONAL bit
    reader — the one [inflate.c] actually runs, [Spec.PngModel.ZBitsIn]'s
    [BR] record and its [NEEDBITS]/[BITS]/[DROPBITS] macros — is a
    different file and a different lane's work; nothing here mentions it,
    duplicates it, or depends on it.  The refinement between the two is
    stated over [ZBitsIn.br_bytes] and is not proved here.

    BIT ORDER.  LSB first in both directions: the first bit of the stream
    is bit 0 of the first byte ([byte_bits]), and the first bit [read_bits]
    consumes becomes bit 0 of the value it returns.  This is RFC 1951
    §3.1.1's rule for DATA ELEMENTS.  Huffman CODES are packed starting
    from the most-significant bit of the code, so [read_bits] is NOT the
    reader for a Huffman code — that inversion is the caller's business and
    no claim about it is made here.  The order is pinned by the
    [reflexivity] tests at the bottom of this file, not by this comment:
    getting LSB/MSB backwards is the classic DEFLATE bug and a comment does
    not catch it.

    CONVENTIONS.  Bit COUNTS are [nat] (so [read_bits]/[write_bits] are
    plain structural recursions); VALUES and BYTES are [Z].  A byte is a [Z]
    in [[0,256)] ([Base.u8]'s range), but nothing here is dependent or
    partial: every definition is total, non-dependent, obligation-free
    Gallina, and [byte_bits] simply ignores everything above bit 7 of what
    it is handed ([byte_bits_u8]).

    DISCIPLINE.  Every claim any comment in this file makes is stated as a
    lemma below it.  Where a fact is merely NOT proved here, the comment
    says so explicitly rather than asserting it in passing. *)

From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Base.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** ** One byte

    The 8 bits of [b], LSB first.

    Written as an explicit 8-element list rather than as a [map]/fold over
    a range: [cbn] on this is 8 iota steps and no recursion, and this is
    the hottest definition in the layer.  It is deliberately a TOP-LEVEL
    definition — the encoder half's abstraction function is stated in terms
    of it directly. *)
Definition byte_bits (b : Z) : list bool :=
  [ Z.testbit b 0; Z.testbit b 1; Z.testbit b 2; Z.testbit b 3;
    Z.testbit b 4; Z.testbit b 5; Z.testbit b 6; Z.testbit b 7 ].

Lemma byte_bits_length : forall b, (length (byte_bits b) = 8)%nat.
Proof. reflexivity. Qed.

(** [byte_bits] looks only at the low 8 bits, so pushing [Base.u8] (the
    campaign's byte cast, [v mod 256]) through it is a no-op.  This is what
    makes it total on an out-of-range [Z] without a subtype: an argument
    outside [[0,256)] contributes exactly the bits its low byte would. *)
Lemma byte_bits_u8 : forall b, byte_bits (u8 b) = byte_bits b.
Proof.
  intro b. unfold byte_bits, u8. change 256 with (2 ^ 8).
  repeat (rewrite Z.mod_pow2_bits_low by lia). reflexivity.
Qed.

(** ** A byte list *)

Definition bytes_bits (bs : list Z) : list bool := flat_map byte_bits bs.

Lemma bytes_bits_nil : bytes_bits [] = [].
Proof. reflexivity. Qed.

Lemma bytes_bits_cons :
  forall b bs, bytes_bits (b :: bs) = byte_bits b ++ bytes_bits bs.
Proof. reflexivity. Qed.

(** The most-cited lemma of this interface: suffix invariance for the
    entire decoder rests on it. *)
Lemma bytes_bits_app :
  forall xs ys, bytes_bits (xs ++ ys) = bytes_bits xs ++ bytes_bits ys.
Proof. intros xs ys; apply flat_map_app. Qed.

(** The bit stream of a byte list is always a whole number of bytes long.
    Everything [align_byte] does below depends on this. *)
Lemma bytes_bits_length :
  forall bs, (length (bytes_bits bs) = 8 * length bs)%nat.
Proof.
  induction bs as [|b bs IH]; [reflexivity|].
  rewrite bytes_bits_cons, length_app, byte_bits_length, IH.
  cbn [length]. lia.
Qed.

(** Every split of the byte list is a split of the bit stream.  (The
    converse — that a bit-level split at a multiple of 8 always comes from
    a byte-level split — is NOT proved here; no L0 client needs it.) *)
Lemma bytes_bits_split : forall k bs,
  bytes_bits bs = bytes_bits (firstn k bs) ++ bytes_bits (skipn k bs).
Proof. intros k bs; rewrite <- bytes_bits_app, firstn_skipn; reflexivity. Qed.

(** If [bits] is what is left of [bytes_bits bs] after [pre], then the two
    pieces account for exactly [8 * length bs] bits.  The workhorse behind
    the [align_byte] facts at the end of the file. *)
Lemma bytes_bits_split_length : forall bs pre bits,
  bytes_bits bs = pre ++ bits ->
  (length pre + length bits = 8 * length bs)%nat.
Proof.
  intros bs pre bits H.
  rewrite <- bytes_bits_length, H, length_app. reflexivity.
Qed.

(** ** Reading

    [read_bits n bits] reads the first [n] bits of [bits], LSB first: the
    first bit read is bit 0 of the returned value.  It returns that value
    together with the REMAINDER of the stream — literally [skipn n bits]
    ([read_bits_rem]) — and [None] exactly when the stream runs out
    ([read_bits_none_iff]).

    SHAPE.  The recursion recurses FIRST and prepends afterwards: for [S n]
    on [b :: rest] it reads [n] bits from [rest] and then puts [b] in at
    the bottom.  Do NOT "simplify" this into an accumulator —
    [read_bits_write_bits] and [read_bits_app] are one-step inductions on
    [n] precisely because of this shape. *)
Fixpoint read_bits (n : nat) (bits : list bool) : option (Z * list bool) :=
  match n with
  | O => Some (0, bits)
  | S k =>
      match bits with
      | [] => None
      | b :: rest =>
          match read_bits k rest with
          | None => None
          | Some (v, rem) => Some ((if b then 1 else 0) + 2 * v, rem)
          end
      end
  end.

(** The "remainder" really is the tail after the [n] consumed bits. *)
Lemma read_bits_rem : forall n bits v rem,
  read_bits n bits = Some (v, rem) -> skipn n bits = rem.
Proof.
  induction n as [|n IH]; intros bits v rem H.
  - cbn [read_bits] in H. inversion H; subst. reflexivity.
  - destruct bits as [|b rest]; cbn [read_bits skipn] in H |- *; [discriminate|].
    destruct (read_bits n rest) as [[v' rem']|] eqn:E; [|discriminate].
    inversion H; subst. exact (IH rest v' rem E).
Qed.

Lemma read_bits_length : forall n bits v rem,
  read_bits n bits = Some (v, rem) -> (length rem + n = length bits)%nat.
Proof.
  induction n as [|n IH]; intros bits v rem H.
  - cbn [read_bits] in H. inversion H; subst. cbn. lia.
  - destruct bits as [|b rest]; cbn [read_bits] in H; [discriminate|].
    destruct (read_bits n rest) as [[v' rem']|] eqn:E; [|discriminate].
    inversion H; subst.
    specialize (IH rest v' rem E). cbn [length]. lia.
Qed.

(** [read_bits n] delivers exactly [n] bits' worth of value. *)
Lemma read_bits_bound : forall n bits v rem,
  read_bits n bits = Some (v, rem) -> 0 <= v < 2 ^ Z.of_nat n.
Proof.
  induction n as [|n IH]; intros bits v rem H.
  - cbn [read_bits] in H. inversion H; subst. cbn. lia.
  - destruct bits as [|b rest]; cbn [read_bits] in H; [discriminate|].
    destruct (read_bits n rest) as [[v' rem']|] eqn:E; [|discriminate].
    apply IH in E.
    (* [congruence], not [inversion]/[injection]: both of those run an
       internal [simpl] that unfolds [2 * v'] into a [match] on [v'] which
       [lia] cannot see through. *)
    assert (Hv : v = (if b then 1 else 0) + 2 * v') by congruence.
    rewrite Hv, Nat2Z.inj_succ, Z.pow_succ_r by lia.
    destruct b; lia.
Qed.

Corollary read_bits_nonneg : forall n bits v rem,
  read_bits n bits = Some (v, rem) -> 0 <= v.
Proof. intros n bits v rem H; apply read_bits_bound in H; lia. Qed.

(** [None] means, and only means, that the stream ran out. *)
Lemma read_bits_none_iff : forall n bits,
  read_bits n bits = None <-> (length bits < n)%nat.
Proof.
  induction n as [|n IH]; intros bits.
  - cbn [read_bits]. split; intro H; [discriminate|exfalso; lia].
  - destruct bits as [|b rest]; cbn [read_bits length].
    + split; intro H; [lia|reflexivity].
    + destruct (read_bits n rest) as [[v' rem']|] eqn:E.
      * split; intro H; [discriminate|exfalso].
        assert (Hs : (length rest < n)%nat) by lia.
        apply IH in Hs. rewrite E in Hs. discriminate.
      * split; intro H; [|reflexivity].
        assert (Hs : (length rest < n)%nat) by (apply IH; exact E). lia.
Qed.

(** SUFFIX INVARIANCE: appending to the far end of the stream changes
    nothing a successful read has already decided.  Together with
    [bytes_bits_app] this is what lets the decoder reason about one chunk
    at a time. *)
Lemma read_bits_app : forall n bits v rem extra,
  read_bits n bits = Some (v, rem) ->
  read_bits n (bits ++ extra) = Some (v, rem ++ extra).
Proof.
  induction n as [|n IH]; intros bits v rem extra H.
  - cbn [read_bits] in H |- *. inversion H; subst. reflexivity.
  - destruct bits as [|b rest]; cbn [read_bits app] in H |- *; [discriminate|].
    destruct (read_bits n rest) as [[v' rem']|] eqn:E; [|discriminate].
    rewrite (IH rest v' rem' extra E).
    inversion H; subst. reflexivity.
Qed.

(** ** Writing

    The inverse of [read_bits]: [write_bits n v] is the [n]-bit LSB-first
    encoding of [v].  It is total — for [v] outside [[0, 2^n)] it still
    produces exactly [n] bits ([write_bits_length]), namely bits [0..n-1]
    of [v]'s two's-complement expansion ([write_bits_testbit]) — but the
    round trip [read_bits_write_bits] needs the range hypothesis. *)
Fixpoint write_bits (n : nat) (v : Z) : list bool :=
  match n with
  | O => []
  | S k => Z.odd v :: write_bits k (v / 2)
  end.

Lemma write_bits_length : forall n v, (length (write_bits n v) = n)%nat.
Proof.
  induction n as [|n IH]; intro v; cbn [write_bits length]; [reflexivity|].
  now rewrite IH.
Qed.

(** [write_bits] emits bits [0 .. n-1] of [v], in that order. *)
Lemma write_bits_testbit : forall n v,
  write_bits n v = map (fun i => Z.testbit v (Z.of_nat i)) (seq 0 n).
Proof.
  induction n as [|n IH]; intro v; [reflexivity|].
  assert (Htail : write_bits n (v / 2)
                  = map (fun i : nat => Z.testbit v (Z.of_nat i)) (seq 1 n)).
  { rewrite IH, <- seq_shift, map_map. apply map_ext; intro i.
    rewrite Nat2Z.inj_succ. apply Z.div2_bits. lia. }
  cbn [write_bits seq map]. rewrite Htail.
  (* heads: [Z.odd v] and [Z.testbit v (Z.of_nat 0)] are convertible *)
  reflexivity.
Qed.

(** The byte view IS the 8-bit writer.  This is the coherence fact that
    makes [byte_bits] and [read_bits]/[write_bits] one interface rather
    than two unrelated definitions; it needs no range hypothesis because
    both sides read the same 8 bits of [v]'s two's-complement expansion. *)
Lemma byte_bits_write_bits : forall b, byte_bits b = write_bits 8%nat b.
Proof. intro b. rewrite write_bits_testbit. reflexivity. Qed.

(** ** The encoder/decoder handshake

    The reason [write_bits] lives in L0 at all. *)
Lemma read_bits_write_bits : forall n v rest,
  0 <= v < 2 ^ Z.of_nat n ->
  read_bits n (write_bits n v ++ rest) = Some (v, rest).
Proof.
  induction n as [|n IH]; intros v rest Hv; cbn [write_bits app read_bits].
  - cbn in Hv. assert (v = 0) by lia. subst. reflexivity.
  - assert (Hv2 : 0 <= v / 2 < 2 ^ Z.of_nat n).
    { rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hv by lia.
      split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
    rewrite (IH (v / 2) rest Hv2). cbn [fst snd].
    f_equal. f_equal.
    rewrite <- Z.div2_div.
    pose proof (Z.div2_odd v) as Hd.
    destruct (Z.odd v); cbn [Z.b2z] in Hd; lia.
Qed.

(** Specialised to one byte: reading 8 bits off the front of a byte
    stream returns that byte and the rest of the stream. *)
Lemma read_bits_byte_bits : forall b rest,
  0 <= b < 256 -> read_bits 8%nat (byte_bits b ++ rest) = Some (b, rest).
Proof.
  intros b rest Hb. rewrite byte_bits_write_bits.
  apply read_bits_write_bits. change (2 ^ Z.of_nat 8) with 256. exact Hb.
Qed.

Lemma read_bits_bytes_bits_cons : forall b bs,
  0 <= b < 256 ->
  read_bits 8%nat (bytes_bits (b :: bs)) = Some (b, bytes_bits bs).
Proof.
  intros b bs Hb. rewrite bytes_bits_cons. now apply read_bits_byte_bits.
Qed.

(** ** Byte alignment

    [align_byte bits] drops the [length bits mod 8] leading bits of [bits].

    WHY THAT COUNT, AND WHAT IT DEPENDS ON.  [align_byte] is only
    meaningful relative to a stream produced by [bytes_bits], whose length
    is always a multiple of 8 ([bytes_bits_length]).  Under that hypothesis,
    if [bits] is the unconsumed suffix of [bytes_bits bs] then dropping
    [length bits mod 8] bits leaves a suffix whose length is a multiple of
    8 ([align_byte_aligned]) — equivalently, it advances the CONSUMED
    prefix to a multiple of 8, i.e. to a byte boundary of the original
    stream ([align_byte_boundary]).

    Note what [length bits mod 8] is NOT.  It is the number of bits
    REMAINING in the current partial byte, not the number already consumed
    from it: those two differ ([align_byte_consumed_in_byte] gives the
    consumed count as [(8 - length bits mod 8) mod 8]).  Stating this
    dependency is the point of the last two lemmas — without a
    multiple-of-8 stream, "align" here is just a length computation and
    means nothing. *)
Definition align_byte (bits : list bool) : list bool :=
  skipn ((length bits) mod 8)%nat bits.

Lemma align_byte_length : forall bits,
  (length (align_byte bits) = length bits - length bits mod 8)%nat.
Proof. intro bits; unfold align_byte; apply length_skipn. Qed.

(** Unconditionally: the result is a whole number of bytes long. *)
Lemma align_byte_aligned : forall bits,
  ((length (align_byte bits)) mod 8 = 0)%nat.
Proof.
  intro bits. rewrite align_byte_length.
  pose proof (Nat.Div0.div_mod (length bits) 8) as H.
  pose proof (Nat.mod_upper_bound (length bits) 8 ltac:(lia)) as Hb.
  replace (length bits - length bits mod 8)%nat
     with (8 * (length bits / 8))%nat by lia.
  rewrite Nat.mul_comm. apply Nat.Div0.mod_mul.
Qed.

(** It only ever drops a prefix, and the dropped prefix has exactly the
    advertised length. *)
Lemma align_byte_suffix : forall bits,
  firstn (length bits mod 8)%nat bits ++ align_byte bits = bits.
Proof. intro bits; apply firstn_skipn. Qed.

Lemma align_byte_dropped : forall bits : list bool,
  (length (firstn (length bits mod 8)%nat bits) = length bits mod 8)%nat.
Proof.
  intro bits. rewrite length_firstn.
  pose proof (Nat.Div0.mod_le (length bits) 8). lia.
Qed.

(** Aligning an aligned stream does nothing. *)
Lemma align_byte_idem : forall bits,
  align_byte (align_byte bits) = align_byte bits.
Proof.
  intro bits. unfold align_byte at 1.
  rewrite align_byte_aligned. reflexivity.
Qed.

(** THE DEPENDENCY, stated.  If [bits] is the unconsumed suffix of a
    [bytes_bits] stream, then after dropping [length bits mod 8] bits the
    total number of consumed bits is a multiple of 8 — the alignment point
    is a byte boundary of the ORIGINAL stream, which is the only reason the
    operation deserves its name. *)
Lemma align_byte_boundary : forall bs pre bits,
  bytes_bits bs = pre ++ bits ->
  ((length pre + length bits mod 8) mod 8 = 0)%nat.
Proof.
  intros bs pre bits H.
  pose proof (bytes_bits_split_length bs pre bits H) as HE.
  pose proof (Nat.Div0.div_mod (length bits) 8) as HL.
  pose proof (Nat.mod_upper_bound (length bits) 8 ltac:(lia)) as HbL.
  replace (length pre + length bits mod 8)%nat
     with (8 * (length bs - length bits / 8))%nat by lia.
  rewrite Nat.mul_comm. apply Nat.Div0.mod_mul.
Qed.

(** And the correction to the tempting misreading: the bits ALREADY
    consumed from the current byte number [(8 - length bits mod 8) mod 8],
    not [length bits mod 8]. *)
Lemma align_byte_consumed_in_byte : forall bs pre bits,
  bytes_bits bs = pre ++ bits ->
  (length pre mod 8 = (8 - length bits mod 8) mod 8)%nat.
Proof.
  intros bs pre bits H.
  pose proof (bytes_bits_split_length bs pre bits H) as HE.
  pose proof (Nat.Div0.div_mod (length bits) 8) as HL.
  pose proof (Nat.Div0.div_mod (length pre) 8) as HP.
  pose proof (Nat.mod_upper_bound (length bits) 8 ltac:(lia)) as HbL.
  pose proof (Nat.mod_upper_bound (length pre) 8 ltac:(lia)) as HbP.
  destruct (Nat.eq_dec (length bits mod 8) 0) as [E|E].
  - rewrite E in HL |- *. change ((8 - 0) mod 8)%nat with 0%nat. lia.
  - rewrite (Nat.mod_small (8 - length bits mod 8) 8) by lia. lia.
Qed.

(** ** Bit-order tests

    These pin the LSB-first convention by computation.  A comment cannot
    catch an MSB/LSB inversion; [reflexivity] can. *)

(** [6 = ]: bit 0 clear, bits 1 and 2 set, the rest clear. *)
Example byte_bits_6 :
  byte_bits 6 = [false; true; true; false; false; false; false; false].
Proof. reflexivity. Qed.

Example bytes_bits_0_255_1 :
  bytes_bits [0; 255; 1] =
    [false; false; false; false; false; false; false; false;
     true;  true;  true;  true;  true;  true;  true;  true;
     true;  false; false; false; false; false; false; false].
Proof. reflexivity. Qed.

(** The reader agrees: the first bit off the stream is bit 0 of the value. *)
Example read_bits_6 :
  read_bits 3%nat (byte_bits 6) = Some (6, [false; false; false; false; false]).
Proof. reflexivity. Qed.

Example write_bits_6 : write_bits 3%nat 6 = [false; true; true].
Proof. reflexivity. Qed.

(** And the two agree on a whole byte, in both directions. *)
Example read_bits_byte_255 :
  read_bits 8%nat (bytes_bits [255; 7]) = Some (255, bytes_bits [7]).
Proof. reflexivity. Qed.
