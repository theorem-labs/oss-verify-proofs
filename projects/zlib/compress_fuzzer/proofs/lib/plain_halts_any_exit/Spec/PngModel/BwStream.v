(** * Spec.PngModel.BwStream — the deflate bit WRITER's abstraction function
      (round-trip layer L-C, part B).

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT.  Depends only on
    [Spec.PngModel.Base], [Spec.PngModel.Bits], [Spec.PngModel.ZBitsOut]
    and Stdlib.

    THE MISSING DUAL.  [Spec/PngModel/ZBitsBridge.v:47] gives the bit
    READER an abstraction into [list bool] ([br_stream]) and proves the two
    facts that make the reader's register machine speak L0's language:
    buffering is a no-op ([br_stream_pullbyte]) and consuming is [skipn]
    ([br_stream_dropbits]).  The WRITER had no such function.  That is why
    no lemma anywhere in the tree relates [Trees.v] to [Huff.v]: there was
    no vocabulary in which to state one.  This file supplies it —
    [bw_stream] — and the corresponding laws for all four emitters.

    LAYERING.  This is a bridge in the same sense as [ZBitsBridge.v]: it
    imports the TRANSCRIPTION ([ZBitsOut.v]) and L0's bit view ([Bits.v])
    and belongs to neither.  It does NOT import [Trees.v], [Huff.v] or
    [DeflateSpec.v] — the per-symbol layer is [EmitSym.v] and the seam that
    joins the two is a third file.  It also does not import [ZBitsIn.v] or
    [ZBitsBridge.v]: a writer bridge that depended on the reader's register
    machine to borrow an arithmetic lemma would be a dependency nobody can
    later remove.  See the DUPLICATION note in section 1.

    WHAT [bw_stream] IS.  A [BW] holds bytes already pushed to
    [pending_buf] plus up to sixteen bits still in the [bi_buf] register.
    The abstract stream is the concatenation, bytes first, and it is
    LSB-first throughout because that is what the binary does:
    [compress_block] at 0x418a8 in /harness/reference_binary emits the low
    byte of [bi_buf] before the high byte (0x41964 then 0x41984 after
    [srli 8]), and shifts each new value UP by [bi_valid] (0x4193c) so it
    occupies the next stream positions.  See §SYMID-STMT for the full
    instruction-level reading.

    THE DOMAIN BOUNDARY, and it is sharper than "bytes plus pending bits".
    [bw_out] is NOT a pure bit-writer queue.  [Deflate.putShortMSB]
    ([Deflate.v:552]) pushes two bytes into it with [bw_put_byte], HIGH BYTE
    FIRST — the opposite orientation from everything this file is about — and
    its callers are the zlib header ([Deflate.v:1132]), the dictionary adler
    ([:1134-1135]) and the trailing adler32 ([:1145]).  So [bw_out] is a
    MIXED queue, and [bw_stream] reads every byte in it as LSB-first bit
    stream, which is right for bit-writer output and MEANINGLESS for those.
    Three consequences a consumer must respect:
      - [bw_stream] and [bw_windup_bytes] are statements about the DEFLATE
        BIT STREAM only when [bw_out] holds bit-writer output alone.  The
        equations remain true as arithmetic whatever is in the queue —
        [bytes_bits] does not care — so nothing here is unsound, but calling
        the result "the deflate bit stream" in the presence of a header would
        be a misattribution of two bytes, in the direction that hides a
        two-byte offset error.
      - the zlib header is therefore OUTSIDE this abstraction, at the head of
        the byte queue rather than in the bit stream.
      - and it is rewritten again further downstream: libpng's
        [optimize_cmf] (0x32530, [pngwutil.c:243-286]) overwrites those two
        bytes AFTER deflate produced them, with a mod-31 fixup, and
        filter-id's audit (§FILTER-ID-CMF) measures EIGHT distinct (CMF,FLG)
        pairs across the synth family rather than the two literals a single
        measurement suggests.  So the bytes that reach the file at offsets 0
        and 1 are neither deflate's nor this file's.  Any inverse that starts
        from the EMITTED bytes must compose with that rewrite; an inverse
        that starts from the bit writer, as this one does, must not claim
        those two bytes at all.

    THE INVARIANT IS [<= 16], NOT [< 16], AND THAT IS A CORRECTION.
    [Trees.v:1478] ([tr_wf]'s [wf_bivalid]) carries
    [0 <= bw_valid < Buf_size], i.e. strictly less than 16.  That
    predicate is NOT closed under [bw_send_bits]: zlib's test is
    [bi_valid > Buf_size - length], so a send that lands EXACTLY on 16
    ([bi_valid = 16 - length]) takes the else-branch and leaves
    [bi_valid = 16].  It is reachable — any run of sends whose widths sum
    to 16 does it — and zlib is correct there for a reason worth writing
    down: the next send has [16 - length < 16], so it takes the flush
    branch, where [(ush)value << 16] truncates to zero inside the [ush]
    [bi_buf], so the merged value is [bi_buf] unchanged, the whole register
    is pushed out as a short, and [value >> (Buf_size - 16)] makes [value]
    the new register.  [ZBitsOut.v]'s model reproduces that exactly
    (it writes the [u16] out), so [bw_wf] below uses [<= 16] and is closed.
    [tr_wf] is STRICTLY STRONGER, so a caller holding [tr_wf] can supply
    [bw_wf] — no consumer is inconvenienced by the weakening, and
    [bw_valid_16_reachable] at the bottom exhibits the state [tr_wf]
    excludes, as a value. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Base Bits ZBitsOut.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** ** 1. Bit arithmetic over [Bits.write_bits]

    DUPLICATION, declared rather than hidden — AND PREFIXED, WHICH IS NOT
    COSMETIC.  [bw_write_bits_split] below is the same statement as
    [ZBitsBridge.v]'s [write_bits_split], and [bw_land_shiftl_disj] is
    [Common/ZChecksum.v:380]'s [land_shiftl_disj].  I originally gave them the
    SAME names as the originals and that was a defect: a duplicate is a
    judgement call, but a RIVAL NAME is a collision, and the window's rule is
    that collisions are resolved by rename before either version lands (a
    duplicate under a distinct name composes; two live definitions competing
    for one name make the next reader's [Locate] ambiguous and invite an
    import-order accident of exactly the kind §GTBL-PROD reported for the two
    [Code] records).  Caught by rt-scout's rival-name census, not by me — my
    own collision check tested the names I INVENTED and never the names I
    REUSED, which is precisely backwards.  Neither original is imported:
    [ZBitsBridge] would drag in the reader's register machine, and NO file
    in [Spec/PngModel] imports [Common] (checked: zero occurrences), so
    being the first would silently widen this layer's dependency footprint.
    Both facts are about [Bits.write_bits] and [Z], not about either
    machine, and they BELONG in [Bits.v]; the recommendation to the
    interface owner is to move them there and have all three consumers cite
    one copy.  Until then this comment is the pointer. *)

Lemma write_bits_zero : forall n, write_bits n 0 = repeat false n.
Proof.
  induction n as [|n IH]; [reflexivity|].
  cbn [write_bits repeat]. rewrite Z.div_0_l by lia. now rewrite IH.
Qed.

Lemma bw_write_bits_split :
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

(** [write_bits n] reads only bits [0..n-1], so reducing its argument mod
    [2^n] changes nothing.  Proved through [Bits.write_bits_testbit] rather
    than by induction, because that is the lemma that says exactly this. *)
Lemma write_bits_mod : forall n v,
  write_bits n (v mod 2 ^ Z.of_nat n) = write_bits n v.
Proof.
  intros n v. rewrite !write_bits_testbit.
  apply map_ext_in. intros i Hi.
  apply in_seq in Hi.
  apply Z.mod_pow2_bits_low. lia.
Qed.

(** No sign hypothesis: [Z]'s division is Euclidean, so
    [v = 2^k * (v/2^k) + v mod 2^k] holds for negative [v] too, and only the
    LOW piece needs a range (it is a [mod], so it has one).  That matters —
    [bw_put_short] is applied to values this file must not assume about. *)
(** [write_bits n] is determined by bits [0..n-1] of its argument.  The
    extensionality principle behind every [u8]/[u16] cast below: a cast
    changes only bits this width never reads. *)
Lemma write_bits_ext : forall n v w,
  (forall i, (i < n)%nat -> Z.testbit v (Z.of_nat i) = Z.testbit w (Z.of_nat i)) ->
  write_bits n v = write_bits n w.
Proof.
  intros n v w H. rewrite !write_bits_testbit.
  apply map_ext_in. intros i Hi. apply in_seq in Hi. apply H. lia.
Qed.

Lemma write_bits_cut : forall k n v,
  (k <= n)%nat ->
  write_bits n v
  = write_bits k (v mod 2 ^ Z.of_nat k) ++ write_bits (n - k) (v / 2 ^ Z.of_nat k).
Proof.
  intros k n v Hk.
  assert (Hp : 0 < 2 ^ Z.of_nat k) by (apply Z.pow_pos_nonneg; lia).
  rewrite <- bw_write_bits_split by (apply Z.mod_pos_bound; lia).
  replace (k + (n - k))%nat with n by lia.
  f_equal. rewrite Z.mul_comm, Z.add_comm. apply Z.div_mod. lia.
Qed.

Lemma bw_land_shiftl_disj : forall x y k,
  0 <= x < 2 ^ k -> 0 <= k -> 0 <= y -> Z.land x (Z.shiftl y k) = 0.
Proof.
  intros x y k Hx Hk Hy. apply Z.bits_inj'. intros m Hm.
  rewrite Z.land_spec, Z.bits_0, Z.shiftl_spec by lia.
  destruct (Z.ltb_spec m k) as [Hlt|Hge].
  - rewrite (Z.testbit_neg_r y (m - k)) by lia. apply Bool.andb_false_r.
  - replace (Z.testbit x m) with false; [reflexivity|].
    symmetry. apply Z.testbit_false; [lia|].
    rewrite Z.div_small; [reflexivity|].
    split; [lia|].
    eapply Z.lt_le_trans; [apply Hx|]. apply Z.pow_le_mono_r; lia.
Qed.

(** zlib's [|=] is an ADD, because the retained bits sit strictly below the
    incoming ones.  This is the only place the bit-level [lor] appears. *)
Lemma lor_shiftl_add : forall x y k,
  0 <= x < 2 ^ k -> 0 <= k -> 0 <= y ->
  Z.lor x (Z.shiftl y k) = x + y * 2 ^ k.
Proof.
  intros x y k Hx Hk Hy.
  assert (Hd := bw_land_shiftl_disj x y k Hx Hk Hy).
  rewrite <- Z.lxor_lor by exact Hd.
  rewrite <- Z.add_nocarry_lxor by exact Hd.
  rewrite Z.shiftl_mul_pow2 by lia. reflexivity.
Qed.

(** ** 2. Widths as [Z]

    [bw_valid] is a [Z] and [write_bits] takes a [nat]; [zwrite] keeps the
    conversion in one place instead of scattering [Z.to_nat] through every
    statement below. *)

Definition zwrite (n v : Z) : list bool := write_bits (Z.to_nat n) v.

Lemma zwrite_0 : forall v, zwrite 0 v = [].
Proof. reflexivity. Qed.

Lemma zwrite_length : forall n v, 0 <= n -> Z.of_nat (length (zwrite n v)) = n.
Proof. intros n v Hn. unfold zwrite. rewrite write_bits_length. lia. Qed.

Lemma zwrite_mod : forall n v, 0 <= n -> zwrite n (v mod 2 ^ n) = zwrite n v.
Proof.
  intros n v Hn. unfold zwrite.
  rewrite <- (write_bits_mod (Z.to_nat n) v).
  replace (2 ^ Z.of_nat (Z.to_nat n)) with (2 ^ n) by (f_equal; lia).
  reflexivity.
Qed.

Lemma zwrite_split : forall n m v w,
  0 <= n -> 0 <= m -> 0 <= v < 2 ^ n ->
  zwrite (n + m) (v + w * 2 ^ n) = zwrite n v ++ zwrite m w.
Proof.
  intros n m v w Hn Hm Hv. unfold zwrite.
  replace (Z.to_nat (n + m)) with (Z.to_nat n + Z.to_nat m)%nat by lia.
  replace (2 ^ n) with (2 ^ Z.of_nat (Z.to_nat n)) by (f_equal; lia).
  apply bw_write_bits_split.
  replace (Z.of_nat (Z.to_nat n)) with n by lia. exact Hv.
Qed.

Lemma zwrite_cut : forall k n v,
  0 <= k <= n ->
  zwrite n v = zwrite k (v mod 2 ^ k) ++ zwrite (n - k) (v / 2 ^ k).
Proof.
  intros k n v [Hk Hkn]. unfold zwrite.
  replace (Z.to_nat (n - k)) with (Z.to_nat n - Z.to_nat k)%nat by lia.
  rewrite (write_bits_cut (Z.to_nat k) (Z.to_nat n) v) by lia.
  replace (Z.of_nat (Z.to_nat k)) with k by lia. reflexivity.
Qed.

Lemma zwrite_zero : forall n, 0 <= n -> zwrite n 0 = repeat false (Z.to_nat n).
Proof. intros n Hn. unfold zwrite. apply write_bits_zero. Qed.

Lemma byte_bits_zwrite : forall v, byte_bits (u8 v) = zwrite 8 v.
Proof.
  intro v. unfold zwrite; cbn [Z.to_nat].
  rewrite byte_bits_u8. apply byte_bits_write_bits.
Qed.

(** The two bytes [put_short] pushes ARE the low sixteen bits of its
    argument, in LSB-first stream order.  Proved once and used at all four
    sites that emit a short ([put_short] itself, [send_bits]'s flush branch,
    [bi_flush] at a full register, [bi_windup] above eight bits) — the
    high-byte cast is where a bit-order defect would hide, so it is
    discharged in exactly one place. *)
Lemma bytes_bits_short : forall X,
  bytes_bits [u8 X; u8 (Z.shiftr (u16 X) 8)] = zwrite 16 X.
Proof.
  intro X. cbn [bytes_bits flat_map]. rewrite app_nil_r.
  rewrite (zwrite_cut 8 16 X) by lia.
  unfold zwrite; cbn [Z.to_nat].
  replace (Z.to_nat (16 - 8)) with 8%nat by lia.
  f_equal.
  - rewrite byte_bits_u8, byte_bits_write_bits.
    change (2 ^ 8) with (2 ^ Z.of_nat 8). now rewrite write_bits_mod.
  - rewrite byte_bits_u8, byte_bits_write_bits.
    apply write_bits_ext. intros i Hi.
    rewrite Z.shiftr_spec by lia.
    unfold u16. change 65536 with (2 ^ 16).
    rewrite Z.mod_pow2_bits_low by lia.
    rewrite <- Z.shiftr_div_pow2 by lia.
    rewrite Z.shiftr_spec by lia. reflexivity.
Qed.

(** ** 3. The abstraction function *)

Definition bw_stream (b : BW) : list bool :=
  bytes_bits (bw_out b) ++ zwrite (bw_valid b) (bw_buf b).

(** The closed invariant.  See the header: [<= Buf_size], not [<], and
    [Trees.tr_wf] is strictly stronger so it implies this. *)
Definition bw_wf (b : BW) : Prop :=
  0 <= bw_valid b <= Buf_size /\ 0 <= bw_buf b < 2 ^ bw_valid b.

Lemma bw_wf_init : bw_wf bw_init.
Proof.
  assert (HB : Buf_size = 16) by reflexivity.
  unfold bw_wf, bw_init; cbn. lia.
Qed.

Lemma bw_stream_init : bw_stream bw_init = [].
Proof. reflexivity. Qed.

(** ** 4. The two byte pushes

    [put_byte] appends to the byte QUEUE, so it inserts its bits BELOW the
    ones still pending in the register — it is a stream append only when
    the register is empty.  Stating it without that hypothesis would be
    wrong, and this is the shape of mistake the whole file exists to make
    impossible to write. *)

Lemma bw_put_byte_stream : forall v b,
  bw_valid b = 0 ->
  bw_stream (bw_put_byte v b) = bw_stream b ++ zwrite 8 v.
Proof.
  intros v b Hv. unfold bw_stream, bw_put_byte; cbn [bw_out bw_buf bw_valid].
  rewrite Hv, bytes_bits_app, !zwrite_0, !app_nil_r.
  cbn [bytes_bits flat_map]. rewrite app_nil_r.
  unfold zwrite. rewrite <- byte_bits_write_bits, byte_bits_u8. reflexivity.
Qed.

Lemma bw_put_short_stream : forall w b,
  bw_valid b = 0 ->
  bw_stream (bw_put_short w b) = bw_stream b ++ zwrite 16 w.
Proof.
  intros w b Hv. unfold bw_stream.
  rewrite bw_put_short_out, bytes_bits_app, bytes_bits_short.
  cbn [bw_put_short bw_put_byte bw_buf bw_valid].
  rewrite Hv, !zwrite_0, !app_nil_r. reflexivity.
Qed.

(** The unconditional half: the byte queue only ever grows at the tail, so
    the bits already handed out are never rewritten. *)
Lemma bw_out_prefix_stream : forall b,
  exists t, bw_stream b = bytes_bits (bw_out b) ++ t.
Proof. intro b. exists (zwrite (bw_valid b) (bw_buf b)). reflexivity. Qed.

(** ** 5. THE MAIN LAW: [send_bits] appends exactly its argument *)

Theorem bw_send_bits_stream : forall v n b,
  bw_wf b -> 0 <= n <= Buf_size -> 0 <= v < 2 ^ n ->
  bw_stream (bw_send_bits v n b) = bw_stream b ++ zwrite n v
  /\ bw_wf (bw_send_bits v n b).
Proof.
  intros v n b [[Hv0 Hv16] [Hb0 Hb1]] [Hn0 Hn16] [Hvlo Hvhi].
  assert (HB : Buf_size = 16) by reflexivity.
  assert (Hp16 : (0:Z) < 2 ^ Buf_size) by (apply Z.pow_pos_nonneg; cbn; lia).
  assert (Hpv : 0 < 2 ^ bw_valid b) by (apply Z.pow_pos_nonneg; lia).
  assert (Hpn : 0 < 2 ^ n) by (apply Z.pow_pos_nonneg; lia).
  (* the ush cast on the value is the identity: n <= 16 *)
  assert (Hu16v : u16 v = v).
  { apply u16_id. split; [lia|].
    eapply Z.lt_le_trans; [exact Hvhi|].
    change 65536 with (2 ^ Buf_size). apply Z.pow_le_mono_r; [lia|exact Hn16]. }
  (* the OR is an add *)
  assert (Hmerge : Z.lor (bw_buf b) (Z.shiftl (u16 v) (bw_valid b))
                   = bw_buf b + v * 2 ^ bw_valid b).
  { rewrite Hu16v. apply lor_shiftl_add; [split; lia|lia|lia]. }
  unfold bw_send_bits, bw_stream, bw_wf.
  rewrite Hmerge.
  (* [set] AFTER the rewrite that creates the term: folding before it exists
     leaves the goal holding the raw form while every later tactic names [X],
     and the two never meet. *)
  set (X := bw_buf b + v * 2 ^ bw_valid b).
  assert (HX0 : 0 <= X) by (unfold X; nia).
  destruct (Z.ltb_spec (Buf_size - n) (bw_valid b)) as [Hflush|Hkeep].
  - (* FLUSH branch: the register overflows, a whole short leaves *)
    assert (Hge : Buf_size <= bw_valid b + n) by lia.
    (* v / 2^(16-valid) = X / 2^16 *)
    assert (Hdiv : v / 2 ^ (Buf_size - bw_valid b) = X / 2 ^ Buf_size).
    { set (d := Buf_size - bw_valid b).
      assert (Hd0 : 0 <= d) by (unfold d; lia).
      assert (Hpd : 0 < 2 ^ d) by (apply Z.pow_pos_nonneg; lia).
      assert (Hsum : bw_valid b + d = Buf_size) by (unfold d; lia).
      pose proof (Z.div_mod v (2 ^ d) (Z.neq_sym _ _ (Z.lt_neq _ _ Hpd))) as Hqr.
      pose proof (Z.mod_pos_bound v (2 ^ d) Hpd) as [Hr0 Hr1].
      assert (Hpow : 2 ^ d * 2 ^ bw_valid b = 2 ^ Buf_size)
        by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
      assert (HXeq : X = (v / 2 ^ d) * 2 ^ Buf_size
                         + (bw_buf b + (v mod 2 ^ d) * 2 ^ bw_valid b)).
      { unfold X. rewrite Hqr at 1. rewrite <- Hpow. ring. }
      assert (Hlow : 0 <= bw_buf b + (v mod 2 ^ d) * 2 ^ bw_valid b < 2 ^ Buf_size).
      { split; [nia|].
        assert ((v mod 2 ^ d) * 2 ^ bw_valid b
                <= (2 ^ d - 1) * 2 ^ bw_valid b) by nia.
        assert ((2 ^ d - 1) * 2 ^ bw_valid b = 2 ^ Buf_size - 2 ^ bw_valid b)
          by (rewrite <- Hpow; ring).
        lia. }
      rewrite HXeq, Z.div_add_l by lia.
      rewrite (Z.div_small _ _ Hlow). lia. }
    cbn [bw_out bw_buf bw_valid].
    rewrite bw_put_short_out, bytes_bits_app.
    rewrite <- !app_assoc.
    split.
    + f_equal.
      rewrite bytes_bits_short.
      (* The [ush] cast on the merged register IS [mod 2 ^ Buf_size].  Keeping
         it in that form is what lets [zwrite_cut] fold the emitted short and
         the new register back into one [bw_valid + n] write. *)
      change (zwrite 16 (u16 X)) with (zwrite Buf_size (X mod 2 ^ Buf_size)).
      rewrite Z.shiftr_div_pow2 by lia. rewrite Hu16v, Hdiv.
      rewrite <- (zwrite_cut Buf_size (bw_valid b + n) X) by lia.
      unfold X. rewrite (zwrite_split (bw_valid b) n) by (try lia; split; lia).
      reflexivity.
    + rewrite Z.shiftr_div_pow2 by lia. rewrite Hu16v.
      split; [lia|].
      split; [apply Z.div_pos; lia|].
      apply Z.div_lt_upper_bound; [lia|].
      rewrite <- Z.pow_add_r by lia.
      replace (Buf_size - bw_valid b + (bw_valid b + n - Buf_size)) with n by lia.
      lia.
  - (* KEEP branch: everything stays in the register *)
    assert (Hle : bw_valid b + n <= Buf_size) by lia.
    assert (HXlt : X < 2 ^ (bw_valid b + n)).
    { unfold X. rewrite Z.pow_add_r by lia.
      assert (v * 2 ^ bw_valid b <= (2 ^ n - 1) * 2 ^ bw_valid b) by nia.
      nia. }
    assert (HXu : u16 X = X).
    { apply u16_id. split; [lia|].
      change 65536 with (2 ^ Buf_size).
      eapply Z.lt_le_trans; [exact HXlt|]. apply Z.pow_le_mono_r; lia. }
    cbn [bw_out bw_buf bw_valid].
    rewrite HXu.
    split.
    + rewrite <- app_assoc. f_equal.
      unfold X. rewrite (zwrite_split (bw_valid b) n) by (try lia; split; lia).
      reflexivity.
    + split; [lia|]. split; [unfold X; nia | exact HXlt].
Qed.

(** ** 6. [bi_flush] is a stream no-op

    The dual of [ZBitsBridge.br_stream_pullbyte] ("buffering is a no-op at
    spec level"), and for the same reason: moving bits from the register to
    the queue moves them across the [++] in [bw_stream] and nowhere else. *)

Theorem bw_flush_stream : forall b,
  bw_wf b -> bw_stream (bw_flush b) = bw_stream b /\ bw_wf (bw_flush b).
Proof.
  intros b [[Hv0 Hv16] [Hb0 Hb1]].
  assert (HB : Buf_size = 16) by reflexivity.
  assert (Hpv : 0 < 2 ^ bw_valid b) by (apply Z.pow_pos_nonneg; lia).
  unfold bw_flush, bw_stream, bw_wf.
  destruct (Z.eqb_spec (bw_valid b) 16) as [E16|E16].
  - cbn [bw_out bw_buf bw_valid].
    rewrite bw_put_short_out, bytes_bits_app, zwrite_0, app_nil_r.
    split; [|split; [lia|rewrite Z.pow_0_r; lia]].
    f_equal. rewrite E16. apply bytes_bits_short.
  - destruct (Z.leb_spec 8 (bw_valid b)) as [E8|E8].
    + cbn [bw_out bw_buf bw_valid].
      rewrite bw_put_byte_out, bytes_bits_app, <- app_assoc.
      split.
      * f_equal. cbn [bytes_bits flat_map]. rewrite app_nil_r.
        rewrite (zwrite_cut 8 (bw_valid b) (bw_buf b)) by lia.
        f_equal.
        -- rewrite byte_bits_zwrite. symmetry. apply zwrite_mod. lia.
        -- rewrite Z.shiftr_div_pow2 by lia. reflexivity.
      * split; [lia|].
        rewrite Z.shiftr_div_pow2 by lia.
        split; [apply Z.div_pos; lia|].
        apply Z.div_lt_upper_bound; [lia|].
        rewrite <- Z.pow_add_r by lia.
        replace (8 + (bw_valid b - 8)) with (bw_valid b) by lia. lia.
    + split; [reflexivity | split; lia].
Qed.

(** ** 7. [bi_windup] pads with zeros, and that is OBSERVABLE

    Not a no-op: [bi_windup] rounds the stream up to a byte boundary by
    emitting the register with its high bits (which are zero by the
    invariant) included.  Stating windup as stream-preserving would be
    FALSE, and the padding is exactly what a byte-level consumer sees, so
    it is named. *)

Definition bw_pad (b : BW) : Z :=
  if Z.ltb 8 (bw_valid b) then Buf_size - bw_valid b
  else if Z.ltb 0 (bw_valid b) then 8 - bw_valid b
  else 0.

Theorem bw_windup_stream : forall b,
  bw_wf b ->
  bw_stream (bw_windup b)
  = bw_stream b ++ repeat false (Z.to_nat (bw_pad b)).
Proof.
  intros b [[Hv0 Hv16] [Hb0 Hb1]].
  assert (HB : Buf_size = 16) by reflexivity.
  assert (Hpv : 0 < 2 ^ bw_valid b) by (apply Z.pow_pos_nonneg; lia).
  unfold bw_windup, bw_stream, bw_pad; cbn [bw_out bw_buf bw_valid].
  rewrite zwrite_0, app_nil_r.
  (* in every branch the emitted bytes are [zwrite W buf] for the branch
     width W, and buf's bits above bw_valid are zero *)
  assert (Hpad : forall W, bw_valid b <= W ->
            zwrite W (bw_buf b)
            = zwrite (bw_valid b) (bw_buf b) ++ repeat false (Z.to_nat (W - bw_valid b))).
  { intros W HW.
    rewrite (zwrite_cut (bw_valid b) W (bw_buf b)) by lia.
    rewrite (Z.mod_small (bw_buf b) (2 ^ bw_valid b)) by lia.
    f_equal. rewrite (Z.div_small (bw_buf b) (2 ^ bw_valid b)) by lia.
    apply zwrite_zero. lia. }
  destruct (Z.ltb_spec 8 (bw_valid b)) as [E8|E8].
  - rewrite bw_put_short_out, bytes_bits_app, <- app_assoc.
    f_equal.
    rewrite bytes_bits_short.
    change (zwrite 16 (bw_buf b)) with (zwrite Buf_size (bw_buf b)).
    apply Hpad. lia.
  - destruct (Z.ltb_spec 0 (bw_valid b)) as [E0|E0].
    + rewrite bw_put_byte_out, bytes_bits_app, <- app_assoc.
      f_equal.
      cbn [bytes_bits flat_map]. rewrite app_nil_r.
      replace (byte_bits (u8 (bw_buf b))) with (zwrite 8 (bw_buf b)).
      2:{ unfold zwrite; cbn [Z.to_nat].
          rewrite byte_bits_u8, byte_bits_write_bits. reflexivity. }
      apply Hpad. lia.
    + replace (bw_valid b) with 0 by lia.
      rewrite zwrite_0, app_nil_r. cbn [Z.to_nat repeat]. now rewrite app_nil_r.
Qed.

(** The reason windup matters to every consumer above this file: AFTER it,
    the abstract stream IS the byte stream, so a bit-level statement can be
    handed over as a statement about the bytes the harness actually
    compares. *)
Corollary bw_windup_bytes : forall b,
  bw_wf b ->
  bw_valid (bw_windup b) = 0
  /\ bw_stream (bw_windup b) = bytes_bits (bw_out (bw_windup b)).
Proof.
  intros b Hwf. split; [apply bw_windup_empty|].
  unfold bw_stream.
  destruct (bw_windup_empty b) as [_ Hv]. rewrite Hv, zwrite_0.
  apply app_nil_r.
Qed.

Lemma bw_windup_wf : forall b, bw_wf (bw_windup b).
Proof.
  intro b. assert (HB : Buf_size = 16) by reflexivity.
  unfold bw_wf. destruct (bw_windup_empty b) as [Hbuf Hval].
  rewrite Hbuf, Hval. cbn. lia.
Qed.

(** ** 8. Pins

    [bw_valid = 16] is REACHABLE, which is the header's correction to
    [Trees.tr_wf]'s [< Buf_size], exhibited as a value rather than argued:
    two 8-bit sends from an empty register land exactly on 16, and the
    third send still behaves — it pushes the full register out and installs
    the new value, which is what makes the [<= 16] invariant the right one. *)

Example bw_valid_16_reachable :
  bw_valid (bw_send_bits 170 8 (bw_send_bits 85 8 bw_init)) = 16
  /\ bw_out (bw_send_bits 170 8 (bw_send_bits 85 8 bw_init)) = [].
Proof. vm_compute. split; reflexivity. Qed.

Example bw_valid_16_then_send :
  let b := bw_send_bits 170 8 (bw_send_bits 85 8 bw_init) in
  bw_out (bw_send_bits 3 2 b) = [85; 170] /\ bw_valid (bw_send_bits 3 2 b) = 2.
Proof. vm_compute. split; reflexivity. Qed.

(** And the whole stream of those three sends is their concatenation — the
    main theorem, RUN, at a state [Trees.tr_wf] would have excluded. *)
Example bw_stream_three_sends :
  bw_stream (bw_send_bits 3 2 (bw_send_bits 170 8 (bw_send_bits 85 8 bw_init)))
  = zwrite 8 85 ++ zwrite 8 170 ++ zwrite 2 3.
Proof. vm_compute. reflexivity. Qed.

(** Windup's padding is not zero-width in general: a 2-bit register pads to
    a byte with six false bits, and the emitted byte is the value, not the
    value shifted. *)
Example bw_windup_pads_six :
  let b := bw_send_bits 3 2 bw_init in
  bw_pad b = 6 /\ bw_out (bw_windup b) = [3]
  /\ bw_stream (bw_windup b) = zwrite 2 3 ++ repeat false 6.
Proof. vm_compute. split; [reflexivity|split; reflexivity]. Qed.
