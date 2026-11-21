(** * Spec.PngModel.StoredRt — the STORED-block round trip (round-trip layer
      L-C, the stored arm of L4's symbol half).

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT.  Depends on
    [Spec.PngModel.{Base, Bits, Huff, DeflateSpec, ZBitsOut, Trees, BwStream}].
    Adds no [Definition] any model function calls; edits nothing.

    WHICH ARTIFACT, because the two are easy to conflate and rt-scout measured
    them apart.  This file is about **[Trees.tr_stored_block]**
    ([Trees.v:956], [trees.c:858-873]) — the BLOCK ARM that [_tr_flush_block]
    selects on cost, LIVE at 307 of 1970 blocks across the whole size range
    including 25 above 8 KiB, confirmed on riscv64.  It says **nothing** about
    [deflate_stored] (0x37868), which is 0-reached and dead in this build:
    that function is level-0-only and nothing sets level 0.

    WHAT IS PROVED.  The stored block is the one BTYPE whose payload is not
    Huffman coded, so its inverse is a byte copy — but the framing around it
    is where the content is, and two parts of it are not free:

    THE COMPLEMENT.  [decode_stored] tests [Z.lxor len nlen = 65535] and the
    emitter writes [u16 (- stored_len - 1)] — the C's [(ush)~stored_len].  So
    the obligation is that a two's-complement negate-and-decrement truncated
    to sixteen bits IS the bitwise complement.  [- v - 1] is [Z.lnot v] by
    definition, so it reduces to [Z.lnot v mod 2^16 = Z.lxor 65535 v] for
    [0 <= v < 65536], proved below by bit extensionality.  Nothing of that
    shape existed in the tree (the only [Z.lnot] occurrence is
    [Deflate.v:942], in the dead [deflate_stored] path, with no lemma).

    THE ALIGNMENT, which is the part worth reading.  [Bits.align_byte] is
    [skipn (length bits mod 8) bits] — a LENGTH computation, not a position —
    and [DeflateSpec.v]'s own header says it is meaningful only because the
    enclosing stream came from [bytes_bits] and so has length divisible by 8.
    That is why every statement here carries [length tail mod 8 = 0].  It is
    not a convenience hypothesis: it is exactly what makes the DECODER's
    alignment equal the WRITER's padding, so [align_byte] drops precisely the
    zeros [bi_windup] wrote and not one bit more.  Drop it and the theorem is
    FALSE; [align_needs_byte_tail] exhibits that as a value rather than
    asserting it. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff DeflateSpec ZBitsOut Trees BwStream.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** ** 1. Negate-and-decrement, truncated, is complement *)

(** A value below 2^16 has no bits at or above 16.  Stated locally rather than
    via [Z.bits_above_log2], which needs [0 < v] and so fails at [v = 0] — the
    stored block of length zero, which is a real case. *)
Lemma testbit_high16 : forall v i, 0 <= v < 2 ^ 16 -> 16 <= i -> Z.testbit v i = false.
Proof.
  intros v i Hv Hi. apply Z.testbit_false; [lia|].
  rewrite Z.div_small; [reflexivity|].
  split; [lia|]. eapply Z.lt_le_trans; [apply Hv|]. apply Z.pow_le_mono_r; lia.
Qed.

Lemma lnot_mod16 : forall v, 0 <= v < 65536 -> u16 (- v - 1) = Z.lxor 65535 v.
Proof.
  intros v Hv. unfold u16.
  change 65536 with (2 ^ 16) in *.
  apply Z.bits_inj'. intros i Hi.
  destruct (Z.lt_ge_cases i 16) as [Hlt|Hge].
  - rewrite Z.mod_pow2_bits_low by lia.
    replace (- v - 1) with (Z.lnot v) by (unfold Z.lnot; lia).
    rewrite Z.lnot_spec by lia.
    rewrite Z.lxor_spec.
    replace 65535 with (Z.ones 16) by (rewrite Z.ones_equiv; lia).
    rewrite Z.ones_spec_low by lia. reflexivity.
  - rewrite Z.mod_pow2_bits_high by lia.
    rewrite Z.lxor_spec.
    replace 65535 with (Z.ones 16) by (rewrite Z.ones_equiv; lia).
    rewrite Z.ones_spec_high by lia.
    rewrite (testbit_high16 v i Hv Hge). reflexivity.
Qed.

Lemma xor_complement : forall v, 0 <= v < 65536 -> Z.lxor v (u16 (- v - 1)) = 65535.
Proof.
  intros v Hv. rewrite (lnot_mod16 v Hv).
  rewrite (Z.lxor_comm 65535 v), <- Z.lxor_assoc, Z.lxor_nilpotent.
  apply Z.lxor_0_l.
Qed.

(** ** 2. Reading back a byte list *)

Lemma read_bytes_bytes_bits : forall bs tail,
  read_bytes (length bs) (bytes_bits bs ++ tail) = Some (map u8 bs, tail).
Proof.
  induction bs as [|b bs IH]; intro tail; cbn [length read_bytes map].
  - rewrite bytes_bits_nil. reflexivity.
  - rewrite bytes_bits_cons, <- app_assoc.
    rewrite <- byte_bits_u8.
    rewrite read_bits_byte_bits by (unfold u8; pose proof (Z.mod_pos_bound b 256); lia).
    rewrite IH. reflexivity.
Qed.

(** ** 3. Alignment: the decoder's [skipn] IS the writer's padding

    ONLY under a byte-aligned tail.  That is the whole dependency. *)

Lemma align_byte_pad : forall pad rest,
  (pad < 8)%nat -> (length rest mod 8 = 0)%nat ->
  align_byte (repeat false pad ++ rest) = rest.
Proof.
  intros pad rest Hp Hr. unfold align_byte.
  rewrite length_app, repeat_length.
  replace ((pad + length rest) mod 8)%nat with pad.
  2:{ rewrite Nat.Div0.add_mod, Hr, Nat.add_0_r by lia.
      rewrite Nat.Div0.mod_mod. symmetry. apply Nat.mod_small. exact Hp. }
  rewrite skipn_app, repeat_length, skipn_all2 by (rewrite repeat_length; lia).
  rewrite Nat.sub_diag. cbn [skipn]. reflexivity.
Qed.

(** ** 4. The emitted body, and THE DECODER INVERTS IT *)

Definition stored_tail (dat : list Z) (stored_len : Z) (pad : nat) : list bool :=
  repeat false pad
  ++ zwrite 16 stored_len
  ++ zwrite 16 (u16 (- stored_len - 1))
  ++ bytes_bits (map u8 dat).

Lemma stored_tail_length : forall dat stored_len pad,
  (length (stored_tail dat stored_len pad) = pad + 32 + 8 * length dat)%nat.
Proof.
  intros dat stored_len pad. unfold stored_tail, zwrite.
  rewrite !length_app, repeat_length, !write_bits_length.
  rewrite bytes_bits_length, length_map. cbn [Z.to_nat]. lia.
Qed.

Theorem decode_stored_tail : forall dat stored_len pad tail,
  stored_len = Z.of_nat (length dat) ->
  0 <= stored_len < 65536 ->
  (pad < 8)%nat -> (length tail mod 8 = 0)%nat ->
  decode_stored (stored_tail dat stored_len pad ++ tail)
    = Some (map u8 dat, tail).
Proof.
  intros dat stored_len pad tail Hlen Hrange Hp Ht.
  unfold decode_stored, stored_tail.
  rewrite <- !app_assoc.
  (* the alignment drops exactly the padding *)
  rewrite align_byte_pad; [| exact Hp |].
  2:{ unfold zwrite. rewrite !length_app, !write_bits_length, bytes_bits_length,
        length_map. cbn [Z.to_nat].
      (* the tail's byte-alignment, as a multiple rather than as a mod fact, so
         the arithmetic is linear and [lia] can finish it *)
      pose (k := (length tail / 8)%nat).
      assert (Hk : (length tail = 8 * k)%nat)
        by (unfold k; pose proof (Nat.Div0.div_mod (length tail) 8); lia).
      rewrite Hk.
      match goal with
      | |- (?X mod 8 = 0)%nat => replace X with (8 * (4 + length dat + k))%nat by lia
      end.
      rewrite Nat.mul_comm. apply Nat.Div0.mod_mul. }
  (* LEN *)
  unfold zwrite at 1. cbn [Z.to_nat].
  rewrite read_bits_write_bits by (change (2 ^ Z.of_nat 16) with 65536; lia).
  (* NLEN *)
  unfold zwrite at 1. cbn [Z.to_nat].
  rewrite read_bits_write_bits
    by (change (2 ^ Z.of_nat 16) with 65536; unfold u16;
        pose proof (Z.mod_pos_bound (- stored_len - 1) 65536); lia).
  (* the complement check *)
  rewrite (proj2 (Z.eqb_eq _ _) (xor_complement stored_len Hrange)).
  (* the payload *)
  replace (Z.to_nat stored_len) with (length (map u8 dat))
    by (rewrite length_map; lia).
  rewrite read_bytes_bytes_bits.
  (* [map u8] is idempotent on an already-truncated list *)
  f_equal. f_equal. rewrite map_map. apply map_ext. intro b.
  unfold u8. rewrite Zmod_mod. reflexivity.
Qed.

(** THE NECESSITY WITNESS for the byte-aligned tail, as a VALUE.  With one
    stray bit in the tail the alignment slips by one and the decode is not
    merely weaker, it is WRONG — here it fails outright. *)
Example align_needs_byte_tail :
  decode_stored (stored_tail [65] 1 3 ++ [true]) <> Some (map u8 [65], [true]).
Proof. vm_compute. intro H. discriminate H. Qed.

Example stored_tail_roundtrips :
  decode_stored (stored_tail [65; 66; 67] 3 5 ++ repeat false 8)
  = Some ([65; 66; 67], repeat false 8).
Proof. vm_compute. reflexivity. Qed.

(** ** 5. The emitter appends exactly that *)

Theorem tr_stored_block_stream : forall dat stored_len last s,
  bw_wf (ts_bw s) -> 0 <= last <= 1 -> 0 <= stored_len < 65536 ->
  exists pad,
    (pad < 8)%nat
    /\ bw_stream (ts_bw (tr_stored_block dat stored_len last s))
       = bw_stream (ts_bw s)
         ++ zwrite 3 (Z.shiftl STORED_BLOCK 1 + last)
         ++ stored_tail dat stored_len pad.
Proof.
  intros dat stored_len last s Hwf Hlast Hrange.
  unfold tr_stored_block, set_bw; cbn [ts_bw].
  (* the 3-bit header *)
  destruct (bw_send_bits_stream (Z.shiftl STORED_BLOCK 1 + last) 3 (ts_bw s)
                                Hwf ltac:(unfold Buf_size; lia)
                                ltac:(unfold STORED_BLOCK; cbn; lia)) as [S0 W0].
  set (b0 := bw_send_bits (Z.shiftl STORED_BLOCK 1 + last) 3 (ts_bw s)) in *.
  (* windup pads to the byte boundary *)
  pose proof (bw_windup_stream b0 W0) as S1.
  pose proof (bw_windup_wf b0) as W1.
  destruct (bw_windup_empty b0) as [Hbuf1 Hval1].
  set (b1 := bw_windup b0) in *.
  assert (Hpad : 0 <= bw_pad b0 < 8).
  { destruct W0 as [[Hv0 Hv16] _]. unfold bw_pad.
    destruct (Z.ltb_spec 8 (bw_valid b0)); [unfold Buf_size in *; lia|].
    destruct (Z.ltb_spec 0 (bw_valid b0)); lia. }
  (* the two shorts, each appending 16 bits because the register is empty *)
  pose proof (bw_put_short_stream stored_len b1 Hval1) as S2.
  set (b2 := bw_put_short stored_len b1) in *.
  assert (Hval2 : bw_valid b2 = 0)
    by (unfold b2, bw_put_short, bw_put_byte; cbn [bw_valid]; exact Hval1).
  pose proof (bw_put_short_stream (u16 (- stored_len - 1)) b2 Hval2) as S3.
  set (b3 := bw_put_short (u16 (- stored_len - 1)) b2) in *.
  assert (Hval3 : bw_valid b3 = 0)
    by (unfold b3, bw_put_short, bw_put_byte; cbn [bw_valid]; exact Hval2).
  exists (Z.to_nat (bw_pad b0)).
  split; [lia|].
  (* the payload is appended to the QUEUE directly, not through the writer *)
  unfold bw_stream; cbn [bw_out bw_buf bw_valid].
  rewrite Hval3, zwrite_0, app_nil_r, bytes_bits_app.
  unfold bw_stream in S3, S2, S1, S0.
  rewrite Hval3, zwrite_0, app_nil_r in S3.
  rewrite Hval2, zwrite_0, app_nil_r in S3, S2.
  rewrite Hval1, zwrite_0, app_nil_r in S2, S1.
  rewrite S3, S2, S1, S0.
  unfold stored_tail.
  rewrite <- !app_assoc. reflexivity.
Qed.

(** ** 6. The composition — the form a consumer wants

    The emitter's stream delta splits into a three-bit block header and a
    BODY, and the body is what [decode_stored] inverts.  ld-seams' covered-
    choice split consumes exactly this shape; their own bridge supplies [dat]
    from [tr_flush_block]'s window bytes. *)

Corollary tr_stored_block_roundtrip : forall dat stored_len last s tail,
  bw_wf (ts_bw s) -> 0 <= last <= 1 ->
  stored_len = Z.of_nat (length dat) -> 0 <= stored_len < 65536 ->
  (length tail mod 8 = 0)%nat ->
  exists body,
    bw_stream (ts_bw (tr_stored_block dat stored_len last s))
      = bw_stream (ts_bw s) ++ zwrite 3 (Z.shiftl STORED_BLOCK 1 + last) ++ body
    /\ decode_stored (body ++ tail) = Some (map u8 dat, tail).
Proof.
  intros dat stored_len last s tail Hwf Hlast Hlen Hrange Ht.
  destruct (tr_stored_block_stream dat stored_len last s Hwf Hlast Hrange)
    as [pad [Hp Hs]].
  exists (stored_tail dat stored_len pad).
  split; [exact Hs | apply decode_stored_tail; assumption].
Qed.

(** PREFIXED ON PURPOSE.  This lemma was named [map_u8_id] when the file
    landed, and that generic name collided with ld-seams' LdWin.v -- a clash I
    created by landing a helper whose name nobody could have guessed was taken.
    The prefix is the fix; the lesson is that my pre-flight census was REACTIVE
    (rename what the census found) rather than SYSTEMATIC (prefix every generic
    helper), so a second block's names went unchecked. *)
Lemma stored_map_u8_id : forall bs, Forall (fun b => 0 <= b < 256) bs -> map u8 bs = bs.
Proof.
  induction bs as [|b bs IH]; intro H; [reflexivity|].
  inversion H as [|b' bs' Hb Hbs]; subst.
  cbn [map]. rewrite (IH Hbs). f_equal. apply u8_id, Hb.
Qed.

(** And the refinement for a consumer that already holds genuine bytes: the
    payload comes back as ITSELF, not as its truncation. *)
Corollary tr_stored_block_roundtrip_bytes : forall dat stored_len last s tail,
  bw_wf (ts_bw s) -> 0 <= last <= 1 ->
  stored_len = Z.of_nat (length dat) -> 0 <= stored_len < 65536 ->
  (length tail mod 8 = 0)%nat ->
  Forall (fun b => 0 <= b < 256) dat ->
  exists body,
    bw_stream (ts_bw (tr_stored_block dat stored_len last s))
      = bw_stream (ts_bw s) ++ zwrite 3 (Z.shiftl STORED_BLOCK 1 + last) ++ body
    /\ decode_stored (body ++ tail) = Some (dat, tail).
Proof.
  intros dat stored_len last s tail Hwf Hlast Hlen Hrange Ht Hbytes.
  destruct (tr_stored_block_roundtrip dat stored_len last s tail
              Hwf Hlast Hlen Hrange Ht) as [body [Hs Hd]].
  exists body. split; [exact Hs|].
  rewrite Hd, (stored_map_u8_id dat Hbytes). reflexivity.
Qed.

(** ** 7. THE CROSS-LANE EXPORT

    Stated as a NAMED [Prop] so a consuming lane can take it as a hypothesis
    and discharge it by [exact stored_rt_export], following ld-seams'
    [LdDistExport] device rather than inventing a second convention.

    AND THE BOUND IS EXPORTED IN THE COMPOSING SHAPE, which is filter-id's
    [DistBound] lesson applied here rather than relearned: they found that a
    bound exported as plain [dist <= data_size] does NOT compose above the
    window and that the [Z.min] form does, because [Z.min] is the shape the
    upstream fact concludes at.  A stored block's LEN is a SIXTEEN-BIT field,
    so the hard ceiling is 65535 whatever the data size; a consumer arriving
    with a data-size bound composes with [StoredLenBound] in one [lia], and a
    consumer arriving with only the field bound instantiates [d] at 65535. *)

Definition StoredLenBound (d stored_len : Z) : Prop :=
  0 <= stored_len <= Z.min d 65535.

Lemma storedlen_bound_field : forall d stored_len,
  StoredLenBound d stored_len -> 0 <= stored_len < 65536.
Proof. intros d l [H1 H2]. pose proof (Z.le_min_r d 65535). lia. Qed.

(** Satisfiable, and not only at zero: the premise is inhabited at a real
    payload length under a real data-size bound.  An added premise counts as
    landed only with an inhabitation witness, per the register. *)
Lemma storedlen_inhabited : StoredLenBound 8192 3 /\ StoredLenBound 65535 65535.
Proof. unfold StoredLenBound. split; cbn; lia. Qed.

(** AND THE QUANTIFIER ORDER IS THE STRONG ONE, which it was not when this
    file first landed.  ld-seams, consuming it, found that [forall tail] sat
    OUTSIDE [exists body], so the export handed out a body PER TAIL — while the
    emitted bits plainly do not depend on what follows them.  A consumer that
    wants THE delta (which is what a stream has) then had to prove the per-tail
    bodies coincide, two [app_inv_head]s off the shared left side, before it
    could use the export at all.

    So [exists body] now precedes [forall tail], and the tail-alignment premise
    moves inside with the decode it guards.  This is strictly stronger
    (instantiate at any single tail to recover the old shape, which
    [stored_rt_export_tailwise] does below) and it is the shape a streaming
    caller can use directly.  Nothing in the proof had to change: the facts
    were ALREADY in the strong order — [tr_stored_block_stream] mentions no
    tail at all, and [decode_stored_tail] is [forall tail] — so the weakness was
    in the export's statement and nowhere else.  An export can be weaker than
    every fact it is built from, and only a consumer finds that out. *)

Definition StoredRtExport : Prop :=
  forall dat stored_len last s d,
    bw_wf (ts_bw s) -> 0 <= last <= 1 ->
    stored_len = Z.of_nat (length dat) ->
    StoredLenBound d stored_len ->
    Forall (fun b => 0 <= b < 256) dat ->
    exists body,
      bw_stream (ts_bw (tr_stored_block dat stored_len last s))
        = bw_stream (ts_bw s) ++ zwrite 3 (Z.shiftl STORED_BLOCK 1 + last) ++ body
      /\ forall tail, (length tail mod 8 = 0)%nat ->
           decode_stored (body ++ tail) = Some (dat, tail).

Theorem stored_rt_export : StoredRtExport.
Proof.
  unfold StoredRtExport. intros dat stored_len last s d Hwf Hlast Hlen Hb Hbytes.
  pose proof (storedlen_bound_field d stored_len Hb) as Hrange.
  destruct (tr_stored_block_stream dat stored_len last s Hwf Hlast Hrange)
    as [pad [Hpad Hstream]].
  exists (stored_tail dat stored_len pad). split; [exact Hstream|].
  intros tail Ht.
  rewrite (decode_stored_tail dat stored_len pad tail Hlen Hrange Hpad Ht).
  rewrite (stored_map_u8_id dat Hbytes). reflexivity.
Qed.

(** The PREVIOUSLY PUBLISHED shape, retained rather than deleted so a consumer
    written against it keeps compiling — annotate, never remove a record.  It is
    now a one-line consequence, which is the measure of what the reshape bought:
    the [app_inv_head] pair a caller used to owe is discharged here once, for
    everyone. *)
Corollary stored_rt_export_tailwise : forall dat stored_len last s tail d,
    bw_wf (ts_bw s) -> 0 <= last <= 1 ->
    stored_len = Z.of_nat (length dat) ->
    StoredLenBound d stored_len ->
    (length tail mod 8 = 0)%nat ->
    Forall (fun b => 0 <= b < 256) dat ->
    exists body,
      bw_stream (ts_bw (tr_stored_block dat stored_len last s))
        = bw_stream (ts_bw s) ++ zwrite 3 (Z.shiftl STORED_BLOCK 1 + last) ++ body
      /\ decode_stored (body ++ tail) = Some (dat, tail).
Proof.
  intros dat stored_len last s tail d Hwf Hlast Hlen Hb Ht Hbytes.
  destruct (stored_rt_export dat stored_len last s d Hwf Hlast Hlen Hb Hbytes)
    as [body [Hs Hd]].
  exists body. split; [exact Hs | exact (Hd tail Ht)].
Qed.

(** ONE BODY FOR TWO DIFFERENT TAILS, as a value.  This is the whole content of
    the reshape and the old statement could not express it: the same [body]
    serves an empty tail and an eight-bit one.  Under the old quantifier order
    this was a theorem a consumer had to prove; here it falls out of the
    order. *)
Corollary stored_rt_body_tail_independent : forall dat stored_len last s d,
    bw_wf (ts_bw s) -> 0 <= last <= 1 ->
    stored_len = Z.of_nat (length dat) ->
    StoredLenBound d stored_len ->
    Forall (fun b => 0 <= b < 256) dat ->
    exists body,
      decode_stored (body ++ []) = Some (dat, [])
      /\ decode_stored (body ++ repeat false 8) = Some (dat, repeat false 8).
Proof.
  intros dat stored_len last s d Hwf Hlast Hlen Hb Hbytes.
  destruct (stored_rt_export dat stored_len last s d Hwf Hlast Hlen Hb Hbytes)
    as [body [_ Hd]].
  exists body. split.
  - apply Hd. reflexivity.
  - apply Hd. rewrite repeat_length. reflexivity.
Qed.
