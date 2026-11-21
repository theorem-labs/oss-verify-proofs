(** * HuffGenCodes — layer L-B(i)+(ii): zlib's [gen_codes] emits the canonical code.

    OWNER: huffman-id (claim §HUFFID on notes/c5-progress.md).

    WHAT THIS FILE IS FOR.  [Spec/PngModel/Huff.v] is the DECLARATIVE
    canonical-Huffman layer: [nc] is RFC 1951's [next_code] recurrence,
    [code_offset] is the count of earlier symbols of the same length, and
    [code_for] is the codeword, MSB first, as a [list bool].  On top of it
    [hdecode_code_for] is already Qed: a canonical codeword decodes back to
    its own symbol with the rest of the stream intact.

    [Spec/PngModel/Trees.v] is the OPERATIONAL transcription of zlib's
    [trees.c]: [gc_next] is the [next_code] loop over a [zarr], [gc_assign]
    is the assignment loop, and [gen_codes] is their composition.  Nothing
    in the tree consumes any of the three — measured, not assumed: an
    uncapped grep for [gen_codes] / [bi_reverse] / [send_tree] / [scan_tree]
    over every [.v] outside [Trees.v] returns ZERO hits.  So the operational
    side is transcribed and entirely unproven, and the gap between the two
    files is exactly this file's subject.

    THE ORIENTATION HAZARD, first, because getting it wrong would make every
    theorem below true about the wrong artifact.  zlib does NOT store the
    canonical code value.  [trees.c:225] stores [bi_reverse(next_code[len]++,
    len)] — the code with its bits REVERSED — because [send_bits] is
    LSB-first ([ZBitsOut.v:55]: [bi_buf |= value << bi_valid], bytes flushed
    low byte first).  Reversing at store time is what makes the bit the
    decoder reads FIRST be the codeword's MOST significant bit, which is
    what RFC 1951 requires.  So the two files disagree about the stored
    value by exactly a bit reversal, and agree about the emitted BIT
    SEQUENCE.  This file proves the second, and [bi_rev_write_bits] below is
    where the reversal is discharged rather than assumed.

    WHAT IS A HYPOTHESIS AND WHY.  [ValidLengths L 15] (Kraft) is taken as a
    hypothesis, per §RT-IDENTITY-PLAN: zlib's [build_tree]/[gen_bitlen]
    guarantee it by construction and re-deriving that is not this layer's
    job.  It is not decoration — it is what bounds [nc] below 2^15 and so
    discharges zlib's [u16] truncations ([t_setcode] and [gc_next] both
    truncate).  A witness discharging it is at the foot of this file, so the
    theorems are known to say something about at least one real code.

    THE BOUNDARY, stated so nobody reads this file as more than it is.  The
    theorems below end at [write_bits len (t_code ...)] — the LSB-first bit
    list of the stored code.  The step from there to the BYTES
    [bw_send_bits] actually appends to [bw_out] is layer L-C's
    (symbol-id's); no such bridge exists in the tree today (measured: no
    lemma mentions both [bw_send_bits] and [write_bits]).  [write_bits] is
    the interface point, not a claim that the byte-level writer has been
    verified.

    ONE SHARPENING against the statement posted at §HUFFID-STATEMENT, made
    after re-reading [send_code] ([Trees.v:741]:
    [bw_send_bits (t_code t c) (t_len t c) b]): zlib reads BOTH operands off
    the SAME tree, namely [gen_codes]' output.  The posted draft took the
    width from the INPUT tree.  The theorems below take both from the
    OUTPUT tree, which is what the C does; [gen_codes_len] is what makes
    the two agree, and it is proved rather than assumed. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Base Bits Huff Trees ZBitsBridge.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(** Small [Z] steps, isolated so the reversal proof reads as arithmetic. *)

Lemma land_1 : forall x, Z.land x 1 = x mod 2.
Proof.
  intro x. replace (Z.land x 1) with (Z.land x (Z.ones 1)) by reflexivity.
  rewrite Z.land_ones by lia. reflexivity.
Qed.

Lemma shiftr_1 : forall x, Z.shiftr x 1 = x / 2.
Proof. intro x. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.

Lemma shiftl_1 : forall x, Z.shiftl x 1 = 2 * x.
Proof. intro x. rewrite Z.shiftl_mul_pow2 by lia. ring. Qed.

Lemma even_mod2 : forall r, Z.even r = true -> r mod 2 = 0.
Proof.
  intros r H. rewrite Zmod_odd. rewrite <- Z.negb_even, H. reflexivity.
Qed.

(** ** [zrev]: reversal of the low [n] bits, as a value *)

Fixpoint zrev (n : nat) (c : Z) : Z :=
  match n with
  | O => 0
  | S k => zrev k (c / 2) + (c mod 2) * 2 ^ Z.of_nat k
  end.

Lemma zrev_bound : forall n c, 0 <= zrev n c < 2 ^ Z.of_nat n.
Proof.
  induction n as [|k IH]; intro c; cbn [zrev].
  - change (Z.of_nat 0) with 0. rewrite Z.pow_0_r. lia.
  - specialize (IH (c / 2)).
    assert (Hm : 0 <= c mod 2 < 2) by (apply Z.mod_pos_bound; lia).
    assert (Hp : 0 < 2 ^ Z.of_nat k) by (apply Z.pow_pos_nonneg; lia).
    rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. nia.
Qed.

(** THE LIST-LEVEL REVERSAL.  [zrev] is to [write_bits] what [rev] is to a
    list: writing the reversed value LSB-first is writing the original
    value MSB-first.  No bit-twiddling — [write_bits_split] peels the top
    bit and the induction is a one-liner. *)
Lemma write_bits_zrev : forall n c, write_bits n (zrev n c) = rev (write_bits n c).
Proof.
  induction n as [|k IH]; intro c; [reflexivity|].
  cbn [zrev].
  replace (S k) with (k + 1)%nat by lia.
  rewrite write_bits_split by apply zrev_bound.
  rewrite IH.
  replace (k + 1)%nat with (S k) by lia.
  cbn [write_bits rev].
  f_equal. f_equal.
  rewrite Zmod_odd. destruct (Z.odd c); reflexivity.
Qed.

(** ** [bi_reverse] IS [zrev]

    [bi_rev_go] is a [do..while] accumulator: it shifts [code] right one
    bit per trip and shifts the accumulator LEFT, so the accumulator ends
    up holding the reversal shifted up by one, which [bi_reverse] undoes
    with its [>> 1].

    The [u32] is zlib's [unsigned]; the bound hypothesis is what makes it
    the identity.  It is stated as [2^(n+1) * (r + 2) <= 2^32] rather than
    as a bound on the RESULT because that form is what the induction can
    carry: one trip doubles the accumulator and adds at most 1, so
    [r' + 2 <= 2 * (r + 2)] and the invariant reproduces itself. *)
Lemma bi_rev_go_val : forall n c r,
  0 <= c -> 0 <= r -> Z.even r = true ->
  2 ^ Z.of_nat (S n) * (r + 2) <= 4294967296 ->
  bi_rev_go n c r = 2 ^ Z.of_nat n * r + 2 * zrev n c.
Proof.
  induction n as [|k IH]; intros c r Hc Hr Hev Hb.
  - cbn [bi_rev_go zrev]. change (Z.of_nat 0) with 0. rewrite Z.pow_0_r. ring.
  - cbn [bi_rev_go zrev].
    rewrite land_1, shiftl_1, shiftr_1.
    assert (Hm : 0 <= c mod 2 < 2) by (apply Z.mod_pos_bound; lia).
    assert (Hlor : Z.lor r (c mod 2) = r + c mod 2).
    { pose proof (Z.add_lor_land r (c mod 2)) as HA.
      assert (Hland : Z.land r (c mod 2) = 0).
      { destruct (Z.eq_dec (c mod 2) 0) as [E|E].
        - rewrite E. apply Z.land_0_r.
        - assert (E1 : c mod 2 = 1) by lia. rewrite E1, land_1.
          apply even_mod2. exact Hev. }
      rewrite Hland in HA. lia. }
    rewrite Hlor.
    assert (Hpk : 0 < 2 ^ Z.of_nat k) by (apply Z.pow_pos_nonneg; lia).
    assert (Hsk : 2 ^ Z.of_nat (S k) = 2 * 2 ^ Z.of_nat k)
      by (rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia; ring).
    assert (Hssk : 2 ^ Z.of_nat (S (S k)) = 4 * 2 ^ Z.of_nat k).
    { rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. rewrite Hsk. ring. }
    rewrite Hssk in Hb.
    assert (Hu : u32 (2 * (r + c mod 2)) = 2 * (r + c mod 2)).
    { unfold u32. apply Z.mod_small. nia. }
    rewrite Hu.
    rewrite IH; [ | apply Z.div_pos; lia | lia
                 | rewrite Z.even_mul; reflexivity
                 | rewrite Hsk; nia ].
    rewrite Hsk. ring.
Qed.

(** The identification.  [Z.max 1 len] is zlib's [do..while]: [bi_reverse]
    runs at least one trip even at [len <= 0].  At [1 <= len] the max is
    [len] and the two agree on the nose. *)
Lemma bi_reverse_zrev : forall c len,
  1 <= len <= 30 -> 0 <= c ->
  bi_reverse c len = zrev (Z.to_nat len) c.
Proof.
  intros c len Hlen Hc. unfold bi_reverse.
  rewrite Z.max_r by lia.
  assert (Hev0 : Z.even 0 = true) by reflexivity.
  assert (H31 : 2 ^ 31 = 2147483648) by reflexivity.
  assert (Hbnd : 2 ^ Z.of_nat (S (Z.to_nat len)) * (0 + 2) <= 4294967296).
  { rewrite Nat2Z.inj_succ, Z2Nat.id by lia.
    assert (Hle : 2 ^ Z.succ len <= 2 ^ 31) by (apply Z.pow_le_mono_r; lia).
    rewrite H31 in Hle. lia. }
  rewrite (bi_rev_go_val (Z.to_nat len) c 0 Hc (Z.le_refl 0) Hev0 Hbnd).
  rewrite Z.mul_0_r, Z.add_0_l, shiftr_1, Z.mul_comm, Z.div_mul by lia.
  reflexivity.
Qed.

(** ** THE ORIENTATION THEOREM

    The bits zlib emits for a stored reversed code are the canonical
    codeword, MSB first.  Both sides are [list bool] of length [w], so an
    inversion cannot hide behind a value equality. *)
Theorem bi_rev_write_bits : forall w v,
  (1 <= w <= 30)%nat -> 0 <= v ->
  write_bits w (bi_reverse v (Z.of_nat w)) = code_bits v w.
Proof.
  intros w v Hw Hv.
  rewrite bi_reverse_zrev by lia.
  rewrite Nat2Z.id.
  rewrite write_bits_zrev.
  symmetry. apply code_bits_rev_write_bits.
Qed.

Definition BlcOf (blc : zarr) (L : list nat) : Prop :=
  forall b, 0 <= b <= MAX_BITS -> blc b = Z.of_nat (bl_count L (Z.to_nat b)).

(** [nc L b] fits in a [ush] for every length in range — the fact that makes
    zlib's two truncations the identity.  Kraft is doing the work here:
    without [ValidLengths], [nc] is unbounded and the [u16] in [gc_next]
    would be lossy.

    Stated and proved in [Z], deliberately.  The [nat] route needs [2^15]
    as a [nat] literal, whose unary expansion made one [cbn] cost nine
    seconds; [Z] is binary and the same step is free. *)
Lemma nc_le_Z : forall L b,
  ValidLengths L 15%nat -> (b <= 15)%nat ->
  Z.of_nat (nc L b) + Z.of_nat (bl_count L b) <= 32768.
Proof.
  intros L b HV Hb.
  pose proof (nc_count_bound L 15%nat b HV Hb) as H.
  apply inj_le in H. rewrite Nat2Z.inj_add, <- two_pow_nat in H.
  assert (Hle : 2 ^ Z.of_nat b <= 2 ^ 15) by (apply Z.pow_le_mono_r; lia).
  assert (H32 : (2:Z) ^ 15 = 32768) by reflexivity.
  lia.
Qed.

(** [gc_next] writes only at indices [bits .. bits + fuel - 1]. *)
Lemma gc_next_untouched : forall f bits code blc acc b,
  b < bits -> gc_next f bits code blc acc b = acc b.
Proof.
  induction f as [|f IH]; intros bits code blc acc b Hb; cbn [gc_next].
  - reflexivity.
  - rewrite IH by lia. apply zset_other. lia.
Qed.

(** The [next_code] loop, with the loop-carried [code] pinned to
    [nc L (bits-1)] — RFC 1951's own invariant: on entry to iteration
    [bits], [code] is [next_code[bits-1]]. *)
Lemma gc_next_spec : forall L blc f bits acc b,
  BlcOf blc L -> ValidLengths L 15%nat ->
  1 <= bits -> bits + Z.of_nat f <= MAX_BITS + 1 ->
  bits <= b < bits + Z.of_nat f ->
  gc_next f bits (Z.of_nat (nc L (Z.to_nat (bits - 1)))) blc acc b
  = Z.of_nat (nc L (Z.to_nat b)).
Proof.
  intros L blc f. unfold MAX_BITS.
  induction f as [|f IH]; intros bits acc b Hblc HV H1 Hf Hb; cbn [gc_next].
  - cbn in Hb. lia.
  - assert (Htn : Z.to_nat bits = S (Z.to_nat (bits - 1))) by lia.
    assert (Hb15 : (Z.to_nat (bits - 1) <= 15)%nat) by lia.
    assert (Hblcv : blc (bits - 1) = Z.of_nat (bl_count L (Z.to_nat (bits - 1))))
      by (apply Hblc; unfold MAX_BITS; lia).
    pose proof (nc_le_Z L (Z.to_nat (bits - 1)) HV Hb15) as Hbd.
    assert (Hcode : u32 (Z.shiftl (Z.of_nat (nc L (Z.to_nat (bits - 1))) + blc (bits - 1)) 1)
                    = Z.of_nat (nc L (Z.to_nat bits))).
    { rewrite Hblcv, shiftl_1.
      unfold u32. rewrite Z.mod_small by lia.
      rewrite Htn, nc_succ, Nat2Z.inj_mul, Nat2Z.inj_add. lia. }
    rewrite Hcode.
    destruct (Z.eq_dec b bits) as [->|Hne].
    + rewrite gc_next_untouched by lia. rewrite zset_same.
      assert (Hb15' : (Z.to_nat bits <= 15)%nat) by lia.
      pose proof (nc_le_Z L (Z.to_nat bits) HV Hb15') as Hbd'.
      assert (Hnn : 0 <= Z.of_nat (bl_count L (Z.to_nat bits))) by lia.
      unfold u16. rewrite Z.mod_small by lia. reflexivity.
    + replace (Z.of_nat (nc L (Z.to_nat bits)))
        with (Z.of_nat (nc L (Z.to_nat (bits + 1 - 1))))
        by (f_equal; f_equal; f_equal; lia).
      apply IH; try assumption; try lia.
Qed.

Definition nc_arr (blc : zarr) : zarr := gc_next (Z.to_nat MAX_BITS) 1 0 blc zzero.

Theorem gc_next_nc : forall L blc b,
  BlcOf blc L -> ValidLengths L 15%nat ->
  1 <= b <= MAX_BITS ->
  nc_arr blc b = Z.of_nat (nc L (Z.to_nat b)).
Proof.
  intros L blc b Hblc HV Hb. unfold nc_arr, MAX_BITS in *.
  replace 0 with (Z.of_nat (nc L (Z.to_nat (1 - 1)))) by reflexivity.
  apply gc_next_spec; try assumption; unfold MAX_BITS; try lia.
Qed.

(** ** The offset recurrence

    [code_offset L m l] counts the symbols BEFORE [m] of length [l].  Going
    from [m] to [m+1] adds one exactly when symbol [m] itself has length
    [l].  That is the declarative content of zlib's [next_code[len]++], and
    the three shapes below are the three branches [gc_assign] takes. *)

Lemma hid_firstn_S_nth : forall (L : list nat) m,
  firstn (S m) L
  = firstn m L ++ (match nth_error L m with Some x => [x] | None => [] end).
Proof.
  induction L as [|a L IH]; intros m.
  - destruct m; reflexivity.
  - destruct m as [|m].
    + reflexivity.
    + (* [cbn] would unfold [firstn (S m) L] into a match on [L] and the
         induction hypothesis would no longer apply; [change] keeps the
         subterm the IH is stated about. *)
      change (firstn (S (S m)) (a :: L)) with (a :: firstn (S m) L).
      change (firstn (S m) (a :: L)) with (a :: firstn m L).
      change (nth_error (a :: L) (S m)) with (nth_error L m).
      rewrite (IH m). reflexivity.
Qed.

Lemma code_offset_step_eq : forall L m l,
  nth_error L m = Some l -> code_offset L (S m) l = S (code_offset L m l).
Proof.
  intros L m l H. unfold code_offset. rewrite hid_firstn_S_nth, count_len_app, H.
  unfold count_len. cbn [count_occ].
  destruct (Nat.eq_dec l l) as [_|Hne]; [lia|exfalso; apply Hne; reflexivity].
Qed.

Lemma code_offset_step_ne : forall L m l x,
  nth_error L m = Some x -> x <> l -> code_offset L (S m) l = code_offset L m l.
Proof.
  intros L m l x H Hne. unfold code_offset.
  rewrite hid_firstn_S_nth, count_len_app, H.
  unfold count_len. cbn [count_occ].
  destruct (Nat.eq_dec x l) as [->|_]; [exfalso; apply Hne; reflexivity|lia].
Qed.

Lemma code_offset_step_none : forall L m l,
  nth_error L m = None -> code_offset L (S m) l = code_offset L m l.
Proof.
  intros L m l H. unfold code_offset.
  rewrite hid_firstn_S_nth, count_len_app, H.
  unfold count_len. cbn [count_occ]. lia.
Qed.

(** ** The two representation predicates *)

Definition LensOf (t : Tree) (L : list nat) : Prop :=
  forall k, (k < length L)%nat -> t_len t (Z.of_nat k) = Z.of_nat (nth k L 0%nat).

(** The assignment loop's invariant: on arrival at symbol [m], the slot for
    each length holds [nc L l] plus the number of EARLIER symbols of that
    length.  [gc_next] establishes it at [m = 0] and every trip preserves
    it — the whole content of [next_code[len]++]. *)
Definition NcAt (A : zarr) (L : list nat) (m : nat) : Prop :=
  forall l, (1 <= l <= 15)%nat ->
    A (Z.of_nat l) = Z.of_nat (nc L l + code_offset L m l).

Lemma t_setcode_len : forall t n v k, t_len (t_setcode t n v) k = t_len t k.
Proof. reflexivity. Qed.

Lemma LensOf_setcode : forall t L n v, LensOf t L -> LensOf (t_setcode t n v) L.
Proof. intros t L n v H k Hk. rewrite t_setcode_len. apply H, Hk. Qed.

(** Reading a length off the tree.  Stated as a lemma rather than an
    in-proof helper because [destruct (nth_error L m) eqn:] rewrites inside
    hypotheses, and a helper quantified over the value gets captured. *)
Lemma LensOf_at : forall t L k x,
  LensOf t L -> nth_error L k = Some x -> t_len t (Z.of_nat k) = Z.of_nat x.
Proof.
  intros t L k x H Hx. rewrite H.
  - f_equal. apply (nth_error_nth L k 0%nat Hx).
  - apply nth_error_Some. rewrite Hx. discriminate.
Qed.

(** [gc_assign] writes only at indices [>= n]. *)
Lemma gc_assign_untouched : forall f n maxc t A b,
  b < n -> t_code (gc_assign f n maxc t A) b = t_code t b.
Proof.
  induction f as [|f IH]; intros n maxc t A b Hb; cbn [gc_assign]; [reflexivity|].
  destruct (Z.ltb maxc n); [reflexivity|].
  destruct (Z.eqb (t_len t n) 0).
  - apply IH. lia.
  - rewrite IH by lia. unfold t_code, t_setcode. cbn [tr_fc].
    apply zset_other. lia.
Qed.

(** A stored reversed code fits in a [ush]: it is the reversal of a value
    below [2^len], hence itself below [2^len <= 2^15]. *)
Lemma bi_reverse_lt : forall v len,
  1 <= len <= 15 -> 0 <= v -> 0 <= bi_reverse v len < 65536.
Proof.
  intros v len Hl Hv. rewrite bi_reverse_zrev by lia.
  pose proof (zrev_bound (Z.to_nat len) v) as H.
  assert (Hle : 2 ^ Z.of_nat (Z.to_nat len) <= 2 ^ 15)
    by (apply Z.pow_le_mono_r; lia).
  assert (H32 : (2:Z) ^ 15 = 32768) by reflexivity. lia.
Qed.

(** ** THE ASSIGNMENT LOOP *)

Theorem gc_assign_spec : forall L f (m : nat) maxc t A (sym : nat) len,
  LensOf t L -> ValidLengths L 15%nat -> NcAt A L m ->
  (m <= sym)%nat -> Z.of_nat sym <= maxc -> (sym < m + f)%nat ->
  nth_error L sym = Some len -> (1 <= len)%nat ->
  t_code (gc_assign f (Z.of_nat m) maxc t A) (Z.of_nat sym)
  = bi_reverse (Z.of_nat (nc L len + code_offset L sym len)) (Z.of_nat len).
Proof.
  intros L f. induction f as [|f IH];
    intros m maxc t A sym len Hlens HV HA Hms Hsm Hsf He Hl.
  - lia.
  - (* [sym] is in range, so [L] is long enough to reach it *)
    assert (HsymL : (sym < length L)%nat)
      by (apply nth_error_Some; rewrite He; discriminate).
    assert (Hlen15 : (len <= 15)%nat).
    { destruct HV as [Hmax _]. apply Hmax. eapply nth_error_In; exact He. }
    cbn [gc_assign].
    assert (Hltb : Z.ltb maxc (Z.of_nat m) = false) by (apply Z.ltb_ge; lia).
    rewrite Hltb.
    destruct (Nat.eq_dec m sym) as [Heqms|Hne].
    + (* THIS symbol: store, and no later trip touches index [m] *)
      subst sym.
      rewrite (LensOf_at t L m len Hlens He).
      assert (Hz : Z.eqb (Z.of_nat len) 0 = false) by (apply Z.eqb_neq; lia).
      rewrite Hz.
      rewrite gc_assign_untouched by lia.
      unfold t_code, t_setcode. cbn [tr_fc]. rewrite zset_same.
      assert (Hlr : (1 <= len <= 15)%nat) by lia.
      rewrite (HA len Hlr).
      unfold u16. apply Z.mod_small. apply bi_reverse_lt; lia.
    + (* an EARLIER symbol: step the invariant and recurse *)
      assert (Hms' : (S m <= sym)%nat) by lia.
      assert (HmltL : (m < length L)%nat) by lia.
      replace (Z.of_nat m + 1) with (Z.of_nat (S m)) by lia.
      destruct (nth_error L m) as [x|] eqn:Ex.
      * rewrite (LensOf_at t L m x Hlens Ex).
        destruct (Nat.eq_dec x 0%nat) as [Hx0|Hx0].
        -- (* absent symbol: nothing stored, invariant unchanged *)
           subst x.
           assert (Hz0 : Z.eqb (Z.of_nat 0%nat) 0 = true) by (apply Z.eqb_eq; lia).
           rewrite Hz0.
           apply IH; try assumption; try lia.
           intros l Hlr. rewrite (HA l Hlr).
           rewrite (code_offset_step_ne L m l 0%nat Ex) by lia. reflexivity.
        -- (* present symbol: exactly its own slot advances by one *)
           assert (Hz : Z.eqb (Z.of_nat x) 0 = false) by (apply Z.eqb_neq; lia).
           rewrite Hz.
           assert (Hx15 : (x <= 15)%nat).
           { destruct HV as [Hmax _]. apply Hmax. eapply nth_error_In; exact Ex. }
           (* [LensOf (t_setcode t n v) L] is CONVERTIBLE to [LensOf t L]
              ([t_setcode] writes [fc.code], and [t_len] reads [dl.len]), so
              [assumption] discharges it and only the array invariant is
              left.  [LensOf_setcode] above records the same fact for
              readers; it is not needed as a step. *)
           apply IH; try assumption; try lia.
           intros l Hlr.
           destruct (Nat.eq_dec x l) as [Hxl|Hxl].
           ++ subst x.
              rewrite zset_same, (HA l Hlr).
              rewrite (code_offset_step_eq L m l Ex).
              pose proof (nc_le_Z L l HV (proj2 Hlr)) as Hbd.
              pose proof (code_offset_lt L m l Ex) as Hoff.
              rewrite (bl_count_pos L l) in Hbd by lia.
              unfold u16. rewrite Z.mod_small; [lia|lia].
           ++ rewrite zset_other by lia.
              rewrite (HA l Hlr).
              rewrite (code_offset_step_ne L m l x Ex) by lia. reflexivity.
      * (* impossible: [m <= sym < length L] *)
        exfalso. apply nth_error_None in Ex. lia.
Qed.

(** Symbols past [max_code] are ABSENT — zlib's own invariant ([build_tree]
    sets [max_code] to the largest symbol with nonzero frequency and
    [gen_bitlen] leaves the rest at length 0).  Stated in [Z] so that
    [maxc = -1] (no codes at all) says what it should. *)
Definition AbsentBeyond (L : list nat) (maxc : Z) : Prop :=
  forall k, maxc < Z.of_nat k -> nth k L 0%nat = 0%nat.

(** [gen_codes] never touches the [Len] array: [t_setcode] writes [fc.code]
    and [t_len] reads [dl.len]. *)
Lemma gc_assign_len : forall f n maxc t A k,
  t_len (gc_assign f n maxc t A) k = t_len t k.
Proof.
  induction f as [|f IH]; intros n maxc t A k; cbn [gc_assign]; [reflexivity|].
  destruct (Z.ltb maxc n); [reflexivity|].
  destruct (Z.eqb (t_len t n) 0).
  - apply IH.
  - (* [rewrite], not [apply]: unification would fix the tree from the
       right-hand side and then fail on the left. *)
    rewrite IH. reflexivity.
Qed.

Lemma gen_codes_len : forall t maxc blc n,
  t_len (gen_codes t maxc blc) n = t_len t n.
Proof. intros. unfold gen_codes. apply gc_assign_len. Qed.

(** ** [gen_codes] stores the reversed canonical value

    THE [maxc <= 288] BOUND, and why it is not 285.  [gen_codes]' fuel is
    [Z.to_nat L_CODES + 3 = 289], so the loop covers symbols [0 .. 288]; the
    hypothesis is exactly what the fuel affords and nothing tighter.  My
    first draft said [285] on the reasoning that the dynamic literal/length
    tree has [L_CODES = 286] symbols.  That excluded [static_ltree], which
    has 288 entries with [max_code = 287] — so the bound would have made the
    theorem inapplicable to the FIXED Huffman tables baked into the binary,
    which are the very instance that makes this layer live under a
    fixed-block answer to Q2.  The witness corrected the hypothesis. *)

Theorem gen_codes_stored_value : forall L t maxc blc sym len,
  LensOf t L -> BlcOf blc L -> ValidLengths L 15%nat ->
  AbsentBeyond L maxc -> -1 <= maxc <= 288 ->
  nth_error L sym = Some len -> (1 <= len)%nat ->
  t_code (gen_codes t maxc blc) (Z.of_nat sym)
  = bi_reverse (Z.of_nat (nc L len + code_offset L sym len)) (Z.of_nat len).
Proof.
  intros L t maxc blc sym len Hlens Hblc HV Hab Hmc He Hl.
  (* [sym <= maxc] is DERIVED, not assumed: a symbol with a codeword cannot
     be past [max_code], because everything past it has length 0. *)
  assert (Hsm : Z.of_nat sym <= maxc).
  { destruct (Z_le_gt_dec (Z.of_nat sym) maxc) as [H|H]; [exact H|exfalso].
    assert (Hn : nth sym L 0%nat = len) by (apply (nth_error_nth L sym 0%nat He)).
    rewrite (Hab sym) in Hn by lia. lia. }
  assert (Hfuel : (Z.to_nat L_CODES + 3 = 289)%nat) by reflexivity.
  unfold gen_codes.
  apply (gc_assign_spec L (Z.to_nat L_CODES + 3)%nat 0%nat maxc t
           (gc_next (Z.to_nat MAX_BITS) 1 0 blc zzero) sym len);
    try assumption; try lia.
  (* the array [gc_next] hands over satisfies the loop invariant at symbol 0 *)
  intros l Hlr.
  assert (Hb : 1 <= Z.of_nat l <= MAX_BITS) by (unfold MAX_BITS; lia).
  pose proof (gc_next_nc L blc (Z.of_nat l) Hblc HV Hb) as Hg.
  unfold nc_arr in Hg. rewrite Nat2Z.id in Hg. rewrite Hg. f_equal.
  unfold code_offset. cbn [firstn]. unfold count_len. cbn [count_occ]. lia.
Qed.

(** ** (a) THE EMITTED BITS ARE THE CANONICAL CODEWORD

    Both operands are read off the OUTPUT tree, which is exactly what
    [send_code] does ([Trees.v:741]: [bw_send_bits (t_code t c) (t_len t c) b]),
    so the pair below is the pair zlib hands its bit writer. *)
Theorem gen_codes_emits_code_for : forall L t maxc blc sym cw,
  LensOf t L -> BlcOf blc L -> ValidLengths L 15%nat ->
  AbsentBeyond L maxc -> -1 <= maxc <= 288 ->
  code_for L 15%nat sym = Some cw ->
  write_bits (Z.to_nat (t_len (gen_codes t maxc blc) (Z.of_nat sym)))
             (t_code (gen_codes t maxc blc) (Z.of_nat sym))
  = cw.
Proof.
  intros L t maxc blc sym cw Hlens Hblc HV Hab Hmc Hcf.
  apply code_for_inv in Hcf as [len [He [Hl1 [Hl15 Hcw]]]].
  rewrite gen_codes_len, (LensOf_at t L sym len Hlens He), Nat2Z.id.
  rewrite (gen_codes_stored_value L t maxc blc sym len Hlens Hblc HV Hab Hmc He Hl1).
  rewrite Hcw. apply bi_rev_write_bits; lia.
Qed.

(** ** (b) DECODE OF ENCODE IS THE IDENTITY

    [rest] is universally quantified: a statement about a codeword alone
    would be satisfied by a decoder that consumed its whole input.  What a
    round trip needs is that the decoder STOPS at the codeword's last bit,
    and that is what leaving [rest] untouched says. *)
Theorem gen_codes_decode_of_encode : forall L t maxc blc sym cw rest,
  LensOf t L -> BlcOf blc L -> ValidLengths L 15%nat ->
  AbsentBeyond L maxc -> -1 <= maxc <= 288 ->
  code_for L 15%nat sym = Some cw ->
  hdecode (code_table L 15%nat)
          (write_bits (Z.to_nat (t_len (gen_codes t maxc blc) (Z.of_nat sym)))
                      (t_code (gen_codes t maxc blc) (Z.of_nat sym)) ++ rest)
  = Some (sym, rest).
Proof.
  intros L t maxc blc sym cw rest Hlens Hblc HV Hab Hmc Hcf.
  rewrite (gen_codes_emits_code_for L t maxc blc sym cw Hlens Hblc HV Hab Hmc Hcf).
  apply (hdecode_code_for L 15%nat sym cw rest HV Hcf).
Qed.

(** [BlcOf] is indexed by [Z] because [gc_next] indexes by [Z]; a witness is
    far easier to give over [nat].  This is the adapter. *)
Lemma BlcOf_of_nat : forall blc L,
  (forall b, (b <= 15)%nat -> blc (Z.of_nat b) = Z.of_nat (bl_count L b)) ->
  BlcOf blc L.
Proof.
  intros blc L H b Hb. unfold MAX_BITS in Hb.
  specialize (H (Z.to_nat b)). rewrite Z2Nat.id in H by lia.
  apply H. lia.
Qed.

(** ** The witness: RFC 1951 §3.2.2 *)

Definition Lrfc : list nat := [3;3;3;3;3;2;4;4]%nat.
Definition trfc : Tree := mkTree zzero (zlist [3;3;3;3;3;2;4;4]).
Definition blcrfc : zarr := zlist [0;0;1;5;2].

Lemma rfc_LensOf : LensOf trfc Lrfc.
Proof.
  intros k Hk. cbn [length Lrfc] in Hk.
  destruct k as [|[|[|[|[|[|[|[|k]]]]]]]]; try reflexivity. lia.
Qed.

Lemma rfc_BlcOf : BlcOf blcrfc Lrfc.
Proof.
  apply BlcOf_of_nat. intros b Hb.
  destruct b as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|b]]]]]]]]]]]]]]]];
    try reflexivity. lia.
Qed.

Lemma rfc_ValidLengths : ValidLengths Lrfc 15%nat.
Proof. apply valid_lengths_b_true. vm_compute. reflexivity. Qed.

Lemma rfc_AbsentBeyond : AbsentBeyond Lrfc 7.
Proof. intros k Hk. apply nth_overflow. cbn [length Lrfc]. lia. Qed.

Lemma rfc_maxc : -1 <= 7 <= 288.
Proof. lia. Qed.

(** ** The applied conclusion

    Not "the hypotheses are satisfiable" but "here is the theorem's
    conclusion, closed, for a symbol of this code".  Symbol 6 is chosen
    deliberately: its canonical value is 14 and zlib stores 7, so this
    instance exercises the bit reversal rather than a palindrome. *)
Example rfc_code_for_6 : code_for Lrfc 15%nat 6%nat = Some [true;true;true;false].
Proof. vm_compute. reflexivity. Qed.

Example rfc_stored_6 : t_code (gen_codes trfc 7 blcrfc) 6 = 7.
Proof. vm_compute. reflexivity. Qed.

Example rfc_canonical_value_6 :
  Z.of_nat (nc Lrfc 4%nat + code_offset Lrfc 6%nat 4%nat) = 14.
Proof. vm_compute. reflexivity. Qed.

Theorem rfc_roundtrip_6 : forall rest,
  hdecode (code_table Lrfc 15%nat)
          (write_bits (Z.to_nat (t_len (gen_codes trfc 7 blcrfc) (Z.of_nat 6%nat)))
                      (t_code (gen_codes trfc 7 blcrfc) (Z.of_nat 6%nat)) ++ rest)
  = Some (6%nat, rest).
Proof.
  intro rest.
  apply (gen_codes_decode_of_encode Lrfc trfc 7 blcrfc 6%nat
           [true;true;true;false] rest
           rfc_LensOf rfc_BlcOf rfc_ValidLengths rfc_AbsentBeyond rfc_maxc
           rfc_code_for_6).
Qed.

(** And the same for a symbol whose stored value is NOT its canonical value
    in the other direction (symbol 1: canonical 3 = 011, stored 6 = 110). *)
Example rfc_code_for_1 : code_for Lrfc 15%nat 1%nat = Some [false;true;true].
Proof. vm_compute. reflexivity. Qed.

Theorem rfc_roundtrip_1 : forall rest,
  hdecode (code_table Lrfc 15%nat)
          (write_bits (Z.to_nat (t_len (gen_codes trfc 7 blcrfc) (Z.of_nat 1%nat)))
                      (t_code (gen_codes trfc 7 blcrfc) (Z.of_nat 1%nat)) ++ rest)
  = Some (1%nat, rest).
Proof.
  intro rest.
  apply (gen_codes_decode_of_encode Lrfc trfc 7 blcrfc 1%nat
           [false;true;true] rest
           rfc_LensOf rfc_BlcOf rfc_ValidLengths rfc_AbsentBeyond rfc_maxc
           rfc_code_for_1).
Qed.

(** ** The whole-code check, by computation

    Theorem (a) says the emitted bits equal [code_for]'s answer.  Here it is
    for all eight symbols at once, computed rather than proved — the check
    that would have caught an inverted orientation before any induction was
    written. *)
Definition rfc_emitted : list (option (list bool)) :=
  map (fun s => Some (write_bits (Z.to_nat (t_len (gen_codes trfc 7 blcrfc) (Z.of_nat s)))
                                 (t_code (gen_codes trfc 7 blcrfc) (Z.of_nat s))))
      (seq 0 8).

Definition rfc_declared : list (option (list bool)) :=
  map (fun s => code_for Lrfc 15%nat s) (seq 0 8).

Example rfc_all_eight : rfc_emitted = rfc_declared.
Proof. vm_compute. reflexivity. Qed.

(** THE REVERSAL IS EXERCISED, not merely mentioned: the stored values and
    the canonical values differ at five of the eight symbols, while the
    emitted bit sequences agree everywhere. *)
Definition rfc_stored_values : list Z :=
  map (fun s => t_code (gen_codes trfc 7 blcrfc) (Z.of_nat s)) (seq 0 8).

Definition rfc_canonical_values : list Z :=
  map (fun s => Z.of_nat (nc Lrfc (nth s Lrfc 0%nat)
                          + code_offset Lrfc s (nth s Lrfc 0%nat))) (seq 0 8).

Example rfc_stored_is : rfc_stored_values = [2;6;1;5;3;0;7;15].
Proof. vm_compute. reflexivity. Qed.

Example rfc_canonical_is : rfc_canonical_values = [2;3;4;5;6;0;14;15].
Proof. vm_compute. reflexivity. Qed.

Example rfc_stored_differs_from_canonical :
  rfc_stored_values <> rfc_canonical_values.
Proof. vm_compute. discriminate. Qed.

(** ** A second, degenerate witness

    The theorems must also hold where the code is INCOMPLETE (Kraft strict)
    and where a symbol is absent.  [hid_Lz = [0;2;0;2]] has two absent symbols
    and two TWO-bit codes, and the absent symbol at index 2 sits BETWEEN the two
    present ones, so [gc_assign]'s skip branch is on the path.  The two-bit
    widths are what make it Kraft-STRICT ([kraft_sum = 16384 < 2^15]); one-bit
    codes would make it complete and lose the property this witness exists for.

    (Corrected 2026-08-18: this header said "two ONE-bit codes", which is wrong
    about its own values — the lengths are 2.  Found while adjudicating a name
    clash, and it mattered: the width is exactly what carries the strictness.) *)
Definition hid_Lz : list nat := [0;2;0;2]%nat.
Definition tz : Tree := mkTree zzero (zlist [0;2;0;2]).
Definition blcz : zarr := zlist [0;0;2].

Lemma z_LensOf : LensOf tz hid_Lz.
Proof.
  intros k Hk. cbn [length hid_Lz] in Hk.
  destruct k as [|[|[|[|k]]]]; try reflexivity. lia.
Qed.

Lemma z_BlcOf : BlcOf blcz hid_Lz.
Proof.
  apply BlcOf_of_nat. intros b Hb.
  destruct b as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|b]]]]]]]]]]]]]]]];
    try reflexivity. lia.
Qed.

Lemma z_ValidLengths : ValidLengths hid_Lz 15%nat.
Proof. apply valid_lengths_b_true. vm_compute. reflexivity. Qed.

Lemma z_AbsentBeyond : AbsentBeyond hid_Lz 3.
Proof. intros k Hk. apply nth_overflow. cbn [length hid_Lz]. lia. Qed.

Example z_code_for_3 : code_for hid_Lz 15%nat 3%nat = Some [false;true].
Proof. vm_compute. reflexivity. Qed.

(** The incomplete code round-trips too, and symbol 3 sits AFTER two absent
    symbols, so the skip branch of [gc_assign] is on the path. *)
Theorem z_roundtrip_3 : forall rest,
  hdecode (code_table hid_Lz 15%nat)
          (write_bits (Z.to_nat (t_len (gen_codes tz 3 blcz) (Z.of_nat 3%nat)))
                      (t_code (gen_codes tz 3 blcz) (Z.of_nat 3%nat)) ++ rest)
  = Some (3%nat, rest).
Proof.
  intro rest.
  apply (gen_codes_decode_of_encode hid_Lz tz 3 blcz 3%nat [false;true] rest
           z_LensOf z_BlcOf z_ValidLengths z_AbsentBeyond).
  - lia.
  - exact z_code_for_3.
Qed.

(** Absent symbols get NO codeword — the branch is real, not decorative. *)
Example z_absent_0 : code_for hid_Lz 15%nat 0%nat = None.
Proof. vm_compute. reflexivity. Qed.

Example z_absent_2 : code_for hid_Lz 15%nat 2%nat = None.
Proof. vm_compute. reflexivity. Qed.

(** ** Axiom profile *)

Print Assumptions gen_codes_emits_code_for.
Print Assumptions gen_codes_decode_of_encode.
Print Assumptions rfc_roundtrip_6.
Print Assumptions z_roundtrip_3.
Print Assumptions bi_rev_write_bits.
Print Assumptions gc_next_nc.
Print Assumptions gc_assign_spec.

