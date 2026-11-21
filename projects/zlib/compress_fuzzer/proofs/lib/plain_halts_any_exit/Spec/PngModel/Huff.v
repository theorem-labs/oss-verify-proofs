(** * Spec.PngModel.Huff — the declarative canonical-Huffman / LZ77 layer.

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT.  Depends only on
    [Spec.PngModel.Base], [Spec.PngModel.Bits] and Stdlib.

    L0a-ii, the sibling of [Bits.v].  This is the SPECIFICATION side of the
    Huffman layer: what a canonical DEFLATE code IS, per RFC 1951 §3.2.2,
    and what it means to decode with one.  The OPERATIONAL side — the
    [inftrees.c] table builder, [inflate.c]'s state machine, the [ZBitsIn]
    bit reader — is a different lane's work in different files.  Nothing
    here mentions, imports, or depends on any of them; the refinement
    between the two is stated in a separate bridge module (compare
    [Spec.PngModel.ZBitsBridge], which does exactly that for the bit
    reader).  This file must never grow a dependency on
    [Inftrees]/[Inflate]/[InflateFast]/[ZBitsIn]/[Trees]/[Deflate].

    TWO BIT ORDERS COEXIST HERE, AND CONFLATING THEM IS THE CLASSIC
    DEFLATE BUG.

      - The bit STREAM ([Bits.byte_bits], [Bits.read_bits],
        [Bits.write_bits]) is LSB first: RFC 1951 §3.1.1's rule for data
        elements.
      - A Huffman CODEWORD ([code_bits] below) is MSB first: RFC 1951
        §3.1.1 says Huffman codes are packed starting from the most
        significant bit of the code.

    So a codeword is NOT [write_bits] of its value, and the two are pinned
    apart by computation at the bottom of this file
    ([code_bits_is_not_write_bits], [code_bits_msb_first],
    [write_bits_lsb_first]) rather than by this comment.  The exact
    relationship is a lemma: [code_bits_rev_write_bits].

    CONVENTIONS.  Bit widths, symbol indices, code-length histograms and
    Kraft sums are [nat]; the default scope of this file is [nat_scope]
    (unlike [Bits.v], which is [Z]-dominated and opens [Z_scope]).  Only
    codeword VALUES and payload BYTES are [Z].  Every definition is total,
    non-dependent and obligation-free: no [Program], no subtypes, no
    dependent [getElem] — out-of-range symbol lookups go through
    [nth_error] and return [None].

    [maxBits] IS ALWAYS AN EXPLICIT ARGUMENT and never has a default.
    DEFLATE uses 15 for the literal/length and distance trees but 7 for
    the code-length tree; a silent 15-for-7 would let an oversubscribed
    code-length tree validate.  [maxbits_matters_9] / [maxbits_matters_7]
    pin that the argument is load bearing.

    DISCIPLINE.  Every claim any comment in this file makes is stated as a
    lemma below it.  Where a fact is merely NOT proved here, the comment
    says so explicitly rather than asserting it in passing. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Bits.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

(** ** 1. Codewords: MSB first

    [code_bits v w] is the [w]-bit codeword whose value is [v]: bit [w-1]
    of [v] first, bit [0] of [v] last.  It is total — for [v] outside
    [[0, 2^w)] it still produces exactly [w] bits ([code_bits_length]),
    namely bits [w-1 .. 0] of [v]'s two's-complement expansion, i.e. it
    sees [v] only through [v mod 2^w] ([code_bits_mod]). *)

Fixpoint code_bits (v : Z) (w : nat) : list bool :=
  match w with
  | O => []
  | S k => Z.testbit v (Z.of_nat k) :: code_bits v k
  end.

Lemma code_bits_length : forall v w, length (code_bits v w) = w.
Proof.
  intros v w; induction w as [|k IH]; cbn [code_bits length]; [reflexivity|].
  now rewrite IH.
Qed.

(** The append form of the recursion: peel the LAST (least significant)
    bit rather than the first.  This is what makes [code_bits_firstn]
    a one-step induction. *)
Lemma code_bits_snoc : forall k v,
  code_bits v (S k) = code_bits (v / 2)%Z k ++ [Z.odd v].
Proof.
  induction k as [|k IH]; intro v.
  - reflexivity.
  - change (code_bits v (S (S k)))
      with (Z.testbit v (Z.of_nat (S k)) :: code_bits v (S k)).
    change (code_bits (v / 2)%Z (S k))
      with (Z.testbit (v / 2)%Z (Z.of_nat k) :: code_bits (v / 2)%Z k).
    rewrite (IH v). cbn [app]. f_equal.
    rewrite Nat2Z.inj_succ. symmetry. apply Z.div2_bits. lia.
Qed.

(** THE MSB/LSB DUALITY, stated.  A codeword is the REVERSE of the
    LSB-first [Bits.write_bits] of the same value at the same width.
    This is the only sanctioned way to move between the two orders. *)
Lemma code_bits_rev_write_bits : forall w v, code_bits v w = rev (write_bits w v).
Proof.
  intro w; induction w as [|k IH]; intro v; [reflexivity|].
  rewrite code_bits_snoc, (IH (v / 2)%Z).
  cbn [write_bits rev]. reflexivity.
Qed.

(** [code_bits] reads only the low [w] bits of [v].  Consequence worth
    spelling out: any error in a code's base value that shifts it by a
    MULTIPLE of [2^w] produces byte-identical codewords, so no codeword
    test can catch it — only [nc_bound] below can.  That is exactly the
    shape of the [bl_count[0]] mistake discussed in §3. *)
Lemma code_bits_mod : forall w v,
  code_bits (v mod 2 ^ Z.of_nat w)%Z w = code_bits v w.
Proof.
  intros w v. rewrite !code_bits_rev_write_bits, !write_bits_testbit.
  f_equal. apply map_ext_in. intros i Hi. apply in_seq in Hi.
  apply Z.mod_pow2_bits_low. lia.
Qed.

(** Codewords of the same width determine their value, in range. *)
Lemma code_bits_inj : forall w v1 v2,
  (0 <= v1 < 2 ^ Z.of_nat w)%Z -> (0 <= v2 < 2 ^ Z.of_nat w)%Z ->
  code_bits v1 w = code_bits v2 w -> v1 = v2.
Proof.
  intros w v1 v2 H1 H2 Heq.
  rewrite !code_bits_rev_write_bits in Heq.
  assert (Hw : write_bits w v1 = write_bits w v2).
  { rewrite <- (rev_involutive (write_bits w v1)), Heq, rev_involutive.
    reflexivity. }
  pose proof (read_bits_write_bits w v1 [] H1) as R1.
  pose proof (read_bits_write_bits w v2 [] H2) as R2.
  rewrite Hw in R1. rewrite R1 in R2. congruence.
Qed.

(** Truncating a codeword to its top [w1] bits is the codeword of the
    value shifted right — the fact the whole prefix-freeness argument
    turns on. *)
Lemma code_bits_firstn : forall w2 w1 v, w1 <= w2 ->
  firstn w1 (code_bits v w2) = code_bits (v / 2 ^ Z.of_nat (w2 - w1))%Z w1.
Proof.
  intro w2; induction w2 as [|k IH]; intros w1 v Hle.
  - assert (w1 = 0) by lia. subst w1. reflexivity.
  - destruct (Nat.eq_dec w1 (S k)) as [->|Hne].
    + replace (2 ^ Z.of_nat (S k - S k))%Z with 1%Z
        by (rewrite Nat.sub_diag; reflexivity).
      rewrite Z.div_1_r. apply firstn_all2. rewrite code_bits_length. lia.
    + assert (Hw1 : w1 <= k) by lia.
      rewrite code_bits_snoc, firstn_app, code_bits_length.
      replace (w1 - k) with 0 by lia.
      change (firstn 0 [Z.odd v]) with (@nil bool).
      rewrite app_nil_r, (IH w1 (v / 2)%Z Hw1).
      f_equal.
      rewrite Zdiv_Zdiv by (first [lia | apply Z.pow_nonneg; lia]).
      f_equal.
      replace (S k - w1) with (S (k - w1)) by lia.
      rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. reflexivity.
Qed.

(** ** 2. Prefixes

    [is_prefix p q] is a decision procedure, not a specification: the
    specification is [is_prefix_true_iff].  [hdecode] below does not
    require prefix-freeness in order to be DEFINED — only in order to be
    CORRECT. *)

Fixpoint is_prefix (p q : list bool) : bool :=
  match p with
  | [] => true
  | a :: p' =>
      match q with
      | [] => false
      | b :: q' => Bool.eqb a b && is_prefix p' q'
      end
  end.

Lemma is_prefix_true_iff : forall p q,
  is_prefix p q = true <-> exists r, q = p ++ r.
Proof.
  induction p as [|a p IH]; intro q.
  - split; [intros _; exists q; reflexivity | intros _; reflexivity].
  - split.
    + destruct q as [|b q]; cbn [is_prefix]; [discriminate|].
      intro H. apply andb_true_iff in H as [Hab Hp].
      apply eqb_prop in Hab. subst b.
      apply IH in Hp as [r Hr]. exists r. cbn [app]. now rewrite Hr.
    + intros [r Hr]. cbn [app] in Hr. subst q. cbn [is_prefix].
      apply andb_true_iff. split; [apply eqb_reflx|].
      apply IH. exists r. reflexivity.
Qed.

Lemma is_prefix_app : forall p r, is_prefix p (p ++ r) = true.
Proof. intros p r. apply is_prefix_true_iff. exists r. reflexivity. Qed.

Lemma is_prefix_refl : forall p, is_prefix p p = true.
Proof.
  intro p. pose proof (is_prefix_app p []) as H. rewrite app_nil_r in H. exact H.
Qed.

Lemma is_prefix_length : forall p q, is_prefix p q = true -> length p <= length q.
Proof.
  intros p q H. apply is_prefix_true_iff in H as [r ->]. rewrite length_app. lia.
Qed.

Lemma is_prefix_firstn : forall p q, is_prefix p q = true -> firstn (length p) q = p.
Proof.
  intros p q H. apply is_prefix_true_iff in H as [r ->].
  rewrite firstn_app, Nat.sub_diag.
  change (firstn 0 r) with (@nil bool). rewrite app_nil_r.
  apply firstn_all2. lia.
Qed.

Lemma is_prefix_skipn : forall p q,
  is_prefix p q = true -> p ++ skipn (length p) q = q.
Proof.
  intros p q H. apply is_prefix_true_iff in H as [r ->].
  rewrite skipn_app, Nat.sub_diag, skipn_all2 by lia. reflexivity.
Qed.

Lemma is_prefix_of_firstn : forall p q, firstn (length p) q = p -> is_prefix p q = true.
Proof.
  intros p q Hf. apply is_prefix_true_iff. exists (skipn (length p) q).
  transitivity (firstn (length p) q ++ skipn (length p) q).
  - symmetry. apply firstn_skipn.
  - rewrite Hf. reflexivity.
Qed.

(** Two prefixes of the same list are comparable.  This is the whole
    reason prefix-freeness makes a linear scan deterministic. *)
Lemma is_prefix_common : forall p q l,
  is_prefix p l = true -> is_prefix q l = true -> length p <= length q ->
  is_prefix p q = true.
Proof.
  intros p q l Hp Hq Hlen.
  apply is_prefix_of_firstn.
  rewrite <- (is_prefix_firstn q l Hq).
  rewrite firstn_firstn, Nat.min_l by exact Hlen.
  apply is_prefix_firstn. exact Hp.
Qed.

(** ** 3. Length histograms and canonical base values

    RFC 1951 §3.2.2 step 2:

<<
        code = 0;
        bl_count[0] = 0;
        for (bits = 1; bits <= MAX_BITS; bits++) {
            code = (code + bl_count[bits-1]) << 1;
            next_code[bits] = code;
        }
>>

    [count_len lengths b] is the plain histogram — how many entries of
    [lengths] equal [b].  [bl_count] is that histogram AFTER the RFC's
    [bl_count[0] = 0] fixup, and [nc] is [next_code], as a four-line
    structural recursion (no array, no [set!], no well-founded loop).

    THE FIXUP IS NOT COSMETIC.  A symbol whose length is 0 is ABSENT from
    the code, not a code of length 0; the RFC zeroes [bl_count[0]] before
    running the loop for exactly that reason.  Feeding the raw histogram
    in instead adds [z * 2^b] to every [nc b] (where [z] is the number of
    unused symbols).  That is a multiple of [2^b], so by [code_bits_mod]
    every CODEWORD comes out byte-identical and no codeword test can see
    it — but [nc_bound] becomes false, and with it the whole
    prefix-freeness argument.  [nc_1] and [nc_ignores_zero_lengths] pin
    the fixup by computation. *)

Definition count_len (lengths : list nat) (b : nat) : nat :=
  count_occ Nat.eq_dec lengths b.

Definition bl_count (lengths : list nat) (b : nat) : nat :=
  match b with
  | O => O
  | S _ => count_len lengths b
  end.

Fixpoint nc (lengths : list nat) (b : nat) : nat :=
  match b with
  | O => O
  | S b' => 2 * (nc lengths b' + bl_count lengths b')
  end.

Lemma count_len_app : forall l1 l2 b,
  count_len (l1 ++ l2) b = count_len l1 b + count_len l2 b.
Proof. intros; apply count_occ_app. Qed.

Lemma bl_count_0 : forall lengths, bl_count lengths 0 = 0.
Proof. reflexivity. Qed.

Lemma bl_count_pos : forall lengths b,
  1 <= b -> bl_count lengths b = count_len lengths b.
Proof. intros lengths [|b] H; [lia|reflexivity]. Qed.

Lemma nc_0 : forall lengths, nc lengths 0 = 0.
Proof. reflexivity. Qed.

(** The RFC's [bl_count[0] = 0], visible. *)
Lemma nc_1 : forall lengths, nc lengths 1 = 0.
Proof. reflexivity. Qed.

Lemma nc_succ : forall lengths b,
  nc lengths (S b) = 2 * (nc lengths b + bl_count lengths b).
Proof. reflexivity. Qed.

(** The blueprint's [ncRec blCount (b+1) = (ncRec blCount b + blCount[b]) * 2],
    verbatim, on the range where the histogram is the raw count. *)
Lemma nc_succ_pos : forall lengths b, 1 <= b ->
  nc lengths (S b) = 2 * (nc lengths b + count_len lengths b).
Proof. intros lengths b H. rewrite nc_succ, bl_count_pos by lia. reflexivity. Qed.

(** [nc] at least doubles per level. *)
Lemma nc_mono_pow : forall lengths b k, 2 ^ k * nc lengths b <= nc lengths (b + k).
Proof.
  intros lengths b k; induction k as [|k IH].
  - rewrite Nat.add_0_r. cbn [Nat.pow]. lia.
  - replace (b + S k) with (S (b + k)) by lia.
    rewrite nc_succ. cbn [Nat.pow]. nia.
Qed.

(** ** 4. Kraft sums and validity

    [kraft_term maxBits len] is the leaf weight [2^(maxBits - len)] of a
    code of length [len], and 0 for an absent symbol ([len = 0]).
    [kraft_sum_from lengths maxBits b] adds the weights of all entries
    with length at least [b] (so entries of length 0 never contribute).

    [ValidLengths] is the Kraft INEQUALITY, not the equality: RFC 1951
    admits incomplete codes, and zlib deliberately accepts the
    single-symbol distance code ([valid_lengths_incomplete] below).
    Everything is [nat]: no rationals, no division. *)

Definition kraft_term (maxBits len : nat) : nat :=
  match len with
  | O => O
  | S _ => 2 ^ (maxBits - len)
  end.

Definition kraft_at (maxBits b len : nat) : nat :=
  if b <=? len then kraft_term maxBits len else 0.

Definition kraft_sum_from (lengths : list nat) (maxBits b : nat) : nat :=
  list_sum (map (kraft_at maxBits b) lengths).

Definition kraft_sum (lengths : list nat) (maxBits : nat) : nat :=
  kraft_sum_from lengths maxBits 0.

Definition ValidLengths (lengths : list nat) (maxBits : nat) : Prop :=
  (forall len, In len lengths -> len <= maxBits)
  /\ kraft_sum lengths maxBits <= 2 ^ maxBits.

Definition valid_lengths_b (lengths : list nat) (maxBits : nat) : bool :=
  forallb (fun len => len <=? maxBits) lengths
  && (kraft_sum lengths maxBits <=? 2 ^ maxBits).

Lemma valid_lengths_reflect : forall lengths maxBits,
  reflect (ValidLengths lengths maxBits) (valid_lengths_b lengths maxBits).
Proof.
  intros lengths maxBits. apply iff_reflect. unfold ValidLengths, valid_lengths_b.
  split.
  - intros [H1 H2]. apply andb_true_iff. split.
    + apply forallb_forall. intros x Hx. apply Nat.leb_le. apply H1, Hx.
    + apply Nat.leb_le. exact H2.
  - intro H. apply andb_true_iff in H as [Ha Hb]. split.
    + intros len Hin. apply Nat.leb_le.
      exact (proj1 (forallb_forall _ _) Ha len Hin).
    + apply Nat.leb_le. exact Hb.
Qed.

Corollary valid_lengths_b_true : forall lengths maxBits,
  valid_lengths_b lengths maxBits = true -> ValidLengths lengths maxBits.
Proof.
  intros lengths maxBits H.
  destruct (valid_lengths_reflect lengths maxBits); [assumption|discriminate].
Qed.

Corollary valid_lengths_b_false : forall lengths maxBits,
  valid_lengths_b lengths maxBits = false -> ~ ValidLengths lengths maxBits.
Proof.
  intros lengths maxBits H.
  destruct (valid_lengths_reflect lengths maxBits); [discriminate|assumption].
Qed.

Lemma kraft_at_lt : forall maxBits b len, len < b -> kraft_at maxBits b len = 0.
Proof.
  intros maxBits b len H. unfold kraft_at.
  replace (b <=? len) with false by (symmetry; apply Nat.leb_gt; lia). reflexivity.
Qed.

Lemma kraft_at_ge : forall maxBits b len,
  b <= len -> kraft_at maxBits b len = kraft_term maxBits len.
Proof.
  intros maxBits b len H. unfold kraft_at.
  replace (b <=? len) with true by (symmetry; apply Nat.leb_le; lia). reflexivity.
Qed.

Lemma kraft_sum_from_nil : forall maxBits b, kraft_sum_from [] maxBits b = 0.
Proof. reflexivity. Qed.

Lemma kraft_sum_from_cons : forall len l maxBits b,
  kraft_sum_from (len :: l) maxBits b
  = kraft_at maxBits b len + kraft_sum_from l maxBits b.
Proof. reflexivity. Qed.

(** Peeling one level off a Kraft sum. *)
Lemma kraft_sum_from_step : forall maxBits b lengths,
  kraft_sum_from lengths maxBits b
  = count_len lengths b * kraft_term maxBits b + kraft_sum_from lengths maxBits (S b).
Proof.
  intros maxBits b lengths. unfold count_len.
  induction lengths as [|len l IH].
  - cbn. lia.
  - rewrite !kraft_sum_from_cons, IH.
    destruct (Nat.eq_dec len b) as [He|Hne].
    + subst len.
      rewrite (count_occ_cons_eq Nat.eq_dec l (eq_refl b)).
      rewrite (kraft_at_ge maxBits b b (Nat.le_refl b)).
      rewrite (kraft_at_lt maxBits (S b) b (Nat.lt_succ_diag_r b)).
      nia.
    + rewrite (count_occ_cons_neq Nat.eq_dec l Hne).
      assert (Hsame : kraft_at maxBits b len = kraft_at maxBits (S b) len).
      { destruct (Nat.le_gt_cases b len) as [Hle|Hlt].
        - rewrite (kraft_at_ge maxBits b len Hle).
          rewrite (kraft_at_ge maxBits (S b) len) by lia. reflexivity.
        - rewrite (kraft_at_lt maxBits b len Hlt).
          rewrite (kraft_at_lt maxBits (S b) len) by lia. reflexivity. }
      rewrite Hsame. lia.
Qed.

(** The same step, in the [bl_count] form the [nc] recurrence uses. *)
Lemma kraft_sum_from_step_bl : forall maxBits b lengths,
  kraft_sum_from lengths maxBits b
  = bl_count lengths b * 2 ^ (maxBits - b) + kraft_sum_from lengths maxBits (S b).
Proof.
  intros maxBits b lengths. rewrite (kraft_sum_from_step maxBits b lengths).
  destruct b as [|b]; cbn [bl_count kraft_term]; lia.
Qed.

(** ** 5. The conservation law and the bound

    Everything canonical codes need, in two lemmas. *)

Theorem nc_kraft_conservation : forall lengths maxBits b, b <= maxBits ->
  nc lengths b * 2 ^ (maxBits - b) + kraft_sum_from lengths maxBits b
  = kraft_sum_from lengths maxBits 0.
Proof.
  intros lengths maxBits b. induction b as [|b IH]; intro Hb.
  - cbn [nc]. lia.
  - assert (Hb' : b <= maxBits) by lia. specialize (IH Hb').
    rewrite nc_succ.
    rewrite (kraft_sum_from_step_bl maxBits b lengths) in IH.
    assert (Hp : 2 ^ (maxBits - b) = 2 * 2 ^ (maxBits - S b)).
    { replace (maxBits - b) with (S (maxBits - S b)) by lia.
      cbn [Nat.pow]. lia. }
    rewrite Hp in IH. nia.
Qed.

Lemma two_pow_pos : forall k, 0 < 2 ^ k.
Proof. induction k as [|k IH]; cbn [Nat.pow]; lia. Qed.

(** [nc b + bl_count b] is the first code value of length [b+1], halved;
    Kraft says it fits in [b] bits. *)
Theorem nc_count_bound : forall lengths maxBits b,
  ValidLengths lengths maxBits -> b <= maxBits ->
  nc lengths b + bl_count lengths b <= 2 ^ b.
Proof.
  intros lengths maxBits b [_ Hk] Hb.
  pose proof (nc_kraft_conservation lengths maxBits b Hb) as Hc.
  rewrite (kraft_sum_from_step_bl maxBits b lengths) in Hc.
  unfold kraft_sum in Hk.
  assert (Hpow : 2 ^ b * 2 ^ (maxBits - b) = 2 ^ maxBits).
  { rewrite <- Nat.pow_add_r. f_equal. lia. }
  apply (proj2 (Nat.mul_le_mono_pos_r
                  (nc lengths b + bl_count lengths b) (2 ^ b)
                  (2 ^ (maxBits - b)) (two_pow_pos (maxBits - b)))).
  rewrite Hpow. nia.
Qed.

(** The blueprint's [nc_bound].  The [1 <= b] hypothesis is not
    decoration: at [b = 0] the left-hand side counts the ABSENT symbols
    and can be arbitrarily large, while [2^0 = 1]. *)
Corollary nc_bound : forall lengths maxBits b,
  ValidLengths lengths maxBits -> 1 <= b -> b <= maxBits ->
  nc lengths b + count_len lengths b <= 2 ^ b.
Proof.
  intros lengths maxBits b HV H1 Hb.
  rewrite <- (bl_count_pos lengths b H1).
  exact (nc_count_bound lengths maxBits b HV Hb).
Qed.

(** ** 6. [code_for] / [all_codes] / [code_table]

    [code_for lengths maxBits sym] is total and unconditional: [None] if
    [sym] is out of range, or its length is 0, or its length exceeds
    [maxBits]; otherwise the canonical codeword.  The value is
    [nc lengths len] plus the number of EARLIER symbols with the SAME
    length ([code_offset]).

    [code_table] is [all_codes] with the components flipped, and it is
    named rather than inlined on purpose: symbol-first and codeword-first
    tables both occur, and prefix-freeness is a statement about the
    codeword-first one.

    COMPLEXITY, honestly.  Both [nc] and [code_offset] are recomputed per
    symbol, exactly as in the blueprint, so [all_codes] is quadratic in
    [length lengths].  Hoisting them would mean either a memo table in
    [code_for]'s statement or a fold whose equality with the per-symbol
    spec is its own proof obligation; neither is worth complicating the
    FROZEN statements for, since the only reductions this layer performs
    are the small worked examples at the bottom of this file.  The
    executable table builder is [inftrees.c]'s, in another file. *)

Definition code_offset (lengths : list nat) (sym len : nat) : nat :=
  count_len (firstn sym lengths) len.

Definition code_for (lengths : list nat) (maxBits sym : nat) : option (list bool) :=
  match nth_error lengths sym with
  | None => None
  | Some len =>
      if (len =? 0) || (maxBits <? len) then None
      else Some (code_bits (Z.of_nat (nc lengths len + code_offset lengths sym len)) len)
  end.

Definition code_entry (lengths : list nat) (maxBits sym : nat)
                      (acc : list (nat * list bool)) : list (nat * list bool) :=
  match code_for lengths maxBits sym with
  | Some cw => (sym, cw) :: acc
  | None => acc
  end.

Definition all_codes (lengths : list nat) (maxBits : nat) : list (nat * list bool) :=
  fold_right (code_entry lengths maxBits) [] (seq 0 (length lengths)).

Definition code_table (lengths : list nat) (maxBits : nat) : list (list bool * nat) :=
  map (fun p => (snd p, fst p)) (all_codes lengths maxBits).

Lemma code_for_inv : forall lengths maxBits sym cw,
  code_for lengths maxBits sym = Some cw ->
  exists len, nth_error lengths sym = Some len
           /\ 1 <= len /\ len <= maxBits
           /\ cw = code_bits (Z.of_nat (nc lengths len + code_offset lengths sym len)) len.
Proof.
  intros lengths maxBits sym cw H. unfold code_for in H.
  destruct (nth_error lengths sym) as [len|] eqn:E; [|discriminate].
  destruct ((len =? 0) || (maxBits <? len)) eqn:Eb; [discriminate|].
  apply orb_false_iff in Eb as [E1 E2].
  apply Nat.eqb_neq in E1. apply Nat.ltb_ge in E2.
  exists len. split; [reflexivity|]. split; [lia|]. split; [lia|]. congruence.
Qed.

Lemma code_for_range : forall lengths maxBits sym cw,
  code_for lengths maxBits sym = Some cw -> sym < length lengths.
Proof.
  intros lengths maxBits sym cw H. unfold code_for in H.
  destruct (nth_error lengths sym) eqn:E; [|discriminate].
  apply nth_error_Some. rewrite E. discriminate.
Qed.

Lemma fold_code_entry_In : forall lengths maxBits L sym cw,
  In (sym, cw) (fold_right (code_entry lengths maxBits) [] L)
  <-> In sym L /\ code_for lengths maxBits sym = Some cw.
Proof.
  intros lengths maxBits L. induction L as [|s L IH]; intros sym cw.
  - cbn [fold_right In]. split; [contradiction | intros [[] _]].
  - cbn [fold_right]. unfold code_entry at 1.
    destruct (code_for lengths maxBits s) as [cws|] eqn:Es.
    + cbn [In]. split.
      * intros [Heq | Hin].
        -- inversion Heq; subst. split; [left; reflexivity|exact Es].
        -- apply IH in Hin as [H1 H2]. split; [right; exact H1|exact H2].
      * intros [[Heq|Hin] Hc].
        -- subst s. left. rewrite Es in Hc. inversion Hc. reflexivity.
        -- right. apply IH. split; assumption.
    + cbn [In]. split.
      * intro Hin. apply IH in Hin as [H1 H2]. split; [right; exact H1|exact H2].
      * intros [[Heq|Hin] Hc].
        -- subst s. rewrite Es in Hc. discriminate.
        -- apply IH. split; assumption.
Qed.

Theorem all_codes_In_iff : forall lengths maxBits sym cw,
  In (sym, cw) (all_codes lengths maxBits) <-> code_for lengths maxBits sym = Some cw.
Proof.
  intros lengths maxBits sym cw. unfold all_codes.
  rewrite fold_code_entry_In. split.
  - intros [_ H]; exact H.
  - intro H. split; [|exact H].
    pose proof (code_for_range lengths maxBits sym cw H) as Hlt.
    apply in_seq. lia.
Qed.

Theorem code_table_In_iff : forall lengths maxBits sym cw,
  In (cw, sym) (code_table lengths maxBits) <-> code_for lengths maxBits sym = Some cw.
Proof.
  intros lengths maxBits sym cw. unfold code_table. rewrite in_map_iff. split.
  - intros [[s c] [Heq Hin]]. cbn [fst snd] in Heq. inversion Heq; subst.
    apply all_codes_In_iff in Hin. exact Hin.
  - intro H. exists (sym, cw). split; [reflexivity|].
    apply all_codes_In_iff. exact H.
Qed.

(** ** 7. The crown jewel: canonical codes are prefix free

    Two ingredients: the offset of a symbol is strictly monotone in the
    symbol index (so distinct symbols of the same length get distinct
    values), and [nc_bound] (so a value never overflows its width). *)

Lemma code_offset_mono : forall lengths s1 s2 len,
  s1 < s2 -> nth_error lengths s1 = Some len ->
  code_offset lengths s1 len < code_offset lengths s2 len.
Proof.
  intros lengths s1 s2 len Hlt Hn.
  apply nth_error_split in Hn as [l1 [l2 [-> Hl1]]].
  unfold code_offset, count_len.
  rewrite !firstn_app, Hl1, Nat.sub_diag.
  change (firstn 0 (len :: l2)) with (@nil nat).
  rewrite app_nil_r.
  rewrite (@firstn_all2 nat s1 l1) by lia.
  rewrite (@firstn_all2 nat s2 l1) by lia.
  rewrite count_occ_app.
  replace (s2 - s1) with (S (s2 - s1 - 1)) by lia.
  cbn [firstn].
  rewrite (count_occ_cons_eq Nat.eq_dec (firstn (s2 - s1 - 1) l2) (eq_refl len)).
  lia.
Qed.

Lemma code_offset_inj : forall lengths s1 s2 len,
  nth_error lengths s1 = Some len -> nth_error lengths s2 = Some len ->
  code_offset lengths s1 len = code_offset lengths s2 len -> s1 = s2.
Proof.
  intros lengths s1 s2 len H1 H2 Heq.
  destruct (lt_eq_lt_dec s1 s2) as [[Hlt|Heqs]|Hgt]; [|exact Heqs|].
  - pose proof (code_offset_mono lengths s1 s2 len Hlt H1). lia.
  - pose proof (code_offset_mono lengths s2 s1 len Hgt H2). lia.
Qed.

Lemma code_offset_lt : forall lengths sym len,
  nth_error lengths sym = Some len ->
  code_offset lengths sym len < count_len lengths len.
Proof.
  intros lengths sym len H.
  apply nth_error_split in H as [l1 [l2 [-> Hl1]]].
  unfold code_offset, count_len.
  rewrite firstn_app, Hl1, Nat.sub_diag.
  change (firstn 0 (len :: l2)) with (@nil nat).
  rewrite app_nil_r, (@firstn_all2 nat sym l1) by lia.
  rewrite count_occ_app, (count_occ_cons_eq Nat.eq_dec l2 (eq_refl len)).
  lia.
Qed.

Lemma two_pow_nat : forall k, (2 ^ Z.of_nat k)%Z = Z.of_nat (2 ^ k).
Proof. intro k. rewrite Nat2Z.inj_pow. reflexivity. Qed.

Lemma two_pow_mul_nat : forall k n,
  (2 ^ Z.of_nat k * (Z.of_nat n + 1))%Z = Z.of_nat (2 ^ k * (n + 1)).
Proof.
  intros k n. rewrite Nat2Z.inj_mul, Nat2Z.inj_add, two_pow_nat. reflexivity.
Qed.

(** Everything the prefix-freeness argument needs about one codeword,
    in one package. *)
Lemma code_for_value : forall lengths maxBits sym cw,
  ValidLengths lengths maxBits ->
  code_for lengths maxBits sym = Some cw ->
  exists len v,
       nth_error lengths sym = Some len
    /\ 1 <= len /\ len <= maxBits
    /\ v = nc lengths len + code_offset lengths sym len
    /\ nc lengths len <= v
    /\ v + 1 <= nc lengths len + bl_count lengths len
    /\ v < 2 ^ len
    /\ cw = code_bits (Z.of_nat v) len.
Proof.
  intros lengths maxBits sym cw HV H.
  apply code_for_inv in H as [len [Hn [H1 [Hm Hcw]]]].
  exists len, (nc lengths len + code_offset lengths sym len).
  pose proof (code_offset_lt lengths sym len Hn) as Ho.
  pose proof (bl_count_pos lengths len H1) as Hb.
  pose proof (nc_count_bound lengths maxBits len HV Hm) as Hbd.
  split; [exact Hn|]. split; [exact H1|]. split; [exact Hm|].
  split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. exact Hcw.
Qed.

Theorem canonical_prefix_free : forall lengths maxBits s1 s2 cw1 cw2,
  ValidLengths lengths maxBits ->
  code_for lengths maxBits s1 = Some cw1 ->
  code_for lengths maxBits s2 = Some cw2 ->
  s1 <> s2 ->
  is_prefix cw1 cw2 = false.
Proof.
  intros lengths maxBits s1 s2 cw1 cw2 HV H1 H2 Hne.
  destruct (is_prefix cw1 cw2) eqn:Hp; [exfalso|reflexivity].
  apply (code_for_value lengths maxBits s1 cw1 HV) in H1
    as [l1 [v1 [Hn1 [Ha1 [Hm1 [Hv1e [Hv1lo [Hv1hi [Hv1b Hc1]]]]]]]]].
  apply (code_for_value lengths maxBits s2 cw2 HV) in H2
    as [l2 [v2 [Hn2 [Ha2 [Hm2 [Hv2e [Hv2lo [Hv2hi [Hv2b Hc2]]]]]]]]].
  subst cw1 cw2.
  assert (HZ1 : (0 <= Z.of_nat v1 < 2 ^ Z.of_nat l1)%Z)
    by (rewrite two_pow_nat; lia).
  assert (HZ2 : (0 <= Z.of_nat v2 < 2 ^ Z.of_nat l2)%Z)
    by (rewrite two_pow_nat; lia).
  assert (Hle : l1 <= l2).
  { pose proof (is_prefix_length _ _ Hp) as HL.
    rewrite !code_bits_length in HL. exact HL. }
  destruct (Nat.eq_dec l1 l2) as [Heql|Hneql].
  - (* Same length: the codewords coincide, hence the offsets, hence the
       symbols — contradicting [s1 <> s2]. *)
    subst l2.
    apply Hne.
    assert (Hcw : code_bits (Z.of_nat v1) l1 = code_bits (Z.of_nat v2) l1).
    { apply is_prefix_true_iff in Hp as [r Hr].
      assert (Hlr : r = []).
      { assert (HL : length (code_bits (Z.of_nat v2) l1)
                     = length (code_bits (Z.of_nat v1) l1 ++ r))
          by (rewrite <- Hr; reflexivity).
        rewrite length_app, !code_bits_length in HL.
        destruct r as [|x r]; [reflexivity|cbn [length] in HL; lia]. }
      subst r. rewrite app_nil_r in Hr. symmetry. exact Hr. }
    apply (code_bits_inj l1 _ _ HZ1 HZ2) in Hcw.
    assert (Hv : v1 = v2) by lia.
    apply (code_offset_inj lengths s1 s2 l1 Hn1 Hn2). lia.
  - (* Strictly shorter: the canonical layout puts every length-[l2] value
       at or above [nc l2], while a strict prefix bounds [v2] below it. *)
    assert (Hlt : l1 < l2) by lia.
    assert (Hfir : firstn l1 (code_bits (Z.of_nat v2) l2)
                   = code_bits (Z.of_nat v1) l1).
    { pose proof (is_prefix_firstn _ _ Hp) as HF.
      rewrite code_bits_length in HF. exact HF. }
    rewrite (code_bits_firstn l2 l1 (Z.of_nat v2) Hle) in Hfir.
    assert (Hd : (0 <= Z.of_nat v2 / 2 ^ Z.of_nat (l2 - l1) < 2 ^ Z.of_nat l1)%Z).
    { split.
      - apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia].
      - apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; lia|].
        rewrite <- Z.pow_add_r by lia.
        replace (Z.of_nat (l2 - l1) + Z.of_nat l1)%Z with (Z.of_nat l2) by lia.
        lia. }
    apply (code_bits_inj l1 _ _ Hd HZ1) in Hfir.
    assert (Hub : (Z.of_nat v2 < 2 ^ Z.of_nat (l2 - l1) * (Z.of_nat v1 + 1))%Z).
    { rewrite <- Hfir. apply Z.mul_succ_div_gt. apply Z.pow_pos_nonneg; lia. }
    rewrite two_pow_mul_nat in Hub. apply Nat2Z.inj_lt in Hub.
    assert (Hmono : 2 ^ (l2 - S l1) * nc lengths (S l1) <= nc lengths l2).
    { replace l2 with (S l1 + (l2 - S l1)) at 2 by lia. apply nc_mono_pow. }
    rewrite nc_succ in Hmono.
    assert (Hpow : 2 ^ (l2 - l1) = 2 * 2 ^ (l2 - S l1)).
    { replace (l2 - l1) with (S (l2 - S l1)) by lia. cbn [Nat.pow]. lia. }
    assert (Hchain : 2 ^ (l2 - l1) * (v1 + 1) <= nc lengths l2).
    { rewrite Hpow. nia. }
    lia.
Qed.

(** ** 8. Declarative decoding

    [hdecode] is a linear scan: the first table entry whose codeword is a
    prefix of the stream wins.  It is DEFINED without any prefix-freeness
    hypothesis; prefix-freeness is what makes it CORRECT
    ([hdecode_complete]).

    [PrefixFreeTable] is the membership form (four binders over entries),
    not the index-quantified form: every call site spells this one out. *)

Fixpoint hdecode {A : Type} (table : list (list bool * A)) (bits : list bool)
  : option (A * list bool) :=
  match table with
  | [] => None
  | (cw, a) :: rest =>
      if is_prefix cw bits then Some (a, skipn (length cw) bits)
      else hdecode rest bits
  end.

Definition PrefixFreeTable {A : Type} (table : list (list bool * A)) : Prop :=
  forall cw1 s1 cw2 s2, In (cw1, s1) table -> In (cw2, s2) table ->
                        (cw1, s1) <> (cw2, s2) -> is_prefix cw1 cw2 = false.

Lemma hdecode_sound : forall (A : Type) (table : list (list bool * A)) bits a rem,
  hdecode table bits = Some (a, rem) ->
  exists cw, In (cw, a) table /\ is_prefix cw bits = true /\ bits = cw ++ rem.
Proof.
  intros A table; induction table as [|[cw0 a0] rest IH]; intros bits a rem H.
  - discriminate.
  - cbn [hdecode] in H. destruct (is_prefix cw0 bits) eqn:Hp.
    + inversion H; subst. exists cw0. split; [left; reflexivity|].
      split; [exact Hp|]. symmetry. apply is_prefix_skipn. exact Hp.
    + apply IH in H as [cw [Hin [Hpf Heq]]]. exists cw.
      split; [right; exact Hin|]. split; assumption.
Qed.

Lemma hdecode_none : forall (A : Type) (table : list (list bool * A)) bits,
  hdecode table bits = None ->
  forall cw a, In (cw, a) table -> is_prefix cw bits = false.
Proof.
  intros A table; induction table as [|[cw0 a0] rest IH]; intros bits H cw a Hin.
  - contradiction.
  - cbn [hdecode] in H. destruct (is_prefix cw0 bits) eqn:Hp; [discriminate|].
    destruct Hin as [Heq|Hin].
    + inversion Heq; subst. exact Hp.
    + exact (IH bits H cw a Hin).
Qed.

(** The decidability hypothesis on [A] is not avoidable and not
    incidental: a prefix-free table cannot contain [(cw,a1)] and
    [(cw,a2)] with [a1 <> a2] (that would need [is_prefix cw cw = false],
    contradicting [is_prefix_refl]) — but turning that into [a1 = a2]
    requires deciding the equality.  [nat] supplies it at every call site
    in this layer. *)
Theorem hdecode_complete :
  forall (A : Type) (Adec : forall x y : A, {x = y} + {x <> y})
         (table : list (list bool * A)) (cw : list bool) (a : A) (rest : list bool),
  PrefixFreeTable table -> In (cw, a) table ->
  hdecode table (cw ++ rest) = Some (a, rest).
Proof.
  intros A Adec table cw a rest HPF Hin.
  assert (Hpcw : is_prefix cw (cw ++ rest) = true) by apply is_prefix_app.
  destruct (hdecode table (cw ++ rest)) as [[a' rem']|] eqn:Hd.
  - apply hdecode_sound in Hd as [cw' [Hin' [Hp' Heq]]].
    assert (Hcw : cw' = cw).
    { destruct (list_eq_dec Bool.bool_dec cw' cw) as [Hy|Hne]; [exact Hy|exfalso].
      destruct (Nat.le_gt_cases (length cw') (length cw)) as [Hle|Hgt].
      - pose proof (is_prefix_common cw' cw (cw ++ rest) Hp' Hpcw Hle) as Ht.
        assert (Hf : is_prefix cw' cw = false)
          by (apply (HPF cw' a' cw a Hin' Hin); congruence).
        congruence.
      - pose proof (is_prefix_common cw cw' (cw ++ rest) Hpcw Hp'
                      (Nat.lt_le_incl _ _ Hgt)) as Ht.
        assert (Hf : is_prefix cw cw' = false)
          by (apply (HPF cw a cw' a' Hin Hin'); congruence).
        congruence. }
    subst cw'.
    assert (Ha : a' = a).
    { destruct (Adec a' a) as [Hy|Hne]; [exact Hy|exfalso].
      assert (Hf : is_prefix cw cw = false)
        by (apply (HPF cw a' cw a Hin' Hin); congruence).
      pose proof (is_prefix_refl cw). congruence. }
    subst a'. f_equal. f_equal. symmetry. exact (app_inv_head cw rest rem' Heq).
  - exfalso. pose proof (hdecode_none A table (cw ++ rest) Hd cw a Hin). congruence.
Qed.

Theorem code_table_prefix_free : forall lengths maxBits,
  ValidLengths lengths maxBits -> PrefixFreeTable (code_table lengths maxBits).
Proof.
  intros lengths maxBits HV cw1 s1 cw2 s2 H1 H2 Hne.
  apply code_table_In_iff in H1. apply code_table_In_iff in H2.
  destruct (Nat.eq_dec s1 s2) as [Heq|Hs].
  - exfalso. apply Hne. subst s2. congruence.
  - exact (canonical_prefix_free lengths maxBits s1 s2 cw1 cw2 HV H1 H2 Hs).
Qed.

(** The L0 handshake: what the encoder half writes, the decoder half
    reads back, symbol for symbol, with the rest of the stream intact. *)
Corollary hdecode_code_for : forall lengths maxBits sym cw rest,
  ValidLengths lengths maxBits ->
  code_for lengths maxBits sym = Some cw ->
  hdecode (code_table lengths maxBits) (cw ++ rest) = Some (sym, rest).
Proof.
  intros lengths maxBits sym cw rest HV H.
  apply (hdecode_complete nat Nat.eq_dec).
  - apply code_table_prefix_free. exact HV.
  - apply code_table_In_iff. exact H.
Qed.

(** ** 9. LZ77 resolution

    [LzRef len dist] copies [len] bytes starting [dist] bytes back from
    the current end of the output.  Overlapping copies (the [dist < len]
    case, which DEFLATE uses heavily for runs) are given in CLOSED FORM
    rather than as a byte-at-a-time loop: index [i] of the run reads
    [acc] at [length acc - dist + i mod dist].  [lz_overlap] and
    [lz_overlap2] pin that against worked examples.

    [LzEnd] STOPS resolution and returns what has been produced so far
    ([resolve_lz_end]); symbols after it are ignored.  A reference with
    [dist = 0] or [dist > length acc] fails ([resolve_lz_bad_dist]).

    NOT proved here: that this closed form agrees with a sequential
    byte-at-a-time copy.  No L0 client needs it, and asserting it without
    a lemma would violate this file's discipline. *)

Inductive lz_sym : Set :=
| LzLit (b : Z)
| LzRef (len dist : nat)
| LzEnd.

Definition lz_copy (acc : list Z) (len dist : nat) : list Z :=
  map (fun i => nth (length acc - dist + i mod dist) acc 0%Z) (seq 0 len).

Fixpoint resolve_lz (syms : list lz_sym) (acc : list Z) : option (list Z) :=
  match syms with
  | [] => Some acc
  | LzLit b :: tl => resolve_lz tl (acc ++ [b])
  | LzEnd :: _ => Some acc
  | LzRef len dist :: tl =>
      if (dist =? 0) || (length acc <? dist) then None
      else resolve_lz tl (acc ++ lz_copy acc len dist)
  end.

Lemma lz_copy_length : forall acc len dist, length (lz_copy acc len dist) = len.
Proof. intros; unfold lz_copy; rewrite length_map, length_seq; reflexivity. Qed.

(** One more copied byte at a time, for clients that must induct. *)
Lemma lz_copy_S : forall acc len dist,
  lz_copy acc (S len) dist
  = lz_copy acc len dist ++ [nth (length acc - dist + len mod dist) acc 0%Z].
Proof.
  intros acc len dist. unfold lz_copy.
  rewrite seq_S, map_app. cbn [map]. rewrite Nat.add_0_l. reflexivity.
Qed.

Lemma resolve_lz_nil : forall acc, resolve_lz [] acc = Some acc.
Proof. reflexivity. Qed.

Lemma resolve_lz_end : forall tl acc, resolve_lz (LzEnd :: tl) acc = Some acc.
Proof. reflexivity. Qed.

Lemma resolve_lz_bad_dist : forall len dist tl acc,
  dist = 0 \/ length acc < dist ->
  resolve_lz (LzRef len dist :: tl) acc = None.
Proof.
  intros len dist tl acc H. cbn [resolve_lz].
  replace ((dist =? 0) || (length acc <? dist)) with true; [reflexivity|].
  symmetry. apply orb_true_iff. destruct H as [->|H].
  - left. reflexivity.
  - right. apply Nat.ltb_lt. exact H.
Qed.

(** The accumulator is never rewritten, only extended.  Both halves of
    the round trip need this. *)
Theorem resolve_lz_extends : forall syms acc out,
  resolve_lz syms acc = Some out -> exists ext, out = acc ++ ext.
Proof.
  induction syms as [|s tl IH]; intros acc out H.
  - cbn [resolve_lz] in H. inversion H; subst. exists []. symmetry. apply app_nil_r.
  - destruct s as [b|len dist|]; cbn [resolve_lz] in H.
    + apply IH in H as [ext ->]. exists ([b] ++ ext). symmetry. apply app_assoc.
    + destruct ((dist =? 0) || (length acc <? dist)); [discriminate|].
      apply IH in H as [ext ->]. exists (lz_copy acc len dist ++ ext).
      symmetry. apply app_assoc.
    + inversion H; subst. exists []. symmetry. apply app_nil_r.
Qed.

Corollary resolve_lz_length : forall syms acc out,
  resolve_lz syms acc = Some out -> length acc <= length out.
Proof.
  intros syms acc out H. apply resolve_lz_extends in H as [ext ->].
  rewrite length_app. lia.
Qed.

(** ** 10. Computational pins

    These are the file's real defences.  A comment cannot catch an
    MSB/LSB inversion or an off-by-one in the [count_len]/[nc]/offset
    chain; [reflexivity] against RFC 1951's own worked example can. *)

(** *** Bit order *)

(** [6 = 0b110].  MSB first the codeword is [1;1;0]; LSB first the data
    element is [0;1;1].  They are different lists, and the file says so
    by computation. *)
Example code_bits_msb_first : code_bits 6%Z 3 = [true; true; false].
Proof. reflexivity. Qed.

Example write_bits_lsb_first : write_bits 3 6%Z = [false; true; true].
Proof. reflexivity. Qed.

Example code_bits_is_not_write_bits : code_bits 6%Z 3 <> write_bits 3 6%Z.
Proof. discriminate. Qed.

Example code_bits_rev_write_bits_6 : code_bits 6%Z 3 = rev (write_bits 3 6%Z).
Proof. reflexivity. Qed.

(** *** RFC 1951 §3.2.2, the standard's own worked example

    Lengths [[3;3;3;3;3;2;4;4]] for symbols A..H must produce
    [010 011 100 101 110 00 1110 1111].  This checks
    [count_len] -> [nc] -> [code_offset] -> [code_bits] end to end
    against the standard rather than against itself. *)

Definition rfc_lengths : list nat := [3; 3; 3; 3; 3; 2; 4; 4].

Example rfc_valid : valid_lengths_b rfc_lengths 4 = true.
Proof. reflexivity. Qed.

Example rfc_nc : map (nc rfc_lengths) [0; 1; 2; 3; 4] = [0; 0; 0; 2; 14].
Proof. reflexivity. Qed.

Example rfc_codes :
  map (code_for rfc_lengths 4) [0; 1; 2; 3; 4; 5; 6; 7]
  = [ Some [false; true;  false];
      Some [false; true;  true];
      Some [true;  false; false];
      Some [true;  false; true];
      Some [true;  true;  false];
      Some [false; false];
      Some [true;  true;  true; false];
      Some [true;  true;  true; true] ].
Proof. reflexivity. Qed.

Example rfc_out_of_range : code_for rfc_lengths 4 8 = None.
Proof. reflexivity. Qed.

(** Decoding [00 1110] finds F (symbol 5) and leaves [1110] behind. *)
Example rfc_decode_F :
  hdecode (code_table rfc_lengths 4) [false; false; true; true; true; false]
  = Some (5, [true; true; true; false]).
Proof. reflexivity. Qed.

Example rfc_decode_G :
  hdecode (code_table rfc_lengths 4) [true; true; true; false; false]
  = Some (6, [false]).
Proof. reflexivity. Qed.

(** NON-VACUITY.  [canonical_prefix_free] and [hdecode_code_for] are
    universally quantified over [ValidLengths] codes; these two discharge
    that hypothesis on the standard's own example, so the theorems are
    known to say something about at least one real code. *)
Example rfc_prefix_free : PrefixFreeTable (code_table rfc_lengths 4).
Proof. apply code_table_prefix_free, valid_lengths_b_true. reflexivity. Qed.

Example rfc_roundtrip :
  hdecode (code_table rfc_lengths 4) ([false; true; false] ++ [true; true])
  = Some (0, [true; true]).
Proof.
  apply hdecode_code_for with (maxBits := 4).
  - apply valid_lengths_b_true. reflexivity.
  - reflexivity.
Qed.

(** *** Absent symbols

    [[0;2;0;3;3;1]] has two unused symbols.  The RFC's [bl_count[0] = 0]
    fixup makes [nc 3 = 6]; feeding the raw histogram in instead would
    give [22], which — by [code_bits_mod] — yields the SAME codewords, so
    only this [nc] pin catches it. *)

Definition zero_lengths : list nat := [0; 2; 0; 3; 3; 1].

Example zero_lengths_valid : valid_lengths_b zero_lengths 3 = true.
Proof. reflexivity. Qed.

Example nc_ignores_zero_lengths : map (nc zero_lengths) [1; 2; 3] = [0; 2; 6].
Proof. reflexivity. Qed.

Example zero_lengths_codes :
  map (code_for zero_lengths 3) [0; 1; 2; 3; 4; 5]
  = [ None;
      Some [true; false];
      None;
      Some [true; true; false];
      Some [true; true; true];
      Some [false] ].
Proof. reflexivity. Qed.

(** *** [maxBits] is load bearing

    Two codes of length 8 are fine under a 9-bit (or 15-bit) budget and
    illegal under the code-length tree's 7-bit budget.  A default would
    hide this. *)

Example maxbits_matters_9 : valid_lengths_b [8; 8] 9 = true.
Proof. reflexivity. Qed.

Example maxbits_matters_7 : valid_lengths_b [8; 8] 7 = false.
Proof. reflexivity. Qed.

(** Kraft is an INEQUALITY: zlib's one-symbol distance code is valid. *)
Example valid_lengths_incomplete : valid_lengths_b [1] 7 = true.
Proof. reflexivity. Qed.

Example valid_lengths_oversubscribed : valid_lengths_b [1; 1; 1] 7 = false.
Proof. reflexivity. Qed.

(** *** LZ77 *)

(** The overlapping run [dist = 1]: one byte repeated. *)
Example lz_overlap : resolve_lz [LzLit 65%Z; LzRef 3 1] [] = Some [65; 65; 65; 65]%Z.
Proof. reflexivity. Qed.

(** [dist = 2], [len = 5]: the two-byte pattern repeats past its own end. *)
Example lz_overlap2 :
  resolve_lz [LzLit 1%Z; LzLit 2%Z; LzRef 5 2; LzEnd] [] = Some [1; 2; 1; 2; 1; 2; 1]%Z.
Proof. reflexivity. Qed.

Example lz_no_history : resolve_lz [LzRef 2 1] [] = None.
Proof. reflexivity. Qed.

Example lz_end_stops : resolve_lz [LzLit 7%Z; LzEnd; LzLit 9%Z] [] = Some [7]%Z.
Proof. reflexivity. Qed.
