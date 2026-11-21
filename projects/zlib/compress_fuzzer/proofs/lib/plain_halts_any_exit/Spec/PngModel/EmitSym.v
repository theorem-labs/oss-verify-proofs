(** * Spec.PngModel.EmitSym — the declarative DEFLATE symbol EMITTER and the
      per-symbol decode-of-encode inverse (round-trip layer L-C, part A).

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT.  Depends only on
    [Spec.PngModel.Bits], [Spec.PngModel.Huff], [Spec.PngModel.DeflateSpec]
    and Stdlib.

    WHY THIS FILE EXISTS.  [DeflateSpec.v] freezes the declarative DEFLATE
    DECODER — [decode_lit_len] (:327) reads one [Huff.lz_sym] off a
    [list bool] and [decode_symbols] (:430) reads a block's symbol
    sequence.  It has no inverse partner: nothing in the tree emits a
    symbol.  Two of its own comments were written anticipating one and name
    it — ":316 Used by the encoder half to discharge [LzRef]'s [dist <> 0]
    side condition", ":1434 NON-VACUITY, and the form the encoder half
    consumes".  This is the encoder half.

    LAYERING, hard, inherited from [DeflateSpec.v] and [Huff.v] and stated
    here because this file is where a shortcut would be tempting.  The
    OPERATIONAL emitter — [Trees.v]'s [cb_step]/[send_code] over
    [ZBitsOut.v]'s [BW] register machine — is NOT mentioned, imported or
    depended on here.  The refinement between this declarative surface and
    that transcription is a separate bridge module (compare
    [Spec.PngModel.ZBitsBridge], which does exactly that for the bit
    READER).  Consequence worth stating: nothing in this file is evidence
    about the binary.  It is evidence about RFC 1951.

    THE INDEX-PARAMETRIC CHOICE, and it is the design decision of the file.
    A length code is not determined by the length: RFC 1951 §3.2.5 assigns
    code 284 the range 227..257 with 5 extra bits, and 258 gets its own
    code 285 — but 227 + 31 = 258, so the value 258 is representable BOTH
    ways.  [DeflateSpec.v:1354-1360] pins that anomaly deliberately
    ([length_table_284_anomaly]).  zlib's [_length_code] table picks 285;
    a naive first-match selector picks 284; both decode back to 258.  So
    [emit_sym] takes the length and distance CODE INDICES as arguments
    instead of computing them, and the inverse theorem holds for EVERY
    in-range choice.  Three things follow:
      - the theorem is agnostic to zlib's table, so the transcription
        bridge can instantiate it at zlib's actual choice without this
        file having to reproduce [_length_code];
      - it is agnostic to the match FINDER, which is what layer L-D needs
        ("any in-range (len,dist) round-trips per-symbol");
      - the anomaly cannot become a soundness bug here, because no lemma
        below claims the index is unique.
    What this file therefore does NOT prove: that every length in 3..258
    HAS a code (totality of selection).  That is a different statement, it
    belongs with whoever picks indices, and asserting it here without a
    lemma would be exactly the kind of unearned totality claim the register
    keeps catching.  [emit_len_total_witness] below is a WITNESS, not that
    theorem, and says so.

    BIT ORIENTATION.  Settled against the reference binary before this
    file was written, because it is the classic DEFLATE defect.
    [compress_block] is a real (non-inlined) function at 0x418a8 in
    /harness/reference_binary (md5 ); its
    literal arm at 0x4193c-0x419a4 open-codes zlib's [send_bits], and
    0x41948's [bge t1,a5] branches AWAY when 16-len >= bi_valid, so the
    flush condition is exactly [ZBitsOut.v:57]'s
    [Z.ltb (Buf_size - length) (bw_valid b)].  The two [sh] stores at
    0x41954/0x419a0 are 16-bit — the [ush] truncation.  The low byte
    leaves first (0x41964, then 0x41984 after [srli 8]).  Net:
      - the bit STREAM is LSB-first per byte ([Bits.byte_bits]), and one
        [send_bits (v,n)] occupies the next [n] stream positions as
        [Bits.write_bits n v].  EXTRA BITS are emitted that way, so
        [emit_extra] below is a [write_bits] and its inverse is
        [Bits.read_bits_write_bits].
      - 0x41998 is [sraw], an ARITHMETIC shift, where the model needs a
        logical one ([code >> (Buf_size - bi_valid)]).  It is faithful only
        because [t3] was loaded by [lhu] and is therefore zero-extended
        below 2^16.  The generalisable check, since this is the second site
        in this campaign where a signed shift instruction stands in for an
        unsigned one: VERIFY A SHIFT'S SIGNEDNESS AGAINST THE OPERAND'S
        PROVENANCE, not against the source's [/] or [>>] — it is invisible
        from the C and cheap at the binary.  (Confirmed by filter-id's
        independent audit, which also notes the compiler HOISTED the shared
        [bi_buf |= val << bi_valid] up to 0x41944, above the branch, which
        is why the region reads as one block rather than two arms.)
      - a HUFFMAN CODEWORD reads MSB-first in the stream
        ([Huff.code_bits]) only because zlib stores codes ALREADY
        BIT-REVERSED ([bi_reverse] in [gen_codes]).  So [emit_sym] emits
        [Huff.code_for] DIRECTLY and the reversal is NOT this file's
        business: it is an obligation of the transcription bridge, in the
        form [write_bits (t_len t s) (t_code t s) = code_for lengths 15 s],
        supplied by the L-B lane where [gen_codes] lives.
    [emit_lit_is_msb_first] at the bottom pins the orientation as a VALUE
    rather than leaving it to this comment.

    WHAT IS ASSUMED FROM L-B, and it is one thing: [ValidLengths ll 15]
    and [ValidLengths dl 15], the premise [Huff.hdecode_code_for] (:842)
    needs.  Those are PREMISES of every theorem here, not axioms, and they
    are satisfiable — [DeflateSpec.v:1436-1440] discharges both for the
    fixed trees by computation, and the pins at the bottom of this file
    run the theorems at that instance so nothing here is vacuous. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Bits Huff DeflateSpec.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** ** 1. Extra-bit fields

    The exact inverse of [DeflateSpec.read_extra] (:293).  That reads [e]
    bits LSB-first and ADDS the table base; this writes [v - base] in [e]
    bits, and refuses when [v] is not in the code's range.  The refusal is
    the whole content: it is what makes the inverse unconditional
    downstream. *)

Definition emit_extra (base_tbl extra_tbl : list nat) (idx v : nat)
  : option (list bool) :=
  match nth_error base_tbl idx, nth_error extra_tbl idx with
  | Some b, Some e =>
      if andb (Nat.leb b v) (Nat.ltb (v - b)%nat (2 ^ e)%nat)
      then Some (write_bits e (Z.of_nat (v - b)%nat))
      else None
  | _, _ => None
  end.

Lemma emit_extra_read : forall bt et idx v bs suffix,
  emit_extra bt et idx v = Some bs ->
  read_extra bt et idx (bs ++ suffix) = Some (v, suffix).
Proof.
  intros bt et idx v bs suffix H.
  unfold emit_extra in H. unfold read_extra.
  destruct (nth_error bt idx) as [b|] eqn:Eb; [|discriminate].
  destruct (nth_error et idx) as [e|] eqn:Ee; [|discriminate].
  destruct (andb (Nat.leb b v) (Nat.ltb (v - b)%nat (2 ^ e)%nat)) eqn:Eg;
    [|discriminate].
  apply andb_prop in Eg as [Hle Hlt].
  apply Nat.leb_le in Hle. apply Nat.ltb_lt in Hlt.
  inversion H; subst bs.
  rewrite read_bits_write_bits.
  - f_equal. f_equal. lia.
  - split; [lia|].
    rewrite two_pow_nat. apply Nat2Z.inj_lt. exact Hlt.
Qed.

(** The emitted field is exactly [e] bits wide.  Cited by the bridge, which
    has to know how much of the stream one field owns. *)
Lemma emit_extra_length : forall bt et idx v bs e,
  nth_error et idx = Some e ->
  emit_extra bt et idx v = Some bs ->
  length bs = e.
Proof.
  intros bt et idx v bs e He H. unfold emit_extra in H.
  destruct (nth_error bt idx) as [b|]; [|discriminate].
  rewrite He in H.
  destruct (andb _ _); [|discriminate].
  inversion H. apply write_bits_length.
Qed.

(** ** 2. One symbol

    [emit_sym ll dl li di s] is the bit string for symbol [s] under the two
    code-length vectors, with [li] the length code's index (code [257 + li])
    and [di] the distance code.  [li]/[di] are ignored for literals and end
    of block.  Every failure is a refusal to emit something the decoder
    could not read back: an out-of-range literal byte, a symbol with no
    codeword under [ll]/[dl], or a length/distance outside the named code's
    range. *)

Definition emit_sym (ll dl : list nat) (li di : nat) (s : lz_sym)
  : option (list bool) :=
  match s with
  | LzLit b =>
      if andb (0 <=? b) (b <? 256) then code_for ll 15%nat (Z.to_nat b) else None
  | LzEnd => code_for ll 15%nat 256%nat
  | LzRef len dist =>
      match code_for ll 15%nat (257 + li)%nat with
      | None => None
      | Some cw =>
          match emit_extra length_base length_extra li len with
          | None => None
          | Some ex =>
              match code_for dl 15%nat di with
              | None => None
              | Some dw =>
                  match emit_extra dist_base dist_extra di dist with
                  | None => None
                  | Some dx => Some (cw ++ ex ++ dw ++ dx)
                  end
              end
          end
      end
  end.

(** "Some legal emission of [s] exists" — the form the sequence theorem and
    the transcription bridge quantify over, so neither has to carry index
    arguments it does not use. *)
Definition EmitsTo (ll dl : list nat) (s : lz_sym) (bs : list bool) : Prop :=
  exists li di, emit_sym ll dl li di s = Some bs.

(** ** 3. THE PER-SYMBOL INVERSE

    Decode-of-encode, with the emitted string in front of an ARBITRARY
    suffix and the suffix returned untouched: that is the composable form,
    and it is what makes the sequence fold in section 4 a plain induction
    rather than a stream-invariant argument. *)

Theorem emit_decode_id : forall ll dl li di s bs suffix,
  ValidLengths ll 15%nat -> ValidLengths dl 15%nat ->
  emit_sym ll dl li di s = Some bs ->
  decode_lit_len ll dl (bs ++ suffix) = Some (s, suffix).
Proof.
  intros ll dl li di s bs suffix Hll Hdl H.
  destruct s as [b | len dist | ].
  - (* literal *)
    cbn [emit_sym] in H.
    destruct (andb (0 <=? b) (b <? 256)) eqn:Eg; [|discriminate].
    apply andb_prop in Eg as [Hlo Hhi].
    apply Z.leb_le in Hlo. apply Z.ltb_lt in Hhi.
    unfold decode_lit_len.
    rewrite (hdecode_code_for ll 15%nat (Z.to_nat b) bs suffix Hll H).
    replace (Nat.ltb (Z.to_nat b) 256) with true
      by (symmetry; apply Nat.ltb_lt; lia).
    rewrite Z2Nat.id by lia. reflexivity.
  - (* length/distance pair *)
    cbn [emit_sym] in H.
    destruct (code_for ll 15%nat (257 + li)%nat) as [cw|] eqn:Ec; [|discriminate].
    destruct (emit_extra length_base length_extra li len) as [ex|] eqn:Ee;
      [|discriminate].
    destruct (code_for dl 15%nat di) as [dw|] eqn:Ed; [|discriminate].
    destruct (emit_extra dist_base dist_extra di dist) as [dx|] eqn:Ex;
      [|discriminate].
    inversion H; subst bs.
    unfold decode_lit_len.
    rewrite <- !app_assoc.
    rewrite (hdecode_code_for ll 15%nat (257 + li)%nat cw
                              (ex ++ dw ++ dx ++ suffix) Hll Ec).
    replace (Nat.ltb (257 + li)%nat 256) with false
      by (symmetry; apply Nat.ltb_ge; lia).
    replace (Nat.eqb (257 + li)%nat 256) with false
      by (symmetry; apply Nat.eqb_neq; lia).
    replace ((257 + li) - 257)%nat with li by lia.
    rewrite (emit_extra_read length_base length_extra li len ex
                             (dw ++ dx ++ suffix) Ee).
    rewrite (hdecode_code_for dl 15%nat di dw (dx ++ suffix) Hdl Ed).
    rewrite (emit_extra_read dist_base dist_extra di dist dx suffix Ex).
    reflexivity.
  - (* end of block *)
    cbn [emit_sym] in H.
    unfold decode_lit_len.
    rewrite (hdecode_code_for ll 15%nat 256%nat bs suffix Hll H).
    reflexivity.
Qed.

Corollary EmitsTo_decode : forall ll dl s bs suffix,
  ValidLengths ll 15%nat -> ValidLengths dl 15%nat ->
  EmitsTo ll dl s bs ->
  decode_lit_len ll dl (bs ++ suffix) = Some (s, suffix).
Proof.
  intros ll dl s bs suffix Hll Hdl [li [di He]].
  exact (emit_decode_id ll dl li di s bs suffix Hll Hdl He).
Qed.

(** ** 4. A SYMBOL SEQUENCE

    [decode_symbols] stops at the FIRST end-of-block and returns it as the
    last element.  So the composable statement is over a BODY of non-end
    symbols plus a separately-emitted end marker, and the
    "no interior [LzEnd]" premise is load bearing rather than decoration —
    [interior_end_witness] in section 6 exhibits a body it kills, as a
    value. *)

Theorem emit_decode_seq : forall ll dl body bss bend suffix,
  ValidLengths ll 15%nat -> ValidLengths dl 15%nat ->
  Forall2 (EmitsTo ll dl) body bss ->
  Forall (fun s => lz_is_end s = false) body ->
  EmitsTo ll dl LzEnd bend ->
  decode_symbols ll dl (concat bss ++ bend ++ suffix)
    = Some (body ++ [LzEnd], suffix).
Proof.
  intros ll dl body. induction body as [|s body IH];
    intros bss bend suffix Hll Hdl H2 Hnb Hend.
  - inversion H2; subst bss. cbn [concat app].
    rewrite decode_symbols_unfold.
    rewrite (EmitsTo_decode ll dl LzEnd bend suffix Hll Hdl Hend).
    reflexivity.
  - inversion H2 as [|s0 bs body0 bss0 Hs Hrest Es Ebss]; subst s0 body0.
    subst bss.
    inversion Hnb as [|s1 body1 Hhead Htail]; subst s1 body1.
    cbn [concat]. rewrite <- app_assoc.
    rewrite decode_symbols_unfold.
    rewrite (EmitsTo_decode ll dl s bs (concat bss0 ++ bend ++ suffix)
                            Hll Hdl Hs).
    rewrite Hhead.
    rewrite (IH bss0 bend suffix Hll Hdl Hrest Htail Hend).
    reflexivity.
Qed.

(** ** 5. What the sequence resolves to

    The point of the layer, stated: a body of literals and in-range
    references round-trips THROUGH the bit stream, so the LZ77 resolution
    the decoder performs is the resolution of the symbols the encoder
    chose.  [Huff.resolve_lz] is applied to the decoded list; this says it
    is applied to the emitted one. *)

Corollary emit_decode_resolves : forall ll dl body bss bend suffix acc out,
  ValidLengths ll 15%nat -> ValidLengths dl 15%nat ->
  Forall2 (EmitsTo ll dl) body bss ->
  Forall (fun s => lz_is_end s = false) body ->
  EmitsTo ll dl LzEnd bend ->
  resolve_lz body acc = Some out ->
  exists syms rem,
    decode_symbols ll dl (concat bss ++ bend ++ suffix) = Some (syms, rem)
    /\ resolve_lz syms acc = Some out
    /\ rem = suffix.
Proof.
  intros ll dl body bss bend suffix acc out Hll Hdl H2 Hnb Hend Hres.
  exists (body ++ [LzEnd]), suffix.
  split; [exact (emit_decode_seq ll dl body bss bend suffix Hll Hdl H2 Hnb Hend)|].
  split; [|reflexivity].
  clear H2 Hend. revert acc out Hres Hnb.
  induction body as [|s body IH]; intros acc out Hres Hnb.
  - cbn [app]. cbn [resolve_lz] in Hres |- *. inversion Hres; reflexivity.
  - inversion Hnb as [|s1 body1 Hhead Htail]; subst s1 body1.
    destruct s as [b | len dist | ]; [| |discriminate].
    + cbn [app resolve_lz] in *. apply IH; assumption.
    + cbn [app resolve_lz] in *.
      destruct (orb (Nat.eqb dist 0) (Nat.ltb (length acc) dist));
        [discriminate|].
      apply IH; assumption.
Qed.

(** ** 6. Computational pins

    Each says what wrong implementation it catches.  A pin that only
    restated a definition would catch nothing and is not written.  The
    instance throughout is the RFC 1951 §3.2.6 FIXED pair, because
    [DeflateSpec.v:1436-1440] discharges [ValidLengths] for it by
    computation, so the theorems above can actually be RUN here and this
    file's premises are demonstrably satisfiable rather than merely
    quantified over. *)

Definition ll0 : list nat := fixed_lit_lengths.
Definition dl0 : list nat := fixed_dist_lengths.

(** *** 6.1 The simplest end-to-end instance: one literal

    Catches a wrong codeword orientation, a wrong [maxBits], and an
    off-by-one in the [sym < 256] test at the boundary.  Both endpoints of
    the literal range are checked, and 256 (end of block) is checked to
    land on [LzEnd] and NOT on [LzLit 256]. *)

Example emit_lit_0_roundtrip :
  match emit_sym ll0 dl0 0%nat 0%nat (LzLit 0) with
  | Some bs => decode_lit_len ll0 dl0 (bs ++ [true; false])
               = Some (LzLit 0, [true; false])
  | None => False
  end.
Proof. vm_compute. reflexivity. Qed.

Example emit_lit_255_roundtrip :
  match emit_sym ll0 dl0 0%nat 0%nat (LzLit 255) with
  | Some bs => decode_lit_len ll0 dl0 (bs ++ [true; false])
               = Some (LzLit 255, [true; false])
  | None => False
  end.
Proof. vm_compute. reflexivity. Qed.

Example emit_end_roundtrip :
  match emit_sym ll0 dl0 0%nat 0%nat LzEnd with
  | Some bs => decode_lit_len ll0 dl0 (bs ++ [true]) = Some (LzEnd, [true])
  | None => False
  end.
Proof. vm_compute. reflexivity. Qed.

(** A literal byte outside 0..255 is REFUSED, not silently truncated.  This
    is the pin for [emit_sym]'s literal guard: dropping it would emit
    [code_for ll 15 (Z.to_nat b)], which for [b = 256] is the END-OF-BLOCK
    codeword — an encoder that terminated the block on a literal. *)
Example emit_lit_256_refused : emit_sym ll0 dl0 0%nat 0%nat (LzLit 256) = None.
Proof. vm_compute. reflexivity. Qed.

Example emit_lit_neg_refused : emit_sym ll0 dl0 0%nat 0%nat (LzLit (-1)) = None.
Proof. vm_compute. reflexivity. Qed.

(** *** 6.2 Orientation, as a value

    The header claims codewords go out MSB-first while extra bits go out
    LSB-first.  191 = is not a palindrome, so the two orders are
    distinguishable, and [DeflateSpec.v:1391-1398] independently pins
    [code_for fixed_lit_lengths 15 143 = Some (code_bits 191 8)] against
    RFC 1951's own printed code values.  A file that emitted [write_bits]
    for the codeword would pass every length and range check above and fail
    this one. *)
Example emit_lit_is_msb_first :
  emit_sym ll0 dl0 0%nat 0%nat (LzLit 143) = Some (code_bits 191 8%nat)
  /\ code_bits 191 8%nat <> write_bits 8%nat 191.
Proof.
  split; [vm_compute; reflexivity|].
  vm_compute. intro H. discriminate H.
Qed.

(** *** 6.3 A reference with BOTH extra-bit fields non-empty

    Length 140 sits in length code 281 ([li = 24], base 131, 5 extra bits)
    and distance 1000 in distance code 19 (base 769, 8 extra bits), so this
    exercises the full four-field emission and catches a base/extra
    mismatch, a swapped length/distance table, and an extra field written
    in the wrong bit order. *)
Example emit_ref_roundtrip :
  match emit_sym ll0 dl0 24%nat 19%nat (LzRef 140 1000) with
  | Some bs => decode_lit_len ll0 dl0 (bs ++ [false; true])
               = Some (LzRef 140 1000, [false; true])
  | None => False
  end.
Proof. vm_compute. reflexivity. Qed.

(** Out of the named code's range: REFUSED.  200 is not in code 281's
    131..162, and the refusal is what makes [emit_decode_id] unconditional
    — an emitter that clamped or wrapped here would decode back to a
    DIFFERENT length, which is precisely the round-trip failure the whole
    layer exists to exclude. *)
Example emit_ref_len_out_of_range :
  emit_sym ll0 dl0 24%nat 19%nat (LzRef 200 1000) = None.
Proof. vm_compute. reflexivity. Qed.

Example emit_ref_dist_out_of_range :
  emit_sym ll0 dl0 24%nat 19%nat (LzRef 140 2000) = None.
Proof. vm_compute. reflexivity. Qed.

(** Distance codes 30 and 31 have no [dist_base] entry, so they cannot be
    emitted — the encoder-side counterpart of
    [DeflateSpec.fixed_dist_code_30_rejected]. *)
Example emit_dist_code_30_refused :
  emit_sym ll0 dl0 24%nat 30%nat (LzRef 140 1000) = None.
Proof. vm_compute. reflexivity. Qed.

(** *** 6.4 RFC 1951's table anomaly, and why the statement is index-parametric

    Length 258 is representable TWO ways: code 284 ([li = 27], base 227 with
    5 extra bits, so 227..258) and code 285 ([li = 28], base 258 with none).
    zlib's [_length_code] picks 285.  The two emissions DIFFER as bit
    strings and BOTH decode back to 258.  That is the whole justification
    for making the index an argument rather than computing it here: a
    file that hard-coded either choice would be wrong about the other, and
    the transcription bridge needs zlib's. *)
Example emit_258_two_ways :
  match emit_sym ll0 dl0 27%nat 0%nat (LzRef 258 1),
        emit_sym ll0 dl0 28%nat 0%nat (LzRef 258 1) with
  | Some b27, Some b28 =>
      b27 <> b28
      /\ decode_lit_len ll0 dl0 b27 = Some (LzRef 258 1, [])
      /\ decode_lit_len ll0 dl0 b28 = Some (LzRef 258 1, [])
  | _, _ => False
  end.
Proof.
  vm_compute.
  split; [intro H; discriminate H|].
  split; reflexivity.
Qed.

(** *** 6.5 THE NECESSITY WITNESS for "no interior end-of-block"

    Exhibited as a VALUE, per the fleet register: the premise's necessity is
    shown by computing what actually happens without it, not by asserting
    that the proof needs it.  [decode_symbols] stops at the FIRST [LzEnd],
    so for the body [[LzEnd; LzLit 65]] it returns a ONE-element list with
    the second symbol's bits left in the remainder — so
    [emit_decode_seq]'s conclusion is FALSE for that body, and dropping the
    [Forall] premise would make the theorem unsound rather than merely
    weaker. *)

Example interior_end_witness :
  match emit_sym ll0 dl0 0%nat 0%nat LzEnd, emit_sym ll0 dl0 0%nat 0%nat (LzLit 65) with
  | Some be, Some ba =>
      decode_symbols ll0 dl0 (be ++ ba ++ be) = Some ([LzEnd], ba ++ be)
  | _, _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

Example interior_end_witness_refutes_conclusion :
  match emit_sym ll0 dl0 0%nat 0%nat LzEnd, emit_sym ll0 dl0 0%nat 0%nat (LzLit 65) with
  | Some be, Some ba =>
      decode_symbols ll0 dl0 (be ++ ba ++ be)
        <> Some ([LzEnd; LzLit 65] ++ [LzEnd], @nil bool)
  | _, _ => False
  end.
Proof. vm_compute. intro H. discriminate H. Qed.

(** *** 6.6 NON-VACUITY: the sequence theorem, RUN

    Not a computation — an application of [emit_decode_seq] at the fixed
    trees, with [ValidLengths] discharged by [DeflateSpec]'s own lemmas.
    If any premise of the theorem were unsatisfiable this would not
    typecheck. *)

Example seq_at_fixed_trees : forall be ba suffix,
  emit_sym ll0 dl0 0%nat 0%nat LzEnd = Some be ->
  emit_sym ll0 dl0 24%nat 19%nat (LzRef 140 1000) = Some ba ->
  decode_symbols ll0 dl0 (ba ++ be ++ suffix)
    = Some ([LzRef 140 1000] ++ [LzEnd], suffix).
Proof.
  intros be ba suffix He Ha.
  replace (ba ++ be ++ suffix) with (concat [ba] ++ be ++ suffix)
    by (cbn [concat]; rewrite app_nil_r; reflexivity).
  apply emit_decode_seq.
  - exact fixed_lit_valid.
  - exact fixed_dist_valid.
  - constructor; [exists 24%nat, 19%nat; exact Ha | constructor].
  - constructor; [reflexivity | constructor].
  - exists 0%nat, 0%nat; exact He.
Qed.

(** *** 6.7 Coverage WITNESSES for index selection — witnesses, not theorems

    The header says this file does not prove that every length has a code.
    These are the honest weaker artefacts: a bounded search finds an index
    for every match length 3..258, and for both ENDPOINTS of every distance
    code's range.  They are what a selector's totality proof would have to
    beat, and they are labelled witnesses so nobody cites them as one.
    (The distance side is endpoint coverage, not the full 1..32768: the
    unary [nat] arithmetic makes the full sweep expensive and the endpoints
    are the structural check — a wrong base or extra width moves an
    endpoint.) *)

Definition some_index (base_tbl extra_tbl : list nat) (n v : nat) : option nat :=
  find (fun i => match emit_extra base_tbl extra_tbl i v with
                 | Some _ => true | None => false end)
       (seq 0 n).

Example emit_len_total_witness :
  forallb (fun v => match some_index length_base length_extra 29%nat v with
                    | Some _ => true | None => false end)
          (seq 3 256) = true.
Proof. vm_compute. reflexivity. Qed.

Definition dist_endpoints : list nat :=
  flat_map (fun i => match nth_error dist_base i, nth_error dist_extra i with
                     | Some b, Some e => [b; (b + 2 ^ e - 1)%nat]
                     | _, _ => []
                     end)
           (seq 0 30).

Example emit_dist_endpoints_witness :
  forallb (fun v => match some_index dist_base dist_extra 30%nat v with
                    | Some _ => true | None => false end)
          dist_endpoints = true.
Proof. vm_compute. reflexivity. Qed.

(** And the negative that makes the two above informative: 2 is NOT a match
    length (RFC 1951's shortest match is 3) and 0 is not a distance, so the
    search must FAIL on them.  Without this, a [some_index] that returned
    [Some 0] unconditionally would pass both witnesses. *)
Example emit_len_2_has_no_code :
  some_index length_base length_extra 29%nat 2%nat = None.
Proof. vm_compute. reflexivity. Qed.

Example emit_dist_0_has_no_code :
  some_index dist_base dist_extra 30%nat 0%nat = None.
Proof. vm_compute. reflexivity. Qed.
