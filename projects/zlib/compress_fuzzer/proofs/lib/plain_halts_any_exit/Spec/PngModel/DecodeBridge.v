(** * Spec.PngModel.DecodeBridge — zlib's two-level decode table vs the
      declarative Huffman decoder.

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT.

    A BRIDGE, so unlike the files it joins it is allowed — and required —
    to import both sides.  [Inflate.v] is the bug-for-bug transcription of
    [inflate.c] and must not know about the declarative spec; [Huff.v] /
    [Bits.v] / [DeflateSpec.v] are L0's frozen surface and must not know
    about the transcription.  Same layering call as [ZBitsBridge.v] (the
    bit reader) and [InftreesBridge.v] (the Kraft counter), and this file
    is the third and last of that family: it joins the DECODE STEP.

    ** WHAT IS RELATED, AND WHY THE BIT COUNT IS PART OF IT

    The transcription's decode step is

<<
      Definition inf_decode (sub : Code -> bool) (t : ztbl) (rootbits : Z)
                            (b : BR) : Dec
>>

    called at exactly two sites — [inf_LEN]'s
    [[inf_decode sub_len (tbl_of st (t_lencode tb)) (t_lenbits tb) b]] and
    [inf_DIST]'s
    [[inf_decode sub_dist (tbl_of st (t_distcode tb)) (t_distbits tb) (q_br q)]]
    — plus [cl_step], which uses the root fetch [inf_fetch] alone.  Those
    are the only two uses of [inf_fetch] in [Inflate.v]; the
    [inflate_fast] path walks the same tables with its own code
    ([InflateFast.if_dolen] / [if_dodist]) and is NOT covered by anything
    here.  [inf_decode]'s success constructor [DecOk h b' nb] carries
    THREE things: the table entry [h], the advanced reader [b'], and the
    number of bits consumed [nb].  The declarative side is
    [Huff.hdecode (code_table l maxBits)], returning [Some (sym, rem)].

    The equation below relates all three, not just the symbol:

      - [h] is pinned to [ent sym], the entry the canonical assignment
        predicts for that symbol (see [TableAgreesAt] for what [ent] is);
      - [nb] is pinned to [Z.of_nat (length cw)], the codeword's length,
        equivalently [length (br_stream b) - length rem];
      - [br_stream b'] is pinned to [rem].

    THE BIT COUNT IS NOT DECORATION.  The consumer's termination measure
    is a bit budget, so a decode that returns the right symbol having
    consumed ZERO bits is the failure mode that a symbol-only equation
    cannot rule out — and it is reachable: [pointer_zero_bits_no_progress]
    exhibits a table satisfying the hypothesis of the main theorem on
    which [inf_decode] returns [DecOk _ _ 0] and leaves [br_stream]
    unchanged ([pointer_no_progress_stream]).  What excludes it on the
    codeword path is [inf_decode_progress]: [nb = length cw > 0], with the
    positivity coming from [DeflateSpec.hdecode_code_table_shorter], which
    has no hypotheses.

    ** THE FACTORING: [TableAgreesAt] IS A HYPOTHESIS HERE

    "The built table agrees with the canonical assignment" is the
    table-builder lane's result and is not proved here; it is stated as
    [TableAgreesAt] / [TableAgrees] and assumed, exactly as
    [InftreesBridge] stated [CountsOf] before discharging it in its §8.

    THE SHAPE IS CHOSEN FOR THAT LANE'S OUTPUT.  [Inftrees.it_model] hands
    back an [o] carrying the built table [o_tbl o] and the root width it
    settled on [o_bits o] (see [Inflate.fixedtables_shape] and
    [Inflate.distfix_is_inflate_table] for the two calls the fixed tables
    would make), and [InftreesBridge] already relates that lane's [zarr]
    of lengths to a [list nat] through [Inftrees.zlens].  So the obligation
    to aim at is

<<
      it_model ty (zlens l) (Z.of_nat (length l)) root0 tnone = Some o ->
      TableAgrees (o_tbl o) (o_bits o) l 15 ent
>>

    for a suitable [ent], and nothing here needs to change when it lands.

    [TableAgreesAt t rootbits l maxBits ent sym] says, for the ONE symbol
    [sym] and only when its canonical codeword fits in the root table:

      - the entry's width field is the codeword's length
        ([c_bits (ent sym) = Z.of_nat (length cw)]), and
      - EVERY root index whose low [length cw] bits, READ LSB-FIRST, spell
        the codeword holds that entry
        ([write_bits (length cw) i = cw -> t i = ent sym]).

    Four deliberate choices, each one weakening the obligation:

      1. IT IS POINTWISE IN THE SYMBOL.  The main theorem consumes only
         the symbol it decodes.  [TableAgrees] is the [forall sym] bundle
         for callers who have it uniformly.
      2. IT IS ONE-DIRECTIONAL: index -> entry, never entry -> index.  It
         says NOTHING about an index no codeword covers, which is where
         sub-table pointers and the invalid-code fillers of an incomplete
         code live.  The other direction — "the entry here is a codeword's"
         — is what a converse would need, and [converse_fails] shows what
         goes wrong without it.
      3. IT IS CONDITIONAL ON [Z.of_nat (length cw) <= rootbits].  A
         symbol needing more bits than the root width is reached through a
         sub-table, and that is the other lane's path (below).
      4. THE ENTRY IS ABSTRACT ([ent : nat -> Code]).  [c_val] is NOT the
         symbol in general — in a length or distance table it is the
         BASE length/distance ([lenfix_val_is_not_the_symbol] exhibits
         [c_val = 258] for symbol 285 in zlib's own fixed table).  Callers
         for whom it is the symbol — the code-length tree, and literals —
         say so with [ValEntries] and get [inf_decode_val].

    THE INDEX CONDITION IS A BIT REVERSAL — a table index is the MIRROR of
    the codeword, which is why [inftrees.c] carries the mirrored counter
    [huff].  That claim about the builder is not proved here; what is
    proved is that the convention is the right one for the table zlib
    ships ([lenfix_agrees_at_0]) and that the un-mirrored one is refuted by
    it ([lenfix_reversal_is_load_bearing]).  It is stated LSB-first because
    [write_bits] is the reader's order; [write_bits_index_code_bits] is the
    same condition in [Huff]'s MSB-first order
    ([code_bits i (length cw) = rev cw]).

    ** WHICH PATH THIS FILE COVERS

    THE CODEWORD PATH, and only that.  Concretely, the main theorem's
    hypotheses cut out three cases, each named:

      - [NotAPointer] ([sub (ent sym) = false]): the guard
        [[here.op && (here.op & 0xf0) == 0]] ([inflate.c:1041]) /
        [[(here.op & 0xf0) == 0]] ([:1090]) must classify the entry as a
        real code, not a sub-table pointer.  If it does not, [inf_decode]
        recurses through [inf_fetch2] into the second level, and NOTHING
        here applies.  That path — including the fact that a pointer's
        width is positive, without which the two-level walk can consume
        zero bits — belongs to the table-builder lane
        ([Inftrees.it_pre_root_pos] and the pointer-width positivity
        downstream of it).  [sub_len_false_of_op] / [sub_dist_false_of_op]
        discharge the hypothesis from the entry's [c_op] alone, and
        [lenfix_has_no_subtables] / [distfix_has_no_subtables] discharge
        it outright for zlib's fixed tables.
      - [CodeFitsRoot] ([Z.of_nat (length cw) <= rootbits]): the symbol is
        in the root table.  Same exclusion, from the other side.
      - [Buffered] ([Z.of_nat (length cw) <= br_bits b]): the reader
        already holds the codeword's bits, so the fetch loop stops on its
        first trip ([inf_fetch_hit]).  When it does not hold, the loop
        pulls bytes and the index it reads changes under it; a decode is
        still selected, but showing THAT one is right needs a fact about
        canonical codes that is not proved here (that the zero-extension
        of any decodable prefix is itself covered by a codeword).  NOT
        claimed either way in this file.  What IS proved is the other half
        of that story, and it is the reusable one: pulling is invisible at
        the stream level, so a future discharge of [Buffered] inherits
        both the stream and [br_wf] unchanged ([inf_fetch_stream], on top
        of [br_wf_pullbyte] and [ZBitsBridge.br_stream_pullbyte]).

    ** WHAT IS NOT TRUE

    THE EQUATION DOES NOT REVERSE.  [converse_fails] exhibits a table
    satisfying [TableAgrees] on which [inf_decode] returns [DecOk] while
    [hdecode] returns [None]: the reader is sitting on a bit that no
    codeword of that (one-symbol, incomplete) code matches, and the entry
    there is the invalid-code filler.  [Inflate.inf_LEN]'s
    [Z.land (c_op h) 64] arm ([inflate.c:1065]) is where the machine then
    rejects it; the SPEC never had an answer to compare with.  So "machine
    decodes ==> spec decodes" is false, and this file states only the
    direction that holds.

    THE TABLE CONDITION IS NOT VACUOUS AND DOES NOT PIN THE WHOLE TABLE.
    [TableAgreesAt] holds of zlib's real fixed tables at real symbols
    ([lenfix_agrees_at_0], [distfix_agrees_at_0] — quantified over ALL root
    indices, with the index condition doing the narrowing), and the full
    [TableAgrees] holds of both adversarial tables of §6, which agree at
    every index a codeword covers and differ at one where none does
    ([agrees_does_not_pin_table]).  That is the interface being weak on
    purpose, and it is why the pointer and filler cases must be excluded
    by hypothesis rather than by the table condition.

    ** DISCIPLINE

    Every claim any comment here makes is a lemma below it; where a fact
    is merely NOT proved, the comment says so rather than asserting it.
    Every [reflexivity]/[vm_compute] test is here because a plausible
    WRONG implementation or a wrong STATEMENT fails it, and the mutant is
    named. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff DeflateSpec ZBitsIn ZBitsBridge Inflate.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** ** 1.  Bit-order plumbing

    [write_bits] is LSB-first and sees its value only through its low [k]
    bits.  Three congruences and an injectivity; everything else in the
    file is stated over them. *)

Lemma write_bits_ext_low :
  forall (k : nat) (v w : Z),
    (forall j : nat, (j < k)%nat ->
       Z.testbit v (Z.of_nat j) = Z.testbit w (Z.of_nat j)) ->
    write_bits k v = write_bits k w.
Proof.
  intros k v w H. rewrite !write_bits_testbit.
  apply map_ext_in. intros i Hi. apply in_seq in Hi. apply H. lia.
Qed.

(** Reducing the value modulo any power of two AT OR ABOVE the width is
    invisible.  This is what lets the machine's [rootbits]-wide index
    stand in for the whole accumulator. *)
Lemma write_bits_mod_pow2 :
  forall (k : nat) (n v : Z),
    Z.of_nat k <= n -> write_bits k (v mod 2 ^ n) = write_bits k v.
Proof.
  intros k n v Hk. apply write_bits_ext_low. intros j Hj.
  apply Z.mod_pow2_bits_low. lia.
Qed.

(** A prefix of a write is a shorter write of the same value. *)
Lemma firstn_write_bits :
  forall (m k : nat) (v : Z),
    (k <= m)%nat -> firstn k (write_bits m v) = write_bits k v.
Proof.
  induction m as [|m IH]; intros k v Hk.
  - replace k with 0%nat by lia. reflexivity.
  - destruct k as [|k]; [reflexivity|].
    cbn [write_bits firstn]. f_equal. apply IH. lia.
Qed.

(** Two values with the same [k]-bit write agree modulo [2^k].  Proved
    through [Bits.read_bits_write_bits] rather than by bit surgery. *)
Lemma write_bits_inj_mod :
  forall (k : nat) (i j : Z),
    write_bits k i = write_bits k j ->
    i mod 2 ^ Z.of_nat k = j mod 2 ^ Z.of_nat k.
Proof.
  intros k i j H.
  assert (Hp : 0 < 2 ^ Z.of_nat k) by (apply Z.pow_pos_nonneg; lia).
  pose proof (Z.mod_pos_bound i (2 ^ Z.of_nat k) Hp) as Hi.
  pose proof (Z.mod_pos_bound j (2 ^ Z.of_nat k) Hp) as Hj.
  pose proof (read_bits_write_bits k (i mod 2 ^ Z.of_nat k) [] Hi) as Ri.
  pose proof (read_bits_write_bits k (j mod 2 ^ Z.of_nat k) [] Hj) as Rj.
  rewrite (write_bits_mod_pow2 k (Z.of_nat k) i) in Ri by lia.
  rewrite (write_bits_mod_pow2 k (Z.of_nat k) j) in Rj by lia.
  rewrite H, Rj in Ri. congruence.
Qed.

(** THE INDEX/CODEWORD DUALITY, as a lemma rather than as prose: "index
    [i]'s low bits spell [cw] LSB-first" and "[cw] reversed is the
    MSB-first codeword of [i]" are the same condition.  [Huff]'s codewords
    are MSB-first ([code_bits]); a table index is LSB-first; the bridge
    between the two orders is [Huff.code_bits_rev_write_bits] and nothing
    else. *)
Lemma write_bits_index_code_bits :
  forall (i : Z) (cw : list bool),
    write_bits (length cw) i = cw <-> code_bits i (length cw) = rev cw.
Proof.
  intros i cw. rewrite code_bits_rev_write_bits. split; intro H.
  - now rewrite H.
  - rewrite <- (rev_involutive (write_bits (length cw) i)), H.
    apply rev_involutive.
Qed.

(** ** 2.  The reader's index is the head of its stream

    [ZBitsBridge.br_stream] is the reader's abstract bit stream.  These
    two lemmas say that [BITS(n)] — the value [inf_fetch] indexes the
    table with — is exactly the stream's first bits, LSB-first. *)

Lemma br_bits_of_mod :
  forall (n : Z) (b : BR), 0 <= n -> br_bits_of n b = br_hold b mod 2 ^ n.
Proof.
  intros n b Hn. unfold br_bits_of.
  rewrite Z.shiftl_1_l.
  replace (2 ^ n - 1) with (Z.ones n) by (rewrite Z.ones_equiv; lia).
  apply Z.land_ones; lia.
Qed.

Lemma br_bits_of_in_range :
  forall (n : Z) (b : BR), 0 <= n -> 0 <= br_bits_of n b < 2 ^ n.
Proof.
  intros n b Hn. rewrite br_bits_of_mod by lia.
  apply Z.mod_pos_bound, Z.pow_pos_nonneg; lia.
Qed.

(** Narrowing the [BITS] width is invisible to a shorter write: the
    machine reads the table at the ROOT width, but only the codeword's own
    bits matter. *)
Lemma write_bits_br_bits_of :
  forall (k : nat) (n : Z) (b : BR),
    Z.of_nat k <= n ->
    write_bits k (br_bits_of n b) = write_bits k (br_hold b).
Proof.
  intros k n b Hk. rewrite br_bits_of_mod by lia.
  apply write_bits_mod_pow2; lia.
Qed.

(** The pending bits of [hold] ARE the head of the abstract stream. *)
Lemma br_stream_firstn :
  forall (n : Z) (b : BR),
    0 <= n <= br_bits b ->
    firstn (Z.to_nat n) (br_stream b) = write_bits (Z.to_nat n) (br_hold b).
Proof.
  intros n b [H0 H1]. unfold br_stream.
  rewrite firstn_app, write_bits_length.
  replace (Z.to_nat n - Z.to_nat (br_bits b))%nat with 0%nat by lia.
  cbn [firstn]. rewrite app_nil_r.
  apply firstn_write_bits. lia.
Qed.

(** THE STATEMENT §2 EXISTS FOR: the table index the machine computes at
    the root width spells the stream's first [n] bits, for every [n] the
    reader is holding and the root width covers. *)
Lemma br_index_spells_stream :
  forall (n rootbits : Z) (b : BR),
    0 <= n <= br_bits b -> n <= rootbits ->
    write_bits (Z.to_nat n) (br_bits_of rootbits b)
    = firstn (Z.to_nat n) (br_stream b).
Proof.
  intros n rootbits b Hn Hr.
  rewrite (write_bits_br_bits_of (Z.to_nat n) rootbits b) by lia.
  symmetry. apply br_stream_firstn. lia.
Qed.

(** ** 3.  The hypothesis: the built table agrees with the canonical code

    THIS IS NOT PROVED HERE.  It is the table-builder lane's obligation,
    stated in the shape this file's proofs actually consume — see the
    header for the four ways it is deliberately weak.  Read it as: "at
    every root index that the canonical codeword of [sym] covers, the
    table holds [sym]'s entry, and that entry advertises the codeword's
    length". *)

Definition TableAgreesAt (t : ztbl) (rootbits : Z) (l : list nat)
                         (maxBits : nat) (ent : nat -> Code) (sym : nat) : Prop :=
  forall cw : list bool,
    code_for l maxBits sym = Some cw ->
    Z.of_nat (length cw) <= rootbits ->
    c_bits (ent sym) = Z.of_nat (length cw)
    /\ (forall i : Z,
          0 <= i < 2 ^ rootbits ->
          write_bits (length cw) i = cw ->
          t i = ent sym).

Definition TableAgrees (t : ztbl) (rootbits : Z) (l : list nat)
                       (maxBits : nat) (ent : nat -> Code) : Prop :=
  forall sym : nat, TableAgreesAt t rootbits l maxBits ent sym.

Lemma TableAgrees_at :
  forall t rootbits l maxBits ent sym,
    TableAgrees t rootbits l maxBits ent ->
    TableAgreesAt t rootbits l maxBits ent sym.
Proof. intros t rootbits l maxBits ent sym H. apply H. Qed.

(** The optional extra a caller may have: the entry's [c_val] really is
    the symbol.  True for the code-length tree ([inftrees.c]'s [CODES]
    arm, where [here.val = work[sym]]) and for literals; FALSE for length
    and distance codes ([lenfix_val_is_not_the_symbol]). *)
Definition ValEntries (l : list nat) (ent : nat -> Code) : Prop :=
  forall sym : nat, (sym < length l)%nat -> c_val (ent sym) = Z.of_nat sym.

(** ** 4.  The root fetch

    [inf_fetch] is [[for (;;) { here = t[BITS(rootbits)];
    if (here.bits <= bits) break; PULLBYTE(); }]].  Under [Buffered] the
    first trip breaks, so the reader is not advanced and the entry is the
    one at the root index. *)

Lemma inf_fetch_hit :
  forall (t : ztbl) (rootbits : Z) (b : BR),
    c_bits (t (br_bits_of rootbits b)) <= br_bits b ->
    inf_fetch t rootbits b = FetchOk (t (br_bits_of rootbits b)) b.
Proof.
  intros t rootbits b H. unfold inf_fetch. cbn [inf_fetch_go].
  now rewrite (proj2 (Z.leb_le _ _) H).
Qed.

(** WHAT THE LOOP DOES WHEN [Buffered] FAILS, as far as this file goes.
    It pulls, and pulling is invisible at the stream level: the entry it
    finally selects may be the wrong one (that is the gap named in the
    header), but whatever it selects, the reader it hands back has the
    SAME abstract stream and is still well formed.  The [c_bits <= 32]
    bound is there to feed [br_wf_pullbyte]'s [br_bits b <= 31], i.e. to
    keep the accumulator inside [ZBitsIn.br_wf]'s [bits <= 39] across the
    pull; it holds of zlib's fixed literal/length table at every index
    ([lenfix_bits_bound]). *)

Lemma br_wf_pullbyte :
  forall b b' : BR,
    br_wf b -> br_bits b <= 31 -> br_pullbyte b = Some b' -> br_wf b'.
Proof.
  intros b b' (Hbits & Hhold & Hhave & Hin) H31 Hp.
  rewrite Z.shiftl_1_l in Hhold.
  pose proof (br_pullbyte_step b b' Hp) as (Hh & Hn & Hb & Hi).
  assert (Hval : br_hold b' = br_hold b + br_in b (br_next b) * 2 ^ br_bits b).
  { unfold br_pullbyte in Hp. destruct (Z.eqb (br_have b) 0); [discriminate|].
    inversion Hp. cbn [br_hold]. rewrite Z.shiftl_mul_pow2 by lia. reflexivity. }
  assert (Hpos : 0 < 2 ^ br_bits b) by (apply Z.pow_pos_nonneg; lia).
  assert (Hhave1 : 0 < br_have b).
  { unfold br_pullbyte in Hp.
    destruct (Z.eqb_spec (br_have b) 0); [discriminate|lia]. }
  pose proof (Hin (br_next b)) as Hbyte.
  unfold br_wf. rewrite Z.shiftl_1_l, Hb, Hval, Hh, Hi.
  replace (2 ^ (br_bits b + 8)) with (2 ^ br_bits b * 256)
    by (rewrite Z.pow_add_r by lia; ring).
  split; [lia|]. split; [nia|]. split; [lia|]. exact Hin.
Qed.

Lemma inf_fetch_go_stream :
  forall (f : nat) (t : ztbl) (nb : Z) (b : BR) (h : Code) (b' : BR),
    br_wf b ->
    (forall i : Z, c_bits (t i) <= 32) ->
    inf_fetch_go f t nb b = FetchOk h b' ->
    br_stream b' = br_stream b /\ br_wf b' /\ br_have b' <= br_have b.
Proof.
  induction f as [|f IH]; intros t nb b h b' Hwf Hb32 H;
    cbn [inf_fetch_go] in H; [discriminate|].
  destruct (Z.leb_spec (c_bits (t (br_bits_of nb b))) (br_bits b)) as [Hle|Hgt].
  - injection H as Hh Hb'. subst b'.
    split; [reflexivity|]. split; [exact Hwf|lia].
  - destruct (br_pullbyte b) as [b1|] eqn:Hp; [|discriminate].
    assert (H31 : br_bits b <= 31)
      by (specialize (Hb32 (br_bits_of nb b)); lia).
    pose proof (br_wf_pullbyte b b1 Hwf H31 Hp) as Hwf1.
    pose proof (br_stream_pullbyte b b1 Hwf Hp) as Hs.
    pose proof (br_pullbyte_step b b1 Hp) as (Hh1 & _ & _ & _).
    destruct (IH t nb b1 h b' Hwf1 Hb32 H) as [H1 [H2 H3]].
    split; [congruence|]. split; [exact H2|lia].
Qed.

Corollary inf_fetch_stream :
  forall (t : ztbl) (nb : Z) (b : BR) (h : Code) (b' : BR),
    br_wf b ->
    (forall i : Z, c_bits (t i) <= 32) ->
    inf_fetch t nb b = FetchOk h b' ->
    br_stream b' = br_stream b /\ br_wf b'.
Proof.
  intros t nb b h b' Hwf Hb32 H.
  destruct (inf_fetch_go_stream _ t nb b h b' Hwf Hb32 H) as [H1 [H2 _]].
  split; assumption.
Qed.

(** The entry the root fetch lands on, from the two sides at once: the
    table condition names it, and [Buffered] makes the loop stop. *)
Lemma inf_fetch_agrees :
  forall (t : ztbl) (rootbits : Z) (l : list nat) (maxBits : nat)
         (ent : nat -> Code) (b : BR) (sym : nat) (cw rem : list bool),
    TableAgreesAt t rootbits l maxBits ent sym ->
    code_for l maxBits sym = Some cw ->
    br_stream b = cw ++ rem ->
    Z.of_nat (length cw) <= rootbits ->
    Z.of_nat (length cw) <= br_bits b ->
    t (br_bits_of rootbits b) = ent sym
    /\ c_bits (ent sym) = Z.of_nat (length cw)
    /\ inf_fetch t rootbits b = FetchOk (ent sym) b.
Proof.
  intros t rootbits l maxBits ent b sym cw rem HTA Hcf Hstr Hroot Hbuf.
  destruct (HTA cw Hcf Hroot) as [Hbits Hlook].
  assert (Hidx : 0 <= br_bits_of rootbits b < 2 ^ rootbits)
    by (apply br_bits_of_in_range; lia).
  assert (Hspell : write_bits (length cw) (br_bits_of rootbits b) = cw).
  { replace (length cw) with (Z.to_nat (Z.of_nat (length cw))) by lia.
    rewrite (br_index_spells_stream (Z.of_nat (length cw)) rootbits b)
      by lia.
    rewrite Hstr, Nat2Z.id, firstn_app, firstn_all, Nat.sub_diag.
    cbn [firstn]. apply app_nil_r. }
  pose proof (Hlook _ Hidx Hspell) as Hent.
  split; [exact Hent|]. split; [exact Hbits|].
  rewrite (inf_fetch_hit t rootbits b) by (rewrite Hent, Hbits; lia).
  now rewrite Hent.
Qed.

(** ** 5.  The equation

    One side for each consumer: [inf_decode] for [inf_LEN] / [inf_DIST]
    (§5.2), [inf_fetch] for [cl_step] (§5.3). *)

(** *** 5.1  The general form

    Stated over the stream split [br_stream b = cw ++ rem] rather than
    over [hdecode] directly, so it is usable by a caller who obtained the
    split some other way; §5.2 supplies the [hdecode] form. *)

Theorem inf_decode_root_entry :
  forall (sub : Code -> bool) (t : ztbl) (rootbits : Z) (l : list nat)
         (maxBits : nat) (ent : nat -> Code) (b : BR) (sym : nat)
         (cw rem : list bool),
    TableAgreesAt t rootbits l maxBits ent sym ->
    code_for l maxBits sym = Some cw ->
    br_stream b = cw ++ rem ->
    Z.of_nat (length cw) <= rootbits ->          (** CodeFitsRoot *)
    Z.of_nat (length cw) <= br_bits b ->         (** Buffered *)
    sub (ent sym) = false ->                     (** NotAPointer *)
    inf_decode sub t rootbits b
    = DecOk (ent sym) (br_dropbits (Z.of_nat (length cw)) b)
            (Z.of_nat (length cw)).
Proof.
  intros sub t rootbits l maxBits ent b sym cw rem HTA Hcf Hstr Hroot Hbuf Hsub.
  destruct (inf_fetch_agrees t rootbits l maxBits ent b sym cw rem
              HTA Hcf Hstr Hroot Hbuf) as [_ [Hbits Hfetch]].
  unfold inf_decode. rewrite Hfetch, Hsub, Hbits. reflexivity.
Qed.

(** The reader really did advance over the codeword and nothing else.
    [0 <= br_hold b] is the only part of [ZBitsIn.br_wf] this file needs,
    and it enters only through [ZBitsBridge.br_stream_dropbits]. *)
Lemma inf_decode_root_stream :
  forall (b : BR) (cw rem : list bool),
    br_stream b = cw ++ rem ->
    Z.of_nat (length cw) <= br_bits b ->
    0 <= br_hold b ->
    br_stream (br_dropbits (Z.of_nat (length cw)) b) = rem.
Proof.
  intros b cw rem Hstr Hbuf Hhold.
  rewrite br_stream_dropbits by lia.
  rewrite Hstr, Nat2Z.id, skipn_app, skipn_all, Nat.sub_diag.
  reflexivity.
Qed.

(** *** 5.2  Against [hdecode]: the headline

    The declarative decode of the reader's own stream, and the machine's
    decode of the built table, in one equation carrying entry, remainder
    and bit count. *)

Lemma hdecode_code_table_split :
  forall (l : list nat) (maxBits : nat) (bits : list bool) (sym : nat)
         (rem : list bool),
    hdecode (code_table l maxBits) bits = Some (sym, rem) ->
    exists cw, code_for l maxBits sym = Some cw /\ bits = cw ++ rem.
Proof.
  intros l maxBits bits sym rem H.
  apply hdecode_sound in H as [cw [Hin [_ Heq]]].
  apply code_table_In_iff in Hin. exists cw. split; assumption.
Qed.

Theorem inf_decode_hdecode :
  forall (sub : Code -> bool) (t : ztbl) (rootbits : Z) (l : list nat)
         (maxBits : nat) (ent : nat -> Code) (b : BR) (sym : nat)
         (cw rem : list bool),
    TableAgreesAt t rootbits l maxBits ent sym ->
    hdecode (code_table l maxBits) (br_stream b) = Some (sym, rem) ->
    code_for l maxBits sym = Some cw ->
    Z.of_nat (length cw) <= rootbits ->          (** CodeFitsRoot *)
    Z.of_nat (length cw) <= br_bits b ->         (** Buffered *)
    0 <= br_hold b ->
    sub (ent sym) = false ->                     (** NotAPointer *)
    inf_decode sub t rootbits b
      = DecOk (ent sym) (br_dropbits (Z.of_nat (length cw)) b)
              (Z.of_nat (length cw))
    /\ br_stream (br_dropbits (Z.of_nat (length cw)) b) = rem
    /\ Z.of_nat (length cw)
       = Z.of_nat (length (br_stream b) - length rem)%nat.
Proof.
  intros sub t rootbits l maxBits ent b sym cw rem
         HTA Hdec Hcf Hroot Hbuf Hhold Hsub.
  destruct (hdecode_code_table_split l maxBits (br_stream b) sym rem Hdec)
    as [cw' [Hcf' Hstr]].
  assert (Hcw : cw' = cw) by congruence. subst cw'.
  split.
  { exact (inf_decode_root_entry sub t rootbits l maxBits ent b sym cw rem
             HTA Hcf Hstr Hroot Hbuf Hsub). }
  split.
  { exact (inf_decode_root_stream b cw rem Hstr Hbuf Hhold). }
  rewrite Hstr, length_app. lia.
Qed.

(** POSITIVE CONSUMPTION, the property the bit count exists to carry.  It
    is the spec side that supplies it, hypothesis-free
    ([DeflateSpec.hdecode_code_table_shorter]) — note this covers the
    CODEWORD path only, since a sub-table POINTER is not a codeword and
    that lemma says nothing about one. *)
Corollary inf_decode_progress :
  forall (sub : Code -> bool) (t : ztbl) (rootbits : Z) (l : list nat)
         (maxBits : nat) (ent : nat -> Code) (b : BR) (sym : nat)
         (cw rem : list bool),
    TableAgreesAt t rootbits l maxBits ent sym ->
    hdecode (code_table l maxBits) (br_stream b) = Some (sym, rem) ->
    code_for l maxBits sym = Some cw ->
    Z.of_nat (length cw) <= rootbits ->
    Z.of_nat (length cw) <= br_bits b ->
    0 <= br_hold b ->
    sub (ent sym) = false ->
    inf_decode sub t rootbits b
      = DecOk (ent sym) (br_dropbits (Z.of_nat (length cw)) b)
              (Z.of_nat (length cw))
    /\ 0 < Z.of_nat (length cw)
    /\ (length rem < length (br_stream b))%nat.
Proof.
  intros sub t rootbits l maxBits ent b sym cw rem
         HTA Hdec Hcf Hroot Hbuf Hhold Hsub.
  pose proof (hdecode_code_table_shorter l maxBits (br_stream b) sym rem Hdec)
    as Hlt.
  destruct (inf_decode_hdecode sub t rootbits l maxBits ent b sym cw rem
              HTA Hdec Hcf Hroot Hbuf Hhold Hsub) as [Heq [_ Hnb]].
  split; [exact Heq|]. split; [lia|exact Hlt].
Qed.

(** And the symbol itself, for a caller whose entries carry it. *)
Corollary inf_decode_val :
  forall (sub : Code -> bool) (t : ztbl) (rootbits : Z) (l : list nat)
         (maxBits : nat) (ent : nat -> Code) (b : BR) (sym : nat)
         (cw rem : list bool),
    TableAgreesAt t rootbits l maxBits ent sym ->
    ValEntries l ent ->
    hdecode (code_table l maxBits) (br_stream b) = Some (sym, rem) ->
    code_for l maxBits sym = Some cw ->
    Z.of_nat (length cw) <= rootbits ->
    Z.of_nat (length cw) <= br_bits b ->
    0 <= br_hold b ->
    sub (ent sym) = false ->
    exists h b',
      inf_decode sub t rootbits b = DecOk h b' (Z.of_nat (length cw))
      /\ c_val h = Z.of_nat sym
      /\ br_stream b' = rem.
Proof.
  intros sub t rootbits l maxBits ent b sym cw rem
         HTA HV Hdec Hcf Hroot Hbuf Hhold Hsub.
  destruct (inf_decode_hdecode sub t rootbits l maxBits ent b sym cw rem
              HTA Hdec Hcf Hroot Hbuf Hhold Hsub) as [Heq [Hrem _]].
  exists (ent sym), (br_dropbits (Z.of_nat (length cw)) b).
  split; [exact Heq|]. split; [|exact Hrem].
  apply HV. apply (code_for_range l maxBits sym cw Hcf).
Qed.

(** *** 5.3  Per consumer

    [inf_LEN] and [inf_DIST] differ only in the pointer guard; [cl_step]
    uses the root fetch alone and never takes a second level. *)

(** [sub_len h = negb (op =? 0) && (op & 0xf0 =? 0)]: false for a literal
    ([op = 0]) and for anything with a bit set above the low nibble, which
    in [inftrees.c] is every length code ([lext] is offset by 16), the
    end-of-block marker (96) and the invalid marker (64). *)
Lemma sub_len_false_of_op :
  forall h : Code, c_op h = 0 \/ Z.land (c_op h) 240 <> 0 -> sub_len h = false.
Proof.
  intros h [H|H]; unfold sub_len.
  - rewrite H. reflexivity.
  - rewrite (proj2 (Z.eqb_neq _ _) H). apply andb_false_r.
Qed.

(** [sub_dist] has no [op /= 0] conjunct ([inflate.c:1090]), so [op = 0]
    does NOT save a distance entry — and it need not, since no distance
    entry has [op = 0] ([dext] is offset by 16 too). *)
Lemma sub_dist_false_of_op :
  forall h : Code, Z.land (c_op h) 240 <> 0 -> sub_dist h = false.
Proof.
  intros h H. unfold sub_dist. now apply Z.eqb_neq.
Qed.

Corollary inf_decode_len :
  forall (t : ztbl) (rootbits : Z) (l : list nat) (maxBits : nat)
         (ent : nat -> Code) (b : BR) (sym : nat) (cw rem : list bool),
    TableAgreesAt t rootbits l maxBits ent sym ->
    hdecode (code_table l maxBits) (br_stream b) = Some (sym, rem) ->
    code_for l maxBits sym = Some cw ->
    Z.of_nat (length cw) <= rootbits ->
    Z.of_nat (length cw) <= br_bits b ->
    0 <= br_hold b ->
    c_op (ent sym) = 0 \/ Z.land (c_op (ent sym)) 240 <> 0 ->
    inf_decode sub_len t rootbits b
      = DecOk (ent sym) (br_dropbits (Z.of_nat (length cw)) b)
              (Z.of_nat (length cw))
    /\ br_stream (br_dropbits (Z.of_nat (length cw)) b) = rem
    /\ 0 < Z.of_nat (length cw).
Proof.
  intros t rootbits l maxBits ent b sym cw rem HTA Hdec Hcf Hroot Hbuf Hhold Hop.
  pose proof (hdecode_code_table_shorter l maxBits (br_stream b) sym rem Hdec).
  destruct (inf_decode_hdecode sub_len t rootbits l maxBits ent b sym cw rem
              HTA Hdec Hcf Hroot Hbuf Hhold (sub_len_false_of_op _ Hop))
    as [H1 [H2 H3]].
  split; [exact H1|]. split; [exact H2|]. lia.
Qed.

Corollary inf_decode_dist :
  forall (t : ztbl) (rootbits : Z) (l : list nat) (maxBits : nat)
         (ent : nat -> Code) (b : BR) (sym : nat) (cw rem : list bool),
    TableAgreesAt t rootbits l maxBits ent sym ->
    hdecode (code_table l maxBits) (br_stream b) = Some (sym, rem) ->
    code_for l maxBits sym = Some cw ->
    Z.of_nat (length cw) <= rootbits ->
    Z.of_nat (length cw) <= br_bits b ->
    0 <= br_hold b ->
    Z.land (c_op (ent sym)) 240 <> 0 ->
    inf_decode sub_dist t rootbits b
      = DecOk (ent sym) (br_dropbits (Z.of_nat (length cw)) b)
              (Z.of_nat (length cw))
    /\ br_stream (br_dropbits (Z.of_nat (length cw)) b) = rem
    /\ 0 < Z.of_nat (length cw).
Proof.
  intros t rootbits l maxBits ent b sym cw rem HTA Hdec Hcf Hroot Hbuf Hhold Hop.
  pose proof (hdecode_code_table_shorter l maxBits (br_stream b) sym rem Hdec).
  destruct (inf_decode_hdecode sub_dist t rootbits l maxBits ent b sym cw rem
              HTA Hdec Hcf Hroot Hbuf Hhold (sub_dist_false_of_op _ Hop))
    as [H1 [H2 H3]].
  split; [exact H1|]. split; [exact H2|]. lia.
Qed.

(** [cl_step] ([inflate.c:935-985]) reads the code-length tree with
    [inf_fetch] and drops [here.bits] itself, so it wants the fetch form.
    No pointer guard appears in it at all: the code-length table is one
    level by construction. *)
Corollary inf_fetch_hdecode :
  forall (t : ztbl) (rootbits : Z) (l : list nat) (maxBits : nat)
         (ent : nat -> Code) (b : BR) (sym : nat) (cw rem : list bool),
    TableAgreesAt t rootbits l maxBits ent sym ->
    hdecode (code_table l maxBits) (br_stream b) = Some (sym, rem) ->
    code_for l maxBits sym = Some cw ->
    Z.of_nat (length cw) <= rootbits ->
    Z.of_nat (length cw) <= br_bits b ->
    0 <= br_hold b ->
    inf_fetch t rootbits b = FetchOk (ent sym) b
    /\ c_bits (ent sym) = Z.of_nat (length cw)
    /\ br_stream (br_dropbits (c_bits (ent sym)) b) = rem
    /\ 0 < c_bits (ent sym).
Proof.
  intros t rootbits l maxBits ent b sym cw rem HTA Hdec Hcf Hroot Hbuf Hhold.
  pose proof (hdecode_code_table_shorter l maxBits (br_stream b) sym rem Hdec)
    as Hlt.
  destruct (hdecode_code_table_split l maxBits (br_stream b) sym rem Hdec)
    as [cw' [Hcf' Hstr]].
  assert (Hcw : cw' = cw) by congruence. subst cw'.
  destruct (inf_fetch_agrees t rootbits l maxBits ent b sym cw rem
              HTA Hcf Hstr Hroot Hbuf) as [_ [Hbits Hfetch]].
  split; [exact Hfetch|]. split; [exact Hbits|].
  rewrite Hbits.
  split; [exact (inf_decode_root_stream b cw rem Hstr Hbuf Hhold)|].
  rewrite Hstr, length_app in Hlt. lia.
Qed.

(** ** 6.  What is NOT true

    Two adversarial tables, both satisfying [TableAgrees] for the SAME
    one-symbol code, agreeing wherever a codeword reaches and differing
    where none does.  [code_for] gives [inc_lens = [1]]'s single symbol
    the one-bit codeword [[false]], so index parity is the whole story,
    and the odd indices are covered by no codeword at all — which is what
    [converse_fails]'s [hdecode ... = None] conjunct records. *)

Definition inc_lens : list nat := [1%nat].
Definition inc_ent : nat -> Code := fun _ => mkCode 0 1 0.

(** Even indices carry the real entry; odd ones are free.  [inc_tbl] puts
    [inftrees.c]'s invalid-code filler there ([op = 64]); [ptr_tbl] puts a
    ZERO-WIDTH sub-table pointer there ([op = 1], so [op & 0xf0 = 0]). *)
Definition inc_tbl : ztbl :=
  fun i => if Z.even i then mkCode 0 1 0 else mkCode 64 1 0.
Definition ptr_tbl : ztbl :=
  fun i => if Z.even i then mkCode 0 1 0 else mkCode 1 0 0.

(** A reader holding a single [1] bit — an index no codeword covers. *)
Definition inc_b : BR :=
  {| br_in := zzero; br_have := 0; br_next := 0; br_hold := 1; br_bits := 1 |}.

Lemma inc_b_stream : br_stream inc_b = [true].
Proof. vm_compute. reflexivity. Qed.

(** Both tables satisfy the interface, at every symbol.  The proof is the
    same for both: only the even indices are constrained. *)
Lemma inc_agrees_gen :
  forall f : Z -> Code,
    (forall i, Z.even i = true -> f i = mkCode 0 1 0) ->
    TableAgrees f 1 inc_lens 15%nat inc_ent.
Proof.
  intros f Hf sym cw Hcf Hle.
  destruct sym as [|s].
  - vm_compute in Hcf. injection Hcf as Hcw. subst cw.
    split; [reflexivity|].
    intros i Hi Hw. cbn [write_bits length] in Hw.
    injection Hw as Hodd.
    apply Hf. rewrite <- Z.negb_odd, Hodd. reflexivity.
  - exfalso. apply code_for_range in Hcf.
    unfold inc_lens in Hcf. cbn [length] in Hcf. lia.
Qed.

Lemma inc_tbl_agrees : TableAgrees inc_tbl 1 inc_lens 15%nat inc_ent.
Proof.
  apply inc_agrees_gen. intros i Hi. unfold inc_tbl. now rewrite Hi.
Qed.

Lemma ptr_tbl_agrees : TableAgrees ptr_tbl 1 inc_lens 15%nat inc_ent.
Proof.
  apply inc_agrees_gen. intros i Hi. unfold ptr_tbl. now rewrite Hi.
Qed.

(** THE EQUATION DOES NOT REVERSE.  The machine reports [DecOk] — with the
    invalid-code entry, which [inflate.c:1065] then rejects — where the
    spec has no decode at all.  So no lemma in this file may be read as
    "machine decodes ==> spec decodes". *)
Theorem converse_fails :
  TableAgrees inc_tbl 1 inc_lens 15%nat inc_ent
  /\ hdecode (code_table inc_lens 15%nat) (br_stream inc_b) = None
  /\ inf_decode sub_len inc_tbl 1 inc_b
     = DecOk (mkCode 64 1 0) (br_dropbits 1 inc_b) 1.
Proof.
  split; [exact inc_tbl_agrees|].
  split; vm_compute; reflexivity.
Qed.

(** THE POINTER PATH, AND WHY THE BIT COUNT IS IN THE EQUATION.  The same
    interface, satisfied by a table whose free indices hold a zero-width
    sub-table pointer: [inf_decode] follows [inf_fetch2] into the second
    level and returns [DecOk] having consumed NOTHING.  [TableAgrees] does
    not exclude this and is not meant to; the main theorem excludes it by
    [NotAPointer], and on the codeword path [inf_decode_progress] refutes
    it outright. *)
Theorem pointer_zero_bits_no_progress :
  TableAgrees ptr_tbl 1 inc_lens 15%nat inc_ent
  /\ inf_decode sub_len ptr_tbl 1 inc_b
     = DecOk (mkCode 1 0 0) (br_dropbits 0 (br_dropbits 0 inc_b)) 0
  /\ sub_len (mkCode 1 0 0) = true.
Proof.
  split; [exact ptr_tbl_agrees|].
  split; vm_compute; reflexivity.
Qed.

(** "Consumed nothing" spelled out at the stream level, so the claim is
    about observable progress and not about the [nb] field alone. *)
Theorem pointer_no_progress_stream :
  br_stream (br_dropbits 0 (br_dropbits 0 inc_b)) = br_stream inc_b.
Proof. vm_compute. reflexivity. Qed.

(** The two tables differ, and only off the covered indices — which is the
    precise sense in which [TableAgrees] does not pin the table. *)
Theorem agrees_does_not_pin_table :
  inc_tbl 1 <> ptr_tbl 1
  /\ (forall i, Z.even i = true -> inc_tbl i = ptr_tbl i).
Proof.
  split.
  - vm_compute. discriminate.
  - intros i Hi. unfold inc_tbl, ptr_tbl. now rewrite Hi.
Qed.

(** ** 7.  Against zlib's own fixed tables

    [Inflate.lenfix] / [Inflate.distfix] are that file's verbatim
    transcription of [inffixed.h], so every test in this section is a
    check against real zlib data rather than against a table this file
    made up. *)

(** *** 7.0  The [c_bits <= 32] bound of §4 is real

    [lenfix] is a TOTAL function — out-of-range indices read
    [tbl_of_list]'s [(0,0,0)] default — so the bound holds at every [Z],
    not merely on [[0,512)]. *)
Lemma lenfix_bits_bound : forall i : Z, c_bits (lenfix i) <= 32.
Proof.
  intro i.
  assert (Hall : forallb (fun e => Z.leb (snd (fst e)) 32) lenfix_list = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in Hall.
  unfold lenfix, tbl_of_list.
  destruct (nth_in_or_default (Z.to_nat i) lenfix_list (0, 0, 0)) as [Hin|Hd].
  - specialize (Hall _ Hin).
    set (e := nth (Z.to_nat i) lenfix_list (0, 0, 0)) in *.
    destruct e as [[op bits] val].
    cbn [snd fst c_bits] in Hall |- *. lia.
  - rewrite Hd. cbn [c_bits]. lia.
Qed.

(** *** 7.1  The [NotAPointer] hypothesis is discharged, not assumed

    The fixed tables are single-level, so the guard is false at EVERY
    index.  A test that fails for any table with a sub-table. *)
Example lenfix_has_no_subtables :
  forallb (fun i => negb (sub_len (lenfix (Z.of_nat i)))) (seq 0 512) = true.
Proof. vm_compute. reflexivity. Qed.

Example distfix_has_no_subtables :
  forallb (fun i => negb (sub_dist (distfix (Z.of_nat i)))) (seq 0 32) = true.
Proof. vm_compute. reflexivity. Qed.

(** *** 7.2  [TableAgreesAt] holds of a real table at a real symbol

    Literal 0 of the fixed literal/length tree: RFC 1951 §3.2.6 gives it
    the 8-bit codeword [00110000], so the index is its LSB-first reading,
    [12], and the 9-bit root table holds the entry at both [12] and
    [12 + 256].  Proved for ALL 512 root indices, not just those two: the
    index condition is what narrows it. *)

Definition ent_lit0 : nat -> Code := fun _ => mkCode 0 8 0.

Lemma lenfix_agrees_at_0 :
  TableAgreesAt lenfix 9 fixed_lit_lengths 15%nat ent_lit0 0%nat.
Proof.
  intros cw Hcf Hle. vm_compute in Hcf. injection Hcf as Hcw. subst cw.
  split; [reflexivity|].
  intros i Hi Hw. cbn [length] in Hw.
  assert (Hmod : i mod 2 ^ Z.of_nat 8 = 12 mod 2 ^ Z.of_nat 8).
  { apply (write_bits_inj_mod 8%nat). rewrite Hw. vm_compute. reflexivity. }
  change (2 ^ Z.of_nat 8) with 256 in Hmod.
  change (12 mod 256) with 12 in Hmod.
  change (2 ^ 9) with 512 in Hi.
  assert (Hcase : i = 12 \/ i = 268).
  { destruct (Z.lt_ge_cases i 256) as [Hlt|Hge].
    - left. rewrite Z.mod_small in Hmod by lia. exact Hmod.
    - right. replace i with ((i - 256) + 1 * 256) in Hmod by lia.
      rewrite Z_mod_plus_full, Z.mod_small in Hmod by lia. lia. }
  destruct Hcase as [->| ->]; vm_compute; reflexivity.
Qed.

(** THE REVERSAL IS LOAD BEARING.  If the index were the code VALUE (48)
    instead of its mirror (12), the entry would be a length code, not
    literal 0.  This is the mutant [lenfix_agrees_at_0] rules out. *)
Example lenfix_reversal_is_load_bearing :
  lenfix 12 = mkCode 0 8 0
  /\ lenfix 48 = mkCode 16 7 8
  /\ lenfix 48 <> lenfix 12.
Proof. split; [|split]; vm_compute; try reflexivity. discriminate. Qed.

(** *** 7.3  End to end on the fixed tree

    A reader holding 16 bits whose first eight are literal 0's codeword.
    The bridge equation is DERIVED — [fixb_via_bridge] runs the theorem —
    and the raw computation is kept beside it so that a change to either
    side shows up as a mismatch rather than as a silently weaker claim. *)

Definition fixb : BR :=
  {| br_in := zzero; br_have := 0; br_next := 0; br_hold := 12; br_bits := 16 |}.

Definition fixrem : list bool :=
  [false; false; false; false; false; false; false; false].

Example fixb_stream :
  br_stream fixb
  = [false; false; true; true; false; false; false; false] ++ fixrem.
Proof. vm_compute. reflexivity. Qed.

Example fixb_hdecode :
  hdecode (code_table fixed_lit_lengths 15%nat) (br_stream fixb)
  = Some (0%nat, fixrem).
Proof. vm_compute. reflexivity. Qed.

Example fixb_machine :
  inf_decode sub_len lenfix 9 fixb = DecOk (mkCode 0 8 0) (br_dropbits 8 fixb) 8.
Proof. vm_compute. reflexivity. Qed.

(** The same, through the theorem instead of through [vm_compute]: this is
    the test that the STATEMENT is right, not just the computation. *)
Theorem fixb_via_bridge :
  inf_decode sub_len lenfix 9 fixb
    = DecOk (mkCode 0 8 0) (br_dropbits 8 fixb) 8
  /\ br_stream (br_dropbits 8 fixb) = fixrem
  /\ (8 = Z.of_nat (length (br_stream fixb) - length fixrem)%nat)
  /\ 0 < 8.
Proof.
  assert (Hcf : code_for fixed_lit_lengths 15%nat 0%nat
                = Some [false; false; true; true; false; false; false; false])
    by (vm_compute; reflexivity).
  assert (Hlen : Z.of_nat
                   (length [false; false; true; true; false; false; false; false])
                 = 8) by reflexivity.
  destruct (inf_decode_progress sub_len lenfix 9 fixed_lit_lengths 15%nat
              ent_lit0 fixb 0%nat
              [false; false; true; true; false; false; false; false] fixrem
              lenfix_agrees_at_0 fixb_hdecode Hcf
              ltac:(vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)) as [Heq [Hpos _]].
  destruct (inf_decode_hdecode sub_len lenfix 9 fixed_lit_lengths 15%nat
              ent_lit0 fixb 0%nat
              [false; false; true; true; false; false; false; false] fixrem
              lenfix_agrees_at_0 fixb_hdecode Hcf
              ltac:(vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(vm_compute; reflexivity)) as [_ [Hrem Hnb]].
  cbn [ent_lit0] in Heq, Hrem, Hnb.
  rewrite Hlen in Heq, Hrem, Hnb.
  split; [exact Heq|]. split; [exact Hrem|]. split; [exact Hnb|lia].
Qed.

(** *** 7.4  The distance consumer, on the fixed distance table

    [distfix] is the one fixed table that IS [inflate_table]'s own output
    ([Inflate.distfix_is_inflate_table]), so this instance is the closest
    thing available to a builder-produced table until the table lane
    lands.  All 32 codes are 5 bits, the root width is 5, and distance
    symbol 0's codeword is [00000] — index 0, entry [(16,5,1)]: [op = 16]
    is [dext]'s offset, so [sub_dist] is false and the entry is a real
    code, not a pointer. *)

Definition ent_dist0 : nat -> Code := fun _ => mkCode 16 5 1.

Lemma distfix_agrees_at_0 :
  TableAgreesAt distfix 5 fixed_dist_lengths 15%nat ent_dist0 0%nat.
Proof.
  intros cw Hcf Hle. vm_compute in Hcf. injection Hcf as Hcw. subst cw.
  split; [reflexivity|].
  intros i Hi Hw. cbn [length] in Hw.
  assert (Hmod : i mod 2 ^ Z.of_nat 5 = 0 mod 2 ^ Z.of_nat 5).
  { apply (write_bits_inj_mod 5%nat). rewrite Hw. vm_compute. reflexivity. }
  change (2 ^ Z.of_nat 5) with 32 in Hmod.
  change (0 mod 32) with 0 in Hmod.
  change (2 ^ 5) with 32 in Hi.
  rewrite Z.mod_small in Hmod by lia. subst i.
  vm_compute. reflexivity.
Qed.

Definition distb : BR :=
  {| br_in := zzero; br_have := 0; br_next := 0; br_hold := 0; br_bits := 8 |}.

Definition distrem : list bool := [false; false; false].

Example distb_hdecode :
  hdecode (code_table fixed_dist_lengths 15%nat) (br_stream distb)
  = Some (0%nat, distrem).
Proof. vm_compute. reflexivity. Qed.

Theorem distb_via_bridge :
  inf_decode sub_dist distfix 5 distb
    = DecOk (mkCode 16 5 1) (br_dropbits 5 distb) 5
  /\ br_stream (br_dropbits 5 distb) = distrem
  /\ 0 < 5.
Proof.
  assert (Hcf : code_for fixed_dist_lengths 15%nat 0%nat
                = Some [false; false; false; false; false])
    by (vm_compute; reflexivity).
  destruct (inf_decode_dist distfix 5 fixed_dist_lengths 15%nat ent_dist0
              distb 0%nat [false; false; false; false; false] distrem
              distfix_agrees_at_0 distb_hdecode Hcf
              ltac:(vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(vm_compute; discriminate)
              ltac:(vm_compute; discriminate)) as [H1 [H2 H3]].
  cbn [ent_dist0] in H1, H2.
  change (Z.of_nat (length [false; false; false; false; false])) with 5
    in H1, H2.
  split; [exact H1|]. split; [exact H2|lia].
Qed.

(** *** 7.5  [c_val] is NOT the symbol

    Symbol 285 of the fixed literal/length tree is the length code for
    258 with no extra bits.  Its codeword is [11000101], its index is the
    mirror [163], and the entry there carries [c_val = 258].  Any bridge
    that had written [c_val h = Z.of_nat sym] into the equation would be
    refuted here — which is why [TableAgreesAt] keeps the entry abstract
    and [ValEntries] is a separate, optional hypothesis. *)
Example lenfix_val_is_not_the_symbol :
  code_for fixed_lit_lengths 15%nat 285%nat = Some (write_bits 8 163)
  /\ lenfix 163 = mkCode 16 8 258
  /\ c_val (lenfix 163) <> Z.of_nat 285%nat.
Proof.
  split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  vm_compute. discriminate.
Qed.

(** Sharper, and the reason [ValEntries] is a hypothesis and not a
    consequence: NO entry function can both agree with zlib's fixed
    literal/length table at symbol 285 and carry the symbol in [c_val].
    A bridge that had folded [c_val h = Z.of_nat sym] into the main
    equation would therefore be unusable at the LEN call site, not merely
    unproven there. *)
Theorem val_entries_fails_for_lenfix :
  forall ent : nat -> Code,
    TableAgreesAt lenfix 9 fixed_lit_lengths 15%nat ent 285%nat ->
    ~ ValEntries fixed_lit_lengths ent.
Proof.
  intros ent HTA HV.
  destruct (HTA (write_bits 8 163)
              ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; discriminate)) as [_ Hlook].
  assert (Hi : 0 <= 163 < 2 ^ 9) by (change (2 ^ 9) with 512; lia).
  specialize (Hlook 163 Hi ltac:(vm_compute; reflexivity)).
  assert (Hv : c_val (ent 285%nat) = 258)
    by (rewrite <- Hlook; vm_compute; reflexivity).
  assert (Hv' : c_val (ent 285%nat) = Z.of_nat 285%nat)
    by (apply HV; rewrite fixed_lit_lengths_length; lia).
  rewrite Hv in Hv'. vm_compute in Hv'. discriminate.
Qed.

(** ... and it is not empty either — it is exactly what the [CODES] arm of
    [inftrees.c] produces, where [here.val = work[sym]].  Witnessed on the
    one-symbol code of §6, so the two statements together say: satisfiable
    in general, false for a length tree. *)
Lemma inc_ent_val_entries : ValEntries inc_lens inc_ent.
Proof. intros sym Hs. destruct sym as [|s]; [reflexivity|cbn in Hs; lia]. Qed.
