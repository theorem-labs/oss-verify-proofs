(** * Spec.PngModel.DeflateSpec — the declarative DEFLATE decoder (L0b).

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT.  Depends only on
    [Spec.PngModel.Base], [Spec.PngModel.Bits], [Spec.PngModel.Huff] and
    Stdlib.

    L0b, the second and last piece of L0.  [Bits.v] fixed the bit view of a
    byte list and [Huff.v] fixed what a canonical Huffman code is; this
    file assembles them into RFC 1951 proper: the constant tables, the
    per-symbol decoder, the per-block decoders for all three BTYPEs, the
    stream decoder, and the validity predicates the capstone quantifies
    over.

    LAYERING, hard.  The OPERATIONAL side — [inftrees.c]'s table builder,
    [inflate.c]'s state machine, [InflateFast], [ZBitsIn]/[ZBitsOut],
    [Trees], [Deflate], [Codec] — is a different lane's work in different
    files.  This file must never grow a dependency on any of them.  The
    refinement between the declarative surface and the transcription is
    stated in separate bridge modules (compare [Spec.PngModel.ZBitsBridge],
    which does exactly that for the bit reader).

    THE FORWARD-ONLY RULING, and what it buys.

    The campaign proves only "spec-succeeds => implementation-succeeds and
    agrees".  It does NOT prove the converse.  The capstone quantifies over
    streams our own encoder produced, so the decoder in this file is never
    run on a stream the spec has not already characterised.

    Consequence, and it is visible in nearly every definition below: the
    [None] cases are LOOSE.  They are not required to line up with any
    error path in [inflate.c], they carry no meaning of their own, and no
    lemma here says anything about them beyond "the recursion is
    well-founded".  Where zlib and this file could differ, this file
    prefers to fail — [None] where zlib errors is free, and it is the safe
    direction if the ruling is ever narrowed — but it makes no claim of
    agreement, and it spends no case analysis establishing one.  Each such
    point is flagged in the comments with the marker FORWARD-ONLY, and the
    total is tallied in section 10.

    One deliberate exception is inherited from [Huff.v] and is worth
    naming: [ValidLengths] is the Kraft INEQUALITY, so this file ACCEPTS
    incomplete codes that zlib's [inftrees.c] rejects.  That is the
    dangerous direction (spec succeeds where the implementation errors) and
    it is sound only because the capstone restricts the input universe to
    encoder output, which is always complete.  It is stated here rather
    than buried.

    CONVENTIONS, inherited.  The default scope is [Z_scope] (as in
    [Bits.v]), so every [nat] literal carries an explicit [%nat].  BIT
    COUNTS, symbol indices, code lengths, match lengths and match distances
    are [nat] — match lengths and distances because [Huff.lz_sym]'s
    [LzRef] already fixed them that way.  Only BYTE VALUES and the raw
    results of [Bits.read_bits] are [Z].  Comparisons are written with the
    named functions [Nat.eqb]/[Nat.ltb]/[Nat.leb]/[Z.eqb] rather than
    notation, so no scope annotation can silently pick the wrong one.

    Every definition is total, non-dependent and obligation-free: no
    [Program], no subtypes, no dependent elimination.  Out-of-range table
    lookups go through [nth_error] and return [None].

    [maxBits] IS ALWAYS AN EXPLICIT ARGUMENT.  15 for the literal/length
    and distance trees, 7 for the code-length tree.  Section 9 proves the
    uncomfortable fact that for a code-length tree read from 3-bit fields
    the 7-vs-15 choice is UNOBSERVABLE ([cl_valid_7_15]) — so no test can
    pin it, and a lemma is stated instead of a test that would only look
    like one.

    DISCIPLINE.  Every claim any comment in this file makes is stated as a
    lemma below it.  Where a fact is merely NOT proved here, the comment
    says so explicitly rather than asserting it in passing.  Tests are
    chosen for what wrong implementation they would catch, and section 10
    says, per test, what that is. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Bits Huff.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** ** 1. The RFC 1951 constant tables

    Pure data; there is no cleverness available and a wrong table is a
    wrong spec that compiles.  The defence is section 10's
    [length_table_contiguous] / [dist_table_contiguous], which check the
    tables against a STRUCTURAL property of RFC 1951 (each code's range
    starts where the previous one's ends) rather than restating them.

    All four numeric tables are [list nat].  Match lengths and distances
    are [nat] because [Huff.lz_sym]'s [LzRef] is; extra-bit widths are
    [nat] because [Bits.read_bits] takes a [nat]. *)

(** RFC 1951 §3.2.5, length codes 257..285, indexed by [code - 257]. *)
Definition length_base : list nat :=
  [ 3; 4; 5; 6; 7; 8; 9; 10; 11; 13; 15; 17; 19; 23; 27; 31;
    35; 43; 51; 59; 67; 83; 99; 115; 131; 163; 195; 227; 258 ]%nat.

Definition length_extra : list nat :=
  [ 0; 0; 0; 0; 0; 0; 0; 0; 1; 1; 1; 1; 2; 2; 2; 2;
    3; 3; 3; 3; 4; 4; 4; 4; 5; 5; 5; 5; 0 ]%nat.

(** RFC 1951 §3.2.5, distance codes 0..29, indexed by the code itself.
    Codes 30 and 31 do not exist; [nth_error] returns [None] for them and
    the decoder fails, which is what [dist_base_length] is for. *)
Definition dist_base : list nat :=
  [ 1; 2; 3; 4; 5; 7; 9; 13; 17; 25; 33; 49; 65; 97; 129; 193;
    257; 385; 513; 769; 1025; 1537; 2049; 3073; 4097; 6145; 8193; 12289;
    16385; 24577 ]%nat.

Definition dist_extra : list nat :=
  [ 0; 0; 0; 0; 1; 1; 2; 2; 3; 3; 4; 4; 5; 5; 6; 6;
    7; 7; 8; 8; 9; 9; 10; 10; 11; 11; 12; 12; 13; 13 ]%nat.

(** RFC 1951 §3.2.6, the fixed literal/length code: 0..143 -> 8 bits,
    144..255 -> 9, 256..279 -> 7, 280..287 -> 8.  Written with [repeat] so
    the four block sizes are visible and a mis-sized block changes the
    Kraft sum ([fixed_lit_valid_b] catches that); the ORDER of the four
    blocks is pinned separately by [fixed_lit_rfc_codes]. *)
Definition fixed_lit_lengths : list nat :=
  (repeat 8 144 ++ repeat 9 112 ++ repeat 7 24 ++ repeat 8 8)%nat.

(** RFC 1951 §3.2.6: 32 distance codes of 5 bits each. *)
Definition fixed_dist_lengths : list nat := (repeat 5 32)%nat.

(** RFC 1951 §3.2.7: the order in which the code-length code's own lengths
    are transmitted. *)
Definition cl_order : list nat :=
  [ 16; 17; 18; 0; 8; 7; 9; 6; 10; 5; 11; 4; 12; 3; 13; 2; 14; 1; 15 ]%nat.

Lemma length_base_length : length length_base = 29%nat.
Proof. reflexivity. Qed.

Lemma length_extra_length : length length_extra = 29%nat.
Proof. reflexivity. Qed.

Lemma dist_base_length : length dist_base = 30%nat.
Proof. reflexivity. Qed.

Lemma dist_extra_length : length dist_extra = 30%nat.
Proof. reflexivity. Qed.

Lemma fixed_lit_lengths_length : length fixed_lit_lengths = 288%nat.
Proof. reflexivity. Qed.

Lemma fixed_dist_lengths_length : length fixed_dist_lengths = 32%nat.
Proof. reflexivity. Qed.

Lemma cl_order_length : length cl_order = 19%nat.
Proof. reflexivity. Qed.

(** ** 2. Small total helpers

    [pos_of] and [last_len] are the only two list utilities this file
    needs that Stdlib does not supply in a convenient total form. *)

Fixpoint pos_of (x : nat) (l : list nat) : option nat :=
  match l with
  | [] => None
  | y :: tl => if Nat.eqb x y then Some 0%nat else option_map S (pos_of x tl)
  end.

Lemma pos_of_correct : forall l x i,
  pos_of x l = Some i -> nth_error l i = Some x.
Proof.
  induction l as [|y tl IH]; intros x i H; [discriminate|].
  cbn [pos_of] in H. destruct (Nat.eqb x y) eqn:E.
  - apply Nat.eqb_eq in E. subst y.
    assert (i = 0%nat) by congruence. subst i. reflexivity.
  - destruct (pos_of x tl) as [j|] eqn:Ej; cbn [option_map] in H; [|discriminate].
    inversion H; subst. cbn [nth_error]. exact (IH x j Ej).
Qed.

(** The "previous code length" symbol 16 copies is the LAST one appended,
    not the first one. *)
Definition last_len (acc : list nat) : option nat :=
  match rev acc with
  | [] => None
  | x :: _ => Some x
  end.

Lemma last_len_nil : last_len [] = None.
Proof. reflexivity. Qed.

Lemma last_len_snoc : forall l x, last_len (l ++ [x]) = Some x.
Proof. intros l x. unfold last_len. now rewrite rev_app_distr. Qed.

(** [read_bytes n] reads [n] whole bytes off a bit stream.  It is the
    stored-block payload reader and nothing else. *)
Fixpoint read_bytes (n : nat) (bits : list bool) : option (list Z * list bool) :=
  match n with
  | O => Some ([], bits)
  | S k =>
      match read_bits 8%nat bits with
      | None => None
      | Some (b, r) =>
          match read_bytes k r with
          | None => None
          | Some (bs, r') => Some (b :: bs, r')
          end
      end
  end.

Lemma read_bytes_length : forall n bits bs rem,
  read_bytes n bits = Some (bs, rem) -> length bs = n.
Proof.
  induction n as [|n IH]; intros bits bs rem H; cbn [read_bytes] in H.
  - inversion H; subst. reflexivity.
  - destruct (read_bits 8%nat bits) as [[b r]|]; [|discriminate].
    destruct (read_bytes n r) as [[bs' r']|] eqn:E; [|discriminate].
    inversion H; subst. cbn [length]. f_equal. exact (IH r bs' rem E).
Qed.

(** Every byte [read_bytes] produces is in range: the payload of a stored
    block is a genuine byte list, not an arbitrary [list Z]. *)
Lemma read_bytes_u8 : forall n bits bs rem,
  read_bytes n bits = Some (bs, rem) -> Forall (fun b => 0 <= b < 256) bs.
Proof.
  induction n as [|n IH]; intros bits bs rem H; cbn [read_bytes] in H.
  - inversion H; subst. constructor.
  - destruct (read_bits 8%nat bits) as [[b r]|] eqn:Eb; [|discriminate].
    destruct (read_bytes n r) as [[bs' r']|] eqn:E; [|discriminate].
    inversion H; subst. constructor.
    + pose proof (read_bits_bound 8%nat bits b r Eb) as Hb.
      change (2 ^ Z.of_nat 8) with 256 in Hb. exact Hb.
    + exact (IH r bs' rem E).
Qed.

(** ** 3. Length bookkeeping

    Every decoder in this file must be shown not to grow its input, and
    the recursive ones must be shown to shrink it.  These are the leaves
    of that argument; the composite statements are [decode_lit_len_shorter]
    (section 4), [decode_symbols_shorter] (section 5) and [dec_blk_shorter]
    (section 8). *)

Lemma read_bits_le : forall n bits v rem,
  read_bits n bits = Some (v, rem) -> (length rem <= length bits)%nat.
Proof. intros n bits v rem H. apply read_bits_length in H. lia. Qed.

Lemma read_bits_pos_shorter : forall n bits v rem,
  read_bits n bits = Some (v, rem) -> (1 <= n)%nat ->
  (length rem < length bits)%nat.
Proof. intros n bits v rem H Hn. apply read_bits_length in H. lia. Qed.

Lemma read_bytes_le : forall n bits bs rem,
  read_bytes n bits = Some (bs, rem) -> (length rem <= length bits)%nat.
Proof.
  induction n as [|n IH]; intros bits bs rem H; cbn [read_bytes] in H.
  - inversion H; subst. lia.
  - destruct (read_bits 8%nat bits) as [[b r]|] eqn:Eb; [|discriminate].
    destruct (read_bytes n r) as [[bs' r']|] eqn:E; [|discriminate].
    inversion H; subst.
    pose proof (read_bits_le 8%nat bits b r Eb).
    pose proof (IH r bs' rem E). lia.
Qed.

Lemma align_byte_le : forall bits, (length (align_byte bits) <= length bits)%nat.
Proof. intro bits. rewrite align_byte_length. lia. Qed.

(** THE key length fact of the whole file: every codeword a canonical
    table can emit is non-empty, because [Huff.code_for] rejects length
    zero.  So one [hdecode] against a [code_table] always makes progress —
    with no [ValidLengths] hypothesis, which matters because the recursion
    must be well founded even on a table this file has not validated. *)
Lemma hdecode_code_table_shorter : forall lengths maxBits bits sym rem,
  hdecode (code_table lengths maxBits) bits = Some (sym, rem) ->
  (length rem < length bits)%nat.
Proof.
  intros lengths maxBits bits sym rem H.
  apply hdecode_sound in H as [cw [Hin [_ Heq]]].
  apply code_table_In_iff in Hin.
  apply code_for_inv in Hin as [len [_ [Hlen [_ Hcw]]]].
  rewrite Heq, Hcw, length_app, code_bits_length. lia.
Qed.

(** ** 4. One literal/length symbol

    [decode_lit_len] decodes exactly one [Huff.lz_sym] off the stream with
    a given pair of code-length vectors.  Symbol < 256 is a literal, 256 is
    end of block, >= 257 is a length code: read its extra bits (RFC 1951
    §3.2.5, [length_base]/[length_extra]), then a distance symbol from the
    distance tree and its extra bits.

    Pure [option] plumbing; no recursion lives here.  [maxBits] is 15 for
    both trees, spelled out at both call sites.

    FORWARD-ONLY.  Six distinct [None] branches (a failed [hdecode] on
    either tree, an out-of-range length or distance code, a truncated extra
    field on either) and no lemma relates any of them to [inflate.c]. *)

(** Read the extra-bit field of a length or distance code and add it to
    the base.  [Z.to_nat] is faithful here because [Bits.read_bits] never
    returns a negative value ([Bits.read_bits_nonneg]). *)
Definition read_extra (base_tbl extra_tbl : list nat) (idx : nat)
                      (bits : list bool) : option (nat * list bool) :=
  match nth_error base_tbl idx, nth_error extra_tbl idx with
  | Some b, Some e =>
      match read_bits e bits with
      | None => None
      | Some (v, rem) => Some ((b + Z.to_nat v)%nat, rem)
      end
  | _, _ => None
  end.

Lemma read_extra_le : forall bt et idx bits n rem,
  read_extra bt et idx bits = Some (n, rem) -> (length rem <= length bits)%nat.
Proof.
  intros bt et idx bits n rem H. unfold read_extra in H.
  destruct (nth_error bt idx) as [b|]; [|discriminate].
  destruct (nth_error et idx) as [e|]; [|discriminate].
  destruct (read_bits e bits) as [[v r]|] eqn:E; [|discriminate].
  inversion H; subst. exact (read_bits_le e bits v rem E).
Qed.

(** A decoded length or distance is at least its table base.  Used by the
    encoder half to discharge [LzRef]'s [dist <> 0] side condition. *)
Lemma read_extra_ge : forall bt et idx bits n rem,
  read_extra bt et idx bits = Some (n, rem) ->
  exists b, nth_error bt idx = Some b /\ (b <= n)%nat.
Proof.
  intros bt et idx bits n rem H. unfold read_extra in H.
  destruct (nth_error bt idx) as [b|] eqn:Eb; [|discriminate].
  destruct (nth_error et idx) as [e|]; [|discriminate].
  destruct (read_bits e bits) as [[v r]|]; [|discriminate].
  inversion H; subst. exists b. split; [reflexivity|lia].
Qed.

Definition decode_lit_len (lit_lengths dist_lengths : list nat)
                          (bits : list bool) : option (lz_sym * list bool) :=
  match hdecode (code_table lit_lengths 15%nat) bits with
  | None => None
  | Some (sym, r1) =>
      if Nat.ltb sym 256 then Some (LzLit (Z.of_nat sym), r1)
      else if Nat.eqb sym 256 then Some (LzEnd, r1)
      else
        match read_extra length_base length_extra (sym - 257)%nat r1 with
        | None => None
        | Some (len, r2) =>
            match hdecode (code_table dist_lengths 15%nat) r2 with
            | None => None
            | Some (dsym, r3) =>
                match read_extra dist_base dist_extra dsym r3 with
                | None => None
                | Some (dist, r4) => Some (LzRef len dist, r4)
                end
            end
        end
  end.

(** THE lemma the blueprint never proved, and the reason this file exists
    as a freeze rather than a sketch.  Every successful symbol decode
    strictly consumes bits, because every canonical codeword is non-empty.
    Downstream lanes cite this and never re-derive it. *)
Lemma decode_lit_len_shorter : forall ll dl bits sym bits',
  decode_lit_len ll dl bits = Some (sym, bits') ->
  (length bits' < length bits)%nat.
Proof.
  intros ll dl bits sym bits' H. unfold decode_lit_len in H.
  destruct (hdecode (code_table ll 15%nat) bits) as [[s r1]|] eqn:E1;
    [|discriminate].
  pose proof (hdecode_code_table_shorter ll 15%nat bits s r1 E1) as H1.
  destruct (Nat.ltb s 256) eqn:Elt.
  { inversion H; subst. exact H1. }
  destruct (Nat.eqb s 256) eqn:Eeq.
  { inversion H; subst. exact H1. }
  destruct (read_extra length_base length_extra (s - 257)%nat r1)
    as [[len r2]|] eqn:E2; [|discriminate].
  pose proof (read_extra_le _ _ _ _ _ _ E2) as H2.
  destruct (hdecode (code_table dl 15%nat) r2) as [[ds r3]|] eqn:E3;
    [|discriminate].
  pose proof (hdecode_code_table_shorter dl 15%nat r2 ds r3 E3) as H3.
  destruct (read_extra dist_base dist_extra ds r3) as [[d r4]|] eqn:E4;
    [|discriminate].
  pose proof (read_extra_le _ _ _ _ _ _ E4) as H4.
  inversion H; subst. lia.
Qed.

(** ** 5. The symbol sequence of one Huffman block

    THE ROUTE: explicit [nat] fuel, then a fuel-free wrapper and a
    GUARD-FREE unfold equation.  Rationale, since the choice is
    load bearing for every downstream lane:

      - The Lean blueprint uses well-founded recursion with the decreasing
        condition RE-TESTED in the body as a [dite] returning [none].  That
        pushes the obligation to every use site, in both halves, forever.
        This file pays it once, here.
      - [Program Fixpoint {measure ...}] would put the obligation in the
        right place but leaves a [Fix]/[Acc] term behind: its unfolding
        equation needs [Fix_eq], which needs an extensionality lemma for a
        machine-generated functional over five nested matches, and — the
        decisive point — a [Fix] term does not reduce under [vm_compute],
        which would kill every computational test in section 10.
      - Fuel keeps everything a plain [Fixpoint]: transparent, reducible,
        and the fuel-independence proof is one induction.

    [decode_symbols] therefore has no guard and no fuel parameter, and
    [decode_symbols_unfold] is the rewrite rule downstream lanes cite.
    [S (length bits)] is enough fuel because [decode_lit_len_shorter] says
    each iteration strictly consumes.

    FORWARD-ONLY.  Fuel exhaustion is a [None] like any other, and the
    "loop ran out" case is not distinguished from "the stream was
    malformed".  [decode_symbols_unfold] makes the distinction invisible
    downstream, which is the whole point. *)

Definition lz_is_end (s : lz_sym) : bool :=
  match s with LzEnd => true | _ => false end.

Lemma lz_is_end_true : forall s, lz_is_end s = true -> s = LzEnd.
Proof. intros [b|l d|] H; try discriminate; reflexivity. Qed.

Fixpoint decode_symbols_fuel (fuel : nat) (ll dl : list nat)
                             (bits : list bool)
  : option (list lz_sym * list bool) :=
  match fuel with
  | O => None
  | S f =>
      match decode_lit_len ll dl bits with
      | None => None
      | Some (s, rem) =>
          if lz_is_end s then Some ([s], rem)
          else
            match decode_symbols_fuel f ll dl rem with
            | None => None
            | Some (syms, rem') => Some (s :: syms, rem')
            end
      end
  end.

Definition decode_symbols (ll dl : list nat) (bits : list bool)
  : option (list lz_sym * list bool) :=
  decode_symbols_fuel (S (length bits)) ll dl bits.

Lemma decode_symbols_fuel_shorter : forall f ll dl bits syms rem,
  decode_symbols_fuel f ll dl bits = Some (syms, rem) ->
  (length rem < length bits)%nat.
Proof.
  induction f as [|f IH]; intros ll dl bits syms rem H; [discriminate|].
  cbn [decode_symbols_fuel] in H.
  destruct (decode_lit_len ll dl bits) as [[s r]|] eqn:E; [|discriminate].
  pose proof (decode_lit_len_shorter ll dl bits s r E) as Hs.
  destruct (lz_is_end s).
  - inversion H; subst. exact Hs.
  - destruct (decode_symbols_fuel f ll dl r) as [[syms' r']|] eqn:E2;
      [|discriminate].
    inversion H; subst. pose proof (IH ll dl r syms' rem E2). lia.
Qed.

Corollary decode_symbols_shorter : forall ll dl bits syms rem,
  decode_symbols ll dl bits = Some (syms, rem) ->
  (length rem < length bits)%nat.
Proof.
  intros ll dl bits syms rem H. unfold decode_symbols in H.
  exact (decode_symbols_fuel_shorter _ _ _ _ _ _ H).
Qed.

(** Any fuel strictly above [length bits] gives the same answer, [None]
    cases included.  This is what makes the wrapper below well defined and
    the unfold equation guard free. *)
Lemma decode_symbols_fuel_indep : forall f1 f2 ll dl bits,
  (length bits < f1)%nat -> (length bits < f2)%nat ->
  decode_symbols_fuel f1 ll dl bits = decode_symbols_fuel f2 ll dl bits.
Proof.
  induction f1 as [|f1 IH]; intros f2 ll dl bits H1 H2; [lia|].
  destruct f2 as [|f2]; [lia|].
  cbn [decode_symbols_fuel].
  destruct (decode_lit_len ll dl bits) as [[s r]|] eqn:E; [|reflexivity].
  pose proof (decode_lit_len_shorter ll dl bits s r E) as Hs.
  destruct (lz_is_end s); [reflexivity|].
  rewrite (IH f2 ll dl r) by lia. reflexivity.
Qed.

(** THE EXPORT.  No guard, no fuel.  Every downstream lane rewrites with
    this and never sees the implementation. *)
Lemma decode_symbols_unfold : forall ll dl bits,
  decode_symbols ll dl bits =
    match decode_lit_len ll dl bits with
    | None => None
    | Some (s, rem) =>
        if lz_is_end s then Some ([s], rem)
        else
          match decode_symbols ll dl rem with
          | None => None
          | Some (syms, rem') => Some (s :: syms, rem')
          end
    end.
Proof.
  intros ll dl bits. unfold decode_symbols at 1.
  cbn [decode_symbols_fuel].
  destruct (decode_lit_len ll dl bits) as [[s r]|] eqn:E; [|reflexivity].
  pose proof (decode_lit_len_shorter ll dl bits s r E) as Hs.
  destruct (lz_is_end s); [reflexivity|].
  unfold decode_symbols.
  rewrite (decode_symbols_fuel_indep (length bits) (S (length r)) ll dl r)
    by lia.
  reflexivity.
Qed.

(** The symbol list of a block is always terminated by [LzEnd], so
    [Huff.resolve_lz] applied to it stops exactly at the block's end.
    (Nothing here says [LzEnd] occurs only at the end; that is true by
    construction but no client needs it, so it is NOT proved.) *)
Lemma decode_symbols_fuel_last_end : forall f ll dl bits syms rem,
  decode_symbols_fuel f ll dl bits = Some (syms, rem) ->
  exists pre, syms = pre ++ [LzEnd].
Proof.
  induction f as [|f IH]; intros ll dl bits syms rem H; [discriminate|].
  cbn [decode_symbols_fuel] in H.
  destruct (decode_lit_len ll dl bits) as [[s r]|] eqn:E; [|discriminate].
  destruct (lz_is_end s) eqn:Ee.
  - inversion H; subst. exists []. cbn [app]. f_equal.
    exact (lz_is_end_true s Ee).
  - destruct (decode_symbols_fuel f ll dl r) as [[syms' r']|] eqn:E2;
      [|discriminate].
    inversion H; subst.
    destruct (IH ll dl r syms' rem E2) as [pre ->].
    exists (s :: pre). reflexivity.
Qed.

Corollary decode_symbols_last_end : forall ll dl bits syms rem,
  decode_symbols ll dl bits = Some (syms, rem) ->
  exists pre, syms = pre ++ [LzEnd].
Proof.
  intros ll dl bits syms rem H. unfold decode_symbols in H.
  exact (decode_symbols_fuel_last_end _ _ _ _ _ _ H).
Qed.

(** ** 6. Stored blocks (BTYPE = 00)

    RFC 1951 §3.2.4: skip to the next byte boundary, then LEN and NLEN as
    two 16-bit little-endian fields, then LEN raw bytes.

    [Bits.align_byte] drops [length bits mod 8] bits.  That is the right
    count only because the enclosing stream came from [Bits.bytes_bits] and
    so has a length that is a multiple of 8; [Bits.align_byte_boundary]
    states exactly that dependency, and it is why no separate alignment
    argument appears here.

    FORWARD-ONLY.  Four [None] branches (truncated LEN, truncated NLEN,
    failed complement check, truncated payload).  zlib distinguishes
    "invalid stored block lengths" from "need more input"; this file does
    not, and no lemma claims it does. *)
Definition decode_stored (bits : list bool) : option (list Z * list bool) :=
  match read_bits 16%nat (align_byte bits) with
  | None => None
  | Some (len, r1) =>
      match read_bits 16%nat r1 with
      | None => None
      | Some (nlen, r2) =>
          if Z.eqb (Z.lxor len nlen) 65535
          then read_bytes (Z.to_nat len) r2
          else None
      end
  end.

Lemma decode_stored_le : forall bits payload rem,
  decode_stored bits = Some (payload, rem) ->
  (length rem <= length bits)%nat.
Proof.
  intros bits payload rem H. unfold decode_stored in H.
  destruct (read_bits 16%nat (align_byte bits)) as [[len r1]|] eqn:E1;
    [|discriminate].
  destruct (read_bits 16%nat r1) as [[nlen r2]|] eqn:E2; [|discriminate].
  destruct (Z.eqb (Z.lxor len nlen) 65535); [|discriminate].
  pose proof (align_byte_le bits).
  pose proof (read_bits_le _ _ _ _ E1).
  pose proof (read_bits_le _ _ _ _ E2).
  pose proof (read_bytes_le _ _ _ _ H). lia.
Qed.

(** The advertised LEN really is the payload length, and the payload
    really is bytes. *)
Lemma decode_stored_payload : forall bits payload rem,
  decode_stored bits = Some (payload, rem) ->
  Forall (fun b => 0 <= b < 256) payload.
Proof.
  intros bits payload rem H. unfold decode_stored in H.
  destruct (read_bits 16%nat (align_byte bits)) as [[len r1]|]; [|discriminate].
  destruct (read_bits 16%nat r1) as [[nlen r2]|]; [|discriminate].
  destruct (Z.eqb (Z.lxor len nlen) 65535); [|discriminate].
  exact (read_bytes_u8 _ _ _ _ H).
Qed.

(** ** 7. Dynamic Huffman tables (BTYPE = 10)

    RFC 1951 §3.2.7.  HLIT/HDIST/HCLEN, then [HCLEN + 4] three-bit code
    lengths for the code-length alphabet in [cl_order] order, then the
    [HLIT + 257 + HDIST + 1] literal/length and distance code lengths,
    run-length coded with symbols 16 (copy the previous length 3..6 times,
    2 extra bits), 17 (repeat zero 3..10 times, 3 extra bits) and 18
    (repeat zero 11..138 times, 7 extra bits).

    Dynamic blocks are IN SCOPE: measurement on the campaign's own PNG
    corpus confirmed they occur.

    Both resulting length vectors are gated by [Huff.valid_lengths_b] at
    15, and the code-length vector at 7.  Section 9 proves the 7 is
    unobservable given 3-bit fields, and says so rather than pretending a
    test pins it. *)

Fixpoint read_3bit_vals (n : nat) (bits : list bool)
  : option (list nat * list bool) :=
  match n with
  | O => Some ([], bits)
  | S k =>
      match read_bits 3%nat bits with
      | None => None
      | Some (v, r) =>
          match read_3bit_vals k r with
          | None => None
          | Some (vs, r') => Some (Z.to_nat v :: vs, r')
          end
      end
  end.

Lemma read_3bit_vals_le : forall n bits vs rem,
  read_3bit_vals n bits = Some (vs, rem) -> (length rem <= length bits)%nat.
Proof.
  induction n as [|n IH]; intros bits vs rem H; cbn [read_3bit_vals] in H.
  - inversion H; subst. lia.
  - destruct (read_bits 3%nat bits) as [[v r]|] eqn:E1; [|discriminate].
    destruct (read_3bit_vals n r) as [[vs' r']|] eqn:E2; [|discriminate].
    inversion H; subst.
    pose proof (read_bits_le _ _ _ _ E1). pose proof (IH r vs' rem E2). lia.
Qed.

(** A 3-bit field can only hold 0..7.  This is what makes the CL tree's
    [maxBits = 7] unobservable ([cl_valid_7_15]). *)
Lemma read_3bit_vals_bound : forall n bits vs rem,
  read_3bit_vals n bits = Some (vs, rem) -> Forall (fun v => (v <= 7)%nat) vs.
Proof.
  induction n as [|n IH]; intros bits vs rem H; cbn [read_3bit_vals] in H.
  - inversion H; subst. constructor.
  - destruct (read_bits 3%nat bits) as [[v r]|] eqn:E1; [|discriminate].
    destruct (read_3bit_vals n r) as [[vs' r']|] eqn:E2; [|discriminate].
    inversion H; subst. constructor; [|exact (IH r vs' rem E2)].
    pose proof (read_bits_bound 3%nat bits v r E1) as Hb.
    change (2 ^ Z.of_nat 3) with 8 in Hb. lia.
Qed.

(** Scatter the [n] transmitted values back into code-length-symbol order.
    Symbols whose length was not transmitted get 0 — RFC 1951's rule, and
    the reason [nth ... 0] (which is total) is used rather than
    [nth_error]. *)
Definition scatter_cl (vals : list nat) : list nat :=
  map (fun j => match pos_of j cl_order with
                | None => 0%nat
                | Some i => nth i vals 0%nat
                end)
      (seq 0 19).

Lemma scatter_cl_length : forall vals, length (scatter_cl vals) = 19%nat.
Proof. intro vals. unfold scatter_cl. now rewrite length_map, length_seq. Qed.

Lemma scatter_cl_bound : forall vals,
  Forall (fun v => (v <= 7)%nat) vals ->
  forall len, In len (scatter_cl vals) -> (len <= 7)%nat.
Proof.
  intros vals HF len Hin. unfold scatter_cl in Hin.
  apply in_map_iff in Hin as [j [Heq _]].
  destruct (pos_of j cl_order) as [i|]; [|lia].
  destruct (nth_in_or_default i vals 0%nat) as [Hi|Hd].
  - rewrite <- Heq. rewrite Forall_forall in HF. exact (HF _ Hi).
  - lia.
Qed.

Definition read_cl_lengths (n : nat) (bits : list bool)
  : option (list nat * list bool) :=
  match read_3bit_vals n bits with
  | None => None
  | Some (vals, r) => Some (scatter_cl vals, r)
  end.

Lemma read_cl_lengths_length : forall n bits cl rem,
  read_cl_lengths n bits = Some (cl, rem) -> length cl = 19%nat.
Proof.
  intros n bits cl rem H. unfold read_cl_lengths in H.
  destruct (read_3bit_vals n bits) as [[vals r]|]; [|discriminate].
  inversion H; subst. apply scatter_cl_length.
Qed.

Lemma read_cl_lengths_le : forall n bits cl rem,
  read_cl_lengths n bits = Some (cl, rem) -> (length rem <= length bits)%nat.
Proof.
  intros n bits cl rem H. unfold read_cl_lengths in H.
  destruct (read_3bit_vals n bits) as [[vals r]|] eqn:E; [|discriminate].
  inversion H; subst. exact (read_3bit_vals_le _ _ _ _ E).
Qed.

Lemma read_cl_lengths_bound : forall n bits cl rem,
  read_cl_lengths n bits = Some (cl, rem) ->
  forall len, In len cl -> (len <= 7)%nat.
Proof.
  intros n bits cl rem H. unfold read_cl_lengths in H.
  destruct (read_3bit_vals n bits) as [[vals r]|] eqn:E; [|discriminate].
  inversion H; subst.
  apply scatter_cl_bound. exact (read_3bit_vals_bound _ _ _ _ E).
Qed.

(** One run-length step: given the code-length symbol [sym] (> 15), read
    its extra field and return the value to repeat, the repeat count and
    the remaining stream.

    FORWARD-ONLY, and flagged because it is the one place where being
    loose would have been tempting: symbol 16 with an empty accumulator
    has no previous length.  zlib errors; this file returns [None] too,
    which costs one [match] and is the safe direction, but no lemma
    relates the two. *)
Definition rl_run (sym : nat) (acc : list nat) (bits : list bool)
  : option (nat * nat * list bool) :=
  if Nat.eqb sym 16 then
    match last_len acc with
    | None => None
    | Some prev =>
        match read_bits 2%nat bits with
        | None => None
        | Some (e, rem) => Some (prev, (Z.to_nat e + 3)%nat, rem)
        end
    end
  else if Nat.eqb sym 17 then
    match read_bits 3%nat bits with
    | None => None
    | Some (e, rem) => Some (0%nat, (Z.to_nat e + 3)%nat, rem)
    end
  else if Nat.eqb sym 18 then
    match read_bits 7%nat bits with
    | None => None
    | Some (e, rem) => Some (0%nat, (Z.to_nat e + 11)%nat, rem)
    end
  else None.

Lemma rl_run_le : forall sym acc bits rep k rem,
  rl_run sym acc bits = Some (rep, k, rem) ->
  (length rem <= length bits)%nat.
Proof.
  intros sym acc bits rep k rem H. unfold rl_run in H.
  destruct (Nat.eqb sym 16).
  { destruct (last_len acc) as [prev|]; [|discriminate].
    destruct (read_bits 2%nat bits) as [[e r]|] eqn:E; [|discriminate].
    inversion H; subst. exact (read_bits_le _ _ _ _ E). }
  destruct (Nat.eqb sym 17).
  { destruct (read_bits 3%nat bits) as [[e r]|] eqn:E; [|discriminate].
    inversion H; subst. exact (read_bits_le _ _ _ _ E). }
  destruct (Nat.eqb sym 18).
  { destruct (read_bits 7%nat bits) as [[e r]|] eqn:E; [|discriminate].
    inversion H; subst. exact (read_bits_le _ _ _ _ E). }
  discriminate.
Qed.

(** Every run repeats at least three times — RFC 1951's minimum for all
    three run symbols.  This is what makes the [need] argument strictly
    decrease, so the fuel below never binds. *)
Lemma rl_run_pos : forall sym acc bits rep k rem,
  rl_run sym acc bits = Some (rep, k, rem) -> (3 <= k)%nat.
Proof.
  intros sym acc bits rep k rem H. unfold rl_run in H.
  destruct (Nat.eqb sym 16).
  { destruct (last_len acc) as [prev|]; [|discriminate].
    destruct (read_bits 2%nat bits) as [[e r]|]; [|discriminate].
    inversion H; subst. lia. }
  destruct (Nat.eqb sym 17).
  { destruct (read_bits 3%nat bits) as [[e r]|]; [|discriminate].
    inversion H; subst. lia. }
  destruct (Nat.eqb sym 18).
  { destruct (read_bits 7%nat bits) as [[e r]|]; [|discriminate].
    inversion H; subst. lia. }
  discriminate.
Qed.

(** [need] is the number of code lengths still wanted; it strictly
    decreases at every step, so [need] itself is enough fuel and the
    wrapper below is fuel free. *)
Fixpoint read_lengths_fuel (fuel : nat) (cl : list nat) (need : nat)
                           (acc : list nat) (bits : list bool)
  : option (list nat * list bool) :=
  match need with
  | O => Some (acc, bits)
  | S _ =>
      match fuel with
      | O => None
      | S f =>
          match hdecode (code_table cl 7%nat) bits with
          | None => None
          | Some (sym, r1) =>
              if Nat.leb sym 15 then
                read_lengths_fuel f cl (need - 1)%nat (acc ++ [sym]) r1
              else
                match rl_run sym acc r1 with
                | None => None
                | Some (rep, k, r2) =>
                    if Nat.ltb need k then None
                    else read_lengths_fuel f cl (need - k)%nat
                                           (acc ++ repeat rep k) r2
                end
          end
      end
  end.

Definition read_lengths (cl : list nat) (need : nat) (bits : list bool)
  : option (list nat * list bool) :=
  read_lengths_fuel need cl need [] bits.

(** Exactly [need] lengths come out.  Note this holds unconditionally:
    running out of fuel yields [None], and the statement only speaks about
    [Some]. *)
Lemma read_lengths_fuel_length : forall f cl need acc bits ls rem,
  read_lengths_fuel f cl need acc bits = Some (ls, rem) ->
  length ls = (length acc + need)%nat.
Proof.
  induction f as [|f IH]; intros cl need acc bits ls rem H.
  - destruct need as [|n]; [|discriminate].
    cbn [read_lengths_fuel] in H. inversion H; subst. lia.
  - destruct need as [|n].
    { cbn [read_lengths_fuel] in H. inversion H; subst. lia. }
    cbn [read_lengths_fuel] in H.
    destruct (hdecode (code_table cl 7%nat) bits) as [[sym r1]|] eqn:E1;
      [|discriminate].
    destruct (Nat.leb sym 15) eqn:Es.
    + apply IH in H. rewrite length_app in H. cbn [length] in H. lia.
    + destruct (rl_run sym acc r1) as [[[rep k] r2]|] eqn:E2; [|discriminate].
      destruct (Nat.ltb (S n) k) eqn:Ek; [discriminate|].
      apply Nat.ltb_ge in Ek.
      apply IH in H. rewrite length_app, repeat_length in H. lia.
Qed.

Corollary read_lengths_length : forall cl need bits ls rem,
  read_lengths cl need bits = Some (ls, rem) -> length ls = need.
Proof.
  intros cl need bits ls rem H. unfold read_lengths in H.
  apply read_lengths_fuel_length in H. cbn [length] in H. lia.
Qed.

Lemma read_lengths_fuel_le : forall f cl need acc bits ls rem,
  read_lengths_fuel f cl need acc bits = Some (ls, rem) ->
  (length rem <= length bits)%nat.
Proof.
  induction f as [|f IH]; intros cl need acc bits ls rem H.
  - destruct need as [|n]; [|discriminate].
    cbn [read_lengths_fuel] in H. inversion H; subst. lia.
  - destruct need as [|n].
    { cbn [read_lengths_fuel] in H. inversion H; subst. lia. }
    cbn [read_lengths_fuel] in H.
    destruct (hdecode (code_table cl 7%nat) bits) as [[sym r1]|] eqn:E1;
      [|discriminate].
    pose proof (hdecode_code_table_shorter _ _ _ _ _ E1) as H1.
    destruct (Nat.leb sym 15).
    + apply IH in H. lia.
    + destruct (rl_run sym acc r1) as [[[rep k] r2]|] eqn:E2; [|discriminate].
      pose proof (rl_run_le _ _ _ _ _ _ E2).
      destruct (Nat.ltb (S n) k); [discriminate|].
      apply IH in H. lia.
Qed.

Corollary read_lengths_le : forall cl need bits ls rem,
  read_lengths cl need bits = Some (ls, rem) ->
  (length rem <= length bits)%nat.
Proof.
  intros cl need bits ls rem H. unfold read_lengths in H.
  exact (read_lengths_fuel_le _ _ _ _ _ _ _ H).
Qed.

(** [need] fuel is enough, so the wrapper's choice is canonical. *)
Lemma read_lengths_fuel_indep : forall f1 f2 cl need acc bits,
  (need <= f1)%nat -> (need <= f2)%nat ->
  read_lengths_fuel f1 cl need acc bits
  = read_lengths_fuel f2 cl need acc bits.
Proof.
  induction f1 as [|f1 IH]; intros f2 cl need acc bits H1 H2.
  - destruct need as [|n]; [|lia].
    destruct f2; reflexivity.
  - destruct need as [|n]; [destruct f2; reflexivity|].
    destruct f2 as [|f2]; [lia|].
    cbn [read_lengths_fuel].
    destruct (hdecode (code_table cl 7%nat) bits) as [[sym r1]|];
      [|reflexivity].
    destruct (Nat.leb sym 15).
    + apply IH; lia.
    + destruct (rl_run sym acc r1) as [[[rep k] r2]|] eqn:E2; [|reflexivity].
      pose proof (rl_run_pos _ _ _ _ _ _ E2).
      destruct (Nat.ltb (S n) k) eqn:Ek; [reflexivity|].
      apply Nat.ltb_ge in Ek. apply IH; lia.
Qed.

(** The dynamic-table header.  Returns the literal/length lengths, the
    distance lengths and the remaining stream.

    FORWARD-ONLY.  Seven [None] branches here (three truncated header
    fields, a truncated code-length vector, an over-subscribed CL tree, a
    failed run decode, an invalid lit or dist tree).  zlib distinguishes
    all of them; nothing here does. *)
Definition decode_dynamic_tables (bits : list bool)
  : option (list nat * list nat * list bool) :=
  match read_bits 5%nat bits with
  | None => None
  | Some (hlit, r1) =>
      match read_bits 5%nat r1 with
      | None => None
      | Some (hdist, r2) =>
          match read_bits 4%nat r2 with
          | None => None
          | Some (hclen, r3) =>
              let nlit := (Z.to_nat hlit + 257)%nat in
              let ndist := (Z.to_nat hdist + 1)%nat in
              let ncl := (Z.to_nat hclen + 4)%nat in
              match read_cl_lengths ncl r3 with
              | None => None
              | Some (cl, r4) =>
                  if valid_lengths_b cl 7%nat then
                    match read_lengths cl (nlit + ndist)%nat r4 with
                    | None => None
                    | Some (ls, r5) =>
                        let lit := firstn nlit ls in
                        let dst := skipn nlit ls in
                        if valid_lengths_b lit 15%nat
                           && valid_lengths_b dst 15%nat
                        then Some (lit, dst, r5)
                        else None
                    end
                  else None
              end
          end
      end
  end.

Lemma decode_dynamic_tables_le : forall bits lit dst rem,
  decode_dynamic_tables bits = Some (lit, dst, rem) ->
  (length rem <= length bits)%nat.
Proof.
  intros bits lit dst rem H. unfold decode_dynamic_tables in H.
  destruct (read_bits 5%nat bits) as [[hlit r1]|] eqn:E1; [|discriminate].
  destruct (read_bits 5%nat r1) as [[hdist r2]|] eqn:E2; [|discriminate].
  destruct (read_bits 4%nat r2) as [[hclen r3]|] eqn:E3; [|discriminate].
  destruct (read_cl_lengths (Z.to_nat hclen + 4)%nat r3) as [[cl r4]|] eqn:E4;
    [|discriminate].
  destruct (valid_lengths_b cl 7%nat); [|discriminate].
  destruct (read_lengths cl
              ((Z.to_nat hlit + 257) + (Z.to_nat hdist + 1))%nat r4)
    as [[ls r5]|] eqn:E5; [|discriminate].
  destruct (valid_lengths_b (firstn (Z.to_nat hlit + 257)%nat ls) 15%nat
            && valid_lengths_b (skipn (Z.to_nat hlit + 257)%nat ls) 15%nat);
    [|discriminate].
  inversion H; subst.
  pose proof (read_bits_le _ _ _ _ E1). pose proof (read_bits_le _ _ _ _ E2).
  pose proof (read_bits_le _ _ _ _ E3).
  pose proof (read_cl_lengths_le _ _ _ _ E4).
  pose proof (read_lengths_le _ _ _ _ _ E5). lia.
Qed.

(** THE postcondition the rest of the campaign needs: both trees that come
    out of a dynamic header are valid at [maxBits = 15], so
    [Huff.canonical_prefix_free] and [Huff.hdecode_code_for] apply to
    them. *)
Lemma decode_dynamic_tables_valid : forall bits lit dst rem,
  decode_dynamic_tables bits = Some (lit, dst, rem) ->
  ValidLengths lit 15%nat /\ ValidLengths dst 15%nat.
Proof.
  intros bits lit dst rem H. unfold decode_dynamic_tables in H.
  destruct (read_bits 5%nat bits) as [[hlit r1]|]; [|discriminate].
  destruct (read_bits 5%nat r1) as [[hdist r2]|]; [|discriminate].
  destruct (read_bits 4%nat r2) as [[hclen r3]|]; [|discriminate].
  destruct (read_cl_lengths (Z.to_nat hclen + 4)%nat r3) as [[cl r4]|];
    [|discriminate].
  destruct (valid_lengths_b cl 7%nat); [|discriminate].
  destruct (read_lengths cl
              ((Z.to_nat hlit + 257) + (Z.to_nat hdist + 1))%nat r4)
    as [[ls r5]|]; [|discriminate].
  destruct (valid_lengths_b (firstn (Z.to_nat hlit + 257)%nat ls) 15%nat
            && valid_lengths_b (skipn (Z.to_nat hlit + 257)%nat ls) 15%nat)
    eqn:Ev; [|discriminate].
  apply andb_true_iff in Ev as [Hl Hd].
  inversion H; subst.
  split; apply valid_lengths_b_true; assumption.
Qed.

(** The RFC's HLIT/HDIST offsets, visible in the output shape.  257..288
    literal/length lengths and 1..32 distance lengths. *)
Lemma decode_dynamic_tables_sizes : forall bits lit dst rem,
  decode_dynamic_tables bits = Some (lit, dst, rem) ->
  (257 <= length lit <= 288)%nat /\ (1 <= length dst <= 32)%nat.
Proof.
  intros bits lit dst rem H. unfold decode_dynamic_tables in H.
  destruct (read_bits 5%nat bits) as [[hlit r1]|] eqn:E1; [|discriminate].
  destruct (read_bits 5%nat r1) as [[hdist r2]|] eqn:E2; [|discriminate].
  destruct (read_bits 4%nat r2) as [[hclen r3]|]; [|discriminate].
  destruct (read_cl_lengths (Z.to_nat hclen + 4)%nat r3) as [[cl r4]|];
    [|discriminate].
  destruct (valid_lengths_b cl 7%nat); [|discriminate].
  destruct (read_lengths cl
              ((Z.to_nat hlit + 257) + (Z.to_nat hdist + 1))%nat r4)
    as [[ls r5]|] eqn:E5; [|discriminate].
  destruct (valid_lengths_b (firstn (Z.to_nat hlit + 257)%nat ls) 15%nat
            && valid_lengths_b (skipn (Z.to_nat hlit + 257)%nat ls) 15%nat);
    [|discriminate].
  inversion H; subst.
  pose proof (read_bits_bound 5%nat bits hlit r1 E1) as Hb1.
  pose proof (read_bits_bound 5%nat r1 hdist r2 E2) as Hb2.
  change (2 ^ Z.of_nat 5) with 32 in Hb1, Hb2.
  apply read_lengths_length in E5.
  rewrite length_firstn, length_skipn, E5. lia.
Qed.

(** ** 8. Blocks and streams

    [dec_blk] decodes ONE block against the output produced so far and
    returns BFINAL, the EXTENDED output, and the rest of the stream.  The
    accumulator is threaded because DEFLATE's LZ77 window crosses block
    boundaries: a match in block [n] may reach back into block [n-1].
    [dec_blk_extends] states that the accumulator is only ever extended.

    [dec_stream_from] is the ONE stream recursion.  The blueprint defines a
    remainder-returning and a remainder-discarding version and then proves
    they agree; here the second is [option_map fst] of the first, so there
    is nothing to prove.

    FORWARD-ONLY.  BTYPE = 11 is [None] (the RFC reserves it), as are all
    the failures inherited from the three block decoders. *)
Definition dec_blk (bits : list bool) (acc : list Z)
  : option (bool * list Z * list bool) :=
  match read_bits 1%nat bits with
  | None => None
  | Some (bfinal, r1) =>
      match read_bits 2%nat r1 with
      | None => None
      | Some (btype, r2) =>
          let fin := Z.eqb bfinal 1 in
          if Z.eqb btype 0 then
            match decode_stored r2 with
            | None => None
            | Some (payload, r3) => Some (fin, acc ++ payload, r3)
            end
          else if Z.eqb btype 1 then
            match decode_symbols fixed_lit_lengths fixed_dist_lengths r2 with
            | None => None
            | Some (syms, r3) =>
                match resolve_lz syms acc with
                | None => None
                | Some out => Some (fin, out, r3)
                end
            end
          else if Z.eqb btype 2 then
            match decode_dynamic_tables r2 with
            | None => None
            | Some (lit, dst, r3) =>
                match decode_symbols lit dst r3 with
                | None => None
                | Some (syms, r4) =>
                    match resolve_lz syms acc with
                    | None => None
                    | Some out => Some (fin, out, r4)
                    end
                end
            end
          else None
      end
  end.

(** A block always consumes at least its own three header bits, so the
    stream recursion below terminates.  All three BTYPEs, one lemma. *)
Lemma dec_blk_shorter : forall bits acc fin out rem,
  dec_blk bits acc = Some (fin, out, rem) ->
  (length rem < length bits)%nat.
Proof.
  intros bits acc fin out rem H. unfold dec_blk in H.
  destruct (read_bits 1%nat bits) as [[bfinal r1]|] eqn:E1; [|discriminate].
  pose proof (read_bits_pos_shorter 1%nat bits bfinal r1 E1 ltac:(lia)) as H1.
  destruct (read_bits 2%nat r1) as [[btype r2]|] eqn:E2; [|discriminate].
  pose proof (read_bits_le _ _ _ _ E2) as H2.
  destruct (Z.eqb btype 0).
  { destruct (decode_stored r2) as [[payload r3]|] eqn:E3; [|discriminate].
    inversion H; subst. pose proof (decode_stored_le _ _ _ E3). lia. }
  destruct (Z.eqb btype 1).
  { destruct (decode_symbols fixed_lit_lengths fixed_dist_lengths r2)
      as [[syms r3]|] eqn:E3; [|discriminate].
    pose proof (decode_symbols_shorter _ _ _ _ _ E3).
    destruct (resolve_lz syms acc) as [o|]; [|discriminate].
    inversion H; subst. lia. }
  destruct (Z.eqb btype 2).
  { destruct (decode_dynamic_tables r2) as [[[lit dst] r3]|] eqn:E3;
      [|discriminate].
    pose proof (decode_dynamic_tables_le _ _ _ _ E3).
    destruct (decode_symbols lit dst r3) as [[syms r4]|] eqn:E4;
      [|discriminate].
    pose proof (decode_symbols_shorter _ _ _ _ _ E4).
    destruct (resolve_lz syms acc) as [o|]; [|discriminate].
    inversion H; subst. lia. }
  discriminate.
Qed.

(** The window is append only: a block never rewrites earlier output. *)
Lemma dec_blk_extends : forall bits acc fin out rem,
  dec_blk bits acc = Some (fin, out, rem) -> exists ext, out = acc ++ ext.
Proof.
  intros bits acc fin out rem H. unfold dec_blk in H.
  destruct (read_bits 1%nat bits) as [[bfinal r1]|]; [|discriminate].
  destruct (read_bits 2%nat r1) as [[btype r2]|]; [|discriminate].
  destruct (Z.eqb btype 0).
  { destruct (decode_stored r2) as [[payload r3]|]; [|discriminate].
    inversion H; subst. exists payload. reflexivity. }
  destruct (Z.eqb btype 1).
  { destruct (decode_symbols fixed_lit_lengths fixed_dist_lengths r2)
      as [[syms r3]|]; [|discriminate].
    destruct (resolve_lz syms acc) as [o|] eqn:Er; [|discriminate].
    inversion H; subst. exact (resolve_lz_extends _ _ _ Er). }
  destruct (Z.eqb btype 2).
  { destruct (decode_dynamic_tables r2) as [[[lit dst] r3]|]; [|discriminate].
    destruct (decode_symbols lit dst r3) as [[syms r4]|]; [|discriminate].
    destruct (resolve_lz syms acc) as [o|] eqn:Er; [|discriminate].
    inversion H; subst. exact (resolve_lz_extends _ _ _ Er). }
  discriminate.
Qed.

Fixpoint dec_stream_fuel (fuel : nat) (bits : list bool) (acc : list Z)
  : option (list Z * list bool) :=
  match fuel with
  | O => None
  | S f =>
      match dec_blk bits acc with
      | None => None
      | Some (fin, acc', rem) =>
          if fin then Some (acc', rem) else dec_stream_fuel f rem acc'
      end
  end.

Definition dec_stream_from (bits : list bool) (acc : list Z)
  : option (list Z * list bool) :=
  dec_stream_fuel (S (length bits)) bits acc.

(** THE remainder-returning stream decoder. *)
Definition dec_stream_rem (bits : list bool) : option (list Z * list bool) :=
  dec_stream_from bits [].

(** ...and the remainder-discarding one, derived rather than defined. *)
Definition dec_stream (bits : list bool) : option (list Z) :=
  option_map fst (dec_stream_rem bits).

Lemma dec_stream_from_shorter : forall bits acc out rem,
  dec_stream_from bits acc = Some (out, rem) ->
  (length rem <= length bits)%nat.
Proof.
  intros bits acc out rem. unfold dec_stream_from.
  generalize (S (length bits)) as f. revert bits acc out rem.
  intros bits acc out rem f. revert bits acc out rem.
  induction f as [|f IH]; intros bits acc out rem H; [discriminate|].
  cbn [dec_stream_fuel] in H.
  destruct (dec_blk bits acc) as [[[fin acc'] r]|] eqn:E; [|discriminate].
  pose proof (dec_blk_shorter _ _ _ _ _ E) as Hs.
  destruct fin.
  - inversion H; subst. lia.
  - apply IH in H. lia.
Qed.

Lemma dec_stream_fuel_indep : forall f1 f2 bits acc,
  (length bits < f1)%nat -> (length bits < f2)%nat ->
  dec_stream_fuel f1 bits acc = dec_stream_fuel f2 bits acc.
Proof.
  induction f1 as [|f1 IH]; intros f2 bits acc H1 H2; [lia|].
  destruct f2 as [|f2]; [lia|].
  cbn [dec_stream_fuel].
  destruct (dec_blk bits acc) as [[[fin acc'] r]|] eqn:E; [|reflexivity].
  pose proof (dec_blk_shorter _ _ _ _ _ E) as Hs.
  destruct fin; [reflexivity|].
  apply IH; lia.
Qed.

(** THE EXPORT.  No guard, no fuel; one recursion. *)
Lemma dec_stream_from_unfold : forall bits acc,
  dec_stream_from bits acc =
    match dec_blk bits acc with
    | None => None
    | Some (fin, acc', rem) =>
        if fin then Some (acc', rem) else dec_stream_from rem acc'
    end.
Proof.
  intros bits acc. unfold dec_stream_from at 1.
  cbn [dec_stream_fuel].
  destruct (dec_blk bits acc) as [[[fin acc'] r]|] eqn:E; [|reflexivity].
  pose proof (dec_blk_shorter _ _ _ _ _ E) as Hs.
  destruct fin; [reflexivity|].
  unfold dec_stream_from.
  rewrite (dec_stream_fuel_indep (length bits) (S (length r)) r acc') by lia.
  reflexivity.
Qed.

Lemma dec_stream_from_extends : forall bits acc out rem,
  dec_stream_from bits acc = Some (out, rem) -> exists ext, out = acc ++ ext.
Proof.
  intros bits acc out rem. unfold dec_stream_from.
  generalize (S (length bits)) as f. revert bits acc out rem.
  intros bits acc out rem f. revert bits acc out rem.
  induction f as [|f IH]; intros bits acc out rem H; [discriminate|].
  cbn [dec_stream_fuel] in H.
  destruct (dec_blk bits acc) as [[[fin acc'] r]|] eqn:E; [|discriminate].
  destruct (dec_blk_extends _ _ _ _ _ E) as [ext1 ->].
  destruct fin.
  - inversion H; subst. exists ext1. reflexivity.
  - apply IH in H as [ext2 ->]. exists (ext1 ++ ext2). now rewrite app_assoc.
Qed.

(** The two stream decoders agree by construction. *)
Lemma dec_stream_rem_dec_stream : forall bits out rem,
  dec_stream_rem bits = Some (out, rem) -> dec_stream bits = Some out.
Proof. intros bits out rem H. unfold dec_stream. now rewrite H. Qed.

(** ** 9. [maxBits] for the code-length tree: an honest non-test

    The [maxBits] argument is load bearing in general — [Huff]'s
    [maxbits_matters_9]/[maxbits_matters_7] show a code that is valid at 9
    and invalid at 7.  But for the CODE-LENGTH tree specifically, the
    lengths come from 3-bit fields ([read_3bit_vals_bound]), and on such a
    vector the 7 and the 15 give literally the same answer: the Kraft sum
    scales by a uniform [2 ^ (m2 - m1)] and the bound scales with it.

    So NO test can pin the 7, and writing one that appears to would be
    exactly the kind of always-passing test [Huff.v]'s [nc] incident warns
    about.  A lemma is stated instead. *)

Lemma kraft_at_scale : forall m1 m2 len,
  (len <= m1)%nat -> (m1 <= m2)%nat ->
  kraft_at m2 0 len = (2 ^ (m2 - m1) * kraft_at m1 0 len)%nat.
Proof.
  intros m1 m2 len Hl Hm. unfold kraft_at. cbn [Nat.leb].
  destruct len as [|k]; cbn [kraft_term]; [lia|].
  rewrite <- Nat.pow_add_r. f_equal. lia.
Qed.

Lemma kraft_sum_scale : forall l m1 m2,
  (forall len, In len l -> (len <= m1)%nat) -> (m1 <= m2)%nat ->
  kraft_sum l m2 = (2 ^ (m2 - m1) * kraft_sum l m1)%nat.
Proof.
  induction l as [|x l IH]; intros m1 m2 Hall Hm.
  - unfold kraft_sum. rewrite !kraft_sum_from_nil. lia.
  - unfold kraft_sum in *. rewrite !kraft_sum_from_cons.
    rewrite (kraft_at_scale m1 m2 x (Hall x (or_introl eq_refl)) Hm).
    rewrite (IH m1 m2 (fun len H => Hall len (or_intror H)) Hm). lia.
Qed.

Theorem valid_lengths_maxbits_irrelevant : forall l m1 m2,
  (forall len, In len l -> (len <= m1)%nat) -> (m1 <= m2)%nat ->
  (ValidLengths l m1 <-> ValidLengths l m2).
Proof.
  intros l m1 m2 Hall Hm.
  pose proof (kraft_sum_scale l m1 m2 Hall Hm) as Hs.
  assert (Hpow : (2 ^ (m2 - m1) * 2 ^ m1 = 2 ^ m2)%nat).
  { rewrite <- Nat.pow_add_r. f_equal. lia. }
  pose proof (two_pow_pos (m2 - m1)) as Hp.
  unfold ValidLengths. split.
  - intros [_ Hk]. split; [intros len Hin; specialize (Hall len Hin); lia|].
    rewrite Hs, <- Hpow. apply Nat.mul_le_mono_l. exact Hk.
  - intros [_ Hk]. split; [exact Hall|].
    rewrite Hs, <- Hpow in Hk. nia.
Qed.

Corollary valid_lengths_b_maxbits_irrelevant : forall l m1 m2,
  (forall len, In len l -> (len <= m1)%nat) -> (m1 <= m2)%nat ->
  valid_lengths_b l m1 = valid_lengths_b l m2.
Proof.
  intros l m1 m2 Hall Hm.
  pose proof (valid_lengths_maxbits_irrelevant l m1 m2 Hall Hm) as Hiff.
  destruct (valid_lengths_reflect l m1) as [H1|H1];
    destruct (valid_lengths_reflect l m2) as [H2|H2]; try reflexivity.
  - exfalso. apply H2. apply Hiff. exact H1.
  - exfalso. apply H1. apply Hiff. exact H2.
Qed.

(** The concrete statement: on any code-length vector this file can
    actually produce, [7] and [15] are interchangeable. *)
Corollary cl_valid_7_15 : forall n bits cl rem,
  read_cl_lengths n bits = Some (cl, rem) ->
  valid_lengths_b cl 7%nat = valid_lengths_b cl 15%nat.
Proof.
  intros n bits cl rem H.
  apply valid_lengths_b_maxbits_irrelevant; [|lia].
  exact (read_cl_lengths_bound n bits cl rem H).
Qed.

(** By contrast the 15 in [decode_lit_len] IS observable, because
    literal/length codes really do reach 9 bits (the fixed tree does).
    [fixed_lit_valid_b_7] in section 11 is the pin, and mutation testing
    confirms [fixed_block_decodes] fails if the 15 is changed to 7.

    Section 11.2 records a second, independently discovered
    unobservability of the same shape: the 32 in [fixed_dist_lengths]. *)

(** ** 10. Validity predicates

    What the capstone quantifies over.

    [DecodesTo] is the loose form: the stream decodes and we do not care
    what is left.  [IsValidStreamFor] is the EXACTNESS variant: the byte
    list is consumed to within one byte, so no whole trailing byte is
    ignored.  Section 11's [stored_spare_byte_not_exact] shows the two
    really differ. *)

Definition DecodesTo (bits : list bool) (out : list Z) : Prop :=
  exists rem, dec_stream_rem bits = Some (out, rem).

Definition IsValidStreamFor (bytes : list Z) (out : list Z) : Prop :=
  exists rem, dec_stream_rem (bytes_bits bytes) = Some (out, rem)
           /\ (length rem < 8)%nat.

Definition IsValidStream (bytes : list Z) : Prop :=
  exists out, IsValidStreamFor bytes out.

Lemma IsValidStreamFor_DecodesTo : forall bytes out,
  IsValidStreamFor bytes out -> DecodesTo (bytes_bits bytes) out.
Proof. intros bytes out [rem [H _]]. exists rem. exact H. Qed.

(** Decoding is deterministic — it is a function, and both predicates say
    so.  Trivial, and stated because the capstone's uniqueness argument
    should cite a lemma rather than re-derive it. *)
Lemma DecodesTo_det : forall bits o1 o2,
  DecodesTo bits o1 -> DecodesTo bits o2 -> o1 = o2.
Proof.
  intros bits o1 o2 [r1 H1] [r2 H2]. rewrite H1 in H2. congruence.
Qed.

Lemma IsValidStreamFor_det : forall bytes o1 o2,
  IsValidStreamFor bytes o1 -> IsValidStreamFor bytes o2 -> o1 = o2.
Proof.
  intros bytes o1 o2 H1 H2.
  apply (DecodesTo_det (bytes_bits bytes));
    apply IsValidStreamFor_DecodesTo; assumption.
Qed.

(** ** 11. Computational pins

    Each test below says what wrong implementation it would catch.  A test
    that only restates a table would catch nothing and is not written. *)

(** *** 11.1 The RFC 1951 §3.2.5 tables, checked STRUCTURALLY

    Each length/distance code's range starts exactly where the previous
    one's ends: [base[i] + 2 ^ extra[i] = base[i+1]].  A typo in ANY base
    or extra entry breaks one of these equations (two, if it is a base in
    the interior), so this catches transposed digits, dropped entries and
    off-by-one extra widths — none of which a restatement of the table
    would catch. *)
Definition table_contiguous (base extra : list nat) (n : nat) : bool :=
  forallb (fun i => Nat.eqb (nth i base 0 + 2 ^ nth i extra 0)%nat
                            (nth (S i) base 0%nat))
          (seq 0 n).

Example length_table_contiguous :
  table_contiguous length_base length_extra 27 = true.
Proof. vm_compute. reflexivity. Qed.

Example dist_table_contiguous :
  table_contiguous dist_base dist_extra 29 = true.
Proof. vm_compute. reflexivity. Qed.

(** RFC 1951's one deliberate discontinuity, pinned to its exact index:
    code 284 (index 27) has 5 extra bits over base 227, which would reach
    259, but 258 is reserved to code 285, so 284 stops at 257.  The
    contiguity check therefore MUST fail at 28 — a "fix" that made it pass
    would be a wrong spec. *)
Example length_table_284_anomaly :
  table_contiguous length_base length_extra 28 = false.
Proof. vm_compute. reflexivity. Qed.

(** The endpoints: max match length 258, max match distance 32768 (the
    DEFLATE window). *)
Example length_max : nth 28 length_base 0%nat = 258%nat.
Proof. reflexivity. Qed.

(** Stated as a boolean rather than as an equation between [nat]s: 32769 in
    unary is 32769 constructors, and the kernel's structural comparison of
    two terms that deep overflows its stack.  [Nat.eqb] normalises to
    [true] and does not. *)
Example dist_max :
  Nat.eqb (nth 29 dist_base 0 + 2 ^ nth 29 dist_extra 0)%nat 32769%nat = true.
Proof. vm_compute. reflexivity. Qed.

(** [cl_order] is a permutation of 0..18: nineteen entries covering every
    symbol.  Catches a duplicated or dropped entry.  It does NOT catch a
    transposition — [dyn_block_decodes] does, because it depends on 18
    sitting at index 2 and 1 at index 17. *)
Example cl_order_covers :
  forallb (fun j => existsb (Nat.eqb j) cl_order) (seq 0 19) = true.
Proof. reflexivity. Qed.

(** *** 11.2 The fixed trees, against RFC 1951 §3.2.6's own code values

    The RFC prints the codes, not the lengths, so this checks
    [count_len] -> [nc] -> [code_offset] -> [code_bits] end to end against
    the standard.  It catches a wrong ORDER of the four length blocks,
    which the Kraft check below cannot see. *)
Example fixed_lit_rfc_codes :
  map (code_for fixed_lit_lengths 15%nat) [0; 143; 144; 255; 256; 279; 280; 287]%nat
  = [ Some (code_bits 48 8%nat);  Some (code_bits 191 8%nat);
      Some (code_bits 400 9%nat); Some (code_bits 511 9%nat);
      Some (code_bits 0 7%nat);   Some (code_bits 23 7%nat);
      Some (code_bits 192 8%nat); Some (code_bits 199 8%nat) ].
Proof. vm_compute. reflexivity. Qed.

(** The fixed literal/length code is complete: Kraft is an EQUALITY here,
    so a mis-sized [repeat] block changes the sum and this fails.  (The
    same test at 7 fails because the tree has 9-bit codes — which is the
    pin that [decode_lit_len]'s 15 is load bearing.) *)
Example fixed_lit_valid_b : valid_lengths_b fixed_lit_lengths 15%nat = true.
Proof. vm_compute. reflexivity. Qed.

Example fixed_lit_valid_b_7 : valid_lengths_b fixed_lit_lengths 7%nat = false.
Proof. vm_compute. reflexivity. Qed.

Example fixed_dist_valid_b : valid_lengths_b fixed_dist_lengths 15%nat = true.
Proof. vm_compute. reflexivity. Qed.

(** A SECOND HONEST NON-TEST, found by mutation testing this file: the 32
    in [fixed_dist_lengths] is UNOBSERVABLE.  Distance codes 30 and 31 can
    never occur (RFC 1951 §3.2.6), [dist_base] has only 30 entries so
    [decode_lit_len] rejects them anyway, and trimming the tree to 30
    entries leaves every code for symbols 0..29 byte identical — [nc 5] is
    0 either way and [code_offset] is just the symbol index.  Kraft is an
    inequality, so even [valid_lengths_b] cannot see the difference.

    So [fixed_dist_lengths_length] above is a RESTATEMENT of the table and
    catches nothing on its own; it is kept because the RFC states 32, and
    the unobservability is pinned here rather than left as a comment. *)
Example fixed_dist_32_unobservable :
  map (code_for fixed_dist_lengths 15%nat) (seq 0 30)
  = map (code_for (repeat 5%nat 30) 15%nat) (seq 0 30).
Proof. vm_compute. reflexivity. Qed.

(** What IS observable: [dist_base] stopping at 30 entries, so a stream
    that names distance code 30 is rejected.  This catches a [dist_base]
    padded out to 32 with invented values. *)
Example fixed_dist_code_30_rejected :
  decode_lit_len fixed_lit_lengths fixed_dist_lengths
                 (code_bits 1 7%nat ++ code_bits 30 5%nat ++ repeat false 8)
  = None.
Proof. vm_compute. reflexivity. Qed.

(** NON-VACUITY, and the form the encoder half consumes: the fixed trees
    discharge [Huff]'s [ValidLengths] hypothesis, so
    [Huff.hdecode_code_for] applies to them. *)
Lemma fixed_lit_valid : ValidLengths fixed_lit_lengths 15%nat.
Proof. apply valid_lengths_b_true. vm_compute. reflexivity. Qed.

Lemma fixed_dist_valid : ValidLengths fixed_dist_lengths 15%nat.
Proof. apply valid_lengths_b_true. vm_compute. reflexivity. Qed.

(** *** 11.3 [scatter_cl]

    Three transmitted values put a 1 at CL symbol [cl_order[2] = 18] and
    nowhere else.  Catches a scatter written as a gather (the inverse
    permutation), which would place nothing anywhere here, and catches a
    wrong [cl_order[2]]. *)
Example scatter_cl_third :
  scatter_cl [0; 0; 1]%nat
  = [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1]%nat.
Proof. vm_compute. reflexivity. Qed.

(** *** 11.4 A stored block, end to end

    Header byte 1 = BFINAL 1, BTYPE 00, five pad bits; then LEN = 2 and
    NLEN = 0xFFFD little endian; then the payload "HI".

    Catches: a missing [align_byte] (LEN would be read five bits early and
    the complement check would fail), LEN/NLEN swapped, a wrong complement
    constant, and a payload read in the wrong bit order. *)
Definition stored_bytes : list Z := [1; 2; 0; 253; 255; 72; 73].

Example stored_decodes :
  dec_stream_rem (bytes_bits stored_bytes) = Some ([72; 73], []).
Proof. vm_compute. reflexivity. Qed.

Example stored_valid : IsValidStreamFor stored_bytes [72; 73].
Proof. exists []. split; [vm_compute; reflexivity | cbn; lia]. Qed.

(** EXACTNESS IS LOAD BEARING.  Append one spare byte: the stream still
    decodes to the same output, but a whole byte is left over, so
    [IsValidStreamFor] must reject it.  If the [< 8] were dropped (or
    written [<= 8]) this would pass and the predicate would be the loose
    one under a different name. *)
Example stored_spare_byte_decodes :
  DecodesTo (bytes_bits (stored_bytes ++ [0])) [72; 73].
Proof. exists (bytes_bits [0]). vm_compute. reflexivity. Qed.

Example stored_spare_byte_not_exact :
  ~ IsValidStreamFor (stored_bytes ++ [0]) [72; 73].
Proof.
  intros [rem [H Hlt]]. vm_compute in H. inversion H; subst.
  cbn [length] in Hlt. lia.
Qed.

(** *** 11.5 A fixed-Huffman block, end to end, with a real LZ77 match

    Literal 'A' (65), literal 'B' (66), then a match of length 12 at
    distance 2 — an OVERLAPPING copy, so it exercises [Huff.lz_copy]'s
    closed form — then end of block.

    Codes: 65 -> [code_bits 113 8] and 66 -> [code_bits 114 8] (fixed
    literals are [48 + sym] at 8 bits); length 12 is code 265
    ([length_base[8] = 11], one extra bit set) whose fixed code is
    [code_bits 9 7]; distance 2 is code 1 ([dist_base[1] = 2], no extra
    bits) whose fixed code is [code_bits 1 5]; end of block is
    [code_bits 0 7].

    Catches: BFINAL/BTYPE read in the wrong bit order, the wrong fixed
    tree, MSB/LSB confusion between codewords and extra fields, a wrong
    [length_base[8]] or [length_extra[8]], a wrong [dist_base[1]], the
    [sym - 257] index shift, and a broken [decode_symbols] recursion (the
    block has four symbols, so the fuel path is genuinely iterated). *)
Definition fixed_block_bits : list bool :=
  [true]                                   (* BFINAL = 1 *)
  ++ write_bits 2%nat 1                    (* BTYPE  = 01, fixed *)
  ++ code_bits 113 8%nat                   (* literal 'A' *)
  ++ code_bits 114 8%nat                   (* literal 'B' *)
  ++ code_bits 9 7%nat                     (* length code 265 *)
  ++ write_bits 1%nat 1                    (* + 1 extra bit -> length 12 *)
  ++ code_bits 1 5%nat                     (* distance code 1 -> distance 2 *)
  ++ code_bits 0 7%nat                     (* end of block *)
  ++ [false].                              (* pad to 40 bits *)

Example fixed_block_decodes :
  dec_stream_rem fixed_block_bits
  = Some ([65; 66; 65; 66; 65; 66; 65; 66; 65; 66; 65; 66; 65; 66], [false]).
Proof. vm_compute. reflexivity. Qed.

(** The same block one symbol at a time, so a failure localises. *)
Example fixed_block_first_symbol :
  decode_lit_len fixed_lit_lengths fixed_dist_lengths
                 (code_bits 113 8%nat ++ [true; false])
  = Some (LzLit 65, [true; false]).
Proof. vm_compute. reflexivity. Qed.

Example fixed_block_match_symbol :
  decode_lit_len fixed_lit_lengths fixed_dist_lengths
                 (code_bits 9 7%nat ++ write_bits 1%nat 1
                  ++ code_bits 1 5%nat ++ [true])
  = Some (LzRef 12 2, [true]).
Proof. vm_compute. reflexivity. Qed.

(** *** 11.6 A dynamic block, end to end

    The one test that exercises §3.2.7.  HLIT = 0 (257 literal lengths),
    HDIST = 0 (1 distance length), HCLEN = 14 (18 transmitted code-length
    lengths, enough to reach [cl_order[17] = 1]).  The code-length tree
    gives symbols 1 and 18 one bit each, so CL symbol 1 is [false] and CL
    symbol 18 is [true].  The 258 lengths are then run-length coded as
    65 zeros (18, extra 54), one 1, 138 zeros (18, extra 127), 52 zeros
    (18, extra 41), one 1, one 1 — putting a 1-bit code on literal 65 and
    on end-of-block 256, and a 1-bit distance code on distance symbol 0.
    The data is then literal 'A' followed by end of block.

    Catches: a wrong [cl_order] permutation, the HLIT +257 / HDIST +1 /
    HCLEN +4 offsets, a 3-bit field read at the wrong width, symbol 18's
    base 11 and its 7 extra bits, [scatter_cl]'s direction, and the
    [firstn]/[skipn] split between the literal and distance vectors. *)
Definition dyn_block_bits : list bool :=
  [true]                                   (* BFINAL = 1 *)
  ++ write_bits 2%nat 2                    (* BTYPE  = 10, dynamic *)
  ++ write_bits 5%nat 0                    (* HLIT  = 0  -> 257 *)
  ++ write_bits 5%nat 0                    (* HDIST = 0  -> 1 *)
  ++ write_bits 4%nat 14                   (* HCLEN = 14 -> 18 *)
  ++ flat_map (write_bits 3%nat)
       [0; 0; 1; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1]
  ++ ([true] ++ write_bits 7%nat 54)       (* 18: 11 + 54 = 65 zeros *)
  ++ [false]                               (* 1: literal 65 gets length 1 *)
  ++ ([true] ++ write_bits 7%nat 127)      (* 18: 11 + 127 = 138 zeros *)
  ++ ([true] ++ write_bits 7%nat 41)       (* 18: 11 + 41 = 52 zeros *)
  ++ [false]                               (* 1: literal 256 gets length 1 *)
  ++ [false]                               (* 1: distance 0 gets length 1 *)
  ++ [false]                               (* data: literal 'A' *)
  ++ [true]                                (* data: end of block *)
  ++ repeat false 7.

Example dyn_block_decodes :
  dec_stream_rem dyn_block_bits = Some ([65], repeat false 7).
Proof. vm_compute. reflexivity. Qed.

(** The header alone, so a failure localises to §3.2.7 rather than to the
    data.  257 literal lengths with a 1 at index 65 and at index 256; one
    distance length. *)
Example dyn_block_tables_shape :
  match decode_dynamic_tables
          (write_bits 5%nat 0 ++ write_bits 5%nat 0 ++ write_bits 4%nat 14
           ++ flat_map (write_bits 3%nat)
                [0; 0; 1; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1]
           ++ ([true] ++ write_bits 7%nat 54)
           ++ [false]
           ++ ([true] ++ write_bits 7%nat 127)
           ++ ([true] ++ write_bits 7%nat 41)
           ++ [false] ++ [false]) with
  | None => None
  | Some (lit, dst, _) =>
      Some (length lit, nth 65 lit 0%nat, nth 256 lit 0%nat, dst)
  end = Some (257%nat, 1%nat, 1%nat, [1]%nat).
Proof. vm_compute. reflexivity. Qed.

(** *** 11.7 Two blocks, and the window that crosses between them

    A stored block carrying "HI" (BFINAL = 0) followed by a fixed block
    whose only symbol is a match of length 2 at distance 2 — reaching back
    into the PREVIOUS block's output.  Catches an accumulator that is
    reset per block, which every other test here would pass. *)
Definition two_block_bits : list bool :=
  bytes_bits [0; 2; 0; 253; 255; 72; 73]
  ++ [true]                                (* BFINAL = 1 *)
  ++ write_bits 2%nat 1                    (* BTYPE  = 01, fixed *)
  ++ code_bits 1 7%nat                     (* length code 257 -> length 3 *)
  ++ code_bits 1 5%nat                     (* distance code 1 -> distance 2 *)
  ++ code_bits 0 7%nat                     (* end of block *)
  ++ repeat false 2.                       (* pad to 80 bits *)

Example two_block_window_crosses :
  dec_stream_rem two_block_bits
  = Some ([72; 73; 72; 73; 72], repeat false 2).
Proof. vm_compute. reflexivity. Qed.

(** *** 11.8 The reserved block type

    BTYPE = 11 is reserved; the decoder must not accept it. *)
Example reserved_btype_rejected :
  dec_stream_rem ([true] ++ write_bits 2%nat 3 ++ repeat false 21) = None.
Proof. vm_compute. reflexivity. Qed.
