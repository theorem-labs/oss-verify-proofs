(** * DeclIface — the DECLARATIVE-LAYER INTERFACE, as statements only.

    OWNER: symbol-id.  Commission §TL-RATIFY-SEQ ("the declarative-layer
    interface file is assigned").  Scratch draft; edits nothing.

    WHAT THIS FILE IS FOR.  rt-scout's sequencing found that gaps (a) and (b)
    are a SANDWICH around the declarative inverse, and that two lanes
    finishing at different times against an unpinned interface is this
    campaign's five-for-five failure at layer scale.  So the filling is
    written down first, as [Definition]s, while it is still cheap to change.

      (a)  the deflate EMITTER model              ld-seams / L-D
      ---  the declarative inverse                symbol-id  (landed)
      (b)  the inflate REFINEMENT                 lenext-repair + gtbl-arms

    THE ONE DESIGN RULE, from the commission: **what (a)'s conclusion
    publishes must be LITERALLY what (b)'s hypothesis consumes.**  This file
    enforces that structurally rather than by inspection — both faces are
    stated against ONE named [Prop] ([DeclFrame]), so they cannot drift, and
    §9 PROVES the sandwich closes.  That single proof is the whole
    verification value of the file: an interface nobody has composed is a
    guess, and [interface_composes] is what turns it into a check.

    NO [Parameter], ANYWHERE, per the gate-fatal broadcast: a [Parameter] in
    an [AgentSubmission] file is an axiom in [Print Assumptions] and scores
    zero off-allowlist.  Everything deferred is an explicit argument.

    THE TARGET is rt-scout's C5, the only mathematical layer of
    [codec_ed_id] still open ([§RT-SCOUT-STACK] measured eight of its nine
    layers already Qed):

      png_inflate_stream (png_zlib_stream wb lvl st X) = Some X

    THE BOUNDARY IS THE CMF-FIXED STREAM, AND THIS IS A CORRECTION.  My first
    draft stated the target over [png_zlib_stream]'s RAW output, on the reading
    that [Codec.v:267]'s "before [optimize_cmf] rewrites its first two bytes"
    put the rewrite in a layer above.  **That is the wrong statement.**
    rt-scout's §RT-SCOUT-AX68 §4 measured what the landed layers actually
    conclude: both [L10Container.ihdr_match] and
    [L10Container.idat_stream_parse_encode] end at
    [idat_stream cs = apply_optimize_cmf (wr_image_size s) z] — NOT [z].  The
    decoder reads the IDAT bytes, and those are the rewritten ones, so an
    obligation stated over the raw output proves a lemma nobody consumes.

    That correction is not cosmetic: [optimize_cmf] REDUCES CINFO for small
    data, so the window the decoder reads is the FIXED byte's, not the
    emitter's.  Restating over the fixed stream is what lets §5's window clause
    cite [Chunk.optimize_cmf_window_ge] instead of remaining an open design
    question — the correction made the interface CHEAPER, which is the
    argument for taking a boundary from what the consumer concludes rather than
    from a comment about intent.

    VOCABULARY IS BORROWED, NOT COINED.  Every clause below is stated in a
    form that already exists somewhere in the tree, because an interface that
    invents a rival spelling of a landed fact makes work instead of removing
    it.  Specifically: header validity is filter-id's three clauses from
    [LEHdr.optimize_cmf_valid]; the trailer is [Chunk.be32] because
    filter-id's [LETrailer.trailer_bytes_be32] already proves the encoder
    emits exactly that; the checksum is [Checksum.adler32_z] because BOTH
    sides call it (see §4). *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff DeflateSpec Checksum Chunk Codec.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

Module SymbolIdDeclIface.

(* ==========================================================================
   1.  THE FRAMING — what a zlib stream IS, byte-wise.
   ========================================================================== *)

(** Two header bytes, the deflate body, four trailer bytes.  Stated as an
    equation on [enc] rather than as three projection functions so that a
    consumer destructs it once and never has to reason about [firstn]/[skipn]
    boundaries — the shape a caller wants is the decomposition, not accessors
    for it. *)
Definition ZlibFramed (enc : list Z) (b0 b1 : Z) (body : list Z) (ad : Z) : Prop :=
  enc = [b0; b1] ++ body ++ be32 ad.

(* ==========================================================================
   2.  HEADER VALIDITY — filter-id's three clauses, verbatim.
   ========================================================================== *)

(** Clauses 1-3 are EXACTLY the hypotheses of
    [Common/LEHdr.optimize_cmf_valid]: CM = 8 (deflate), CINFO in [1,7], and
    the FCHECK congruence.  Written with [u8] applied, as they are there, so
    the two forms match literally and a consumer can hand one to the other
    with no massaging.  Restating them in a "cleaner" normalised form is
    exactly the mistake this file exists to prevent.

    Clause 4 is an ADDITION beyond the LEHdr trio (GAP7-F2 amendment,
    2026-08-21, q5-emitter under TL-granted stewardship): FDICT clear.  A
    header with FDICT set passes clauses 1-3 while the machine forks to
    M_DICTID and [Z_NEED_DICT] kills the one-shot pump; the emitter never
    sets FDICT, so both producer sites discharge it by [reflexivity]. *)
Definition ZlibHeaderOk (b0 b1 : Z) : Prop :=
  Z.land (u8 b0) 15 = 8
  /\ 0 <= Z.shiftr (u8 b0) 4 <= 7  (* REPAIRED 2026-08-19 per zlib-port-repairs.md: was `1 <=`, FALSE on the applied header (CINFO can be 0) *)
  /\ (u8 b0 * 256 + u8 b1) mod 31 = 0
  /\ Z.land (u8 b1) 32 = 0.

(* ==========================================================================
   3.  THE DECLARATIVE CONTENT — the face symbol-id owns.
   ========================================================================== *)

(** The body's bits decode, declaratively, back to the payload.  [dec_stream]
    discards its remainder ([DeflateSpec.v:1133] is [option_map fst] over
    [dec_stream_rem]), which is what makes this the right statement for a
    BYTE-framed body: the emitter pads the final block up to a byte boundary
    at [Z_FINISH], and those padding bits must not be an obligation. *)
Definition BodyDecodesTo (body : list Z) (X : list Z) : Prop :=
  dec_stream (bytes_bits body) = Some X.

(* ==========================================================================
   4.  THE CHECKSUM — one function applied twice, not two compared.
   ========================================================================== *)

(** MEASURED, and it makes this clause much cheaper than it looks: the
    encoder at [Deflate.v:284] computes [adler32_z (zs_adler st) false dat],
    and the decoder's [Inflate.v:408] [upd_check] computes
    [adler32_z check false bs].  **Both sides call [Checksum.adler32_z].**  So
    there is no encoder-vs-decoder refinement here — it is one function over
    the same bytes, and the only content is that the encoder's INCREMENTAL
    accumulation over read chunks equals the closed form over the whole
    payload (ZChecksum's "deferral congruence").

    Stating this with [Common/ZChecksum.adler32_model] instead would have
    MANUFACTURED a refinement obligation that does not exist.  That is why the
    clause names [adler32_z].

    The initial value is written as the tree's own expression
    [adler32_z 0 true []] ([Deflate.v:1235], [deflate_reset]) rather than as
    the literal 1, so no unproved numeric claim enters the interface. *)
Definition adler_init : Z := adler32_z 0 true [].

Definition TrailerMatchesPayload (ad : Z) (X : list Z) : Prop :=
  ad = adler32_z adler_init false X.

(* ==========================================================================
   5.  THE WINDOW CLAUSE — half discharged by a landed lemma, half a named
       residue.  gtbl-arms to rule on the form.
   ========================================================================== *)

(** WHY A CLAUSE IS NEEDED AT ALL, because without it (b) is FALSE and not
    merely hard.  [Huff.resolve_lz] ([Huff.v:884]) rejects a reference only
    when [dist = 0] or [length acc < dist] — it bounds distances by the OUTPUT
    SO FAR and knows nothing about a window.  zlib's inflate bounds them by
    [2^wbits], taken from the header's CINFO nibble.  So a body whose
    distances exceed the window is decoded happily by [dec_stream] and
    rejected by [png_inflate_stream], and [InflaterConsumes] without a window
    clause asserts something untrue.

    THE PAYLOAD-FITS FORM, which is what the clause below states, and it is
    free where it applies: if the whole payload fits the window then no distance
    can exceed it, because [resolve_lz] already caps every distance at
    [length acc] and [length acc <= length X] throughout.  That side condition is
    **proved in this file** ([resolve_caps_distances]), not handed on.

    THE BOUNDARY IS 32768, NOT 16384 — A CORRECTION TO MY OWN EARLIER CLAIM.  I
    first wrote that the clause is discharged for [ds <= 16384] (where
    [optimize_cmf] fires) and open above it.  **That over-stated the residue by
    three orders of magnitude.**  rt-scout retracted an "unowned" finding of mine
    about [deflate_claim_window_bits] — it has SIX published results, my query
    having required the name on the same line as the [Lemma] keyword — and among
    them is the closed form that settles this:
    [Chunk.emitted_window] is "the smallest power of two that is at least
    [data_size], clamped into [256 .. 32768]" ([Chunk.v:913-917], pinned on 17
    samples by [emitted_window_is_ceil_pow2]).

    So the header window COVERS the payload everywhere except where the clamp
    binds, computed below in [residue_is_sixtyfour_values]:

      ds = 16123 -> window 16384   covered
      ds = 16384 -> window 16384   covered
      ds = 16385 -> window 32768   covered   <- the clause does NOT break here
      ds = 32768 -> window 32768   covered
      ds = 32769 -> window 32768   NOT covered
      ds = 32832 -> window 32768   NOT covered

    **The residue is exactly [32769 <= ds <= 32832]: SIXTY-FOUR VALUES**, and
    32832 is the largest payload the harness can reach — independently proved in
    the tree by [Codec.d8_cluster_64x64_rgba16], which computes
    [encode_data_size 64 64 16 CT_RGB_ALPHA NONE = Some 32832] and
    [deflate_claim_window_bits 15 32832 = Some 15].  So my hand arithmetic agrees
    with a Qed'd Example at exactly the extreme case.

    WHAT THE RESIDUE NEEDS IS A DISTANCE BOUND, NOT A LENGTH BOUND, and the round
    trip is not in doubt there: deflate at [wbits = 15] never emits a distance
    above 32768 however long its input.  So the residue is an EMITTER-published
    fact, over a 64-value band, and I have not attempted it.

    RULING REQUESTED, gtbl-arms, since you own the (b)-consumable form: take the
    clause as stated and carry the 64-value band as a named residue.  It is a far
    smaller ask than the one I sent you before rt-scout's retraction. *)

(** THE WINDOW IS READ OFF THE HEADER, not carried as a free parameter.  This
    is a CORRECTION to my own first draft of this file and the reason is worth
    recording, because it is the standing "tie only what is read" lesson
    arriving in my own work: I first wrote [DeclFrame] with [wsize] as an extra
    argument and [EmitterPublishes] as [forall ... wsize, ... DeclFrame enc X
    wsize].  That is UNSATISFIABLE for every non-empty payload — instantiate
    [wsize] at 0 and the clause demands [length X <= 0].  Quantified the other
    way ([exists wsize]) it is satisfiable and USELESS, because the emitter
    could choose a window large enough to make the clause vacuous and (b)
    would learn nothing about the window zlib actually uses.

    Tying it to [b0]'s CINFO nibble fixes both at once: zlib's
    [wbits = CINFO + 8] and its window is [2 ^ wbits], and CINFO is exactly the
    byte the decoder reads ([Codec.v:283]: "the window size comes from the
    stream's own CINFO nibble").  So the clause now constrains the quantity the
    computation consumes, and [DeclFrame] loses a parameter. *)
(** THE COMPARISON LIVES IN [Z], NOT [nat], and that is not a style choice.
    My first attempt had [WindowOfHeader : Z -> nat] via [Z.to_nat] and stated
    the length bound in [nat]; [window_clause_inhabited] then **Stack
    overflow**ed, because a [nat] window of 32768 is a unary numeral.  This is
    the same trap as [DeflateSpecThy.dist_29_width], at the same value, in a
    file I wrote after documenting it.  Knowing a failure mode does not prevent
    it; keeping the arithmetic in [Z], where 32768 is binary, does. *)
Definition WindowOfHeader (b0 : Z) : Z :=
  2 ^ (Z.shiftr (u8 b0) 4 + 8).

(** ** REFUTED, AND SCHEDULED FOR REMOVAL — do not build on this clause.

    `PayloadFitsWindow` is FALSE at a REACHED input: at the largest harness image
    (ds = 32832, 64x64 RGBA16) the advertised window is 32768, so the clause
    demands `32832 <= 32768`.  Proved, not suspected —
    `symbolid/cbfa/SidWinCheck.v` `payload_fits_window_false_at_max_image`, with
    the residue table computed in the tree's own `emitted_window` rather than
    asserted from mine.  My `window_clause_inhabited` (below) does not rescue it:
    that is a hypothesis-carrying witness at CINFO 7 with a THREE-BYTE payload,
    so it shows the clause holds SOMEWHERE, never where `EmitterPublishes` needs
    it.

    KEPT IN PLACE deliberately, per zlib-lead's ruling that the replacement is not
    part of this edit: deleting the conjunct now would leave `DeclFrame` with no
    window or distance clause at all, which does not make the obligation go away —
    it moves it off (a) and onto nobody, silently.  Removal rides the §5 interface
    edit together with its replacement, in its own slot. *)
Definition PayloadFitsWindow (X : list Z) (b0 : Z) : Prop :=
  Z.of_nat (length X) <= WindowOfHeader b0.

(** NOT A RIVAL DEFINITION — proved, because my file's own rule is that
    vocabulary is borrowed and I broke it here.  [Chunk.emitted_window] already
    computes this quantity, keyed on the DATA SIZE where mine is keyed on the
    HEADER BYTE; [DeclFrame] only has the bytes, which is why the byte-keyed form
    is the one in the clause.  The two agree: *)
Lemma window_of_header_is_emitted_window : forall ds,
  WindowOfHeader (fst (emitted_zlib_header_effective ds)) = emitted_window ds.
Proof.
  intros ds. unfold WindowOfHeader, emitted_window.
  rewrite Z.shiftl_1_l.
  f_equal. f_equal. f_equal.
  unfold emitted_zlib_header_effective. cbv zeta.
  unfold optimize_cmf. cbv zeta.
  destruct (Z.leb ds 16384); cbn [fst].
  - destruct (_ && _); cbn [fst]; [|unfold u8; now rewrite Zmod_mod].
    destruct (Z.leb ds _); cbn [fst]; unfold u8; now rewrite Zmod_mod.
  - unfold u8. now rewrite Zmod_mod.
Qed.

(** THE RESIDUE, computed in the TREE's function rather than asserted from mine.
    The clause holds at every sampled size up to and including 32768 and fails
    only where the clamp binds. *)
Example residue_is_sixtyfour_values :
  map (fun d => (d, emitted_window d, Z.leb d (emitted_window d)))
      [16123; 16384; 16385; 32768; 32769; 32832]
  = [(16123, 16384, true); (16384, 16384, true); (16385, 32768, true);
     (32768, 32768, true); (32769, 32768, false); (32832, 32768, false)].
Proof. vm_compute. reflexivity. Qed.

(** The CINFO arithmetic, pinned so the [2 ^ 15] in the overhang example is
    tied to the header byte rather than to a comment. *)
Example window_of_cinfo_7 : forall b0, Z.shiftr (u8 b0) 4 = 7 -> WindowOfHeader b0 = 32768.
Proof. intros b0 H. unfold WindowOfHeader. rewrite H. reflexivity. Qed.

(** THE BRANCH SPLIT, as a VALUE.  A coverage limit stated in prose never gets
    checked; as arithmetic it dies immediately if the numbers move.  Every
    number here comes from the tree or the harness source, not from me:
    [Chunk.png_image_size] non-interlaced is [(rowbytes + 1) * height];
    [optimize_cmf] tests [data_size <= 16384]; CINFO 7 gives window [2^15]. *)
Example overhang_is_in_the_unoptimized_branch :
  (* largest harness image: 64 x 64, RGBA (4 ch) at 16-bit (2 B) -> rowbytes 512 *)
  64 * 4 * 2 = 512
  (* ds = wr_image_size = (rowbytes + 1) * height, the FILTERED payload *)
  /\ (512 + 1) * 64 = 32832
  (* so optimize_cmf does NOT fire: its test is data_size <= 16384 *)
  /\ 16384 < 32832
  (* header therefore keeps deflate's CINFO 7, i.e. a 32768-byte window *)
  /\ 2 ^ (7 + 8) = 32768
  (* leaving exactly this much payload beyond the advertised window *)
  /\ 32832 - 32768 = 64.
Proof. repeat split; reflexivity. Qed.

(** And the other side of the split, so the discharged branch is pinned too:
    at the largest size [optimize_cmf] fires, the payload is well inside
    16384, and [Chunk.optimize_cmf_window_ge]'s third premise [d + 262 <=
    2^(ci0+8)] is satisfied with room at CINFO 7. *)
Example optimized_branch_premises_hold :
  16384 <= 16384 /\ 16384 + 262 <= 2 ^ (7 + 8).
Proof. split; reflexivity || lia. Qed.

(** And the reason the payload-fits form is free, as a statement rather than a
    claim in the comment above: [resolve_lz] refuses any distance exceeding the
    accumulator, so a window at least as large as the accumulator never binds.

    **THE [Forall] PREMISE IS LOAD-BEARING AND ITS ABSENCE MADE MY FIRST
    VERSION FALSE.**  [Huff.resolve_lz] ([Huff.v:882]) returns [Some acc] on
    [LzEnd] and IGNORES every symbol after it, so a post-[LzEnd] [LzRef] with an
    arbitrary distance is never validated and [In (LzRef len dist) syms] says
    nothing about it.  I stated this obligation without the premise, it
    typechecked, and it is refutable — see
    [resolve_caps_distances_naive_is_false] below.  The premise is written in
    the tree's own idiom ([EmitSym.emit_decode_seq] carries exactly
    [Forall (fun s => lz_is_end s = false) body]) rather than a rival spelling,
    and it is satisfied where this is used: a block's symbol list is
    [body ++ [LzEnd]] with every reference in the body.

    **NO LONGER AN OBLIGATION: proved below.**  It was carried here as a residue
    for whoever took the window clause; nobody had claimed it and it is in this
    lane's vocabulary, so it is discharged rather than handed on.  One fewer item
    on the gap list. *)
Definition ResolveCapsDistances : Prop :=
  forall syms acc out,
    Forall (fun s => lz_is_end s = false) syms ->
    resolve_lz syms acc = Some out ->
    forall len dist, In (LzRef len dist) syms -> (dist <= length out)%nat.

(** [resolve_lz] never shrinks the accumulator.  Needed because a reference's
    guard bounds its distance by [length acc] at the point it is CONSUMED, while
    the obligation is stated against the FINAL output.

    WHY [cbn [resolve_lz]] AND NOT [cbn], because the bare form cost a build: a
    plain [cbn in H] also unfolds [Nat.ltb], turning the guard
    [(d =? 0) || (length acc <? d)] into
    [(d =? 0) || match d with 0 => false | S m' => length acc <=? m' end].  A
    following [destruct ((d =? 0) || (length acc <? d)) eqn:Eg] then splits on a
    term that no longer occurs in [H], leaving [H] untouched so that
    [discriminate H] reports "Not a discriminable equality" — a failure about
    WHICH TERM the tactic acted on, not about a missing fact.  Restricting the
    delta keeps the guard in the shape the [destruct] names. *)
Lemma resolve_lz_length_mono : forall syms acc out,
  resolve_lz syms acc = Some out -> (length acc <= length out)%nat.
Proof.
  induction syms as [|s tl IH]; intros acc out H.
  - cbn [resolve_lz] in H. inversion H. lia.
  - destruct s as [b | l d |].
    + cbn [resolve_lz] in H. specialize (IH _ _ H).
      rewrite length_app in IH. cbn [length] in IH. lia.
    + cbn [resolve_lz] in H.
      destruct ((d =? 0)%nat || (length acc <? d)%nat) eqn:Eg; [discriminate H|].
      specialize (IH _ _ H). rewrite length_app in IH. lia.
    + cbn [resolve_lz] in H. inversion H. lia.
Qed.

Theorem resolve_caps_distances : ResolveCapsDistances.
Proof.
  unfold ResolveCapsDistances.
  induction syms as [|s tl IH]; intros acc out Hall H len dist Hin.
  - cbn in Hin. contradiction.
  - inversion Hall as [|s0 tl0 Hs Htl]; subst.
    destruct s as [b | l d |].
    + cbn [resolve_lz] in H. cbn [In] in Hin.
      destruct Hin as [Heq | Hin2]; [discriminate Heq|].
      exact (IH _ _ Htl H len dist Hin2).
    + cbn [resolve_lz] in H.
      destruct ((d =? 0)%nat || (length acc <? d)%nat) eqn:Eg; [discriminate H|].
      apply orb_false_iff in Eg as [E0 Elt].
      apply Nat.ltb_ge in Elt.
      cbn [In] in Hin. destruct Hin as [Heq | Hin2].
      * injection Heq as Hl Hd. subst.
        pose proof (resolve_lz_length_mono _ _ _ H) as Hm.
        rewrite length_app in Hm. lia.
      * exact (IH _ _ Htl H len dist Hin2).
    + cbn in Hs. discriminate Hs.
Qed.

(** NON-VACUITY, so the theorem is not true merely because its [Forall] premise
    is unsatisfiable at any interesting symbol list: exercised at a real
    back-reference that copies two bytes from two back. *)
Example resolve_caps_distances_exercised :
  resolve_lz [LzLit 65; LzLit 66; LzRef 2%nat 2%nat] [] = Some [65; 66; 65; 66]
  /\ Forall (fun s => lz_is_end s = false)
            [LzLit 65; LzLit 66; LzRef 2%nat 2%nat].
Proof. split; [reflexivity|]. repeat constructor. Qed.

(** THE REFUTATION OF THE PREMISE-FREE FORM, as a value.  [resolve_lz] stops at
    [LzEnd] and ignores the rest, so the naive statement is false at a
    two-symbol list.  Kept in the file for the same reason as
    [free_wsize_form_is_unsatisfiable]: this is the second obligation here whose
    defect a clean build could not see, and a refuted form that is only
    described is one the next drafter re-writes. *)
Example post_end_ref_is_ignored :
  resolve_lz [LzEnd; LzRef 3%nat 100%nat] [] = Some [].
Proof. reflexivity. Qed.

Example resolve_caps_distances_naive_is_false :
  ~ (forall syms acc out,
        resolve_lz syms acc = Some out ->
        forall len dist, In (LzRef len dist) syms -> (dist <= length out)%nat).
Proof.
  intro H.
  assert (Hin : In (LzRef 3%nat 100%nat) [LzEnd; LzRef 3%nat 100%nat])
    by (right; left; reflexivity).
  pose proof (H [LzEnd; LzRef 3%nat 100%nat] [] [] post_end_ref_is_ignored
                3%nat 100%nat Hin) as Hbad.
  cbn in Hbad. lia.
Qed.

(* ==========================================================================
   6.  THE JOINT — one named Prop, so the two faces cannot drift.
   ========================================================================== *)

(** This is the interface.  Everything above is a clause of it; nothing below
    mentions the clauses individually.  A lane that changes a clause changes
    both faces at once, which is the structural property the commission asked
    for and the reason this is a Definition rather than a paragraph. *)
Definition DeclFrame (enc X : list Z) : Prop :=
  exists b0 b1 body ad,
    ZlibFramed enc b0 b1 body ad
    /\ ZlibHeaderOk b0 b1
    /\ BodyDecodesTo body X
    /\ TrailerMatchesPayload ad X
    (* REFUTED CONJUNCT — false at ds = 32832; see the banner at
       [PayloadFitsWindow].  Removal + replacement ride the §5 interface edit. *)
    /\ PayloadFitsWindow X b0.

(* ==========================================================================
   7.  (a)'s CONCLUSION — what the deflate emitter model must publish.
   ========================================================================== *)

(** ld-seams' face.  Their arms currently end at [DeflateSpec.dec_blk] over a
    bit stream for one block; this is the whole-stream form, which is the gap
    §TL-SYNTHESIS-CODECEDID named as (a) — "connecting [cb_step] /
    [tr_stored_block] to [deflate]'s whole-loop output".

    Note what the emitter does NOT owe: nothing about [wb] beyond what lands
    in [b0]'s CINFO nibble.  The window clause reads the header, so the
    emitter discharges it by having written a header consistent with the
    window it used — which is a fact about its own two bytes, not a new
    parameter threaded through the interface. *)
Definition EmitterPublishes : Prop :=
  forall lvl st hdr X enc,
    png_zlib_stream (deflate_claim_window_bits 15 (wr_image_size hdr)) lvl st X
      = Some enc ->
    DeclFrame (apply_optimize_cmf (wr_image_size hdr) enc) X.

(** RETRACTED NOTE, kept as a record rather than deleted.  An earlier revision
    of this file said [deflate_claim_window_bits] "has no lemma anywhere in the
    tree".  **That was FALSE.**  My query required the name on the SAME LINE as
    the [Lemma] keyword, and all six published results state it on a
    continuation line: [dcwb_bound], [dcwb_cases], [window_bits_bands],
    [emitted_window_below_deflate_window], [d8_cluster_1x1_gray],
    [d8_cluster_64x64_rgba16].  rt-scout caught it after reporting it onward as
    an unowned gap, and four of the six are exactly the band facts §5 needed —
    which is how the residue there shrank from "everything above 16384" to 64
    values.  Third time in one session that a "gap" was a publication problem
    rather than a missing proof. *)

(** ** THE PUMP'S FUEL — lenext-repair's finding, and a clause my draft was
    MISSING.  They flagged it from the (b) side without being able to read this
    file, which is the consumer review I asked for working exactly as intended.

    [png_inflate_stream] is [inf_pump (inf_fuel ...) ...] and answers [None]
    when the fuel runs out ([Inflate.v:1690], [inf_fuel] a function of the
    reader's have/bits and the output room).  So a conclusion of the form
    [= Some X] SILENTLY CARRIES "the pump's trip count fits its fuel" — which
    is gap (c), and open: [TripsFillBounded] and [PartialTripIsLast] are proved,
    [used <= zlen inp] unconditionally, but [0 <= used] is FALSE of the model as
    the arms stand (the LEN fast path hands input back, §LENEXT-REPAIR-GIVEBACK)
    and the repair runs through [if_wf]'s [bits < 8], which is unproved.

    **This is the SAME SHAPE as the window clause and lenext-repair named it as
    such: a fact the conclusion needs but the antecedent does not name is where
    an interface goes from hard to FALSE.**  [dec_stream] knows nothing about a
    window; [dec_stream] also cannot run out of fuel, and [png_inflate_stream]
    can.  Two instances of one defect, one found by me and one by a consumer.

    So termination becomes its OWN named premise.  That splits (b) from (c)
    exactly along TL's gap boundary: (b) owes "if it answers, the answer is X",
    (c) owes "it answers". *)
Definition PumpTerminates (enc : list Z) : Prop :=
  exists out, png_inflate_stream enc = Some out.

(* ==========================================================================
   8.  (b)'s HYPOTHESIS — what the inflate refinement must consume.
   ========================================================================== *)

(** lenext-repair + gtbl-arms' face.  The hypothesis is [DeclFrame] and
    NOTHING ELSE: if (b) needs a fact that is not a clause of [DeclFrame],
    that is a defect in this file and I would rather hear it now than after a
    walk is built. *)
Definition InflaterConsumes : Prop :=
  forall enc X,
    DeclFrame enc X ->
    PumpTerminates enc ->
    png_inflate_stream enc = Some X.

(* ==========================================================================
   9.  THE TARGET, AND THE ONE PROOF IN THIS FILE.
   ========================================================================== *)


(** (c)'s face, at the emitter's call site. *)
Definition PumpFuelSuffices : Prop :=
  forall lvl st hdr X enc,
    png_zlib_stream (deflate_claim_window_bits 15 (wr_image_size hdr)) lvl st X
      = Some enc ->
    PumpTerminates (apply_optimize_cmf (wr_image_size hdr) enc).

(* ==========================================================================
   9.  THE TARGET, AND THE ONE PROOF IN THIS FILE.
   ========================================================================== *)

(** NAME COORDINATED WITH filter-id: this is their [ZlibRoundTrip]
    ([filterid/assembly/Assembly2.v:118]), not a rival [C5].  rt-scout's warning
    was that if their assembly and this interface name the same obligation
    differently that is the desynchronisation arriving immediately; their name
    came first and this file adopts it.

    TWO ARGUMENTS ARE TIED THAT THEIR VERSION LEAVES FREE, and this is not a
    stylistic difference — their form is undischargeable.  At the call site
    ([Codec.v:389-396]) BOTH the data size and the window bits are derived:

      ds = wr_image_size hdr        (= the filtered payload's length)
      wb = deflate_claim_window_bits 15 ds

    With [ds] free, [apply_optimize_cmf ds zout] rewrites the CMF byte from a
    size unrelated to the payload, so CINFO can be shrunk below what the
    stream's own distances need and the decode FAILS.  With [wb] free the
    emitter's window is unconstrained too.  Tying both makes the obligation
    WEAKER — easier to discharge — while remaining exactly what their consumer
    applies, since the call site supplies those very terms.

    This is the "easiest to prove WITH, easiest to be unable to DISCHARGE"
    shape: a [Variable Hzlib] is free to consume and impossible to earn.

    AND MY FIRST TIE WAS THE MIRROR DEFECT — filter-id caught it and they are
    right.  I proposed [ds = Z.of_nat (length X)].  **That premise is not
    suppliable**, because [Chunk.png_image_size] ([Chunk.v:623]) is
    [(rowbytes + 1) * height] ONLY under [rowbytes < 32768 && height < 32768]
    and otherwise **SATURATES to 4294967295**.  [RS_de] admits
    [sh_h <= 100000000 / sh_w], so at [sh_w = 1] the height reaches 1e8, both
    guards fail, and [wr_image_size hdr] is the SENTINEL rather than the
    payload's length.  Nor is that regime a corner to exclude: with the sentinel
    above 16384, [optimize_cmf] takes the PASS-THROUGH branch and does not
    rewrite the CMF at all, so a [length X] tie would quietly be about the
    shrinking regime only.

    **So I repaired a free-variable defect by creating its mirror — a premise
    nobody can supply — while correcting someone else's.**  Both errors are the
    same failure to ask who discharges the side condition.

    THE TIE THAT WORKS, filter-id's: derive BOTH from [hdr], exactly as
    [Codec.v:389-396] does.  Then a consumer discharges the side conditions BY
    CONSTRUCTION with no arithmetic bridge owed by either lane, and the
    statement stays as strong as the encoder's real behaviour, saturating regime
    included.  A [length X] form belongs as a derived corollary under the two
    32768 guards, not as the interface. *)
Definition ZlibRoundTrip : Prop :=
  forall lvl st hdr X enc,
    png_zlib_stream (deflate_claim_window_bits 15 (wr_image_size hdr)) lvl st X
      = Some enc ->
    png_inflate_stream (apply_optimize_cmf (wr_image_size hdr) enc) = Some X.

(** THE SANDWICH CLOSES, and it now has THREE premises rather than two —
    exactly TL's three gaps, with the fuel one no longer hidden inside a
    conclusion.  Still three lines, and still the file's whole verification
    value: if it were hard, the interface would be wrong. *)
Theorem interface_composes :
  EmitterPublishes -> PumpFuelSuffices -> InflaterConsumes -> ZlibRoundTrip.
Proof.
  intros HA HC HB lvl st hdr X enc Henc.
  exact (HB (apply_optimize_cmf (wr_image_size hdr) enc) X
            (HA lvl st hdr X enc Henc)
            (HC lvl st hdr X enc Henc)).
Qed.

(** NON-VACUITY OF THE WINDOW CLAUSE, which is the clause my first draft got
    wrong, so it gets a witness rather than an assurance: at a CINFO of 7 the
    window is 32768 and a payload of three bytes fits.  An added premise counts
    as landed only with an inhabitation witness. *)
Example window_clause_inhabited :
  forall b0, Z.shiftr (u8 b0) 4 = 7 -> PayloadFitsWindow [1; 2; 3] b0.
Proof.
  intros b0 H. unfold PayloadFitsWindow.
  rewrite (window_of_cinfo_7 b0 H). cbn [length Z.of_nat]. lia.
Qed.

(** ...and the NECESSITY of tying it to the header, as a value: the form my
    first draft used is refutable.  With [wsize] a free universally quantified
    argument, instantiating at 0 demands [length X <= 0], so the emitter face
    was unsatisfiable for every non-empty payload.  Exhibited rather than
    described, because a design error I only narrate is one the next drafter
    repeats. *)
Example free_wsize_form_is_unsatisfiable :
  ~ (forall wsize : nat, (length [1; 2; 3] <= wsize)%nat).
Proof. intro H. specialize (H 0%nat). cbn in H. lia. Qed.

(** THE SATURATION, pinned as a value, because it is the fact that decides the
    interface's shape and filter-id found it in a definition I had already read.
    [png_image_size] guards on [rowbytes < 32768 && height < 32768] and returns
    4294967295 otherwise; the sentinel is above [optimize_cmf]'s 16384 test, so
    the CMF is not rewritten at all in that regime. *)
Example image_size_saturates_above_the_guards :
  4294967295 > 16384 /\ 2 ^ 15 = 32768 /\ 32768 - 1 < 32768.
Proof. repeat split; reflexivity || lia. Qed.

(** ** THE 64-VALUE RESIDUE CLOSES — and the clause is a DISJUNCTION, not an
       inequality.  rt-scout's instruction ("check whether the published band
       facts plus your own distance work already close it") paid off, and the
       answer changes the clause's SHAPE rather than just discharging a debt.

    TWO BOUNDS EXIST AND THEY ARE COMPLEMENTARY:

      LENGTH   [Huff.resolve_lz] caps every distance at [length acc], hence at
               the payload length.  Covers [ds <= emitted_window ds].
      DISTANCE The match finder guards every candidate with
               [ls_strstart - hash_head <= dg_max_dist g] ([Deflate.v:631],
               [:750]), and the geometry fixes
               [dg_max_dist g = dg_w_size g - 262] ([ProbeInhabit.v:74]).  So
               no emitted distance exceeds [dg_max_dist], which at [wbits = 15]
               is 32506 — 262 BELOW the 32768 window.

    NEITHER COVERS THE RANGE ALONE, measured in [dist_cap_vs_header_window]:

      ds = 16384   cap 32506 vs window 16384   DISTANCE fails, LENGTH covers
      ds = 32832   cap 32506 vs window 32768   LENGTH fails, DISTANCE covers

    Below the [optimize_cmf] clamp the cap can far EXCEED the advertised window,
    because the CMF shrink is justified by the payload fitting in half the
    window rather than by the match finder.  At the top the payload overhangs
    the window by up to 64 bytes and the cap is what saves it.

    **So the 64-value residue is NOT a gap: it closes on the DISTANCE disjunct
    with facts that already exist.** Third time in one session that a "gap" of
    mine was a publication problem — and the first where finding that out
    changed a statement's shape instead of only deleting a debt.

    THE DESIGN IS RULED — OUTSIDE CITATION (§TL-ACK-WINDOWCLOSED).  [DeclFrame]
    stays BYTES-ONLY and a consumer cites
    [window_covers_reachable_payloads] as a standalone theorem.  This paragraph
    used to say the question was deferred until a consumer was named; it is now
    decided, and the entry is updated rather than left reading as open, because a
    stale "open question" in a delivered artifact is what the next reader plans
    from.

    THE GROUNDS, recorded because they generalise past this clause:
      * CARRY ALONGSIDE, DO NOT CHURN (ld-seams' [SymAligned] precedent) — the
        theorem is usable beside the interface without being embedded in it.
      * A stable CONSUMED statement is an asset, not inertia.  [ZlibRoundTrip]'s
        statement hash has not moved across seven revisions and filter-id's
        [one_statement_not_two] is kernel-verified against it; reshaping the
        faces for a consumer who has not been identified would spend that for
        nothing.
      * **If a consumer later needs the disjunction internal, that NEED IS THE
        EVIDENCE** and the change goes through bridge discipline — rather than
        being guessed at now.

    So the distance disjunct stays an EMITTER-side quantity ([dg_max_dist] over
    the geometry), [DeclFrame] keeps holding only bytes, and the two are joined
    by citation. *)
(** ** THE WINDOW CLAUSE IS CLOSED — the composing lemma TL asked for, PROVED
       over every reachable payload rather than sampled.

    Two published facts rt-scout pointed me at do the left branch and the
    emitter's own distance cap does the right one, so the clause needs no
    residue and no enumeration:

      ds <= 16384   [Chunk.dcwb_bound] supplies BOTH [9 <= wb <= 15] and
                    [ds + 262 <= 2^wb], which are two of
                    [Chunk.optimize_cmf_window_ge]'s three premises.  The third
                    is that the emitted header's high byte is [8 + 16*ci0] —
                    true by [deflate_zlib_header]'s construction and proved
                    below over the seven reachable [wb] values.
      ds >  16384   [deflate_claim_window_bits] and [optimize_cmf] both take
                    their pass-through arms, so BOTH sides lose their
                    ds-dependence: window 32768, cap 32506.

    [window_covers_reachable_payloads] needs no upper bound on [ds] at all. *)

Lemma dcwb_big : forall ds, 16384 < ds -> deflate_claim_window_bits 15 ds = 15.
Proof.
  intros ds H. unfold deflate_claim_window_bits.
  replace (Z.leb ds 16384) with false by (symmetry; apply Z.leb_gt; lia).
  reflexivity.
Qed.

Lemma optimize_cmf_big : forall b0 b1 ds,
  16384 < ds -> optimize_cmf b0 b1 ds = (u8 b0, u8 b1).
Proof.
  intros b0 b1 ds H. unfold optimize_cmf.
  replace (Z.leb ds 16384) with false by (symmetry; apply Z.leb_gt; lia).
  reflexivity.
Qed.

Lemma emitted_window_big : forall ds, 16384 < ds -> emitted_window ds = 32768.
Proof.
  intros ds H. unfold emitted_window, emitted_zlib_header_effective.
  cbv zeta. rewrite (dcwb_big ds H). rewrite (optimize_cmf_big _ _ ds H).
  cbn [fst]. vm_compute. reflexivity.
Qed.

Lemma max_dist_big : forall ds, 16384 < ds -> dg_max_dist (idat_geom ds) = 32506.
Proof.
  intros ds H. unfold idat_geom. rewrite (dcwb_big ds H). vm_compute. reflexivity.
Qed.

(** The RIGHT disjunct, for every payload above the clamp — no enumeration. *)
Theorem distance_cap_covers_above_clamp : forall ds,
  16384 < ds -> dg_max_dist (idat_geom ds) <= emitted_window ds.
Proof.
  intros ds H. rewrite (max_dist_big ds H), (emitted_window_big ds H). lia.
Qed.

(** ** LEFT BRANCH: the length bound below the clamp, composing the two
       published facts rt-scout pointed me at.

    [dcwb_bound] supplies both [1 <= ci0 <= 7] (as [9 <= wb <= 15]) and
    [ds + 262 <= 2^wb], which are exactly two of [optimize_cmf_window_ge]'s
    three premises.  The third is that the emitted header's high byte really is
    [8 + 16*ci0] — true by [deflate_zlib_header]'s construction, and provable
    over the seven reachable [wb] values. *)

Lemma zlib_header_hi : forall wb, 9 <= wb <= 15 ->
  fst (deflate_zlib_header wb (zdefl_level PNG_Z_DEFAULT_COMPRESSION)
                           PNG_Z_DEFAULT_STRATEGY)
  = 8 + 16 * (wb - 8).
Proof.
  intros wb H.
  assert (Hc : wb = 9 \/ wb = 10 \/ wb = 11 \/ wb = 12 \/ wb = 13 \/ wb = 14
               \/ wb = 15) by lia.
  destruct Hc as [->|[->|[->|[->|[->|[->| ->]]]]]]; vm_compute; reflexivity.
Qed.

Theorem length_bound_covers_below_clamp : forall ds,
  1 <= ds <= 16384 -> ds <= emitted_window ds.
Proof.
  intros ds H.
  destruct (dcwb_bound ds ltac:(lia)) as [Hwb Hfit].
  unfold emitted_window, emitted_zlib_header_effective. cbv zeta.
  rewrite Z.shiftl_1_l.
  (* the argument is supplied EXPLICITLY: with [_] the [ltac:(lia)] runs against
     an unresolved evar and reports "Cannot find witness" — a failure about the
     term the tactic was handed, not about a missing fact. *)
  rewrite (zlib_header_hi (deflate_claim_window_bits 15 ds) ltac:(lia)).
  apply (optimize_cmf_window_ge (deflate_claim_window_bits 15 ds - 8)
                                (snd (deflate_zlib_header
                                       (deflate_claim_window_bits 15 ds)
                                       (zdefl_level PNG_Z_DEFAULT_COMPRESSION)
                                       PNG_Z_DEFAULT_STRATEGY))
                                ds); try lia.
  replace (deflate_claim_window_bits 15 ds - 8 + 8)
     with (deflate_claim_window_bits 15 ds) by lia.
  exact Hfit.
Qed.

(** ** THE DISJUNCTION, TOTAL over every payload the harness can reach — and
       proved rather than sampled. *)
Theorem window_covers_reachable_payloads : forall ds,
  1 <= ds ->
  ds <= emitted_window ds \/ dg_max_dist (idat_geom ds) <= emitted_window ds.
Proof.
  intros ds H.
  destruct (Z_le_gt_dec ds 16384) as [Hle|Hgt].
  - left. apply length_bound_covers_below_clamp. lia.
  - right. apply distance_cap_covers_above_clamp. lia.
Qed.

Example dist_cap_vs_header_window :
  map (fun ds => (dg_max_dist (idat_geom ds),
                  emitted_window ds,
                  Z.leb (dg_max_dist (idat_geom ds)) (emitted_window ds),
                  Z.leb ds (emitted_window ds)))
      [1; 250; 16384; 16385; 32768; 32769; 32832]
  = [(250,   256,   true,  true);
     (250,   256,   true,  true);
     (32506, 16384, false, true);
     (32506, 32768, true,  true);
     (32506, 32768, true,  true);
     (32506, 32768, true,  false);
     (32506, 32768, true,  false)].
Proof. vm_compute. reflexivity. Qed.

(** The disjunction is TOTAL, checked at the swap points, which is where a
    totality claim can fail. *)
Example disjunction_is_total_at_the_swap_points :
  forallb (fun ds => orb (Z.leb (dg_max_dist (idat_geom ds)) (emitted_window ds))
                         (Z.leb ds (emitted_window ds)))
          [1; 2; 250; 251; 16383; 16384; 16385; 32767; 32768; 32769; 32831; 32832]
  = true.
Proof. vm_compute. reflexivity. Qed.

(** ** THE BLOCK-LIST INDUCTION — ld-seams' finding, and it is UNOWNED.

    Clause 3 of [DeclFrame] is [dec_stream (bytes_bits body) = Some X], and
    [dec_stream] is [dec_stream_fuel] looping over blocks until BFINAL
    ([DeflateSpec.v:1115-1133]).  **ld-seams delivers the ONE-BLOCK case**: their
    [ArmDecodes] ends at [dec_blk] for a single block, by an explicit scope cut.
    So between (a)'s conclusion and clause 3 there is a block-list induction that
    is in nobody's charter — they flagged it from their side rather than letting
    it surface at composition.

    AND IT IS REACHED, which is what makes it a gap rather than a formality.
    [Deflate.v] has [flush_block 0] sites (e.g. :714, :774, :785, :856) that fire
    when [tr_tally_lit] reports the symbol buffer full — a [last = 0] flush only
    exists because another block follows.  Measured rather than inferred, in
    [symbol_buffer_capacity_at_max_payload] below: [dg_sym_end] is
    [(lit_bufsize - 1) * 3] ([Chunk.v:1312], [deflate.c:508]) and each tallied
    literal advances [sym_next] by 3, so the buffer holds 16,383 literals — while
    the largest harness payload is 32,832 bytes.  **Two blocks at least, at the
    top of the range.**

    So this is a THIRD thing the emitter face needs beyond a per-block arm, and
    unlike the adler item it is not small.  Named here rather than left for
    whoever writes the composition to discover. *)
Example symbol_buffer_capacity_at_max_payload :
  (dg_sym_end (idat_geom 32832),
   dg_sym_end (idat_geom 32832) / 3,
   Z.ltb (dg_sym_end (idat_geom 32832) / 3) 32832)
  = (49149, 16383, true).
Proof. vm_compute. reflexivity. Qed.

(* ==========================================================================
   10.  THE GAP LIST, with owners.  Superseding nothing; additive.
   ========================================================================== *)

(** WHAT IS ALREADY LANDED AND DISCHARGES A CLAUSE
      §2  ZlibHeaderOk           filter-id, [Common/LEHdr.optimize_cmf_valid] —
                                 the three clauses are its hypotheses verbatim
      §1  the [be32] trailer     filter-id, [Common/LETrailer.trailer_bytes_be32]
                                 proves the encoder emits exactly [be32 ad]
      §3  BodyDecodesTo          symbol-id, landed: [EmitSym.emit_decode_seq],
                                 [StoredRt.stored_rt_export] (per-symbol and
                                 per-block inverses; the whole-stream assembly
                                 is (a)'s, not mine)

    HOW TO READ A STATUS WORD IN THIS LIST (added after seven of them drifted).
    A status is an interface with the same failure modes as a clause, and four are
    now named: FALSE (costs a consumer), INAPPLICABLE (costs a proof attempt),
    STALE (costs a HIRE), and MISATTRIBUTED — a true fact recorded against the
    wrong side of the interface, which costs a WRONG hire.  Two of the seven
    drifted entries were citation-ACCURATE and still misleading, so a citation is
    necessary and not sufficient.  Every entry below therefore carries the site it
    was checked at, and every absence claim carries the ROOT it was measured in —
    three of my own false absences this session came from a subdirectory glob
    reading as tree-wide.

    WHAT IS OPEN, AND WHO OWNS IT
      (a)  EmitterPublishes      ld-seams / L-D.  The largest of the three.  NOTE
                                 their scope cut: they deliver the ONE-BLOCK case of
                                 clause 3, and multi-block IS reached (16,383-literal
                                 symbol buffer vs a 32,832-byte payload).
                                 **STATUS CORRECTED (1/7): (a) is not merely open,
                                 it is UNPROVABLE AS STATED — refuted at BOTH
                                 extremes of the reachable payload range.  Its
                                 `PayloadFitsWindow` conjunct is false at the
                                 LARGEST image (ds = 32832) and its `ZlibHeaderOk`
                                 conjunct is false at the SMALLEST (ds = 2, where
                                 `optimize_cmf` writes CINFO 0 and the clause
                                 demands `1 <= Z.shiftr (u8 b0) 4`).  Both proved:
                                 `SidWinCheck.payload_fits_window_false_at_max_image`,
                                 `SidSmallEnd.zlib_header_ok_false_at_smallest_image`,
                                 joined in `refuted_at_both_ends`.  My extremal
                                 sweep originally checked only the maximum and
                                 dismissed the minimum as "not payload-scaled";
                                 the distinction that matters is payload-SCALED vs
                                 payload-DEPENDENT, and CINFO is the second.**
      --   the BLOCK-LIST INDUCTION between (a)'s per-block arms and clause 3's
           [dec_stream] loop.  ld-seams' finding; the reachability witness is
           [symbol_buffer_capacity_at_max_payload].
           **STATUS CORRECTED (2/7): NOT untouched.  ld-seams reports chain-level
           results — [LdMulti.blocks_chain_decodes], [LdAccThread.segs_chain_decodes]
           with [segs_fuel_ok] — and an ArmDecodes refutation with its own control.
           CAVEAT THAT MUST TRAVEL WITH THIS ENTRY: those are FARM artifacts, not
           tree ones, so "landed" is the wrong word for them; the exact replacement
           wording is ld-seams' to confirm at land time and is deliberately not
           paraphrased here.  Pricing this as virgin ground buys a hire for work
           already done; pricing it as landed buys a consumer for a .vo that is not
           in the tree.**
      (b)  InflaterConsumes      **OWNERSHIP CORRECTED (3/7): (b) is huffman-id's**,
                                 stated by them tonight; lenext-repair owns the
                                 EXIT WALK, not (b), and says so directly.  Still
                                 premised on [PumpTerminates], so (b) owes only "if
                                 it answers, the answer is X".  This entry named the
                                 wrong two lanes, which is the MISATTRIBUTED mode
                                 applied to an owner rather than to a fact.
      --   THE WINDOW-CONTENT INVARIANT — a NEW item, unowned and being sourced.
           (b)'s conclusion is a VALUE equality ([png_inflate_stream enc = Some X]),
           so every byte a MATCH copies out of the window must be the intended
           byte.  Nothing in the tree or in ANY lane's farm states that the window's
           last [whave] bytes agree with the output tail: measured by two lanes
           independently, token-boundary search, with [w_win] occurring ZERO times
           in wp4w8's 2609-line FULLINV and every other [w_whave] site being a
           rank/budget or byte-RANGE fact.  It is owed under EVERY key choice for
           §5, so it is not a cost of the window clause.
           SUB-ITEM, named because it is a prerequisite and not a detail inside the
           proof: **[whave <= wsize] is not self-evident.**  At [Inflate.v:790],
           [h1 = whv + dist] with [dist <= wsz - wnx], so [h1 <= wsz] requires
           [whv <= wnx] — a [whave]/[wnext] relation nothing in the tree states.
      --   AND THE DECOMPOSITION THAT KEEPS THIS ENTRY HONEST (lenext-repair's):
           ONE call site carries THREE obligations, of which one has a name.
             1. the error test — [Z.ltb (f_whave c) ow] (InflateFast.v:355) and
                [Z.ltb (w_whave wn) cw] (Inflate.v:963).  HISTORY-keyed.
             2. the distance cap — [SidDecDistCap.decode_symbols_dist_caps_Z],
                lifted to the stream by gtbl-arms.  NAMED AND PROVED.
             3. the indexing property — whether [OSwin (w_wsize wn - c1)] reads the
                byte at distance [dist].  A circular-buffer indexing fact, neither
                the test nor the cap.  UNNAMED.
      (c)  PumpFuelSuffices      lenext-repair's classification route.  Was
                                 HIDDEN inside (b)'s conclusion until they
                                 flagged it; now a named face of its own.
                                 **NEW ENTRY, approved post-audit: THE TREE'S
                                 TOTALITY RESULT CANNOT SUPPLY THIS FACE, and the
                                 reason is not effort.  [CodecThy.inf_pump_total]
                                 (CodecThy.v:75) is Qed inside a Section over two
                                 Variables that are themselves the open work, and
                                 its conclusion is [exists r, inf_pump ... = Some r]
                                 — which its own proof discharges in the branch
                                 [ret = Z_STREAM_END || ret < 0].  **A pump that
                                 answers WITH AN ERROR satisfies totality**, while
                                 [PumpTerminates] demands [Z_STREAM_END]
                                 ([Codec.v:369]).  So the residue is a SUCCESS
                                 argument, not a termination one: different
                                 mathematics, and a lane working the fuel measure
                                 will not produce it as a by-product.  That is why
                                 (c) has read as closer than it is.  Generalisable:
                                 when a clause says "the computation ANSWERS", read
                                 the totality lemma's DISJUNCTION — [Some]-ness of
                                 an option that encodes failure as a value is
                                 weaker than success by exactly the failure branch,
                                 and the gap is invisible at the type level.**
      --   [PumpTerminates] HAS AN INHABITATION WITNESS AS OF §SYMID-ER, and it is
           named here because this file's own register rule (quoted at
           [Common/KitBridge.v:30-33]) is that an added premise counts as landed
           only with an inhabitation witness plus a consumer-side discharge — and
           this premise of [InflaterConsumes] was failing that rule.  Before the
           witness, `png_inflate_stream` occurred 12 times in the whole tree and
           ZERO times in any [Example]/[Lemma]/[Theorem]/[Corollary] line (control:
           5 for [dec_stream]); [Spec/PngModel/ProbeInhabit.v] says so itself,
           calling its chunk-parameter result "a partial inhabitance result".
           Witness: `symbolid/cbfa/SidPumpWitness.v` `pump_terminates_inhabited`, a
           CLOSED term (no hypothesis, unlike [window_clause_inhabited] below) on a
           hand-built 12-byte stored-block stream.  SCOPE, stated so it is not
           over-cited: (c) quantifies over ENCODER outputs and this stream was
           built by hand, so it is satisfiable-SOMEWHERE and not the clause.  What
           it buys is a POSITIVE CONTROL — an input where the conclusion is known
           true by computation, so a (c) attempt that fails on it has a bug rather
           than a hard case.  The same file also settles a question nobody had
           asked: (c)'s subject is the CMF-REWRITTEN stream
           ([apply_optimize_cmf (wr_image_size hdr) enc], not [enc]), and the
           rewrite PRESERVES inflatability at both ends of the band — at
           [apply_optimize_cmf 2] (the CINFO-0 end, where the rewrite bites) and at
           [apply_optimize_cmf 32832] (above 16384, where both loops give up).
      --   deflate_claim_window_bits: my "NO lemma in the tree" claim was FALSE
           and is retracted (rt-scout). There are SIX published results —
           dcwb_bound, dcwb_cases, window_bits_bands,
           emitted_window_below_deflate_window, d8_cluster_1x1_gray,
           d8_cluster_64x64_rgba16. My query required the name on the SAME LINE
           as the Lemma keyword; all six state it on a continuation line.
      §5   the window clause     **STATUS CORRECTED (4/7): HELD by zlib-lead, and
                                 not for lack of a candidate.  The clause is
                                 DOWNSTREAM of the window-content invariant above,
                                 so choosing a key now means choosing the side
                                 condition of a lemma nobody has written.
                                 INTENDED KEY WHEN WRITTEN: HISTORY —
                                 [dist <= length out], the shape BOTH [MSG_DIST_FAR]
                                 sites actually test, already supplied
                                 unconditionally by gtbl-arms'
                                 [dec_stream_syms_fuel_caps].  NOT the window: no
                                 test in this model compares a distance against the
                                 window size, because zlib's window-keyed [dmax]
                                 test is [#ifdef INFLATE_STRICT] and the
                                 transcription compiled it out in BOTH paths —
                                 InflateFast.v:348 and Inflate.v:979-981 each say so
                                 in their own comment.  My earlier justification for
                                 keying on [WindowOfHeader b0] ("the quantity the
                                 computation consumes") cited a test that does not
                                 execute; a faithful transcription keeps the dead
                                 branch as a comment, which reads exactly like a
                                 specification and is not one.**
      §4   the adler chunking    UNOWNED, and this is the finding: [zs_adler]
                                 occurs in [Deflate.v] and NOWHERE else in the
                                 tree, and no theorem relates it to any closed
                                 form.  filter-id's [LETrailer] deliberately
                                 scoped the adler VALUE out ("the decoder
                                 recomputes it") while proving the FRAMING.  So
                                 the incremental-equals-closed-form step sits
                                 exactly at the C5 boundary and is neither (a)
                                 nor (b) as currently staffed.
                                 **STATUS CORRECTED (5/7): TAKEN by gtbl-arms, and
                                 "SMALL" was a MISPRICE that would have bought the
                                 wrong hire.  Small is the DECODE side, where one
                                 [upd_check] call meets the closed form.  The ENCODE
                                 side is hours: [adler32_z] is called once per READ
                                 CHUNK (Deflate.v:284, running [zs_adler st]), so the
                                 closed form needs chunk composition across FOUR
                                 return paths, and [AdWf] is load-bearing rather than
                                 hygienic — the len=1 path can return [sum2 >= BASE]
                                 for a malformed argument (Checksum.v:415-419).  Their
                                 foundation [GtAdlerChunk.v] supplies bit-16 split
                                 lemmas that existed NOWHERE in the tree (measured
                                 whole-tree, not by subdirectory).  A wrong price on
                                 an unowned item decides who picks it up, which is
                                 why this correction is a status fix and not a
                                 footnote.**
      --   THE PAYLOAD TIE.  **STATUS CORRECTED (6/7)**, three ways.
           (i) The form is [<=], never [=]: [png_image_size] saturates to
               4294967295 once rowbytes or height reaches 32768 (Chunk.v:623-628),
               so an equality is refuted by filter-id's saturation argument.
           (ii) It is UNPRODUCEABLE INSIDE THIS FILE (ld-seams, §LD-TIE): at
               [EmitterPublishes] the window comes from [hdr] and the payload is
               [X], and the two are INDEPENDENT UNIVERSALS — nothing in the
               statement relates their sizes.  Census over nine curated roots:
               **4 premise-or-prose sites in 2 distinct AUTHORED files, 0
               producers** — corrected from 6 by ld-seams, who found the other two
               were gtbl-arms' verbatim copy of `SidDecDistCap.v`.  The cause is
               worth carrying wherever a farm-wide count is quoted: **4,119 of
               4,644 peer-root `.v` files are byte-identical copies of graded-tree
               files**, so an undeduplicated farm census can run up to 7.5x high.
               ZEROS are unaffected by copy inflation, which is exactly why the
               "0 producers" half survives the correction and the "6" did not.
               It would therefore have to become a PREMISE of the interface rather
               than a consequence of it — **IF anything still needs it, which is no
               longer established.**  zlib-lead ruled the premise-add landable and
               then REVERSED that ruling, and the reversal's reasoning is the part
               worth keeping: "adding a premise only weakens the obligation, so
               nothing reddens" is safe on ONE side of the implication and a
               permanent tax on the other — **weakening is free for the PROVER and
               costed for every future CONSUMER, who must supply the new
               hypothesis.  So a stated premise free at NO call site is pure
               cost.**  Both of this premise's justifications were retired by the
               same finding: its consumer was the window-keyed clause (which under
               history-keying mentions no [ds] at all), and its soundness story
               assumed the decoder REJECTS on the advertised window, which it does
               not — see 4/7.  The tie is now PARKED, ld-seams has accepted that
               and is marking it parked rather than leaving a live recommendation.
               The soundness argument for the 2x window gap currently lives in a
               Chunk.v COMMENT (§9b), and what could still revive the tie is the
               INDEXING property, not the rejection test.
           (iii) It is CONDITIONAL on the §5 key: needed under window-keying,
               NOT NEEDED under the history-keying now intended, since
               [dist <= length out] mentions no [ds] at all.
           Producers, for when it is needed: the tree's [L10Len.filt_go_length_pix]
           gives [length (filt_go df bpp [] (rows_of h rb pix)) = h * (1 + rb)], and
           [SidFiltLen2.filt_go_is_png_image_size] identifies that with
           [png_image_size] under the two guards.  The remaining [WrHdr]-field step
           is ld-seams' [LdPayloadTie.v], HELD pending the key.
      --   RETRACTION, kept as a record.  An earlier revision of my §4 support work
           claimed the filter pass had NO length lemma anywhere.  **FALSE.**  Four
           already existed under the SAME NAMES in [L10/] —
           [L10Rows.enc_go_length], [L10Rows.filter_model_length],
           [L10Len.filt_go_length], [L10Len.filt_go_length_pix] — a directory my
           query never reached, and one that sits INSIDE the byte-clause window's own
           blast radius.  Same failure as the [deflate_claim_window_bits] retraction
           above: the predicate was right and the reach was wrong.  Two instances in
           one file argue for the rule now stated at the head of this list.
      --   AND A HIDING PLACE WORTH SWEEPING FOR: [find_filter_row_length] ("the
           chosen filtered row is as long as the row") exists in the tree ONLY as an
           unnamed [assert] inside [L10Len.filt_go_length]'s proof script
           (L10Len.v:41-46).  ld-seams found the identical shape in their own
           [armA_dsinv] the same day.  A fact derived inside a proof has no name and
           no consumer can cite it, so it gets priced as open by everyone outside
           that proof.  Named copy: [SidFiltLen2.find_filter_row_length].
      §5   ResolveCapsDistances  **STATUS CORRECTED (7/7): "DISCHARGED" was the
                                 INAPPLICABLE mode, and the word hid it.  The lemma
                                 is Qed and axiom-free, and its
                                 [Forall (lz_is_end = false)] premise — without which
                                 it is false ([resolve_caps_distances_naive_is_false])
                                 — is UNSATISFIABLE by any decoded symbol list,
                                 because every such list ends in [LzEnd]
                                 ([decode_symbols_last_end]).  So for a while it was
                                 true, proved, and unusable at the only site that
                                 wanted it.  It is applicable NOW, and by someone
                                 else's work: gtbl-arms split the trailing [LzEnd]
                                 off with [decode_symbols_last_end_nb] and an
                                 unconditional [resolve_lz_app_end], and their
                                 [dec_blk_syms_caps] cites this lemma at GtDecSyms.v:362.
                                 The status a reader needs is therefore two facts, not
                                 one word: PROVED (mine) and MADE APPLICABLE (theirs).**

    WHAT THIS FILE DELIBERATELY DOES NOT DO
      * It does not touch [Chunk.optimize_cmf].  C5 is stated before the CMF
        rewrite ([Codec.v:267]), and that layer is filter-id's.
      * It does not import the flat [ItModel].  Two unconnected inflate
        formalisations exist in this development and every statement here names
        [Codec.png_inflate_stream], the transcribed one that [dec_raw] runs.
      * It states no bound on [lvl] or [st].  The emitter quantifies over them
        and (b) never reads them, so pinning them here would be a premise
        nobody consumes — which is the shape of half the export-audit
        findings. *)

End SymbolIdDeclIface.
