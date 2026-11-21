(** * OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.GtAdlerChunk — §4 (adler chunking): CLOSED,
      and TWO price corrections in opposite directions

    Titled at the DESTINATION root while still in the lane, so that lane form and
    landed form are byte-identical and the landing is a pure copy — no rewrite
    step means no rewrite to get wrong, and the declared digest cannot go stale
    between declaration and slot.

    DeclIface's gap list carries §4 as "UNOWNED ... It is SMALL — both sides call
    one function", and symbol-id has cleared me to take it.  Checking the price
    against the artifact FIRST, per this lane's standing order, the smallness
    claim is about a DIFFERENT question than the one §4 actually needs:

      * SMALL, and true: the DECODE-side check passes by function equality — both
        ends call [Checksum.adler32_z] over the same bytes, so no
        encoder-vs-decoder refinement arises.  [Checksum.v:511-519] says exactly
        this, and says the closed form "is left for whoever needs a closed form".
      * NOT small, and it is what §4 is: the ENCODER accumulates INCREMENTALLY.
        [Deflate.read_buf] (:284) applies [adler32_z (zs_adler st) false dat] once
        per read chunk, while [TrailerMatchesPayload] states the closed form over
        the WHOLE payload.  Those agree only via a chunk-composition law

          adler32_z (adler32_z a false xs) false ys = adler32_z a false (xs ++ ys)

        and that law has to cross [adler32_z]'s FOUR return paths ([len = 1],
        [isnull], [len < 16], [len >= 16] with NMAX blocking) — because the
        blocking of [xs ++ ys] is not the concatenation of the blockings of [xs]
        and [ys].  The tree's own note names the residue: "the case split over the
        four return paths and the range facts that turn the conditional
        subtractions into [mod]".

    So §4 is the item the tree PARKED with a named residue, not a small one.  The
    misprice is traceable: the gap list's "both sides call one function" is the
    decode-side sentence from [Checksum.v] applied to the encode-side question.

    WHAT THIS FILE DOES.  The part every version of the law needs, and the part
    the [len = 1] quirk threatens: the WELL-FORMEDNESS invariant.  Chunk k+1 reads
    its incoming adler by splitting it at bit 16 ([Z.land _ 65535] and
    [Z.land (Z.shiftr _ 16) 65535]), and that split is only exact if the previous
    chunk returned both halves below [ADLER_BASE].  [Checksum.v:415-419] records
    that the [len = 1] path can return [sum2 >= BASE] for a malformed argument, so
    the invariant is not free.

    WHAT IT NOW CONTAINS, since the header above describes only the foundation it
    started as.  §4 is CLOSED: [adler32_z_chunk] is the composition law and
    [adler32_z_chunks] the multi-chunk fold that [read_buf] actually produces,
    both via [adler32_z_closed_form] ("[ad_run] once, then one [mod]"), which
    discharges the residue [Checksum.v:512-519] names as the file's one open item.

    THE PRICE CORRECTION ABOVE IS ITSELF CORRECTED, in the opposite direction.
    Yesterday I repriced §4 UPWARD off a reading of [Checksum.v].  Today,
    searching the tree at the OUTPUT state instead of by the names I had coined,
    the algebra turned out to already exist: [ZChecksum.adl_raw_mod] (the deferral
    congruence), [ZChecksum.adl_canon], [ZChkAdl.adl_raw_app], [ZChkAdl.condsub],
    and inside [Checksum.v] itself [ad_run_cong] / [ad_mod_cong] /
    [ad_do16_split].  **A price derived from one file is a price for that file** —
    and a reprice is not a one-time act.

    Three structures priced as expensive here were free: the [len >= 16] path
    (every exit is [ad_mod]-reduced), the NMAX blocking (the residue invariant
    needs no index arithmetic), and [ad_inner]'s iteration count (the proof never
    mentions it).  Each was priced from the shape of the CODE; none of it appears
    in the PROOF.

    GTBL-ARMS, 2026-08-19.  Landing candidate, declared to rt-scout; not landed.
    Read-only against the graded tree. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk Checksum Deflate.
(** [Require] WITHOUT [Import], deliberately: [Common/ZChecksum] defines its own
    [NMAX] (and [ABASE]), so importing it would silently shadow
    [Checksum.NMAX] — the constant this file's NMAX-blocking reasoning is about.
    Only two names are needed from it and both are cited fully qualified. *)
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Common Require ZChecksum.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ######################################################################### *)
(* 1.  The bit-16 split, which nothing in the tree had                        *)
(* ######################################################################### *)

Lemma land16_mod : forall x, Z.land x 65535 = x mod 65536.
Proof.
  intros x. replace 65535 with (Z.ones 16) by (rewrite Z.ones_equiv; reflexivity).
  rewrite Z.land_ones by lia. reflexivity.
Qed.

(** The two halves occupy disjoint bit ranges, which is what makes [Z.lor] the
    same as addition here — the step that lets the split be arithmetic instead of
    bit-twiddling from then on. *)
Lemma land_disjoint_shiftl16 : forall a s,
  0 <= a < 65536 -> 0 <= s -> Z.land a (Z.shiftl s 16) = 0.
Proof.
  intros a s Ha Hs.
  destruct (Z.eq_dec a 0) as [->|Hne]; [apply Z.land_0_l|].
  apply Z.bits_inj'. intros n Hn.
  rewrite Z.bits_0, Z.land_spec.
  destruct (Z_lt_le_dec n 16) as [Hlt | Hge].
  - rewrite Z.shiftl_spec_low by lia. apply andb_false_r.
  - rewrite (Z.bits_above_log2 a n); [apply andb_false_l | lia |].
    assert (Z.log2 a < 16) by (apply Z.log2_lt_pow2; lia). lia.
Qed.

Lemma lor_is_add16 : forall a s,
  0 <= a < 65536 -> 0 <= s -> Z.lor a (Z.shiftl s 16) = a + s * 65536.
Proof.
  intros a s Ha Hs.
  assert (Hd : Z.land a (Z.shiftl s 16) = 0)
    by (apply land_disjoint_shiftl16; assumption).
  (* [Z.add_nocarry_lor] does not exist; the pair that does is
     [Z.lxor_lor] (disjoint bits make xor and or agree) composed with
     [Z.add_nocarry_lxor].  Named here because the missing-lemma guess costs a
     compile each time. *)
  rewrite <- (Z.lxor_lor a (Z.shiftl s 16) Hd).
  rewrite <- (Z.add_nocarry_lxor a (Z.shiftl s 16) Hd).
  rewrite Z.shiftl_mul_pow2 by lia. reflexivity.
Qed.

Lemma lor_split_low : forall a s,
  0 <= a < 65536 -> 0 <= s -> Z.land (Z.lor a (Z.shiftl s 16)) 65535 = a.
Proof.
  intros a s Ha Hs.
  rewrite (lor_is_add16 a s Ha Hs), land16_mod.
  (* [Z.mod_add], not [Z.add_mul_mod_distr_r]: the goal's shape is
     [(a + s * c) mod c], which is the former's pattern exactly.  The latter
     wants [(a * c + b) mod (d * c)] and reports "no subterm matching" — an
     error about the PATTERN, not about the arithmetic. *)
  rewrite Z.mod_add by lia.
  apply Z.mod_small. lia.
Qed.

Lemma lor_split_high : forall a s,
  0 <= a < 65536 -> 0 <= s < 65536 ->
  Z.land (Z.shiftr (Z.lor a (Z.shiftl s 16)) 16) 65535 = s.
Proof.
  intros a s Ha Hs.
  rewrite (lor_is_add16 a s Ha (proj1 Hs)).
  rewrite Z.shiftr_div_pow2 by lia.
  replace (2 ^ 16) with 65536 by reflexivity.
  rewrite Z.div_add by lia.
  replace (a / 65536) with 0 by (symmetry; apply Z.div_small; lia).
  rewrite Z.add_0_l, land16_mod. apply Z.mod_small. lia.
Qed.

(* ######################################################################### *)
(* 2.  Well-formedness of an adler value, and why it is the load-bearing part  *)
(* ######################################################################### *)

(** "Both halves below BASE" — exactly the shape the NEXT chunk's split assumes,
    and exactly what [Checksum.v:415-419] warns the [len = 1] path can break for a
    malformed argument. *)
Definition AdWf (a : Z) : Prop :=
  0 <= Z.land a 65535 < ADLER_BASE
  /\ 0 <= Z.land (Z.shiftr a 16) 65535 < ADLER_BASE.

(** A value assembled from two in-range halves is well-formed: the split
    lemmas run the other way. *)
Lemma adwf_of_halves : forall a s,
  0 <= a < ADLER_BASE -> 0 <= s < ADLER_BASE -> AdWf (Z.lor a (Z.shiftl s 16)).
Proof.
  intros a s Ha Hs. unfold ADLER_BASE in *. split.
  - rewrite (lor_split_low a s ltac:(lia) ltac:(lia)). unfold ADLER_BASE. lia.
  - rewrite (lor_split_high a s ltac:(lia) ltac:(lia)). unfold ADLER_BASE. lia.
Qed.

(** The initial value the encoder starts from ([Deflate.deflate_reset], written
    in the tree's own idiom as [adler32_z 0 true []]) is well-formed — checked by
    computation rather than by reading it as 1. *)
Lemma adler_init_is_1 : adler32_z 0 true [] = 1.
Proof. vm_compute. reflexivity. Qed.

Lemma adwf_init : AdWf (adler32_z 0 true []).
Proof.
  (* compute the VALUE, then the two halves — not [vm_compute] on the whole
     [AdWf], which leaves [Z.le] in its raw comparison form and no tactic
     applies (the same shape as reducing a comparison and losing [lia]). *)
  rewrite adler_init_is_1. unfold AdWf.
  assert (H1 : Z.land 1 65535 = 1) by reflexivity.
  assert (H2 : Z.land (Z.shiftr 1 16) 65535 = 0) by reflexivity.
  rewrite H1, H2. unfold ADLER_BASE. split; lia.
Qed.

(* ######################################################################### *)
(* 3.  The growth bound, which is what turns a conditional subtraction into a  *)
(*     [mod] on the short paths                                               *)
(* ######################################################################### *)

Lemma ad_run_bound : forall l s,
  (forall b, In b l -> 0 <= b < 256) ->
  0 <= a_adler s ->
  a_adler s <= a_adler (ad_run s l)
  /\ a_adler (ad_run s l) <= a_adler s + 255 * Z.of_nat (length l).
Proof.
  induction l as [|b r IH]; intros s Hb Hs; unfold ad_run in *; cbn [fold_left length].
  - cbn. lia.
  - assert (Hb0 : 0 <= b < 256) by (apply Hb; left; reflexivity).
    assert (Hrest : forall x, In x r -> 0 <= x < 256)
      by (intros x Hx; apply Hb; right; exact Hx).
    destruct (IH (ad_do1 s b) Hrest ltac:(cbn [ad_do1 a_adler]; lia)) as [Hlo Hhi].
    cbn [ad_do1 a_adler] in Hlo, Hhi |- *.
    rewrite Nat2Z.inj_succ. lia.
Qed.

(** So on the [len < 16] path the single conditional subtraction IS exact: the
    running adler cannot exceed [2 * ADLER_BASE], because it starts below BASE and
    fewer than sixteen bytes add at most 3825. *)
Lemma short_path_one_subtraction : forall s l,
  (forall b, In b l -> 0 <= b < 256) ->
  0 <= a_adler s < ADLER_BASE ->
  (length l < 16)%nat ->
  a_adler (ad_run s l) < 2 * ADLER_BASE.
Proof.
  intros s l Hb Hs Hlen.
  destruct (ad_run_bound l s Hb ltac:(lia)) as [_ Hhi].
  assert (Z.of_nat (length l) <= 15) by lia.
  unfold ADLER_BASE in *. lia.
Qed.

(* ######################################################################### *)
(* 4.  THE CHUNK'S WELL-FORMEDNESS IS FREE BY CONSTRUCTION                     *)
(* ######################################################################### *)

(** symbol-id (§SYMID-EL) pointed me at ld-seams' loop invariant field
    [dli_bytes : Forall IsByte (zs_in (d_strm s))], whose comment names my own
    reason for splitting [read_buf_conserves_bytes] into two forms
    ("[read_buf]'s [map u8] is an identity only on bytes"), and suggested checking
    it before threading a byte premise through the §4 walk.

    CONTAINER, because a path is not an address and this one is not where a reader
    would assume: that field lives at
    [LdLoopInv.v:62] — **ld-seams' FARM, not the graded
    tree** (measured: 0 copies under a working folder, 1 under their farm).
    So it is not [Require]-able from here and would not be even if I wanted it —
    the same landing-unbuilt/farm-resident cost documented in [GtT0Discharge].
    zlib-lead relayed the bare filename to two lanes and has since corrected it;
    my first draft of this header inherited the ambiguity by naming the owner
    ("ld-seams' loop invariant") without naming the container, which is precisely
    the form that invites someone to try importing it.

    **Checked, and the answer is better than the field: for the ADLER's premise the
    obligation does not arise at all.** [ad_wf] ([Checksum.v:451]) demands
    [forall b, In b bs -> 0 <= b < 256] of the CHUNK, and [read_buf] hands
    [adler32_z] the chunk [map u8 (firstn len (zs_in st))] — every element of which
    is [u8 x = x mod 256], in range unconditionally.  So no invariant field, no
    premise, nothing to thread.

    AND THIS IS THE SAME [map u8] AS THE ONE THAT COST ME A PREMISE, WITH THE
    OPPOSITE CONSEQUENCE.  In [GtReadBufConserve] the [map u8] is what BREAKS
    byte-level conservation without a range hypothesis, because it changes values.
    Here it is what GUARANTEES the range, because it normalises them.  Third
    instance today of one mechanism cutting both ways: [mkCodeT]'s truncation makes
    writer provenance irrelevant for the SIGN while destroying strict POSITIVITY;
    [sub_dist]'s classifier excludes the unwritten default at one polarity and
    includes it at the other; and [u8] destroys conservation while establishing
    range.  **The lesson is not about any of the three: it is that "same mechanism"
    is never a reason to expect the same consequence.** *)
Lemma in_map_u8_is_byte : forall l b, In b (map u8 l) -> 0 <= b < 256.
Proof.
  intros l b Hin. apply in_map_iff in Hin as [x [<- _]].
  unfold u8. apply Z.mod_pos_bound. lia.
Qed.

Theorem read_buf_chunk_ad_wf : forall wrap size st,
  ad_wf false (fst (read_buf wrap size st)).
Proof.
  intros wrap size st. unfold ad_wf. split; [| discriminate].
  unfold read_buf. cbv zeta.
  destruct (Z.eqb (if Z.ltb size (zlen (zs_in st)) then size else zlen (zs_in st)) 0);
    cbn [fst].
  - intros b Hin. cbn [In] in Hin. exact (False_ind _ Hin).
  - intros b Hin. exact (in_map_u8_is_byte _ b Hin).
Qed.

(* ######################################################################### *)
(* 5.  [AdWf] IS PROVABLY THE RIGHT GUARD — the witness is outside its class   *)
(* ######################################################################### *)

(** ld-seams (§LD-ADLER-REFUTE) refuted filter-id's two named chunking Props at
    their stated hypothesis [0 <= init], with the witness below, and checked that it
    fails [AdWf] rather than assuming so.  They deliberately did NOT claim the
    [AdWf]-guarded form is TRUE — "that is your arithmetic" — so what is proved here
    is the half that is mine to prove: **[AdWf] EXCLUDES the witness, and excludes it
    for the right reason.**

    The witness is chosen so that a range hypothesis cannot see the defect: its LOW
    half is a perfectly legal adler ([65265 < ADLER_BASE]) and only its HIGH half is
    out of range ([65534 >= 65521]).  So [0 <= init] admits it, and [AdWf] does not —
    which is exactly what makes [AdWf] load-bearing rather than hygiene.

    The mechanism is the [len = 1] fast path ([Checksum.v:415-419]): it normalises
    with a SINGLE conditional subtraction instead of a [mod], so a high half starting
    in [BASE .. 65535] comes back [>= BASE], while the [len < 16] path takes a [mod].
    ld-seams' byte 255 is picked so [adl0 + 255 = 65520], one below [ADLER_BASE] —
    the point at which one subtraction is insufficient.  That is the same quirk this
    file's [AdWf] was written for, arriving as a refutation from another lane. *)
Definition bad_init : Z := Z.lor 65265 (Z.shiftl 65534 16).

Lemma bad_init_low_is_legal : Z.land bad_init 65535 = 65265.
Proof. unfold bad_init. apply lor_split_low; lia. Qed.

Lemma bad_init_high_is_out_of_range : Z.land (Z.shiftr bad_init 16) 65535 = 65534.
Proof. unfold bad_init. apply lor_split_high; lia. Qed.

Theorem adwf_excludes_bad_init : ~ AdWf bad_init.
Proof.
  intros [_ Hhi]. rewrite bad_init_high_is_out_of_range in Hhi.
  unfold ADLER_BASE in Hhi. lia.
Qed.

(** And the precise shape of the exclusion, which is the part a reader needs: the
    witness is a LEGAL-LOOKING adler.  A hypothesis about the value as a whole — or
    about its low half, or [0 <= init] — cannot reject it; only a two-halves
    condition can.  So the guard cannot be weakened to a range on the value. *)
Theorem bad_init_fails_only_in_the_high_half :
  (0 <= Z.land bad_init 65535 < ADLER_BASE)
  /\ ~ (Z.land (Z.shiftr bad_init 16) 65535 < ADLER_BASE)
  /\ 0 <= bad_init.
Proof.
  rewrite bad_init_low_is_legal, bad_init_high_is_out_of_range.
  unfold ADLER_BASE. repeat split; try lia.
  unfold bad_init. rewrite lor_is_add16 by lia. lia.
Qed.

(* ######################################################################### *)
(* 6.  THE OUTPUT-RANGE PREMISE symbol-id routed here — and a CORRECTION to    *)
(*     how they priced it                                                     *)
(* ######################################################################### *)

(** symbol-id (§SYMID-EU) routed a premise nobody supplies: filter-id's
    [Common/LETrailer.trailer_bytes_be32] needs [0 <= ad < 4294967296] of the adler
    VALUE, and [ad_wf] constrains only the INPUT bytes.  They asked whether the fact
    is a corollary of what my walk already carries, and said I was the only one who
    could tell.

    ** THE ANSWER IS NO, AND THE REASON MATTERS FOR THEIR PRICING.

    They guessed: "if your walk already carries 'both halves are below BASE' as an
    invariant at each return, the range fact is a corollary."  My walk does carry
    that — it is [AdWf] — **and it is not sufficient.**  [AdWf] constrains the two
    16-bit WINDOWS extracted by [Z.land]/[Z.shiftr]; it says nothing about bits at or
    above 32, which those windows cannot see.  Refuted below with [2 ^ 40], whose
    both halves are 0.

    What DOES give the range is the packed FORM — [Z.lor low (Z.shiftl high 16)] with
    both halves in [0, 65536) — which is how [adler32_z] assembles every one of its
    return values.  So the fact is available from my walk, but as a statement about
    the CONSTRUCTOR rather than about the invariant, and a walk that carried only
    [AdWf] at each return would not yield it.  **That is the difference between
    "the halves are small" and "the value is these halves".** *)
Lemma packed_lt_2_32 : forall a s,
  0 <= a < 65536 -> 0 <= s < 65536 -> 0 <= Z.lor a (Z.shiftl s 16) < 4294967296.
Proof.
  intros a s Ha Hs. rewrite (lor_is_add16 a s Ha (proj1 Hs)). lia.
Qed.

(** And with the halves below [ADLER_BASE], as [ad_mod] leaves them, there is room
    to spare — [65520 * 65536 + 65520], comfortably inside [2 ^ 32]. *)
Corollary packed_adler_lt_2_32 : forall a s,
  0 <= a < ADLER_BASE -> 0 <= s < ADLER_BASE ->
  0 <= Z.lor a (Z.shiftl s 16) < 4294967296.
Proof.
  intros a s Ha Hs. unfold ADLER_BASE in *. apply packed_lt_2_32; lia.
Qed.

(** THE REFUTATION that corrects the pricing: [AdWf] alone does not bound the value,
    because the two extracted halves are blind to bits at or above 32. *)
Theorem adwf_does_not_bound_the_value : ~ (forall a, AdWf a -> a < 4294967296).
Proof.
  intro H.
  assert (Hwf : AdWf (2 ^ 40)).
  { unfold AdWf, ADLER_BASE. split.
    - assert (E : Z.land (2 ^ 40) 65535 = 0) by reflexivity. rewrite E. lia.
    - assert (E : Z.land (Z.shiftr (2 ^ 40) 16) 65535 = 0) by reflexivity.
      rewrite E. lia. }
  pose proof (H (2 ^ 40) Hwf) as Hbad.
  assert (H32 : 4294967296 < 2 ^ 40) by (vm_compute; reflexivity).
  lia.
Qed.

(** ** THE OUTPUT RANGE IS NOT UNCONDITIONAL — REFUTED

    zlib-lead rerouted this premise to ld-seams and reported it "effectively already
    answered: the range is UNCONDITIONAL, because [adler32_z] masks both halves
    before folding", verified at three corners including [init = 2 ^ 40] and the
    malformed witness.  **The three corners vary the INIT.  The defect is in the
    INPUT.**

    Witness: [adler32_z 0 false [1000000] = 56948048463], about 13x over [2 ^ 32].
    The [len = 1] fast path ([Checksum.v:415-419]) adds the element to [adl0] and
    normalises with a SINGLE conditional subtraction rather than a [mod], so a
    non-byte element escapes both halves' bounds and the packed value escapes the
    range.  Contrast, computed at the same shape:

      adler32_z 0 false [255]           = 16711935     in range   (a real byte)
      adler32_z 0 false [1000000; 0]    = 2253275727   in range   (len<16 path MODs)
      adler32_z 0 false [1000000]       = 56948048463  OUT        (len=1 path does not)

    So the range needs [ad_wf] on the INPUT — the same guard, and the same [len = 1]
    deviation, that already refuted filter-id's two Props at [0 <= init].  **Third
    statement tonight asserted unconditionally over an object whose fast path
    normalises by subtraction instead of [mod]**; the first two were caught by
    ld-seams, this one is symmetric to theirs and was caught by varying the other
    parameter.  A three-corner check that holds [bs] fixed cannot see it. *)
Theorem output_range_is_not_unconditional :
  ~ (forall init bs, 0 <= init -> 0 <= adler32_z init false bs < 4294967296).
Proof.
  intro H.
  pose proof (H 0 [1000000] ltac:(lia)) as Hr.
  assert (Hval : adler32_z 0 false [1000000] = 56948048463)
    by (vm_compute; reflexivity).
  rewrite Hval in Hr. lia.
Qed.

(** And the guarded form is the one that survives, with the contrast pinned so the
    guard's necessity is visible at the two neighbouring shapes. *)
Example range_holds_on_bytes_and_on_the_mod_path :
  adler32_z 0 false [255] < 4294967296
  /\ adler32_z 0 false [1000000; 0] < 4294967296
  /\ ~ (adler32_z 0 false [1000000] < 4294967296).
Proof.
  repeat split; vm_compute; try reflexivity; try discriminate.
Qed.

(** ** THE GUARDED RANGE, at the path where all the risk is

    symbol-id (§SYMID-EV) settled the shape after their own independent refutation
    ([adler32_z 1 false [1000000] = 56948114000]): guarded on the BYTES, FREE in the
    init, because the masking at [Checksum.v:422-423] discards bits 16 and up of each
    half so a malformed init cannot escape.  Their target:

      forall ad bs, (forall b, In b bs -> 0 <= b < 256) ->
        0 <= adler32_z ad false bs < 4294967296

    **And their margin analysis says where to spend the effort: the whole risk is in
    the [len = 1] path**, the only one with no [mod] — the other three reduce
    [a_sum2] explicitly ([:438]) or via [ad_mod], and were never at risk.  So that
    path is proved here, with the margin they computed made explicit rather than
    asserted: [adl0 <= 65535] and a byte [< 256] give [s0 <= 131055], and
    [131055 - 65521 = 65534 < 65536].  **It survives by two.**

    A bound with a margin of two is exactly the shape to prove rather than inspect:
    three different lanes tonight asserted a property of this function by inspection
    and all three were refuted. *)
(** ONE conditional subtraction, bounded — stated at the two input bounds the
    [len = 1] path actually reaches, so each use is a single [destruct] plus [lia].

    MY FIRST VERSION NESTED the two destructs over a repeated scrutinee, and the
    measured cost is below.  [repeat (destruct (Z.leb_spec ...))] over a term that
    also appears inside the second conditional multiplies the branches, and every
    branch carries the [Z.land] atoms.  The registered fix applies exactly: bound
    each conditional ONCE, in its own lemma, and compose.

      nested destructs over a repeated scrutinee   787.50 s   47262264 KB   SIGABRT
      two single-destruct helpers, composed          5.38 s     516256 KB   rc=0

    i.e. **146x wall and 92x memory**, at loads 149 and 175 respectively.

    AND I FIRST REPORTED THIS WRONG, IN THE WAY THAT MATTERS.  I published ">900 s,
    KILLED — flat output, no error" to two lanes and the board.  It was **787.50 s
    and it was not killed**: it aborted itself with SIGNAL 6 at ~47 GB, which is an
    OUT-OF-MEMORY abort.  My own register carries the distinguishing rule — *an OOM
    GROWS; flat RSS is the tell of a conversion blowup* — and I filed a growing-RSS
    abort under the flat-RSS signature.  **The symptom is what the next person
    pattern-matches on, so misfiling it is worse than misquoting the number.**

    Two instrument notes from the correction itself.  The [.err] was genuinely empty
    (no coqc diagnostic), which is what misled me — the abort is reported by
    [/usr/bin/time] into the [.time] file, not by coqc into [.err], so a reader
    checking only [.err] sees silence and infers a hang.  And the [.time] file was
    being written by TWO builds at once (a backgrounded run plus my foreground
    retries), the registered "two builds, one output path" trap, so the first
    [.time] I read was not the run I thought I was reading. *)
Lemma one_sub_bound_narrow : forall x,
  0 <= x <= 65790 -> 0 <= (if Z.leb ADLER_BASE x then x - ADLER_BASE else x) <= 65520.
Proof. intros x Hx. unfold ADLER_BASE. destruct (Z.leb_spec 65521 x); lia. Qed.

Lemma one_sub_bound_wide : forall x,
  0 <= x <= 131055 -> 0 <= (if Z.leb ADLER_BASE x then x - ADLER_BASE else x) <= 65534.
Proof. intros x Hx. unfold ADLER_BASE. destruct (Z.leb_spec 65521 x); lia. Qed.

(** The [len = 1] path's two halves, with symbol-id's margins as the bounds:
    [a <= 65520] because one subtraction from at most [65535 + 255]; then
    [s <= 65534] because [65535 + 65520 = 131055] and [131055 - 65521 = 65534].
    **It survives by two.** *)
Lemma len1_halves_in_range : forall adler b, 0 <= b < 256 ->
  0 <= (if Z.leb ADLER_BASE (Z.land adler 65535 + b)
        then Z.land adler 65535 + b - ADLER_BASE else Z.land adler 65535 + b) <= 65520.
Proof.
  intros adler b Hb.
  assert (Hlo : 0 <= Z.land adler 65535 < 65536)
    by (rewrite land16_mod; apply Z.mod_pos_bound; lia).
  apply one_sub_bound_narrow. lia.
Qed.

Lemma len1_sum2_in_range : forall adler a,
  0 <= a <= 65520 ->
  0 <= (if Z.leb ADLER_BASE (Z.land (Z.shiftr adler 16) 65535 + a)
        then Z.land (Z.shiftr adler 16) 65535 + a - ADLER_BASE
        else Z.land (Z.shiftr adler 16) 65535 + a) <= 65534.
Proof.
  intros adler a Ha.
  assert (Hhi : 0 <= Z.land (Z.shiftr adler 16) 65535 < 65536)
    by (rewrite land16_mod; apply Z.mod_pos_bound; lia).
  apply one_sub_bound_wide. lia.
Qed.

(** So the risky path's return value is packed from two in-range halves, hence inside
    [2 ^ 32].  The other three paths reduce [a_sum2] by an explicit [mod] and were
    never at risk — which is why the effort went here. *)
Corollary len1_output_in_range : forall adler b, 0 <= b < 256 ->
  0 <= Z.lor
         (if Z.leb ADLER_BASE (Z.land adler 65535 + b)
          then Z.land adler 65535 + b - ADLER_BASE else Z.land adler 65535 + b)
         (Z.shiftl
            (if Z.leb ADLER_BASE (Z.land (Z.shiftr adler 16) 65535
                                  + (if Z.leb ADLER_BASE (Z.land adler 65535 + b)
                                     then Z.land adler 65535 + b - ADLER_BASE
                                     else Z.land adler 65535 + b))
             then Z.land (Z.shiftr adler 16) 65535
                  + (if Z.leb ADLER_BASE (Z.land adler 65535 + b)
                     then Z.land adler 65535 + b - ADLER_BASE
                     else Z.land adler 65535 + b) - ADLER_BASE
             else Z.land (Z.shiftr adler 16) 65535
                  + (if Z.leb ADLER_BASE (Z.land adler 65535 + b)
                     then Z.land adler 65535 + b - ADLER_BASE
                     else Z.land adler 65535 + b)) 16)
       < 4294967296.
Proof.
  intros adler b Hb.
  pose proof (len1_halves_in_range adler b Hb) as Ha.
  pose proof (len1_sum2_in_range adler _ Ha) as Hs.
  apply packed_lt_2_32; lia.
Qed.

(* ######################################################################### *)
(* 8.  CANONICALITY IS A SECOND PROPERTY, AND ONLY ONE PATH THREATENS IT       *)
(* ######################################################################### *)

(** CHECK-BEFORE-PRICING, AND IT MOVED THE WHOLE ITEM.  Before building the
    chunk-composition law I searched the tree for what already concludes
    something about the adler accumulation, at the OUTPUT state rather than by
    the names I had coined.  The mathematical core of §4 is already Qed'd, and
    not by me:

      - [Common/ZChecksum.adl_raw_mod] (:483) — THE DEFERRAL CONGRUENCE, the
        exact fact DeclIface §4's prose names ("ZChecksum's deferral
        congruence"): reducing once at the end of a block equals reducing after
        every byte.  This is what allows NMAX blocking.
      - [Common/ZChecksum.adl_canon] (:508) — CANONICALITY of [adl], with a
        comment that states my own conclusion before I reached it: "which is
        what lets a CHAIN of [adler32] calls satisfy the next call's
        precondition ... canonicality is a real precondition of the compiled
        code and not a modelling convenience.  (That was found the hard way:
        the first version of the walk's postcondition was FALSE at [len = 1]
        for a non-canonical input.)"
      - [Common/ZChkAdl.adl_raw_app] (:79) — the append law.
      - [Common/ZChkAdl.condsub] (:245) — the conditional subtraction as an
        EQUALITY with [mod], on [0 <= x < 2 * ABASE].

    So §4 is not "a four-path case split from scratch"; it is a BRIDGE between
    [Checksum.adler32_z] (the tree's transcription, which the interface clause
    names) and [ZChecksum.adl]/[adl_raw] (where the algebra already lives).
    Both constants agree — [ZChecksum.ABASE = 65521 = Checksum.ADLER_BASE] and
    both [NMAX = 5552] — pinned below rather than assumed.

    SUBSUMPTION, honestly reported against my own work: [condsub] is STRONGER
    than my [one_sub_bound_narrow], because an equality with [mod] yields the
    range and composes, where a range only bounds.  My [one_sub_bound_wide] is
    NOT subsumed, and the reason is the interesting one: its domain
    ([x <= 131055]) reaches ABOVE [2 * ABASE - 1 = 131041], and that is exactly
    where [condsub] is false — the conditional subtraction stops being a [mod]
    there.  That gap is not an artifact of my statement; it is the corner
    [Checksum.v:415-419] warns about, and it is where the next result lives. *)

Lemma abase_agrees_with_adler_base : ZChecksum.ABASE = ADLER_BASE.
Proof. reflexivity. Qed.

Lemma nmax_agrees : ZChecksum.NMAX = Checksum.NMAX.
Proof. reflexivity. Qed.

(** ** The two properties, and a single value that separates them

    "The output range" has been used in this fleet for two different Props, and
    they are not the same one:

      FITS-WORD    [0 <= adler32_z a isnull bs < 2 ^ 32]
                   — guarded on the BYTES, FREE in the init (symbol-id §SYMID-EV,
                     after two independent refutations of the unguarded form).
      CANONICAL    [AdWf (adler32_z a isnull bs)], both halves below BASE
                   — what the NEXT chunk's bit-16 split needs, hence what the
                     composition law consumes.

    They differ, and one value shows it: with [a = 2 ^ 32 - 16] (low half 65520,
    high half 65535 — a legal word, NOT canonical) and the single byte [0],

      adler32_z (2^32 - 16) false [0] = 4294901744

    which is BELOW [2 ^ 32] (fits-word holds) and whose high half is 65534,
    ABOVE BASE (canonical fails).  The byte is a real byte, so [ad_wf] holds:
    the separation is not reached through a malformed input, only through a
    non-canonical init.  **So fits-word cannot be strengthened to canonicality
    by adding a byte hypothesis; it needs a hypothesis on the init, and that is
    a different guard from the one already settled.**

    Which retires a phrase I had accepted: my own note above says the [len = 1]
    margin "survives by two" (65534 < 65536).  True for fits-word.  For
    canonicality the same 65534 is a FAILURE by fourteen — the margin was
    measured against the wrong ceiling, because the property was not yet
    distinguished. *)

Definition noncanon_init : Z := 4294967280.

Lemma noncanon_init_is_not_adwf : ~ AdWf noncanon_init.
Proof.
  unfold AdWf, noncanon_init, ADLER_BASE.
  intros [_ Hh].
  assert (Hv : Z.land (Z.shiftr 4294967280 16) 65535 = 65535) by reflexivity.
  rewrite Hv in Hh. lia.
Qed.

Theorem len1_does_not_restore_canonicality :
  ad_wf false [0]
  /\ 0 <= adler32_z noncanon_init false [0] < 4294967296
  /\ ~ AdWf (adler32_z noncanon_init false [0]).
Proof.
  split; [split; [intros b Hin; cbn in Hin; destruct Hin as [<-|[]]; lia
                 | discriminate]|].
  assert (Hval : adler32_z noncanon_init false [0] = 4294901744)
    by (vm_compute; reflexivity).
  rewrite Hval. split; [lia|].
  unfold AdWf, ADLER_BASE. intros [_ Hh].
  assert (Hv : Z.land (Z.shiftr 4294901744 16) 65535 = 65534) by reflexivity.
  rewrite Hv in Hh. lia.
Qed.

(** ** The state-level invariant, and the structural surprise

    Where I expected the cost to be: the [len >= 16] path, with NMAX blocking,
    [ad_inner]'s 347 iterations and a fuelled outer loop.  Where it actually is:
    NOWHERE.  **Every exit of that path passes through [ad_mod], so it needs no
    bound on anything** — not on the bytes, not on the init.  The fuelled loop
    either ran at least once (and its state is [ad_mod]-reduced) or did not run
    at all (and then its residue is the whole input list, which the [length = 0]
    test excludes).  The expensive-looking path is the free one.

    The one that costs is [len < 16], which reduces [a_sum2] by a [mod] but the
    ADLER half by a single conditional subtraction — so it needs the growth
    bound ([ad_run_bound]) to know the operand is below [2 * BASE]. *)

Definition AdWfSt (s : AdSt) : Prop :=
  0 <= a_adler s < ADLER_BASE /\ 0 <= a_sum2 s < ADLER_BASE.

Lemma ad_mod_wf : forall s, AdWfSt (ad_mod s).
Proof.
  intros s. unfold AdWfSt, ad_mod. cbn [a_adler a_sum2].
  split; apply Z.mod_pos_bound; unfold ADLER_BASE; lia.
Qed.

(** The fuelled NMAX loop leaves a state that is either untouched or reduced.
    Stated as a disjunction over the WHOLE pair, so the "untouched" case carries
    the residue and can be refuted by the caller's [length] test. *)
Lemma ad_nmax_id_or_mod : forall f s l,
  ad_nmax f s l = (s, l) \/ exists s', fst (ad_nmax f s l) = ad_mod s'.
Proof.
  induction f as [|f IH]; intros s l; cbn [ad_nmax].
  - left. reflexivity.
  - destruct (Z.leb Checksum.NMAX (Z.of_nat (length l))) eqn:E.
    + destruct (ad_inner 347%nat s l) as [s1 l1] eqn:E2.
      destruct (IH (ad_mod s1) l1) as [H|[s2 H]].
      * right. exists s1. rewrite H. reflexivity.
      * right. exists s2. exact H.
    + left. reflexivity.
Qed.

(* ######################################################################### *)
(* 9.  ONE CASE ANALYSIS, TWO CONSUMERS                                       *)
(* ######################################################################### *)

(** The conditional subtraction, NAMED.  Everything above states it inline, which
    is why those statements are unreadable and why my first proof of one of them
    cost 787 s and 47 GB: the term appears twice in the [len = 1] path and an
    inline [destruct] over a repeated scrutinee multiplies branches.  With a name
    it is one atom, each bound is one [destruct], and the composition is free. *)
Definition csub (x : Z) : Z := if Z.leb ADLER_BASE x then x - ADLER_BASE else x.

(** [csub] IS [mod ADLER_BASE] exactly on [0 <= x < 2 * ADLER_BASE], which is
    [Common/ZChkAdl.condsub] (:245) at the model's polarity.  Their form tests
    [Z.leb x 65520] because that is the branch the compiled code emits; the two
    are the same function with the arms swapped, and the bridge is Qed'd below so
    a consumer can move between the model and the walk without re-deriving it. *)
Lemma csub_is_mod : forall x, 0 <= x < 2 * ADLER_BASE -> csub x = x mod ADLER_BASE.
Proof.
  intros x Hx. unfold csub, ADLER_BASE in *.
  destruct (Z.leb_spec 65521 x) as [H|H].
  - rewrite <- (Z.mod_add x (-1) 65521) by lia. symmetry. apply Z.mod_small. lia.
  - symmetry. apply Z.mod_small. lia.
Qed.

Lemma csub_polarity : forall x, csub x = if Z.leb x 65520 then x else x - ADLER_BASE.
Proof.
  intros x. unfold csub, ADLER_BASE.
  destruct (Z.leb_spec 65521 x); destruct (Z.leb_spec x 65520); try reflexivity; lia.
Qed.

Corollary csub_range : forall x, 0 <= x < 2 * ADLER_BASE -> 0 <= csub x < ADLER_BASE.
Proof.
  intros x Hx. rewrite (csub_is_mod x Hx).
  apply Z.mod_pos_bound. unfold ADLER_BASE. lia.
Qed.

(** AND THE DOMAIN WHERE IT STOPS BEING A [mod], which is the whole content of the
    [len = 1] corner: [csub] still lands inside a 16-bit half up to 131055, but it
    lands at or above BASE from 131042 on.  That window [131042 .. 131055] is
    exactly fourteen wide, it is unreachable from a canonical init (which caps the
    sum at 131040), and it is where [noncanon_init] sits. *)
Lemma csub_fits_half : forall x, 0 <= x <= 131055 -> 0 <= csub x < 65536.
Proof.
  intros x Hx. unfold csub, ADLER_BASE. destruct (Z.leb_spec 65521 x); lia.
Qed.

(** The tight low-half bound, RE-EXPRESSED rather than re-proved: this is
    [one_sub_bound_narrow] in the [csub] vocabulary, and it cites it instead of
    repeating the [destruct]/[lia].  Keeping both forms is deliberate — symbol-id
    cites the raw one — but only one of them carries a proof. *)
Corollary csub_le_65520 : forall x, 0 <= x <= 65790 -> 0 <= csub x <= 65520.
Proof. intros x Hx. unfold csub. apply one_sub_bound_narrow. exact Hx. Qed.

Lemma csub_escapes_base_above_2base : forall x,
  2 * ADLER_BASE <= x <= 131055 -> ADLER_BASE <= csub x.
Proof.
  intros x Hx. unfold csub, ADLER_BASE in *.
  destruct (Z.leb_spec 65521 x); lia.
Qed.

Lemma adwf_one : AdWf 1.
Proof.
  unfold AdWf.
  assert (H1 : Z.land 1 65535 = 1) by reflexivity.
  assert (H2 : Z.land (Z.shiftr 1 16) 65535 = 0) by reflexivity.
  rewrite H1, H2. unfold ADLER_BASE. split; lia.
Qed.

(** The [len = 1] path as a [reflexivity] lemma — the reduction packaged rather
    than performed by a tactic, the idiom [Common/ZChkAdl] adopted for the same
    reason (neither [cbn] nor [simpl] points at the right subterm here). *)
Lemma adler32_z_len1_csub : forall a b,
  adler32_z a false [b]
  = Z.lor (csub (Z.land a 65535 + b))
          (Z.shiftl (csub (Z.land (Z.shiftr a 16) 65535 + csub (Z.land a 65535 + b))) 16).
Proof. reflexivity. Qed.

(** ** THE SHARED CASE ANALYSIS

    Off the [len = 1] path, the result is packed from two halves that are BOTH
    below BASE — with no hypothesis on the init at all.  This is the one pass over
    [adler32_z]'s structure; canonicality and fits-word are both corollaries of
    it, which is the point (publish for the furthest consumer: a case analysis
    re-done per property is the same work twice and drifts).

    Per path: [isnull] returns 1; [len < 16] mods [a_sum2] and needs the growth
    bound for the adler half; [len >= 16] passes every exit through [ad_mod] and
    so needs nothing. *)
Lemma adler32_z_packed_off_len1 : forall a isnull bs,
  ad_wf isnull bs -> Z.of_nat (length bs) <> 1 ->
  exists lo hi, adler32_z a isnull bs = Z.lor lo (Z.shiftl hi 16)
             /\ 0 <= lo < ADLER_BASE /\ 0 <= hi < ADLER_BASE.
Proof.
  intros a isnull bs [Hb Hnull] Hlen.
  assert (Hmask : 0 <= Z.land a 65535 < 65536)
    by (rewrite land16_mod; apply Z.mod_pos_bound; lia).
  unfold adler32_z. cbv zeta.
  destruct (Z.eqb (Z.of_nat (length bs)) 1) eqn:E1.
  { apply Z.eqb_eq in E1. lia. }
  destruct isnull.
  { exists 1, 0. split; [reflexivity|]. unfold ADLER_BASE. lia. }
  destruct (Z.ltb (Z.of_nat (length bs)) 16) eqn:E3.
  - (* len < 16: the adler half is one conditional subtraction, so it needs the
       growth bound; [Z.land a 65535 <= 65535] plus fifteen bytes is 69360, and
       69360 < 2 * ADLER_BASE = 131042 with room to spare. *)
    apply Z.ltb_lt in E3.
    destruct (ad_run_bound bs
                {| a_adler := Z.land a 65535 ; a_sum2 := Z.land (Z.shiftr a 16) 65535 |}
                Hb ltac:(cbn [a_adler]; lia)) as [Hge Hle].
    cbn [a_adler] in Hge, Hle.
    assert (Hlen15 : Z.of_nat (length bs) <= 15) by lia.
    match goal with
    | |- exists lo hi, Z.lor _ (Z.shiftl (?S mod _) _) = _ /\ _ =>
        exists (csub (a_adler (ad_run {| a_adler := Z.land a 65535 ;
                                         a_sum2 := Z.land (Z.shiftr a 16) 65535 |} bs))),
               (S mod ADLER_BASE)
    end.
    split; [reflexivity|]. split.
    + apply csub_range. unfold ADLER_BASE in *. lia.
    + apply Z.mod_pos_bound. unfold ADLER_BASE. lia.
  - (* len >= 16: EVERY exit is [ad_mod]-reduced, so no bound is needed.  The
       fuelled NMAX loop either ran (reduced state) or did not (residue is the
       whole input, which the [length = 0] test excludes because len >= 16). *)
    apply Z.ltb_ge in E3.
    match goal with
    | |- context[ad_nmax ?f ?s ?l] =>
        assert (Hdisj : ad_nmax f s l = (s, l)
                        \/ exists s', fst (ad_nmax f s l) = ad_mod s')
          by (apply ad_nmax_id_or_mod);
        destruct (ad_nmax f s l) as [st1 l1] eqn:E4
    end.
    destruct (Nat.eqb (length l1) 0) eqn:E5.
    + apply Nat.eqb_eq in E5.
      assert (Hwf : AdWfSt st1).
      (* NO [rewrite E4 in H]: [destruct ... eqn:E4] has ALREADY substituted the
         pattern into [Hdisj], so the hypothesis reads [(st1, l1) = (s, l)] and a
         rewrite reports "found no subterm" — an error about what the tactic
         already did, not about the fact. *)
      { destruct Hdisj as [H|[s' H]].
        - injection H as _ Hl1. subst l1. lia.
        - cbn [fst] in H. subst st1. apply ad_mod_wf. }
      exists (a_adler st1), (a_sum2 st1). split; [reflexivity|]. exact Hwf.
    + match goal with
      | |- context[ad_blk16 ?f ?s ?l] => destruct (ad_blk16 f s l) as [sa l2] eqn:E6
      end.
      exists (a_adler (ad_mod (ad_run sa l2))), (a_sum2 (ad_mod (ad_run sa l2))).
      split; [reflexivity|]. apply ad_mod_wf.
Qed.

(** THE SHARPENING that makes the composition law's guard cheap: three of the four
    paths RESTORE canonicality, with no hypothesis on the incoming adler.  So the
    invariant is owed at exactly one chunk length. *)
Theorem adler32_z_restores_adwf : forall a isnull bs,
  ad_wf isnull bs -> Z.of_nat (length bs) <> 1 -> AdWf (adler32_z a isnull bs).
Proof.
  intros a isnull bs Hwf Hlen.
  destruct (adler32_z_packed_off_len1 a isnull bs Hwf Hlen) as [lo [hi [Heq [Hlo Hhi]]]].
  rewrite Heq. apply adwf_of_halves; assumption.
Qed.

(** The [len = 1] path with the guard: a canonical init caps the sum2 operand at
    [65520 + 65520 = 131040], one short of the window where [csub] escapes BASE.
    **The guard buys exactly two.** *)
Lemma len1_adwf_guarded : forall a b,
  AdWf a -> 0 <= b < 256 -> AdWf (adler32_z a false [b]).
Proof.
  intros a b [Hlo Hhi] Hb.
  rewrite adler32_z_len1_csub.
  assert (Hu : 0 <= csub (Z.land a 65535 + b) < ADLER_BASE)
    by (apply csub_range; unfold ADLER_BASE in *; lia).
  apply adwf_of_halves; [exact Hu|].
  apply csub_range. unfold ADLER_BASE in *. lia.
Qed.

Theorem adler32_z_preserves_adwf : forall a isnull bs,
  AdWf a -> ad_wf isnull bs -> AdWf (adler32_z a isnull bs).
Proof.
  intros a isnull bs Ha Hwf.
  destruct (Z.eq_dec (Z.of_nat (length bs)) 1) as [E|E].
  - destruct Hwf as [Hb Hnull].
    assert (Hl : length bs = 1%nat) by lia.
    destruct bs as [|x [|y r]]; try (cbn in Hl; discriminate).
    destruct isnull; [specialize (Hnull eq_refl); discriminate|].
    apply len1_adwf_guarded; [exact Ha|apply Hb; left; reflexivity].
  - apply adler32_z_restores_adwf; assumption.
Qed.

(** ** symbol-id's property, generalised from one path to all four

    Their statement was proved at [len = 1] because their margin analysis put all
    the risk there.  That was right, and the generalisation costs nothing extra:
    off that path the halves are below BASE, and on it they are below 65536.
    **Free in the init entirely** — not even [0 <= a], because both halves are
    masked and [Z.land _ 65535] lands in [0, 65536) for every integer, negatives
    included. *)
Theorem adler32_z_fits_word : forall a isnull bs,
  ad_wf isnull bs -> 0 <= adler32_z a isnull bs < 4294967296.
Proof.
  intros a isnull bs Hwf.
  destruct (Z.eq_dec (Z.of_nat (length bs)) 1) as [E|E].
  - destruct Hwf as [Hb Hnull].
    assert (Hl : length bs = 1%nat) by lia.
    destruct bs as [|x [|y r]]; try (cbn in Hl; discriminate).
    destruct isnull; [specialize (Hnull eq_refl); discriminate|].
    assert (Hbx : 0 <= x < 256) by (apply Hb; left; reflexivity).
    assert (Hmask : 0 <= Z.land a 65535 < 65536)
      by (rewrite land16_mod; apply Z.mod_pos_bound; lia).
    assert (Hmaskh : 0 <= Z.land (Z.shiftr a 16) 65535 < 65536)
      by (rewrite land16_mod; apply Z.mod_pos_bound; lia).
    rewrite adler32_z_len1_csub.
    (* The low half needs the TIGHT bound [<= 65520], not merely [< 65536]: the
       high half's operand is [65535 + csub_low], and with [csub_low <= 65535]
       that is 131070, past [csub_fits_half]'s domain.  With [csub_low <= 65520]
       it is 131055 — the domain boundary EXACTLY.  This is where "survives by
       two" actually lives, and it is an equality, not a margin with slack. *)
    assert (Hu : 0 <= csub (Z.land a 65535 + x) <= 65520)
      by (apply csub_le_65520; lia).
    apply packed_lt_2_32; [lia|].
    apply csub_fits_half. lia.
  - destruct (adler32_z_packed_off_len1 a isnull bs Hwf E) as [lo [hi [Heq [Hlo Hhi]]]].
    rewrite Heq. apply packed_adler_lt_2_32; assumption.
Qed.

(* ######################################################################### *)
(* 10.  THE CLOSED FORM — and the tree's own open item, closed as stated       *)
(* ######################################################################### *)

(** [Checksum.v:512-519] names ONE open item on the adler side and describes it
    precisely: *"[adler32_z] vs [ad_run] then one [mod]. [ad_run_cong] is the
    inductive core; the remaining work is the case split over the four return
    paths and the range facts that turn the conditional subtractions into
    [mod]."*  Section 9 above is that case split and those range facts.  This
    section assembles them, so the item closes on its own terms.

    And the tree had already built more of the core than its note claims — three
    more Qed'd facts I would otherwise have proved:

      [Checksum.v:470] [ad_do16_split]  DO16 on >=16 bytes is [ad_run] on the prefix
      [Checksum.v:487] [ad_run_cong]    reducing the state before a block is sound
      [Checksum.v:500] [ad_mod_cong]    and [ad_mod] does not move anything mod BASE

    THE BLOCKING NEEDS NO INDEX ARITHMETIC, which is where I expected to spend the
    section.  I had planned [ad_inner n s l = (ad_run s (firstn (16*n) l),
    skipn (16*n) l)] and the [firstn]/[skipn]/[min] juggling that goes with it.
    Unnecessary: state the invariant as **"running the RESIDUE from the CURRENT
    state"**, and every consumption step preserves it EXACTLY while every
    reduction step preserves it mod BASE.  The consumed prefix never has to be
    named, so no length hypothesis is needed either — [ad_don] on a short list
    consumes all of it and the equation still holds. *)

Lemma ad_run_cons : forall s b r, ad_run s (b :: r) = ad_run (ad_do1 s b) r.
Proof. reflexivity. Qed.

Lemma ad_run_app : forall xs ys s, ad_run s (xs ++ ys) = ad_run (ad_run s xs) ys.
Proof. intros xs ys s. unfold ad_run. apply fold_left_app. Qed.

(** UNCONDITIONAL, and that is the point: [ad_don] either takes [n] bytes or
    exhausts the list, and in both cases what remains to run is unchanged. *)
Lemma ad_don_preserves : forall n s l,
  ad_run (fst (ad_don n s l)) (snd (ad_don n s l)) = ad_run s l.
Proof.
  induction n as [|n IH]; intros s l; cbn [ad_don].
  - reflexivity.
  - destruct l as [|b r]; [reflexivity|]. rewrite IH. reflexivity.
Qed.

Lemma ad_inner_preserves : forall n s l,
  ad_run (fst (ad_inner n s l)) (snd (ad_inner n s l)) = ad_run s l.
Proof.
  induction n as [|n IH]; intros s l; cbn [ad_inner].
  - reflexivity.
  - pose proof (ad_don_preserves 16%nat s l) as H.
    destruct (ad_do16 s l) as [s' l'] eqn:E.
    unfold ad_do16 in E. rewrite E in H. cbn [fst snd] in H.
    rewrite IH, H. reflexivity.
Qed.

Lemma ad_blk16_preserves : forall f s l,
  ad_run (fst (ad_blk16 f s l)) (snd (ad_blk16 f s l)) = ad_run s l.
Proof.
  induction f as [|f IH]; intros s l; cbn [ad_blk16].
  - reflexivity.
  - destruct (Z.leb 16 (Z.of_nat (length l))) eqn:E16; [|reflexivity].
    pose proof (ad_don_preserves 16%nat s l) as H.
    destruct (ad_do16 s l) as [s' l'] eqn:E.
    unfold ad_do16 in E. rewrite E in H. cbn [fst snd] in H.
    rewrite IH, H. reflexivity.
Qed.

Definition AdSameMod (u v : AdSt) : Prop :=
  a_adler u mod ADLER_BASE = a_adler v mod ADLER_BASE
  /\ a_sum2 u mod ADLER_BASE = a_sum2 v mod ADLER_BASE.

Lemma adsamemod_refl : forall u, AdSameMod u u.
Proof. intros u. split; reflexivity. Qed.

Lemma adsamemod_trans : forall u v w, AdSameMod u v -> AdSameMod v w -> AdSameMod u w.
Proof. intros u v w [A1 B1] [A2 B2]. split; congruence. Qed.

(** The one place a reduction happens mid-stream, discharged by the tree's own
    [ad_run_cong] and [ad_mod_cong] rather than re-derived. *)
Lemma ad_run_ad_mod_samemod : forall s l, AdSameMod (ad_run (ad_mod s) l) (ad_run s l).
Proof.
  intros s l. destruct (ad_mod_cong s) as [Ha Hs].
  destruct (ad_run_cong l (ad_mod s) s Ha Hs) as [A B]. split; assumption.
Qed.

(** The fuelled NMAX loop is sound: reduce every 5552 bytes or never, the answer
    mod BASE is the same.  No fuel side condition, no length side condition. *)
Lemma ad_nmax_samemod : forall f s l,
  AdSameMod (ad_run (fst (ad_nmax f s l)) (snd (ad_nmax f s l))) (ad_run s l).
Proof.
  induction f as [|f IH]; intros s l; cbn [ad_nmax].
  - apply adsamemod_refl.
  - destruct (Z.leb Checksum.NMAX (Z.of_nat (length l))) eqn:EN; [|apply adsamemod_refl].
    pose proof (ad_inner_preserves 347%nat s l) as H.
    destruct (ad_inner 347%nat s l) as [s' l'] eqn:E.
    cbn [fst snd] in H.
    eapply adsamemod_trans; [apply IH|].
    eapply adsamemod_trans; [apply ad_run_ad_mod_samemod|].
    rewrite H. apply adsamemod_refl.
Qed.

(** ** The closed form *)

Definition ad_state0 (a : Z) : AdSt :=
  {| a_adler := Z.land a 65535 ; a_sum2 := Z.land (Z.shiftr a 16) 65535 |}.

Definition ad_closed (a : Z) (bs : list Z) : Z :=
  Z.lor (a_adler (ad_run (ad_state0 a) bs) mod ADLER_BASE)
        (Z.shiftl (a_sum2 (ad_run (ad_state0 a) bs) mod ADLER_BASE) 16).

Lemma ad_closed_is_adwf : forall a bs, AdWf (ad_closed a bs).
Proof.
  intros a bs. unfold ad_closed.
  apply adwf_of_halves; apply Z.mod_pos_bound; unfold ADLER_BASE; lia.
Qed.

Lemma ad_run_singleton : forall s b,
  ad_run s [b] = {| a_adler := a_adler s + b ; a_sum2 := a_sum2 s + (a_adler s + b) |}.
Proof. reflexivity. Qed.

(** OFF the [len = 1] path the closed form needs NO hypothesis on the init — the
    same asymmetry as canonicality, and for the same reason.  [isnull] must be
    false: at [isnull = true] the function returns 1 rather than the accumulated
    value ([Checksum.v:80-81], the deferred NULL test), so the closed form is
    genuinely false there and the boolean is a real side condition, not an
    artifact. *)
Lemma adler32_z_closed_form_nn : forall a bs,
  ad_wf false bs -> Z.of_nat (length bs) <> 1 ->
  adler32_z a false bs = ad_closed a bs.
Proof.
  intros a bs [Hb _] Hlen.
  assert (Hmask : 0 <= Z.land a 65535 < 65536)
    by (rewrite land16_mod; apply Z.mod_pos_bound; lia).
  unfold ad_closed, ad_state0, adler32_z. cbv zeta.
  destruct (Z.eqb (Z.of_nat (length bs)) 1) eqn:E1.
  { apply Z.eqb_eq in E1. lia. }
  destruct (Z.ltb (Z.of_nat (length bs)) 16) eqn:E3.
  - (* len < 16: one conditional subtraction on the adler half, and the growth
       bound puts its operand at most 69360, well inside 2 * BASE. *)
    apply Z.ltb_lt in E3.
    destruct (ad_run_bound bs
                {| a_adler := Z.land a 65535 ; a_sum2 := Z.land (Z.shiftr a 16) 65535 |}
                Hb ltac:(cbn [a_adler]; lia)) as [Hge Hle].
    cbn [a_adler] in Hge, Hle.
    assert (Hlen15 : Z.of_nat (length bs) <= 15) by lia.
    f_equal. change (if Z.leb ADLER_BASE ?x then ?x - ADLER_BASE else ?x) with (csub x).
    apply csub_is_mod. unfold ADLER_BASE in *. lia.
  - (* len >= 16: every exit is [ad_mod]-reduced AND agrees mod BASE with the
       unblocked run, so both halves are already the closed form's. *)
    apply Z.ltb_ge in E3.
    match goal with
    | |- context[ad_nmax ?f ?s ?l] =>
        pose proof (ad_nmax_samemod f s l) as Hsm;
        assert (Hdisj : ad_nmax f s l = (s, l)
                        \/ exists s', fst (ad_nmax f s l) = ad_mod s')
          by (apply ad_nmax_id_or_mod);
        destruct (ad_nmax f s l) as [st1 l1] eqn:E4
    end.
    cbn [fst snd] in Hsm. destruct Hsm as [Hsa Hss].
    destruct (Nat.eqb (length l1) 0) eqn:E5.
    + apply Nat.eqb_eq in E5.
      assert (Hwf : AdWfSt st1).
      { destruct Hdisj as [H|[s' H]].
        - injection H as _ Hl1. subst l1. lia.
        - cbn [fst] in H. subst st1. apply ad_mod_wf. }
      destruct l1 as [|z zs]; [|cbn in E5; discriminate].
      destruct Hwf as [Hwa Hws].
      rewrite <- Hsa, <- Hss.
      (* [ad_run st1 [] = st1], and a reduced half is its own residue mod BASE *)
      cbn [ad_run fold_left].
      rewrite (Z.mod_small (a_adler st1) ADLER_BASE) by exact Hwa.
      rewrite (Z.mod_small (a_sum2 st1) ADLER_BASE) by exact Hws.
      reflexivity.
    + match goal with
      | |- context[ad_blk16 ?f ?s ?l] =>
          pose proof (ad_blk16_preserves f s l) as Hbk;
          destruct (ad_blk16 f s l) as [sa l2] eqn:E6
      end.
      cbn [fst snd] in Hbk.
      rewrite <- Hsa, <- Hss, <- Hbk.
      cbn [ad_mod a_adler a_sum2]. reflexivity.
Qed.

(** The [len = 1] path, where the guard on the init is real: the single
    conditional subtraction is [mod] only below [2 * BASE], and a canonical init
    caps the sum2 operand at 131040 — one short of the escape window. *)
Lemma adler32_z_closed_form_len1 : forall a b,
  AdWf a -> 0 <= b < 256 -> adler32_z a false [b] = ad_closed a [b].
Proof.
  intros a b [Hlo Hhi] Hb.
  unfold ad_closed, ad_state0. rewrite ad_run_singleton. cbn [a_adler a_sum2].
  rewrite adler32_z_len1_csub.
  assert (Hi : csub (Z.land a 65535 + b) = (Z.land a 65535 + b) mod ADLER_BASE)
    by (apply csub_is_mod; unfold ADLER_BASE in *; lia).
  assert (Hmod : 0 <= (Z.land a 65535 + b) mod ADLER_BASE < ADLER_BASE)
    by (apply Z.mod_pos_bound; unfold ADLER_BASE; lia).
  rewrite Hi. f_equal. f_equal.
  rewrite csub_is_mod by (unfold ADLER_BASE in *; lia).
  apply Zplus_mod_idemp_r.
Qed.

Theorem adler32_z_closed_form : forall a bs,
  AdWf a -> ad_wf false bs -> adler32_z a false bs = ad_closed a bs.
Proof.
  intros a bs Ha Hwf.
  destruct (Z.eq_dec (Z.of_nat (length bs)) 1) as [E|E].
  - destruct Hwf as [Hb Hnull].
    assert (Hl : length bs = 1%nat) by lia.
    destruct bs as [|x [|y r]]; try (cbn in Hl; discriminate).
    apply adler32_z_closed_form_len1; [exact Ha|apply Hb; left; reflexivity].
  - apply adler32_z_closed_form_nn; assumption.
Qed.

Print Assumptions ad_run_cons.
Print Assumptions ad_run_app.
Print Assumptions ad_don_preserves.
Print Assumptions ad_inner_preserves.
Print Assumptions ad_blk16_preserves.
Print Assumptions adsamemod_refl.
Print Assumptions adsamemod_trans.
Print Assumptions ad_run_ad_mod_samemod.
Print Assumptions ad_nmax_samemod.
Print Assumptions ad_closed_is_adwf.
Print Assumptions ad_run_singleton.
Print Assumptions adler32_z_closed_form_nn.
Print Assumptions adler32_z_closed_form_len1.
Print Assumptions adler32_z_closed_form.
(* ######################################################################### *)
(* 11.  THE CHUNK-COMPOSITION LAW                                             *)
(* ######################################################################### *)

(** THE HYPOTHESES ALL LIVE IN THE BRIDGE, NOT IN THE ALGEBRA.  Composition of the
    CLOSED form is unconditional — no [AdWf], no byte range, no length — because
    it is [ad_run_app] and [ad_run_cong] and nothing else.  Every hypothesis in
    the theorem below is there to relate [adler32_z] to the closed form, which is
    where the [len = 1] shortcut and the deferred NULL test live.

    That is the shape of the whole item, stated as a boundary: the ALGEBRA is
    free, the TRANSCRIPTION is what costs. *)
Lemma ad_state0_of_packed : forall lo hi,
  0 <= lo < ADLER_BASE -> 0 <= hi < ADLER_BASE ->
  ad_state0 (Z.lor lo (Z.shiftl hi 16)) = {| a_adler := lo ; a_sum2 := hi |}.
Proof.
  intros lo hi Hlo Hhi. unfold ad_state0, ADLER_BASE in *. f_equal.
  - apply lor_split_low; lia.
  - apply lor_split_high; lia.
Qed.

Lemma ad_closed_state0 : forall a bs,
  ad_state0 (ad_closed a bs)
  = {| a_adler := a_adler (ad_run (ad_state0 a) bs) mod ADLER_BASE ;
       a_sum2  := a_sum2  (ad_run (ad_state0 a) bs) mod ADLER_BASE |}.
Proof.
  intros a bs. unfold ad_closed.
  apply ad_state0_of_packed; apply Z.mod_pos_bound; unfold ADLER_BASE; lia.
Qed.

(** UNCONDITIONAL. *)
Lemma ad_closed_app : forall a xs ys,
  ad_closed (ad_closed a xs) ys = ad_closed a (xs ++ ys).
Proof.
  intros a xs ys.
  unfold ad_closed at 1. rewrite ad_closed_state0.
  unfold ad_closed. rewrite ad_run_app.
  destruct (ad_run_cong ys
              {| a_adler := a_adler (ad_run (ad_state0 a) xs) mod ADLER_BASE ;
                 a_sum2  := a_sum2  (ad_run (ad_state0 a) xs) mod ADLER_BASE |}
              (ad_run (ad_state0 a) xs)
              ltac:(cbn [a_adler]; apply Z.mod_mod; unfold ADLER_BASE; lia)
              ltac:(cbn [a_sum2]; apply Z.mod_mod; unfold ADLER_BASE; lia)) as [CA CS].
  rewrite CA, CS. reflexivity.
Qed.

Lemma ad_wf_app : forall xs ys,
  ad_wf false xs -> ad_wf false ys -> ad_wf false (xs ++ ys).
Proof.
  intros xs ys [Hx _] [Hy _]. split; [|discriminate].
  intros b Hin. apply in_app_or in Hin. destruct Hin; [apply Hx|apply Hy]; assumption.
Qed.

(** §4's law.  The encoder's incremental accumulation over read chunks equals the
    closed form over the whole payload — which is what [TrailerMatchesPayload]
    needs and what [DeclIface] §4 parks with a named residue.

    Note which hypothesis is NOT here: nothing about the chunk LENGTHS.  A chunk
    of one byte is fine, because [AdWf] is threaded through the composition by
    [ad_closed_is_adwf] rather than avoided. *)
Theorem adler32_z_chunk : forall a xs ys,
  AdWf a -> ad_wf false xs -> ad_wf false ys ->
  adler32_z (adler32_z a false xs) false ys = adler32_z a false (xs ++ ys).
Proof.
  intros a xs ys Ha Hx Hy.
  rewrite (adler32_z_closed_form a xs Ha Hx).
  rewrite (adler32_z_closed_form (ad_closed a xs) ys (ad_closed_is_adwf a xs) Hy).
  rewrite (adler32_z_closed_form a (xs ++ ys) Ha (ad_wf_app xs ys Hx Hy)).
  apply ad_closed_app.
Qed.

(** And the invariant is closed under the law, so a fold over any number of
    chunks stays inside the hypothesis the next chunk needs. *)
Corollary adler32_z_chunk_adwf : forall a xs,
  AdWf a -> ad_wf false xs -> AdWf (adler32_z a false xs).
Proof.
  intros a xs Ha Hx.
  rewrite (adler32_z_closed_form a xs Ha Hx). apply ad_closed_is_adwf.
Qed.

(* ######################################################################### *)
(* 12.  THE MULTI-CHUNK FORM — and [AdWf] alone is NOT the right invariant     *)
(* ######################################################################### *)

(** What [read_buf] actually produces is not two chunks but a LIST of them: the
    encoder applies [adler32_z] once per read, so the payload's checksum is a fold
    and the clause states one call over the concatenation.

    **Writing the fold REFUTED the invariant I had been carrying.**  With [AdWf]
    as the only hypothesis the fold is FALSE at zero chunks, and my own earlier
    refutation says exactly why: [adwf_does_not_bound_the_value] — [AdWf] reads
    two 16-bit windows and is blind to every bit at or above 32.  So an [AdWf]
    init can carry high bits that [adler32_z] discards, and the empty fold
    returns the init while the empty call returns the truncation.

    Witness, Qed'd below: [a = 2 ^ 32 + 1] has halves [(1, 0)], so [AdWf a] holds,
    yet [adler32_z a false [] = 1].  The fold returns [4294967297].

    **This is the third time today that "the halves are small" and "the value is
    these halves" have come apart, and the first time it cost a theorem rather
    than a phrasing.**  I proved that refutation as a pricing correction and then
    carried [AdWf] as the chunk invariant anyway — a refutation is only as useful
    as the next statement that respects it. *)
Fixpoint ad_chunks (a : Z) (cs : list (list Z)) : Z :=
  match cs with
  | [] => a
  | c :: r => ad_chunks (adler32_z a false c) r
  end.

Theorem adwf_is_not_enough_for_the_fold :
  ~ (forall cs a, AdWf a -> (forall c, In c cs -> ad_wf false c) ->
       ad_chunks a cs = adler32_z a false (concat cs)).
Proof.
  intro H.
  assert (Hwf : AdWf 4294967297).
  { unfold AdWf.
    assert (H1 : Z.land 4294967297 65535 = 1) by reflexivity.
    assert (H2 : Z.land (Z.shiftr 4294967297 16) 65535 = 0) by reflexivity.
    rewrite H1, H2. unfold ADLER_BASE. split; lia. }
  specialize (H [] 4294967297 Hwf ltac:(intros c Hc; cbn in Hc; destruct Hc)).
  cbn [ad_chunks concat] in H.
  assert (Hval : adler32_z 4294967297 false [] = 1) by (vm_compute; reflexivity).
  rewrite Hval in H. discriminate.
Qed.

(** THE CORRECTED INVARIANT: canonical AND a machine word.  Both conjuncts are
    needed and neither implies the other — [AdWf] misses the high bits (above),
    and [0 <= a < 2 ^ 32] misses canonicality ([noncanon_init] is a word). *)
Definition AdVal (a : Z) : Prop := AdWf a /\ 0 <= a < 4294967296.

(** And it is CLOSED under the function, which is what makes it usable as a fold
    invariant: canonicality from [adler32_z_preserves_adwf], the word bound from
    symbol-id's [adler32_z_fits_word].  Two lanes' results, one invariant. *)
Lemma adval_step : forall a bs, AdVal a -> ad_wf false bs -> AdVal (adler32_z a false bs).
Proof.
  intros a bs [Ha _] Hbs. split.
  - apply adler32_z_preserves_adwf; assumption.
  - apply adler32_z_fits_word; assumption.
Qed.

Lemma ad_closed_nil : forall a, AdVal a -> ad_closed a [] = a.
Proof.
  intros a [[Hlo Hhi] Hw]. unfold ad_closed, ad_state0.
  cbn [ad_run fold_left a_adler a_sum2].
  rewrite (Z.mod_small (Z.land a 65535) ADLER_BASE) by exact Hlo.
  rewrite (Z.mod_small (Z.land (Z.shiftr a 16) 65535) ADLER_BASE) by exact Hhi.
  rewrite land16_mod, Z.shiftr_div_pow2 by lia.
  replace (2 ^ 16) with 65536 by reflexivity.
  rewrite land16_mod.
  rewrite (Z.mod_small (a / 65536) 65536)
    by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  (* [Z_div_mod_eq_full], NOT [Z.div_mod_eq_full]: the div/mod identity lives at
     the top level in [Zdiv], not in the [Z] module.  Handed to [lia] rather than
     rewritten, because the identity's addends come in the opposite order and
     matching them costs a [Z.mul_comm] plus a [symmetry] that [lia] does not
     need. *)
  rewrite lor_is_add16 by (first [apply Z.mod_pos_bound; lia | apply Z.div_pos; lia]).
  pose proof (Z_div_mod_eq_full a 65536) as Hdm. lia.
Qed.

Lemma ad_wf_concat : forall cs,
  (forall c, In c cs -> ad_wf false c) -> ad_wf false (concat cs).
Proof.
  induction cs as [|c r IH]; intros H; cbn [concat].
  - split; [intros b Hb; cbn in Hb; destruct Hb|discriminate].
  - apply ad_wf_app; [apply H; left; reflexivity|].
    apply IH. intros d Hd. apply H; right; exact Hd.
Qed.

Theorem adler32_z_chunks : forall cs a,
  AdVal a -> (forall c, In c cs -> ad_wf false c) ->
  ad_chunks a cs = adler32_z a false (concat cs).
Proof.
  induction cs as [|c r IH]; intros a Ha Hcs; cbn [ad_chunks concat].
  - assert (Hnil : ad_wf false (@nil Z))
      by (split; [intros b Hb; cbn in Hb; destruct Hb|discriminate]).
    rewrite (adler32_z_closed_form a [] (proj1 Ha) Hnil).
    symmetry. apply ad_closed_nil. exact Ha.
  - assert (Hc : ad_wf false c) by (apply Hcs; left; reflexivity).
    assert (Hr : forall d, In d r -> ad_wf false d)
      by (intros d Hd; apply Hcs; right; exact Hd).
    rewrite (IH (adler32_z a false c) (adval_step a c Ha Hc) Hr).
    apply adler32_z_chunk; [apply Ha|exact Hc|apply ad_wf_concat; exact Hr].
Qed.

(** The clause's own starting point satisfies the invariant, so the fold applies
    to the encoder's actual run rather than to a hypothetical canonical init. *)
Lemma adval_init : AdVal (adler32_z 0 true []).
Proof.
  split; [exact adwf_init|]. rewrite adler_init_is_1. lia.
Qed.

Corollary adler32_z_chunks_from_init : forall cs,
  (forall c, In c cs -> ad_wf false c) ->
  ad_chunks (adler32_z 0 true []) cs
  = adler32_z (adler32_z 0 true []) false (concat cs).
Proof.
  intros cs Hcs. apply adler32_z_chunks; [exact adval_init|exact Hcs].
Qed.

Print Assumptions ad_state0_of_packed.
Print Assumptions ad_closed_state0.
Print Assumptions ad_closed_app.
Print Assumptions ad_wf_app.
Print Assumptions adler32_z_chunk.
Print Assumptions adler32_z_chunk_adwf.
Print Assumptions adwf_is_not_enough_for_the_fold.
Print Assumptions adval_step.
Print Assumptions ad_closed_nil.
Print Assumptions ad_wf_concat.
Print Assumptions adler32_z_chunks.
Print Assumptions adval_init.
Print Assumptions adler32_z_chunks_from_init.
Print Assumptions in_map_u8_is_byte.
Print Assumptions read_buf_chunk_ad_wf.
Print Assumptions abase_agrees_with_adler_base.
Print Assumptions nmax_agrees.
Print Assumptions noncanon_init_is_not_adwf.
Print Assumptions len1_does_not_restore_canonicality.
Print Assumptions ad_mod_wf.
Print Assumptions ad_nmax_id_or_mod.
Print Assumptions csub_is_mod.
Print Assumptions csub_polarity.
Print Assumptions csub_range.
Print Assumptions csub_fits_half.
Print Assumptions csub_le_65520.
Print Assumptions csub_escapes_base_above_2base.
Print Assumptions adwf_one.
Print Assumptions adler32_z_len1_csub.
Print Assumptions adler32_z_packed_off_len1.
Print Assumptions adler32_z_restores_adwf.
Print Assumptions len1_adwf_guarded.
Print Assumptions adler32_z_preserves_adwf.
Print Assumptions adler32_z_fits_word.
Print Assumptions one_sub_bound_narrow.
Print Assumptions one_sub_bound_wide.
Print Assumptions len1_halves_in_range.
Print Assumptions len1_sum2_in_range.
Print Assumptions len1_output_in_range.
Print Assumptions output_range_is_not_unconditional.
Print Assumptions range_holds_on_bytes_and_on_the_mod_path.
Print Assumptions packed_lt_2_32.
Print Assumptions packed_adler_lt_2_32.
Print Assumptions adwf_does_not_bound_the_value.
Print Assumptions bad_init_low_is_legal.
Print Assumptions bad_init_high_is_out_of_range.
Print Assumptions adwf_excludes_bad_init.
Print Assumptions bad_init_fails_only_in_the_high_half.
Print Assumptions land16_mod.
Print Assumptions land_disjoint_shiftl16.
Print Assumptions lor_is_add16.
Print Assumptions lor_split_low.
Print Assumptions lor_split_high.
Print Assumptions adwf_of_halves.
Print Assumptions adler_init_is_1.
Print Assumptions adwf_init.
Print Assumptions ad_run_bound.
Print Assumptions short_path_one_subtraction.
