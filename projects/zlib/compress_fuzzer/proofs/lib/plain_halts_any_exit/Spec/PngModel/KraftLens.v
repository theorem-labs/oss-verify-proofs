(** * KraftLens -- the RANGE half of ledger item 6, at the real [tree_lens],
      discharged from a hypothesis the consumer already carries.

    OWNER: kraftsum.

    THE CLAIM THIS FILE TURNS INTO A Qed.  This lane was chartered to treat
    [KraftRangeHalf] as possibly-owed and to carry the negative-length hazard
    ([tr_dl : Z -> Z] permits a negative "length") as a second direction needing
    its own proof.  Reading the CONSUMER settles both.  [LdDynV.v]'s theorem
    already takes, for the same tree and before item 6 is ever reached
    ([LdDynV.v:116-118]):

        (forall i, 0 <= t_len (ts_trees s TK_L) i)
        (forall i, 0 <= i <= lcodes - 1 -> 0 <= t_len (ts_trees s TK_L) i <= 15)

    and [SendGo.tree_lens t maxc] reads [t_len t] at exactly [0 .. maxc]
    ([SendGo.v:182-183]).  So the range half is not an obligation on anybody's
    build_tree work -- it is a projection of a hypothesis in scope.

    WHAT IS NOT CLAIMED.  This says nothing about who discharges the
    [0 <= t_len ... <= 15] hypothesis itself; that is ledger item 4
    (scan_tree/gen_bitlen), and huffman-id's [GbRange.gen_bitlen_ub] /
    [BuildChain.build_chain] are the work that closes it.  The point here is
    only that item 6 does not owe it a SECOND time.

    THE NEGATIVE-LENGTH HAZARD, resolved rather than carried.  [Z.to_nat]
    truncates, so a negative length would silently become 0 and CONTRIBUTE
    NOTHING to the Kraft sum ([kraft_term _ 0 = 0]) -- the hazard direction that
    matters for Kraft is therefore the UPPER bound, and the lower bound is not
    needed for the range half at all.  [tree_lens_range] below takes only the
    upper half of the consumer's conjunction, which is why it does not mention
    non-negativity.  Stated as the weaker hypothesis on purpose: an unnecessary
    hypothesis is a premise the consumer must supply. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff Trees DeflateSpec.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  HuffGenCodes HuffMaxBits ClStream SendItems SendGo.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Kraft15 KraftTree.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** ** 1. Membership in [tree_lens] names its index

    Everything else is a corollary of this. Kept separate because it is the only
    step that touches [map]/[seq] and the arithmetic of [Z.of_nat]/[Z.to_nat]. *)
Lemma in_tree_lens_inv : forall t maxc len,
  In len (SendGo.tree_lens t maxc) ->
  exists i, 0 <= i <= maxc /\ len = Z.to_nat (t_len t i).
Proof.
  intros t maxc len Hin. unfold SendGo.tree_lens in Hin.
  apply in_map_iff in Hin as [n [Heq Hn]].
  apply in_seq in Hn as [_ Hn]. cbn in Hn.
  exists (Z.of_nat n). split; [|now symmetry].
  (* [n < Z.to_nat (maxc + 1)] gives [Z.of_nat n <= maxc]. A negative [maxc]
     needs no case split: [zify] knows [Z.to_nat] is 0 there, so [Hn] is
     already absurd and [lia] closes both situations at once. *)
  lia.
Qed.

(** ** 2. The range half, at the consumer's shape *)
Theorem tree_lens_range : forall t maxc,
  (forall i, 0 <= i <= maxc -> t_len t i <= 15) ->
  forall len, In len (SendGo.tree_lens t maxc) -> (len <= 15)%nat.
Proof.
  intros t maxc Hub len Hin.
  apply (in_tree_lens_inv t maxc len) in Hin as [i [Hi ->]].
  specialize (Hub i Hi). lia.
Qed.

(** [KraftOwed.KraftRangeHalf]'s exact spelling, so nobody has to see that these
    are the same statement -- they are the same statement. *)
Corollary tree_lens_range_half : forall t maxc,
  (forall i, 0 <= i <= maxc -> t_len t i <= 15) ->
  forall len, In len (SendGo.tree_lens t maxc) -> (len <= 15)%nat.
Proof. exact tree_lens_range. Qed.

(** ** 3. The composition: item 6 reduces to the histogram bound ALONE

    This is the statement to hand the lanes owning [build_tree] and [gb_adjust].
    Both hypotheses are things that side already has or is already proving; the
    conclusion is item 6 verbatim. *)
Theorem tree_lens_valid_from_histogram : forall t maxc,
  (forall i, 0 <= i <= maxc -> t_len t i <= 15) ->
  (list_sum (map (fun j => bl_count (SendGo.tree_lens t maxc) j * 2 ^ (15 - j))
                 (seq 1 15)) <= 2 ^ 15)%nat ->
  ValidLengths (SendGo.tree_lens t maxc) 15%nat.
Proof.
  intros t maxc Hub Hsum.
  apply (kraft_from_histogram (SendGo.tree_lens t maxc) 15).
  - exact (tree_lens_range t maxc Hub).
  - exact Hsum.
Qed.

(** ** 3b. The SMALLEST form of item 6, via [Kraft15.valid_lengths_iff_nc]

    Two terms instead of fifteen.  [nc] is RFC 1951's [next_code] recurrence, and
    [HuffGenCodes.gc_next_nc] already proves zlib's [gc_next] computes it from the
    [bl_count] array -- so this is the obligation stated in a vocabulary the
    operational side of [trees.c] already speaks.

    **This is the version I recommend the [build_tree] side aim at**: it says
    "the next_code value after the last level, plus the count at that level, fits
    in fifteen bits", which is zlib's own no-code-overflow invariant rather than a
    reformulation chosen for this proof's convenience. *)
Theorem tree_lens_valid_from_nc : forall t maxc,
  (forall i, 0 <= i <= maxc -> t_len t i <= 15) ->
  (nc (SendGo.tree_lens t maxc) 15
   + bl_count (SendGo.tree_lens t maxc) 15 <= 2 ^ 15)%nat ->
  ValidLengths (SendGo.tree_lens t maxc) 15%nat.
Proof.
  intros t maxc Hub Hnc.
  apply (valid_lengths_of_nc (SendGo.tree_lens t maxc) 15).
  - exact (tree_lens_range t maxc Hub).
  - exact Hnc.
Qed.

(** ...and the converse, so a lane holding item 6 can PROJECT the [nc] bound out
    of it rather than reproving it.  Stated because a one-directional bridge is a
    defect this fleet keeps finding: [Huff.nc_count_bound] had exactly this fact
    forward-only. *)
Theorem tree_lens_nc_of_valid : forall t maxc,
  (forall i, 0 <= i <= maxc -> t_len t i <= 15) ->
  ValidLengths (SendGo.tree_lens t maxc) 15%nat ->
  (nc (SendGo.tree_lens t maxc) 15
   + bl_count (SendGo.tree_lens t maxc) 15 <= 2 ^ 15)%nat.
Proof.
  intros t maxc Hub HV.
  apply (valid_lengths_iff_nc (SendGo.tree_lens t maxc) 15
           (tree_lens_range t maxc Hub)).
  exact HV.
Qed.

(** ** 4. And in the [BlcOf] currency, which is what zlib actually maintains

    [HuffGenCodes.BlcOf blc L] is [forall b, 0 <= b <= MAX_BITS ->
    blc b = Z.of_nat (bl_count L (Z.to_nat b))] -- i.e. exactly "the [zarr]
    [blc] IS the histogram of [L]".  [gen_bitlen] maintains such an array in
    [ts_blcount] ([Trees.v:392-441]), so restating the obligation over the
    [zarr] removes the list from the hard half entirely: what is left is an
    inequality about FIFTEEN [Z] VALUES.

    A NOTE ON CURRENCY, for whoever proves the bound.  huffman-id's [nc_le_Z]
    records that the [nat] route "needs [2^15] as a [nat] literal, whose unary
    expansion made one [cbn] cost nine seconds; [Z] is binary and the same step
    is free".  The [2 ^ (15 - j)] factors below are what that warning is about,
    so the INTERNAL arithmetic of the hard half wants to be in [Z]; the
    obligation is stated in [nat] here only because [bl_count] and [kraft_sum]
    are, and the crossing costs one [Nat2Z.id] per level.  (That same comment is
    also the third independent measurement contradicting this lane's charter:
    huffman-id measured the nat route as SLOW, not impossible.) *)
Definition NatHistBound (blc : zarr) : Prop :=
  (list_sum (map (fun j => Z.to_nat (blc (Z.of_nat j)) * 2 ^ (15 - j))
                 (seq 1 15)) <= 2 ^ 15)%nat.

Theorem tree_lens_valid_from_zarr : forall t maxc blc,
  (forall i, 0 <= i <= maxc -> t_len t i <= 15) ->
  HuffGenCodes.BlcOf blc (SendGo.tree_lens t maxc) ->
  NatHistBound blc ->
  ValidLengths (SendGo.tree_lens t maxc) 15%nat.
Proof.
  intros t maxc blc Hub Hblc Hz. unfold NatHistBound in Hz.
  apply (tree_lens_valid_from_histogram t maxc Hub).
  (* The two summands agree LEVEL BY LEVEL, so the lists are equal and no
     inequality reasoning is needed -- [BlcOf] is an equality, and spending it
     pointwise via [map_ext_in] keeps [2 ^ (15 - j)] untouched. *)
  (* [%nat] on both lambda bodies: this file is in [Z_scope], so an unannotated
     [*] / [^] / [-] here would build a Z term and the map would not typecheck
     against [Hz]. *)
  assert (Heq :
    map (fun j => (Z.to_nat (blc (Z.of_nat j)) * 2 ^ (15 - j))%nat) (seq 1 15)
    = map (fun j => (bl_count (SendGo.tree_lens t maxc) j * 2 ^ (15 - j))%nat)
          (seq 1 15)).
  { apply map_ext_in. intros j Hj. apply in_seq in Hj.
    assert (Hb : 0 <= Z.of_nat j <= MAX_BITS) by (unfold MAX_BITS; lia).
    rewrite (Hblc (Z.of_nat j) Hb), !Nat2Z.id. reflexivity. }
  rewrite <- Heq. exact Hz.
Qed.

(** ** 5. ITEM 6'S SUM HALF AS ONE NAMED OBLIGATION ABOUT THE TREE

    [KraftTree.v] reduces the sum half to two counting recurrences on per-depth
    internal-node and leaf counts.  Bundled here as a single Prop about the tree,
    so the obligation has ONE name and mentions no arithmetic at all:

      "there is an internal-node count per depth that completes the binary-tree
       recurrence against this tree's own length histogram"

    The existential is the right strength and not a dodge: it is exactly
    Kraft-completeness, and [KraftTree.over_full_has_no_binary_levels] proves an
    over-full histogram admits NO such sequence, so the predicate discriminates
    rather than being satisfiable by anything.  [KraftTree]'s two witnesses show it
    is satisfiable at real [build_tree] outputs on both sides of the [ov] split. *)
Definition DadBinaryShape (t : Tree) (maxc : Z) : Prop :=
  exists I : nat -> nat,
    KraftTree.BinaryLevels I (fun b => bl_count (SendGo.tree_lens t maxc) b).

(** So the whole of item 6 is: the range hypothesis the consumer already carries,
    plus this one shape fact about the dad relation. *)
Theorem tree_lens_valid_from_dad_shape : forall t maxc,
  (forall i, 0 <= i <= maxc -> t_len t i <= 15) ->
  DadBinaryShape t maxc ->
  ValidLengths (SendGo.tree_lens t maxc) 15%nat.
Proof.
  intros t maxc Hub [I HBL].
  apply (KraftTree.valid_lengths_of_binary_levels
           I (fun b => bl_count (SendGo.tree_lens t maxc) b)
           (SendGo.tree_lens t maxc) 15 HBL).
  - intros b _ _. reflexivity.
  - exact (tree_lens_range t maxc Hub).
Qed.

(** ** 6. AT THE TWO CALL SITES, in the consumer's own hypothesis forms

    ld-seams pasted `LdDynV.v:100 dynamic_header_on_the_wire`'s hypothesis list
    from their WORKING copy with binder names.  Item 6 is the pair [HVL]/[HVD] at
    the end; what my range half consumes is the [(* 4 *)] group.  These two
    theorems take the hypotheses in EXACTLY the form that theorem states them --
    note [HL15] is TWO-SIDED ([0 <= t_len ... i <= 15]) while
    [tree_lens_range] needs only the upper half, so the projection happens here
    rather than being pushed back on the consumer.

    [HLmc] ([0 <= lcodes - 1 <= 285]) is taken and unused: it is in the consumer's
    list, so taking it costs them nothing and makes the correspondence to their
    binder list checkable by eye.  Flagged rather than silently dropped because an
    unnecessary hypothesis is normally a defect -- here it buys legibility against
    a named call site, which is the one case where it pays. *)
Definition DadBinaryShapeExact (t : Tree) (maxc : Z) : Prop :=
  exists I : nat -> nat,
    KraftTree.BinaryLevelsExact I (fun b => bl_count (SendGo.tree_lens t maxc) b) 15.

Theorem item6_at_L_site : forall (s : TSt) (lcodes : Z),
  (forall i, 0 <= i <= lcodes - 1 -> 0 <= t_len (ts_trees s TK_L) i <= 15) ->
  DadBinaryShape (ts_trees s TK_L) (lcodes - 1) ->
  ValidLengths (SendGo.tree_lens (ts_trees s TK_L) (lcodes - 1)) 15%nat.
Proof.
  intros s lcodes HL15 Hshape.
  apply tree_lens_valid_from_dad_shape; [|exact Hshape].
  intros i Hi. specialize (HL15 i Hi). lia.
Qed.

Theorem item6_at_D_site : forall (s : TSt) (dcodes : Z),
  (forall i, 0 <= i <= dcodes - 1 -> 0 <= t_len (ts_trees s TK_D) i <= 15) ->
  DadBinaryShape (ts_trees s TK_D) (dcodes - 1) ->
  ValidLengths (SendGo.tree_lens (ts_trees s TK_D) (dcodes - 1)) 15%nat.
Proof.
  intros s dcodes HD15 Hshape.
  apply tree_lens_valid_from_dad_shape; [|exact Hshape].
  intros i Hi. specialize (HD15 i Hi). lia.
Qed.

(** And the EXACT form, which is what the measured runs satisfy: the Kraft sum is
    [2 ^ 15] on the nose, not merely under it.  Both conclusions at once, so a
    consumer that wants item 6 and a consumer that wants the tightness get the
    same theorem. *)
Theorem item6_at_L_site_exact : forall (s : TSt) (lcodes : Z),
  (forall i, 0 <= i <= lcodes - 1 -> 0 <= t_len (ts_trees s TK_L) i <= 15) ->
  DadBinaryShapeExact (ts_trees s TK_L) (lcodes - 1) ->
  kraft_sum (SendGo.tree_lens (ts_trees s TK_L) (lcodes - 1)) 15 = (2 ^ 15)%nat
  /\ ValidLengths (SendGo.tree_lens (ts_trees s TK_L) (lcodes - 1)) 15%nat.
Proof.
  intros s lcodes HL15 [I HBLE].
  assert (Hub : forall len,
            In len (SendGo.tree_lens (ts_trees s TK_L) (lcodes - 1)) ->
            (len <= 15)%nat).
  { apply tree_lens_range. intros i Hi. specialize (HL15 i Hi). lia. }
  assert (Hks : kraft_sum (SendGo.tree_lens (ts_trees s TK_L) (lcodes - 1)) 15
                = (2 ^ 15)%nat).
  { apply (KraftTree.kraft_sum_equality_of_binary_levels
             I (fun b => bl_count (SendGo.tree_lens (ts_trees s TK_L)
                                     (lcodes - 1)) b)
             _ 15 HBLE);
      [ intros b _ _; reflexivity
      | apply bl_count_0
      | exact Hub ]. }
  split; [exact Hks|].
  unfold ValidLengths. split; [exact Hub|]. rewrite Hks. lia.
Qed.

Print Assumptions in_tree_lens_inv.
Print Assumptions tree_lens_range.
Print Assumptions tree_lens_valid_from_histogram.
Print Assumptions tree_lens_valid_from_nc.
Print Assumptions tree_lens_nc_of_valid.
Print Assumptions tree_lens_valid_from_dad_shape.
Print Assumptions item6_at_L_site.
Print Assumptions item6_at_D_site.
Print Assumptions item6_at_L_site_exact.
Print Assumptions tree_lens_valid_from_zarr.

(** ** UNUSED PREMISE DROPPED 2026-08-19 -- and the freeze it was protected by had no
       beneficiary.

    [item6_at_L_site] and [item6_at_D_site] carried [0 <= codes - 1 <= 285] and neither used
    it (the [_] in their [intros]).  Found by filter-id's premise-carrying census -- their
    filter flagged the results and reading the [intros] line showed the discarded hypothesis
    was this rather than the shape premise their tag named.

    **Why it was safe to drop, measured rather than assumed.** I had believed ld-seams cited
    this file by digest and held it frozen on that basis.  **They corrected me: [KraftLens]
    appears NOWHERE in their lane** -- they consume [Kraft], [KraftExports] and [KraftFold].
    Census over every farm and the graded tree, with a positive control so a zero means
    something ([KraftExports] found in 1 farm, [KraftFold] in 3, [Kraft15] in 1):

      consumers of [KraftLens] / [item6_at_*_site] outside this farm:  NONE
      the only outside hits are filter-id's census TSVs -- instruments, not consumers

    **So the freeze was a constraint with no beneficiary**, which is ld-seams' point and the
    reason the drop costs nothing: no citation breaks, and the statements are now strictly
    weaker, hence strictly more usable if a consumer ever appears.

    **The range bound was inherited by copy from the emitter's call-site convention.**
    ld-seams confirmed the mechanism from the other side: the pair
    [0 <= lcodes - 1 <= 285] / [0 <= dcodes - 1 <= 285] is LIVE in their dynamic theorems
    (the emitter genuinely needs the field ranges) and got carried into statements that
    needed only the 15-bound and the shape premise.  **A premise that arrives as a PAIR is
    the one nobody splits.** *)
