(** * Kraft15 -- the owed Kraft SUM, converted from a statement about a list
      into a statement about a length HISTOGRAM.

    OWNER: kraftsum.  Ledger item 6 of [LdDynV.v] is
    [ValidLengths (tree_lens t maxc) 15], and its only genuinely open conjunct is
    the sum: [kraft_sum (tree_lens t maxc) 15 <= 2 ^ 15].

    WHY THIS FILE EXISTS.  The owed inequality quantifies over a LIST, but every
    fact zlib itself maintains about code lengths is a fact about the length
    HISTOGRAM -- [s->bl_count[]], which [gb_pass1] accumulates and [gb_adjust]
    repairs ([Trees.v:392-441]).  The two views are connected by
    [Huff.kraft_sum_from_step_bl], which peels one level at a time.  Iterating
    that peel to the top converts the owed Prop into a FINITE sum of
    [maxBits] histogram terms, with no reference to [build_tree] at all.  So the
    conversion is separable from the hard heap/[gb_adjust] mathematics, and it is
    what tells the lanes owning those what shape their result has to take.

    THE CONSUMER'S OBLIGATION, named rather than described.  After
    [kraft_from_histogram] below, whoever discharges item 6 owes exactly:

        list_sum (map (fun j => bl_count L j * 2 ^ (maxBits - j)) (seq 1 maxBits))
          <= 2 ^ maxBits

    i.e. "sum over levels of (symbols at that level) * 2^(maxBits - level)".  Not
    a property of a list, and not a property of a tree: a property of a
    fifteen-entry integer vector.

    GENERIC IN [maxBits] ON PURPOSE, and it is not decoration.  Item 6 wants
    [maxBits = 15]; ledger item 2 of the same theorem wants
    [ValidLengths cl 7] for the code-length tree ([LdDynV.v:18], [sd_max_length
    TK_BL = 7]).  One lemma, both obligations, no restatement.

    ON COMPUTATION, because the record needs correcting.  This lane was chartered
    with the claim that [ValidLengths L 15] is not dischargeable by computation
    for ANY vector -- that [2^15] in unary nat overflows the stack regardless of
    the vector.  That is false, and the controls at the bottom of this file are
    the refutation: a 286-entry vector with mixed depths 1..15 summing exactly to
    [2 ^ 15] is decided by [vm_compute] in well under a second.  What actually
    overflows is a nat TERM-EQUALITY against a decimal literal
    ([(2^15 = 32768)%nat] by [reflexivity]); coqc's own [abstract-large-number]
    warning on that line says large nat literals are read through
    [Init.Nat.of_num_uint] precisely to avoid it.  Computation cannot discharge
    item 6 because the consumer's vector is SYMBOLIC
    ([tree_lens (ts_trees s TK_L) (lcodes - 1)], [s] and [lcodes] universally
    quantified at [LdDynV.v:127]) -- not because the arithmetic is out of reach.
    The distinction matters operationally: it is what lets this file carry a real
    positive control and a matched negative one. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope nat_scope.

(** ** 1. The tail above [maxBits] vanishes

    [kraft_at maxBits b len] is 0 for [len < b], so once the peel passes
    [maxBits] there is nothing left -- PROVIDED no length exceeds [maxBits].
    This is where the range half earns its keep: it is not merely the other
    conjunct of [ValidLengths], it is a HYPOTHESIS of the sum half's proof.
    Without it the tail is nonzero, and by an easy-to-miss route -- [nat]
    subtraction truncates, so a length above [maxBits] contributes
    [2 ^ (maxBits - len) = 2 ^ 0 = 1] rather than a fraction. *)
(** Two one-line shape lemmas.  They exist because [list_sum] is
    [fold_right Init.Nat.add 0], so [list_sum (x :: l)] does NOT contain
    [list_sum l] as a subterm and an induction hypothesis about the tail will not
    [rewrite] into it.  That cost a build; recording it as named lemmas rather
    than as a [cbn] delta list keeps the peel below readable. *)
Lemma list_sum_nil : list_sum (@nil nat) = 0.
Proof. reflexivity. Qed.

Lemma list_sum_cons : forall x l, list_sum (x :: l) = x + list_sum l.
Proof. reflexivity. Qed.

Lemma kraft_tail_vanishes : forall L maxBits,
  (forall len, In len L -> len <= maxBits) ->
  kraft_sum_from L maxBits (S maxBits) = 0.
Proof.
  intros L maxBits Hub.
  induction L as [|len l IH].
  - apply kraft_sum_from_nil.
  - rewrite kraft_sum_from_cons.
    rewrite (kraft_at_lt maxBits (S maxBits) len)
      by (specialize (Hub len (or_introl eq_refl)); lia).
    rewrite IH by (intros x Hx; apply Hub; now right).
    reflexivity.
Qed.

(** ** 2. The peel, iterated

    [Huff.kraft_sum_from_step_bl] takes one level off.  This takes them all off,
    in the shape [seq] produces, so the result is an ordinary [list_sum] over
    levels rather than a [maxBits]-fold nest.  The induction is on the NUMBER OF
    LEVELS REMAINING with [b] free, not on [b] -- the peel moves [b] upward and
    an induction on [b] would be recursing the wrong way. *)
Lemma kraft_sum_from_hist : forall n L maxBits b,
  b + n = S maxBits ->
  (forall len, In len L -> len <= maxBits) ->
  kraft_sum_from L maxBits b
  = list_sum (map (fun j => bl_count L j * 2 ^ (maxBits - j)) (seq b n)).
Proof.
  induction n as [|n IH]; intros L maxBits b Hbn Hub.
  - (* no levels left: b = S maxBits, and the tail is 0 *)
    replace b with (S maxBits) by lia.
    cbn [seq map]. rewrite list_sum_nil.
    exact (kraft_tail_vanishes L maxBits Hub).
  - rewrite (kraft_sum_from_step_bl maxBits b L).
    cbn [seq map]. rewrite list_sum_cons.
    rewrite (IH L maxBits (S b)) by (lia || exact Hub).
    reflexivity.
Qed.

(** The whole sum, from level 0.  [bl_count L 0 = 0] ([Huff.bl_count_0]) is what
    makes the [b = 0] term drop, so the useful range is [1 .. maxBits]. *)
Lemma kraft_sum_hist : forall L maxBits,
  (forall len, In len L -> len <= maxBits) ->
  kraft_sum L maxBits
  = list_sum (map (fun j => bl_count L j * 2 ^ (maxBits - j)) (seq 1 maxBits)).
Proof.
  intros L maxBits Hub. unfold kraft_sum.
  rewrite (kraft_sum_from_hist (S maxBits) L maxBits 0) by (lia || exact Hub).
  cbn [seq map]. rewrite list_sum_cons.
  rewrite (bl_count_0 L). lia.
Qed.

(** ** 3. The interface

    This is the statement the lanes owning [build_tree] and [gb_adjust] should
    aim at.  Both hypotheses are things they already have or can get: the first
    is the range half (free at [LdDynV.v]'s call site -- lines 116-118 already
    take [0 <= t_len (ts_trees s TK_L) i <= 15] over exactly the index range
    [tree_lens] reads), the second is Kraft stated on the histogram. *)
Theorem kraft_from_histogram : forall L maxBits,
  (forall len, In len L -> len <= maxBits) ->
  list_sum (map (fun j => bl_count L j * 2 ^ (maxBits - j)) (seq 1 maxBits))
    <= 2 ^ maxBits ->
  ValidLengths L maxBits.
Proof.
  intros L maxBits Hub Hsum. unfold ValidLengths. split; [exact Hub|].
  rewrite (kraft_sum_hist L maxBits Hub). exact Hsum.
Qed.

(** And the converse direction, so the histogram form is an EQUIVALENT
    reformulation rather than merely a sufficient one.  Stated because a
    one-directional bridge is the defect this fleet keeps finding: a lane holding
    [ValidLengths] and needing the histogram bound would otherwise be stuck. *)
Theorem kraft_to_histogram : forall L maxBits,
  ValidLengths L maxBits ->
  list_sum (map (fun j => bl_count L j * 2 ^ (maxBits - j)) (seq 1 maxBits))
    <= 2 ^ maxBits.
Proof.
  intros L maxBits [Hub Hsum].
  rewrite <- (kraft_sum_hist L maxBits Hub). exact Hsum.
Qed.

(** ** 3b. THE SHARPER INTERFACE: the Kraft sum IS [nc] plus the top level

    Found by reading [Huff.nc_kraft_conservation] rather than by proving anything,
    and it is strictly better than the fifteen-term histogram sum above.
    Instantiating conservation at [b = maxBits] and killing the tail with
    [kraft_tail_vanishes] collapses the whole sum to TWO terms:

        kraft_sum L maxBits = nc L maxBits + bl_count L maxBits

    [nc] is RFC 1951's [next_code] recurrence, which is exactly what zlib's
    [gc_next] computes from the [bl_count] array -- and huffman-id's
    [HuffGenCodes.gc_next_nc] already ties the two together
    ([nc_arr blc b = Z.of_nat (nc L (Z.to_nat b))]).  So the owed inequality is
    not a fifteen-term sum at all; it is **"the next_code value after the last
    level, plus the count at that level, fits in maxBits bits"** -- one arithmetic
    fact about a recurrence the operational side already computes.

    WHY THIS MATTERS FOR PRICING.  [Huff.nc_count_bound] already proves
    [ValidLengths L maxBits -> nc L b + bl_count L b <= 2 ^ b] for [b <= maxBits].
    That is the forward direction.  What was missing was the CONVERSE at
    [b = maxBits], which is what a producer needs -- the library had the fact
    one-directionally, which is a defect this fleet has hit before.  With
    [valid_lengths_iff_nc] below it is an equivalence, and either side can be
    the one that is proved. *)
Theorem kraft_sum_is_nc : forall L maxBits,
  (forall len, In len L -> len <= maxBits) ->
  kraft_sum L maxBits = nc L maxBits + bl_count L maxBits.
Proof.
  intros L maxBits Hub.
  pose proof (nc_kraft_conservation L maxBits maxBits (Nat.le_refl maxBits)) as Hc.
  rewrite (kraft_sum_from_step_bl maxBits maxBits L) in Hc.
  rewrite (kraft_tail_vanishes L maxBits Hub) in Hc.
  replace (maxBits - maxBits) with 0 in Hc by lia.
  cbn [Nat.pow] in Hc. unfold kraft_sum. lia.
Qed.

(** The obligation, at its smallest.  Both directions, so a lane holding either
    form can move to the other. *)
Theorem valid_lengths_iff_nc : forall L maxBits,
  (forall len, In len L -> len <= maxBits) ->
  (ValidLengths L maxBits <-> nc L maxBits + bl_count L maxBits <= 2 ^ maxBits).
Proof.
  intros L maxBits Hub. unfold ValidLengths. split.
  - intros [_ Hk]. rewrite <- (kraft_sum_is_nc L maxBits Hub). exact Hk.
  - intro Hnc. split; [exact Hub|].
    rewrite (kraft_sum_is_nc L maxBits Hub). exact Hnc.
Qed.

(** The producer's direction on its own, which is the one that was missing:
    [Huff.nc_count_bound] gives [ValidLengths -> nc bound], never the reverse. *)
Corollary valid_lengths_of_nc : forall L maxBits,
  (forall len, In len L -> len <= maxBits) ->
  nc L maxBits + bl_count L maxBits <= 2 ^ maxBits ->
  ValidLengths L maxBits.
Proof.
  intros L maxBits Hub Hnc.
  apply (valid_lengths_iff_nc L maxBits Hub). exact Hnc.
Qed.

(** ** 3c. FROM THE TOP-LEVEL BOUND TO A PER-LEVEL OBLIGATION

    [valid_lengths_of_nc] asks for [nc L maxBits + bl_count L maxBits <= 2 ^
    maxBits] -- one inequality at the TOP level.  A proof that walks levels (which
    is the shape [gb_pass1] and [gb_pass2] have: both iterate over [bits]) cannot
    produce that directly; it produces one fact per level.  This section converts
    between the two, so the producer's obligation matches the producer's control
    flow.

    THE PER-LEVEL CONTENT, spelled out because it is the combinatorial heart of a
    prefix code and it is not obvious from the [nc] recurrence.  Since
    [nc L (S b) = 2 * (nc L b + bl_count L b)] ([Huff.nc_succ]), the step
    obligation

        nc L (S b) + bl_count L (S b) <= 2 ^ (S b)

    is equivalent to

        bl_count L (S b) <= 2 * (2 ^ b - (nc L b + bl_count L b))

    -- "the number of codes at level [b+1] fits in twice the slots left over at
    level [b]".  [nc_level_step] below is that restatement, and it is the form a
    counting argument over the heap would actually establish. *)
Theorem nc_bound_by_levels : forall L maxBits,
  (forall b, b < maxBits ->
     nc L b + bl_count L b <= 2 ^ b ->
     nc L (S b) + bl_count L (S b) <= 2 ^ (S b)) ->
  nc L maxBits + bl_count L maxBits <= 2 ^ maxBits.
Proof.
  intros L maxBits Hstep.
  induction maxBits as [|m IH].
  - (* the base is FREE: nc L 0 = 0, bl_count L 0 = 0, and 2 ^ 0 = 1 *)
    rewrite nc_0, bl_count_0. cbn [Nat.pow]. lia.
  - apply (Hstep m (Nat.lt_succ_diag_r m)).
    apply IH. intros b Hb Hprev. apply Hstep; [lia|exact Hprev].
Qed.

(** The step obligation in slot-counting form. *)
Lemma nc_level_step : forall L b,
  nc L b + bl_count L b <= 2 ^ b ->
  bl_count L (S b) <= 2 * (2 ^ b - (nc L b + bl_count L b)) ->
  nc L (S b) + bl_count L (S b) <= 2 ^ (S b).
Proof.
  intros L b Hprev Hfit.
  rewrite nc_succ. cbn [Nat.pow]. lia.
Qed.

(** The interface a level-walking producer should aim at: establish the fit at
    each level, and item 6 follows.  Both hypotheses are per-level and neither
    mentions [kraft_sum]. *)
Theorem valid_lengths_by_levels : forall L maxBits,
  (forall len, In len L -> len <= maxBits) ->
  (forall b, b < maxBits ->
     nc L b + bl_count L b <= 2 ^ b ->
     bl_count L (S b) <= 2 * (2 ^ b - (nc L b + bl_count L b))) ->
  ValidLengths L maxBits.
Proof.
  intros L maxBits Hub Hfit.
  apply (valid_lengths_of_nc L maxBits Hub).
  apply nc_bound_by_levels.
  intros b Hb Hprev.
  exact (nc_level_step L b Hprev (Hfit b Hb Hprev)).
Qed.

(** ** 4. CONTROLS

    A conversion lemma with no controls is a lemma that can be true about the
    wrong object.  Both directions are exercised at a REALISTIC width -- 286
    entries, the true [lcodes] bound -- with mixed depths, and the negative
    control sits at the same width and the same shape so the positive
    discriminates on the arithmetic rather than on the vector being small. *)

(** The maximally skewed complete Huffman code: one symbol at each depth 1..14,
    two at depth 15.  Sums to EXACTLY [2 ^ 15], so it also pins the boundary. *)
Definition skew : list nat :=
  [1;2;3;4;5;6;7;8;9;10;11;12;13;14;15;15] ++ repeat 0 270.

Example skew_width : length skew = 286.
Proof. vm_compute. reflexivity. Qed.

Lemma skew_ub : forall len, In len skew -> len <= 15.
Proof.
  intros len Hin. unfold skew in Hin.
  apply in_app_or in Hin as [Hin|Hin].
  - cbn in Hin. lia.
  - apply repeat_spec in Hin. lia.
Qed.

(** POSITIVE: the histogram form computes, and it agrees with the list form. *)
Example skew_hist_value :
  list_sum (map (fun j => bl_count skew j * 2 ^ (15 - j)) (seq 1 15)) = 32768.
Proof. apply Nat.eqb_eq. vm_compute. reflexivity. Qed.

Example skew_sum_value : kraft_sum skew 15 = 32768.
Proof. apply Nat.eqb_eq. vm_compute. reflexivity. Qed.

(** The two views AGREE at the witness -- [kraft_sum_hist] as a tripwire rather
    than as an assertion.  If the conversion were off by a level this fails. *)
Example skew_views_agree :
  kraft_sum skew 15
  = list_sum (map (fun j => bl_count skew j * 2 ^ (15 - j)) (seq 1 15)).
Proof. exact (kraft_sum_hist skew 15 skew_ub). Qed.

(** ...and the same equality by COMPUTATION, independently of the lemma, so the
    tripwire is not testing the lemma against itself. *)
Example skew_views_agree_computed :
  Nat.eqb (kraft_sum skew 15)
          (list_sum (map (fun j => bl_count skew j * 2 ^ (15 - j)) (seq 1 15)))
  = true.
Proof. vm_compute. reflexivity. Qed.

(** The interface, exercised end to end at the witness. *)
Example skew_valid : ValidLengths skew 15.
Proof.
  apply (kraft_from_histogram skew 15 skew_ub).
  rewrite skew_hist_value. apply Nat.leb_le. vm_compute. reflexivity.
Qed.

(** NEGATIVE CONTROL, same width and same shape: one extra 15-bit symbol and the
    code overflows by exactly 1.  The histogram bound must FAIL, otherwise
    [kraft_from_histogram]'s hypothesis is satisfiable by anything and the
    interface is vacuous. *)
Definition skew_over : list nat :=
  [1;2;3;4;5;6;7;8;9;10;11;12;13;14;15;15;15] ++ repeat 0 269.

Example skew_over_width : length skew_over = 286.
Proof. vm_compute. reflexivity. Qed.

Example skew_over_hist_value :
  list_sum (map (fun j => bl_count skew_over j * 2 ^ (15 - j)) (seq 1 15)) = 32769.
Proof. apply Nat.eqb_eq. vm_compute. reflexivity. Qed.

Example skew_over_hist_exceeds :
  Nat.leb (list_sum (map (fun j => bl_count skew_over j * 2 ^ (15 - j)) (seq 1 15)))
          (2 ^ 15) = false.
Proof. vm_compute. reflexivity. Qed.

Example skew_over_not_valid : ~ ValidLengths skew_over 15.
Proof.
  (* [Nat.leb_le] FIRST, then rewrite: converting the sum to its literal 32769
     before moving to the boolean destroys the very subterm
     [skew_over_hist_exceeds] is stated about. *)
  intro HV. apply kraft_to_histogram in HV.
  apply Nat.leb_le in HV.
  rewrite skew_over_hist_exceeds in HV. discriminate.
Qed.

(** CONTROLS on the [nc] form, at the same 286-entry witness.  The two-term
    identity must agree with the fifteen-term sum and with the direct
    computation -- three routes to 32768, so a wrong level offset in any of them
    shows up as a disagreement rather than as a plausible number. *)
Example skew_nc_value : nc skew 15 + bl_count skew 15 = 32768.
Proof. apply Nat.eqb_eq. vm_compute. reflexivity. Qed.

Example skew_nc_agrees_with_sum :
  kraft_sum skew 15 = nc skew 15 + bl_count skew 15.
Proof. exact (kraft_sum_is_nc skew 15 skew_ub). Qed.

Example skew_nc_agrees_computed :
  Nat.eqb (kraft_sum skew 15) (nc skew 15 + bl_count skew 15) = true.
Proof. vm_compute. reflexivity. Qed.

(** NEGATIVE CONTROL: the over-full vector must fail the [nc] test too, at the
    same width, otherwise the two-term form is weaker than the sum it replaces. *)
Example skew_over_nc_exceeds :
  Nat.leb (nc skew_over 15 + bl_count skew_over 15) (2 ^ 15) = false.
Proof. vm_compute. reflexivity. Qed.

Example skew_over_not_valid_via_nc : ~ ValidLengths skew_over 15.
Proof.
  intro HV.
  assert (Hub : forall len, In len skew_over -> len <= 15).
  { intros len Hin. unfold skew_over in Hin.
    apply in_app_or in Hin as [Hin|Hin].
    - cbn in Hin. lia.
    - apply repeat_spec in Hin. lia. }
  apply (valid_lengths_iff_nc skew_over 15 Hub) in HV.
  apply Nat.leb_le in HV. rewrite skew_over_nc_exceeds in HV. discriminate.
Qed.

(** CONTROLS on the per-level route.  [skew] is EXACTLY tight, so it exercises
    the level boundary rather than sitting comfortably inside it: at every level
    [b] the leftover slot count is 1, and the single code at level [b+1] uses one
    of the two slots that leftover buys.  A route that were off by a factor of two
    would pass on a slack witness and fail here. *)
Example skew_levels_tight :
  map (fun b => (2 ^ b - (nc skew b + bl_count skew b))) (seq 0 15)
  = [1;1;1;1;1;1;1;1;1;1;1;1;1;1;1].
Proof. vm_compute. reflexivity. Qed.

(** ...and the per-level interface FIRES at it, so the theorem is not vacuous. *)
Example skew_valid_by_levels : ValidLengths skew 15.
Proof.
  apply (valid_lengths_by_levels skew 15 skew_ub).
  intros b Hb Hprev.
  (* [b < 15] with [b] symbolic: fifteen concrete levels, each decided by
     computation.  [destruct] rather than [lia] because the goal mentions
     [bl_count skew (S b)], which only reduces once [b] is a literal.

     [do 15], NOT [repeat].  With [repeat] this does not terminate and dies as
     "Out of memory" after 100 s: past level 14 the hypothesis [b < 15] is
     contradictory, so [lia] closes the ZERO branch too, the inner tactic never
     fails, and [repeat] keeps destructing forever -- each round leaving another
     vm_computed goal behind.  The OOM is the symptom of a non-failing [repeat],
     not of expensive arithmetic; the arithmetic here is a millisecond. *)
  do 15 (destruct b as [|b]; [vm_compute; lia|]). lia.
Qed.

(** NEGATIVE CONTROL: the over-full vector must break the fit at SOME level,
    otherwise the per-level condition is not equivalent to Kraft.  It breaks at
    the top: level 15 wants three codes where the leftover buys two. *)
Example skew_over_level_15_overfull :
  Nat.leb (bl_count skew_over 15)
          (2 * (2 ^ 14 - (nc skew_over 14 + bl_count skew_over 14))) = false.
Proof. vm_compute. reflexivity. Qed.

(** LIVENESS CONTROL for the generic-in-[maxBits] claim, which is otherwise a
    claim about a binder nobody exercised: the same theorem at [maxBits = 7],
    which is ledger item 2's [ValidLengths cl 7] for the code-length tree.
    [twt_lens]'s shape, padded to the 19 entries [cl] has. *)
Definition cl7 : list nat := [3;3;3;3;3;0;0;0;0;0;2] ++ repeat 0 8.

Lemma cl7_ub : forall len, In len cl7 -> len <= 7.
Proof.
  intros len Hin. unfold cl7 in Hin.
  apply in_app_or in Hin as [Hin|Hin].
  - cbn in Hin. lia.
  - apply repeat_spec in Hin. lia.
Qed.

Example cl7_width : length cl7 = 19.
Proof. vm_compute. reflexivity. Qed.

Example cl7_valid_at_7 : ValidLengths cl7 7.
Proof.
  apply (kraft_from_histogram cl7 7 cl7_ub).
  apply Nat.leb_le. vm_compute. reflexivity.
Qed.

(** ** 5. THE SHARP-SLACK CONTROL (ld-seams', and it is better than mine)

    Every control above is at [maxBits = 15], where [skew]'s slack is 0 and
    [cl7]'s at 7 is comfortable.  ld-seams pointed out the failure those cannot
    see: **a witness with large slack still passes with an off-by-one in the
    exponent.**  Their instance is the fleet's own round-trip vector
    ([SendTreeRT.v:126-137], [twt_lens = [3;3;3;3;3;0;0;0;0;0;2]]) taken at
    [maxBits = 3] rather than 15:

        maxBits = 15   5*2^12 + 1*2^13 = 20480 + 8192 = 28672 <= 32768   slack 4096
        maxBits =  3   5*2^0  + 1*2^1  =     5 +    2 =     7 <=     8   slack 1

    **Slack 1 is the whole point**: shift the exponent by one anywhere in the
    chain and the sum moves by at least 1, so the control fails.  At slack 4096 it
    would not.  Using their vector rather than a fresh one also means the witness
    has a producer -- it is a length vector some tree actually emits, not a list I
    chose to satisfy the predicate. *)
Definition twt3 : list nat := [3;3;3;3;3;0;0;0;0;0;2].

Lemma twt3_ub : forall len, In len twt3 -> len <= 3.
Proof. intros len Hin. unfold twt3 in Hin. cbn in Hin. lia. Qed.

Example twt3_sum_is_7 : kraft_sum twt3 3 = 7.
Proof. apply Nat.eqb_eq. vm_compute. reflexivity. Qed.

Example twt3_budget_is_8 : (2 ^ 3)%nat = 8.
Proof. vm_compute. reflexivity. Qed.

(** POSITIVE at slack 1, through the [nc] route -- so the two-term identity is
    exercised where a one-off exponent error cannot hide. *)
Example twt3_nc_is_7 : nc twt3 3 + bl_count twt3 3 = 7.
Proof. apply Nat.eqb_eq. vm_compute. reflexivity. Qed.

Example twt3_valid : ValidLengths twt3 3.
Proof.
  apply (valid_lengths_of_nc twt3 3 twt3_ub).
  rewrite twt3_nc_is_7. apply Nat.leb_le. vm_compute. reflexivity.
Qed.

(** ...and through the per-level route, independently. *)
Example twt3_valid_by_levels : ValidLengths twt3 3.
Proof.
  apply (valid_lengths_by_levels twt3 3 twt3_ub).
  intros b Hb Hprev.
  do 3 (destruct b as [|b]; [vm_compute; lia|]). lia.
Qed.

(** NEGATIVE CONTROL ONE STEP AWAY: two more 3-bit codes and the sum is 9 > 8.
    The nearest failing vector, not an extreme one -- so the positive above is
    discriminating at the boundary rather than merely inside it. *)
Definition twt3_over : list nat := [3;3;3;3;3;3;3;0;0;0;2].

Example twt3_over_sum_is_9 : kraft_sum twt3_over 3 = 9.
Proof. apply Nat.eqb_eq. vm_compute. reflexivity. Qed.

Example twt3_over_rejected : valid_lengths_b twt3_over 3 = false.
Proof. vm_compute. reflexivity. Qed.

Example twt3_over_not_valid : ~ ValidLengths twt3_over 3.
Proof.
  intro HV.
  assert (Hub : forall len, In len twt3_over -> len <= 3)
    by (intros len Hin; unfold twt3_over in Hin; cbn in Hin; lia).
  apply (valid_lengths_iff_nc twt3_over 3 Hub) in HV.
  apply Nat.leb_le in HV.
  assert (E : Nat.leb (nc twt3_over 3 + bl_count twt3_over 3) (2 ^ 3) = false)
    by (vm_compute; reflexivity).
  rewrite E in HV. discriminate.
Qed.

(** AND THE BOUNDARY BETWEEN THEM: six 3-bit codes plus the 2 is EXACTLY 8, still
    valid.  So the rejection above is about crossing 8, not about seven codes
    being disallowed -- the same sharpening huffman-id used for
    [kraft_admits_exactly_two]. *)
Definition twt3_exact : list nat := [3;3;3;3;3;3;0;0;0;0;2].

Example twt3_exact_sum_is_8 : kraft_sum twt3_exact 3 = 8.
Proof. apply Nat.eqb_eq. vm_compute. reflexivity. Qed.

Example twt3_exact_valid : valid_lengths_b twt3_exact 3 = true.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions kraft_tail_vanishes.
Print Assumptions kraft_sum_from_hist.
Print Assumptions kraft_sum_hist.
Print Assumptions kraft_from_histogram.
Print Assumptions kraft_to_histogram.
Print Assumptions kraft_sum_is_nc.
Print Assumptions valid_lengths_iff_nc.
Print Assumptions valid_lengths_of_nc.
Print Assumptions nc_bound_by_levels.
Print Assumptions nc_level_step.
Print Assumptions valid_lengths_by_levels.
Print Assumptions skew_valid_by_levels.
Print Assumptions skew_over_level_15_overfull.
Print Assumptions skew_nc_agrees_with_sum.
Print Assumptions skew_over_not_valid_via_nc.
Print Assumptions skew_valid.
Print Assumptions skew_over_not_valid.
Print Assumptions cl7_valid_at_7.
Print Assumptions twt3_valid.
Print Assumptions twt3_valid_by_levels.
Print Assumptions twt3_over_not_valid.
Print Assumptions twt3_exact_valid.
