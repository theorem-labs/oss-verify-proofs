(** * Spec.PngModel.InftreesBridge — zlib's Kraft counter vs the
      declarative Kraft condition.

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT.

    A BRIDGE, so unlike the two files it joins it is allowed — and
    required — to import both sides.  [Inftrees.v] is the bug-for-bug
    transcription of [inftrees.c] and must not know about the declarative
    spec; [Huff.v] is L0's frozen surface and must not know about the
    transcription.  Same layering call as [ZBitsBridge.v], which does the
    same job for the bit reader.

    WHAT IS RELATED.  [inftrees.c:125-132] accepts a code-length set iff

<<
      it_kraft 15 1 1 cnt0 = Some lft  /\  it_incomplete ty lft mx = false
>>

    whereas [Huff.ValidLengths lengths 15] is "every length is at most 15
    AND the Kraft sum is at most 2^15".  The two halves of the C's test
    behave very differently and this file keeps them apart.

    ** THE KRAFT HALF IS AN IFF — the claim held, unweakened.

    [it_kraft_spec] says exactly what the counter returns:

<<
      it_kraft maxBits 1 1 cnt
      = if kraft_sum lengths maxBits <=? 2 ^ maxBits
        then Some (2 ^ maxBits - kraft_sum lengths maxBits)
        else None
>>

    so [it_kraft ... <> None] IS the Kraft inequality
    ([it_kraft_some_iff_valid], both directions), and when it holds the
    residual [lft] is pinned to [2^maxBits - kraft_sum]
    ([it_kraft_left_value]).  The C's per-iteration [left < 0] test loses
    nothing, exactly as argued: [itk_left_closed] gives
    [left_len = 2^len - sum_{j<=len} cnt[j] * 2^(len-j)] in closed form,
    and [it_kraft_as_left] turns "some intermediate went negative" into
    "the final residual is negative" — the negative branch multiplies the
    deficit by the remaining [2^k > 0] and subtracts a NON-NEGATIVE tail
    ([itk_sum_nonneg]), so it can only get more negative.

    ONE SIDE CONDITION IS LOAD-BEARING AND WAS NOT IN THE INFORMAL
    ARGUMENT'S STATEMENT (only in its reasoning): the counts must be
    non-negative.  Without that the equivalence is FALSE, and
    [nonneg_hypothesis_load_bearing] exhibits a [cnt] with a negative
    entry where [it_kraft] returns [None] while the final residual is
    [802816 > 0].  Here non-negativity is free: it follows from the
    histogram hypothesis, and in the C the array is [unsigned short].

    ** [it_kraft] NEVER READS [cnt 0], BY UNREACHABILITY.

    It is called with [len = 1] and fuel 15, so it visits exactly indices
    [1 .. 15].  [it_kraft_ext_on] is the congruence — the result depends
    on [cnt] only over [[len, len + n)] — and
    [it_kraft_never_reads_cnt0] specialises it: overwriting [cnt 0] with
    ANY value changes nothing.  This is why [CountsOf] below constrains
    only [1 <= b <= maxBits], and why the bridge needs no [cnt 0 = 0]
    hypothesis and no [bl_count]-style fix-up.

    A reader who knows RFC 1951 §3.2.2 will look for the [bl_count[0] = 0]
    fix-up and wonder where it went.  Two answers, both lemmas.  On the
    spec side it is already there: [kraft_sum_from_1] shows
    [kraft_sum lengths maxBits = kraft_sum_from lengths maxBits 1], i.e.
    the [b = 0] term of [Huff]'s sum is identically zero.  On the C side
    it is never needed: [it_count] really does put the count of UNUSED
    symbols into bucket 0 ([zero_lengths_bucket0] computes it to 2 for
    [[0;0;1;1]]), and [it_kraft] still returns the right answer
    ([zero_lengths_valid] takes that concrete histogram all the way to
    [ValidLengths]).  The unreachability argument is also pinned as
    non-trivial: [it_kraft_at_0_does_read_cnt0] shows that the SAME
    function started one index lower does read bucket 0 and gives a
    different answer, so the [len = 1] start is doing real work.

    ** THE OTHER HALF IS ONE-WAY, AND THIS IS NOT AN IFF.

    [it_accept_valid] is the direction that matters: implementation
    accepts ==> [ValidLengths] (hence [it_accept_prefix_free], which is
    what a decoder walk wants out of this file).  It goes through the
    Kraft half alone — [it_incomplete] is not consulted.

    THE CONVERSE IS FALSE.  [ValidLengths] does NOT imply the accept
    condition, because [it_incomplete] additionally rejects an INCOMPLETE
    code (residual [lft > 0]) whenever [ty = CT_CODES] or [mx <> 1].  Two
    witnesses, both with the [mx] the driver itself computes:
    [valid_but_rejected_codes] ([lengths = [1]], [ty = CT_CODES]) and
    [valid_but_rejected_lens] ([lengths = [2]], [ty = CT_LENS], [mx = 2]).
    Do not read anything in this file as an iff between [it_accept] and
    [ValidLengths]; only the KRAFT half is one.

    Neither is [it_accept] vacuous: [accept_complete] (a complete code)
    and [accept_incomplete_dists] (zlib's deliberately-accepted
    one-symbol distance code) satisfy it.

    ** TIE-IN TO THE DRIVER.  [it_pre_err_iff] shows the pair really is
    the driver's accept test: for [mx <> 0], [it_pre] returns [PreErr]
    exactly when [it_accept] fails.  The [mx <> 0] side condition is
    load-bearing ([it_pre_err_mx_needed]): the all-zero-lengths call
    leaves via the [max == 0] arm before ever reaching [:125].

    ** THE HISTOGRAM OBLIGATION IS DISCHARGED, in §8.

    [CountsOf] is still a hypothesis of everything in §§3-6, and those
    statements are kept: a caller who obtains [CountsOf] by some other
    route (a decoder tracking the histogram symbolically, say) still wants
    them.  What §8 adds is the discharge for the real thing.
    [counts_of_it_count] proves [CountsOf] of the histogram [it_count]
    actually builds, at the shape [it_pre] actually calls it with, and the
    headline results are restated with the hypothesis gone --
    [it_kraft_spec_of_lengths], [it_accept_valid_of_lengths],
    [it_accept_prefix_free_of_lengths].  The driver-level form is
    [it_pre_go_prefix_free]: if [it_pre] handed a state to the loop then
    the length list is prefix-free, with nothing assumed but the 15-bit
    length bound.  [L11_prefix_free_via_driver] runs that chain on a
    concrete list, so it is not vacuous. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Base Huff Inftrees.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** ** 1.  What the counter reads

    [it_kraft n len left cnt] consults [cnt] only at [len, len+1, ...,
    len+n-1].  Stated as a congruence over [Base.arr_eq_on], which is the
    shape everything else in this tree composes with. *)

Lemma it_kraft_ext_on :
  forall n cnt cnt' len left,
    arr_eq_on cnt cnt' len (len + Z.of_nat n) ->
    it_kraft n len left cnt = it_kraft n len left cnt'.
Proof.
  induction n as [|k IH]; intros cnt cnt' len left H; cbn [it_kraft];
    [reflexivity|].
  assert (Hc : cnt len = cnt' len) by (apply H; lia).
  rewrite Hc.
  destruct (Z.ltb_spec (left * 2 - cnt' len) 0); [reflexivity|].
  apply IH. intros j Hj. apply H. lia.
Qed.

(** Anything strictly below the starting index is invisible. *)
Corollary it_kraft_ignores_below :
  forall n cnt len left i v,
    i < len -> it_kraft n len left (zset cnt i v) = it_kraft n len left cnt.
Proof.
  intros n cnt len left i v Hi.
  apply it_kraft_ext_on. intros j Hj. apply zset_other. lia.
Qed.

(** THE CLAIM: the [len = 1] call never reads [cnt 0].  Stated in the
    strongest available form — bucket 0 may hold ANY value at all. *)
Corollary it_kraft_never_reads_cnt0 :
  forall n cnt left v,
    it_kraft n 1 left (zset cnt 0 v) = it_kraft n 1 left cnt.
Proof. intros. apply it_kraft_ignores_below. lia. Qed.

(** Symmetrically, nothing at or above [len + n] is read. *)
Corollary it_kraft_ignores_above :
  forall n cnt len left i v,
    len + Z.of_nat n <= i ->
    it_kraft n len left (zset cnt i v) = it_kraft n len left cnt.
Proof.
  intros n cnt len left i v Hi.
  apply it_kraft_ext_on. intros j Hj. apply zset_other. lia.
Qed.

(** "Visits EXACTLY buckets 1..15", as one statement — and it is exactly
    the range [CountsOf] below constrains. *)
Corollary it_kraft_15_window :
  forall cnt cnt' left,
    (forall b, (1 <= b <= 15)%nat -> cnt (Z.of_nat b) = cnt' (Z.of_nat b)) ->
    it_kraft 15%nat 1 left cnt = it_kraft 15%nat 1 left cnt'.
Proof.
  intros cnt cnt' left H. apply it_kraft_ext_on. intros j Hj.
  assert (Hb : (1 <= Z.to_nat j <= 15)%nat) by lia.
  specialize (H _ Hb).
  replace (Z.of_nat (Z.to_nat j)) with j in H by lia. exact H.
Qed.

(** ... and the same function started one index lower DOES read bucket 0,
    so the corollaries above are facts about the call site, not vacuous
    properties of [it_kraft].  A test that a wrong start index would fail. *)
Lemma it_kraft_at_0_does_read_cnt0 :
  it_kraft 16%nat 0 1 (zset zzero 0 5) <> it_kraft 16%nat 0 1 zzero.
Proof. vm_compute. discriminate. Qed.

(** ** 2.  The counter in closed form

    [itk_left] is [it_kraft] with the [left < 0] test deleted: the
    "final residual regardless of intermediate failure".  The whole
    content of the Kraft claim is that under non-negative counts the two
    agree on acceptance. *)

Fixpoint itk_left (n : nat) (len left : Z) (cnt : zarr) : Z :=
  match n with
  | O => left
  | S k => itk_left k (len + 1) (left * 2 - cnt len) cnt
  end.

(** [itk_sum n len cnt = sum_{i<n} cnt (len+i) * 2^(n-1-i)]. *)
Fixpoint itk_sum (n : nat) (len : Z) (cnt : zarr) : Z :=
  match n with
  | O => 0
  | S k => cnt len * 2 ^ Z.of_nat k + itk_sum k (len + 1) cnt
  end.

(** The comment above [itk_sum], as a checkable claim rather than prose. *)
Example itk_sum_unfold3 : forall len cnt,
  itk_sum 3%nat len cnt = 4 * cnt len + 2 * cnt (len + 1) + 1 * cnt (len + 2).
Proof.
  intros len cnt. cbn [itk_sum].
  replace (len + 1 + 1) with (len + 2) by ring.
  change (2 ^ Z.of_nat 2) with 4.
  change (2 ^ Z.of_nat 1) with 2.
  change (2 ^ Z.of_nat 0) with 1.
  ring.
Qed.

Lemma itk_left_closed :
  forall n len left cnt,
    itk_left n len left cnt = left * 2 ^ Z.of_nat n - itk_sum n len cnt.
Proof.
  induction n as [|k IH]; intros len left cnt; cbn [itk_left itk_sum].
  - change (Z.of_nat 0) with 0. rewrite Z.pow_0_r. ring.
  - rewrite IH, Nat2Z.inj_succ, Z.pow_succ_r by lia. ring.
Qed.

Lemma itk_sum_nonneg :
  forall n len cnt,
    (forall j, len <= j < len + Z.of_nat n -> 0 <= cnt j) ->
    0 <= itk_sum n len cnt.
Proof.
  induction n as [|k IH]; intros len cnt H; cbn [itk_sum]; [lia|].
  assert (H0 : 0 <= cnt len) by (apply H; lia).
  assert (Hp : 0 < 2 ^ Z.of_nat k) by (apply Z.pow_pos_nonneg; lia).
  assert (Ht : 0 <= itk_sum k (len + 1) cnt)
    by (apply IH; intros j Hj; apply H; lia).
  nia.
Qed.

(** THE KEY LEMMA.  Under non-negative counts and a non-negative start,
    the per-iteration [left < 0] test is equivalent to testing the FINAL
    residual: an intermediate deficit is multiplied by the remaining
    [2^k > 0] and then has a non-negative tail subtracted, so it can only
    get worse.  [None] and "final residual negative" coincide. *)
Lemma it_kraft_as_left :
  forall n len left cnt,
    0 <= left ->
    (forall j, len <= j < len + Z.of_nat n -> 0 <= cnt j) ->
    it_kraft n len left cnt
    = (if 0 <=? itk_left n len left cnt
       then Some (itk_left n len left cnt) else None).
Proof.
  induction n as [|k IH]; intros len left cnt Hl Hc; cbn [it_kraft itk_left].
  - destruct (Z.leb_spec 0 left); [reflexivity | exfalso; lia].
  - set (l := left * 2 - cnt len).
    destruct (Z.ltb_spec l 0) as [Hneg|Hpos].
    + assert (Hs : 0 <= itk_sum k (len + 1) cnt)
        by (apply itk_sum_nonneg; intros j Hj; apply Hc; lia).
      assert (Hp : 0 < 2 ^ Z.of_nat k) by (apply Z.pow_pos_nonneg; lia).
      rewrite itk_left_closed.
      assert (Hlp : l * 2 ^ Z.of_nat k < 0) by nia.
      destruct (Z.leb_spec 0 (l * 2 ^ Z.of_nat k - itk_sum k (len + 1) cnt));
        [exfalso; lia | reflexivity].
    + assert (H1 : 0 <= l) by lia.
      assert (H2 : forall j, len + 1 <= j < len + 1 + Z.of_nat k -> 0 <= cnt j)
        by (intros j Hj; apply Hc; lia).
      rewrite (IH (len + 1) l cnt H1 H2). reflexivity.
Qed.

(** NON-NEGATIVITY IS LOAD-BEARING, not decoration.  With one negative
    count the intermediate test fires while the final residual is
    comfortably positive, so [it_kraft_as_left] is false without its
    hypothesis.  (Unreachable for a real histogram; the C's [count[]] is
    an array of [unsigned short].) *)
Definition cnt_neg : zarr := zset (zset zzero 1 3) 2 (-100).

Lemma nonneg_hypothesis_load_bearing :
  it_kraft 15%nat 1 1 cnt_neg = None
  /\ itk_left 15%nat 1 1 cnt_neg = 802816.
Proof. split; vm_compute; reflexivity. Qed.

(** ** 3.  The histogram relation

    [cnt] is a [zarr]; [Huff.ValidLengths] is over a [list nat].  This is
    the correspondence.  It is a HYPOTHESIS here, so that everything in
    §§3-6 holds of any histogram however obtained; §8 discharges it for the
    histogram [it_count] actually builds ([counts_of_it_count]).

    Note what is NOT constrained: bucket 0 (see §1: never read) and every
    bucket above [maxBits].  [count_len] rather than [bl_count] on
    purpose: [count_len] is literally what [it_count] tallies, including
    the unused symbols in bucket 0. *)

Definition CountsOf (cnt : zarr) (lengths : list nat) (maxBits : nat) : Prop :=
  forall b, (1 <= b <= maxBits)%nat ->
    cnt (Z.of_nat b) = Z.of_nat (count_len lengths b).

(** Above [maxBits] the spec-side sum is empty — needs the length bound. *)
Lemma kraft_sum_from_above :
  forall lengths maxBits b,
    (forall len, In len lengths -> (len <= maxBits)%nat) ->
    (maxBits < b)%nat ->
    kraft_sum_from lengths maxBits b = 0%nat.
Proof.
  induction lengths as [|x l IH]; intros maxBits b Hle Hb.
  - apply kraft_sum_from_nil.
  - rewrite kraft_sum_from_cons.
    rewrite (IH maxBits b);
      [ | intros len Hin; apply Hle; now right | exact Hb ].
    assert (Hx : (x <= maxBits)%nat) by (apply Hle; now left).
    unfold kraft_at.
    destruct (Nat.leb_spec b x); [exfalso; lia | reflexivity].
Qed.

(** RFC 1951 §3.2.2's [bl_count[0] = 0], on the SPEC side: [Huff]'s Kraft
    sum already ignores bucket 0, so the C not touching it is agreement,
    not a missing fix-up. *)
Lemma kraft_sum_from_1 :
  forall lengths maxBits,
    kraft_sum lengths maxBits = kraft_sum_from lengths maxBits 1.
Proof.
  intros lengths maxBits. unfold kraft_sum.
  rewrite (kraft_sum_from_step_bl maxBits 0 lengths), bl_count_0. lia.
Qed.

Lemma itk_sum_kraft :
  forall (m : nat) (lengths : list nat) (maxBits b : nat) (cnt : zarr),
    (b + m = S maxBits)%nat -> (1 <= b)%nat ->
    (forall len, In len lengths -> (len <= maxBits)%nat) ->
    (forall j, (b <= j < b + m)%nat ->
       cnt (Z.of_nat j) = Z.of_nat (count_len lengths j)) ->
    itk_sum m (Z.of_nat b) cnt = Z.of_nat (kraft_sum_from lengths maxBits b).
Proof.
  induction m as [|k IH]; intros lengths maxBits b cnt Hbm Hb Hle Hcnt.
  - cbn [itk_sum].
    rewrite (kraft_sum_from_above lengths maxBits b Hle) by lia. reflexivity.
  - cbn [itk_sum].
    assert (Hk : k = (maxBits - b)%nat) by lia.
    rewrite (Hcnt b) by lia.
    replace (Z.of_nat b + 1) with (Z.of_nat (S b)) by lia.
    rewrite (IH lengths maxBits (S b) cnt);
      [ | lia | lia | exact Hle | intros j Hj; apply Hcnt; lia ].
    rewrite (kraft_sum_from_step_bl maxBits b lengths).
    rewrite (bl_count_pos lengths b Hb).
    rewrite Nat2Z.inj_add, Nat2Z.inj_mul, <- two_pow_nat, Hk.
    reflexivity.
Qed.

Lemma itk_left_kraft :
  forall lengths maxBits cnt,
    (forall len, In len lengths -> (len <= maxBits)%nat) ->
    CountsOf cnt lengths maxBits ->
    itk_left maxBits 1 1 cnt
    = 2 ^ Z.of_nat maxBits - Z.of_nat (kraft_sum lengths maxBits).
Proof.
  intros lengths maxBits cnt Hle Hc.
  rewrite itk_left_closed, kraft_sum_from_1.
  change (itk_sum maxBits 1 cnt) with (itk_sum maxBits (Z.of_nat 1) cnt).
  rewrite (itk_sum_kraft maxBits lengths maxBits 1%nat cnt);
    [ | lia | lia | exact Hle | intros j Hj; apply Hc; lia ].
  lia.
Qed.

(** THE KRAFT BRIDGE, in the sharpest form available: an equation that
    says exactly what the C's counter returns. *)
Theorem it_kraft_spec :
  forall lengths maxBits cnt,
    (forall len, In len lengths -> (len <= maxBits)%nat) ->
    CountsOf cnt lengths maxBits ->
    it_kraft maxBits 1 1 cnt
    = (if (kraft_sum lengths maxBits <=? 2 ^ maxBits)%nat
       then Some (2 ^ Z.of_nat maxBits - Z.of_nat (kraft_sum lengths maxBits))
       else None).
Proof.
  intros lengths maxBits cnt Hle Hc.
  assert (Hnn : forall j, 1 <= j < 1 + Z.of_nat maxBits -> 0 <= cnt j).
  { intros j Hj.
    assert (Hb : (1 <= Z.to_nat j <= maxBits)%nat) by lia.
    specialize (Hc _ Hb).
    replace (Z.of_nat (Z.to_nat j)) with j in Hc by lia.
    rewrite Hc. lia. }
  rewrite (it_kraft_as_left maxBits 1 1 cnt ltac:(lia) Hnn).
  rewrite (itk_left_kraft lengths maxBits cnt Hle Hc).
  assert (Hp : 2 ^ Z.of_nat maxBits = Z.of_nat (2 ^ maxBits)) by apply two_pow_nat.
  destruct ((kraft_sum lengths maxBits <=? 2 ^ maxBits)%nat) eqn:Hb.
  - apply Nat.leb_le in Hb.
    destruct (Z.leb_spec 0
      (2 ^ Z.of_nat maxBits - Z.of_nat (kraft_sum lengths maxBits)));
      [reflexivity | exfalso; lia].
  - apply Nat.leb_gt in Hb.
    destruct (Z.leb_spec 0
      (2 ^ Z.of_nat maxBits - Z.of_nat (kraft_sum lengths maxBits)));
      [exfalso; lia | reflexivity].
Qed.

(** The claim as an iff: over-subscription detection is EXACTLY the Kraft
    inequality, in both directions. *)
Corollary it_kraft_some_iff_valid :
  forall lengths maxBits cnt,
    (forall len, In len lengths -> (len <= maxBits)%nat) ->
    CountsOf cnt lengths maxBits ->
    (it_kraft maxBits 1 1 cnt <> None <-> ValidLengths lengths maxBits).
Proof.
  intros lengths maxBits cnt Hle Hc.
  rewrite (it_kraft_spec lengths maxBits cnt Hle Hc).
  unfold ValidLengths.
  destruct ((kraft_sum lengths maxBits <=? 2 ^ maxBits)%nat) eqn:Hb.
  - apply Nat.leb_le in Hb.
    split; [intros _; split; assumption | intros _; discriminate].
  - apply Nat.leb_gt in Hb.
    split; [intros HN; exfalso; now apply HN | intros [_ HK]; lia].
Qed.

(** ... and the residual is pinned when it succeeds. *)
Corollary it_kraft_left_value :
  forall lengths maxBits cnt lft,
    (forall len, In len lengths -> (len <= maxBits)%nat) ->
    CountsOf cnt lengths maxBits ->
    it_kraft maxBits 1 1 cnt = Some lft ->
    lft = 2 ^ Z.of_nat maxBits - Z.of_nat (kraft_sum lengths maxBits)
    /\ ValidLengths lengths maxBits.
Proof.
  intros lengths maxBits cnt lft Hle Hc Hk.
  assert (HV : ValidLengths lengths maxBits).
  { apply (it_kraft_some_iff_valid lengths maxBits cnt Hle Hc).
    rewrite Hk. discriminate. }
  split; [|exact HV].
  rewrite (it_kraft_spec lengths maxBits cnt Hle Hc) in Hk.
  destruct ((kraft_sum lengths maxBits <=? 2 ^ maxBits)%nat);
    [now inversion Hk | discriminate].
Qed.

Corollary it_kraft_of_valid :
  forall lengths maxBits cnt,
    (forall len, In len lengths -> (len <= maxBits)%nat) ->
    CountsOf cnt lengths maxBits ->
    ValidLengths lengths maxBits ->
    it_kraft maxBits 1 1 cnt
    = Some (2 ^ Z.of_nat maxBits - Z.of_nat (kraft_sum lengths maxBits)).
Proof.
  intros lengths maxBits cnt Hle Hc [_ HK].
  rewrite (it_kraft_spec lengths maxBits cnt Hle Hc).
  now rewrite (proj2 (Nat.leb_le _ _) HK).
Qed.

(** The call [inftrees.c] actually makes, with [MAXBITS = 15] plugged in. *)
Corollary it_kraft_15_spec :
  forall lengths cnt,
    (forall len, In len lengths -> (len <= 15)%nat) ->
    CountsOf cnt lengths 15%nat ->
    it_kraft 15%nat 1 1 cnt
    = (if (kraft_sum lengths 15 <=? 32768)%nat
       then Some (32768 - Z.of_nat (kraft_sum lengths 15))
       else None).
Proof.
  intros lengths cnt Hle Hc.
  rewrite (it_kraft_spec lengths 15%nat cnt Hle Hc).
  replace (2 ^ Z.of_nat 15) with 32768 by reflexivity.
  replace ((2 ^ 15)%nat) with 32768%nat by reflexivity.
  reflexivity.
Qed.

(** ** 4.  The accept condition

    The pair from [inftrees.c:129] and [:132], at the fuel and start the
    driver uses.  [it_incomplete] is used as-is, never inlined: WP-5's
    phase-PC walk is pinned to that exact expression. *)

Definition it_accept (ty mx : Z) (cnt : zarr) : Prop :=
  exists lft, it_kraft 15%nat 1 1 cnt = Some lft
              /\ it_incomplete ty lft mx = false.

(** THE DIRECTION THAT MATTERS.  Note it goes through the Kraft half
    alone: [it_incomplete] only ever REJECTS more, so it cannot break the
    implication. *)
Theorem it_accept_valid :
  forall ty mx cnt lengths,
    (forall len, In len lengths -> (len <= 15)%nat) ->
    CountsOf cnt lengths 15%nat ->
    it_accept ty mx cnt ->
    ValidLengths lengths 15%nat.
Proof.
  intros ty mx cnt lengths Hle Hc [lft [Hk _]].
  apply (it_kraft_some_iff_valid lengths 15%nat cnt Hle Hc).
  rewrite Hk. discriminate.
Qed.

(** What the bridge buys a decoder walk. *)
Corollary it_accept_prefix_free :
  forall ty mx cnt lengths,
    (forall len, In len lengths -> (len <= 15)%nat) ->
    CountsOf cnt lengths 15%nat ->
    it_accept ty mx cnt ->
    PrefixFreeTable (code_table lengths 15%nat).
Proof.
  intros ty mx cnt lengths Hle Hc Ha.
  apply code_table_prefix_free.
  exact (it_accept_valid ty mx cnt lengths Hle Hc Ha).
Qed.

Corollary it_accept_codes_prefix_free :
  forall ty mx cnt lengths s1 s2 cw1 cw2,
    (forall len, In len lengths -> (len <= 15)%nat) ->
    CountsOf cnt lengths 15%nat ->
    it_accept ty mx cnt ->
    code_for lengths 15%nat s1 = Some cw1 ->
    code_for lengths 15%nat s2 = Some cw2 ->
    s1 <> s2 ->
    is_prefix cw1 cw2 = false.
Proof.
  intros ty mx cnt lengths s1 s2 cw1 cw2 Hle Hc Ha H1 H2 Hs.
  eapply canonical_prefix_free;
    [ exact (it_accept_valid ty mx cnt lengths Hle Hc Ha)
    | exact H1 | exact H2 | exact Hs ].
Qed.

(** ** 5.  [it_incomplete], and why the converse fails

    Every claim the docstring makes about [it_incomplete] is one of these
    four lemmas. *)

(** A COMPLETE code (residual 0) is always accepted. *)
Lemma it_incomplete_complete : forall ty mx, it_incomplete ty 0 mx = false.
Proof. intros ty mx. unfold it_incomplete. reflexivity. Qed.

(** zlib's one deliberate exception: an incomplete DISTS code whose
    longest code is one bit. *)
Lemma it_incomplete_dists_one : forall lft, it_incomplete CT_DISTS lft 1 = false.
Proof.
  intros lft. unfold it_incomplete, CT_DISTS.
  replace ((0 =? 2) || negb (1 =? 1))%bool with false by reflexivity.
  apply andb_false_r.
Qed.

(** An incomplete CODES set is always rejected, whatever [mx]. *)
Lemma it_incomplete_codes : forall lft mx, 0 < lft -> it_incomplete CT_CODES lft mx = true.
Proof.
  intros lft mx H. unfold it_incomplete, CT_CODES.
  replace ((0 =? 0) || negb (mx =? 1))%bool with true by reflexivity.
  rewrite andb_true_r. now apply Z.ltb_lt.
Qed.

(** Any incomplete set whose longest code is longer than one bit is
    rejected, whatever the type. *)
Lemma it_incomplete_nonunit :
  forall ty lft mx, 0 < lft -> mx <> 1 -> it_incomplete ty lft mx = true.
Proof.
  intros ty lft mx Hl Hm. unfold it_incomplete.
  rewrite (proj2 (Z.ltb_lt 0 lft) Hl).
  rewrite (proj2 (Z.eqb_neq mx 1) Hm).
  cbn [negb]. rewrite orb_true_r. reflexivity.
Qed.

(** Concrete histograms.  Each is the [count_len] histogram of the
    [lengths] it is paired with; [counts15] discharges that by
    computation over all fifteen live buckets. *)

Ltac counts15 :=
  unfold CountsOf; intros b Hb;
  destruct b as [|b]; [lia|];
  do 15 (destruct b as [|b]; [vm_compute; reflexivity|]);
  lia.

Lemma bound15_of_forallb :
  forall l : list nat,
    forallb (fun x => Nat.leb x 15) l = true ->
    forall len, In len l -> (len <= 15)%nat.
Proof.
  intros l H len Hin. rewrite forallb_forall in H.
  now apply Nat.leb_le, H.
Qed.

Definition L1 : list nat := [1%nat].          (** one 1-bit code: incomplete *)
Definition L2 : list nat := [2%nat].          (** one 2-bit code: incomplete *)
Definition L11 : list nat := [1%nat; 1%nat].  (** two 1-bit codes: complete *)
Definition L111 : list nat := [1%nat; 1%nat; 1%nat].  (** over-subscribed *)

Definition cnt1 : zarr := zset zzero 1 1.
Definition cnt2 : zarr := zset zzero 2 1.
Definition cnt11 : zarr := zset zzero 1 2.
Definition cnt111 : zarr := zset zzero 1 3.

Lemma cnt1_counts : CountsOf cnt1 L1 15%nat.   Proof. counts15. Qed.
Lemma cnt2_counts : CountsOf cnt2 L2 15%nat.   Proof. counts15. Qed.
Lemma cnt11_counts : CountsOf cnt11 L11 15%nat. Proof. counts15. Qed.
Lemma cnt111_counts : CountsOf cnt111 L111 15%nat. Proof. counts15. Qed.

Lemma L1_bound : forall len, In len L1 -> (len <= 15)%nat.
Proof. apply bound15_of_forallb. reflexivity. Qed.
Lemma L2_bound : forall len, In len L2 -> (len <= 15)%nat.
Proof. apply bound15_of_forallb. reflexivity. Qed.
Lemma L11_bound : forall len, In len L11 -> (len <= 15)%nat.
Proof. apply bound15_of_forallb. reflexivity. Qed.
Lemma L111_bound : forall len, In len L111 -> (len <= 15)%nat.
Proof. apply bound15_of_forallb. reflexivity. Qed.

(** THE CONVERSE IS FALSE, witness 1: a valid but incomplete CODES set.
    [mx] is not chosen adversarially — it is the value [it_pre] itself
    computes from this very histogram. *)
Theorem valid_but_rejected_codes :
  ValidLengths L1 15%nat
  /\ it_findmax 15%nat MAXBITS cnt1 = 1
  /\ ~ it_accept CT_CODES (it_findmax 15%nat MAXBITS cnt1) cnt1.
Proof.
  split; [apply valid_lengths_b_true; vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  intros [lft [Hk Hi]].
  vm_compute in Hk. inversion Hk. subst lft.
  vm_compute in Hi. discriminate.
Qed.

(** Witness 2: a valid but incomplete LENS set with [mx = 2]. *)
Theorem valid_but_rejected_lens :
  ValidLengths L2 15%nat
  /\ it_findmax 15%nat MAXBITS cnt2 = 2
  /\ ~ it_accept CT_LENS (it_findmax 15%nat MAXBITS cnt2) cnt2.
Proof.
  split; [apply valid_lengths_b_true; vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  intros [lft [Hk Hi]].
  vm_compute in Hk. inversion Hk. subst lft.
  vm_compute in Hi. discriminate.
Qed.

(** NON-VACUITY of [it_accept]: without these, [it_accept_valid] would be
    a theorem about the empty set. *)
Theorem accept_complete : it_accept CT_LENS 1 cnt11.
Proof.
  exists 0. split; [vm_compute; reflexivity | apply it_incomplete_complete].
Qed.

Theorem accept_incomplete_dists : it_accept CT_DISTS 1 cnt1.
Proof.
  exists 16384. split; [vm_compute; reflexivity | apply it_incomplete_dists_one].
Qed.

Corollary accept_complete_valid : ValidLengths L11 15%nat.
Proof.
  exact (it_accept_valid CT_LENS 1 cnt11 L11 L11_bound cnt11_counts accept_complete).
Qed.

(** ** 6.  Tie-in to the driver

    The pair really is [it_pre]'s accept test. *)

Definition it_cnt0 (lens : zarr) (codes : Z) : zarr :=
  it_count (Z.to_nat codes) 0 lens zzero.

Definition it_mx (lens : zarr) (codes : Z) : Z :=
  it_findmax 15%nat MAXBITS (it_cnt0 lens codes).

Definition is_preerr (p : ItPre) : bool :=
  match p with PreErr => true | _ => false end.

Lemma is_preerr_false : forall p, is_preerr p = false -> p <> PreErr.
Proof. intros p H E. subst p. cbn in H. discriminate. Qed.

Lemma it_pre_err_iff :
  forall ty lens codes root0 t0,
    it_mx lens codes <> 0 ->
    (it_pre ty lens codes root0 t0 = PreErr
     <-> ~ it_accept ty (it_mx lens codes) (it_cnt0 lens codes)).
Proof.
  intros ty lens codes root0 t0 Hmx.
  unfold it_mx, it_cnt0, it_accept in *.
  unfold it_pre. cbv beta zeta.
  destruct (Z.eqb_spec
    (it_findmax 15%nat MAXBITS (it_count (Z.to_nat codes) 0 lens zzero)) 0)
    as [E|E]; [contradiction|].
  destruct (it_kraft 15%nat 1 1 (it_count (Z.to_nat codes) 0 lens zzero))
    as [lft|] eqn:Hk.
  - destruct (it_incomplete ty lft
      (it_findmax 15%nat MAXBITS (it_count (Z.to_nat codes) 0 lens zzero)))
      eqn:Hi.
    + split.
      * intros _ [l [Hl Hb]]. injection Hl as Heq.
        rewrite <- Heq, Hi in Hb. discriminate.
      * intros _. reflexivity.
    + split.
      * match goal with
        | |- (if ?c then _ else _) = PreErr -> _ => destruct c
        end; intros H; discriminate H.
      * intros Hna. exfalso. apply Hna. exists lft.
        split; [reflexivity | exact Hi].
  - split.
    + intros _ [l [Hl _]]. discriminate Hl.
    + intros _. reflexivity.
Qed.

(** The [mx <> 0] side condition is load-bearing: an all-zero length set
    leaves via [inftrees.c:110]'s [max == 0] arm without ever reaching
    the Kraft check, so [it_pre] is not [PreErr] even though the pair
    rejects.  (This witness doubles as a live demonstration of §1: here
    [it_count] puts 1 in bucket 0 and [it_kraft] still returns [2^15].) *)
Theorem it_pre_err_mx_needed :
  it_mx zzero 1 = 0
  /\ it_cnt0 zzero 1 0 = 1
  /\ it_kraft 15%nat 1 1 (it_cnt0 zzero 1) = Some 32768
  /\ it_pre CT_LENS zzero 1 9 tnone <> PreErr
  /\ ~ it_accept CT_LENS (it_mx zzero 1) (it_cnt0 zzero 1).
Proof.
  split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  split; [vm_compute; reflexivity|].
  split; [apply is_preerr_false; vm_compute; reflexivity|].
  intros [l [Hl Hb]]. vm_compute in Hl. inversion Hl. subst l.
  vm_compute in Hb. discriminate.
Qed.

(** ** 7.  Computational tests

    Each of these is chosen because a plausible WRONG implementation
    fails it; a test no mutant can fail is not written. *)

(** Over-subscription really returns [None].  Catches a transcription (or
    a bridge) that dropped the [left < 0] test. *)
Example kraft_oversubscribed : it_kraft 15%nat 1 1 cnt111 = None.
Proof. vm_compute. reflexivity. Qed.

(** ... and the spec side agrees that this one is invalid, so the test is
    a bridge check and not a bare computation. *)
Example L111_not_valid : ~ ValidLengths L111 15%nat.
Proof. apply valid_lengths_b_false. vm_compute. reflexivity. Qed.

Example kraft_oversubscribed_via_bridge : it_kraft 15%nat 1 1 cnt111 = None.
Proof.
  destruct (it_kraft 15%nat 1 1 cnt111) eqn:E; [exfalso|reflexivity].
  apply L111_not_valid.
  apply (it_kraft_some_iff_valid L111 15%nat cnt111 L111_bound cnt111_counts).
  rewrite E. discriminate.
Qed.

(** The boundary is [<=], not [<]: a code that is EXACTLY complete is
    accepted with residual 0.  Paired with the next test this pins the
    comparison exactly — an off-by-one in either direction fails one of
    the two. *)
Example kraft_exactly_complete : it_kraft 15%nat 1 1 cnt11 = Some 0.
Proof. vm_compute. reflexivity. Qed.

Example kraft_one_over : it_kraft 15%nat 1 1 (zset (zset zzero 1 2) 15 1) = None.
Proof. vm_compute. reflexivity. Qed.

(** The residual value, not just its sign.  Catches an exponent slip
    ([2^14] vs [2^15]) in [itk_left_closed] or in the bridge statement. *)
Example kraft_residual : it_kraft 15%nat 1 1 cnt1 = Some 16384.
Proof. vm_compute. reflexivity. Qed.

(** Bucket 15 IS visited.  Catches both a fuel off-by-one (fuel 14 would
    answer [Some 16384]) and a start-index off-by-one (starting at 0 with
    fuel 15 would miss bucket 15 and answer [Some 32768]). *)
Example kraft_reads_bucket_15 : it_kraft 15%nat 1 1 (zset zzero 15 32768) = Some 0.
Proof. vm_compute. reflexivity. Qed.

Example kraft_bucket_15_can_reject :
  it_kraft 15%nat 1 1 (zset zzero 15 32769) = None.
Proof. vm_compute. reflexivity. Qed.

(** The two mutants that test rules out, spelled out so the claim above is
    itself checked: fuel 14 stops one bucket short, and starting at 0 with
    fuel 15 slides the window off the top. *)
Example kraft_mutant_fuel14 : it_kraft 14%nat 1 1 (zset zzero 15 32768) = Some 16384.
Proof. vm_compute. reflexivity. Qed.

Example kraft_mutant_start0 : it_kraft 15%nat 0 1 (zset zzero 15 32768) = Some 32768.
Proof. vm_compute. reflexivity. Qed.

(** RFC 1951 §3.2.2 in the concrete: [it_count] really does tally unused
    symbols into bucket 0, and the Kraft check is unaffected — all the way
    to [ValidLengths].  Catches a bridge that "helpfully" required
    [cnt 0 = 0]: real [it_count] output does not satisfy it whenever the
    caller's [lens[]] has an unused symbol, which for a DEFLATE literal
    tree is the normal case. *)

Definition Lz : list nat := [0%nat; 0%nat; 1%nat; 1%nat].
Definition cnt_z : zarr := it_count 4%nat 0 (zlist [0; 0; 1; 1]) zzero.

Example zero_lengths_bucket0 : cnt_z 0 = 2.
Proof. vm_compute. reflexivity. Qed.

Lemma zero_lengths_counts : CountsOf cnt_z Lz 15%nat.
Proof. counts15. Qed.

Lemma Lz_bound : forall len, In len Lz -> (len <= 15)%nat.
Proof. apply bound15_of_forallb. reflexivity. Qed.

Lemma zero_lengths_accept : it_accept CT_LENS 1 cnt_z.
Proof.
  exists 0. split; [vm_compute; reflexivity | apply it_incomplete_complete].
Qed.

Theorem zero_lengths_valid : ValidLengths Lz 15%nat.
Proof.
  exact (it_accept_valid CT_LENS 1 cnt_z Lz Lz_bound zero_lengths_counts
                         zero_lengths_accept).
Qed.

(** The general theorem, exercised end to end on that histogram: the
    residual really is [2^15 - kraft_sum]. *)
Example zero_lengths_residual :
  it_kraft 15%nat 1 1 cnt_z
  = Some (2 ^ Z.of_nat 15 - Z.of_nat (kraft_sum Lz 15)).
Proof.
  rewrite (it_kraft_spec Lz 15%nat cnt_z Lz_bound zero_lengths_counts).
  vm_compute. reflexivity.
Qed.

(** ** 8.  Discharging [CountsOf] from real [it_count] output

    §3 states [CountsOf] as a hypothesis and §§3-6 take it as one.  Here it
    is discharged: the histogram [it_count] really builds, at the shape
    [it_pre] really calls it with, satisfies [CountsOf] for the length
    list it was built from ([counts_of_it_count]).  Nothing above is
    weakened -- the hypothesis-carrying forms are kept; what is added is
    the hypothesis-free specialisation, suffixed [_of_lengths].

    The transcription-side half lives in [Inftrees.v] ([zcount],
    [it_count_spec], [zcount_zlens_tail], [zcount_zlens_cons]), stated
    over [zarr]s alone because that file must not import [Huff].  Only the
    last step -- [zcount] over [zlens] is [count_len] -- is here, where
    both sides are in scope, and it is one list induction
    ([zcount_zlens_count_len]) whose step is [zcount_zlens_cons] composed
    with [count_len_cons].

    THE ACCUMULATOR IS PART OF THE STATEMENT.  [it_count] ADDS into [cnt]
    rather than assigning, so the general form keeps the term:
    [it_count_zlens_plus] says [it_count (length l) 0 (zlens l) cnt
    (Z.of_nat b) = cnt (Z.of_nat b) + Z.of_nat (count_len l b)].  That
    [it_pre] passes [zzero] is not assumed but proved -- the first
    conjunct of [it_pre_go_inv] shows every state the driver hands to the
    loop carries exactly [it_count (Z.to_nat codes) 0 lens zzero] in
    [s_count] ([it_pre_counts] is the [CountsOf] form).  And the [cnt b +]
    term is observable: [it_count_accumulator_visible] exhibits a non-zero
    accumulator surviving into the answer, so a bridge that dropped it
    would be refuted here rather than merely unsupported.

    WHAT THE HISTOGRAM DOES NOT SEE.  [counts_of_it_count_agree] reads
    [lens] only on [[0, codes)]; [counts_ignore_beyond_codes] applies it
    to an array LONGER than [codes] and still gets the right histogram.
    The ORDER of the lengths is invisible too -- [count_len_rev]
    proves it -- so no test at this interface can catch a walk that runs
    the list backwards; what pins the direction is the index arithmetic of
    [Inftrees.zcount_zlens_tail].  [histogram_order_blind] states both
    halves: the two [lens] arrays differ, the two histograms do not. *)

(** *** 8.1  [count_occ]'s cons behaviour, in the shape the induction wants *)

Lemma count_len_nil : forall b, count_len [] b = 0%nat.
Proof. reflexivity. Qed.

Lemma count_len_cons :
  forall x l b,
    count_len (x :: l) b
    = (if Nat.eq_dec x b then S (count_len l b) else count_len l b).
Proof.
  intros x l b. unfold count_len. destruct (Nat.eq_dec x b) as [H|H].
  - apply (count_occ_cons_eq Nat.eq_dec l H).
  - apply (count_occ_cons_neq Nat.eq_dec l H).
Qed.

(** *** 8.2  The list induction

    [Inftrees.zcount_zlens_cons] has already done the index arithmetic;
    all that is left is to line its [Z.eqb] up with [count_occ]'s
    decision. *)

Lemma zcount_zlens_count_len :
  forall (l : list nat) (b : nat),
    zcount (length l) 0 (zlens l) (Z.of_nat b) = Z.of_nat (count_len l b).
Proof.
  induction l as [|x l IH]; intros b; [reflexivity|].
  rewrite zcount_zlens_cons, IH, count_len_cons.
  destruct (Nat.eq_dec x b) as [Hx|Hx].
  - subst x. rewrite Z.eqb_refl. lia.
  - replace (Z.of_nat x =? Z.of_nat b) with false
      by (symmetry; apply Z.eqb_neq; lia).
    lia.
Qed.

(** *** 8.3  [it_count] over a length list

    THE ACCUMULATOR IS PART OF THE STATEMENT.  [it_count] adds into [cnt]
    rather than assigning, so the general form carries [cnt (Z.of_nat b) +]. *)

Lemma it_count_zlens_plus :
  forall (l : list nat) (cnt : zarr) (b : nat),
    it_count (length l) 0 (zlens l) cnt (Z.of_nat b)
    = cnt (Z.of_nat b) + Z.of_nat (count_len l b).
Proof.
  intros l cnt b. rewrite it_count_spec, zcount_zlens_count_len. reflexivity.
Qed.

(** At the accumulator [it_pre] actually passes, and at EVERY bucket --
    including bucket 0, which [CountsOf] does not constrain. *)
Lemma it_cnt0_zlens :
  forall (l : list nat) (b : nat),
    it_cnt0 (zlens l) (Z.of_nat (length l)) (Z.of_nat b)
    = Z.of_nat (count_len l b).
Proof.
  intros l b. unfold it_cnt0. rewrite Nat2Z.id, it_count_zlens_plus.
  unfold zzero, zconst. lia.
Qed.

(** THE OBLIGATION, DISCHARGED, at the shape [it_pre] calls [it_count]
    with.  No hypothesis: it holds at every [maxBits]. *)
Theorem counts_of_it_count :
  forall (l : list nat) (maxBits : nat),
    CountsOf (it_cnt0 (zlens l) (Z.of_nat (length l))) l maxBits.
Proof. intros l maxBits b _. apply it_cnt0_zlens. Qed.

(** The same, for a [lens] array that is only KNOWN to agree with the list
    on the live window [[0, codes)] -- which is what a decoder walk holds,
    its [lens] having been filled in from the bit stream.  Outside the
    window [lens] may be anything at all. *)
Theorem counts_of_it_count_agree :
  forall (lens : zarr) (codes : Z) (l : list nat) (maxBits : nat),
    codes = Z.of_nat (length l) ->
    arr_eq_on lens (zlens l) 0 codes ->
    CountsOf (it_cnt0 lens codes) l maxBits.
Proof.
  intros lens codes l maxBits Hcodes Hag b _. subst codes.
  unfold it_cnt0. rewrite it_count_zzero, Nat2Z.id.
  rewrite (zcount_ext (length l) 0 lens (zlens l))
    by (intros j Hj; apply Hag; lia).
  apply zcount_zlens_count_len.
Qed.

(** *** 8.4  The driver really does pass [zzero]

    Not assumed: proved.  Every state [it_pre] hands to the loop carries
    exactly [it_count (Z.to_nat codes) 0 lens zzero] in [s_count], and
    reaching that state means the accept pair held. *)

(** The [s_count] field of a [PreGo] result.  Reading the histogram off
    a [PreGo] equation with [f_equal pre_count] is not decoration: an
    [injection] over the whole eleven-field state record costs ~23 s of
    [coqc] on the (let-inlined) [it_pre] body, and this costs nothing. *)
Definition pre_count (p : ItPre) : zarr :=
  match p with PreGo _ st => s_count st | _ => zzero end.

Lemma it_pre_go_inv :
  forall ty lens codes root0 t0 c st,
    it_pre ty lens codes root0 t0 = PreGo c st ->
    s_count st = it_cnt0 lens codes
    /\ it_mx lens codes <> 0
    /\ it_accept ty (it_mx lens codes) (it_cnt0 lens codes).
Proof.
  intros ty lens codes root0 t0 c st H.
  unfold it_mx, it_cnt0, it_accept.
  unfold it_pre in H. cbv beta zeta in H.
  destruct (Z.eqb_spec
    (it_findmax 15%nat MAXBITS (it_count (Z.to_nat codes) 0 lens zzero)) 0)
    as [E|E]; [discriminate H|].
  destruct (it_kraft 15%nat 1 1 (it_count (Z.to_nat codes) 0 lens zzero))
    as [lft|] eqn:Hk; [|discriminate H].
  destruct (it_incomplete ty lft
    (it_findmax 15%nat MAXBITS (it_count (Z.to_nat codes) 0 lens zzero)))
    eqn:Hi; [discriminate H|].
  match type of H with
  | (if ?c then _ else _) = _ => destruct c
  end; [discriminate H|].
  apply (f_equal pre_count) in H.
  cbv beta iota delta [pre_count s_count] in H.
  split; [now rewrite H|].
  split; [exact E|].
  exists lft. split; first [ reflexivity | assumption ].
Qed.

Corollary it_pre_counts :
  forall ty (l : list nat) root0 t0 c st maxBits,
    it_pre ty (zlens l) (Z.of_nat (length l)) root0 t0 = PreGo c st ->
    CountsOf (s_count st) l maxBits.
Proof.
  intros ty l root0 t0 c st maxBits H.
  destruct (it_pre_go_inv ty (zlens l) (Z.of_nat (length l)) root0 t0 c st H)
    as [Hs _].
  rewrite Hs. apply counts_of_it_count.
Qed.

(** *** 8.5  The headline results with [CountsOf] discharged

    The hypothesis-carrying versions above are NOT replaced: a caller who
    obtains [CountsOf] by another route still wants them.  These are the
    specialisations for a caller who holds only "this is the length list,
    and this is the histogram [it_count] built from it". *)

Theorem it_kraft_spec_of_lengths :
  forall (l : list nat) (maxBits : nat),
    (forall len, In len l -> (len <= maxBits)%nat) ->
    it_kraft maxBits 1 1 (it_cnt0 (zlens l) (Z.of_nat (length l)))
    = (if (kraft_sum l maxBits <=? 2 ^ maxBits)%nat
       then Some (2 ^ Z.of_nat maxBits - Z.of_nat (kraft_sum l maxBits))
       else None).
Proof.
  intros l maxBits Hle.
  exact (it_kraft_spec l maxBits _ Hle (counts_of_it_count l maxBits)).
Qed.

Corollary it_kraft_some_iff_valid_of_lengths :
  forall (l : list nat) (maxBits : nat),
    (forall len, In len l -> (len <= maxBits)%nat) ->
    (it_kraft maxBits 1 1 (it_cnt0 (zlens l) (Z.of_nat (length l))) <> None
     <-> ValidLengths l maxBits).
Proof.
  intros l maxBits Hle.
  exact (it_kraft_some_iff_valid l maxBits _ Hle (counts_of_it_count l maxBits)).
Qed.

Theorem it_accept_valid_of_lengths :
  forall ty mx (l : list nat),
    (forall len, In len l -> (len <= 15)%nat) ->
    it_accept ty mx (it_cnt0 (zlens l) (Z.of_nat (length l))) ->
    ValidLengths l 15%nat.
Proof.
  intros ty mx l Hle Ha.
  exact (it_accept_valid ty mx _ l Hle (counts_of_it_count l 15%nat) Ha).
Qed.

Corollary it_accept_prefix_free_of_lengths :
  forall ty mx (l : list nat),
    (forall len, In len l -> (len <= 15)%nat) ->
    it_accept ty mx (it_cnt0 (zlens l) (Z.of_nat (length l))) ->
    PrefixFreeTable (code_table l 15%nat).
Proof.
  intros ty mx l Hle Ha.
  exact (it_accept_prefix_free ty mx _ l Hle (counts_of_it_count l 15%nat) Ha).
Qed.

Corollary it_accept_codes_prefix_free_of_lengths :
  forall ty mx (l : list nat) s1 s2 cw1 cw2,
    (forall len, In len l -> (len <= 15)%nat) ->
    it_accept ty mx (it_cnt0 (zlens l) (Z.of_nat (length l))) ->
    code_for l 15%nat s1 = Some cw1 ->
    code_for l 15%nat s2 = Some cw2 ->
    s1 <> s2 ->
    is_prefix cw1 cw2 = false.
Proof.
  intros ty mx l s1 s2 cw1 cw2 Hle Ha H1 H2 Hs.
  exact (it_accept_codes_prefix_free ty mx _ l s1 s2 cw1 cw2 Hle
           (counts_of_it_count l 15%nat) Ha H1 H2 Hs).
Qed.

(** The whole chain, from the driver: if [it_pre] handed a state to the
    loop, the length list is prefix-free.  No [CountsOf], no [it_accept]
    -- the [PreGo] is the entire premise beyond the length bound. *)
Corollary it_pre_go_prefix_free :
  forall ty (l : list nat) root0 t0 c st,
    (forall len, In len l -> (len <= 15)%nat) ->
    it_pre ty (zlens l) (Z.of_nat (length l)) root0 t0 = PreGo c st ->
    PrefixFreeTable (code_table l 15%nat).
Proof.
  intros ty l root0 t0 c st Hle H.
  destruct (it_pre_go_inv ty (zlens l) (Z.of_nat (length l)) root0 t0 c st H)
    as [_ [_ Ha]].
  exact (it_accept_prefix_free_of_lengths ty _ l Hle Ha).
Qed.

(** *** 8.6  Tests

    Same rule as §7: each is here because a plausible WRONG implementation
    or a wrong STATEMENT fails it.  Where a mutant is invisible through
    this interface, that invisibility is itself proved rather than
    silently relied on. *)

Definition L311 : list nat := [3%nat; 1%nat; 1%nat].

Lemma L311_bound : forall len, In len L311 -> (len <= 15)%nat.
Proof. apply bound15_of_forallb. reflexivity. Qed.

(** The FIRST symbol is counted.  Catches a walk that starts at index 1,
    or a [zlens] that reads [nth (i+1)] -- both drop the head, and the
    head is the only 3-bit code here. *)
Example counts_first_symbol :
  it_cnt0 (zlens L311) (Z.of_nat (length L311)) 3 = 1.
Proof. vm_compute. reflexivity. Qed.

(** ... and that mutant, spelled out, so the test above is demonstrably
    capable of failing: the same walk started one index up answers 0. *)
Example counts_first_symbol_shift_mutant :
  it_count (length L311) 1 (zlens L311) zzero 3 = 0.
Proof. vm_compute. reflexivity. Qed.

(** THE [+ ACCUMULATOR] DETAIL, checked rather than assumed.  A non-zero
    accumulator survives into the answer (7 = 5 + 2), so a bridge that
    stated [it_count ... cnt b = Z.of_nat (count_len l b)] -- dropping the
    [cnt b +] -- would be refuted here, not merely unsupported.  The
    second conjunct is the same walk at [zzero], which is what [it_pre]
    passes ([it_pre_go_inv]); an [it_count] that ASSIGNED instead of
    adding would answer 1 there, since [L11] repeats a length. *)
Example it_count_accumulator_visible :
  it_count (length L11) 0 (zlens L11) (zset zzero 1 5) (Z.of_nat 1%nat) = 7
  /\ it_count (length L11) 0 (zlens L11) zzero (Z.of_nat 1%nat) = 2.
Proof. split; vm_compute; reflexivity. Qed.

(** The general statement reproduces both numbers, so the test is a check
    on [it_count_zlens_plus] and not a bare computation. *)
Example it_count_accumulator_via_lemma :
  it_count (length L11) 0 (zlens L11) (zset zzero 1 5) (Z.of_nat 1%nat)
  = zset zzero 1 5 (Z.of_nat 1%nat) + Z.of_nat (count_len L11 1).
Proof. apply it_count_zlens_plus. Qed.

(** The §5 histograms really ARE [it_count] output: what used to be a
    satisfiable hypothesis is now the genuine article.  Second conjunct
    pins the value computationally. *)
Example cnt11_is_it_count :
  (forall b : nat, (1 <= b <= 15)%nat ->
     it_cnt0 (zlens L11) (Z.of_nat (length L11)) (Z.of_nat b) = cnt11 (Z.of_nat b))
  /\ it_cnt0 (zlens L11) (Z.of_nat (length L11)) 1 = 2.
Proof.
  split; [|vm_compute; reflexivity].
  intros b Hb. rewrite (counts_of_it_count L11 15%nat b Hb).
  symmetry. exact (cnt11_counts b Hb).
Qed.

(** OUT-OF-WINDOW [lens] ENTRIES ARE INVISIBLE.  [counts_of_it_count_agree]
    asks for agreement on [[0, codes)] only -- which is exactly what a
    caller whose array is LONGER than [codes] needs: take [l] to be the
    live prefix and the tail cannot matter.  Here the array carries a
    3-bit code at index 2 that [codes = 2] excludes, and the histogram is
    still [L11]'s.  The first conjunct pins that the excluded entry really
    does disagree, without which the second would be vacuous.  This test
    fails if the window is ever widened; the lemma's own proof is what
    stops it being narrowed. *)
Definition lens_long : zarr := zlens [1%nat; 1%nat; 3%nat].

Lemma counts_ignore_beyond_codes :
  lens_long 2 <> zlens L11 2
  /\ CountsOf (it_cnt0 lens_long (Z.of_nat (length L11))) L11 15%nat.
Proof.
  split; [vm_compute; discriminate|].
  apply (counts_of_it_count_agree _ _ L11 15%nat eq_refl).
  intros j Hj. cbn in Hj.
  assert (Hj' : j = 0 \/ j = 1) by lia.
  destruct Hj' as [Hj0 | Hj0]; subst j; vm_compute; reflexivity.
Qed.

(** ORDER IS UNOBSERVABLE HERE, AND THAT IS A THEOREM.  A walk that ran
    the list backwards would produce the same histogram, so no [CountsOf]
    test can catch one; what pins the direction is the index arithmetic of
    [Inftrees.zcount_zlens_tail], not anything visible through this
    interface. *)
Lemma count_len_rev :
  forall (l : list nat) (b : nat), count_len (rev l) b = count_len l b.
Proof.
  induction l as [|x l IH]; intros b; [reflexivity|].
  cbn [rev]. rewrite count_len_app, IH, !count_len_cons, count_len_nil.
  destruct (Nat.eq_dec x b); lia.
Qed.

(** Both halves of that claim: the two [lens] arrays genuinely differ, the
    two histograms genuinely do not. *)
Example histogram_order_blind :
  zlens L311 0 <> zlens (rev L311) 0
  /\ (forall b : nat,
        it_cnt0 (zlens L311) (Z.of_nat (length L311)) (Z.of_nat b)
        = it_cnt0 (zlens (rev L311)) (Z.of_nat (length (rev L311))) (Z.of_nat b)).
Proof.
  split; [vm_compute; discriminate|].
  intros b. rewrite !it_cnt0_zlens, count_len_rev. reflexivity.
Qed.

(** *** 8.7  The chain end to end, with nothing assumed

    [it_pre] is run on a real length list; it reaches the loop; therefore
    the code is prefix-free.  No [CountsOf], no [it_accept], no histogram
    supplied by hand -- and it is not vacuous, because the [PreGo] is
    discharged by computation. *)

Definition is_prego (p : ItPre) : bool :=
  match p with PreGo _ _ => true | _ => false end.

Lemma it_pre_L11_prego :
  is_prego (it_pre CT_LENS (zlens L11) (Z.of_nat (length L11)) 9 tnone) = true.
Proof. vm_compute. reflexivity. Qed.

Theorem L11_prefix_free_via_driver : PrefixFreeTable (code_table L11 15%nat).
Proof.
  destruct (it_pre CT_LENS (zlens L11) (Z.of_nat (length L11)) 9 tnone)
    as [ | t | | c st ] eqn:E;
    try (exfalso; pose proof it_pre_L11_prego as Hg; rewrite E in Hg;
         cbv in Hg; discriminate Hg).
  exact (it_pre_go_prefix_free CT_LENS L11 9 tnone c st L11_bound E).
Qed.
