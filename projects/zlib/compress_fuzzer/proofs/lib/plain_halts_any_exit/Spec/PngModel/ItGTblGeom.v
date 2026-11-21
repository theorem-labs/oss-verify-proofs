(** * OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel.ItGTblGeom — unit-interval geometry of the reversed position, and the
      Kraft mass.  Layer 2 of the root-region COVERAGE development
      ([ItGTblRev.v] is layer 1: [zrev] and the increment law; the loop lives
      in [ItGTblCover.v]).

    GTBL-ARMS lane, 2026-08-18.  Scratch tree
    a working folder (a COPY of gtblarms' spec + [ItGTblRev];
    nothing here writes into that lane).

    WHAT THIS FILE IS FOR.  [inflate_table]'s build loop advances a scaled
    POSITION [P] at the MAXBITS scale [2^15]: one trip writes the Huffman code
    of length [L] whose bit-reversal is [huff], and advances

        P  :=  zrev L huff * 2 ^ (15 - L)   -->   P + 2 ^ (15 - L).

    A root-table index [j] owns the "unit interval"

        [ zrev root j * 2 ^ (15 - root) , (zrev root j + 1) * 2 ^ (15 - root) )

    and the coverage invariant is "every unit entirely below [P] is written".
    §2 supplies the only two facts about that geometry the loop needs: when a
    trip completes a NEW unit, the completed unit's index is determined — it is
    the current code's write class ([L <= root]) or the current code's own root
    prefix ([root < L]).  §3 is the Kraft bookkeeping that says the per-trip
    advance [2 ^ (15 - L)] is exactly what [it_kraft] debits, so the total
    advance over a complete code set is [2 ^ 15].

    ONE MODEL ONLY.  This chain imports [Base] and [Inftrees] and nothing else
    from the spec tree: it is deliberately independent of the repo's other
    formalization, and facts wanted from there are re-derived.  Likewise [it_mass]
    below is the same function as [itk_sum] in the graded tree's
    [Spec/PngModel/InftreesBridge.v]:197-229 and is re-derived on purpose.

    THE [15] IS [MAXBITS] AND IS NOT A PARAMETER.  Every consumer is at that
    scale; generalising it would only move the [15 - L >= 0] side conditions to
    the call sites.

    HOUSE RULES OBSERVED HERE.  (a) Cancellation of a positive factor is NOT
    linear arithmetic, so §1 names the three monotonicity steps [lia] cannot
    take; everything else in this file is [lia] over MONOMIALS (micromega ring-
    normalises, so [(c+1)*S] and [c*S + S] are the same goal to it — that is
    what keeps §2 short).  (b) [cbn] is always given an explicit constant list:
    unrestricted [cbn] unfolds [Z.le] and turns a [lia] goal into "Cannot find
    witness".  (c) Nat numerals are constructor applications, so lemmas keyed
    on [S k] are applied with EXPLICIT arguments. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Base Inftrees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import ItGTblRev.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache. Open Scope Z_scope.

(** ** 1.  The three non-linear steps

    [lia] ring-normalises, so it can compare [(c+1)*S] with [c*S + S]; what it
    cannot do is DIVIDE, i.e. go from [a * s < b * s] to [a < b].  Naming the
    three cancellation/monotonicity steps once means §2 never has to think
    about it again. *)

Lemma mul_lt_cancel_r : forall a b s : Z, 0 < s -> a * s < b * s -> a < b.
Proof.
  intros a b s Hs H.
  destruct (Z.lt_ge_cases a b) as [Hlt|Hge]; [exact Hlt|].
  exfalso.
  assert (Hm : b * s <= a * s) by (apply Z.mul_le_mono_nonneg_r; lia).
  lia.
Qed.

Lemma mul_le_cancel_r : forall a b s : Z, 0 < s -> a * s <= b * s -> a <= b.
Proof.
  intros a b s Hs H.
  destruct (Z.le_gt_cases a b) as [Hle|Hgt]; [exact Hle|].
  exfalso.
  assert (Hm : (b + 1) * s <= a * s) by (apply Z.mul_le_mono_nonneg_r; lia).
  lia.
Qed.

Lemma mul_lt_mono_r' : forall a b s : Z, 0 < s -> a < b -> a * s < b * s.
Proof.
  intros a b s Hs H.
  assert (Hm : (a + 1) * s <= b * s) by (apply Z.mul_le_mono_nonneg_r; lia).
  lia.
Qed.

(** ** 2a.  Reversal is an involution, hence injective

    [zrev_zrev] is the only genuinely inductive fact added here; both
    unit-crossing lemmas end with [zrev_inj], which is its one-line corollary. *)

Lemma zrev_zrev : forall n h, 0 <= h < 2 ^ Z.of_nat n -> zrev n (zrev n h) = h.
Proof.
  induction n as [|k IH]; intros h Hh.
  - change (Z.of_nat 0) with 0 in Hh. rewrite Z.pow_0_r in Hh.
    assert (h = 0) by lia. subst h. reflexivity.
  - pose proof (pow2_pos_nat k) as Hp.
    assert (Hd : 0 <= Z.div2 h < 2 ^ Z.of_nat k).
    { rewrite pow2_succ_nat in Hh. rewrite Z.div2_div. split.
      - apply Z.div_pos; lia.
      - apply Z.div_lt_upper_bound; lia. }
    assert (Ha : 0 <= zrev k (Z.div2 h) < 2 ^ Z.of_nat k).
    { pose proof (zrev_nonneg k (Z.div2 h)). pose proof (zrev_lt k (Z.div2 h)). lia. }
    (* Rewrite the INNER application into split form.  The pattern
       [zrev (S k) h] occurs exactly once in [zrev (S k) (zrev (S k) h)] — the
       outer application is not an instance of it — so this rewrite is
       unambiguous without an occurrence selector. *)
    assert (Hinner : zrev (S k) h
                     = zrev k (Z.div2 h) + (if Z.odd h then 1 else 0) * 2 ^ Z.of_nat k).
    { cbn [zrev]. destruct (Z.odd h); ring. }
    rewrite Hinner.
    (* [S k] and [k + 1] are convertible but not syntactically equal, and
       [zrev_split] is stated at [k + d]. *)
    replace (S k) with (k + 1)%nat by lia.
    rewrite (zrev_split k 1 (zrev k (Z.div2 h)) (if Z.odd h then 1 else 0) Ha).
    rewrite (IH (Z.div2 h) Hd).
    assert (Hz1 : zrev 1 (if Z.odd h then 1 else 0) = (if Z.odd h then 1 else 0))
      by (destruct (Z.odd h); reflexivity).
    rewrite Hz1, pow2_one.
    rewrite (Z.div2_odd h) at 3.
    destruct (Z.odd h); cbn [Z.b2z]; lia.
Qed.

Lemma zrev_inj : forall n a b,
  0 <= a < 2 ^ Z.of_nat n -> 0 <= b < 2 ^ Z.of_nat n ->
  zrev n a = zrev n b -> a = b.
Proof.
  intros n a b Ha Hb H.
  pose proof (zrev_zrev n a Ha) as Ea.
  pose proof (zrev_zrev n b Hb) as Eb.
  rewrite H in Ea. rewrite Ea in Eb. exact Eb.
Qed.

(** Widening the reversal width scales the value: the reversed code of a short
    code, read at a longer width, is the short reversal times [2 ^ D].  This is
    exactly "a code of length [L] is the prefix class of all length-[L+D]
    extensions". *)
Lemma zrev_widen : forall (L D : nat) (h : Z),
  0 <= h < 2 ^ Z.of_nat L -> zrev (L + D) h = zrev L h * 2 ^ Z.of_nat D.
Proof.
  intros L D h Hh.
  pose proof (zrev_split L D h 0 Hh) as HS.
  rewrite zrev_zero in HS.
  replace (h + 0 * 2 ^ Z.of_nat L) with h in HS by ring.
  lia.
Qed.

(** ** 2b.  The two unit-crossing lemmas

    Both take the same pair of hypotheses about the current position
    [P = zrev L huff * 2 ^ (15 - L)] and the unit of root index [j]:

      [P < (zrev R j + 1) * 2 ^ (15 - R)]                  (unit not yet done)
      [(zrev R j + 1) * 2 ^ (15 - R) <= P + 2 ^ (15 - L)]   (done after one step)

    and conclude that [j] is determined by [huff].  They differ only in which
    of [L], [R] is the larger width.

    PREMISES.  [(1 <= L)] in the short lemma and [(1 <= R)] in the long one are
    NOT used — both proofs go through verbatim without them (machine-checked;
    the degenerate width 0 has [2 ^ 0 = 1], so the conclusion is [0 = 0]).  They
    are kept because they are the requested interface and a caller has them for
    free; a caller need not work to discharge them.  What IS load-bearing is
    [(R <= 15)] / [(L <= 15)]: without it [15 - width] goes negative, [Z.pow]
    returns 0, and the exponent split [2 ^ (15-L) = 2 ^ (15-R) * 2 ^ D] fails.

    HOW MANY UNITS A TRIP COMPLETES.  In the SHORT case the step [2 ^ (15-L)] is
    [2 ^ (R-L)] root units, so [2 ^ (R-L)] indices [j] satisfy the hypotheses at
    once — and the conclusion [j mod 2 ^ L = huff] holds for all of them, which
    is exactly the code's write class.  In the LONG case the step is at most one
    root unit, so at most one [j] qualifies.  Neither lemma pins [j] itself in
    the short case; it pins the class. *)

(** SHORT CODES ([L <= R]): the newly completed unit lies in the write class of
    the current code, i.e. its low [L] bits are [huff]. *)
Lemma unit_cross_short : forall (R L : nat) (huff j : Z),
  (1 <= L)%nat -> (L <= R)%nat -> (R <= 15)%nat ->
  0 <= huff < 2 ^ Z.of_nat L ->
  0 <= j < 2 ^ Z.of_nat R ->
  zrev L huff * 2 ^ (15 - Z.of_nat L) < (zrev R j + 1) * 2 ^ (15 - Z.of_nat R) ->
  (zrev R j + 1) * 2 ^ (15 - Z.of_nat R)
    <= zrev L huff * 2 ^ (15 - Z.of_nat L) + 2 ^ (15 - Z.of_nat L) ->
  j mod 2 ^ Z.of_nat L = huff.
Proof.
  intros R L huff j HL1 HLR HR15 Hhuff Hj H1 H2.
  assert (HDex : exists D, (L + D = R)%nat) by (exists (R - L)%nat; lia).
  destruct HDex as [D HLD].
  assert (HZD : Z.of_nat D = Z.of_nat R - Z.of_nat L) by lia.
  pose proof (pow2_pos_nat D) as HpD.
  pose proof (pow2_pos_nat L) as HpL.
  assert (HSpos : 0 < 2 ^ (15 - Z.of_nat R)) by (apply Z.pow_pos_nonneg; lia).
  (* the short code's advance is [2 ^ D] units of the root scale *)
  assert (Hexp : 2 ^ (15 - Z.of_nat L) = 2 ^ (15 - Z.of_nat R) * 2 ^ Z.of_nat D).
  { rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  rewrite Hexp in H1, H2.
  (* Divide both hypotheses by the root scale: the reversed root index sits in
     the half-open block of the reversed code. *)
  assert (Hlo : zrev L huff * 2 ^ Z.of_nat D <= zrev R j).
  { assert (Hx : zrev L huff * 2 ^ Z.of_nat D * 2 ^ (15 - Z.of_nat R)
                 < (zrev R j + 1) * 2 ^ (15 - Z.of_nat R)) by lia.
    pose proof (mul_lt_cancel_r _ _ _ HSpos Hx). lia. }
  assert (Hhi : zrev R j < (zrev L huff + 1) * 2 ^ Z.of_nat D).
  { assert (Hx : (zrev R j + 1) * 2 ^ (15 - Z.of_nat R)
                 <= (zrev L huff + 1) * 2 ^ Z.of_nat D * 2 ^ (15 - Z.of_nat R)) by lia.
    pose proof (mul_le_cancel_r _ _ _ HSpos Hx). lia. }
  (* Split [j] at bit [L] and reverse: the low part reverses to the HIGH part
     of [zrev R j], which is the block index just bounded. *)
  set (a := j mod 2 ^ Z.of_nat L).
  set (b := j / 2 ^ Z.of_nat L).
  assert (Ha : 0 <= a < 2 ^ Z.of_nat L)
    by (unfold a; apply Z.mod_pos_bound; lia).
  assert (Hjab : j = a + b * 2 ^ Z.of_nat L).
  { unfold a, b. pose proof (Z.div_mod j (2 ^ Z.of_nat L) ltac:(lia)) as Hdm. lia. }
  assert (Hsplit : zrev R j = zrev L a * 2 ^ Z.of_nat D + zrev D b).
  { rewrite <- HLD. rewrite Hjab. apply (zrev_split L D a b Ha). }
  pose proof (zrev_nonneg D b) as Hb0.
  pose proof (zrev_lt D b) as HbU.
  assert (Heq : zrev L a = zrev L huff).
  { assert (H3 : zrev L huff * 2 ^ Z.of_nat D < (zrev L a + 1) * 2 ^ Z.of_nat D) by lia.
    assert (H4 : zrev L a * 2 ^ Z.of_nat D < (zrev L huff + 1) * 2 ^ Z.of_nat D) by lia.
    pose proof (mul_lt_cancel_r _ _ _ HpD H3).
    pose proof (mul_lt_cancel_r _ _ _ HpD H4).
    lia. }
  exact (zrev_inj L a huff Ha Hhuff Heq).
Qed.

(** LONG CODES ([R < L]): the newly completed unit is the current code's own
    root prefix, i.e. [huff]'s low [R] bits. *)
Lemma unit_cross_long : forall (R L : nat) (huff j : Z),
  (1 <= R)%nat -> (R < L)%nat -> (L <= 15)%nat ->
  0 <= huff < 2 ^ Z.of_nat L ->
  0 <= j < 2 ^ Z.of_nat R ->
  zrev L huff * 2 ^ (15 - Z.of_nat L) < (zrev R j + 1) * 2 ^ (15 - Z.of_nat R) ->
  (zrev R j + 1) * 2 ^ (15 - Z.of_nat R)
    <= zrev L huff * 2 ^ (15 - Z.of_nat L) + 2 ^ (15 - Z.of_nat L) ->
  j = huff mod 2 ^ Z.of_nat R.
Proof.
  intros R L huff j HR1 HRL HL15 Hhuff Hj H1 H2.
  assert (HDex : exists D, (R + D = L)%nat) by (exists (L - R)%nat; lia).
  destruct HDex as [D HRD].
  assert (HZD : Z.of_nat D = Z.of_nat L - Z.of_nat R) by lia.
  pose proof (pow2_pos_nat D) as HpD.
  pose proof (pow2_pos_nat R) as HpR.
  assert (HTpos : 0 < 2 ^ (15 - Z.of_nat L)) by (apply Z.pow_pos_nonneg; lia).
  assert (HSpos : 0 < 2 ^ (15 - Z.of_nat R)) by (apply Z.pow_pos_nonneg; lia).
  assert (HTS : 2 ^ (15 - Z.of_nat L) <= 2 ^ (15 - Z.of_nat R))
    by (apply Z.pow_le_mono_r; lia).
  (* [2 ^ D] long-code steps make up one root unit *)
  assert (Hexp : 2 ^ Z.of_nat D * 2 ^ (15 - Z.of_nat L) = 2 ^ (15 - Z.of_nat R)).
  { rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  (* Split [huff] at bit [R]: its low [R] bits reverse to the HIGH part of
     [zrev L huff], which is the root prefix. *)
  set (low := huff mod 2 ^ Z.of_nat R).
  set (q := huff / 2 ^ Z.of_nat R).
  assert (Hlow : 0 <= low < 2 ^ Z.of_nat R)
    by (unfold low; apply Z.mod_pos_bound; lia).
  assert (Hhsplit : huff = low + q * 2 ^ Z.of_nat R).
  { unfold low, q. pose proof (Z.div_mod huff (2 ^ Z.of_nat R) ltac:(lia)) as Hdm. lia. }
  assert (Hrev : zrev L huff = zrev R low * 2 ^ Z.of_nat D + zrev D q).
  { rewrite <- HRD. rewrite Hhsplit. apply (zrev_split R D low q Hlow). }
  pose proof (zrev_nonneg D q) as Hq0.
  pose proof (zrev_lt D q) as HqU.
  assert (Hnn : 0 <= zrev D q * 2 ^ (15 - Z.of_nat L))
    by (apply Z.mul_nonneg_nonneg; lia).
  assert (Hlt : zrev D q * 2 ^ (15 - Z.of_nat L)
                < 2 ^ Z.of_nat D * 2 ^ (15 - Z.of_nat L))
    by (apply mul_lt_mono_r'; lia).
  (* The position sits inside the root unit of [zrev R low]. *)
  assert (Hplo : zrev R low * 2 ^ (15 - Z.of_nat R)
                 <= zrev L huff * 2 ^ (15 - Z.of_nat L)).
  { rewrite Hrev, <- Hexp. lia. }
  assert (Hphi : zrev L huff * 2 ^ (15 - Z.of_nat L)
                 < (zrev R low + 1) * 2 ^ (15 - Z.of_nat R)).
  { rewrite Hrev, <- Hexp. lia. }
  (* Squeeze the reversed root index between the same two bounds. *)
  assert (Hu1 : zrev R low <= zrev R j).
  { assert (Hx : zrev R low * 2 ^ (15 - Z.of_nat R)
                 < (zrev R j + 1) * 2 ^ (15 - Z.of_nat R)) by lia.
    pose proof (mul_lt_cancel_r _ _ _ HSpos Hx). lia. }
  assert (Hu2 : zrev R j <= zrev R low).
  { assert (Hx : (zrev R j + 1) * 2 ^ (15 - Z.of_nat R)
                 < (zrev R low + 2) * 2 ^ (15 - Z.of_nat R)) by lia.
    pose proof (mul_lt_cancel_r _ _ _ HSpos Hx). lia. }
  assert (Heq : zrev R j = zrev R low) by lia.
  exact (zrev_inj R j low Hj Hlow Heq).
Qed.

(** Coverage of a unit is monotone in the position.  Trivial, but named so the
    call site never has to name the root scale. *)
Lemma unit_le_of_lt : forall (R : nat) (j P Q : Z),
  P <= Q -> (zrev R j + 1) * 2 ^ (15 - Z.of_nat R) <= P ->
  (zrev R j + 1) * 2 ^ (15 - Z.of_nat R) <= Q.
Proof. intros R j P Q HPQ H. lia. Qed.

(** ** 3.  The Kraft mass

    [it_mass n len cnt = sum_{i=0}^{n-1} cnt (len + i) * 2 ^ (n - 1 - i)]; at
    [n = 15, len = 1] this is [sum_{l=1..15} cnt l * 2 ^ (15 - l)], the scaled
    total advance of a code set.  Same function as [itk_sum] in the graded
    tree's [Spec/PngModel/InftreesBridge.v]:197-229; re-derived here to keep
    this chain at three spec files (see the header). *)

Fixpoint it_mass (n : nat) (len : Z) (cnt : zarr) : Z :=
  match n with
  | O => 0
  | S k => cnt len * 2 ^ Z.of_nat k + it_mass k (len + 1) cnt
  end.

Lemma it_mass_ext : forall n len a b,
  (forall j, len <= j < len + Z.of_nat n -> a j = b j) ->
  it_mass n len a = it_mass n len b.
Proof.
  induction n as [|k IH]; intros len a b H; [reflexivity|].
  cbn [it_mass].
  rewrite (H len) by lia.
  f_equal. apply IH. intros j Hj. apply H. lia.
Qed.

(** One decrement of [cnt l] removes exactly the weight [2 ^ (len+n-1-l)] —
    at [n = 15, len = 1] the [2 ^ (15 - l)] the build loop advances per trip.

    THE RANGE PREMISE IS REAL, and at [n = 15, len = 1] it is [1 <= l <= 15].
    [Inftrees.v]:131-138 warns that [it_findmin 16%nat] can return 16; that
    would put [s_len] outside this range and make the lemma inapplicable.  It
    cannot happen at a real call site because [mn <= mx = it_findmax 15 MAXBITS
    ... <= 15], but a consumer carrying only [1 <= s_len] must ALSO carry
    [s_len <= 15] to use this lemma. *)
Lemma it_mass_dec : forall n len cnt l,
  len <= l < len + Z.of_nat n ->
  it_mass n len (zset cnt l (cnt l - 1))
  = it_mass n len cnt - 2 ^ (len + Z.of_nat n - 1 - l).
Proof.
  induction n as [|k IH]; intros len cnt l Hl.
  - exfalso. change (Z.of_nat 0) with 0 in Hl. lia.
  - destruct (Z.eq_dec l len) as [Heq|Hne].
    + subst l. cbn [it_mass]. rewrite zset_same.
      rewrite (it_mass_ext k (len + 1) (zset cnt len (cnt len - 1)) cnt)
        by (intros j Hj; apply zset_other; lia).
      replace (len + Z.of_nat (S k) - 1 - len) with (Z.of_nat k) by lia.
      lia.
    + cbn [it_mass]. rewrite (zset_other cnt l (cnt l - 1) len) by lia.
      rewrite (IH (len + 1) cnt l) by lia.
      replace (len + 1 + Z.of_nat k - 1 - l)
        with (len + Z.of_nat (S k) - 1 - l) by lia.
      lia.
Qed.

Lemma it_mass_zero_on : forall n len cnt,
  (forall j, len <= j < len + Z.of_nat n -> cnt j = 0) ->
  it_mass n len cnt = 0.
Proof.
  induction n as [|k IH]; intros len cnt H; [reflexivity|].
  cbn [it_mass].
  rewrite (H len) by lia.
  rewrite (IH (len + 1) cnt) by (intros j Hj; apply H; lia).
  ring.
Qed.

Lemma it_mass_nonneg : forall n len cnt,
  (forall j, len <= j < len + Z.of_nat n -> 0 <= cnt j) ->
  0 <= it_mass n len cnt.
Proof.
  induction n as [|k IH]; intros len cnt H; cbn [it_mass]; [lia|].
  assert (H0 : 0 <= cnt len) by (apply H; lia).
  pose proof (pow2_pos_nat k).
  assert (Hm : 0 <= cnt len * 2 ^ Z.of_nat k) by (apply Z.mul_nonneg_nonneg; lia).
  assert (Ht : 0 <= it_mass k (len + 1) cnt) by (apply IH; intros j Hj; apply H; lia).
  lia.
Qed.

(** THE KRAFT LINK.  [it_kraft] is [inflate_table]'s over-subscription counter;
    when it survives ([Some]) its residual is the scaled slack.  No
    nonnegativity premise is needed in THIS direction: the [None] branch is
    excluded by the hypothesis, and the residual identity is an unconditional
    consequence of the recursion. *)
Lemma it_kraft_mass : forall n len left cnt lft,
  it_kraft n len left cnt = Some lft ->
  lft = left * 2 ^ Z.of_nat n - it_mass n len cnt.
Proof.
  induction n as [|k IH]; intros len left cnt lft H.
  - cbn [it_kraft it_mass] in H |- *.
    injection H as H. change (Z.of_nat 0) with 0. rewrite Z.pow_0_r. lia.
  - cbn [it_kraft it_mass] in H |- *.
    (* A [let] in the definition hides the scrutinee from [destruct]. *)
    cbv zeta in H.
    destruct (Z.ltb_spec (left * 2 - cnt len) 0) as [Hneg|Hpos]; [discriminate|].
    specialize (IH (len + 1) (left * 2 - cnt len) cnt lft H).
    rewrite pow2_succ_nat. lia.
Qed.

(** ** 4.  Two ADDITIONS (not on the requested interface — delete if unwanted)

    [it_kraft]'s [Some] already carries nonnegativity of the residual for
    [n >= 1], because the LAST recursive call is the one that returned, and it
    only returned after its own [< 0] check.  (At [n = 0] there is no check and
    [lft = left] is whatever the caller passed, hence the [1 <= n].)  Every real
    call site is [it_kraft 15 1 1 cnt0], so this is free there, and it is what
    turns [it_kraft_mass] into the UPPER bound "the build loop's total advance
    never exceeds [2 ^ 15]" — the fact that makes the position invariant
    well-founded.  Deriving it after the fact costs a second induction, so it
    is done here. *)

Lemma it_kraft_nonneg : forall n len left cnt lft,
  (1 <= n)%nat -> it_kraft n len left cnt = Some lft -> 0 <= lft.
Proof.
  induction n as [|k IH]; intros len left cnt lft Hn H; [lia|].
  cbn [it_kraft] in H. cbv zeta in H.
  destruct (Z.ltb_spec (left * 2 - cnt len) 0) as [Hneg|Hpos]; [discriminate|].
  destruct k as [|k'].
  - cbn [it_kraft] in H. injection H as H. lia.
  - exact (IH (len + 1) (left * 2 - cnt len) cnt lft ltac:(lia) H).
Qed.

Lemma it_mass_upper : forall n len left cnt lft,
  (1 <= n)%nat -> it_kraft n len left cnt = Some lft ->
  it_mass n len cnt <= left * 2 ^ Z.of_nat n.
Proof.
  intros n len left cnt lft Hn H.
  pose proof (it_kraft_mass n len left cnt lft H).
  pose proof (it_kraft_nonneg n len left cnt lft Hn H).
  lia.
Qed.

Set Printing Depth 10000000000.
Print Assumptions mul_lt_cancel_r.
Print Assumptions mul_le_cancel_r.
Print Assumptions mul_lt_mono_r'.
Print Assumptions zrev_zrev.
Print Assumptions zrev_inj.
Print Assumptions zrev_widen.
Print Assumptions unit_cross_short.
Print Assumptions unit_cross_long.
Print Assumptions unit_le_of_lt.
Print Assumptions it_mass_ext.
Print Assumptions it_mass_dec.
Print Assumptions it_mass_zero_on.
Print Assumptions it_mass_nonneg.
Print Assumptions it_kraft_mass.
Print Assumptions it_kraft_nonneg.
Print Assumptions it_mass_upper.
