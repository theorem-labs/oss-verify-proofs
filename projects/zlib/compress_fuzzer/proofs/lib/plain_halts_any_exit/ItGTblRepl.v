(** * OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.ItGTblRepl — ROOT-TABLE REPLICATION for [inflate_table], for
      huffman-id's obligation (b).

    A NEW FILE ON PURPOSE.  [ItGTblCover.v] is now IN the graded tree, so any
    change to it is a REPLACEMENT rather than an addition — the cheap dual-[-Q]
    verification stops applying and the simulated post-landing tree becomes
    mandatory.  Everything here is therefore additive: nothing in Cover is
    touched, and this file only consumes its exports.

    ** WHAT IS BEING PROVED, AND WHY THE OBVIOUS STATEMENT IS FALSE

    huffman-id's fetch loop needs: two root indices that agree on their low [k]
    bits, one of which carries a code no longer than [k], must carry the SAME code
    length.  That converts the loop's pull guard into a bound on the returned
    entry, and it is the one step of their derivation they cannot supply.

    Their first statement of it was FALSE, and the counterexample is kept here
    because it is what fixes the premise set.  Take [root = 2] and a single symbol
    of length 1:

      the fill loop writes {0, 2} with [c_bits = 1]   (the residue class mod 2)
      [it_finish] writes index 1 with [c_bits = 1]
      index 3 is NEVER WRITTEN, so [c_bits = 0]

    At [i = 1] the modulus is [2 ^ c_bits (t 1) = 2], and [3 mod 2 = 1 mod 2], so
    replication demands [c_bits (t 3) = 1].  It is 0.

    That configuration is UNREACHABLE, and the reason is the premise the theorem
    has to carry:
      [it_incomplete ty lft mx = (0 <? lft) && ((ty =? CT_CODES) || negb (mx =? 1))]
      (Inftrees.v:174-175), so an accepted code is either COMPLETE ([lft = 0]) or
      has [mx = 1]; and on the [mx = 1] branch the clamp forces [root = 1]
      ([r1 = min mx root0 = 1], and [mn <= mx = 1] so [r = max r1 mn = 1]), giving
      a two-entry table whose both entries carry [c_bits = 1].
    So replication holds exactly on the accepted arms and fails one step outside
    them — which means the eventual theorem takes the same premises as
    [it_covers_root_pos], and costs the consumer nothing new at its call site.

    ** STATUS OF THIS FILE — READ BEFORE CONSUMING

    LANDED HERE: the two statements; the reduction between them (so only the
    strong one has to be established by the loop); the ARITHMETIC CORE — that the
    set of indices the fill loop touches IS exactly a residue class, which is the
    whole reason replication is true rather than an accident; and the [it_fill]
    hit/miss pair the core is spent on.

    ALSO LANDED: class DISJOINTNESS, reduced as an IFF to a single arithmetic
    condition — two classes at widths [L1 <= L2] are disjoint exactly when
    [h2 mod 2 ^ L1 <> h1], i.e. exactly when the shorter code is not a prefix of
    the longer.  The equal-length case falls out with no prefix reasoning at all.

    AND PREFIX-FREENESS, which the first version of this header listed as the one
    remaining fact: [prefix_free_of_positions] derives it from the interval
    geometry, and [classes_disjoint_of_positions] joins the two — a later trip
    whose position has passed an earlier code's interval END cannot touch that
    code's class.  It cost two lemmas that were already in the layer
    ([zrev_split], [zrev_lt]), so pricing it as new work was another over-estimate.
    [prefix_free_of_pos_z] is the SUBTRACTIVE restatement in [ItGTblCover]'s own
    vocabulary, because the additive form is right for the proof and wrong for
    every caller — publishing only the shape that was convenient to prove would
    leave the result in a form nobody holds.

    NOT HERE: the LOOP INVARIANT itself — riding the above round [it_loop]'s
    fixpoint, which means carrying "every root index below the current position has
    a uniformly-written class" as an achieved-plus-preserved pair and discharging
    the position-ordering hypothesis of [classes_disjoint_of_positions] from the
    loop's own monotonicity.  That is now bookkeeping over proved parts rather than
    an argument of unknown size, but it is NOT DONE, and nothing in this file
    asserts it or implies it has been.

    The two Props are definitions a consumer instantiates, so each is accompanied
    by a POSITIVE INSTANCE: a [Definition] of a [Prop] typechecks whether or not
    it is satisfiable, and a relation published for someone else to instantiate
    needs an exhibited witness rather than a plausibility argument.

    GTBL-ARMS, 2026-08-18. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Base Inftrees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import ItGTblRev ItGTblGeom.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Open Scope Z_scope.

(* ######################################################################### *)
(* 1.  The two statements, in the consumer's own words                       *)
(* ######################################################################### *)

(** huffman-id's original.  The modulus is the code length of the entry at [i],
    so the hypothesis reads "[j] agrees with [i] on [i]'s own code". *)
Definition RootReplicated (t : ztbl) (root : Z) : Prop :=
  forall i j, 0 <= i < 2 ^ root -> 0 <= j < 2 ^ root ->
    i mod 2 ^ (c_bits (t i)) = j mod 2 ^ (c_bits (t i)) ->
    c_bits (t j) = c_bits (t i).

(** The DIRECTIONAL form their derivation actually consumes, with [k] QUANTIFIED
    rather than fixed at the code length — the fetch loop instantiates it at
    [k = bits_exit - 8], never at [c_bits]. *)
Definition RootPrefixDet (t : ztbl) (root : Z) : Prop :=
  forall i j k, 0 <= i < 2 ^ root -> 0 <= j < 2 ^ root -> 0 <= k ->
    c_bits (t i) <= k -> i mod 2 ^ k = j mod 2 ^ k ->
    c_bits (t j) = c_bits (t i).

(** Agreement on a LONGER prefix implies agreement on a shorter one, because
    [2 ^ L] divides [2 ^ k] when [L <= k].  Isolated as a lemma because it is the
    only place the two moduli meet and getting the divisibility direction backwards
    produces a goal that reads as a missing bound. *)
Lemma mod_pow2_tower : forall a L1 L2,
  0 <= L1 <= L2 -> (a mod 2 ^ L2) mod 2 ^ L1 = a mod 2 ^ L1.
Proof.
  intros a L1 L2 H.
  assert (Hdiv : (2 ^ L1 | 2 ^ L2)).
  { exists (2 ^ (L2 - L1)).
    rewrite <- Z.pow_add_r by lia.
    f_equal. lia. }
  exact (Z.mod_mod_divide a (2 ^ L2) (2 ^ L1) Hdiv).
Qed.

Lemma mod_pow2_narrow : forall a b L k,
  0 <= L <= k -> a mod 2 ^ k = b mod 2 ^ k -> a mod 2 ^ L = b mod 2 ^ L.
Proof.
  intros a b L k Hlk Hab.
  rewrite <- (mod_pow2_tower a L k Hlk), <- (mod_pow2_tower b L k Hlk).
  rewrite Hab. reflexivity.
Qed.

(** ** The reduction, WITH the premise it genuinely needs

    [0 <= c_bits (t i)] does NOT follow from [RootPrefixDet]'s own hypotheses
    ([c_bits (t i) <= k] and [0 <= k] leave it free), and it is load-bearing:
    [Z.pow] at a NEGATIVE exponent is 0, [a mod 0 = a], so at a negative width the
    narrowing step would demand [a = b].  Rather than smuggle it in, the reduction
    takes the width bound as a hypothesis — and it is exactly
    [it_covers_root_pos]'s conclusion, which the consumer already holds, so this
    costs them nothing. *)
Theorem root_repl_gives_prefixdet : forall t root,
  (forall i, 0 <= i < 2 ^ root -> 1 <= c_bits (t i)) ->
  RootReplicated t root -> RootPrefixDet t root.
Proof.
  intros t root Hpos HR i j k Hi Hj Hk Hle Hagree.
  assert (Hb : 1 <= c_bits (t i)) by (exact (Hpos i Hi)).
  assert (Hlk : 0 <= c_bits (t i) <= k) by lia.
  exact (HR i j Hi Hj (mod_pow2_narrow i j (c_bits (t i)) k Hlk Hagree)).
Qed.

(* ######################################################################### *)
(* 2.  THE ARITHMETIC CORE: the written index set IS a residue class           *)
(* ######################################################################### *)

(** [it_fill n t bi incr h] writes [h] at [bi + k * incr] for [k] in [[0, n)]
    (Inftrees.v:272-276).  At root phase a symbol of length [L] is replicated with
    [incr = 2 ^ (len - drop) = 2 ^ L] from [bi = huff] for
    [n = 2 ^ curr / 2 ^ (len - drop) = 2 ^ (root - L)] copies.

    This says the written set is EXACTLY the residue class
      { j : 0 <= j < 2 ^ root  /\  j mod 2 ^ L = huff }.
    Both directions matter: [->] is what makes every class member written (so the
    class is uniform), and [<-] is what makes nothing OUTSIDE the class written
    (so a later trip's class is undisturbed).  A one-directional version would
    give coverage without disjointness, which is the half that does not compose. *)
Theorem fill_class_iff : forall root L huff j,
  0 <= L <= root -> 0 <= huff < 2 ^ L ->
  ((0 <= j < 2 ^ root /\ j mod 2 ^ L = huff)
   <-> (exists k, 0 <= k < 2 ^ (root - L) /\ j = huff + k * 2 ^ L)).
Proof.
  intros root L huff j HL Hh.
  assert (HpL : 0 < 2 ^ L) by (apply Z.pow_pos_nonneg; lia).
  assert (HpR : 0 < 2 ^ root) by (apply Z.pow_pos_nonneg; lia).
  assert (HpD : 0 < 2 ^ (root - L)) by (apply Z.pow_pos_nonneg; lia).
  assert (Hsplit : 2 ^ root = 2 ^ L * 2 ^ (root - L)).
  { rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  split.
  - intros (Hj & Hmod).
    exists (j / 2 ^ L).
    assert (Hdm : j = 2 ^ L * (j / 2 ^ L) + j mod 2 ^ L)
      by (apply Z.div_mod; lia).
    assert (Hlo : 0 <= j / 2 ^ L) by (apply Z.div_pos; lia).
    assert (Hhi : j / 2 ^ L < 2 ^ (root - L)).
    { apply Z.div_lt_upper_bound; [lia|]. rewrite <- Hsplit. lia. }
    rewrite Hmod in Hdm.
    split; [lia | lia].
  - intros (k & Hk & Hj).
    assert (Hmod : (huff + k * 2 ^ L) mod 2 ^ L = huff).
    { (* NO [Z.add_comm] first: [Z.mod_add] is stated at [(a + b * c) mod c] and
         the goal already has that shape.  Commuting turns it into
         [(b * c + a) mod c], which the lemma cannot match — the error names the
         pattern, not the tactic that broke it. *)
      rewrite Z.mod_add by lia.
      apply Z.mod_small. lia. }
    assert (Hkm : k * 2 ^ L <= (2 ^ (root - L) - 1) * 2 ^ L)
      by (apply Z.mul_le_mono_nonneg_r; lia).
    assert (Hexp : (2 ^ (root - L) - 1) * 2 ^ L = 2 ^ root - 2 ^ L).
    { rewrite Z.mul_sub_distr_r, Z.mul_1_l. lia. }
    split; [| rewrite Hj; exact Hmod].
    split; [lia | lia].
Qed.

(** ** The two [it_fill] facts, hit and miss

    Stated over the INDEX SET rather than over a bound, so [fill_class_iff] plugs
    straight in.  [it_fill_miss] comes first because the hit case CONSUMES it: the
    outermost copy is written by the [tset], and the recursive call must be shown
    not to overwrite it — which needs [incr <> 0], the one hypothesis a bound-shaped
    statement would have hidden. *)
Lemma it_fill_miss : forall n t bi incr h j,
  (forall k, 0 <= k < Z.of_nat n -> j <> bi + k * incr) ->
  it_fill n t bi incr h j = t j.
Proof.
  induction n as [|m IH]; intros t bi incr h j Hne.
  - cbn [it_fill]. reflexivity.
  - cbn [it_fill].
    assert (Hs : Z.of_nat (S m) = Z.of_nat m + 1)
      by (rewrite Nat2Z.inj_succ; lia).
    rewrite (IH (tset t (bi + Z.of_nat m * incr) h) bi incr h j).
    + unfold tset.
      destruct (Z.eqb_spec j (bi + Z.of_nat m * incr)) as [He | _].
      * exfalso.
        assert (Hlt : 0 <= Z.of_nat m < Z.of_nat (S m)) by lia.
        exact (Hne (Z.of_nat m) Hlt He).
      * reflexivity.
    + intros k Hk.
      assert (Hk' : 0 <= k < Z.of_nat (S m)) by lia.
      exact (Hne k Hk').
Qed.

Lemma it_fill_hit : forall n t bi incr h k,
  0 < incr -> 0 <= k < Z.of_nat n ->
  it_fill n t bi incr h (bi + k * incr) = h.
Proof.
  induction n as [|m IH]; intros t bi incr h k Hi Hk.
  - assert (H0 : Z.of_nat 0%nat = 0) by reflexivity.
    rewrite H0 in Hk. lia.
  - cbn [it_fill].
    assert (Hs : Z.of_nat (S m) = Z.of_nat m + 1)
      by (rewrite Nat2Z.inj_succ; lia).
    rewrite Hs in Hk.
    destruct (Z.eq_dec k (Z.of_nat m)) as [He | Hkm].
    + subst k.
      rewrite it_fill_miss.
      * unfold tset. rewrite Z.eqb_refl. reflexivity.
      * intros k' Hk' Hc.
        assert (Hmul : Z.of_nat m * incr = k' * incr) by lia.
        assert (Heq : Z.of_nat m = k') by (apply (Z.mul_reg_r _ _ incr); lia).
        lia.
    + assert (Hk' : 0 <= k < Z.of_nat m) by lia.
      exact (IH (tset t (bi + Z.of_nat m * incr) h) bi incr h k Hi Hk').
Qed.

(** ** The per-trip ACHIEVED fact: one fill makes its class uniform

    This is the half of the loop invariant that the write itself gives.  The other
    half — that a LATER trip's fill does not disturb this class — is the
    disjointness argument, and it is not in this file. *)
Theorem fill_makes_class_uniform : forall root L huff t h j j',
  0 <= L <= root -> 0 <= huff < 2 ^ L ->
  0 <= j < 2 ^ root -> j mod 2 ^ L = huff ->
  0 <= j' < 2 ^ root -> j' mod 2 ^ L = huff ->
  it_fill (Z.to_nat (2 ^ (root - L))) t huff (2 ^ L) h j
  = it_fill (Z.to_nat (2 ^ (root - L))) t huff (2 ^ L) h j'.
Proof.
  intros root L huff t h j j' HL Hh Hj Hjm Hj' Hj'm.
  assert (HpL : 0 < 2 ^ L) by (apply Z.pow_pos_nonneg; lia).
  assert (HpD : 0 < 2 ^ (root - L)) by (apply Z.pow_pos_nonneg; lia).
  assert (Hcast : Z.of_nat (Z.to_nat (2 ^ (root - L))) = 2 ^ (root - L))
    by (apply Z2Nat.id; lia).
  destruct (proj1 (fill_class_iff root L huff j HL Hh) (conj Hj Hjm))
    as (k & Hk & Hjk).
  destruct (proj1 (fill_class_iff root L huff j' HL Hh) (conj Hj' Hj'm))
    as (k' & Hk' & Hj'k).
  rewrite Hjk, Hj'k.
  rewrite (it_fill_hit _ t huff (2 ^ L) h k HpL);
    [| rewrite Hcast; exact Hk].
  rewrite (it_fill_hit _ t huff (2 ^ L) h k' HpL);
    [| rewrite Hcast; exact Hk'].
  reflexivity.
Qed.

(* ######################################################################### *)
(* 3.  DISJOINTNESS, REDUCED TO ONE NAMED OBLIGATION                          *)
(* ######################################################################### *)

(** The PRESERVED half of the loop invariant needs: a later trip's fill does not
    disturb an earlier trip's class.  That is class disjointness, and this lemma
    reduces it — as an IFF, so nothing is lost — to a single arithmetic condition
    on the two codes.

    Two residue classes at widths [L1 <= L2] are either DISJOINT or NESTED
    ([class(h2,L2)] inside [class(h1,L1)]), never partially overlapping, and which
    one holds is decided entirely by [h2 mod 2 ^ L1 =? h1].  So:

      "the two classes are disjoint"  <->  "the shorter code is not a prefix of
                                            the longer one"

    which is exactly PREFIX-FREENESS read on reversed positions.  The remaining
    work in this file is therefore ONE named fact — that the canonical enumeration
    the fill loop walks produces prefix-free codes — rather than an open-ended
    "disjointness argument".  That fact is where [ItGTblGeom]'s unit-interval
    geometry (positions strictly increasing, a length-[L] code occupying
    [2 ^ (15 - L)]) is meant to be spent, and it is not proved here.

    Stated as an iff on purpose: the forward direction is what a caller consumes,
    and the backward direction is what stops someone "strengthening" the hypothesis
    into something the geometry cannot supply. *)
Theorem class_disjoint_iff : forall root L1 L2 h1 h2,
  0 <= L1 <= L2 -> L2 <= root ->
  0 <= h1 < 2 ^ L1 -> 0 <= h2 < 2 ^ L2 ->
  ((forall j, 0 <= j < 2 ^ root ->
      ~ (j mod 2 ^ L1 = h1 /\ j mod 2 ^ L2 = h2))
   <-> h2 mod 2 ^ L1 <> h1).
Proof.
  intros root L1 L2 h1 h2 HL Hr Hh1 Hh2.
  assert (HpL1 : 0 < 2 ^ L1) by (apply Z.pow_pos_nonneg; lia).
  assert (HpL2 : 0 < 2 ^ L2) by (apply Z.pow_pos_nonneg; lia).
  assert (Hmono : 2 ^ L2 <= 2 ^ root) by (apply Z.pow_le_mono_r; lia).
  split.
  - (* disjoint -> not a prefix.  The witness is [h2] ITSELF: it is in its own
       class, and it is in [h1]'s class exactly when the prefix condition holds. *)
    intros Hdisj Hpre.
    assert (Hj : 0 <= h2 < 2 ^ root) by lia.
    apply (Hdisj h2 Hj).
    split.
    + rewrite <- Hpre. reflexivity.
    + apply Z.mod_small. lia.
  - (* not a prefix -> disjoint.  Any member of class 2 has its low [L1] bits
       determined by [h2], by the tower law. *)
    intros Hpre j Hj (H1 & H2).
    apply Hpre.
    rewrite <- H2, (mod_pow2_tower j L1 L2 HL). exact H1.
Qed.

(** The same-length case, which the geometry supplies for free: distinct codes of
    equal length have disjoint classes with no prefix reasoning at all.  Worth
    having separately because it is the majority of trip pairs and it needs none of
    the interval machinery. *)
Corollary class_disjoint_same_len : forall root L h1 h2,
  0 <= L <= root -> 0 <= h1 < 2 ^ L -> 0 <= h2 < 2 ^ L -> h1 <> h2 ->
  forall j, 0 <= j < 2 ^ root ->
    ~ (j mod 2 ^ L = h1 /\ j mod 2 ^ L = h2).
Proof.
  intros root L h1 h2 HL Hh1 Hh2 Hne.
  apply (proj2 (class_disjoint_iff root L L h1 h2
                  (conj (proj1 HL) (Z.le_refl L)) (proj2 HL) Hh1 Hh2)).
  rewrite Z.mod_small by lia. auto.
Qed.

(* ######################################################################### *)
(* 3b. PREFIX-FREENESS FROM THE INTERVAL GEOMETRY                             *)
(* ######################################################################### *)

(** The "one named fact" §GTBL-DISJ said was outstanding, and it turned out to be
    a corollary of two lemmas that were already in the layer — [zrev_split]
    (ItGTblRev) and [zrev_lt].  Pricing it as new work was another over-estimate,
    which is now the sixth in this campaign and every one of them was high.

    STATED ADDITIVELY, no subtraction anywhere: a caller instantiates
    [D := L2 - L1] and [E := 15 - L2], so the two positions are
    [zrev L1 h1 * (2^D * 2^E)] and [zrev (L1+D) h2 * 2^E], and the earlier code's
    unit is [2^D * 2^E].  Subtraction in the exponents is what makes these
    statements painful to apply (and at a negative exponent [Z.pow] silently
    returns 0), so the widths are given as sums.

    THE CONTENT: if the later code's position is at or beyond the earlier code's
    interval END, the earlier code cannot be a prefix of it.  [zrev_split]
    decomposes the longer reversed code into (reversed low part) * 2^D + (reversed
    high part); a prefix relation would force the low part to be [h1], pinning the
    longer code inside [h1]'s own interval — which is exactly what the position
    hypothesis forbids.

    NOTE the ABSENT premise: no bound on [h2] is needed.  [zrev_lt] holds
    unconditionally and [zrev_split] only wants the low part in range, which [mod]
    supplies.  I had written [0 <= h2 < 2 ^ (L1+D)] into the first draft out of
    symmetry with [h1]; removing it makes the theorem strictly more applicable,
    since an unused premise only ever makes a lemma harder to use. *)
Theorem prefix_free_of_positions : forall (L1 D E : nat) (h1 h2 : Z),
  0 <= h1 < 2 ^ Z.of_nat L1 ->
  zrev L1 h1 * (2 ^ Z.of_nat D * 2 ^ Z.of_nat E)
    + 2 ^ Z.of_nat D * 2 ^ Z.of_nat E
  <= zrev (L1 + D) h2 * 2 ^ Z.of_nat E ->
  h2 mod 2 ^ Z.of_nat L1 <> h1.
Proof.
  intros L1 D E h1 h2 Hh1 Hpos Hpre.
  assert (Hp1 : 0 < 2 ^ Z.of_nat L1) by (apply pow2_pos_nat).
  assert (HpD : 0 < 2 ^ Z.of_nat D) by (apply pow2_pos_nat).
  assert (HpE : 0 < 2 ^ Z.of_nat E) by (apply pow2_pos_nat).
  (* decompose the longer code at bit L1; the low part IS h1 by hypothesis *)
  assert (Hlo : 0 <= h2 mod 2 ^ Z.of_nat L1 < 2 ^ Z.of_nat L1)
    by (apply Z.mod_pos_bound; lia).
  assert (Hdec : h2 = h2 mod 2 ^ Z.of_nat L1
                      + (h2 / 2 ^ Z.of_nat L1) * 2 ^ Z.of_nat L1).
  { pose proof (Z.div_mod h2 (2 ^ Z.of_nat L1)) as HD.
    assert (Hnz : 2 ^ Z.of_nat L1 <> 0) by lia.
    specialize (HD Hnz). lia. }
  assert (Hsplit : zrev (L1 + D) h2
                   = zrev L1 (h2 mod 2 ^ Z.of_nat L1) * 2 ^ Z.of_nat D
                     + zrev D (h2 / 2 ^ Z.of_nat L1)).
  { rewrite Hdec at 1.
    exact (zrev_split L1 D (h2 mod 2 ^ Z.of_nat L1)
             (h2 / 2 ^ Z.of_nat L1) Hlo). }
  (* the high part's reversal is strictly inside one unit of the shorter code *)
  assert (Hhi : zrev D (h2 / 2 ^ Z.of_nat L1) < 2 ^ Z.of_nat D)
    by (apply zrev_lt).
  rewrite Hpre in Hsplit.
  (* so the longer code sits strictly below the shorter one's interval end *)
  assert (Hlt : zrev (L1 + D) h2 < zrev L1 h1 * 2 ^ Z.of_nat D + 2 ^ Z.of_nat D)
    by lia.
  assert (Hscale : zrev (L1 + D) h2 * 2 ^ Z.of_nat E
                   < (zrev L1 h1 * 2 ^ Z.of_nat D + 2 ^ Z.of_nat D)
                     * 2 ^ Z.of_nat E)
    by (apply mul_lt_mono_r'; [lia | exact Hlt]).
  (* ... contradicting the position hypothesis, after one ring step *)
  assert (Hexp : (zrev L1 h1 * 2 ^ Z.of_nat D + 2 ^ Z.of_nat D) * 2 ^ Z.of_nat E
                 = zrev L1 h1 * (2 ^ Z.of_nat D * 2 ^ Z.of_nat E)
                   + 2 ^ Z.of_nat D * 2 ^ Z.of_nat E) by ring.
  lia.
Qed.

(** ** The SUBTRACTIVE form, which is the one a caller actually has

    [prefix_free_of_positions] is stated additively so no exponent can go negative,
    and that is right for the proof — but every caller speaks [ItGTblCover]'s
    vocabulary, where a position is [zrev (Z.to_nat len) huff * 2 ^ (15 - len)] with
    Z widths and a SUBTRACTED exponent.  Publishing only the additive form would
    leave the theorem in a shape nobody holds, so the adapter is part of the
    deliverable rather than left to the consumer.

    The two hypotheses are exactly what [CovInv] already carries: its position
    clause gives [Pos … st = zrev (Z.to_nat (s_len st)) (s_huff st) * 2 ^ (15 -
    s_len st)], and Cover's own advance lemma gives [Pos] increasing by exactly
    [2 ^ (15 - len)] per trip — which IS the interval-end premise below. *)
Theorem prefix_free_of_pos_z : forall (L1 L2 h1 h2 : Z),
  0 <= L1 <= L2 -> L2 <= 15 ->
  0 <= h1 < 2 ^ L1 ->
  zrev (Z.to_nat L1) h1 * 2 ^ (15 - L1) + 2 ^ (15 - L1)
    <= zrev (Z.to_nat L2) h2 * 2 ^ (15 - L2) ->
  h2 mod 2 ^ L1 <> h1.
Proof.
  intros L1 L2 h1 h2 HL H15 Hh1 Hpos.
  (* name the two gaps as nats, then discharge every width identity by lia on the
     Z side -- the nat/Z plumbing is the whole content of this adapter *)
  set (D := Z.to_nat (L2 - L1)).
  set (E := Z.to_nat (15 - L2)).
  assert (HD : Z.of_nat D = L2 - L1) by (unfold D; apply Z2Nat.id; lia).
  assert (HE : Z.of_nat E = 15 - L2) by (unfold E; apply Z2Nat.id; lia).
  assert (HL1 : Z.of_nat (Z.to_nat L1) = L1) by (apply Z2Nat.id; lia).
  assert (Hsum : Z.to_nat L2 = (Z.to_nat L1 + D)%nat).
  { apply Nat2Z.inj. rewrite Nat2Z.inj_add, HD, HL1, (Z2Nat.id L2) by lia. lia. }
  assert (Hsplit : 2 ^ (15 - L1) = 2 ^ Z.of_nat D * 2 ^ Z.of_nat E).
  { rewrite HD, HE, <- Z.pow_add_r by lia. f_equal. lia. }
  assert (Hlast : 2 ^ (15 - L2) = 2 ^ Z.of_nat E) by (rewrite HE; reflexivity).
  assert (Hh1' : 0 <= h1 < 2 ^ Z.of_nat (Z.to_nat L1)) by (rewrite HL1; exact Hh1).
  (* rewrite the hypothesis into the additive form, then it is the lemma above *)
  rewrite Hsplit, Hlast, Hsum in Hpos.
  assert (Hgoal := prefix_free_of_positions (Z.to_nat L1) D E h1 h2 Hh1' Hpos).
  rewrite HL1 in Hgoal. exact Hgoal.
Qed.

(** And the two joined: ordered positions give disjoint write classes.  This is
    the PRESERVED half of the loop invariant, modulo the loop's own bookkeeping —
    a later trip whose position has passed an earlier code's interval cannot touch
    that code's class. *)
Corollary classes_disjoint_of_positions :
  forall (root L1 D E : nat) (h1 h2 : Z),
  (L1 <= L1 + D)%nat -> (L1 + D <= root)%nat ->
  0 <= h1 < 2 ^ Z.of_nat L1 ->
  0 <= h2 < 2 ^ Z.of_nat (L1 + D) ->
  zrev L1 h1 * (2 ^ Z.of_nat D * 2 ^ Z.of_nat E)
    + 2 ^ Z.of_nat D * 2 ^ Z.of_nat E
  <= zrev (L1 + D) h2 * 2 ^ Z.of_nat E ->
  forall j, 0 <= j < 2 ^ Z.of_nat root ->
    ~ (j mod 2 ^ Z.of_nat L1 = h1 /\ j mod 2 ^ Z.of_nat (L1 + D) = h2).
Proof.
  intros root L1 D E h1 h2 Hle Hr Hh1 Hh2 Hpos.
  apply (proj2 (class_disjoint_iff (Z.of_nat root) (Z.of_nat L1)
                  (Z.of_nat (L1 + D)) h1 h2
                  (conj (Nat2Z.is_nonneg L1) (inj_le _ _ Hle))
                  (inj_le _ _ Hr) Hh1 Hh2)).
  exact (prefix_free_of_positions L1 D E h1 h2 Hh1 Hpos).
Qed.

(* ######################################################################### *)
(* 4.  POSITIVE INSTANCES — neither Prop is vacuous                          *)
(* ######################################################################### *)

(** A [Definition] of a [Prop] typechecks whether or not anything satisfies it, so
    a relation published for a consumer to instantiate needs an exhibited witness.
    The smallest honest one: [root = 1] with both entries carrying [c_bits = 1] —
    the shape the accepted-INCOMPLETE arm actually produces, which is the arm the
    counterexample above shows is the delicate one. *)
Definition tbl_two_ones : ztbl :=
  tset (tset tnone 0 (mkCodeT 0 1 0)) 1 (mkCodeT 64 1 0).

Lemma tbl_two_ones_bits : forall i, 0 <= i < 2 ^ 1 -> c_bits (tbl_two_ones i) = 1.
Proof.
  intros i Hi.
  assert (Hc : i = 0 \/ i = 1) by (cbn in Hi; lia).
  unfold tbl_two_ones, tset, mkCodeT, u8, u16.
  destruct Hc as [Hz | Hz]; rewrite Hz; reflexivity.
Qed.

Theorem root_replicated_instantiated : RootReplicated tbl_two_ones 1.
Proof.
  intros i j Hi Hj _.
  rewrite (tbl_two_ones_bits i Hi), (tbl_two_ones_bits j Hj). reflexivity.
Qed.

Theorem root_prefixdet_instantiated : RootPrefixDet tbl_two_ones 1.
Proof.
  apply root_repl_gives_prefixdet.
  - intros i Hi. rewrite (tbl_two_ones_bits i Hi). lia.
  - exact root_replicated_instantiated.
Qed.

Print Assumptions prefix_free_of_positions.
Print Assumptions prefix_free_of_pos_z.
Print Assumptions classes_disjoint_of_positions.
Print Assumptions mod_pow2_tower.
Print Assumptions class_disjoint_iff.
Print Assumptions class_disjoint_same_len.
Print Assumptions mod_pow2_narrow.
Print Assumptions root_repl_gives_prefixdet.
Print Assumptions fill_class_iff.
Print Assumptions it_fill_miss.
Print Assumptions it_fill_hit.
Print Assumptions fill_makes_class_uniform.
Print Assumptions tbl_two_ones_bits.
Print Assumptions root_replicated_instantiated.
Print Assumptions root_prefixdet_instantiated.

(* ######################################################################### *)
(* 5.  0 <= c_val OF EVERY ENTRY -- huffman-id's CopySaneCont input           *)
(* ######################################################################### *)

(** THE PREMISE THEY OFFERED IS NOT NEEDED. huffman-id asked for [0 <= c_val]
    "given a non-negative base array", and offered to accept a premise naming the
    concrete RFC 1951 [lbase]/[dbase] arrays if that were cheaper.

    Neither is required. Every entry [inflate_table] writes is built by
    [Base.mkCodeT], whose val field is [u16 val = val mod 65536] (Base.v:80,103),
    and [Z.modulo] by a positive modulus is non-negative for ANY argument. So the
    sign is a property of the CONSTRUCTOR, not of the base array — it holds even
    for a negative [x_base]. Their four writers ([x_base c k], the work index [w],
    the next-table index [next'], the literal 0) all pass through it.

    What DOES need a premise is the part they did not ask about: entries the loop
    never writes come from [t0], the caller's table, which [it_model] takes as a
    parameter and is otherwise arbitrary. So the whole-table statement carries
    [ValNonneg t0]. In the real decoder that is free — [t0] is a shifted view of
    [state->codes], itself a Code array built by these same constructors — and it
    is strictly weaker than anything about [x_base]. *)
Lemma mkCodeT_val_nonneg : forall op bits val, 0 <= c_val (mkCodeT op bits val).
Proof.
  intros op bits val. unfold mkCodeT, u16. cbn [c_val].
  apply Z.mod_pos_bound. lia.
Qed.

(** Unconditional, and this is the one that makes their premise unnecessary: the
    leaf entry is non-negative whatever the context arrays hold. *)
Lemma it_here_val_nonneg : forall c st, 0 <= c_val (it_here c st).
Proof.
  intros c st. unfold it_here. cbv zeta.
  destruct (Z.ltb (x_work c (s_sym st) + 1) (x_match c));
    [apply mkCodeT_val_nonneg|].
  destruct (Z.leb (x_match c) (x_work c (s_sym st)));
    apply mkCodeT_val_nonneg.
Qed.

Definition ValNonneg (t : ztbl) : Prop := forall i, 0 <= c_val (t i).

Lemma valnonneg_tset : forall t i e,
  ValNonneg t -> 0 <= c_val e -> ValNonneg (tset t i e).
Proof.
  intros t i e Ht He j. unfold tset.
  destruct (Z.eqb j i); [exact He | exact (Ht j)].
Qed.

Lemma valnonneg_fill : forall n t bi incr h,
  ValNonneg t -> 0 <= c_val h -> ValNonneg (it_fill n t bi incr h).
Proof.
  induction n as [|m IH]; intros t bi incr h Ht Hh.
  - cbn [it_fill]. exact Ht.
  - cbn [it_fill]. apply IH; [| exact Hh].
    apply valnonneg_tset; [exact Ht | exact Hh].
Qed.

(** The step's output table, named so the branch analysis never has to [injection]
    a record carrying [it_subsz] at literal fuel -- the projection is taken by
    [cbn] on a record literal, which touches only the table field. *)
Definition step_tbl (r : ItStep) : ztbl :=
  match r with
  | ItCont st => s_tbl st
  | ItBreak st => s_tbl st
  | ItOverflow t => t
  end.

Lemma valnonneg_step : forall c st,
  ValNonneg (s_tbl st) -> ValNonneg (step_tbl (it_step c st)).
Proof.
  intros c st Ht.
  assert (Hfill : ValNonneg (it_fill
      (Z.to_nat (Z.shiftl 1 (s_curr st) / Z.shiftl 1 (s_len st - s_drop st)))
      (s_tbl st) (s_next st + Z.shiftr (s_huff st) (s_drop st))
      (Z.shiftl 1 (s_len st - s_drop st)) (it_here c st))).
  { apply valnonneg_fill; [exact Ht | exact (it_here_val_nonneg c st)]. }
  unfold it_step. cbv zeta.
  destruct (Z.eqb (zset (s_count st) (s_len st) (s_count st (s_len st) - 1)
                     (s_len st)) 0) eqn:Ehit;
    cbn [andb].
  - destruct (Z.eqb (s_len st) (x_max c)) eqn:Emx.
    + cbn [step_tbl s_tbl]. exact Hfill.
    + destruct (andb _ _) eqn:Eg.
      * destruct (it_enough (x_type c) _) eqn:Een;
          cbn [step_tbl s_tbl]; [exact Hfill|].
        apply valnonneg_tset; [exact Hfill | apply mkCodeT_val_nonneg].
      * cbn [step_tbl s_tbl]. exact Hfill.
  - destruct (andb _ _) eqn:Eg.
    + destruct (it_enough (x_type c) _) eqn:Een;
        cbn [step_tbl s_tbl]; [exact Hfill|].
      apply valnonneg_tset; [exact Hfill | apply mkCodeT_val_nonneg].
    + cbn [step_tbl s_tbl]. exact Hfill.
Qed.

Lemma valnonneg_loop : forall n c st r,
  it_loop n c st = Some r -> ValNonneg (s_tbl st) -> ValNonneg (step_tbl r).
Proof.
  induction n as [|m IH]; intros c st r H Ht.
  - cbn [it_loop] in H. discriminate H.
  - cbn [it_loop] in H.
    pose proof (valnonneg_step c st Ht) as Hs.
    destruct (it_step c st) as [st'|st'|t] eqn:E.
    + cbn [step_tbl] in Hs. exact (IH c st' r H Hs).
    + injection H as <-. exact Hs.
    + injection H as <-. exact Hs.
Qed.

Lemma valnonneg_finish : forall st,
  ValNonneg (s_tbl st) -> ValNonneg (it_finish st).
Proof.
  intros st Ht. unfold it_finish.
  destruct (Z.eqb (s_huff st) 0); [exact Ht|].
  apply valnonneg_tset; [exact Ht | apply mkCodeT_val_nonneg].
Qed.

Print Assumptions mkCodeT_val_nonneg.
Print Assumptions it_here_val_nonneg.
Print Assumptions valnonneg_tset.
Print Assumptions valnonneg_fill.
Print Assumptions valnonneg_step.
Print Assumptions valnonneg_loop.
Print Assumptions valnonneg_finish.

(** ** Up through [it_pre] to the top

    [it_pre]'s body substitutes five LITERAL-FUEL scans ([it_findmax 15],
    [it_findmin 16], [it_kraft 15], [it_offs 14], [it_sort]) into its result
    records, so the same discipline applies as everywhere else in this chain:
    destruct the branch booleans with [eqn] (which does not reduce them), invert
    the constructor with a lemma proved ON VARIABLES, and take the field with
    [cbn] on a record literal. Never [injection] the real hypothesis. *)
Lemma prego_inj_st : forall c1 st1 c2 st2,
  PreGo c1 st1 = PreGo c2 st2 -> st1 = st2.
Proof. intros c1 st1 c2 st2 H. injection H as _ H. exact H. Qed.

Lemma preempty_inj : forall t1 t2, PreEmpty t1 = PreEmpty t2 -> t1 = t2.
Proof. intros t1 t2 H. injection H as H. exact H. Qed.

Lemma it_pre_go_tbl : forall ty lens codes root0 t0 c st,
  it_pre ty lens codes root0 t0 = PreGo c st -> s_tbl st = t0.
Proof.
  intros ty lens codes root0 t0 c st H.
  unfold it_pre in H. cbv zeta in H.
  destruct (Z.eqb (it_findmax 15%nat MAXBITS (it_count (Z.to_nat codes) 0 lens zzero)) 0);
    [discriminate H|].
  destruct (it_kraft 15%nat 1 1 (it_count (Z.to_nat codes) 0 lens zzero)) as [lft|];
    [|discriminate H].
  destruct (it_incomplete ty lft _); [discriminate H|].
  destruct (it_enough ty _); [discriminate H|].
  apply prego_inj_st in H. rewrite <- H. cbn [s_tbl]. reflexivity.
Qed.

Lemma it_pre_empty_valnonneg : forall ty lens codes root0 t0 t,
  it_pre ty lens codes root0 t0 = PreEmpty t ->
  ValNonneg t0 -> ValNonneg t.
Proof.
  intros ty lens codes root0 t0 t H Ht.
  unfold it_pre in H. cbv zeta in H.
  destruct (Z.eqb (it_findmax 15%nat MAXBITS (it_count (Z.to_nat codes) 0 lens zzero)) 0).
  - apply preempty_inj in H. rewrite <- H.
    apply valnonneg_tset; [apply valnonneg_tset|]; try apply mkCodeT_val_nonneg.
    exact Ht.
  - destruct (it_kraft 15%nat 1 1 (it_count (Z.to_nat codes) 0 lens zzero)) as [lft|];
      [|discriminate H].
    destruct (it_incomplete ty lft _); [discriminate H|].
    destruct (it_enough ty _); discriminate H.
Qed.

(** THE DELIVERABLE. One premise, on the CALLER's table, and none on [x_base]. *)
Theorem it_model_val_nonneg : forall ty lens codes root0 t0 out,
  ValNonneg t0 ->
  it_model ty lens codes root0 t0 = Some out ->
  forall i, 0 <= c_val (o_tbl out i).
Proof.
  intros ty lens codes root0 t0 out Ht0 H.
  unfold it_model in H.
  destruct (it_pre ty lens codes root0 t0) as [| t | | c st] eqn:E.
  - injection H as <-. cbn [o_tbl]. exact Ht0.
  - injection H as <-. cbn [o_tbl].
    exact (it_pre_empty_valnonneg ty lens codes root0 t0 t E Ht0).
  - injection H as <-. cbn [o_tbl]. exact Ht0.
  - assert (Hst : ValNonneg (s_tbl st))
      by (rewrite (it_pre_go_tbl ty lens codes root0 t0 c st E); exact Ht0).
    destruct (it_loop (S (Z.to_nat codes)) c st) as [r|] eqn:EL; [|discriminate H].
    pose proof (valnonneg_loop (S (Z.to_nat codes)) c st r EL Hst) as Hr.
    destruct r as [st'|st'|t]; cbn [step_tbl] in Hr.
    + discriminate H.
    + injection H as <-. cbn [o_tbl]. exact (valnonneg_finish st' Hr).
    + injection H as <-. cbn [o_tbl]. exact Hr.
Qed.

Print Assumptions prego_inj_st.
Print Assumptions preempty_inj.
Print Assumptions it_pre_go_tbl.
Print Assumptions it_pre_empty_valnonneg.
Print Assumptions it_model_val_nonneg.

(** ** The write-back seam, for huffman-id's [codes_wb]

    [Inflate.v:745] is
      [codes_wb cs k t := fun i => if Z.leb k i then t (i - k) else cs i]
    and they need [ValNonneg] to survive it.

    Stated over the SHAPE rather than over the name, so this file acquires no
    dependency on [Inflate.v] — the consumer does [unfold codes_wb; apply
    valnonneg_splice] and the statement is the same term either way. A bridge
    lemma that drags a large module into the producer's chain to save the consumer
    one [unfold] is a bad trade, and it would put my build behind theirs. *)
Lemma valnonneg_splice : forall (cs t : ztbl) (k : Z),
  ValNonneg cs -> ValNonneg t ->
  ValNonneg (fun i => if Z.leb k i then t (i - k) else cs i).
Proof.
  intros cs t k Hcs Ht i.
  destruct (Z.leb k i); [exact (Ht (i - k)) | exact (Hcs i)].
Qed.

Print Assumptions valnonneg_splice.

(** ** THE TRIPWIRE: pinning the thing whose ABSENCE this theorem depends on

    huffman-id's device, and it belongs here rather than only in their file,
    because [it_model_val_nonneg] is the theorem that carries [ValNonneg t0] as a
    premise. That premise is necessary only because [Base.mkCode] is a bare
    constructor over arbitrary [Z] — [Base.v:99] — used directly at [Base.v:137]
    ([tnone]) and in [DecodeBridge.v]. So [0 <= c_val] is NOT a typing fact and the
    invariant cannot be dropped.

    The two Examples below are a TRIPWIRE, not documentation. If
    [val_can_be_negative] ever stops compiling, [mkCode] has been sealed or the
    field constrained, at which point [ValNonneg] is unnecessary and every premise
    threading it should be deleted rather than maintained. It fires in
    milliseconds, and a comment saying the same thing would not fire at all.

    This is the [cl_order]/[bl_order] pinning device applied to a NEGATIVE: pin the
    absence your theorem depends on, not just the presence it consumes. A theorem
    whose premise exists only because the type is loose should say so in a form the
    build can check, or the premise outlives its reason. *)
Example val_can_be_negative : c_val (mkCode 0 0 (-1)) = -1.
Proof. reflexivity. Qed.

Example valnonneg_rejects_it : ~ ValNonneg (fun _ => mkCode 0 0 (-1)).
Proof.
  intro H. specialize (H 0). cbn [c_val] in H. lia.
Qed.

Print Assumptions val_can_be_negative.
Print Assumptions valnonneg_rejects_it.
