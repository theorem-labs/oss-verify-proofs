(** * KraftAdjust -- what [gb_adjust] does to the Kraft sum, as pure arithmetic.

    OWNER: kraftsum.

    THE RESULT, in one line: **one trip of [gb_adjust] lowers the histogram Kraft
    sum by EXACTLY ONE**, whatever the tree, whatever the histogram.  Every
    [zset] in the body is accounted for, including the case where two of them hit
    the same index.

        blc[bits]   -= 1      costs  2 ^ (maxlen - bits)
        blc[bits+1] += 2      gains  2 * 2 ^ (maxlen - bits - 1) = 2 ^ (maxlen - bits)
        blc[maxlen] -= 1      costs  2 ^ (maxlen - maxlen) = 1
        -------------------------------------------------------------
        net                          -1

    WHY THIS IS THE RIGHT THING TO PROVE FIRST.  [KraftOwed.v] splits the owed sum
    on [gen_bitlen]'s overflow flag, and huffman-id's [GenBitlen.v] header calls
    [gb_adjust] "the hardest single function in the file".  It is hard as a
    SEMANTIC statement -- "the adjusted code is valid" -- because that depends on
    the tree.  But its effect on the Kraft sum does not depend on the tree at all,
    and separating the two turns the hard branch into: prove the PRE-adjust excess
    equals the trip count, then apply this.

    A FINDING THAT CONSTRAINS THE HARD BRANCH, and it came out of a control rather
    than a proof.  I built a histogram over budget by 6 and ran [gb_adjust] with
    [ov = 6]: three trips, sum down by exactly 3, and it ended at 32769 -- STILL
    OVER BUDGET.  So **"the excess after clamping is [ov / 2]" is not a property
    of [gb_adjust]**, and no amount of work on this function will supply it.  It
    is a property of [gb_pass1]'s clamping, and whoever proves the [ov > 0] branch
    owes it separately.  My [blcC] is not a realisable [gb_pass1] output, which is
    exactly why it is informative: it separates what this function guarantees from
    what its caller must.

    CURRENCY: [Z] throughout, per huffman-id's [nc_le_Z] note that the [nat] route
    forces [2 ^ 15] to a unary literal and made one [cbn] cost nine seconds. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff Trees.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** ** 1. The histogram Kraft sum, over an explicit level list

    Over a list rather than a range so the induction has something to recurse on;
    [zksum] below is the instance at [seq 1 maxlen] that everything else uses. *)
Definition zksum_over (M : Z) (blc : zarr) (levels : list nat) : Z :=
  fold_right Z.add 0
    (map (fun j => blc (Z.of_nat j) * 2 ^ (M - Z.of_nat j)) levels).

Definition zksum (M : Z) (blc : zarr) : Z :=
  zksum_over M blc (seq 1 (Z.to_nat M)).

Lemma zksum_over_nil : forall M blc, zksum_over M blc [] = 0.
Proof. reflexivity. Qed.

Lemma zksum_over_cons : forall M blc a l,
  zksum_over M blc (a :: l)
  = blc (Z.of_nat a) * 2 ^ (M - Z.of_nat a) + zksum_over M blc l.
Proof. reflexivity. Qed.

(** ** 2. How one [zset] moves the sum

    Two lemmas, because a [zset] at an index the sum does not read must be shown
    to change NOTHING -- that is what makes the [In] case's accounting exact
    rather than an inequality. *)
Lemma zksum_over_zset_notin : forall M blc n v levels,
  ~ In n levels ->
  zksum_over M (zset blc (Z.of_nat n) v) levels = zksum_over M blc levels.
Proof.
  intros M blc n v levels. induction levels as [|a l IH]; intro Hni.
  - reflexivity.
  - rewrite !zksum_over_cons.
    rewrite zset_other by (intro Hc; apply Hni; left; lia).
    rewrite IH by (intro Hc; apply Hni; now right). reflexivity.
Qed.

Lemma zksum_over_zset_in : forall M blc n v levels,
  NoDup levels -> In n levels ->
  zksum_over M (zset blc (Z.of_nat n) v) levels
  = zksum_over M blc levels + (v - blc (Z.of_nat n)) * 2 ^ (M - Z.of_nat n).
Proof.
  intros M blc n v levels Hnd Hin.
  induction levels as [|a l IH]; [contradiction|].
  inversion Hnd as [|a' l' Hna Hnd']; subst a' l'.
  rewrite !zksum_over_cons.
  destruct Hin as [Heq|Hin].
  - (* the head IS the touched index; the tail cannot contain it again *)
    subst a. rewrite zset_same.
    rewrite (zksum_over_zset_notin M blc n v l Hna). lia.
  - (* the head is some other index; recurse *)
    assert (Hne : a <> n) by (intro Hc; subst; contradiction).
    rewrite zset_other by lia.
    rewrite (IH Hnd' Hin). lia.
Qed.

(** The instance at [seq], which is what [zksum] is. *)
Lemma zksum_zset_in : forall M blc n v,
  (1 <= n)%nat -> Z.of_nat n <= M ->
  zksum M (zset blc (Z.of_nat n) v)
  = zksum M blc + (v - blc (Z.of_nat n)) * 2 ^ (M - Z.of_nat n).
Proof.
  intros M blc n v H1 HM. unfold zksum.
  apply zksum_over_zset_in; [apply seq_NoDup|].
  apply in_seq. lia.
Qed.

(** The same thing with a [Z] index, which is what every use site actually has.
    Worth its own lemma rather than [Z.of_nat]/[Z.to_nat] juggling at each call:
    the nat-indexed form forces positional [rewrite ... at n] to steer the
    conversion, and a positional rewrite is guesswork that breaks whenever the
    surrounding term changes. *)
Lemma zksum_zset_Z : forall M blc (i : Z) v,
  1 <= i <= M ->
  zksum M (zset blc i v) = zksum M blc + (v - blc i) * 2 ^ (M - i).
Proof.
  intros M blc i v Hi. unfold zksum.
  assert (Hin : In (Z.to_nat i) (seq 1 (Z.to_nat M))) by (apply in_seq; lia).
  pose proof (zksum_over_zset_in M blc (Z.to_nat i) v
                (seq 1 (Z.to_nat M)) (seq_NoDup _ _) Hin) as H.
  rewrite (Z2Nat.id i) in H by lia. exact H.
Qed.

(** ** 3. The body of one [gb_adjust] trip, named

    [gb_adjust]'s body is inlined in a [Fixpoint] with a [let]-chain, so it has
    no name to state a lemma about.  Giving it one is what makes the accounting
    below readable, and [gb_adjust_unfold_last]/[_step] tie the name back to the
    real function by [reflexivity]-grade unfolding rather than by assertion. *)
Definition gba_bits (M : Z) (blc : zarr) : Z :=
  gb_findbits (Z.to_nat MAX_BITS + 1) blc (M - 1).

Definition gba_body (M : Z) (blc : zarr) : zarr :=
  let bits := gba_bits M blc in
  let blc1 := zset blc bits (u16 (blc bits - 1)) in
  let blc2 := zset blc1 (bits + 1) (u16 (blc1 (bits + 1) + 2)) in
  zset blc2 M (u16 (blc2 M - 1)).

Lemma gb_adjust_unfold_last : forall f M blc ov,
  ov <= 2 -> gb_adjust (S f) M blc ov = gba_body M blc.
Proof.
  intros f M blc ov Hov. cbn [gb_adjust]. unfold gba_body, gba_bits.
  replace (Z.ltb 2 ov) with false by (symmetry; apply Z.ltb_ge; lia).
  reflexivity.
Qed.

Lemma gb_adjust_unfold_step : forall f M blc ov,
  2 < ov -> gb_adjust (S f) M blc ov = gb_adjust f M (gba_body M blc) (ov - 2).
Proof.
  intros f M blc ov Hov. cbn [gb_adjust]. unfold gba_body, gba_bits.
  replace (Z.ltb 2 ov) with true by (symmetry; apply Z.ltb_lt; lia).
  reflexivity.
Qed.

(** ** 4. The side conditions, named as a predicate

    These are what the [ov > 0] branch owes at each trip.  Naming them rather
    than burying them in a lemma's binder list is deliberate: an obligation with
    a name is one somebody can prove, and [GbaOk] is short enough to check
    against [gb_findbits]' own postcondition.

    [1 <= blc M] is needed only when [bits + 1 < M]; when [bits + 1 = M] the
    [+2] has already made that slot positive.  It is taken unconditionally
    because [gb_pass1] always populates [maxlen] when it clamps -- clamping IS
    writing [maxlen] -- so requiring it costs the consumer nothing. *)
Definition GbaOk (M : Z) (blc : zarr) : Prop :=
  1 <= gba_bits M blc < M
  /\ 1 <= blc (gba_bits M blc)
  /\ 1 <= blc M
  /\ (forall b, 0 <= blc b <= 32768).

(** ** 5. One trip costs exactly one

    The two cases are [bits + 1 < M] (three distinct indices) and [bits + 1 = M]
    (the second and third [zset] alias).  They are genuinely different
    computations that produce the same delta, which is why both are written out
    instead of being handled by a single [lia]. *)
Theorem zksum_gba_body : forall M blc,
  GbaOk M blc -> zksum M (gba_body M blc) = zksum M blc - 1.
Proof.
  intros M blc [Hi [Hbi [HbM Hbnd]]].
  set (i := gba_bits M blc) in *.
  unfold gba_body. fold i.
  (* --- write 1: blc[i] -= 1 --- *)
  assert (Hu1 : u16 (blc i - 1) = blc i - 1)
    by (unfold u16; apply Z.mod_small; specialize (Hbnd i); lia).
  set (blc1 := zset blc i (u16 (blc i - 1))).
  assert (Hs1 : zksum M blc1 = zksum M blc - 2 ^ (M - i)).
  { unfold blc1. rewrite Hu1.
    rewrite (zksum_zset_Z M blc i (blc i - 1)) by lia. lia. }
  (* --- write 2: blc[i+1] += 2 --- *)
  assert (Hb1i1 : blc1 (i + 1) = blc (i + 1))
    by (unfold blc1; rewrite zset_other by lia; reflexivity).
  assert (Hu2 : u16 (blc1 (i + 1) + 2) = blc (i + 1) + 2).
  { rewrite Hb1i1. unfold u16. apply Z.mod_small.
    specialize (Hbnd (i + 1)); lia. }
  set (blc2 := zset blc1 (i + 1) (u16 (blc1 (i + 1) + 2))).
  assert (Hs2 : zksum M blc2 = zksum M blc1 + 2 * 2 ^ (M - (i + 1))).
  { unfold blc2. rewrite Hu2.
    rewrite (zksum_zset_Z M blc1 (i + 1) (blc (i + 1) + 2)) by lia.
    rewrite Hb1i1. lia. }
  (* The first two writes CANCEL exactly: 2 * 2^(M-i-1) = 2^(M-i). *)
  assert (Hpow : 2 * 2 ^ (M - (i + 1)) = 2 ^ (M - i)).
  { replace (M - i) with (1 + (M - (i + 1))) by lia.
    rewrite Z.pow_add_r by lia. cbn [Z.pow]. lia. }
  assert (Hs12 : zksum M blc2 = zksum M blc) by lia.
  (* --- write 3: blc[M] -= 1.  This is the ONLY place the aliasing case
     [i + 1 = M] differs from the distinct case, and it differs only in the
     BOUND on [blc2 M] -- the delta is [-2^0 = -1] either way. --- *)
  assert (Hb2Mrange : 1 <= blc2 M <= 32770).
  { destruct (Z.eq_dec (i + 1) M) as [Halias|Hdist].
    - (* aliasing: write 2 landed on M, so blc2 M = blc M + 2 *)
      unfold blc2, zset.
      replace (M =? i + 1) with true by (symmetry; apply Z.eqb_eq; lia).
      rewrite Hu2. specialize (Hbnd (i + 1)); lia.
    - (* distinct: neither write touched M *)
      unfold blc2, blc1, zset.
      replace (M =? i + 1) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (M =? i) with false by (symmetry; apply Z.eqb_neq; lia).
      specialize (Hbnd M); lia. }
  assert (Hu3 : u16 (blc2 M - 1) = blc2 M - 1)
    by (unfold u16; apply Z.mod_small; lia).
  rewrite (zksum_zset_Z M blc2 M (u16 (blc2 M - 1))) by lia.
  rewrite Hu3. replace (M - M) with 0 by lia. cbn [Z.pow]. lia.
Qed.

(** ** 6. The whole loop: down by exactly the number of trips

    THREE THINGS THIS STATEMENT GETS RIGHT THAT MY FIRST TWO VERSIONS DID NOT.
    All three are registered traps in this fleet and I walked into all three; the
    third was one build away from being published as usable.

    (a) THE TRIP COUNT IS PINNED, not existential.  Version 1 concluded
    [exists trips, 1 <= trips /\ ... = zksum M blc - trips].  True and USELESS:
    a consumer must reach [<= 2 ^ 15], and "decreases by at least 1" cannot get
    there.  A lower bound on a decrease is not a bound on the result.

    (b) NO [Z] DIVISION.  The closed form is [(ov + 1) / 2], and [lia] does not
    reason about [/].  [gba_trips] counts by mirroring [gb_adjust]'s own
    recursion, so the arithmetic stays linear.

    (c) **VERSION 2 WAS VACUOUS AND I MEASURED IT RATHER THAN SHIPPING IT.**  It
    took the global hypothesis [forall b, GbaOk M b -> GbaOk M (gba_body M b)].
    That hypothesis is FALSE at [M = 15], which is the only [M] this campaign
    cares about, so every instance of the theorem was unusable while the file
    stayed green.  The witness is [probe/p8_hpres_refute.v], computed:

        blcD = zlist [0;1;0;0;0;0;0;0;0;0;0;0;0;0;0;1]
        gba_bits 15 blcD = 1        blcD 1 = 1     blcD 15 = 1     (GbaOk holds)
        gba_body 15 blcD 15 = 0                    (GbaOk FAILS on the successor)

    Mechanism: [gb_findbits] descends from [maxlen - 1] and stops at 1, so
    [bits + 1 = 2 <> maxlen] and the third write drives [blc[maxlen]] from 1 to
    0.  A global preservation hypothesis is the easiest kind to prove a theorem
    WITH and the easiest kind to be unable to discharge -- which is exactly the
    note huffman-id left in [GbRange.v] about [LenBound], one function away from
    here.  The fix is to require [GbaOk] only of the arrays the loop actually
    REACHES.

    WHAT THE [ov > 0] BRANCH STILL OWES, unchanged by any of this: (i) that the
    pre-adjust excess equals [gba_trips], which is a property of [gb_pass1]'s
    clamping and NOT of this function (see the [blcC] finding in the header), and
    (ii) [GbaChain] at the reached arrays. *)
Fixpoint gba_trips (f : nat) (ov : Z) : Z :=
  match f with
  | O => 0
  | S f' => if Z.ltb 2 ov then 1 + gba_trips f' (ov - 2) else 1
  end.

(** The side conditions along the arrays the loop actually visits. *)
Fixpoint GbaChain (f : nat) (M : Z) (blc : zarr) (ov : Z) : Prop :=
  match f with
  | O => True
  | S f' => GbaOk M blc
            /\ (if Z.ltb 2 ov
                then GbaChain f' M (gba_body M blc) (ov - 2)
                else True)
  end.

(** [gba_trips] and [GbaChain] unfolded ONE step, as lemmas.  A bare
    [cbn [gba_trips]] on [gba_trips (S (S f)) ov] unfolds TWICE -- [S f] is a
    constructor application, so the recursive call reduces too -- and the result
    no longer matches an induction hypothesis stated at [gba_trips (S f)].  That
    cost a build. *)
Lemma gba_trips_step : forall f ov,
  2 < ov -> gba_trips (S f) ov = 1 + gba_trips f (ov - 2).
Proof.
  intros f ov Hov. cbn [gba_trips].
  replace (Z.ltb 2 ov) with true by (symmetry; apply Z.ltb_lt; lia).
  reflexivity.
Qed.

Lemma gba_trips_last : forall f ov, ov <= 2 -> gba_trips (S f) ov = 1.
Proof.
  intros f ov Hov. cbn [gba_trips].
  replace (Z.ltb 2 ov) with false by (symmetry; apply Z.ltb_ge; lia).
  reflexivity.
Qed.

Lemma GbaChain_head : forall f M blc ov, GbaChain (S f) M blc ov -> GbaOk M blc.
Proof. intros f M blc ov H. cbn [GbaChain] in H. tauto. Qed.

Lemma GbaChain_tail : forall f M blc ov, 2 < ov ->
  GbaChain (S f) M blc ov -> GbaChain f M (gba_body M blc) (ov - 2).
Proof.
  intros f M blc ov Hov H. cbn [GbaChain] in H.
  replace (Z.ltb 2 ov) with true in H by (symmetry; apply Z.ltb_lt; lia).
  tauto.
Qed.

Theorem zksum_gb_adjust : forall f M blc ov,
  GbaChain (S f) M blc ov ->
  zksum M (gb_adjust (S f) M blc ov) = zksum M blc - gba_trips (S f) ov.
Proof.
  induction f as [|f IH]; intros M blc ov Hch.
  - pose proof (GbaChain_head 0 M blc ov Hch) as Hok.
    destruct (Z_lt_le_dec 2 ov) as [Hgt|Hle].
    + rewrite (gb_adjust_unfold_step 0 M blc ov Hgt).
      rewrite (gba_trips_step 0 ov Hgt).
      cbn [gb_adjust gba_trips].
      rewrite (zksum_gba_body M blc Hok). lia.
    + rewrite (gb_adjust_unfold_last 0 M blc ov Hle).
      rewrite (gba_trips_last 0 ov Hle).
      rewrite (zksum_gba_body M blc Hok). lia.
  - pose proof (GbaChain_head (S f) M blc ov Hch) as Hok.
    destruct (Z_lt_le_dec 2 ov) as [Hgt|Hle].
    + rewrite (gb_adjust_unfold_step (S f) M blc ov Hgt).
      rewrite (gba_trips_step (S f) ov Hgt).
      rewrite (IH M (gba_body M blc) (ov - 2)
                 (GbaChain_tail (S f) M blc ov Hgt Hch)).
      rewrite (zksum_gba_body M blc Hok). lia.
    + rewrite (gb_adjust_unfold_last (S f) M blc ov Hle).
      rewrite (gba_trips_last (S f) ov Hle).
      rewrite (zksum_gba_body M blc Hok). lia.
Qed.

(** The single-trip case, which needs NO chain at all -- [ov <= 2] means the loop
    never recurses, so [GbaOk] of the input is the whole side condition.  This is
    the form a consumer can use today, and [gbaok_blcA] below proves its
    hypothesis is satisfiable rather than leaving that to be assumed. *)
Corollary zksum_gb_adjust_one_trip : forall f M blc ov,
  ov <= 2 -> GbaOk M blc ->
  zksum M (gb_adjust (S f) M blc ov) = zksum M blc - 1.
Proof.
  intros f M blc ov Hle Hok.
  rewrite (gb_adjust_unfold_last f M blc ov Hle).
  exact (zksum_gba_body M blc Hok).
Qed.

(** ** 7. CONTROLS

    [gba_trips] is a definition I wrote, so it is tied to measured behaviour
    rather than trusted.  These agree with the three [gb_adjust] instances
    computed in [probe/p7_adjust_invariant.v] BEFORE any of this was proved:
    [ov = 2] gave a decrease of 1, [ov = 6] gave 3. *)
Example trips_ov1 : gba_trips (Z.to_nat 1 + 1) 1 = 1.
Proof. vm_compute. reflexivity. Qed.

Example trips_ov2 : gba_trips (Z.to_nat 2 + 1) 2 = 1.
Proof. vm_compute. reflexivity. Qed.

Example trips_ov6 : gba_trips (Z.to_nat 6 + 1) 6 = 3.
Proof. vm_compute. reflexivity. Qed.

(** The boundary that shows the count is not simply [ov / 2]: at [ov = 3] and
    [ov = 4] the loop makes the SAME number of trips. *)
Example trips_ov3 : gba_trips (Z.to_nat 3 + 1) 3 = 2.
Proof. vm_compute. reflexivity. Qed.

Example trips_ov4 : gba_trips (Z.to_nat 4 + 1) 4 = 2.
Proof. vm_compute. reflexivity. Qed.

(** NEGATIVE CONTROL on the fuel: starved fuel undercounts, so the [S f] shape
    and the caller's [Z.to_nat ov + 1] are load-bearing, not decoration. *)
Example trips_starved : gba_trips 1 6 = 1.
Proof. vm_compute. reflexivity. Qed.

(** A reusable bound for a [zlist]-backed array.  Stated with [Forall] rather
    than [In]: [In] over a sixteen-element list becomes a sixteen-way
    disjunction, and [lia] does not case-split disjunctions in hypotheses, so the
    [In] route needs an explicit cascade at every use site.  [Forall] is built
    once by [apply Forall_cons] and reused. *)
Lemma zlist_bound_of_Forall : forall l hi i,
  0 <= hi -> Forall (fun x => 0 <= x <= hi) l -> 0 <= zlist l i <= hi.
Proof.
  intros l hi i Hhi HF. unfold zlist.
  destruct (nth_in_or_default (Z.to_nat i) l 0) as [Hin|Hd].
  - rewrite Forall_forall in HF. apply HF, Hin.
  - rewrite Hd. lia.
Qed.

(** LIVENESS CONTROL, without which [zksum_gb_adjust_one_trip] could be as
    vacuous as version 2 was: [GbaOk] is INHABITED at [M = 15].  One code at each
    depth 1..14 and three at depth 15 -- the over-full profile from probe p7. *)
Definition blcA : zarr := zlist [0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;3].

Lemma gbaok_blcA : GbaOk 15 blcA.
Proof.
  assert (Hb  : gba_bits 15 blcA = 14) by (vm_compute; reflexivity).
  assert (H14 : blcA 14 = 1) by (vm_compute; reflexivity).
  assert (H15 : blcA 15 = 3) by (vm_compute; reflexivity).
  unfold GbaOk. rewrite Hb, H14, H15.
  (* NOT [repeat split]: it descends through the final [forall] and the
     [0 <= _] (an implication under the hood), leaving a goal about
     [(0 ?= _) = Gt] with the binder already consumed. Three explicit splits. *)
  split; [lia|]. split; [lia|]. split; [lia|].
  (* the global bound: every entry is either a list element or the default 0,
     and [nth_in_or_default] gives exactly that dichotomy -- cheaper and more
     robust than sixteen [destruct]s on [Z.to_nat b]. *)
  intro bb. unfold blcA.
  apply zlist_bound_of_Forall; [lia|].
  repeat (apply Forall_cons; [lia|]). apply Forall_nil.
Qed.

(** ...and the corollary FIRES at it, decreasing the sum by exactly one. *)
Example one_trip_at_blcA :
  zksum 15 (gb_adjust (Z.to_nat 2 + 1) 15 blcA 2) = zksum 15 blcA - 1.
Proof.
  replace (Z.to_nat 2 + 1)%nat with (S (Z.to_nat 2)) by lia.
  apply (zksum_gb_adjust_one_trip (Z.to_nat 2) 15 blcA 2); [lia|].
  exact gbaok_blcA.
Qed.

Print Assumptions zksum_over_zset_notin.
Print Assumptions zksum_over_zset_in.
Print Assumptions zksum_zset_in.
Print Assumptions gb_adjust_unfold_last.
Print Assumptions gb_adjust_unfold_step.
Print Assumptions zksum_gba_body.
Print Assumptions zksum_zset_Z.
Print Assumptions zksum_gb_adjust.
Print Assumptions zksum_gb_adjust_one_trip.
Print Assumptions gbaok_blcA.
Print Assumptions one_trip_at_blcA.
Print Assumptions trips_ov6.
