(** * OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel.ItGTblRev — bit reversal at a width, and the increment law for
      [it_rev_incr].  Layer 1 of the root-region COVERAGE development
      ([ItGTblGeom.v] is the geometry + Kraft mass, [ItGTblCover.v] the loop).

    GTBL-ARMS lane, 2026-08-18.  Own scratch, a working folder.

    THE OBLIGATION (lenext-repair's [LfxCoverStmt.v], md5 , statement
    theirs and adopted verbatim):

<<
      TblBitsPosBelow (root : Z) (t : ztbl) : Prop :=
        forall i, 0 <= i < 2 ^ root -> c_bits (t i) <> 0

      forall ty lens codes root0 t0 out,
        it_model ty lens codes root0 t0 = Some out -> o_ret out = 0 ->
        TblBitsPosBelow (o_bits out) (o_tbl out)
>>

    SPEC-SIDE ON PURPOSE.  This file is about [Inftrees] only.  It never
    mentions [ItModel], so the consumer (Inflate's [inf_decode], which reads a
    [ztbl]) does not wait on my model-to-model bridge for this fact, and the
    import discipline that governs [ItGTblBridge.v] does not apply here — there
    is only one model in scope.  The four small [Z.land]/[Z.shiftr] bridges in
    §2 are RE-DERIVED rather than imported from [ItGTblBridge.v] for exactly
    that reason: importing the bridge would pull [ItModel] in.

    THE FREE HALF.  Every write [inflate_table] performs stores a NONZERO bits
    field: all three branches of [it_here] set [b := s_len - s_drop]; the
    sub-table pointer write sets [bits := x_root]; [it_finish] sets
    [bits := s_len - s_drop]; and [mkCodeT]'s [u8] is the identity on
    [1 <= v <= 15].  So [c_bits <> 0] costs nothing and the whole difficulty is
    WHICH INDICES GET WRITTEN.  What this file delivers is therefore the
    stronger [1 <= c_bits], which also retires lenext-repair's [len_tbl_nonneg]
    on the root region (that premise is quantified over ALL [i], and for a
    built table with the decoder's arbitrary [t0] an unwritten entry's
    [c_bits] is whatever the caller left in [state->codes] — so the loop cannot
    produce it, and on the root region it is not needed).

    THE DESIGN — position, not sets.  [zrev] is bit reversal at a width; the
    loop's [huff] IS a position in the reversed order, and the covered part of
    the root table is an INITIAL SEGMENT in that order.  Tracking a scaled
    position needs no written set, hence neither [WroteProgression] nor
    [AgreeOrInit]; coverage is monotone because every write stores bits <> 0.

    DO NOT "simplify" [zrev] to [Z.rev]-style bit surgery: the [Z.odd]/[Z.div2]
    recursion is what makes [zrev_split] a two-line induction, and the split is
    the only nontrivial arithmetic in §1.

    DO NOT restate the Kraft mass here as a new notion when landing: [it_mass]
    (in [ItGTblGeom.v]) is the same function as [itk_sum] in the graded tree's
    [Spec/PngModel/InftreesBridge.v]:197-229, whose [itk_left_closed] gives
    [lft = 2^15 - mass] outright.  It is re-derived locally ONLY to keep this
    scratch chain at three spec files instead of six; the landing version should
    import [InftreesBridge] and delete the copy. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Base Inftrees.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Open Scope Z_scope.

(** ** 1.  Bit reversal at a width

    [zrev n h] reverses the low [n] bits of [h]: bit [i] of [h] becomes bit
    [n-1-i] of the result.  Width is a [nat] so the recursion is structural;
    the spec's lengths are [Z] and the conversion happens once, at §3. *)

Fixpoint zrev (n : nat) (h : Z) : Z :=
  match n with
  | O => 0
  | S k => (if Z.odd h then 2 ^ Z.of_nat k else 0) + zrev k (Z.div2 h)
  end.

Lemma pow2_pos_nat : forall k : nat, 0 < 2 ^ Z.of_nat k.
Proof. intros k. apply Z.pow_pos_nonneg; lia. Qed.

Lemma pow2_succ_nat : forall k : nat, 2 ^ Z.of_nat (S k) = 2 * 2 ^ Z.of_nat k.
Proof. intros k. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. reflexivity. Qed.

Lemma pow2_nz_nat : forall k : nat, (2 ^ Z.of_nat k =? 0) = false.
Proof. intros k. apply Z.eqb_neq. pose proof (pow2_pos_nat k). lia. Qed.

Lemma zrev_zero : forall n, zrev n 0 = 0.
Proof.
  induction n as [|k IH]; [reflexivity|].
  cbn [zrev]. change (Z.odd 0) with false. change (Z.div2 0) with 0.
  rewrite IH. reflexivity.
Qed.

Lemma zrev_nonneg : forall n h, 0 <= zrev n h.
Proof.
  induction n as [|k IH]; intros h; cbn [zrev]; [lia|].
  pose proof (IH (Z.div2 h)). pose proof (pow2_pos_nat k).
  destruct (Z.odd h); lia.
Qed.

Lemma zrev_lt : forall n h, zrev n h < 2 ^ Z.of_nat n.
Proof.
  induction n as [|k IH]; intros h; cbn [zrev].
  - change (Z.of_nat 0) with 0. rewrite Z.pow_0_r. lia.
  - pose proof (IH (Z.div2 h)). rewrite pow2_succ_nat.
    destruct (Z.odd h); lia.
Qed.

(** The workhorse: a value split at bit [k] reverses into a value split at bit
    [d] the other way round.  Everything else in §1 is a corollary. *)
Lemma zrev_split : forall (k d : nat) (a b : Z),
  0 <= a < 2 ^ Z.of_nat k ->
  zrev (k + d) (a + b * 2 ^ Z.of_nat k) = zrev k a * 2 ^ Z.of_nat d + zrev d b.
Proof.
  induction k as [|k' IH]; intros d a b Ha.
  - cbn [Nat.add zrev]. change (Z.of_nat 0) with 0 in *.
    rewrite Z.pow_0_r in Ha. assert (a = 0) by lia. subst a.
    rewrite Z.pow_0_r. replace (0 + b * 1) with b by ring. lia.
  - replace (S k' + d)%nat with (S (k' + d)) by lia.
    cbn [zrev].
    assert (Hodd : Z.odd (a + b * 2 ^ Z.of_nat (S k')) = Z.odd a).
    { rewrite pow2_succ_nat.
      replace (b * (2 * 2 ^ Z.of_nat k')) with (2 * (b * 2 ^ Z.of_nat k')) by ring.
      apply Z.odd_add_mul_2. }
    assert (Hdiv : Z.div2 (a + b * 2 ^ Z.of_nat (S k'))
                   = Z.div2 a + b * 2 ^ Z.of_nat k').
    { rewrite !Z.div2_div, pow2_succ_nat.
      replace (a + b * (2 * 2 ^ Z.of_nat k'))
        with (a + (b * 2 ^ Z.of_nat k') * 2) by ring.
      rewrite Z.div_add by lia. reflexivity. }
    assert (Ha2 : 0 <= Z.div2 a < 2 ^ Z.of_nat k').
    { rewrite Z.div2_div. pose proof (pow2_pos_nat k'). split.
      - apply Z.div_pos; lia.
      - apply Z.div_lt_upper_bound; [lia|]. rewrite <- pow2_succ_nat. lia. }
    rewrite Hodd, Hdiv, (IH d (Z.div2 a) b Ha2).
    rewrite Nat2Z.inj_add, Z.pow_add_r by lia.
    destruct (Z.odd a); ring.
Qed.

Lemma zrev_ones : forall n, zrev n (2 ^ Z.of_nat n - 1) = 2 ^ Z.of_nat n - 1.
Proof.
  induction n as [|k IH]; cbn [zrev].
  - change (Z.of_nat 0) with 0. rewrite Z.pow_0_r. lia.
  - pose proof (pow2_pos_nat k). rewrite pow2_succ_nat.
    assert (Hodd : Z.odd (2 * 2 ^ Z.of_nat k - 1) = true).
    { replace (2 * 2 ^ Z.of_nat k - 1) with (2 * (2 ^ Z.of_nat k - 1) + 1) by ring.
      apply Z.odd_odd. }
    assert (Hdiv : Z.div2 (2 * 2 ^ Z.of_nat k - 1) = 2 ^ Z.of_nat k - 1).
    { rewrite Z.div2_div.
      replace (2 * 2 ^ Z.of_nat k - 1) with ((2 ^ Z.of_nat k - 1) * 2 + 1) by ring.
      rewrite Z.div_add_l by lia. rewrite Z.div_small by lia. lia. }
    rewrite Hodd, Hdiv, IH. lia.
Qed.

Lemma zrev_one : forall k, zrev (S k) 1 = 2 ^ Z.of_nat k.
Proof.
  intros k. cbn [zrev]. change (Z.odd 1) with true. change (Z.div2 1) with 0.
  rewrite zrev_zero. lia.
Qed.

(** [2^(e+1) - 2] is "all bits but the lowest", which reverses to
    "all bits but the highest" = [2^e - 1].  This is the value the reversed
    counter holds just before it wraps at width [e+1]. *)
Lemma pow2_one : 2 ^ Z.of_nat 1 = 2.
Proof. reflexivity. Qed.

Lemma zrev_pow_minus_two : forall e,
  zrev (S e) (2 ^ Z.of_nat (S e) - 2) = 2 ^ Z.of_nat e - 1.
Proof.
  intros e. pose proof (pow2_pos_nat e).
  replace (S e) with (1 + e)%nat by lia.
  replace (2 ^ Z.of_nat (1 + e) - 2)
    with (0 + (2 ^ Z.of_nat e - 1) * 2 ^ Z.of_nat 1).
  (* [rewrite pow2_succ_nat] must NOT be left unqualified here: the numeral [1]
     IS [S O], so the unqualified rewrite fires on [2 ^ Z.of_nat 1] first and
     the next tactic then finds no [2 ^ Z.of_nat 1] to work on.  Explicit
     argument, and the literal rewritten first. *)
  2:{ replace (1 + e)%nat with (S e) by lia.
      rewrite pow2_one, (pow2_succ_nat e). ring. }
  (* Arguments given EXPLICITLY.  With [rewrite zrev_split by tac] the side
     condition is presented with [k] still an evar, so a tactic that names
     [2 ^ Z.of_nat 1] finds no such subterm; instantiating first removes the
     class of failure rather than this instance of it. *)
  rewrite (zrev_split 1 e 0 (2 ^ Z.of_nat e - 1) ltac:(rewrite pow2_one; lia)).
  rewrite zrev_zero, zrev_ones. lia.
Qed.

(** ** 2.  The [Z.land] / [Z.shiftr] bridges the scan needs

    Re-derived here (they also exist in [ItGTblBridge.v], which imports
    [ItModel] and so must not be imported into this file). *)

Lemma land_pow2_zero_iff : forall a n, 0 <= n ->
  Z.land a (2 ^ n) = 0 <-> Z.testbit a n = false.
Proof.
  intros a n Hn. split.
  - intros H.
    assert (Hb : Z.testbit (Z.land a (2 ^ n)) n = false) by (rewrite H; apply Z.bits_0).
    rewrite Z.land_spec, Z.pow2_bits_eqb in Hb by lia.
    rewrite Z.eqb_refl, andb_true_r in Hb. exact Hb.
  - intros H. apply Z.bits_inj'. intros k Hk.
    rewrite Z.bits_0, Z.land_spec, Z.pow2_bits_eqb by lia.
    destruct (Z.eqb_spec n k) as [->|Ne]; [rewrite H; reflexivity|].
    now rewrite andb_false_r.
Qed.

Lemma shiftr_pow2_succ : forall j, Z.shiftr (2 ^ Z.of_nat (S j)) 1 = 2 ^ Z.of_nat j.
Proof.
  intros j. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.pow_1_r.
  rewrite pow2_succ_nat, Z.mul_comm. apply Z.div_mul. lia.
Qed.

Lemma shift_down_zero : forall n huff, it_shift_down n huff 0 = 0.
Proof.
  intros n huff. destruct n; [reflexivity|].
  cbn. rewrite Z.land_0_r. reflexivity.
Qed.

Lemma land_ones_mod : forall a k, 0 <= k -> Z.land a (2 ^ k - 1) = a mod 2 ^ k.
Proof.
  intros a k Hk.
  replace (2 ^ k - 1) with (Z.ones k) by (rewrite Z.ones_equiv; lia).
  apply Z.land_ones; lia.
Qed.

(** One bit's worth of a modulus, the form the scan's induction consumes. *)
Lemma mod_succ_bit : forall (a : Z) (k : nat), 0 <= a ->
  a mod 2 ^ Z.of_nat (S k)
  = a mod 2 ^ Z.of_nat k
    + (if Z.testbit a (Z.of_nat k) then 2 ^ Z.of_nat k else 0).
Proof.
  intros a k Ha. pose proof (pow2_pos_nat k) as Hp.
  assert (Hb : Z.testbit a (Z.of_nat k) = Z.odd (a / 2 ^ Z.of_nat k)).
  { pose proof (Z.shiftr_spec a (Z.of_nat k) 0 ltac:(lia)) as Hs.
    rewrite Z.bit0_odd in Hs.
    rewrite Z.shiftr_div_pow2 in Hs by lia.
    rewrite Z.add_0_l in Hs. symmetry. exact Hs. }
  replace (2 ^ Z.of_nat (S k)) with (2 ^ Z.of_nat k * 2)
    by (rewrite pow2_succ_nat; ring).
  rewrite Z.rem_mul_r by lia.
  rewrite Zmod_odd, Hb.
  destruct (Z.odd (a / 2 ^ Z.of_nat k)); ring.
Qed.

(** ** 3.  What the downward scan finds

    [it_shift_down] walks [incr = 2^j] down while [huff] has that bit set.  So
    it returns [2^p] for the HIGHEST [p <= j] whose bit is clear — and the
    algebraic content, which is what the increment law consumes, is that
    [huff]'s bits strictly above [p] and up to [j] are all 1. *)

Lemma shift_down_spec : forall (j n : nat) (huff : Z),
  (S j <= n)%nat -> 0 <= huff ->
  ( it_shift_down n huff (2 ^ Z.of_nat j) = 0
    /\ huff mod 2 ^ Z.of_nat (S j) = 2 ^ Z.of_nat (S j) - 1 )
  \/ ( exists p : nat, (p <= j)%nat
       /\ it_shift_down n huff (2 ^ Z.of_nat j) = 2 ^ Z.of_nat p
       /\ huff mod 2 ^ Z.of_nat (S j)
          = huff mod 2 ^ Z.of_nat p
            + (2 ^ Z.of_nat (S j) - 2 ^ Z.of_nat (S p)) ).
Proof.
  induction j as [|j' IH]; intros n huff Hn Hh; destruct n as [|m]; [lia| |lia|].
  - (* position 0: the scan either stops here or bottoms out at incr = 0 *)
    cbn [it_shift_down].
    destruct (Z.eqb_spec (Z.land huff (2 ^ Z.of_nat 0)) 0) as [E|E].
    + right. exists 0%nat. split; [lia|]. split; [reflexivity|].
      rewrite (mod_succ_bit huff 0 Hh).
      rewrite (proj1 (land_pow2_zero_iff huff (Z.of_nat 0) ltac:(lia)) E).
      change (Z.of_nat 0) with 0. rewrite Z.pow_0_r, Z.mod_1_r.
      change (Z.of_nat 1) with 1. rewrite Z.pow_1_r. lia.
    + left.
      assert (Ht : Z.testbit huff (Z.of_nat 0) = true).
      { destruct (Z.testbit huff (Z.of_nat 0)) eqn:Hb; [reflexivity|].
        exfalso. apply E.
        apply (proj2 (land_pow2_zero_iff huff (Z.of_nat 0) ltac:(lia)) Hb). }
      change (Z.shiftr (2 ^ Z.of_nat 0) 1) with 0.
      rewrite shift_down_zero. split; [reflexivity|].
      rewrite (mod_succ_bit huff 0 Hh), Ht.
      change (Z.of_nat 0) with 0. rewrite Z.pow_0_r, Z.mod_1_r.
      change (Z.of_nat 1) with 1. rewrite Z.pow_1_r. lia.
  - (* position S j' *)
    cbn [it_shift_down].
    destruct (Z.eqb_spec (Z.land huff (2 ^ Z.of_nat (S j'))) 0) as [E|E].
    + right. exists (S j'). split; [lia|]. split; [reflexivity|].
      rewrite (mod_succ_bit huff (S j') Hh).
      rewrite (proj1 (land_pow2_zero_iff huff (Z.of_nat (S j')) ltac:(lia)) E).
      lia.
    + assert (Ht : Z.testbit huff (Z.of_nat (S j')) = true).
      { destruct (Z.testbit huff (Z.of_nat (S j'))) eqn:Hb; [reflexivity|].
        exfalso. apply E.
        apply (proj2 (land_pow2_zero_iff huff (Z.of_nat (S j')) ltac:(lia)) Hb). }
      rewrite shiftr_pow2_succ.
      assert (Hstep : huff mod 2 ^ Z.of_nat (S (S j'))
                      = huff mod 2 ^ Z.of_nat (S j') + 2 ^ Z.of_nat (S j'))
        by (rewrite (mod_succ_bit huff (S j') Hh), Ht; reflexivity).
      destruct (IH m huff ltac:(lia) Hh) as [[Hz Hmod] | [p [Hp [Heq Hmod]]]].
      * left. rewrite Hz. split; [reflexivity|].
        rewrite Hstep, Hmod, (pow2_succ_nat (S j')). lia.
      * right. exists p. split; [lia|]. split; [exact Heq|].
        rewrite Hstep, Hmod, (pow2_succ_nat (S j')). lia.
Qed.

(** ** 4.  THE INCREMENT LAW

    [it_rev_incr] is the successor of the bit-REVERSED counter: it either wraps
    (and then [huff] was all ones, i.e. the counter was at its last value) or
    it advances the reversed value by exactly one.  This is the fact that makes
    [huff] usable as a POSITION, and everything downstream rests on it. *)

Theorem zrev_it_rev_incr : forall (L : nat) (huff : Z),
  (1 <= L <= 17)%nat -> 0 <= huff < 2 ^ Z.of_nat L ->
  ( it_rev_incr huff (Z.of_nat L) = 0 /\ zrev L huff = 2 ^ Z.of_nat L - 1 )
  \/ ( 0 <= it_rev_incr huff (Z.of_nat L) < 2 ^ Z.of_nat L
       /\ zrev L (it_rev_incr huff (Z.of_nat L)) = zrev L huff + 1 ).
Proof.
  intros L huff [HL1 HL17] [Hh0 HhL].
  destruct L as [|L']; [lia|].
  assert (HmodL : huff mod 2 ^ Z.of_nat (S L') = huff)
    by (apply Z.mod_small; lia).
  unfold it_rev_incr.
  assert (Hsh : Z.shiftl 1 (Z.of_nat (S L') - 1) = 2 ^ Z.of_nat L').
  { rewrite Nat2Z.inj_succ.
    replace (Z.succ (Z.of_nat L') - 1) with (Z.of_nat L') by lia.
    rewrite Z.shiftl_mul_pow2 by lia. lia. }
  rewrite Hsh.
  destruct (shift_down_spec L' 17 huff ltac:(lia) Hh0)
    as [[Hz Hmod] | [p [Hp [Heq Hmod]]]].
  - (* WRAP: the scan bottomed out, so [huff] was all ones *)
    left. rewrite Hz. cbn zeta. split; [reflexivity|].
    rewrite HmodL in Hmod. rewrite Hmod. apply zrev_ones.
  - (* ADVANCE by one.  Widths are kept as [p] and [S e] from the start rather
       than as [p] and [d = L - p]: the two corollaries [zrev_one] and
       [zrev_pow_minus_two] are stated at [S _], and carrying [S e] avoids the
       positional [rewrite ... at 2 4] that a [d]-shaped proof needs. *)
    right. rewrite Heq. cbn zeta.
    rewrite HmodL in Hmod.
    assert (Hval : (if (2 ^ Z.of_nat p =? 0) then 0
                    else Z.land huff (2 ^ Z.of_nat p - 1) + 2 ^ Z.of_nat p)
                   = huff mod 2 ^ Z.of_nat p + 2 ^ Z.of_nat p).
    { rewrite pow2_nz_nat.
      rewrite (land_ones_mod huff (Z.of_nat p)) by lia. reflexivity. }
    rewrite Hval.
    set (m := huff mod 2 ^ Z.of_nat p).
    assert (Hm : 0 <= m < 2 ^ Z.of_nat p)
      by (unfold m; apply Z.mod_pos_bound, pow2_pos_nat).
    set (e := (S L' - p - 1)%nat).
    assert (Hpd : (p + S e = S L')%nat) by (unfold e; lia).
    assert (Hpow : 2 ^ Z.of_nat (S L') = 2 ^ Z.of_nat (S e) * 2 ^ Z.of_nat p).
    { rewrite <- Z.pow_add_r by lia. f_equal. lia. }
    assert (Hsp : 2 ^ Z.of_nat (S p) = 2 * 2 ^ Z.of_nat p) by apply pow2_succ_nat.
    pose proof (pow2_pos_nat p). pose proof (pow2_pos_nat e).
    pose proof (pow2_succ_nat e).
    assert (Hhuff : huff = m + (2 ^ Z.of_nat (S e) - 2) * 2 ^ Z.of_nat p).
    { assert (Hexp : (2 ^ Z.of_nat (S e) - 2) * 2 ^ Z.of_nat p
                     = 2 ^ Z.of_nat (S L') - 2 ^ Z.of_nat (S p))
        by (rewrite Hpow, Hsp; ring).
      rewrite Hexp. exact Hmod. }
    split.
    { assert (2 ^ Z.of_nat (S p) <= 2 ^ Z.of_nat (S L'))
        by (apply Z.pow_le_mono_r; lia).
      lia. }
    assert (Hnew : zrev (S L') (m + 2 ^ Z.of_nat p)
                   = zrev p m * 2 ^ Z.of_nat (S e) + 2 ^ Z.of_nat e).
    { replace (m + 2 ^ Z.of_nat p) with (m + 1 * 2 ^ Z.of_nat p) by ring.
      rewrite <- Hpd, (zrev_split p (S e) m 1 Hm).
      rewrite zrev_one. reflexivity. }
    assert (Hold : zrev (S L') huff
                   = zrev p m * 2 ^ Z.of_nat (S e) + (2 ^ Z.of_nat e - 1)).
    { rewrite Hhuff. rewrite <- Hpd, (zrev_split p (S e) m (2 ^ Z.of_nat (S e) - 2) Hm).
      rewrite zrev_pow_minus_two. reflexivity. }
    rewrite Hnew, Hold. lia.
Qed.

Set Printing Depth 10000000000.
Print Assumptions zrev_split.
Print Assumptions zrev_ones.
Print Assumptions zrev_pow_minus_two.
Print Assumptions mod_succ_bit.
Print Assumptions shift_down_spec.
Print Assumptions zrev_it_rev_incr.
