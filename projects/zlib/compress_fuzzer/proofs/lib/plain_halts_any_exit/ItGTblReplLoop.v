(** * OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.ItGTblReplLoop — the replication invariant, round the loop

    [ItGTblReplInv] pinned both ENDS of the induction ([repl_at_zero],
    [repl_at_full]) and validated the mid-loop clause's shape against the
    consumer's statement.  This file rides it round [it_loop]'s fixpoint and
    lands on huffman-id's obligation (b): [RootReplicated] for the root table of
    any accepted [it_model] call.

    ONE DESIGN CHANGE, AND IT IS THE WHOLE REASON THIS CLOSES.  [ReplBelow] — the
    clause validated in [ItGTblReplInv] — is NOT inductive on its own.  Writing
    its preservation proof, the case "[i] was written by an earlier code, [j] by
    the code being placed now" needs to contradict [j] lying in BOTH classes, and
    to do that from [ReplBelow] you need the earlier code's POSITION, which
    [ReplBelow] does not carry.  The fix is to carry the class-completeness
    statement instead:

      every done index's whole write class is done, and the table is CONSTANT
      on it

    ([ClassDone] below).  That form is inductive, and it pays for itself twice:

      - the cross case becomes free — a member of an earlier code's class is
        DONE at the old position, while every member of the current code's class
        is NOT (the window lemma below), so the two classes cannot meet;
      - therefore the induction consumes NO prefix-freeness.  [ItGTblRepl]'s
        [classes_disjoint_of_positions] / [prefix_free_of_positions] are true and
        landed, but the loop does not need them: class disjointness arrives from
        the position geometry through the completeness clause.  Recorded because
        it revises my own price: the "PRESERVED half" I costed as the
        prefix-freeness argument is not what the fixpoint asks for.

    ONE STRENGTHENING OF THE CARRIED STATE, and it is forced by the sub-table
    phase.  When the last code of a sub-table is placed, a ROOT unit completes
    without any root entry being written — the entry that becomes done is the
    sub-table POINTER, written on an earlier trip.  [ClassDone] then owes that
    index's class, which is a singleton exactly when the pointer's width is
    [root].  [CovInv]'s phase-2 clause gives only [1 <= c_bits <= root], so this
    file carries the exact form as a second conjunct ([ReplSt]).  It is cheap —
    the pointer is written by [mkCodeT _ (x_root c) _] — but it is not free, and
    a version of this file that assumed [CovInv] sufficed would fail in exactly
    the arm the incomplete-code fix-up lives in.

    GTBL-ARMS, 2026-08-18.  Scratch; not landed. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import Base Inftrees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import ItGTblRev ItGTblGeom ItGTblSortWin ItGTblCover ItGTblRepl
  ItGTblReplInv.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Open Scope Z_scope.

(* ######################################################################### *)
(* 1.  The inductive clause                                                   *)
(* ######################################################################### *)

(** "Every root index whose unit is done carries a COMPLETE, CONSTANT class."
    The class is taken at the entry's own width [c_bits (t i)], which is the
    width of the code that wrote it, so the clause says exactly what the fill
    loop does: one code writes one residue class, entirely, with one entry. *)
Definition ClassDone (root : Z) (t : ztbl) (P : Z) : Prop :=
  forall i, 0 <= i < 2 ^ root -> UnitDone root i P ->
    forall j, 0 <= j < 2 ^ root ->
      j mod 2 ^ (c_bits (t i)) = i mod 2 ^ (c_bits (t i)) ->
      UnitDone root j P /\ t j = t i.

(** THE BRIDGE TO THE LANDED ENDPOINT.  Everything downstream of here is already
    proved in [ItGTblReplInv]: [ReplBelow] at the full position IS
    [RootReplicated], and with positive widths it is [RootPrefixDet].  So this
    file's only obligation is [ClassDone] at the exit. *)
Lemma classdone_repl : forall root t P, ClassDone root t P -> ReplBelow root t P.
Proof.
  intros root t P H i j Hi Hj Hui Huj Hmod.
  destruct (H i Hi Hui j Hj (eq_sym Hmod)) as [_ Heq].
  rewrite Heq. reflexivity.
Qed.

Lemma unitdone_le : forall root i P Q,
  UnitDone root i P -> P <= Q -> UnitDone root i Q.
Proof. intros root i P Q H Hpq. unfold UnitDone in *. lia. Qed.

(** A unit is at least one root-scale block wide, so nothing is done at 0. *)
Lemma unit_pos_lower : forall root i, 0 <= root <= 15 ->
  2 ^ (15 - root) <= (zrev (Z.to_nat root) i + 1) * 2 ^ (15 - root).
Proof.
  intros root i Hr.
  pose proof (zrev_nonneg (Z.to_nat root) i) as H0.
  assert (Hp : 0 < 2 ^ (15 - root)) by (apply Z.pow_pos_nonneg; lia).
  assert (Hm : 1 * 2 ^ (15 - root) <= (zrev (Z.to_nat root) i + 1) * 2 ^ (15 - root))
    by (apply Z.mul_le_mono_nonneg_r; lia).
  lia.
Qed.

Lemma unit_not_done_zero : forall root i, 0 <= root <= 15 -> ~ UnitDone root i 0.
Proof.
  intros root i Hr H. unfold UnitDone in H.
  pose proof (unit_pos_lower root i Hr).
  assert (0 < 2 ^ (15 - root)) by (apply Z.pow_pos_nonneg; lia).
  lia.
Qed.

(** THE BASE CASE: at position 0 the clause is vacuous. *)
Lemma classdone_zero : forall root t, 0 <= root <= 15 -> ClassDone root t 0.
Proof.
  intros root t Hr i Hi Hui.
  exfalso. exact (unit_not_done_zero root i Hr Hui).
Qed.

(** A write at an index that is NOT done is invisible to the clause: no done
    index can be it, and no done index's class can contain it (the class of a
    done index is all-done).  This is how the sub-table POINTER write passes. *)
Lemma classdone_tset_undone : forall root t P k e,
  ClassDone root t P -> ~ UnitDone root k P -> ClassDone root (tset t k e) P.
Proof.
  intros root t P k e H Hk i Hi Hui j Hj Hmod.
  assert (Hik : i <> k) by (intro Heq; subst i; exact (Hk Hui)).
  rewrite (tset_other t k e i Hik) in Hmod |- *.
  destruct (H i Hi Hui j Hj Hmod) as [Hdj Heq].
  assert (Hjk : j <> k) by (intro Hq; subst j; exact (Hk Hdj)).
  rewrite (tset_other t k e j Hjk).
  split; [exact Hdj | exact Heq].
Qed.

(* ######################################################################### *)
(* 2.  THE MISSING GEOMETRY: the converse of [unit_cross_short]               *)
(* ######################################################################### *)

(** [ItGTblGeom]'s [unit_cross_short] says a NEWLY COMPLETED unit lies in the
    current code's class.  The induction also needs the other direction — every
    class member's unit lies in the code's interval, hence is not done before the
    trip and is done after it.  Together they say the newly-done set IS the class,
    which is what makes the two halves of the invariant meet.

    (Register: a one-directional geometry lemma gives coverage without
    disjointness; the pair is what composes.  [ItGTblRepl]'s [fill_class_iff]
    made the same point about the write set — this is the same shape one level
    up, about the position interval.) *)
Lemma class_unit_window : forall (R L : nat) (huff j : Z),
  (L <= R)%nat -> (R <= 15)%nat ->
  0 <= huff < 2 ^ Z.of_nat L ->
  0 <= j < 2 ^ Z.of_nat R ->
  j mod 2 ^ Z.of_nat L = huff ->
  zrev L huff * 2 ^ (15 - Z.of_nat L) < (zrev R j + 1) * 2 ^ (15 - Z.of_nat R)
  /\ (zrev R j + 1) * 2 ^ (15 - Z.of_nat R)
     <= zrev L huff * 2 ^ (15 - Z.of_nat L) + 2 ^ (15 - Z.of_nat L).
Proof.
  intros R L huff j HLR HR15 Hhuff Hj Hmod.
  assert (HDex : (L + (R - L))%nat = R) by lia.
  set (D := (R - L)%nat) in *.
  pose proof (pow2_pos_nat L) as HpL.
  pose proof (pow2_pos_nat D) as HpD.
  assert (HSpos : 0 < 2 ^ (15 - Z.of_nat R)) by (apply Z.pow_pos_nonneg; lia).
  assert (Hexp : 2 ^ (15 - Z.of_nat L) = 2 ^ (15 - Z.of_nat R) * 2 ^ Z.of_nat D).
  { rewrite <- Z.pow_add_r by lia. f_equal. unfold D. lia. }
  remember (j / 2 ^ Z.of_nat L) as b eqn:Hb.
  assert (Hjab : j = huff + b * 2 ^ Z.of_nat L).
  { subst b. pose proof (Z.div_mod j (2 ^ Z.of_nat L) ltac:(lia)) as Hdm.
    rewrite Hmod in Hdm. lia. }
  assert (Hsplit : zrev R j = zrev L huff * 2 ^ Z.of_nat D + zrev D b).
  { rewrite <- HDex, Hjab. exact (zrev_split L D huff b Hhuff). }
  pose proof (zrev_nonneg D b) as Hb0.
  pose proof (zrev_lt D b) as HbU.
  pose proof (zrev_nonneg L huff) as Hh0.
  rewrite Hexp, Hsplit. split; nia.
Qed.

(** And the long-code containment: a code narrower than [root] does not span a
    root unit, so its position sits INSIDE the unit of its own root prefix.  This
    is [unit_cross_long]'s two internal bounds, which that lemma did not export;
    the sub-table phase needs them to say the pointer index is not yet done. *)
Lemma pos_in_root_unit : forall (R L : nat) (huff : Z),
  (R <= L)%nat -> (L <= 15)%nat -> 0 <= huff < 2 ^ Z.of_nat L ->
  zrev R (huff mod 2 ^ Z.of_nat R) * 2 ^ (15 - Z.of_nat R)
    <= zrev L huff * 2 ^ (15 - Z.of_nat L)
  /\ zrev L huff * 2 ^ (15 - Z.of_nat L)
     < (zrev R (huff mod 2 ^ Z.of_nat R) + 1) * 2 ^ (15 - Z.of_nat R).
Proof.
  intros R L huff HRL HL15 Hhuff.
  assert (HDex : (R + (L - R))%nat = L) by lia.
  set (D := (L - R)%nat) in *.
  pose proof (pow2_pos_nat R) as HpR.
  pose proof (pow2_pos_nat D) as HpD.
  assert (HTpos : 0 < 2 ^ (15 - Z.of_nat L)) by (apply Z.pow_pos_nonneg; lia).
  assert (Hexp : 2 ^ Z.of_nat D * 2 ^ (15 - Z.of_nat L) = 2 ^ (15 - Z.of_nat R)).
  { rewrite <- Z.pow_add_r by lia. f_equal. unfold D. lia. }
  remember (huff mod 2 ^ Z.of_nat R) as low eqn:Hlow.
  remember (huff / 2 ^ Z.of_nat R) as q eqn:Hq.
  assert (Hlowr : 0 <= low < 2 ^ Z.of_nat R)
    by (subst low; apply Z.mod_pos_bound; lia).
  assert (Hhsplit : huff = low + q * 2 ^ Z.of_nat R).
  { subst low q. pose proof (Z.div_mod huff (2 ^ Z.of_nat R) ltac:(lia)) as Hdm. lia. }
  assert (Hrev : zrev L huff = zrev R low * 2 ^ Z.of_nat D + zrev D q).
  { rewrite <- HDex, Hhsplit. exact (zrev_split R D low q Hlowr). }
  pose proof (zrev_nonneg D q) as Hq0.
  pose proof (zrev_lt D q) as HqU.
  pose proof (zrev_nonneg R low) as Hl0.
  rewrite Hrev, <- Hexp. split; nia.
Qed.

(** The three geometry facts at the [Z] widths the invariant is stated in.  Done
    as separate adapters rather than by restating the lemmas: [zrev]'s recursion
    is on [nat] and every proof above needs it there, while [UnitDone] is
    [Z]-indexed because [CovInv] is. *)
Lemma class_window_z : forall root L huff j,
  1 <= L <= root -> root <= 15 -> 0 <= huff < 2 ^ L ->
  0 <= j < 2 ^ root -> j mod 2 ^ L = huff ->
  ~ UnitDone root j (zrev (Z.to_nat L) huff * 2 ^ (15 - L))
  /\ UnitDone root j (zrev (Z.to_nat L) huff * 2 ^ (15 - L) + 2 ^ (15 - L)).
Proof.
  intros root L huff j HL Hroot Hhuff Hj Hmod.
  pose proof (class_unit_window (Z.to_nat root) (Z.to_nat L) huff j
                ltac:(lia) ltac:(lia)) as Hw.
  rewrite (Z2Nat.id L) in Hw by lia.
  rewrite (Z2Nat.id root) in Hw by lia.
  destruct (Hw Hhuff Hj Hmod) as [H1 H2].
  unfold UnitDone. split; [lia | lia].
Qed.

Lemma unit_cross_short_z : forall root L huff j,
  1 <= L <= root -> root <= 15 -> 0 <= huff < 2 ^ L -> 0 <= j < 2 ^ root ->
  zrev (Z.to_nat L) huff * 2 ^ (15 - L)
    < (zrev (Z.to_nat root) j + 1) * 2 ^ (15 - root) ->
  (zrev (Z.to_nat root) j + 1) * 2 ^ (15 - root)
    <= zrev (Z.to_nat L) huff * 2 ^ (15 - L) + 2 ^ (15 - L) ->
  j mod 2 ^ L = huff.
Proof.
  intros root L huff j HL Hroot Hhuff Hj H1 H2.
  pose proof (unit_cross_short (Z.to_nat root) (Z.to_nat L) huff j
                ltac:(lia) ltac:(lia) ltac:(lia)) as Hc.
  rewrite (Z2Nat.id L) in Hc by lia.
  rewrite (Z2Nat.id root) in Hc by lia.
  exact (Hc Hhuff Hj H1 H2).
Qed.

Lemma unit_cross_long_z : forall root L huff j,
  1 <= root -> root < L -> L <= 15 -> 0 <= huff < 2 ^ L -> 0 <= j < 2 ^ root ->
  zrev (Z.to_nat L) huff * 2 ^ (15 - L)
    < (zrev (Z.to_nat root) j + 1) * 2 ^ (15 - root) ->
  (zrev (Z.to_nat root) j + 1) * 2 ^ (15 - root)
    <= zrev (Z.to_nat L) huff * 2 ^ (15 - L) + 2 ^ (15 - L) ->
  j = huff mod 2 ^ root.
Proof.
  intros root L huff j Hr1 HrL HL15 Hhuff Hj H1 H2.
  pose proof (unit_cross_long (Z.to_nat root) (Z.to_nat L) huff j
                ltac:(lia) ltac:(lia) ltac:(lia)) as Hc.
  rewrite (Z2Nat.id L) in Hc by lia.
  rewrite (Z2Nat.id root) in Hc by lia.
  exact (Hc Hhuff Hj H1 H2).
Qed.

(** Only the strict half of [pos_in_root_unit] is consumed (a sub-table's
    position has NOT completed its own root unit), so only that half is
    adapted. *)
Lemma pos_in_root_unit_z : forall root L huff,
  0 <= root <= L -> L <= 15 -> 0 <= huff < 2 ^ L ->
  zrev (Z.to_nat L) huff * 2 ^ (15 - L)
    < (zrev (Z.to_nat root) (huff mod 2 ^ root) + 1) * 2 ^ (15 - root).
Proof.
  intros root L huff Hr HL Hhuff.
  pose proof (pos_in_root_unit (Z.to_nat root) (Z.to_nat L) huff
                ltac:(lia) ltac:(lia)) as Hw.
  rewrite (Z2Nat.id L) in Hw by lia.
  rewrite (Z2Nat.id root) in Hw by lia.
  exact (proj2 (Hw Hhuff)).
Qed.

(* ######################################################################### *)
(* 3.  The two fill facts, as [ClassDone] steps                              *)
(* ######################################################################### *)

(** The write set, pointwise, in the two directions the step needs.  Both are
    [fill_class_iff] composed with [it_fill_hit] / [it_fill_miss]; named here so
    the step proof never re-derives the [exists k] form. *)
Lemma fill_class_hit : forall root L huff t h j,
  0 <= L <= root -> 0 <= huff < 2 ^ L -> 0 <= j < 2 ^ root ->
  j mod 2 ^ L = huff ->
  it_fill (Z.to_nat (2 ^ (root - L))) t huff (2 ^ L) h j = h.
Proof.
  intros root L huff t h j HL Hh Hj Hmod.
  assert (HpL : 0 < 2 ^ L) by (apply Z.pow_pos_nonneg; lia).
  assert (Hcast : Z.of_nat (Z.to_nat (2 ^ (root - L))) = 2 ^ (root - L))
    by (apply Z2Nat.id, Z.pow_nonneg; lia).
  destruct (proj1 (fill_class_iff root L huff j HL Hh) (conj Hj Hmod))
    as (k & Hk & ->).
  apply it_fill_hit; [exact HpL | rewrite Hcast; exact Hk].
Qed.

Lemma fill_class_miss : forall root L huff t h j,
  0 <= L <= root -> 0 <= huff < 2 ^ L -> j mod 2 ^ L <> huff ->
  it_fill (Z.to_nat (2 ^ (root - L))) t huff (2 ^ L) h j = t j.
Proof.
  intros root L huff t h j HL Hh Hne.
  assert (Hcast : Z.of_nat (Z.to_nat (2 ^ (root - L))) = 2 ^ (root - L))
    by (apply Z2Nat.id, Z.pow_nonneg; lia).
  apply it_fill_miss. intros k Hk Heq.
  rewrite Hcast in Hk.
  destruct (proj2 (fill_class_iff root L huff j HL Hh)
              (ex_intro _ k (conj Hk Heq))) as [_ Hm].
  exact (Hne Hm).
Qed.

(** THE ACHIEVED STEP: a short code's fill.  Its class becomes uniform (value
    [here], width [L]) and — by the window lemma — the class is exactly the set
    of units the position newly completes, so the clause holds at the advanced
    position with no bookkeeping about which codes came before. *)
Lemma classdone_fill_short : forall root L huff t here P,
  1 <= L <= root -> root <= 15 -> 0 <= huff < 2 ^ L ->
  c_bits here = L ->
  P = zrev (Z.to_nat L) huff * 2 ^ (15 - L) ->
  ClassDone root t P ->
  ClassDone root (it_fill (Z.to_nat (2 ^ (root - L))) t huff (2 ^ L) here)
    (P + 2 ^ (15 - L)).
Proof.
  intros root L huff t here P HL Hroot Hhuff Hbits Hpos H.
  subst P.
  assert (HpL : 0 < 2 ^ (15 - L)) by (apply Z.pow_pos_nonneg; lia).
  intros i Hi Hui j Hj Hmod.
  destruct (Z.eq_dec (i mod 2 ^ L) huff) as [Hic | Hic].
  - (* [i] is in the class the trip just wrote *)
    rewrite (fill_class_hit root L huff t here i ltac:(lia) Hhuff Hi Hic) in Hmod |- *.
    rewrite Hbits in Hmod.
    assert (Hjc : j mod 2 ^ L = huff) by (rewrite Hmod; exact Hic).
    rewrite (fill_class_hit root L huff t here j ltac:(lia) Hhuff Hj Hjc).
    split; [| reflexivity].
    exact (proj2 (class_window_z root L huff j HL Hroot Hhuff Hj Hjc)).
  - (* [i] is outside it: untouched, and already done before the trip *)
    rewrite (fill_class_miss root L huff t here i ltac:(lia) Hhuff Hic) in Hmod |- *.
    assert (Hdi : UnitDone root i (zrev (Z.to_nat L) huff * 2 ^ (15 - L))).
    { destruct (Z_le_gt_dec ((zrev (Z.to_nat root) i + 1) * 2 ^ (15 - root))
                  (zrev (Z.to_nat L) huff * 2 ^ (15 - L))) as [Hle | Hgt];
        [exact Hle | exfalso].
      apply Hic.
      apply (unit_cross_short_z root L huff i HL Hroot Hhuff Hi);
        [lia | unfold UnitDone in Hui; lia]. }
    destruct (H i Hi Hdi j Hj Hmod) as [Hdj Heq].
    assert (Hjc : j mod 2 ^ L <> huff).
    { intro Hq.
      exact (proj1 (class_window_z root L huff j HL Hroot Hhuff Hj Hq) Hdj). }
    rewrite (fill_class_miss root L huff t here j ltac:(lia) Hhuff Hjc).
    (* NOT [unitdone_le _ _ _ _ Hdj ltac:(lia)]: the target position is only
       determined by the expected type, so at the moment the inner [lia] runs its
       goal still carries an open metavariable and it reports "Cannot find
       witness" — a missing-hypothesis message for a fully-hypothesised goal. *)
    split; [unfold UnitDone in Hdj |- *; lia | exact Heq].
Qed.

(** THE OTHER STEP: a fill that does not touch the root region at all (the
    sub-table phase).  The table is unchanged there, and the position may still
    complete a root unit — the one whose pointer the earlier trip wrote.  That
    index's class is a singleton PROVIDED its width is exactly [root], which is
    the hypothesis this file carries in [ReplSt]. *)
Lemma classdone_fill_miss_root : forall root t t' P Q,
  0 <= root -> P <= Q ->
  (forall i, 0 <= i < 2 ^ root -> t' i = t i) ->
  (forall i, 0 <= i < 2 ^ root -> UnitDone root i Q -> ~ UnitDone root i P ->
     c_bits (t i) = root) ->
  ClassDone root t P -> ClassDone root t' Q.
Proof.
  intros root t t' P Q Hr Hpq Hagree Hnew H i Hi Hui j Hj Hmod.
  rewrite (Hagree i Hi) in Hmod |- *.
  rewrite (Hagree j Hj).
  destruct (Z_le_gt_dec ((zrev (Z.to_nat root) i + 1) * 2 ^ (15 - root)) P)
    as [Hold | Hfresh].
  - destruct (H i Hi Hold j Hj Hmod) as [Hdj Heq].
    split; [exact (unitdone_le root j P Q Hdj Hpq) | exact Heq].
  - assert (Hb : c_bits (t i) = root).
    { apply (Hnew i Hi Hui). unfold UnitDone. lia. }
    rewrite Hb in Hmod.
    rewrite (Z.mod_small j (2 ^ root)) in Hmod by exact Hj.
    rewrite (Z.mod_small i (2 ^ root)) in Hmod by exact Hi.
    subst j. split; [exact Hui | reflexivity].
Qed.

(* ######################################################################### *)
(* 4.  Reading the step's result WITHOUT [injection]                          *)
(* ######################################################################### *)

(** [it_step]'s [ItCont] records carry [it_subsz 16 ...], whose [left] argument
    doubles per level, and [injection] on such an equality does not terminate in
    practice (Inftrees.v:'s own note, measured > 150 s; this lane lost an
    afternoon to the same class three times).  So every field this file needs is
    read through a MATCH-VALUED predicate proved for [it_step c st] directly:
    the branch analysis happens where the scrutinee is still a term, the record
    literals are projected by [cbn], and nothing is ever inverted.

    [ItBreak] is the exception in the precedent ([cov_step_break] does
    [injection]) and it is sound there because that record has no [it_subsz] —
    but reading it the same way costs nothing and keeps one discipline. *)
Definition StepShape (c : ItCtx) (st : ItSt) (r : ItStep) : Prop :=
  match r with
  | ItCont s =>
      (s_tbl s = it_fill (Z.to_nat (Z.shiftl 1 (s_curr st) / Z.shiftl 1 (s_len st - s_drop st)))
                   (s_tbl st) (s_next st + Z.shiftr (s_huff st) (s_drop st))
                   (Z.shiftl 1 (s_len st - s_drop st)) (it_here c st)
       /\ s_low s = s_low st)
      \/ (exists e,
            s_tbl s = tset (it_fill (Z.to_nat (Z.shiftl 1 (s_curr st) / Z.shiftl 1 (s_len st - s_drop st)))
                              (s_tbl st) (s_next st + Z.shiftr (s_huff st) (s_drop st))
                              (Z.shiftl 1 (s_len st - s_drop st)) (it_here c st))
                        (s_low s) e
            /\ c_bits e = x_root c
            /\ x_root c < s_len s)
  | ItBreak s =>
      s_tbl s = it_fill (Z.to_nat (Z.shiftl 1 (s_curr st) / Z.shiftl 1 (s_len st - s_drop st)))
                  (s_tbl st) (s_next st + Z.shiftr (s_huff st) (s_drop st))
                  (Z.shiftl 1 (s_len st - s_drop st)) (it_here c st)
      /\ s_huff s = it_rev_incr (s_huff st) (s_len st)
      /\ s_len s = s_len st
      /\ s_drop s = s_drop st
      /\ s_next s = s_next st
  | ItOverflow _ => True
  end.

Lemma step_shape : forall c st, 0 <= x_root c < 256 -> StepShape c st (it_step c st).
Proof.
  intros c st Hr. unfold StepShape, it_step. cbv zeta.
  (* the [if]s are opened by a goal-shape match, so the branch conditions get
     NAMES without the enormous boolean expressions being written out here *)
  match goal with |- context [if ?b then _ else _] => destruct b eqn:Hbrk end.
  - cbn [s_tbl s_huff s_len s_drop s_next]. repeat split; reflexivity.
  - match goal with |- context [if ?b then _ else _] => destruct b eqn:Hsub end.
    + match goal with |- context [if ?b then _ else _] => destruct b eqn:Hen end.
      * exact I.
      * right. cbn [s_tbl s_low s_len].
        (* Take the witness FROM the goal, not by unification.  With [eexists]
           the [c_bits ?e = x_root c] goal is reachable while [?e] is still
           open, and [rewrite bits_mkCodeT] then has no [mkCodeT] to match —
           measured: that is exactly how this leaf first failed, and the error
           ("unable to unify x_root c with c_bits (mkCodeT ...)") named the
           SECOND conjunct while pointing at the FIRST bullet. *)
        match goal with
        | |- exists e, tset _ _ ?E = _ /\ _ => exists E
        end.
        split; [reflexivity | split].
        -- rewrite bits_mkCodeT by lia. reflexivity.
        -- apply Z.ltb_lt. destruct (andb_prop _ _ Hsub) as [Hl _]. exact Hl.
    + left. cbn [s_tbl s_low]. split; reflexivity.
Qed.

Lemma step_shape_cont : forall c st st',
  0 <= x_root c < 256 -> it_step c st = ItCont st' ->
  (s_tbl st' = it_fill (Z.to_nat (Z.shiftl 1 (s_curr st) / Z.shiftl 1 (s_len st - s_drop st)))
                 (s_tbl st) (s_next st + Z.shiftr (s_huff st) (s_drop st))
                 (Z.shiftl 1 (s_len st - s_drop st)) (it_here c st)
   /\ s_low st' = s_low st)
  \/ (exists e,
        s_tbl st' = tset (it_fill (Z.to_nat (Z.shiftl 1 (s_curr st) / Z.shiftl 1 (s_len st - s_drop st)))
                            (s_tbl st) (s_next st + Z.shiftr (s_huff st) (s_drop st))
                            (Z.shiftl 1 (s_len st - s_drop st)) (it_here c st))
                      (s_low st') e
        /\ c_bits e = x_root c
        /\ x_root c < s_len st').
Proof.
  intros c st st' Hr H.
  pose proof (step_shape c st Hr) as Hs. rewrite H in Hs. exact Hs.
Qed.

Lemma step_shape_break : forall c st st1,
  0 <= x_root c < 256 -> it_step c st = ItBreak st1 ->
  s_tbl st1 = it_fill (Z.to_nat (Z.shiftl 1 (s_curr st) / Z.shiftl 1 (s_len st - s_drop st)))
                (s_tbl st) (s_next st + Z.shiftr (s_huff st) (s_drop st))
                (Z.shiftl 1 (s_len st - s_drop st)) (it_here c st)
  /\ s_huff st1 = it_rev_incr (s_huff st) (s_len st)
  /\ s_len st1 = s_len st
  /\ s_drop st1 = s_drop st
  /\ s_next st1 = s_next st.
Proof.
  intros c st st1 Hr H.
  pose proof (step_shape c st Hr) as Hs. rewrite H in Hs. exact Hs.
Qed.

(** The counts, which every exit carrying a state shares, and the position
    advance that follows from them. *)
Definition it_cnt_of (r : ItStep) (d : zarr) : zarr :=
  match r with
  | ItCont s => s_count s
  | ItBreak s => s_count s
  | ItOverflow _ => d
  end.

Lemma it_step_cnt_all : forall c st,
  it_cnt_of (it_step c st)
    (zset (s_count st) (s_len st) (s_count st (s_len st) - 1))
  = zset (s_count st) (s_len st) (s_count st (s_len st) - 1).
Proof.
  intros c st. unfold it_cnt_of, it_step. cbv zeta.
  repeat (match goal with
          | |- context [if ?b then _ else _] => destruct b eqn:?
          end); cbn [s_count]; reflexivity.
Qed.

Lemma step_pos_advance_cont : forall M0 c st st',
  1 <= s_len st <= 15 -> it_step c st = ItCont st' ->
  Pos M0 st' = Pos M0 st + 2 ^ (15 - s_len st).
Proof.
  intros M0 c st st' Hlen H.
  pose proof (it_step_cnt_all c st) as Hc. rewrite H in Hc. cbn [it_cnt_of] in Hc.
  unfold Pos. rewrite Hc. apply pos_advance. lia.
Qed.

Lemma step_pos_advance_break : forall M0 c st st1,
  1 <= s_len st <= 15 -> it_step c st = ItBreak st1 ->
  Pos M0 st1 = Pos M0 st + 2 ^ (15 - s_len st).
Proof.
  intros M0 c st st1 Hlen H.
  pose proof (it_step_cnt_all c st) as Hc. rewrite H in Hc. cbn [it_cnt_of] in Hc.
  unfold Pos. rewrite Hc. apply pos_advance. lia.
Qed.

(** The break's own condition, read the same way: [ItBreak] happens only with the
    current length exhausted AND equal to [max], which is what makes the position
    at the break the whole Kraft mass. *)
Lemma step_break_cond : forall c st st1,
  it_step c st = ItBreak st1 ->
  zset (s_count st) (s_len st) (s_count st (s_len st) - 1) (s_len st) = 0
  /\ s_len st = x_max c.
Proof.
  intros c st st1 H. unfold it_step in H. cbv zeta in H.
  destruct (Z.eqb (zset (s_count st) (s_len st) (s_count st (s_len st) - 1) (s_len st)) 0)
    eqn:H1;
    destruct (Z.eqb (s_len st) (x_max c)) eqn:H2; cbn [andb] in H;
    try (exfalso;
         repeat match type of H with
                | (if ?b then _ else _) = _ => destruct b
                end;
         discriminate H).
  split; [apply Z.eqb_eq; exact H1 | apply Z.eqb_eq; exact H2].
Qed.

(* ######################################################################### *)
(* 5.  The trip                                                               *)
(* ######################################################################### *)

(** The [ClassDone] analogue of [cov_after_fill]: whatever the trip's fill does,
    the clause survives it at the advanced position.  The phase decides WHICH
    argument applies — phase 1 writes a class inside the root region (achieved),
    phase 2 writes only inside a sub-table and can complete a root unit whose
    entry is the pointer (preserved). *)
Lemma repl_after_fill : forall c cnt0 st,
  CovCtxOk c cnt0 -> CovInv c cnt0 st ->
  ClassDone (x_root c) (s_tbl st) (Pos (it_mass 15%nat 1 cnt0) st) ->
  (x_root c < s_len st -> c_bits (s_tbl st (s_low st)) = x_root c) ->
  ClassDone (x_root c)
    (it_fill (Z.to_nat (Z.shiftl 1 (s_curr st) / Z.shiftl 1 (s_len st - s_drop st)))
             (s_tbl st) (s_next st + Z.shiftr (s_huff st) (s_drop st))
             (Z.shiftl 1 (s_len st - s_drop st)) (it_here c st))
    (Pos (it_mass 15%nat 1 cnt0) st + 2 ^ (15 - s_len st)).
Proof.
  intros c cnt0 st Hctx Hinv Hcd Hptr.
  destruct Hctx as (Hroot & Hmask & Hmx & Hmxnz & Hmxz & Hnn & Hcodes & Hlens
                    & Hcnt0 & Hwork & Hupper & Hcase & Hrootmx).
  destruct Hinv as (Hlen & Hhuff & HwinL & HwinU & Hcnt & Hpos & Hcov & Hphase).
  destruct Hphase as [(Hd & Hc & Hnx & Hlow & Hlr) | (Hd & Hrl & Hnx & Hlow & Hlb)].
  - (* PHASE 1: the fill IS the root region's class for this code *)
    rewrite Hd, Hc, Hnx, Z.shiftr_0_r, Z.sub_0_r, Z.add_0_l.
    rewrite (shiftl1 (s_len st) ltac:(lia)), (shiftl1 (x_root c) ltac:(lia)).
    replace (2 ^ x_root c / 2 ^ s_len st) with (2 ^ (x_root c - s_len st))
      by (apply Z.pow_sub_r; lia).
    (* premise order is this file's own lemma's, so the bracket list is
       deterministic — not the [repeat split] order the fleet rule warns about *)
    apply (classdone_fill_short (x_root c) (s_len st) (s_huff st) (s_tbl st)
             (it_here c st) (Pos (it_mass 15%nat 1 cnt0) st));
      [ lia | lia | exact Hhuff
      | rewrite bits_here_val by (rewrite Hd; lia); rewrite Hd; lia
      | exact Hpos | exact Hcd ].
  - (* PHASE 2: the fill is entirely inside a sub-table *)
    assert (Hincr : Z.shiftl 1 (s_len st - s_drop st) = 2 ^ (s_len st - s_drop st))
      by (apply shiftl1; lia).
    assert (Hsr : 0 <= Z.shiftr (s_huff st) (s_drop st)).
    { rewrite Z.shiftr_div_pow2 by lia. apply Z.div_pos; [lia | apply pow2_pos_z; lia]. }
    assert (Hp15 : 0 < 2 ^ (15 - s_len st)) by (apply pow2_pos_z; lia).
    apply (classdone_fill_miss_root (x_root c) (s_tbl st)
             (it_fill (Z.to_nat (Z.shiftl 1 (s_curr st) / Z.shiftl 1 (s_len st - s_drop st)))
                (s_tbl st) (s_next st + Z.shiftr (s_huff st) (s_drop st))
                (Z.shiftl 1 (s_len st - s_drop st)) (it_here c st))
             (Pos (it_mass 15%nat 1 cnt0) st)
             (Pos (it_mass 15%nat 1 cnt0) st + 2 ^ (15 - s_len st))).
    + lia.
    + lia.
    + (* the root region is below the fill's base index *)
      intros i Hi. apply fill_miss_below;
        [ rewrite Hincr; apply pow2_pos_z; lia | lia ].
    + (* a newly completed root unit is this sub-table's own prefix, and that
         entry is the POINTER, whose width is exactly [root] *)
      intros i Hi Hdq Hdp.
      assert (H1 : zrev (Z.to_nat (s_len st)) (s_huff st) * 2 ^ (15 - s_len st)
                   < (zrev (Z.to_nat (x_root c)) i + 1) * 2 ^ (15 - x_root c)).
      { unfold UnitDone in Hdp. rewrite Hpos in Hdp. lia. }
      assert (H2 : (zrev (Z.to_nat (x_root c)) i + 1) * 2 ^ (15 - x_root c)
                   <= zrev (Z.to_nat (s_len st)) (s_huff st) * 2 ^ (15 - s_len st)
                      + 2 ^ (15 - s_len st)).
      { unfold UnitDone in Hdq. rewrite Hpos in Hdq. lia. }
      assert (Hi0 : i = s_huff st mod 2 ^ x_root c)
        by (apply (unit_cross_long_z (x_root c) (s_len st) (s_huff st) i);
            [lia | lia | lia | lia | lia | exact H1 | exact H2]).
      rewrite Hi0, <- Hlow. apply Hptr. lia.
    + exact Hcd.
Qed.

(** The state-level invariant this file carries: the clause, plus the exact width
    of the current sub-table's pointer (see the header — [CovInv] gives only the
    range, and the singleton-class argument needs the equality). *)
Definition ReplSt (c : ItCtx) (cnt0 : zarr) (st : ItSt) : Prop :=
  ClassDone (x_root c) (s_tbl st) (Pos (it_mass 15%nat 1 cnt0) st)
  /\ (x_root c < s_len st -> c_bits (s_tbl st (s_low st)) = x_root c).

(** THE PRESERVED STEP. *)
Lemma repl_step_cont : forall c cnt0 st st',
  CovCtxOk c cnt0 -> CovInv c cnt0 st -> ReplSt c cnt0 st ->
  it_step c st = ItCont st' -> ReplSt c cnt0 st'.
Proof.
  intros c cnt0 st st' Hctx Hinv [Hcd Hptr] Hstep.
  pose proof (repl_after_fill c cnt0 st Hctx Hinv Hcd Hptr) as Hfill.
  pose proof (cov_step_cont c cnt0 st st' Hctx Hinv Hstep) as Hinv'.
  pose proof Hctx as Hctx2. pose proof Hinv as Hinv2.
  destruct Hctx as (Hroot & Hmask & Hmx & Hmxnz & Hmxz & Hnn & Hcodes & Hlens
                    & Hcnt0 & Hwork & Hupper & Hcase & Hrootmx).
  destruct Hinv as (Hlen & Hhuff & HwinL & HwinU & Hcnt & Hpos & Hcov & Hphase).
  assert (Hpos' : Pos (it_mass 15%nat 1 cnt0) st'
                  = Pos (it_mass 15%nat 1 cnt0) st + 2 ^ (15 - s_len st))
    by (apply (step_pos_advance_cont _ c st st'); [lia | exact Hstep]).
  destruct (Hinv') as (Hlen' & Hhuff' & _ & _ & _ & Hpos'' & Hcov' & Hphase').
  destruct (step_shape_cont c st st' ltac:(lia) Hstep)
    as [[Htbl Hlow'] | (e & Htbl & Hbe & Hlt')].
  - (* no sub-table was created: the table is exactly the fill *)
    split.
    + rewrite Htbl, Hpos'. exact Hfill.
    + intros Hlt.
      (* [st'] is then in the sub-table phase, and so was [st]: the phase-1
         sentinel cannot be a root prefix, which is the mechanical form of "a
         sub-table is entered only through the [tset] branch" *)
      destruct Hphase' as [(_ & _ & _ & _ & Hlr') | (Hd' & Hrl' & Hnx' & Hlow2' & Hlb')];
        [lia|].
      assert (Hmodlt : 0 <= s_huff st' mod 2 ^ x_root c < 2 ^ x_root c)
        by (apply Z.mod_pos_bound, pow2_pos_z; lia).
      assert (Hle15 : 2 ^ x_root c <= 2 ^ 15) by (apply Z.pow_le_mono_r; lia).
      destruct Hphase as [(Hd & Hc & Hnx & Hlow & Hlr) | (Hd & Hrl & Hnx & Hlow & Hlb)].
      * exfalso. rewrite Hlow' , Hlow, Hlow2' in *. cbn in *. lia.
      * rewrite Htbl, Hlow'.
        assert (Hlowlt : 0 <= s_low st < 2 ^ x_root c)
          by (rewrite Hlow; apply Z.mod_pos_bound, pow2_pos_z; lia).
        assert (Hsr : 0 <= Z.shiftr (s_huff st) (s_drop st)).
        { rewrite Z.shiftr_div_pow2 by lia.
          apply Z.div_pos; [lia | apply pow2_pos_z; lia]. }
        rewrite fill_miss_below;
          [ apply Hptr; lia
          | rewrite (shiftl1 (s_len st - s_drop st) ltac:(lia)); apply pow2_pos_z; lia
          | lia ].
  - (* a sub-table WAS created: one extra write, at an index that is not done *)
    assert (Hnotdone : ~ UnitDone (x_root c) (s_low st')
                          (Pos (it_mass 15%nat 1 cnt0) st')).
    { destruct Hphase' as [(_ & _ & _ & _ & Hlr') | (Hd' & Hrl' & Hnx' & Hlow2' & Hlb')];
        [lia|].
      unfold UnitDone. rewrite Hpos'', Hlow2'.
      pose proof (pos_in_root_unit_z (x_root c) (s_len st') (s_huff st')
                    ltac:(lia) ltac:(lia) Hhuff') as Hlt2.
      lia. }
    split.
    + rewrite Htbl. apply classdone_tset_undone; [rewrite Hpos'; exact Hfill | exact Hnotdone].
    + intros _. rewrite Htbl, tset_same. exact Hbe.
Qed.

(** THE EXIT.  Two arms, and they close differently: for a COMPLETE code the
    position reaches [2 ^ 15], the reversed counter must have wrapped, so
    [it_finish] is the identity and the clause at the full position IS the
    consumer's statement.  For the one incomplete code zlib accepts the root is
    1 and the coverage bound already forces both widths to 1, so replication is
    immediate and no clause is needed there at all. *)
Lemma repl_step_break : forall c cnt0 st st1,
  CovCtxOk c cnt0 -> CovInv c cnt0 st -> ReplSt c cnt0 st ->
  it_step c st = ItBreak st1 ->
  RootReplicated (it_finish st1) (x_root c).
Proof.
  intros c cnt0 st st1 Hctx Hinv [Hcd Hptr] Hstep.
  pose proof (repl_after_fill c cnt0 st Hctx Hinv Hcd Hptr) as Hfill.
  pose proof (cov_step_break c cnt0 st st1 Hctx Hinv Hstep) as Hbits.
  pose proof Hctx as Hctx2. pose proof Hinv as Hinv2.
  destruct Hctx as (Hroot & Hmask & Hmx & Hmxnz & Hmxz & Hnn & Hcodes & Hlens
                    & Hcnt0 & Hwork & Hupper & Hcase & Hrootmx).
  destruct Hinv as (Hlen & Hhuff & HwinL & HwinU & Hcnt & Hpos & Hcov & Hphase).
  destruct Hcase as [Hfull | [Hmx1 Hhalf]].
  - (* COMPLETE *)
    destruct (step_break_cond c st st1 Hstep) as [Hhit Hmxeq].
    destruct (step_shape_break c st st1 ltac:(lia) Hstep)
      as (Htbl & Hh1 & Hlen1 & Hdrop1 & Hnext1).
    (* every count is exhausted at the break, so the position is the whole mass *)
    assert (Hcnt1 : forall l, 1 <= l <= 15 ->
              zset (s_count st) (s_len st) (s_count st (s_len st) - 1) l = 0).
    { intros l Hl. unfold zset.
      destruct (Z.eqb_spec l (s_len st)) as [->|Hne].
      - unfold zset in Hhit. rewrite Z.eqb_refl in Hhit. exact Hhit.
      - rewrite (Hcnt l Hl).
        destruct (Z.ltb_spec l (s_len st)) as [H1|H1]; [reflexivity|].
        destruct (Z.eqb_spec l (s_len st)) as [H2|H2]; [contradiction|].
        apply Hmxz. lia. }
    assert (Hmass0 : it_mass 15%nat 1
              (zset (s_count st) (s_len st) (s_count st (s_len st) - 1)) = 0)
      by (apply it_mass_zero_on; intros i Hi; apply Hcnt1; cbn in Hi; lia).
    assert (Hposbrk : Pos (it_mass 15%nat 1 cnt0) st + 2 ^ (15 - s_len st) = 2 ^ 15).
    { rewrite <- Hfull. unfold Pos.
      rewrite <- (pos_advance (it_mass 15%nat 1 cnt0) (s_count st) (s_len st) ltac:(lia)).
      rewrite Hmass0. ring. }
    (* the reversed counter wrapped: the position could not have advanced past
       the whole table *)
    assert (Hzfull : zrev (Z.to_nat (s_len st)) (s_huff st) = 2 ^ s_len st - 1).
    { assert (Hsplit : 2 ^ 15 = 2 ^ s_len st * 2 ^ (15 - s_len st))
        by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
      assert (Hp : 0 < 2 ^ (15 - s_len st)) by (apply pow2_pos_z; lia).
      rewrite Hpos in Hposbrk. nia. }
    assert (Hhuff'' : 0 <= s_huff st < 2 ^ Z.of_nat (Z.to_nat (s_len st)))
      by (rewrite (to_nat_pow (s_len st) ltac:(lia)); exact Hhuff).
    pose proof (zrev_it_rev_incr (Z.to_nat (s_len st)) (s_huff st)
                  ltac:(lia) Hhuff'') as Hinc.
    rewrite (Z2Nat.id (s_len st)) in Hinc by lia.
    assert (Hh0 : it_rev_incr (s_huff st) (s_len st) = 0).
    { destruct Hinc as [[Hw _] | [_ Hgood]]; [exact Hw | exfalso].
      pose proof (zrev_lt (Z.to_nat (s_len st))
                    (it_rev_incr (s_huff st) (s_len st))) as Hlt.
      rewrite (to_nat_pow (s_len st) ltac:(lia)) in Hlt.
      rewrite Hzfull in Hgood. lia. }
    (* so the fix-up writes nothing *)
    assert (Hfin : it_finish st1 = s_tbl st1).
    { unfold it_finish. rewrite Hh1, Hh0, Z.eqb_refl. reflexivity. }
    rewrite Hfin, Htbl.
    apply (repl_at_full (x_root c) _ ltac:(lia)).
    apply classdone_repl.
    rewrite <- Hposbrk. exact Hfill.
  - (* INCOMPLETE-BUT-ACCEPTED: [max = 1], hence [root = 1], hence every root
       width is 1 by the coverage bound and replication needs no geometry *)
    intros i j Hi Hj Hmod.
    pose proof (Hbits i Hi) as Hbi.
    pose proof (Hbits j Hj) as Hbj.
    lia.
Qed.

(** THE LOOP.  Bookkeeping, as priced: both per-step lemmas above are stated
    against the same carried state, so this is [cov_loop] with one more
    invariant threaded. *)
Lemma repl_loop : forall n c cnt0 st st1,
  CovCtxOk c cnt0 -> CovInv c cnt0 st -> ReplSt c cnt0 st ->
  it_loop n c st = Some (ItBreak st1) ->
  RootReplicated (it_finish st1) (x_root c).
Proof.
  induction n as [|k IH]; intros c cnt0 st st1 Hctx Hinv Hrepl Hloop;
    cbn [it_loop] in Hloop; [discriminate Hloop|].
  destruct (it_step c st) as [st'|st'|t] eqn:Hs.
  - apply (IH c cnt0 st' st1 Hctx
            (cov_step_cont c cnt0 st st' Hctx Hinv Hs)
            (repl_step_cont c cnt0 st st' Hctx Hinv Hrepl Hs) Hloop).
  - injection Hloop as <-.
    apply (repl_step_break c cnt0 st _ Hctx Hinv Hrepl Hs).
  - discriminate Hloop.
Qed.

(* ######################################################################### *)
(* 6.  The prologue, and the theorem the consumer instantiates                *)
(* ######################################################################### *)

(** [it_pre]'s [PreGo] state, in the two fields the entry conditions need.  Same
    dance as [ItGTblRepl]'s [it_pre_go_tbl]: destruct the branch booleans without
    reducing them, invert the constructor with a lemma proved ON VARIABLES, take
    the field with [cbn] on a record literal. *)
Lemma it_pre_go_start : forall ty lens codes root0 t0 c st,
  it_pre ty lens codes root0 t0 = PreGo c st ->
  s_huff st = 0 /\ s_next st = 0.
Proof.
  intros ty lens codes root0 t0 c st H.
  unfold it_pre in H. cbv zeta in H.
  destruct (Z.eqb (it_findmax 15%nat MAXBITS (it_count (Z.to_nat codes) 0 lens zzero)) 0);
    [discriminate H|].
  destruct (it_kraft 15%nat 1 1 (it_count (Z.to_nat codes) 0 lens zzero)) as [lft|];
    [|discriminate H].
  destruct (it_incomplete ty lft _); [discriminate H|].
  destruct (it_enough ty _); [discriminate H|].
  apply prego_inj_st in H. rewrite <- H. cbn [s_huff s_next].
  split; reflexivity.
Qed.

(** The entry condition, and it is the cheap end: the initial position is 0, so
    the clause is vacuous, and the initial state cannot be in the sub-table phase
    because that phase needs [2 ^ root <= next] and [next] starts at 0.  (The
    second half is why [it_pre_go_start] reads [s_next] as well as [s_huff]:
    [CovInv]'s phase disjunction alone does not say which side the start is on.) *)
Lemma repl_pre : forall ty lens codes root0 t0 c st,
  0 <= codes ->
  (forall i, 0 <= i < codes -> 0 <= lens i <= 15) ->
  1 <= root0 <= 15 ->
  it_pre ty lens codes root0 t0 = PreGo c st ->
  ReplSt c (sw_cnt lens codes) st.
Proof.
  intros ty lens codes root0 t0 c st Hcodes Hlens Hroot0 Hpre.
  destruct (cov_pre ty lens codes root0 t0 c st Hcodes Hlens Hroot0 Hpre)
    as [Hctx Hinv].
  destruct (it_pre_go_start ty lens codes root0 t0 c st Hpre) as [Hh Hnx].
  destruct Hctx as (Hroot & _).
  destruct Hinv as (Hlen & Hhuff & _ & _ & _ & Hpos & _ & Hphase).
  assert (Hp0 : Pos (it_mass 15%nat 1 (sw_cnt lens codes)) st = 0).
  { rewrite Hpos, Hh, zrev_zero. ring. }
  split.
  - rewrite Hp0. apply classdone_zero. lia.
  - intros Hlt. exfalso.
    destruct Hphase as [(_ & _ & _ & _ & Hlr) | (_ & _ & Hnx2 & _ & _)]; [lia|].
    assert (0 < 2 ^ x_root c) by (apply pow2_pos_z; lia).
    rewrite Hnx in Hnx2. lia.
Qed.

(** THE DELIVERABLE, in [it_covers_root_pos]'s shape: root-table replication for
    every accepted [inflate_table] call.  This is huffman-id's obligation (b)
    reduced to their own words — no premise on the caller's table, and none on
    the code set beyond what [it_wf] already gives.

    The [PreEmpty] arm is not a formality: the [max = 0] path writes two
    invalid-code markers and returns [*bits = 1], and both entries have width 1,
    so replication holds there for a different reason than in the loop.  A
    theorem stated only for the loop would leave the empty-code call — which the
    decoder does make — outside its scope. *)
Theorem it_repl_root : forall ty lens codes root0 t0 out,
  0 <= codes ->
  (forall i, 0 <= i < codes -> 0 <= lens i <= 15) ->
  1 <= root0 <= 15 ->
  it_model ty lens codes root0 t0 = Some out ->
  o_ret out = 0 ->
  RootReplicated (o_tbl out) (o_bits out).
Proof.
  intros ty lens codes root0 t0 out Hcodes Hlens Hroot0 Hmodel Hret.
  unfold it_model in Hmodel.
  destruct (it_pre ty lens codes root0 t0) as [ | temp | | c st] eqn:Hpre.
  - (* PreErr *) injection Hmodel as <-. cbn in Hret. lia.
  - (* PreEmpty *)
    rewrite (it_pre_empty_shape ty lens codes root0 t0 temp Hpre) in Hmodel.
    injection Hmodel as <-. cbn [o_tbl o_bits].
    intros i j Hi Hj Hmod.
    assert (Hb : forall k, 0 <= k < 2 ^ 1 ->
              c_bits (tset (tset t0 0 (mkCodeT 64 1 0)) 1 (mkCodeT 64 1 0) k) = 1).
    { intros k Hk. change (2 ^ 1) with 2 in Hk.
      destruct (Z.eq_dec k 1) as [->|H1].
      - rewrite tset_same, bits_mkCodeT by lia. reflexivity.
      - rewrite tset_other by lia.
        assert (Hk0 : k = 0) by lia. rewrite Hk0.
        rewrite tset_same, bits_mkCodeT by lia. reflexivity. }
    rewrite (Hb i Hi), (Hb j Hj). reflexivity.
  - (* PreOver *) injection Hmodel as <-. cbn in Hret. lia.
  - (* PreGo *)
    destruct (cov_pre ty lens codes root0 t0 c st Hcodes Hlens Hroot0 Hpre)
      as [Hctx Hinv].
    pose proof (repl_pre ty lens codes root0 t0 c st Hcodes Hlens Hroot0 Hpre) as Hrepl.
    destruct (it_loop (S (Z.to_nat codes)) c st) as [[st'|st'|tt]|] eqn:Hloop;
      try discriminate Hmodel;
      injection Hmodel as <-;
      try (cbn in Hret; lia).
    cbn [o_tbl o_bits].
    apply (repl_loop (S (Z.to_nat codes)) c (sw_cnt lens codes) st st'
             Hctx Hinv Hrepl Hloop).
Qed.

(** And the DIRECTIONAL form huffman-id's fetch loop instantiates ([k] quantified,
    not fixed at the entry's width), chained through the reduction in [ItGTblRepl]
    whose positivity premise is [it_covers_root_pos]'s conclusion — so the
    consumer pays nothing extra for it. *)
Corollary it_prefixdet_root : forall ty lens codes root0 t0 out,
  0 <= codes ->
  (forall i, 0 <= i < codes -> 0 <= lens i <= 15) ->
  1 <= root0 <= 15 ->
  it_model ty lens codes root0 t0 = Some out ->
  o_ret out = 0 ->
  RootPrefixDet (o_tbl out) (o_bits out).
Proof.
  intros ty lens codes root0 t0 out Hcodes Hlens Hroot0 Hmodel Hret.
  apply root_repl_gives_prefixdet.
  - intros i Hi.
    pose proof (it_covers_root_pos ty lens codes root0 t0 out
                  Hcodes Hlens Hroot0 Hmodel Hret i Hi). lia.
  - exact (it_repl_root ty lens codes root0 t0 out Hcodes Hlens Hroot0 Hmodel Hret).
Qed.

(* ######################################################################### *)
(* 7.  AN INSTANTIATION WITNESS, AT A NON-DIAGONAL PAIR                       *)
(* ######################################################################### *)

(** rt-scout's gate, sharpened for THIS statement.  [ItGTblCover]'s witness
    ([lens_two_ones], root 1) cannot serve here: at root 1 with both widths 1,
    [RootReplicated]'s hypothesis [i mod 2 = j mod 2] forces [i = j], so that
    call would only ever instantiate the reflexive case and a theorem that said
    nothing about distinct indices would pass it.  (Registered: an insensitive
    instance measures the instrument, not the claim.)

    So the witness is a code with a SHORT code in it — [1;2;2] at [root0 = 2],
    complete by Kraft — where the one-bit code occupies root indices 0 AND 2.
    Measured, not assumed (probe/ReplWitnessProbe.v): [o_ret = 0], [o_bits = 2],
    entries [(bits,val) = (1,1);(2,2);(1,1);(2,3)].  The pair [(0,2)] is distinct,
    its hypothesis genuinely holds, and the conclusion below is taken FROM the
    theorem rather than from the table dump. *)
Definition lens_one_two_two : zarr := zlist [1;2;2].

Example it_repl_root_instantiated :
  exists out,
    it_model CT_DISTS lens_one_two_two 3 2 tnone = Some out
    /\ o_ret out = 0
    /\ o_bits out = 2
    /\ c_bits (o_tbl out 0) = 1
    /\ 0 mod 2 ^ (c_bits (o_tbl out 0)) = 2 mod 2 ^ (c_bits (o_tbl out 0))
    /\ c_bits (o_tbl out 2) = c_bits (o_tbl out 0).
Proof.
  assert (H3 : 0 <= 3) by lia.
  assert (Hr2 : 1 <= 2 <= 15) by lia.
  assert (Hlens : forall i, 0 <= i < 3 -> 0 <= lens_one_two_two i <= 15).
  { intros i Hi. assert (Hd : i = 0 \/ i = 1 \/ i = 2) by lia.
    destruct Hd as [H0 | [H1 | H2]].
    - rewrite H0. assert (E : lens_one_two_two 0 = 1) by reflexivity. rewrite E. lia.
    - rewrite H1. assert (E : lens_one_two_two 1 = 2) by reflexivity. rewrite E. lia.
    - rewrite H2. assert (E : lens_one_two_two 2 = 2) by reflexivity. rewrite E. lia. }
  destruct (it_model CT_DISTS lens_one_two_two 3 2 tnone) as [out|] eqn:E;
    [|vm_compute in E; discriminate].
  exists out. split; [reflexivity|].
  assert (Hret : o_ret out = 0)
    by (vm_compute in E; injection E as E'; rewrite <- E'; reflexivity).
  split; [exact Hret|].
  assert (Hbits : o_bits out = 2)
    by (vm_compute in E; injection E as E'; rewrite <- E'; reflexivity).
  split; [exact Hbits|].
  assert (Hb0 : c_bits (o_tbl out 0) = 1)
    by (vm_compute in E; injection E as E'; rewrite <- E'; vm_compute; reflexivity).
  split; [exact Hb0|].
  split; [rewrite Hb0; reflexivity|].
  (* the equality is the THEOREM's output, at a pair of distinct indices *)
  apply (it_repl_root CT_DISTS lens_one_two_two 3 2 tnone out H3 Hlens Hr2 E Hret 0 2).
  - rewrite Hbits. change (2 ^ 2) with 4. lia.
  - rewrite Hbits. change (2 ^ 2) with 4. lia.
  - rewrite Hb0. reflexivity.
Qed.

Print Assumptions classdone_repl.
Print Assumptions unitdone_le.
Print Assumptions unit_pos_lower.
Print Assumptions unit_not_done_zero.
Print Assumptions classdone_zero.
Print Assumptions classdone_tset_undone.
Print Assumptions class_unit_window.
Print Assumptions pos_in_root_unit.
Print Assumptions class_window_z.
Print Assumptions unit_cross_short_z.
Print Assumptions unit_cross_long_z.
Print Assumptions fill_class_hit.
Print Assumptions fill_class_miss.
Print Assumptions classdone_fill_short.
Print Assumptions classdone_fill_miss_root.
Print Assumptions pos_in_root_unit_z.
Print Assumptions step_shape.
Print Assumptions step_shape_cont.
Print Assumptions step_shape_break.
Print Assumptions it_step_cnt_all.
Print Assumptions step_pos_advance_cont.
Print Assumptions step_pos_advance_break.
Print Assumptions step_break_cond.
Print Assumptions repl_after_fill.
Print Assumptions repl_step_cont.
Print Assumptions repl_step_break.
Print Assumptions repl_loop.
Print Assumptions it_pre_go_start.
Print Assumptions repl_pre.
Print Assumptions it_repl_root.
Print Assumptions it_prefixdet_root.
Print Assumptions it_repl_root_instantiated.
