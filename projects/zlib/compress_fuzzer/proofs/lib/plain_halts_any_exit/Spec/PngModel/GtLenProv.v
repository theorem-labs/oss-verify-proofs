

(** * OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel.GtLenProv — the provenance walk for
      [lc_len_ok], CLOSED down to ONE named residue

    This is the residue [Gw.GtLenOk] names, in a NEW file because the eight declared
    candidates are frozen at their digests.

    ============================================================================
    READ THIS FIRST: TWO RETRACTIONS OF MY OWN WORK, BOTH THE SAME DEFECT.

    (1) THE STEP PREMISE.  The [provT_step] I reported earlier tonight — "one trip of
    the loop preserves provenance" — was VACUOUS.  It carried

        (forall n cnt d mx cur f, 0 <= it_subsz n cnt d mx cur f <= 15)

    which I labelled "honest" on the grounds that I did NOT claim it followed from
    [it_subsz_le].  Wrong axis: the premise is FALSE, so the lemma said nothing.
    [it_subsz] returns [curr] unchanged at fuel zero ([Inftrees.v:295-303]), so the
    premise entails [forall cur, 0 <= cur <= 15].  [subsz_flat_bound_is_false] derives
    the contradiction rather than asserting it.

    (2) THE RESIDUE.  Repairing (1) with an UNGUARDED bound on the width the code
    writes moved the same defect up one level, and I caught it only because I ran the
    same check on the repair.  [it_step] computes a sub-table width at every trip, but
    only WRITES it on one branch, and at a state where that branch does not fire the
    width is an arbitrary number — negative on the very first trip whenever
    [min < root], which is the common case.  So the unguarded residue was false at
    essentially every real input, and the implication [residues -> LenTblProv] was
    vacuous exactly as (1) was.

    THE REPAIRED SHAPE, and it is the lesson: the premise is guarded by the code's own
    two branch conditions ([step_breaks c st = false], [step_makes_sub c st = true]),
    so it demands the bound exactly where the pointer is written and nowhere else; and
    the residue carries [it_wf], because without the caller's [lens i <= MAXBITS] a
    code length above 15 is invisible to [it_findmax] and [it_kraft] yet still reaches
    the width through [x_lens].  Both conditions are in the statement from the start
    rather than acquired under refutation.

    THE MECHANISM, since it caught me twice in one file: a premise whose only job is to
    be discharged by someone else gets read for SHAPE (does it mention the right
    function?) and never for CONTENT (is there a reachable state satisfying it?).  A
    flat universal is the shape that hides it, because it looks like a lemma statement
    instead of a context-relative fact.  Guard adopted, and it is what found (2):
    every premise I hand a traversal gets a satisfiability witness IN THE SAME FILE,
    non-vacuously — here [ex_writes_a_pointer] proves the guards actually fire at the
    witness state, so [ptr_width_ok_is_satisfiable] cannot pass by being empty.
    ============================================================================

    THE STATEMENT IMPROVEMENT that makes the walk tractable.  I published the residue
    with arm 1 as [o_tbl out i = t0 i] — POSITION-DEPENDENT.  That is the honest shape
    of "this entry was never written", and a bad shape for the induction, because
    every write lemma then has to relate an index in the conclusion to the same index
    in the hypothesis, while my landed [ItGTblLeafPos.it_model_leafpos] carries a
    POSITION-INDEPENDENT pointwise predicate through the same five sites.  Replacing
    [e = t0 i] with "e is in t0's IMAGE" makes the predicate pointwise:

        InT0 t0 e := exists i, t0 i = e

    Strictly weaker per-entry, and still enough for every consumer, because a consumer
    holds [forall i, lc_len_ok (t0 i)] — a universal over t0 — so it does not care
    WHICH index an unwritten entry came from.  Checked below as
    [prov_gives_lc_len_ok], not asserted.

    WHAT IS HERE: the predicate; its closure under the table setter and the
    replication loop; the four arm facts; one trip; the LOOP; the incomplete-code
    fixup; the pre-loop; and [LenTblProv] itself, closed from ONE residue.
    WHAT IS NOT: that residue — [PtrWidthAlong], the width half of the fill-loop
    invariant.  The other premise the walk needs, [LenArmOk], is huffman-id's
    [len_arm_index_bounded] and is already Qed in their tree, so
    [residues_reduce_to_width] discharges it and the row's remainder is a single
    statement.  And [Inftrees.v:604-610] already declares that same fill-loop
    invariant UNOWNED for its LOWER-BOUND half ([TblBitsPos], which LT's stalled arms
    need).  One supplier closes my row and LT's together.

    GTBL-ARMS, 2026-08-19.  Not declared.  Read-only against the graded tree. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Inftrees Inflate InflateFast IfCtxVacuity IfCtxLenBound.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ######################################################################### *)
(* 1.  The predicate, pointwise and position-independent                      *)
(* ######################################################################### *)

Definition len_entry (j : Z) (b : Z) : Code := mkCodeT (lext j) b (lbase j).

Definition InT0 (t0 : ztbl) (e : Code) : Prop := exists i, t0 i = e.

(** The six provenances an entry of a built length table can have.  Arms 2-4 are
    [it_here]'s three shapes, arm 5 is the markers, arm 6 the sub-table pointer with
    its bit-count bound carried. *)
Definition ProvE (t0 : ztbl) (e : Code) : Prop :=
  InT0 t0 e
  \/ (exists b w, e = mkCodeT 0 b w)
  \/ (exists b j, 0 <= j <= 30 /\ e = len_entry j b)
  \/ (exists b, e = mkCodeT (32 + 64) b 0)
  \/ (exists b v, e = mkCodeT 64 b v)
  \/ (exists op b v, 0 <= op <= 15 /\ e = mkCodeT op b v).

Definition ProvT (t0 t : ztbl) : Prop := forall i, ProvE t0 (t i).

(** The base case, and it is why the image form is the right one: [t0] satisfies its
    own provenance with no side condition at all. *)
Lemma provT_refl : forall t0, ProvT t0 t0.
Proof. intros t0 i. left. exists i. reflexivity. Qed.

(* ######################################################################### *)
(* 2.  THE PAYOFF — so the weakening is checked, not asserted                  *)
(* ######################################################################### *)

(** Every arm is either vacuous for [lc_len_ok] or the checked base arm, and the
    image arm is discharged by the consumer's universal over [t0].  The four vacuity
    facts and [base_arm_ok] are [Gw.GtLenOk]'s; restated here as the local
    obligations this file's payoff needs, since that file is landed-unbuilt and I am
    not going to cite an artifact-less module from a file meant to be consumable. *)
Section Payoff.

  Hypothesis literal_vac : forall b w, lc_len_ok (mkCodeT 0 b w).
  Hypothesis invalid_vac : forall b, lc_len_ok (mkCodeT (32 + 64) b 0).
  Hypothesis marker_vac  : forall b v, lc_len_ok (mkCodeT 64 b v).
  Hypothesis pointer_vac : forall op b v, 0 <= op <= 15 -> lc_len_ok (mkCodeT op b v).
  Hypothesis base_ok     : forall j b, 0 <= j <= 30 -> lc_len_ok (len_entry j b).

  Theorem prov_gives_lc_len_ok : forall t0 t,
    (forall i, lc_len_ok (t0 i)) -> ProvT t0 t -> forall i, lc_len_ok (t i).
  Proof.
    intros t0 t Ht0 Hprov i.
    destruct (Hprov i)
      as [[k Hk] | [[b [w H]] | [[b [j [Hj H]]] | [[b H] | [[b [v H]] | [op [b [v [Hop H]]]]]]]]].
    - rewrite <- Hk. apply Ht0.
    - rewrite H. apply literal_vac.
    - rewrite H. apply base_ok; exact Hj.
    - rewrite H. apply invalid_vac.
    - rewrite H. apply marker_vac.
    - rewrite H. apply pointer_vac; exact Hop.
  Qed.

End Payoff.

(* ######################################################################### *)
(* 3.  CLOSURE UNDER THE WRITE CHANNEL                                        *)
(* ######################################################################### *)

(** The setter: one entry replaced, and the replacement must have a provenance. *)
Lemma provT_tset : forall t0 t i e,
  ProvT t0 t -> ProvE t0 e -> ProvT t0 (tset t i e).
Proof.
  intros t0 t i e Ht He j. unfold tset.
  destruct (Z.eqb j i); [exact He | apply Ht].
Qed.

(** THE REPLICATION LOOP.  [it_fill] writes the SAME entry at [n] strided indices,
    so one provenance covers all of them — and this is the site whose value arrives
    through a PARAMETER, which is why a constructor census cannot see it and why
    huffman-id's sharpening (enumerate the write, then check each write's value) is
    the correct unit. *)
Lemma provT_it_fill : forall n t0 t bi incr h,
  ProvT t0 t -> ProvE t0 h -> ProvT t0 (it_fill n t bi incr h).
Proof.
  induction n as [|n IH]; intros t0 t bi incr h Ht Hh; cbn [it_fill].
  - exact Ht.
  - apply IH; [apply provT_tset; assumption | exact Hh].
Qed.

(* ######################################################################### *)
(* 4.  THE ARM FACTS — every shape the code writes HAS a provenance             *)
(* ######################################################################### *)

Lemma provE_marker : forall t0 b v, ProvE t0 (mkCodeT 64 b v).
Proof. intros. right. right. right. right. left. exists b, v. reflexivity. Qed.

Lemma provE_pointer : forall t0 op b v,
  0 <= op <= 15 -> ProvE t0 (mkCodeT op b v).
Proof.
  intros t0 op b v Hop. right. right. right. right. right.
  exists op, b, v. split; [exact Hop|reflexivity].
Qed.

(** The index bound the base arm needs, named, because from here on it is a supplied
    premise rather than an inline conjunct. *)
Definition LenArmOk (c : ItCtx) : Prop :=
  forall sym, 257 <= x_work c sym -> 0 <= x_work c sym - 257 <= 30.

(** [it_here]'s three shapes at the LENGTH table's arrays.

    THE INDEX BOUND IS TAKEN CONDITIONALLY, AND THAT IS THE WHOLE REASON THIS WALK
    NEEDS NO COVERAGE INVARIANT.  My landed [ItGTblLeafPos.leafpos_loop] carries
    [CovCtxOk c cnt0] and [CovInv c cnt0 st] through every trip, because its per-step
    lemmas need to know where [s_sym] has got to in order to bound the index.
    huffman-id's [len_arm_index_bounded] quantifies [sym] UNIVERSALLY and
    unconstrained — the bound holds at every entry of the work array — so the
    hypothesis below is index-free and the traversal never has to preserve a
    symbol-range clause.

    The antecedent [257 <= w] is supplied by the arm's own branch guard
    ([Z.leb (x_match c) w = true] with [x_match c = 257]), so the caller owes only the
    bound, not the reachability. *)
Lemma provE_it_here : forall t0 c st,
  x_extra c = lext -> x_base c = lbase -> x_match c = 257 ->
  LenArmOk c ->
  ProvE t0 (it_here c st).
Proof.
  intros t0 c st Hex Hba Hmt Hjb. unfold it_here.
  destruct (Z.ltb (x_work c (s_sym st) + 1) (x_match c)) eqn:E1.
  - right. left. exists (s_len st - s_drop st), (x_work c (s_sym st)). reflexivity.
  - destruct (Z.leb (x_match c) (x_work c (s_sym st))) eqn:E2.
    + right. right. left.
      exists (s_len st - s_drop st), (x_work c (s_sym st) - x_match c).
      split.
      * rewrite Hmt. apply Hjb.
        apply Z.leb_le in E2. rewrite Hmt in E2. exact E2.
      * unfold len_entry. rewrite <- Hex, <- Hba. reflexivity.
    + right. right. right. left. exists (s_len st - s_drop st). reflexivity.
Qed.

(** And the same fact with huffman-id's premises rather than my abstracted one, so a
    consumer sees the real sources: the [PreGo] equation, [it_wf]'s code bounds, and
    nothing about reachability. *)
Definition LenArmIndexBounded : Prop :=
  forall lens codes root0 t0 c st sym,
    it_pre CT_LENS lens codes root0 t0 = PreGo c st ->
    codes <= 288 -> 0 < codes ->
    257 <= x_work c sym ->
    0 <= x_work c sym - x_match c <= 30.

Lemma len_arm_ok_from_pre : forall lens codes root0 tinit c st,
  LenArmIndexBounded ->
  it_pre CT_LENS lens codes root0 tinit = PreGo c st ->
  codes <= 288 -> 0 < codes -> x_match c = 257 ->
  LenArmOk c.
Proof.
  intros lens codes root0 tinit c st Hb Hpre Hle Hlt Hmt sym Hsym.
  rewrite <- Hmt.
  exact (Hb lens codes root0 tinit c st sym Hpre Hle Hlt Hsym).
Qed.

Lemma provE_it_here_from_pre : forall t0 lens codes root0 tinit c st st',
  LenArmIndexBounded ->
  it_pre CT_LENS lens codes root0 tinit = PreGo c st ->
  codes <= 288 -> 0 < codes ->
  x_extra c = lext -> x_base c = lbase -> x_match c = 257 ->
  ProvE t0 (it_here c st').
Proof.
  intros t0 lens codes root0 tinit c st st' Hb Hpre Hle Hlt Hex Hba Hmt.
  apply (provE_it_here t0 c st' Hex Hba Hmt).
  exact (len_arm_ok_from_pre lens codes root0 tinit c st Hb Hpre Hle Hlt Hmt).
Qed.

(* ######################################################################### *)
(* 5.  THE POINTER WIDTH — the refutation, and the guarded repair              *)
(* ######################################################################### *)

(** RETRACTION (1).  See the header.  A claim that a premise is unsatisfiable is
    exactly as checkable as the premise itself, so it gets checked. *)
Lemma subsz_flat_bound_is_false :
  (forall n cnt d mx cur f, 0 <= it_subsz n cnt d mx cur f <= 15) -> False.
Proof.
  intros H. specialize (H 0%nat zzero 0 0 16 0). cbn [it_subsz] in H. lia.
Qed.

(** The internal [let]s of [it_step], named, so the premise can be about the width the
    code WRITES at this state — and about the branch on which it writes it — instead of
    about [it_subsz] at every argument.  Same expressions as [Inftrees.v:311-337], in
    the same order. *)
Definition step_cnt1 (st : ItSt) : zarr :=
  zset (s_count st) (s_len st) (s_count st (s_len st) - 1).
Definition step_drop (c : ItCtx) (st : ItSt) : Z :=
  if Z.eqb (s_drop st) 0 then x_root c else s_drop st.
Definition step_len1 (c : ItCtx) (st : ItSt) : Z :=
  if Z.eqb (step_cnt1 st (s_len st)) 0
  then x_lens c (x_work c (s_sym st + 1)) else s_len st.
Definition step_curr (c : ItCtx) (st : ItSt) : Z :=
  it_subsz 16%nat (step_cnt1 st) (step_drop c st) (x_max c)
           (step_len1 c st - step_drop c st)
           (Z.shiftl 1 (step_len1 c st - step_drop c st)).

(** The two branch conditions, [Inftrees.v:322] and [:324-325]. *)
Definition step_breaks (c : ItCtx) (st : ItSt) : bool :=
  Z.eqb (step_cnt1 st (s_len st)) 0 && Z.eqb (s_len st) (x_max c).
Definition step_makes_sub (c : ItCtx) (st : ItSt) : bool :=
  Z.ltb (x_root c) (step_len1 c st)
  && negb (Z.eqb (Z.land (it_rev_incr (s_huff st) (s_len st)) (x_mask c)) (s_low st)).

(** THE REPAIRED PREMISE.  Guarded, because an unguarded version is false: at a state
    where the sub-table branch does not fire, [step_curr] is an arbitrary number, and
    on trip 0 it is [min - root], negative whenever [min < root].

    The overflow exit is deliberately INSIDE the guard rather than excluded: it
    computes the same width and only then discovers the table is full, so excluding it
    would make the premise mention its own conclusion.  Under the fill-loop invariant
    the bound holds on that exit too. *)
Definition PtrWidthOk (c : ItCtx) (st : ItSt) : Prop :=
  step_breaks c st = false ->
  step_makes_sub c st = true ->
  0 <= step_curr c st <= 15.

(** [it_subsz] never goes below its starting width and never above the context's
    ceiling.  The upper half is what my landed [ItGTblLeafPos.it_subsz_le] states;
    re-proved here because that file has no artifact — the FIFTH landed-unbuilt
    duplication — and STRENGTHENED with the lower half, which is what the [0 <=]
    conjunct needs and which [it_subsz_le] does not carry. *)
Lemma it_subsz_bounds : forall n cnt d mx cur f,
  cur <= it_subsz n cnt d mx cur f <= Z.max cur (mx - d).
Proof.
  induction n as [|n IH]; intros cnt d mx cur f; cbn [it_subsz].
  - split; [lia | apply Z.le_max_l].
  - destruct (Z.ltb (cur + d) mx) eqn:E1; [|split; [lia|apply Z.le_max_l]].
    destruct (Z.leb (f - cnt (cur + d)) 0) eqn:E2;
      [split; [lia|apply Z.le_max_l]|].
    destruct (IH cnt d mx (cur + 1) ((f - cnt (cur + d)) * 2)) as [Hlo Hhi].
    apply Z.ltb_lt in E1.
    split; [lia|].
    rewrite Z.max_r in Hhi by lia.
    apply (Z.le_trans _ (mx - d) _); [exact Hhi | apply Z.le_max_r].
Qed.

(** [it_findmax] never returns more than its starting index, so the context's [max]
    is at most [MAXBITS] with no hypothesis at all — which takes one of the residue's
    four premises off the supplier's list entirely.  Stated against [Z.max 0 m] rather
    than [m] because the scan can fall out at 0 from a negative start. *)
Lemma it_findmax_le_max : forall n m cnt, it_findmax n m cnt <= Z.max 0 m.
Proof.
  induction n as [|n IH]; intros m cnt; cbn [it_findmax].
  - apply Z.le_max_l.
  - destruct (Z.eqb (cnt m) 0).
    + specialize (IH (m - 1) cnt).
      destruct (Z.max_spec 0 (m - 1)) as [[_ E1]|[_ E1]];
        destruct (Z.max_spec 0 m) as [[_ E2]|[_ E2]];
        rewrite E1 in IH; rewrite E2; lia.
    + apply Z.le_max_r.
Qed.

(** And [it_findmin] never exceeds the ceiling it is given, which is what bounds the
    loop's STARTING code length.  Same shape as [it_findmax_le_max]: both are one-line
    inductions that were not in the tree, and both take a premise off the supplier's
    list rather than onto it. *)
Lemma it_findmin_le : forall n m mx cnt, m <= mx -> it_findmin n m mx cnt <= mx.
Proof.
  induction n as [|n IH]; intros m mx cnt Hm; cbn [it_findmin]; [lia|].
  destruct (Z.geb_spec m mx) as [_|Hlt]; [lia|].
  destruct (Z.eqb (cnt m) 0); [apply IH; lia | lia].
Qed.

(** THE SORT'S RANGE, and this is what turns the row's last residue into a theorem.

    [it_sort] writes symbol indices into the work array and touches nothing else, so
    every entry is either an index it walked or whatever the initial array held.  With
    the walk starting at 0 over [codes] symbols and the initial array [zzero], every
    entry is in [[0, codes)] as soon as [0 < codes] — the [zzero] default is 0, which
    is in range precisely because the range is non-empty.

    I had routed this to huffman-id as their subject and priced it as a residue.  It is
    twenty lines.  Their [len_arm_index_bounded] is the same fact's consequence above
    the match boundary and remains the canonical statement of it; I prove it here only
    because their file has no artifact and mine has to be consumable.  Duplication
    disclosed, not hidden. *)
Lemma it_sort_snd_range : forall n i lens offs work lo hi,
  (forall j, lo <= work j < hi) ->
  lo <= i -> i + Z.of_nat n <= hi ->
  forall j, lo <= snd (it_sort n i lens offs work) j < hi.
Proof.
  induction n as [|n IH]; intros i lens offs work lo hi Hw Hlo Hhi j; cbn [it_sort].
  - apply Hw.
  - rewrite Nat2Z.inj_succ in Hhi.
    destruct (Z.eqb (lens i) 0).
    + apply (IH (i + 1) lens offs work lo hi Hw); lia.
    + apply (IH (i + 1) lens (zset offs (lens i) (offs (lens i) + 1))
                (zset work (offs (lens i)) i) lo hi); [|lia|lia].
      intros k. unfold zset.
      destruct (Z.eqb k (offs (lens i))); [lia | apply Hw].
Qed.

Lemma sort_zzero_range : forall codes lens offs,
  0 < codes ->
  forall j, 0 <= snd (it_sort (Z.to_nat codes) 0 lens offs zzero) j < codes.
Proof.
  intros codes lens offs Hc j.
  apply (it_sort_snd_range (Z.to_nat codes) 0 lens offs zzero 0 codes);
    [ intros k; unfold zzero, zconst; lia
    | lia
    | rewrite Z2Nat.id by lia; lia ].
Qed.

(** So the repaired premise is DERIVABLE from three width facts about the context and
    the state.  This is where a discharger starts, and it is what makes the premise
    satisfiable rather than self-contradictory.  The guards are not needed for the
    derivation — they are what makes the premise TRUE at states that do not write —
    so they are introduced and dropped. *)
Lemma ptr_width_from_widths : forall c st,
  0 <= step_len1 c st - step_drop c st ->
  step_len1 c st - step_drop c st <= 15 ->
  x_max c - step_drop c st <= 15 ->
  PtrWidthOk c st.
Proof.
  intros c st H0 H1 H2 _ _. unfold step_curr.
  destruct (it_subsz_bounds 16%nat (step_cnt1 st) (step_drop c st) (x_max c)
              (step_len1 c st - step_drop c st)
              (Z.shiftl 1 (step_len1 c st - step_drop c st))) as [Hlo Hhi].
  split; [lia|].
  destruct (Z.max_spec (step_len1 c st - step_drop c st)
              (x_max c - step_drop c st)) as [[_ E]|[_ E]];
    rewrite E in Hhi; lia.
Qed.

(** AND THE PREMISE COUNT DROPS TO TWO.  The [0 <=] conjunct does not need a
    hypothesis at all: the sub-table guard itself says [root < len1], and [drop] is
    only ever [0] or [root], so the starting width is at least 1 exactly where the
    write happens.  That is the guard earning its keep — the unguarded version could
    not see it, which is the other half of why retraction (2) was a real weakening
    and not just a tidier statement.

    What is left for a supplier is the fill-loop invariant's two clauses,
    [DropTwoValued] and [Len1Bounded].  [x_max c <= 15] comes free from
    [it_findmax_le_max] and [1 <= x_root c] is [Inftrees.it_pre_root_pos], already in
    the graded tree. *)
Lemma ptr_width_from_inv : forall c st,
  (s_drop st = 0 \/ s_drop st = x_root c) ->
  step_len1 c st <= 15 ->
  x_max c <= 15 ->
  1 <= x_root c ->
  PtrWidthOk c st.
Proof.
  intros c st Hdrop Hlen Hmx Hr Hbrk Hsub.
  assert (Hlt : x_root c < step_len1 c st).
  { apply andb_prop in Hsub as [H1 _]. apply Z.ltb_lt in H1. exact H1. }
  assert (Hd : step_drop c st = x_root c).
  { unfold step_drop. destruct Hdrop as [E|E]; rewrite E.
    - rewrite Z.eqb_refl. reflexivity.
    - destruct (Z.eqb (x_root c) 0) eqn:E0; [apply Z.eqb_eq in E0; lia|reflexivity]. }
  apply (ptr_width_from_widths c st);
    [ rewrite Hd; lia | rewrite Hd; lia | rewrite Hd; lia
    | exact Hbrk | exact Hsub ].
Qed.

(** NON-VACUITY, and it is a PAIR of lemmas on purpose.  A guarded premise can pass a
    satisfiability check by having its guard fail, which is the defect this file
    retracts wearing a different hat.  So the witness state is shown to FIRE both
    guards ([ex_writes_a_pointer]) before the bound is claimed at it.

    HONEST LABEL: satisfiable, NOT shown reachable.  [it_pre]'s [PreGo] state always
    has [s_drop = 0], so a state with [s_drop = root] needs the loop to have run, and
    exhibiting one is the producer-side check I have not done.  The distinction is
    exactly the one I have insisted on elsewhere, so it gets stated rather than
    blurred. *)
Definition ex_ctx : ItCtx :=
  {| x_type := CT_LENS; x_codes := 288; x_lens := zzero; x_root := 3;
     x_max := 15; x_mask := 7; x_work := zzero; x_base := lbase;
     x_extra := lext; x_match := 257 |}.

Definition ex_st : ItSt :=
  {| s_huff := 0; s_sym := 0; s_len := 5; s_next := 0; s_curr := 5;
     s_drop := 3; s_low := 4294967295; s_used := 8; s_min := 1;
     s_count := zset zzero 5 3; s_tbl := tnone |}.

Lemma ex_writes_a_pointer :
  step_breaks ex_ctx ex_st = false /\ step_makes_sub ex_ctx ex_st = true.
Proof.
  split; vm_compute; reflexivity.
Qed.

Lemma ptr_width_ok_is_satisfiable : PtrWidthOk ex_ctx ex_st.
Proof.
  apply ptr_width_from_widths;
    unfold step_len1, step_drop, step_cnt1, ex_ctx, ex_st; cbn; lia.
Qed.

(* ######################################################################### *)
(* 6.  ONE TRIP                                                               *)
(* ######################################################################### *)

(** The table an [it_step] result carries, for all three exits.  Defined here because
    there is no such projection in [Inftrees] and my landed [ItGTblLeafPos] defines
    its own locally — two files needing the same projection and neither able to share
    it, because the landed one has no artifact. *)
Definition step_table (r : ItStep) : ztbl :=
  match r with
  | ItCont st => s_tbl st
  | ItBreak st => s_tbl st
  | ItOverflow t => t
  end.

(** ONE TRIP PRESERVES PROVENANCE.

    [it_step] writes in exactly two places — the [it_fill] replication (always) and
    the sub-table pointer [tset] (only on the new-sub-table branch) — and exits four
    ways (break, overflow, cont-with-pointer, cont-without).  All four are covered
    because the two writes are. *)
Lemma provT_step : forall t0 c st,
  x_extra c = lext -> x_base c = lbase -> x_match c = 257 ->
  LenArmOk c ->
  PtrWidthOk c st ->
  ProvT t0 (s_tbl st) ->
  ProvT t0 (step_table (it_step c st)).
Proof.
  intros t0 c st Hex Hba Hmt Hjb Hptr Ht.
  assert (Hhere : ProvE t0 (it_here c st))
    by (apply (provE_it_here t0 c st Hex Hba Hmt Hjb)).
  assert (Htbl1 : ProvT t0 (it_fill (Z.to_nat (Z.shiftl 1 (s_curr st)
                                               / Z.shiftl 1 (s_len st - s_drop st)))
                              (s_tbl st)
                              (s_next st + Z.shiftr (s_huff st) (s_drop st))
                              (Z.shiftl 1 (s_len st - s_drop st))
                              (it_here c st)))
    by (apply provT_it_fill; assumption).
  unfold PtrWidthOk, step_curr, step_makes_sub, step_breaks,
         step_len1, step_drop, step_cnt1 in Hptr.
  unfold it_step. cbv zeta.
  destruct (Z.eqb (zset (s_count st) (s_len st) (s_count st (s_len st) - 1) (s_len st)) 0
            && Z.eqb (s_len st) (x_max c)) eqn:Ebrk;
    [cbn [step_table s_tbl]; exact Htbl1|].
  destruct ((Z.ltb (x_root c) _) && negb (Z.eqb _ (s_low st))) eqn:Esub.
  - destruct (it_enough (x_type c) _) eqn:Eover;
      [cbn [step_table]; exact Htbl1|].
    cbn [step_table s_tbl]. apply provT_tset; [exact Htbl1|].
    apply provE_pointer.
    (* [destruct ... eqn:] substitutes the branch expressions in [Hptr] too, so both
       guards arrive already discharged; the [first] keeps the proof honest if a
       future Rocq stops doing that. *)
    apply Hptr; first [reflexivity | exact Ebrk | exact Esub].
  - cbn [step_table s_tbl]. exact Htbl1.
Qed.

(* ######################################################################### *)
(* 7.  THE LOOP                                                               *)
(* ######################################################################### *)

(** [PtrWidthOk] at every state the loop VISITS.  Relativised to reachability by
    construction, because the flat form is the mistake this file retracts:
    [it_iter k c st] is [Inftrees]'s own "state after k fall-through trips". *)
Definition PtrWidthAlong (c : ItCtx) (st : ItSt) : Prop :=
  forall k st', it_iter k c st = Some st' -> PtrWidthOk c st'.

Lemma along_here : forall c st, PtrWidthAlong c st -> PtrWidthOk c st.
Proof. intros c st H. apply (H 0%nat st). reflexivity. Qed.

Lemma along_step : forall c st st',
  it_step c st = ItCont st' -> PtrWidthAlong c st -> PtrWidthAlong c st'.
Proof.
  intros c st st' Hs H k s Hk. apply (H (S k) s).
  cbn [it_iter]. rewrite Hs. exact Hk.
Qed.

(** THE RESIDUE, PRICED.  Two clauses of the fill-loop invariant, and nothing else:
    [drop] is two-valued, and the next code length is at most [MAXBITS].  Everything
    the width bound needed beyond those is either free ([x_max c <= 15]) or already in
    the graded tree ([Inftrees.it_pre_root_pos]).

    [Inftrees.v:604-610] declares this same fill-loop invariant UNOWNED for its
    LOWER-BOUND half ([1 <= s_len - s_drop], which [TblBitsPos] and LT's stalled arms
    need).  The two halves are clauses of one invariant over one loop, so one supplier
    closes both rows. *)
Definition LoopWidthInv (c : ItCtx) (st : ItSt) : Prop :=
  forall k st', it_iter k c st = Some st' ->
    (s_drop st' = 0 \/ s_drop st' = x_root c) /\ step_len1 c st' <= 15.

Theorem width_along_of_inv : forall c st,
  1 <= x_root c -> x_max c <= 15 -> LoopWidthInv c st -> PtrWidthAlong c st.
Proof.
  intros c st Hr Hmx Hinv k st' Hk.
  destruct (Hinv k st' Hk) as [Hd Hl].
  exact (ptr_width_from_inv c st' Hd Hl Hmx Hr).
Qed.

(* ######################################################################### *)
(* 7b. AND THE TWO CLAUSES REDUCE TO ONE — the work array's range             *)
(* ######################################################################### *)

(** The state half of the invariant, as one predicate. *)
Definition WidthSt (c : ItCtx) (st : ItSt) : Prop :=
  (s_drop st = 0 \/ s_drop st = x_root c) /\ s_len st <= 15.

(** THE ONE FACT LEFT.  Neither the code nor [it_wf] gives it: every entry of the
    sorted work array is a symbol index in range.  That is a statement about
    [it_sort], which is huffman-id's subject — their [len_arm_index_bounded] is its
    upper half above the match boundary — and after this section it is the ONLY
    premise the row still owes. *)
Definition WorkInRange (c : ItCtx) : Prop :=
  forall sym, 0 <= x_work c sym < x_codes c.

(** [it_wf]'s code-length bound, read through the context's fields. *)
Definition LensBounded (c : ItCtx) : Prop :=
  forall i, 0 <= i < x_codes c -> 0 <= x_lens c i <= 15.

(** The state projection, FORWARD, and the direction is not a preference here:
    [Inftrees.v:900-905] MEASURES [injection] on an [ItStep] equality at over 150 s,
    because the record's fields carry whole [it_fill] and [it_subsz] calls.  So
    nothing below inverts a step result — the lemmas conclude about the projection and
    a consumer rewrites its own equation in. *)
Definition step_st (r : ItStep) (d : ItSt) : ItSt :=
  match r with ItCont s => s | ItBreak s => s | ItOverflow _ => d end.

Lemma widthst_len1 : forall c st,
  LensBounded c -> WorkInRange c -> WidthSt c st -> step_len1 c st <= 15.
Proof.
  intros c st Hlb Hwr [_ Hlen]. unfold step_len1.
  destruct (Z.eqb (step_cnt1 st (s_len st)) 0); [|exact Hlen].
  destruct (Hlb (x_work c (s_sym st + 1)) (Hwr (s_sym st + 1))) as [_ H]. exact H.
Qed.

Lemma widthst_forward : forall c st,
  LensBounded c -> WorkInRange c -> WidthSt c st ->
  WidthSt c (step_st (it_step c st) st).
Proof.
  intros c st Hlb Hwr Hst.
  pose proof (widthst_len1 c st Hlb Hwr Hst) as Hl1.
  unfold step_len1, step_cnt1 in Hl1.
  destruct Hst as [Hd Hlen].
  unfold it_step. cbv zeta.
  destruct (Z.eqb (zset (s_count st) (s_len st) (s_count st (s_len st) - 1) (s_len st)) 0
            && Z.eqb (s_len st) (x_max c)) eqn:Ebrk;
    [cbn [step_st s_drop s_len]; split; assumption|].
  destruct ((Z.ltb (x_root c) _) && negb (Z.eqb _ (s_low st))) eqn:Esub.
  - destruct (it_enough (x_type c) _) eqn:Eover;
      [cbn [step_st]; split; assumption|].
    cbn [step_st s_drop s_len]. split; [|exact Hl1].
    destruct (Z.eqb (s_drop st) 0) eqn:E0; [right; reflexivity|].
    destruct Hd as [E|E]; [rewrite E in E0; cbn in E0; discriminate E0
                          |right; exact E].
  - cbn [step_st s_drop s_len]. split; [exact Hd | exact Hl1].
Qed.

Lemma widthst_iter : forall k c st st',
  LensBounded c -> WorkInRange c ->
  WidthSt c st -> it_iter k c st = Some st' -> WidthSt c st'.
Proof.
  induction k as [|k IH]; intros c st st' Hlb Hwr Hst H; cbn [it_iter] in H.
  - injection H as H. subst st'. exact Hst.
  - destruct (it_step c st) as [s|s|t] eqn:E; try discriminate.
    apply (IH c s st' Hlb Hwr); [|exact H].
    pose proof (widthst_forward c st Hlb Hwr Hst) as HF.
    rewrite E in HF. cbn [step_st] in HF. exact HF.
Qed.

Theorem loopwidthinv_of_work_range : forall c st,
  LensBounded c -> WorkInRange c -> WidthSt c st -> LoopWidthInv c st.
Proof.
  intros c st Hlb Hwr Hst k st' Hk.
  destruct (widthst_iter k c st st' Hlb Hwr Hst Hk) as [Hd Hlen].
  split; [exact Hd|].
  apply (widthst_len1 c st' Hlb Hwr). split; [exact Hd|exact Hlen].
Qed.

(** THE TRAVERSAL.  Same shape as my landed [ItGTblLeafPos.leafpos_loop]: induct on
    the fuel, case on [it_step], hand the invariant forward on the [ItCont] arm and
    the provenance out on the other two. *)
Lemma provT_loop : forall n t0 c st r,
  x_extra c = lext -> x_base c = lbase -> x_match c = 257 ->
  LenArmOk c ->
  PtrWidthAlong c st ->
  ProvT t0 (s_tbl st) ->
  it_loop n c st = Some r ->
  ProvT t0 (step_table r).
Proof.
  induction n as [|n IH]; intros t0 c st r Hex Hba Hmt Hjb Halong Ht Hl;
    cbn [it_loop] in Hl; [discriminate|].
  destruct (it_step c st) as [st'|st'|tt] eqn:E.
  - assert (Hs : ProvT t0 (s_tbl st')).
    { pose proof (provT_step t0 c st Hex Hba Hmt Hjb
                    (along_here c st Halong) Ht) as H0.
      rewrite E in H0. cbn [step_table] in H0. exact H0. }
    exact (IH t0 c st' r Hex Hba Hmt Hjb (along_step c st st' E Halong) Hs Hl).
  - assert (Hs : ProvT t0 (s_tbl st')).
    { pose proof (provT_step t0 c st Hex Hba Hmt Hjb
                    (along_here c st Halong) Ht) as H0.
      rewrite E in H0. cbn [step_table] in H0. exact H0. }
    injection Hl as Hl. subst r. cbn [step_table]. exact Hs.
  - assert (Hs : ProvT t0 tt).
    { pose proof (provT_step t0 c st Hex Hba Hmt Hjb
                    (along_here c st Halong) Ht) as H0.
      rewrite E in H0. cbn [step_table] in H0. exact H0. }
    injection Hl as Hl. subst r. cbn [step_table]. exact Hs.
Qed.

(* ######################################################################### *)
(* 8.  THE FIXUP AND THE PRE-LOOP                                             *)
(* ######################################################################### *)

(** [it_finish] writes at most one entry, an op-64 marker. *)
Lemma provT_finish : forall t0 st, ProvT t0 (s_tbl st) -> ProvT t0 (it_finish st).
Proof.
  intros t0 st H. unfold it_finish.
  destruct (Z.eqb (s_huff st) 0); [exact H|].
  apply provT_tset; [exact H | apply provE_marker].
Qed.

(** THE PRE-LOOP, in FORWARD form, and the direction is the point.

    Everything the traversal needs from [it_pre] — the three [CT_LENS] field
    equations, the initial table, and the [PreEmpty] arm's two markers — comes from
    ONE pass over the definition, stated as a predicate on the RESULT.  A consumer
    holding [it_pre ... = PreGo c st] then [rewrite]s its own equation into this
    lemma's conclusion instead of inverting the equality.  Constructing forward and
    rewriting is the cheap direction; my [Gw.GtLenOk.it_pre_go_lens] pays [injection]
    on an eleven-field record for a strict subset of the same facts. *)
Definition PreLensOk (lens : zarr) (codes : Z) (t0 : ztbl) (r : ItPre) : Prop :=
  match r with
  | PreErr => True
  | PreOver => True
  | PreEmpty t => ProvT t0 t
  | PreGo c st =>
      x_extra c = lext /\ x_base c = lbase /\ x_match c = 257 /\ s_tbl st = t0
      /\ x_max c <= 15 /\ x_lens c = lens /\ x_codes c = codes
      /\ s_drop st = 0 /\ s_len st <= 15
  end.

Lemma pre_lens_ok : forall lens codes root0 t0,
  PreLensOk lens codes t0 (it_pre CT_LENS lens codes root0 t0).
Proof.
  intros lens codes root0 t0. unfold it_pre. cbv zeta.
  destruct (Z.eqb (it_findmax 15%nat MAXBITS (it_count (Z.to_nat codes) 0 lens zzero)) 0)
    eqn:Emx.
  - cbn [PreLensOk].
    apply provT_tset; [apply provT_tset; [apply provT_refl|apply provE_marker]
                      |apply provE_marker].
  - destruct (it_kraft 15%nat 1 1 (it_count (Z.to_nat codes) 0 lens zzero)) as [lft|];
      [|exact I].
    destruct (it_incomplete CT_LENS lft _); [exact I|].
    destruct (it_enough CT_LENS _); [exact I|].
    assert (Hmx15 : it_findmax 15%nat MAXBITS
                      (it_count (Z.to_nat codes) 0 lens zzero) <= 15).
    { pose proof (it_findmax_le_max 15%nat MAXBITS
                    (it_count (Z.to_nat codes) 0 lens zzero)) as Hm.
      unfold MAXBITS in *. rewrite Z.max_r in Hm by lia. exact Hm. }
    assert (Hmx1 : 1 <= it_findmax 15%nat MAXBITS
                         (it_count (Z.to_nat codes) 0 lens zzero)).
    { apply it_findmax_pos; [cbn; unfold MAXBITS; lia|].
      intro Hc. rewrite Hc in Emx. cbn in Emx. discriminate Emx. }
    cbn [PreLensOk x_extra x_base x_match s_tbl x_max x_lens x_codes s_drop s_len].
    vm_compute (Z.eqb CT_LENS CT_LENS).
    repeat split; try reflexivity; try exact Hmx15.
    apply (Z.le_trans _ (it_findmax 15%nat MAXBITS
                           (it_count (Z.to_nat codes) 0 lens zzero)) _);
      [apply it_findmin_le; lia | exact Hmx15].
Qed.

(** The work array's range, as its own forward read.  Deliberately NOT a conjunct of
    [PreLensOk]: [split] is [constructor], which intros a goal's leading products
    first, so a [repeat split] over a ten-conjunct predicate walks through this
    clause's [0 < codes ->] arrow and its [forall] and then splits the range
    underneath -- three goals where the shape suggests one.  A separate predicate
    keeps the proof one line. *)
Definition PreWorkOk (codes : Z) (r : ItPre) : Prop :=
  match r with
  | PreGo c _ => 0 < codes -> forall sym, 0 <= x_work c sym < codes
  | _ => True
  end.

Lemma pre_work_ok : forall lens codes root0 t0,
  PreWorkOk codes (it_pre CT_LENS lens codes root0 t0).
Proof.
  intros lens codes root0 t0. unfold PreWorkOk, it_pre. cbv zeta.
  destruct (Z.eqb (it_findmax 15%nat MAXBITS (it_count (Z.to_nat codes) 0 lens zzero)) 0);
    [exact I|].
  destruct (it_kraft 15%nat 1 1 (it_count (Z.to_nat codes) 0 lens zzero)) as [lft|];
    [|exact I].
  destruct (it_incomplete CT_LENS lft _); [exact I|].
  destruct (it_enough CT_LENS _); [exact I|].
  cbn [x_work]. intros Hc sy. apply sort_zzero_range; exact Hc.
Qed.

Lemma pre_lens_work_range : forall lens codes root0 t0 c st,
  0 < codes ->
  it_pre CT_LENS lens codes root0 t0 = PreGo c st ->
  forall sym, 0 <= x_work c sym < codes.
Proof.
  intros lens codes root0 t0 c st Hc H.
  pose proof (pre_work_ok lens codes root0 t0) as HP. rewrite H in HP.
  exact (HP Hc).
Qed.

Lemma pre_lens_go : forall lens codes root0 t0 c st,
  it_pre CT_LENS lens codes root0 t0 = PreGo c st ->
  x_extra c = lext /\ x_base c = lbase /\ x_match c = 257 /\ s_tbl st = t0
  /\ x_max c <= 15 /\ x_lens c = lens /\ x_codes c = codes
  /\ s_drop st = 0 /\ s_len st <= 15.
Proof.
  intros lens codes root0 t0 c st H.
  pose proof (pre_lens_ok lens codes root0 t0) as HP. rewrite H in HP. exact HP.
Qed.

Lemma pre_lens_empty : forall lens codes root0 t0 t,
  it_pre CT_LENS lens codes root0 t0 = PreEmpty t -> ProvT t0 t.
Proof.
  intros lens codes root0 t0 t H.
  pose proof (pre_lens_ok lens codes root0 t0) as HP. rewrite H in HP. exact HP.
Qed.

(* ######################################################################### *)
(* 9.  LenTblProv — CLOSED, from ONE residue                                   *)
(* ######################################################################### *)

(** [it_wf] is in the statement from the start.  Without the caller's
    [lens i <= MAXBITS] a code length above 15 is invisible to [it_findmax] and
    [it_kraft] — they only ever scan buckets 1..15 — yet still reaches the sub-table
    width through [x_lens], so the width residue is false without it.  That is
    retraction (2) in the header, and the condition belongs here rather than being
    acquired later. *)
Definition LenTblProv : Prop :=
  forall lens codes root0 t0 out,
    it_wf CT_LENS lens codes root0 ->
    it_model CT_LENS lens codes root0 t0 = Some out ->
    ProvT t0 (o_tbl out).

(** The two premises the walk needs, as ONE named obligation on the [PreGo] pair, so a
    supplier sees a single statement rather than two scattered hypotheses. *)
Definition LenLoopResidues : Prop :=
  forall lens codes root0 t0 c st,
    it_wf CT_LENS lens codes root0 ->
    it_pre CT_LENS lens codes root0 t0 = PreGo c st ->
    LenArmOk c /\ PtrWidthAlong c st.

(** And the FIRST of the two is already someone's theorem, so the row's remainder is
    ONE statement: the width half of the fill-loop invariant. *)
Definition LenWidthAlong : Prop :=
  forall lens codes root0 t0 c st,
    it_wf CT_LENS lens codes root0 ->
    it_pre CT_LENS lens codes root0 t0 = PreGo c st ->
    PtrWidthAlong c st.

(** THE WHOLE ROW, reduced to the work array's range.  Everything else the width
    bound needed is now discharged at the source: [x_max c <= 15] and [s_len st <= 15]
    and [s_drop st = 0] come out of [pre_lens_ok]'s forward read, [1 <= x_root c] is
    [Inftrees.it_pre_root_pos] which is already in the graded tree, and the code-length
    bound is [it_wf]'s own conjunct. *)
Theorem width_along_of_work_range : forall lens codes root0 t0 c st,
  it_wf CT_LENS lens codes root0 ->
  it_pre CT_LENS lens codes root0 t0 = PreGo c st ->
  WorkInRange c ->
  PtrWidthAlong c st.
Proof.
  intros lens codes root0 t0 c st Hwf Hpre Hwr.
  destruct (pre_lens_go lens codes root0 t0 c st Hpre)
    as (_ & _ & _ & _ & Hmx & Hlens & Hcodes & Hdrop & Hlen).
  assert (Hlb : LensBounded c).
  { intros i Hi. rewrite Hlens. rewrite Hcodes in Hi.
    destruct Hwf as (_ & Hl & _ & _). unfold MAXBITS in Hl. apply Hl; exact Hi. }
  assert (Hr : 1 <= x_root c).
  { apply (it_pre_root_pos CT_LENS lens codes root0 t0 c st); [|exact Hpre].
    destruct Hwf as (_ & _ & Hr0 & _). lia. }
  apply (width_along_of_inv c st Hr Hmx).
  apply (loopwidthinv_of_work_range c st Hlb Hwr).
  split; [left; exact Hdrop | exact Hlen].
Qed.

Definition WorkRangeAtPre : Prop :=
  forall lens codes root0 t0 c st,
    it_wf CT_LENS lens codes root0 ->
    it_pre CT_LENS lens codes root0 t0 = PreGo c st ->
    WorkInRange c.

(** AND IT IS NOT A RESIDUE.  Proved, from [it_wf] alone. *)
Theorem work_range_at_pre : WorkRangeAtPre.
Proof.
  intros lens codes root0 t0 c st Hwf Hpre sym.
  destruct (pre_lens_go lens codes root0 t0 c st Hpre)
    as (_ & _ & _ & _ & _ & _ & Hcodes & _ & _).
  rewrite Hcodes.
  apply (pre_lens_work_range lens codes root0 t0 c st); [|exact Hpre].
  destruct Hwf as (H & _). exact H.
Qed.

(** So huffman-id's index bound is a theorem here too — it is exactly the sort range
    read above the match boundary, with [codes <= 288] closing the gap to 30. *)
Theorem len_arm_index_bounded_thm : LenArmIndexBounded.
Proof.
  intros lens codes root0 t0 c st sym Hpre Hle Hlt Hsym.
  destruct (pre_lens_go lens codes root0 t0 c st Hpre)
    as (_ & _ & Hmt & _ & _ & _ & _ & _ & _).
  pose proof (pre_lens_work_range lens codes root0 t0 c st Hlt Hpre sym) as Hwr.
  rewrite Hmt. lia.
Qed.

Theorem width_of_work_range : WorkRangeAtPre -> LenWidthAlong.
Proof.
  intros H lens codes root0 t0 c st Hwf Hpre.
  exact (width_along_of_work_range lens codes root0 t0 c st Hwf Hpre
           (H lens codes root0 t0 c st Hwf Hpre)).
Qed.


Theorem residues_reduce_to_width :
  LenArmIndexBounded -> LenWidthAlong -> LenLoopResidues.
Proof.
  intros Harm Hw lens codes root0 t0 c st Hwf Hpre.
  assert (Hlt : 0 < codes) by (destruct Hwf as (H & _); exact H).
  assert (Hle : codes <= 288).
  { destruct Hwf as (_ & _ & _ & Hty).
    destruct Hty as [[H1 _]|[[_ H2]|[H1 _]]];
      [unfold CT_LENS, CT_CODES in H1; discriminate
      |exact H2
      |unfold CT_LENS, CT_DISTS in H1; discriminate]. }
  split.
  - destruct (pre_lens_go lens codes root0 t0 c st Hpre)
      as (_ & _ & Hmt & _ & _ & _ & _ & _ & _).
    exact (len_arm_ok_from_pre lens codes root0 t0 c st Harm Hpre Hle Hlt Hmt).
  - exact (Hw lens codes root0 t0 c st Hwf Hpre).
Qed.

Definition ModelProv (t0 : ztbl) (o : option ItOut) : Prop :=
  match o with Some out => ProvT t0 (o_tbl out) | None => True end.

Lemma provT_model : forall lens codes root0 t0,
  LenLoopResidues ->
  it_wf CT_LENS lens codes root0 ->
  ModelProv t0 (it_model CT_LENS lens codes root0 t0).
Proof.
  intros lens codes root0 t0 Hres Hwf. unfold ModelProv, it_model.
  destruct (it_pre CT_LENS lens codes root0 t0) as [|t| |c st] eqn:E.
  - cbn [o_tbl]. apply provT_refl.
  - cbn [o_tbl]. exact (pre_lens_empty lens codes root0 t0 t E).
  - cbn [o_tbl]. apply provT_refl.
  - destruct (Hres lens codes root0 t0 c st Hwf E) as [Harm Halong].
    destruct (pre_lens_go lens codes root0 t0 c st E)
      as (Hex & Hba & Hmt & Htbl & _ & _ & _ & _ & _).
    destruct (it_loop (S (Z.to_nat codes)) c st) as [r|] eqn:Hl; [|exact I].
    assert (Hp : ProvT t0 (step_table r)).
    { apply (provT_loop (S (Z.to_nat codes)) t0 c st r Hex Hba Hmt Harm Halong);
        [rewrite Htbl; apply provT_refl | exact Hl]. }
    destruct r as [st'|st'|tt]; cbn [step_table] in Hp.
    + exact I.
    + cbn [o_tbl]. apply provT_finish. exact Hp.
    + cbn [o_tbl]. exact Hp.
Qed.

Theorem lentblprov_of_residues : LenLoopResidues -> LenTblProv.
Proof.
  intros Hres lens codes root0 t0 out Hwf H.
  pose proof (provT_model lens codes root0 t0 Hres Hwf) as HM.
  rewrite H in HM. exact HM.
Qed.

(* ######################################################################### *)
(* 9b. THE FIVE ARM FACTS, PROVED HERE — so the ask closes with NO premises    *)
(* ######################################################################### *)

(** These five are [Gw.GtLenOk]'s, where they are Qed with their measurements (which
    index the premise fires at, which endpoints are attained, the garbage-slot
    attribution).  That file is frozen at its digest and has no artifact, so it cannot
    be cited from a file meant to be consumable.  Re-proved here in the shortest form
    that closes the ask; the MEASUREMENTS are not reproduced and GtLenOk remains where
    they live.  Duplication disclosed. *)

Definition lc_len_okb (h : Code) : bool :=
  Z.eqb (Z.land (c_op h) 16) 0
  || (Z.leb 3 (c_val h)
      && Z.leb (c_val h + Z.shiftl 1 (Z.land (c_op h) 15) - 1) 258).

Lemma lc_len_okb_sound : forall h, lc_len_okb h = true -> lc_len_ok h.
Proof.
  intros h H Hfire. unfold lc_len_okb in H.
  apply orb_prop in H as [H|H].
  - apply Z.eqb_eq in H. contradiction.
  - apply andb_prop in H as [H1 H2].
    apply Z.leb_le in H1. apply Z.leb_le in H2. split; assumption.
Qed.

Lemma arm_literal : forall b w, lc_len_ok (mkCodeT 0 b w).
Proof. intros b w. apply lc_len_okb_sound. vm_compute. reflexivity. Qed.

Lemma arm_invalid : forall b, lc_len_ok (mkCodeT (32 + 64) b 0).
Proof. intros b. apply lc_len_okb_sound. vm_compute. reflexivity. Qed.

Lemma arm_marker : forall b v, lc_len_ok (mkCodeT 64 b v).
Proof. intros b v. apply lc_len_okb_sound. vm_compute. reflexivity. Qed.

(** The pointer arm: [op <= 15] keeps bit 4 clear, so the premise never fires. *)
Lemma land_16_of_small : forall op, 0 <= op <= 15 -> Z.land op 16 = 0.
Proof.
  intros op H.
  rewrite <- (Z2Nat.id op) by lia.
  assert (Hk : (Z.to_nat op < 16)%nat) by lia.
  revert Hk. generalize (Z.to_nat op). intros k Hk.
  do 16 (destruct k as [|k]; [vm_compute; reflexivity|]). lia.
Qed.

(** [mkCodeT] TRUNCATES: [c_op (mkCodeT op b v) = u8 op = op mod 256].  So even the
    pointer arm's vacuity needs the range to survive the cast, which is why this is a
    lemma and not a [reflexivity]. *)
Lemma c_op_mkCodeT_small : forall op b v, 0 <= op < 256 -> c_op (mkCodeT op b v) = op.
Proof. intros op b v H. unfold mkCodeT, u8. cbn [c_op]. apply Z.mod_small. lia. Qed.

Lemma arm_pointer : forall op b v, 0 <= op <= 15 -> lc_len_ok (mkCodeT op b v).
Proof.
  intros op b v Hop. apply lc_len_okb_sound. unfold lc_len_okb.
  rewrite (c_op_mkCodeT_small op b v) by lia.
  rewrite (land_16_of_small op Hop). reflexivity.
Qed.

(** The base arm, over all 31 indices of [lext]/[lbase].  The check does not read the
    bit-count field, so one pass at [b = 0] settles every [b]. *)
Lemma len_entry_okb_b_indep : forall j b,
  lc_len_okb (len_entry j b) = lc_len_okb (len_entry j 0).
Proof. intros j b. reflexivity. Qed.

Lemma arm_base : forall j b, 0 <= j <= 30 -> lc_len_ok (len_entry j b).
Proof.
  intros j b Hj. apply lc_len_okb_sound.
  rewrite len_entry_okb_b_indep.
  rewrite <- (Z2Nat.id j) by lia.
  assert (Hk : (Z.to_nat j < 31)%nat) by lia.
  revert Hk. generalize (Z.to_nat j). intros k Hk.
  do 31 (destruct k as [|k]; [vm_compute; reflexivity|]). lia.
Qed.

(* ######################################################################### *)
(* 10.  THE ASK, CLOSED                                                       *)
(* ######################################################################### *)

Section Residue.

  Hypothesis literal_vac : forall b w, lc_len_ok (mkCodeT 0 b w).
  Hypothesis invalid_vac : forall b, lc_len_ok (mkCodeT (32 + 64) b 0).
  Hypothesis marker_vac  : forall b v, lc_len_ok (mkCodeT 64 b v).
  Hypothesis pointer_vac : forall op b v, 0 <= op <= 15 -> lc_len_ok (mkCodeT op b v).
  Hypothesis base_ok     : forall j b, 0 <= j <= 30 -> lc_len_ok (len_entry j b).

  Theorem prov_closes_the_ask :
    LenTblProv ->
    forall lens codes root0 t0 out,
      it_wf CT_LENS lens codes root0 ->
      (forall i, lc_len_ok (t0 i)) ->
      it_model CT_LENS lens codes root0 t0 = Some out ->
      forall i, lc_len_ok (o_tbl out i).
  Proof.
    intros Hprov lens codes root0 t0 out Hwf Ht0 Hmodel.
    apply (prov_gives_lc_len_ok literal_vac invalid_vac marker_vac pointer_vac
             base_ok t0 (o_tbl out) Ht0
             (Hprov lens codes root0 t0 out Hwf Hmodel)).
  Qed.

  (** And the whole chain in one statement: huffman-id's index bound, the width half of
      the fill-loop invariant, and the five arm facts give [lc_len_ok] on every entry
      of a built length table. *)
  Theorem width_closes_the_ask :
    LenArmIndexBounded -> LenWidthAlong ->
    forall lens codes root0 t0 out,
      it_wf CT_LENS lens codes root0 ->
      (forall i, lc_len_ok (t0 i)) ->
      it_model CT_LENS lens codes root0 t0 = Some out ->
      forall i, lc_len_ok (o_tbl out i).
  Proof.
    intros Harm Hw. apply prov_closes_the_ask.
    exact (lentblprov_of_residues (residues_reduce_to_width Harm Hw)).
  Qed.

  (** ONE PREMISE, and it is the work array's range.  This is the row's remainder in
      a single statement. *)
  Theorem work_range_closes_the_ask :
    LenArmIndexBounded -> WorkRangeAtPre ->
    forall lens codes root0 t0 out,
      it_wf CT_LENS lens codes root0 ->
      (forall i, lc_len_ok (t0 i)) ->
      it_model CT_LENS lens codes root0 t0 = Some out ->
      forall i, lc_len_ok (o_tbl out i).
  Proof.
    intros Harm Hwr. apply width_closes_the_ask;
      [exact Harm | exact (width_of_work_range Hwr)].
  Qed.


End Residue.

(* ######################################################################### *)
(* 11.  THE ASK, CLOSED WITH NO PREMISES AT ALL                                *)
(* ######################################################################### *)

(** The whole question the row was opened for: every entry of a length table that
    [it_model] builds satisfies [InflateFast.lc_len_ok], given only the caller's
    well-formedness and the same property of the table it was handed.  No hypotheses,
    no [Admitted], nothing routed elsewhere.

    The [t0] premise is not a residue but a recurrence: [inf_table] hands [it_model]
    the LIVE [state->codes] array ([Inflate.v:1241]), so a caller carries this property
    forward across builds rather than establishing it once.  See [Gw.GtLcodeBound] for
    what that array looks like after the distance build, which is where the consumer's
    own statement turns out to be false. *)
Theorem built_len_table_is_lc_len_ok :
  forall lens codes root0 t0 out,
    it_wf CT_LENS lens codes root0 ->
    (forall i, lc_len_ok (t0 i)) ->
    it_model CT_LENS lens codes root0 t0 = Some out ->
    forall i, lc_len_ok (o_tbl out i).
Proof.
  apply (work_range_closes_the_ask arm_literal arm_invalid arm_marker arm_pointer
           arm_base len_arm_index_bounded_thm work_range_at_pre).
Qed.

(** NON-VACUITY OF THE FINAL THEOREM, third instance of this check in this file and
    the reason the two retractions above were caught.  A concrete input that satisfies
    [it_wf] and on which [it_model] really does build a table: [o_ret = 0], four
    entries.

    HONEST LABEL: this witness exercises the theorem, not the interesting arm.  Its
    four symbols are all below 257, so every entry is a literal ([c_op = 0]) and
    [lc_len_ok]'s premise never fires in it.  Premise-firing is covered one level down
    by [arm_base], which is checked at all 31 indices of [lext]/[lbase]; an end-to-end
    witness whose premise fires needs a code over 258+ symbols, which I have not
    built. *)
Lemma the_ask_is_not_vacuous :
  it_wf CT_LENS (zlist [2;2;2;2]) 4 9
  /\ match it_model CT_LENS (zlist [2;2;2;2]) 4 9 tnone with
     | Some o => o_ret o = 0 /\ o_used o = 4
     | None => False
     end.
Proof.
  assert (Hb : forall i, 0 <= i < 4 -> zlist [2;2;2;2] i = 2).
  { intros i Hi. rewrite <- (Z2Nat.id i) by lia.
    assert (Hk : (Z.to_nat i < 4)%nat) by lia.
    revert Hk. generalize (Z.to_nat i). intros k Hk.
    do 4 (destruct k as [|k]; [reflexivity|]). lia. }
  split.
  - unfold it_wf. refine (conj _ (conj _ (conj _ _))).
    + lia.
    + intros i Hi. rewrite (Hb i Hi). unfold MAXBITS. lia.
    + unfold MAXBITS. lia.
    + right; left; split; [reflexivity | lia].
  - vm_compute. split; reflexivity.
Qed.

Print Assumptions the_ask_is_not_vacuous.
Print Assumptions it_sort_snd_range.
Print Assumptions sort_zzero_range.
Print Assumptions work_range_at_pre.
Print Assumptions len_arm_index_bounded_thm.
Print Assumptions lc_len_okb_sound.
Print Assumptions arm_literal.
Print Assumptions arm_invalid.
Print Assumptions arm_marker.
Print Assumptions land_16_of_small.
Print Assumptions c_op_mkCodeT_small.
Print Assumptions arm_pointer.
Print Assumptions arm_base.
Print Assumptions built_len_table_is_lc_len_ok.
Print Assumptions provT_refl.
Print Assumptions prov_gives_lc_len_ok.
Print Assumptions provT_tset.
Print Assumptions provT_it_fill.
Print Assumptions provE_marker.
Print Assumptions provE_pointer.
Print Assumptions provE_it_here.
Print Assumptions len_arm_ok_from_pre.
Print Assumptions provE_it_here_from_pre.
Print Assumptions subsz_flat_bound_is_false.
Print Assumptions it_subsz_bounds.
Print Assumptions it_findmax_le_max.
Print Assumptions ptr_width_from_widths.
Print Assumptions ptr_width_from_inv.
Print Assumptions ex_writes_a_pointer.
Print Assumptions ptr_width_ok_is_satisfiable.
Print Assumptions provT_step.
Print Assumptions along_here.
Print Assumptions along_step.
Print Assumptions width_along_of_inv.
Print Assumptions it_findmin_le.
Print Assumptions widthst_len1.
Print Assumptions widthst_forward.
Print Assumptions widthst_iter.
Print Assumptions loopwidthinv_of_work_range.
Print Assumptions width_along_of_work_range.
Print Assumptions width_of_work_range.
Print Assumptions provT_loop.
Print Assumptions provT_finish.
Print Assumptions pre_lens_ok.
Print Assumptions pre_work_ok.
Print Assumptions pre_lens_work_range.
Print Assumptions pre_lens_go.
Print Assumptions pre_lens_empty.
Print Assumptions residues_reduce_to_width.
Print Assumptions provT_model.
Print Assumptions lentblprov_of_residues.
Print Assumptions prov_closes_the_ask.
Print Assumptions width_closes_the_ask.
Print Assumptions work_range_closes_the_ask.
