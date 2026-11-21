(** * CoverChain — THE COMPOSITION of the coverage obligation.

    OWNER: huffman-id.  This is the obligation ld-seams routed to me in
    §LD-DYNSEAM: [SendTreeRT.send_tree_roundtrip]'s hypothesis

        cl_bits cl (send_tree_items t maxc) = Some bits

    WHY THIS FILE EXISTS AND WHY IT IS NOT "GLUE".  I had decomposed that
    hypothesis into three legs and reported them to ld-seams as the work ahead.
    Grepping my own package before starting found ALL THREE ALREADY Qed, written
    at different times for different consumers:

      leg              theorem                          file
      (reduction)      cl_bits_total                    HuffCover.v
      (S)              scan_tree_positive               ScanCount.v
      (B)              build_tree_bl_final              BtTerm.v

    and it also found that **NOTHING ANYWHERE REQUIRES ANY OF THE THREE.**  A
    grep for consumers of all three names across the whole package returns zero
    hits.  Three separately-green segments, never composed — which is exactly the
    configuration in which an interface defect cannot be detected, because a
    hypothesis is only ever checked when something tries to discharge it.

    WHAT WRITING THE COMPOSITION FOUND.  One real gap and three that discharge:

      SEAM A  REAL, and it is a defect in MY OWN (S).  [scan_tree_positive]
              requires a FRESH frequency table ([forall s', t_freq bl s' = 0]).
              [Trees.v:806-810] calls [scan_tree] TWICE — the literal tree, then
              the distance tree, into the SAME [bl_tree] — so the second call's
              input table is not fresh and (S) as stated does not apply to it.
              Nor does positivity from the first call automatically survive the
              second: [t_setfreq] applies [u16] ([Trees.v:227]), so a frequency
              CAN DECREASE by wrapping, and ruling that out is exactly what
              ScanCount's [Budget] does — at a base of zero, which is the
              assumption that fails here.  Carried below as [ScanKeepsPos].
      SEAM B  free.  [LensOf] is [nth]-shaped and [CLCovers] is
              [nth_error]-shaped; [nth_error_nth'] bridges them GIVEN a length
              bound on [cl], which [LensOf] does not supply — see the note on
              [covered_of_len_bound], where the vacuity matters.
      SEAM C  free, and pleasingly so: [CLWf]'s own [CLit] clause carries
              [l <= 15], and [SendGoWf.send_tree_items_wf] already proves [CLWf]
              of the stream.  So "every symbol the stream uses is a legal
              code-length symbol" is not new work.
      SEAM D  not mine.  [build_bl_tree] scans at [ts_maxcode s TK_L] while
              [send_all_trees] sends at [lcodes - 1] ([Trees.v:832]); that those
              agree is a fact about the caller and belongs with the dynamic seam.
              This file quantifies the scan-time [maxc] and uses it on both
              sides, so SEAM D is VISIBLE as the gap between this theorem's
              [maxcL]/[maxcD] and [send_all_trees]' arguments rather than
              smuggled in as an equation.

    So the honest status: the three legs are proved, the composition needs one
    repair to my own theorem, and one hypothesis belongs to another lane. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff Trees DeflateSpec.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  HuffGenCodes ClStream SendItems SendGo SendGoWf HuffCover ScanCount
  BuildChain BtTerm.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** ** SEAM C: the symbols an item stream uses are code-length symbols

    [CLWf]'s [CLit] clause is [(l <= 15)%nat] and the three repeat forms emit the
    fixed symbols 16/17/18, so the whole alphabet is [0..18] — the code-length
    tree's own alphabet, [BL_CODES = 19] symbols.  This needs [CLWf] rather than
    the tree's length bound directly: the bound is what MAKES [CLWf] hold, but the
    stream is the thing whose symbols are being ranged over. *)
Lemma items_syms_range : forall items acc s,
  CLWf acc items -> In s (items_syms items) -> 0 <= s <= 18.
Proof.
  induction items as [|it tl IH]; intros acc s Hwf Hin; [cbn in Hin; contradiction|].
  cbn [items_syms flat_map] in Hin. apply in_app_or in Hin.
  destruct it as [l|p k|k|k]; cbn [CLWf] in Hwf.
  - destruct Hwf as [Hl Hwf']. destruct Hin as [Hin|Hin].
    + cbn [item_syms In] in Hin. destruct Hin as [Hs|[]]. lia.
    + eapply IH; eassumption.
  - destruct Hwf as [Hp [Hk Hwf']]. destruct Hin as [Hin|Hin].
    + cbn [item_syms In] in Hin. destruct Hin as [Hs|[]].
      unfold REP_3_6 in Hs. lia.
    + eapply IH; eassumption.
  - destruct Hwf as [Hk Hwf']. destruct Hin as [Hin|Hin].
    + cbn [item_syms In] in Hin. destruct Hin as [Hs|[]].
      unfold REPZ_3_10 in Hs. lia.
    + eapply IH; eassumption.
  - destruct Hwf as [Hk Hwf']. destruct Hin as [Hin|Hin].
    + cbn [item_syms In] in Hin. destruct Hin as [Hs|[]].
      unfold REPZ_11_138 in Hs. lia.
    + eapply IH; eassumption.
Qed.

(** The code-length tree's alphabet really is 19 wide, so [items_syms_range]'s
    conclusion lines up with [BtTerm]'s [0 <= s0 < sd_elems TK_BL]. *)
Example bl_elems_is_19 : sd_elems TK_BL = 19.
Proof. reflexivity. Qed.

(** ** SEAM B: [LensOf] (nth) to [CLCovers] (nth_error)

    Two spellings of "the list mirrors the tree's lengths".  The bridge needs a
    LENGTH fact, and that is not a formality: [LensOf] quantifies over
    [k < length L] and is therefore VACUOUSLY TRUE OF THE EMPTY LIST, so a
    coverage statement resting on [LensOf] alone would be satisfied by [cl = []].
    The [19 <= length cl] hypothesis is what rules that out, and it is the reason
    this is stated as its own lemma instead of inlined. *)
Lemma covered_of_len_bound : forall blt cl s len,
  LensOf blt cl ->
  (19 <= length cl)%nat ->
  0 <= s <= 18 ->
  t_len blt s = len ->
  1 <= len <= 7 ->
  exists n, nth_error cl (Z.to_nat s) = Some n /\ (1 <= n <= 7)%nat.
Proof.
  intros blt cl s len HL Hlen Hs Ht Hr.
  assert (Hk : (Z.to_nat s < length cl)%nat) by lia.
  exists (nth (Z.to_nat s) cl 0%nat). split.
  - apply nth_error_nth'. exact Hk.
  - specialize (HL (Z.to_nat s) Hk).
    rewrite Z2Nat.id in HL by lia.
    rewrite Ht in HL. lia.
Qed.

(** ** The per-symbol chain: (B) composed with SEAMs B and C

    Positive frequency in the table [build_tree] consumes gives a code of width
    [1..7] in [cl]. *)
Theorem covered_of_freq_pos :
  forall (st : TSt) (cl : list nat) (s : Z)
         t0 hp0 dep0 hlen0 maxc0 t1 hp1 dep1 hlen1 maxc1 ol1 sl1,
  DlNn (ts_trees st TK_BL) ->
  0 <= s <= 18 ->
  0 < t_freq (ts_trees st TK_BL) s ->
  bt_init (Z.to_nat L_CODES + 2) 0 (sd_elems TK_BL) (ts_trees st TK_BL)
          (ts_heap st) (ts_depth st) 0 (-1) = (t0, hp0, dep0, hlen0, maxc0) ->
  bt_force2 3%nat (sd_stree TK_BL) t0 hp0 dep0 hlen0 maxc0
            (ts_optlen st) (ts_statlen st)
    = (t1, hp1, dep1, hlen1, maxc1, ol1, sl1) ->
  LensOf (ts_trees (build_tree TK_BL st) TK_BL) cl ->
  (19 <= length cl)%nat ->
  exists n, nth_error cl (Z.to_nat s) = Some n /\ (1 <= n <= 7)%nat.
Proof.
  intros st cl s t0 hp0 dep0 hlen0 maxc0 t1 hp1 dep1 hlen1 maxc1 ol1 sl1
         Hnn Hs Hpos Hinit Hforce HL Hlen.
  assert (Hb : 1 <= t_len (ts_trees (build_tree TK_BL st) TK_BL) s <= 7).
  { eapply build_tree_bl_final; try eassumption.
    all: try (rewrite bl_elems_is_19; try unfold L_CODES; lia).
    all: try lia. }
  exact (covered_of_len_bound (ts_trees (build_tree TK_BL st) TK_BL) cl s
           (t_len (ts_trees (build_tree TK_BL st) TK_BL) s)
           HL Hlen Hs eq_refl Hb).
Qed.

(** ** SEAM A, NAMED

    What the composition needs of [scan_tree] and cannot get from
    [scan_tree_positive]: after BOTH scans, every symbol either stream uses has a
    positive frequency.  Stated over the pair because that is how
    [build_bl_tree] uses it ([Trees.v:806-810]) — one table, two scans.

    Deliberately a hypothesis here and a theorem elsewhere.  Keeping them apart is
    what makes the composition's other seams checkable NOW rather than after the
    repair — and it is why the repair has a consumer waiting for it, which is the
    condition under which its statement gets tested. *)
Definition ScanKeepsPos : Prop :=
  forall tL maxcL tD maxcD bl p1 p2 s,
    0 <= maxcL <= 285 -> 0 <= maxcD <= 285 ->
    (forall i, 0 <= i <= maxcL -> 0 <= t_len tL i <= 15) ->
    (forall i, 0 <= i <= maxcD -> 0 <= t_len tD i <= 15) ->
    (forall s', t_freq bl s' = 0) ->
    p1 = scan_tree tL maxcL bl ->
    p2 = scan_tree tD maxcD (snd p1) ->
    In s (items_syms (send_tree_items (fst p1) maxcL))
      \/ In s (items_syms (send_tree_items (fst p2) maxcD)) ->
    0 < t_freq (snd p2) s.

(** ** THE COMPOSITION

    Coverage for BOTH code-length streams [send_all_trees] emits
    ([Trees.v:832-833]), from: the two trees' length bounds, a fresh [bl_tree]
    (what [init_block] leaves — [Trees.v:347]), (B)'s heap-free hypotheses, and
    [ScanKeepsPos]. *)
Theorem cover_both_streams :
  forall (st st2 : TSt) (cl : list nat) tL maxcL tD maxcD p1 p2
         t0 hp0 dep0 hlen0 maxc0 t1 hp1 dep1 hlen1 maxc1 ol1 sl1,
  ScanKeepsPos ->
  0 <= maxcL <= 285 -> 0 <= maxcD <= 285 ->
  (forall i, 0 <= i <= maxcL -> 0 <= t_len tL i <= 15) ->
  (forall i, 0 <= i <= maxcD -> 0 <= t_len tD i <= 15) ->
  (forall s', t_freq (ts_trees st TK_BL) s' = 0) ->
  p1 = scan_tree tL maxcL (ts_trees st TK_BL) ->
  p2 = scan_tree tD maxcD (snd p1) ->
  (* the state [build_tree] runs on carries the twice-scanned table *)
  ts_trees st2 TK_BL = snd p2 ->
  DlNn (snd p2) ->
  bt_init (Z.to_nat L_CODES + 2) 0 (sd_elems TK_BL) (ts_trees st2 TK_BL)
          (ts_heap st2) (ts_depth st2) 0 (-1) = (t0, hp0, dep0, hlen0, maxc0) ->
  bt_force2 3%nat (sd_stree TK_BL) t0 hp0 dep0 hlen0 maxc0
            (ts_optlen st2) (ts_statlen st2)
    = (t1, hp1, dep1, hlen1, maxc1, ol1, sl1) ->
  LensOf (ts_trees (build_tree TK_BL st2) TK_BL) cl ->
  (19 <= length cl)%nat ->
  CLCovers cl (send_tree_items (fst p1) maxcL)
  /\ CLCovers cl (send_tree_items (fst p2) maxcD).
Proof.
  intros st st2 cl tL maxcL tD maxcD p1 p2 t0 hp0 dep0 hlen0 maxc0
         t1 hp1 dep1 hlen1 maxc1 ol1 sl1
         HSK HmcL HmcD H15L H15D Hfresh Hp1 Hp2 Hst2 Hnn Hinit Hforce HL Hlen.
  (* both halves are the same three steps; only which disjunct feeds
     [ScanKeepsPos] differs, so the chain is factored once. *)
  assert (Hchain : forall s,
            0 <= s <= 18 -> 0 < t_freq (snd p2) s ->
            exists n, nth_error cl (Z.to_nat s) = Some n /\ (1 <= n <= 7)%nat).
  { intros s Hs Hpos. eapply covered_of_freq_pos; try eassumption.
    - rewrite Hst2. exact Hnn.
    - rewrite Hst2. exact Hpos. }
  (* the guard the [0xffff] store establishes, on each scanned tree *)
  assert (Hwf1 : CLWf nil (send_tree_items (fst p1) maxcL)).
  { apply send_tree_items_wf.
    - lia.
    - rewrite Hp1. unfold scan_tree. cbn [fst].
      rewrite t_len_setlen_same. reflexivity.
    - rewrite Hp1. unfold scan_tree. cbn [fst]. intros i Hi.
      rewrite t_len_setlen_other by lia. apply H15L. lia. }
  assert (Hwf2 : CLWf nil (send_tree_items (fst p2) maxcD)).
  { apply send_tree_items_wf.
    - lia.
    - rewrite Hp2. unfold scan_tree. cbn [fst].
      rewrite t_len_setlen_same. reflexivity.
    - rewrite Hp2. unfold scan_tree. cbn [fst]. intros i Hi.
      rewrite t_len_setlen_other by lia. apply H15D. lia. }
  (* the applications are FULLY EXPLICIT on purpose: [eapply X; eassumption]
     failed here, because with [?items] still open [eassumption] resolves the
     [CLWf] goal against whichever hypothesis comes first in the context and
     then cannot satisfy the [In] goal.  Naming the arguments removes the
     ordering dependence entirely. *)
  split; intros s Hin.
  - apply Hchain.
    + exact (items_syms_range _ nil s Hwf1 Hin).
    + apply (HSK tL maxcL tD maxcD (ts_trees st TK_BL) p1 p2 s
               HmcL HmcD H15L H15D Hfresh Hp1 Hp2).
      left. exact Hin.
  - apply Hchain.
    + exact (items_syms_range _ nil s Hwf2 Hin).
    + apply (HSK tL maxcL tD maxcD (ts_trees st TK_BL) p1 p2 s
               HmcL HmcD H15L H15D Hfresh Hp1 Hp2).
      right. exact Hin.
Qed.

(** ** ...and the capstone's hypothesis, which is what was actually asked for.

    [cl_bits_total] gets its FIRST consumer here.  Trivial as a proof, and the
    only reason it is written down: a re-export with no consumer is what the
    header's zero-hit grep was about. *)
Corollary cl_bits_of_cover : forall cl items,
  CLCovers cl items -> exists bits, cl_bits cl items = Some bits.
Proof. exact cl_bits_total. Qed.

Print Assumptions items_syms_range.
Print Assumptions covered_of_len_bound.
Print Assumptions covered_of_freq_pos.
Print Assumptions cover_both_streams.
