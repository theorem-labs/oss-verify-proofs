(** * ScanBase — SEAM A: [scan_tree] at a NON-FRESH frequency table.

    OWNER: huffman-id.  This repairs the one real gap CoverChain.v found, and it
    is a gap in my own ScanCount.v.

    THE DEFECT, and why it survived being Qed.  [ScanCount.scan_tree_counts] and
    [scan_tree_positive] both require [Budget bl 0] / [forall s', t_freq bl s' = 0]
    — a FRESH frequency table.  That is true of [init_block]'s table
    ([Trees.v:347]) and false of the one the SECOND [scan_tree] call sees, because
    [build_bl_tree] scans twice into the same [bl_tree] ([Trees.v:806-810]).  So
    the theorems applied to the literal tree and to nothing else.

    Nobody noticed because nothing consumed them.  The freshness hypothesis is
    checkable only at a call site, and until CoverChain.v there was no call site —
    which is the general shape: a hypothesis is tested when something tries to
    discharge it, and a theorem with no consumer has never had its hypotheses
    tested at all.

    WHY POSITIVITY DOES NOT JUST SURVIVE.  [t_setfreq] applies [u16]
    ([Trees.v:227]), so a frequency CAN DECREASE — wrap 65536 to 0 and a symbol
    that was counted becomes uncounted.  Monotonicity across the second scan is
    therefore not a structural fact; it needs the same no-wrap budget the counting
    theorem needed, and needs it at a base that is no longer zero.

    THE FIX, and the one design decision worth recording: DECOUPLE THE BUDGET
    INDEX FROM THE LOOP INDEX.  ScanCount's [Budget bl n] ties the allowance
    [3 * n] to the loop's own position, which is what makes it unusable at a
    non-zero base.  Here the budget carries its own index [m] plus a CEILING
    parameter [M] that is CONSTANT across the recursion, with the invariant
    [m + (maxc + 1 - n) <= M].  Because [M] does not move, every recursive call's
    side condition is the same expression and falls to [lia]; a formulation where
    the conclusion's index moved with the recursion made every arm's [Budget] goal
    a different arithmetic shape from the one [budget_short] produces.

    [scan_go_counts_gen] below is ScanCount's induction with that change and no
    other.  It was derived from the pinned text by explicit substitution rather
    than retyped, and reviewed against the original arm by arm. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff Trees DeflateSpec.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  HuffGenCodes ClStream SendItems SendGo SendGoLens SendGoWf HuffCover
  ScanCount BuildChain BtTerm CoverChain.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** ** Budget preservation

    The output table's allowance, at a ceiling that does not move.  Note this
    needs NO fuel bound and NO [count] hypotheses: a budget is preserved whether
    or not the loop had enough fuel to finish, which is what lets the fuel
    argument stay entirely inside the counting theorem. *)
Lemma scan_go_budget : forall f t maxc n prevlen nextlen count maxcnt mincnt bl m M,
  (forall i, 0 <= i <= maxc -> 0 <= t_len t i <= 15) ->
  n <= maxc + 1 -> 0 <= maxc <= 285 ->
  nextlen = t_len t n ->
  0 <= n -> 0 <= count -> mincnt <= 4 ->
  Budget bl m -> 0 <= m ->
  m + (maxc + 1 - n) <= M -> 3 * M <= 65535 ->
  Budget (scan_go f t maxc n prevlen nextlen count maxcnt mincnt bl) M.
Proof.
  induction f as [|f IH];
    intros t maxc n prevlen nextlen count maxcnt mincnt bl m M
           Hlen15 Hn Hmc Hnl Hn0 Hc Hmn Hbud Hm0 HmM HM.
  - cbn [scan_go]. apply (Budget_mono bl m); [exact Hbud | lia].
  - cbn [scan_go].
    destruct (Z.ltb maxc n) eqn:Eexit.
    + apply (Budget_mono bl m); [exact Hbud | lia].
    + apply Z.ltb_ge in Eexit.
      assert (H15 : 0 <= t_len t n <= 15) by (apply Hlen15; lia).
      assert (Hceil : 3 * (m + 1) <= 65535) by lia.
      destruct ((Z.ltb (count + 1) maxcnt) && (Z.eqb nextlen (t_len t (n + 1))))
               eqn:Eacc.
      * (* ACCUMULATE: no store, so the budget index does not advance *)
        apply (IH t maxc (n + 1) prevlen (t_len t (n + 1)) (count + 1) maxcnt
                 mincnt bl m M); try assumption; try lia.
      * destruct (Z.ltb (count + 1) mincnt) eqn:Emin.
        -- (* short run: one slot, up to [mincnt - 1 <= 3] added *)
           apply Z.ltb_lt in Emin.
           apply (IH t maxc (n + 1) nextlen (t_len t (n + 1)) 0
                    (if Z.eqb (t_len t (n + 1)) 0 then 138
                     else if Z.eqb nextlen (t_len t (n + 1)) then 6 else 7)
                    (if Z.eqb (t_len t (n + 1)) 0 then 3
                     else if Z.eqb nextlen (t_len t (n + 1)) then 3 else 4)
                    _ (m + 1) M);
             try assumption; try lia; try if_bound.
           apply budget_short; try assumption; lia.
        -- destruct (negb (Z.eqb nextlen 0)) eqn:Ez.
           ++ apply negb_true_iff, Z.eqb_neq in Ez.
              destruct (negb (Z.eqb nextlen prevlen)) eqn:Ep.
              ** (* two slots: [curlen] and 16, distinct because curlen <= 15 *)
                 apply (IH t maxc (n + 1) nextlen (t_len t (n + 1)) 0
                          (if Z.eqb (t_len t (n + 1)) 0 then 138
                           else if Z.eqb nextlen (t_len t (n + 1)) then 6 else 7)
                          (if Z.eqb (t_len t (n + 1)) 0 then 3
                           else if Z.eqb nextlen (t_len t (n + 1)) then 3 else 4)
                          _ (m + 1) M);
                   try assumption; try lia; try if_bound.
                 apply budget_two; try assumption; try unfold REP_3_6; lia.
              ** apply (IH t maxc (n + 1) nextlen (t_len t (n + 1)) 0
                          (if Z.eqb (t_len t (n + 1)) 0 then 138
                           else if Z.eqb nextlen (t_len t (n + 1)) then 6 else 7)
                          (if Z.eqb (t_len t (n + 1)) 0 then 3
                           else if Z.eqb nextlen (t_len t (n + 1)) then 3 else 4)
                          _ (m + 1) M);
                   try assumption; try lia; try if_bound.
                 apply budget_one; try assumption; lia.
           ++ apply negb_false_iff, Z.eqb_eq in Ez.
              destruct (Z.leb (count + 1) 10) eqn:Eten.
              ** apply (IH t maxc (n + 1) nextlen (t_len t (n + 1)) 0
                          (if Z.eqb (t_len t (n + 1)) 0 then 138
                           else if Z.eqb nextlen (t_len t (n + 1)) then 6 else 7)
                          (if Z.eqb (t_len t (n + 1)) 0 then 3
                           else if Z.eqb nextlen (t_len t (n + 1)) then 3 else 4)
                          _ (m + 1) M);
                   try assumption; try lia; try if_bound.
                 apply budget_one; try assumption; lia.
              ** apply (IH t maxc (n + 1) nextlen (t_len t (n + 1)) 0
                          (if Z.eqb (t_len t (n + 1)) 0 then 138
                           else if Z.eqb nextlen (t_len t (n + 1)) then 6 else 7)
                          (if Z.eqb (t_len t (n + 1)) 0 then 3
                           else if Z.eqb nextlen (t_len t (n + 1)) then 3 else 4)
                          _ (m + 1) M);
                   try assumption; try lia; try if_bound.
                 apply budget_one; try assumption; lia.
Qed.

(** ** The counting theorem at a non-zero base

    ScanCount's induction with the budget index decoupled, and nothing else
    changed.  Every arm still supplies exactly the arithmetic its
    [budget_short]/[budget_one]/[budget_two] step needs; the only difference is
    that the allowance it spends is [m], not the loop position. *)
Lemma scan_go_counts_gen : forall f t maxc n prevlen nextlen count maxcnt mincnt bl s m M,
  t_len t (maxc + 1) = 65535 ->
  (forall i, 0 <= i <= maxc -> 0 <= t_len t i <= 15) ->
  0 <= count -> 0 <= n - count -> n <= maxc + 1 -> 0 <= maxc <= 285 ->
  nextlen = t_len t n ->
  (maxc < n -> count = 0) ->
  (Z.to_nat (maxc + 1 - n) <= f)%nat ->
  mincnt <= 4 ->
  Budget bl m -> 0 <= m ->
  m + (maxc + 1 - n) <= M -> 3 * M <= 65535 ->
  t_freq (scan_go f t maxc n prevlen nextlen count maxcnt mincnt bl) s
  = t_freq bl s
    + hid_zcount s (items_syms (send_items f t maxc n prevlen nextlen count maxcnt mincnt)).
Proof.
  induction f as [|f IH];
    intros t maxc n prevlen nextlen count maxcnt mincnt bl s m M
           Hguard Hlen15 Hc Hnc Hn Hmc Hnl Hexit Hf Hmn Hbud Hm0 HmM HM.
  - cbn [scan_go send_items items_syms]. rewrite hid_zcount_nil. lia.
  - cbn [scan_go send_items].
    destruct (Z.ltb maxc n) eqn:Eexit.
    + cbn [items_syms]. rewrite hid_zcount_nil. lia.
    + apply Z.ltb_ge in Eexit.
      assert (H15 : 0 <= t_len t n <= 15) by (apply Hlen15; lia).
      assert (Hceil : 3 * (m + 1) <= 65535) by lia.
      destruct ((Z.ltb (count + 1) maxcnt) && (Z.eqb nextlen (t_len t (n + 1))))
               eqn:Eacc.
      * (* ACCUMULATE: nothing counted, nothing emitted *)
        apply andb_prop in Eacc as [Emax Eeq]. apply Z.eqb_eq in Eeq.
        assert (Hlt : n < maxc).
        { destruct (Z.eq_dec n maxc) as [->|Hne]; [|lia]. rewrite Hguard in Eeq. lia. }
        (* explicit [m]/[M]: they occur only in HYPOTHESES, so unification with
           the goal cannot determine them.  The original could write a bare
           [apply IH] because its budget index WAS the loop index and therefore
           appeared in the conclusion -- the one place decoupling costs anything.
           No [Budget_mono] step here: the accumulate trip performs no store, so
           the index does not advance and [Hbud] closes the goal outright. *)
        apply (IH t maxc (n + 1) prevlen (t_len t (n + 1)) (count + 1) maxcnt
                 mincnt bl s m M); try assumption; try lia; try if_bound.
      * assert (Hcur : Z.of_nat (Z.to_nat nextlen) = nextlen) by lia.
        destruct (Z.ltb (count + 1) mincnt) eqn:Emin.
        -- (* short run: count' literal codes of curlen; count' <= mincnt-1 <= 3 *)
           apply Z.ltb_lt in Emin.
           rewrite items_syms_app, items_syms_repeat_lit, Hcur, hid_zcount_app.
           destruct (Hbud nextlen) as [Hf0 Hf1].
           rewrite (IH t maxc (n + 1) nextlen (t_len t (n + 1)) 0
                      (if Z.eqb (t_len t (n + 1)) 0 then 138
                       else if Z.eqb nextlen (t_len t (n + 1)) then 6 else 7)
                      (if Z.eqb (t_len t (n + 1)) 0 then 3
                       else if Z.eqb nextlen (t_len t (n + 1)) then 3 else 4)
                      _ _ (m + 1) M);
             try assumption; try lia; try if_bound.
           ++ rewrite (step_short bl nextlen (count + 1) s) by lia. lia.
           ++ apply budget_short; try assumption; lia.
        -- destruct (negb (Z.eqb nextlen 0)) eqn:Ez.
           ++ apply negb_true_iff, Z.eqb_neq in Ez.
              destruct (negb (Z.eqb nextlen prevlen)) eqn:Ep.
              ** (* [CLit curlen; CRep curlen (count'-1)]: slots curlen and 16 *)
                 rewrite items_syms_app, items_syms_lit_rep, Hcur, hid_zcount_app.
                 destruct (Hbud nextlen) as [Hf0 Hf1].
                 destruct (Hbud REP_3_6) as [Hg0 Hg1].
                 rewrite (IH t maxc (n + 1) nextlen (t_len t (n + 1)) 0
                            (if Z.eqb (t_len t (n + 1)) 0 then 138
                             else if Z.eqb nextlen (t_len t (n + 1)) then 6 else 7)
                            (if Z.eqb (t_len t (n + 1)) 0 then 3
                             else if Z.eqb nextlen (t_len t (n + 1)) then 3 else 4)
                            _ _ (m + 1) M);
                   try assumption; try lia; try if_bound.
                 --- (* explicit args: a single [by] tactic must close FIVE side
                        goals here and [unfold REP_3_6] is only applicable to one
                        of them, which killed the whole chain *)
                     assert (Hne : nextlen <> REP_3_6) by (unfold REP_3_6; lia).
                     assert (Hfb : t_freq bl nextlen + 1 <= 65535) by lia.
                     assert (Hgb : t_freq bl REP_3_6 + 1 <= 65535) by lia.
                     rewrite (step_two bl nextlen REP_3_6 s Hne Hf0 Hfb Hg0 Hgb).
                     lia.
                 --- apply budget_two; try assumption; try unfold REP_3_6; lia.
              ** (* [CRep curlen count']: slot 16 only *)
                 rewrite items_syms_app, items_syms_rep, hid_zcount_app.
                 destruct (Hbud REP_3_6) as [Hg0 Hg1].
                 rewrite (IH t maxc (n + 1) nextlen (t_len t (n + 1)) 0
                            (if Z.eqb (t_len t (n + 1)) 0 then 138
                             else if Z.eqb nextlen (t_len t (n + 1)) then 6 else 7)
                            (if Z.eqb (t_len t (n + 1)) 0 then 3
                             else if Z.eqb nextlen (t_len t (n + 1)) then 3 else 4)
                            _ _ (m + 1) M);
                   try assumption; try lia; try if_bound.
                 --- rewrite (step_one bl REP_3_6 s) by lia. lia.
                 --- apply budget_one; try assumption; lia.
           ++ (* zero run: slot 17 or slot 18 *)
              apply negb_false_iff, Z.eqb_eq in Ez.
              destruct (Z.leb (count + 1) 10) eqn:Eten.
              ** rewrite items_syms_app, items_syms_z3, hid_zcount_app.
                 destruct (Hbud REPZ_3_10) as [Hg0 Hg1].
                 rewrite (IH t maxc (n + 1) nextlen (t_len t (n + 1)) 0
                            (if Z.eqb (t_len t (n + 1)) 0 then 138
                             else if Z.eqb nextlen (t_len t (n + 1)) then 6 else 7)
                            (if Z.eqb (t_len t (n + 1)) 0 then 3
                             else if Z.eqb nextlen (t_len t (n + 1)) then 3 else 4)
                            _ _ (m + 1) M);
                   try assumption; try lia; try if_bound.
                 --- rewrite (step_one bl REPZ_3_10 s) by lia. lia.
                 --- apply budget_one; try assumption; lia.
              ** rewrite items_syms_app, items_syms_z11, hid_zcount_app.
                 destruct (Hbud REPZ_11_138) as [Hg0 Hg1].
                 rewrite (IH t maxc (n + 1) nextlen (t_len t (n + 1)) 0
                            (if Z.eqb (t_len t (n + 1)) 0 then 138
                             else if Z.eqb nextlen (t_len t (n + 1)) then 6 else 7)
                            (if Z.eqb (t_len t (n + 1)) 0 then 3
                             else if Z.eqb nextlen (t_len t (n + 1)) then 3 else 4)
                            _ _ (m + 1) M);
                   try assumption; try lia; try if_bound.
                 --- rewrite (step_one bl REPZ_11_138 s) by lia. lia.
                 --- apply budget_one; try assumption; lia.
Qed.

(** ** Entry points, on the guarded tree [scan_tree] builds itself *)

Lemma scan_tree_budget : forall t maxc bl m M,
  0 <= maxc <= 285 ->
  (forall i, 0 <= i <= maxc -> 0 <= t_len t i <= 15) ->
  Budget bl m -> 0 <= m -> m + (maxc + 1) <= M -> 3 * M <= 65535 ->
  Budget (snd (scan_tree t maxc bl)) M.
Proof.
  intros t maxc bl m M Hmc Hlen15 Hbud Hm0 HmM HM.
  unfold scan_tree. cbn [snd].
  set (tg := t_setlen t (maxc + 1) 65535).
  assert (H15 : forall i, 0 <= i <= maxc -> 0 <= t_len tg i <= 15).
  { intros i Hi. unfold tg. rewrite t_len_setlen_other by lia. apply Hlen15. lia. }
  assert (H0 : t_len tg 0 = t_len t 0)
    by (unfold tg; apply t_len_setlen_other; lia).
  destruct (Z.eqb (t_len t 0) 0) eqn:E0;
    (eapply scan_go_budget; try eassumption; try lia).
Qed.

Theorem scan_tree_counts_gen : forall t maxc bl s m M,
  0 <= maxc <= 285 ->
  (forall i, 0 <= i <= maxc -> 0 <= t_len t i <= 15) ->
  Budget bl m -> 0 <= m -> m + (maxc + 1) <= M -> 3 * M <= 65535 ->
  t_freq (snd (scan_tree t maxc bl)) s
  = t_freq bl s
    + hid_zcount s (items_syms (send_tree_items (fst (scan_tree t maxc bl)) maxc)).
Proof.
  intros t maxc bl s m M Hmc Hlen15 Hbud Hm0 HmM HM.
  unfold scan_tree. cbn [fst snd].
  set (tg := t_setlen t (maxc + 1) 65535).
  assert (Hg : t_len tg (maxc + 1) = 65535)
    by (unfold tg; rewrite t_len_setlen_same; reflexivity).
  assert (H15 : forall i, 0 <= i <= maxc -> 0 <= t_len tg i <= 15).
  { intros i Hi. unfold tg. rewrite t_len_setlen_other by lia. apply Hlen15. lia. }
  assert (H0 : t_len tg 0 = t_len t 0)
    by (unfold tg; apply t_len_setlen_other; lia).
  assert (Hfuel : (Z.to_nat L_CODES + 3 = 289)%nat) by reflexivity.
  unfold send_tree_items. rewrite H0.
  (* [m] and [M] must be given: neither occurs in the conclusion. *)
  destruct (Z.eqb (t_len t 0) 0) eqn:E0;
    (eapply (scan_go_counts_gen _ _ _ _ _ _ _ _ _ _ _ m M);
       try eassumption; try lia).
Qed.

(** ** SEAM A, DISCHARGED

    Every symbol either stream uses is positive in the TWICE-scanned table.  The
    two halves are the two reasons a symbol can be positive there, and they need
    different facts: the distance tree's symbols are counted BY the second scan,
    while the literal tree's symbols were counted by the first and must SURVIVE
    the second.  Both come out of the same equation — which is the argument for
    generalising the count rather than proving a bare monotonicity lemma. *)
Theorem scan_keeps_pos : ScanKeepsPos.
Proof.
  unfold ScanKeepsPos.
  intros tL maxcL tD maxcD bl p1 p2 s HmcL HmcD H15L H15D Hfresh Hp1 Hp2 Hin.
  (* SUBSTITUTE the two scan results away rather than rewriting with [Hp1]/[Hp2].
     THIS IS NOT COSMETIC.  With [p1] left as a variable, [assumption] and
     [exact] have to decide whether [send_tree_items (fst p1) maxcL] and
     [send_tree_items (fst (scan_tree tL maxcL bl)) maxcL] are convertible, and
     the only way to try is to unfold [send_tree_items] -> [send_items] at its
     LITERAL fuel [Z.to_nat L_CODES + 3 = 289] over a symbolic tree.  That is the
     fatal cell of the fuel-conversion cost model: a match-bodied fuelled
     definition whose scrutinee can step.  The first version of this proof was
     killed at 700 MB and 99.9% CPU with flat RSS -- expensive conversion, not a
     runaway -- and every step ran in about a second once the terms were
     syntactically identical. *)
  subst p2. subst p1.
  assert (Hb0 : Budget bl 0) by (intro s'; rewrite Hfresh; lia).
  (* after the first scan the allowance is 286; the u16 wrap is at 65536 *)
  assert (Hb1 : Budget (snd (scan_tree tL maxcL bl)) 286).
  { apply (scan_tree_budget tL maxcL bl 0 286); try assumption; lia. }
  (* the second scan's count equation, at that base -- the whole point of the
     generalisation *)
  assert (Heq : t_freq (snd (scan_tree tD maxcD (snd (scan_tree tL maxcL bl)))) s
                = t_freq (snd (scan_tree tL maxcL bl)) s
                  + hid_zcount s (items_syms (send_tree_items
                      (fst (scan_tree tD maxcD (snd (scan_tree tL maxcL bl)))) maxcD))).
  { apply (scan_tree_counts_gen tD maxcD (snd (scan_tree tL maxcL bl)) s 286 572);
      try assumption; lia. }
  assert (Hnn1 : 0 <= t_freq (snd (scan_tree tL maxcL bl)) s)
    by (destruct (Hb1 s); lia).
  destruct Hin as [Hin|Hin].
  - (* counted by the FIRST scan: positive there, and the second scan can only
       ADD, so the u16 never wraps it back to zero *)
    assert (Hpos1 : 0 < t_freq (snd (scan_tree tL maxcL bl)) s).
    { apply (scan_tree_positive tL maxcL bl s); try assumption. }
    assert (Hz : 0 <= hid_zcount s (items_syms (send_tree_items
                    (fst (scan_tree tD maxcD (snd (scan_tree tL maxcL bl)))) maxcD)))
      by (unfold hid_zcount; lia).
    lia.
  - (* counted by the SECOND scan: at least one use, on top of a nonneg base *)
    assert (Hc : (0 < count_occ Z.eq_dec
                    (items_syms (send_tree_items
                       (fst (scan_tree tD maxcD (snd (scan_tree tL maxcL bl)))) maxcD)) s)%nat)
      by (apply (count_occ_In Z.eq_dec); exact Hin).
    assert (Hpos2 : 0 < hid_zcount s (items_syms (send_tree_items
                       (fst (scan_tree tD maxcD (snd (scan_tree tL maxcL bl)))) maxcD)))
      by (unfold hid_zcount; lia).
    lia.
Qed.

(** ** THE COMPOSITION, with no hypothesis left that is mine

    [cover_both_streams] with [ScanKeepsPos] discharged.  What remains are facts
    about the heap ([bt_init]/[bt_force2]'s results), the representation
    ([LensOf], the length of [cl]), and the two trees' length bounds — none of
    them mine, and SEAM D (that the caller sends at the [maxc] it scanned at)
    still sits with the dynamic seam. *)
Corollary cover_both_streams_final :
  forall (st st2 : TSt) (cl : list nat) tL maxcL tD maxcD p1 p2
         t0 hp0 dep0 hlen0 maxc0 t1 hp1 dep1 hlen1 maxc1 ol1 sl1,
  0 <= maxcL <= 285 -> 0 <= maxcD <= 285 ->
  (forall i, 0 <= i <= maxcL -> 0 <= t_len tL i <= 15) ->
  (forall i, 0 <= i <= maxcD -> 0 <= t_len tD i <= 15) ->
  (forall s', t_freq (ts_trees st TK_BL) s' = 0) ->
  p1 = scan_tree tL maxcL (ts_trees st TK_BL) ->
  p2 = scan_tree tD maxcD (snd p1) ->
  ts_trees st2 TK_BL = snd p2 ->
  DlNn (snd p2) ->
  bt_init (Z.to_nat L_CODES + 2) 0 (sd_elems TK_BL) (ts_trees st2 TK_BL)
          (ts_heap st2) (ts_depth st2) 0 (-1) = (t0, hp0, dep0, hlen0, maxc0) ->
  bt_force2 3%nat (sd_stree TK_BL) t0 hp0 dep0 hlen0 maxc0
            (ts_optlen st2) (ts_statlen st2)
    = (t1, hp1, dep1, hlen1, maxc1, ol1, sl1) ->
  LensOf (ts_trees (build_tree TK_BL st2) TK_BL) cl ->
  (19 <= length cl)%nat ->
  (exists bits, cl_bits cl (send_tree_items (fst p1) maxcL) = Some bits)
  /\ (exists bits, cl_bits cl (send_tree_items (fst p2) maxcD) = Some bits).
Proof.
  intros. edestruct (cover_both_streams st st2 cl tL maxcL tD maxcD p1 p2)
    as [Hc1 Hc2]; try eassumption; try exact scan_keeps_pos.
  split; apply cl_bits_total; assumption.
Qed.

Print Assumptions scan_go_budget.
Print Assumptions scan_go_counts_gen.
Print Assumptions scan_tree_counts_gen.
Print Assumptions scan_keeps_pos.
Print Assumptions cover_both_streams_final.
