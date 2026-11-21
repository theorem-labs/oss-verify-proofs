(** * ZReproG6M — the RANGE-RESTRICTED scan budget (BL slots [0,19) only).

    OWNER: g6-bound (zlib z-repro campaign, 2026-08-20).

    WHY THIS FILE EXISTS (crc-capstone's statement-time falsifier, register
    R39): [build_tree TK_BL] writes internal-node frequency sums into the
    SAME array at indices >= BL_CODES = 19, and [init_block] clears only
    [0, BL_CODES).  So at every flush after the first, the BL tree carries
    nonzero garbage at indices >= 19, and a TOTAL freshness hypothesis
    ([forall v, t_freq bl v = 0]) is UNSATISFIABLE there.  The restorable
    hypothesis is freshness on [0, 19) — but ScanBase's count law and
    budget lemmas carry [ScanCount.Budget], a TOTAL invariant, which the
    garbage falsifies for every index [m].

    THE REPAIR: [scan_go] only ever reads or bumps the accumulator at slots
    [curlen ∈ [0,15]] and the REP codes 16/17/18 — all < 19 — so the budget
    only needs to constrain those slots.  [RBudget] is [Budget] restricted
    to [0, 19); the lemmas below are ScanBase/ScanCount's proofs with that
    one change (derived from the pinned text by explicit substitution, arm
    by arm, exactly as ScanBase itself was derived from ScanCount).  The
    count-law CONCLUSION stays total-in-[s]: at a bumped slot the no-wrap
    fact comes from [RBudget] (bump slots are < 19); at any other slot it
    is a frame fact needing no budget at all.

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff Trees DeflateSpec.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  HuffGenCodes ClStream SendItems SendGo SendGoLens SendGoWf HuffCover
  ScanCount BuildChain BtTerm CoverChain ScanBase.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** [ScanCount.Budget] restricted to the slots [scan_go] can touch. *)
Definition RBudget (bl : Tree) (n : Z) : Prop :=
  forall s, 0 <= s < 19 -> 0 <= t_freq bl s /\ t_freq bl s <= 3 * n.

Lemma Budget_to_RBudget : forall bl n, Budget bl n -> RBudget bl n.
Proof. intros bl n Hb s _. exact (Hb s). Qed.

Lemma RBudget_mono : forall bl n m, RBudget bl n -> n <= m -> RBudget bl m.
Proof.
  intros bl n m Hb Hnm s Hs. destruct (Hb s Hs) as [Ha Hbb]. lia.
Qed.

(** ** The per-trip budget steps (ScanCount's, with the slot range added) *)

Lemma rbudget_short : forall bl i cnt n,
  RBudget bl n -> 0 <= i < 19 -> 0 <= n -> 0 <= cnt <= 3 ->
  3 * (n + 1) <= 65535 ->
  RBudget (t_setfreq bl i (t_freq bl i + cnt)) (n + 1).
Proof.
  intros bl i cnt n Hb Hi Hn Hc Hceil s Hs. destruct (Hb i Hi) as [Hi0 Hi1].
  destruct (Z.eq_dec s i) as [->|Hne].
  - rewrite t_freq_setfreq_same. unfold u16.
    rewrite Z.mod_small by lia. lia.
  - rewrite t_freq_setfreq_other by lia. destruct (Hb s Hs) as [Ha Hbb]. lia.
Qed.

Lemma rbudget_one : forall bl i n,
  RBudget bl n -> 0 <= i < 19 -> 0 <= n -> 3 * (n + 1) <= 65535 ->
  RBudget (t_setfreq bl i (t_freq bl i + 1)) (n + 1).
Proof.
  intros bl i n Hb Hi Hn Hceil. apply (rbudget_short bl i 1 n Hb Hi Hn); lia.
Qed.

Lemma rbudget_two : forall bl i j n,
  i <> j -> RBudget bl n -> 0 <= i < 19 -> 0 <= j < 19 -> 0 <= n ->
  3 * (n + 1) <= 65535 ->
  RBudget (t_setfreq (t_setfreq bl i (t_freq bl i + 1)) j
            (t_freq (t_setfreq bl i (t_freq bl i + 1)) j + 1)) (n + 1).
Proof.
  intros bl i j n Hij Hb Hi Hj Hn Hceil.
  set (b1 := t_setfreq bl i (t_freq bl i + 1)).
  assert (Hb1j : t_freq b1 j = t_freq bl j)
    by (unfold b1; apply t_freq_setfreq_other; lia).
  intros s Hs.
  destruct (Hb i Hi) as [Hi0 Hi1]. destruct (Hb j Hj) as [Hj0 Hj1].
  destruct (Hb s Hs) as [Hs0 Hs1].
  destruct (Z.eq_dec s j) as [->|Hsj].
  - rewrite t_freq_setfreq_same, Hb1j. unfold u16.
    rewrite Z.mod_small by lia. lia.
  - rewrite t_freq_setfreq_other by lia. unfold b1.
    destruct (Z.eq_dec s i) as [->|Hsi].
    + rewrite t_freq_setfreq_same. unfold u16. rewrite Z.mod_small by lia. lia.
    + rewrite t_freq_setfreq_other by lia. lia.
Qed.

(** ** Budget preservation (ScanBase's [scan_go_budget], range-restricted) *)

Lemma scan_go_budget_r : forall f t maxc n prevlen nextlen count maxcnt mincnt bl m M,
  (forall i, 0 <= i <= maxc -> 0 <= t_len t i <= 15) ->
  n <= maxc + 1 -> 0 <= maxc <= 285 ->
  nextlen = t_len t n ->
  0 <= n -> 0 <= count -> mincnt <= 4 ->
  RBudget bl m -> 0 <= m ->
  m + (maxc + 1 - n) <= M -> 3 * M <= 65535 ->
  RBudget (scan_go f t maxc n prevlen nextlen count maxcnt mincnt bl) M.
Proof.
  induction f as [|f IH];
    intros t maxc n prevlen nextlen count maxcnt mincnt bl m M
           Hlen15 Hn Hmc Hnl Hn0 Hc Hmn Hbud Hm0 HmM HM.
  - cbn [scan_go]. apply (RBudget_mono bl m); [exact Hbud | lia].
  - cbn [scan_go].
    destruct (Z.ltb maxc n) eqn:Eexit.
    + apply (RBudget_mono bl m); [exact Hbud | lia].
    + apply Z.ltb_ge in Eexit.
      assert (H15 : 0 <= t_len t n <= 15) by (apply Hlen15; lia).
      assert (Hceil : 3 * (m + 1) <= 65535) by lia.
      destruct ((Z.ltb (count + 1) maxcnt) && (Z.eqb nextlen (t_len t (n + 1))))
               eqn:Eacc.
      * apply (IH t maxc (n + 1) prevlen (t_len t (n + 1)) (count + 1) maxcnt
                 mincnt bl m M); try assumption; try lia.
      * destruct (Z.ltb (count + 1) mincnt) eqn:Emin.
        -- apply Z.ltb_lt in Emin.
           apply (IH t maxc (n + 1) nextlen (t_len t (n + 1)) 0
                    (if Z.eqb (t_len t (n + 1)) 0 then 138
                     else if Z.eqb nextlen (t_len t (n + 1)) then 6 else 7)
                    (if Z.eqb (t_len t (n + 1)) 0 then 3
                     else if Z.eqb nextlen (t_len t (n + 1)) then 3 else 4)
                    _ (m + 1) M);
             try assumption; try lia; try if_bound.
           apply rbudget_short; try assumption; lia.
        -- destruct (negb (Z.eqb nextlen 0)) eqn:Ez.
           ++ apply negb_true_iff, Z.eqb_neq in Ez.
              destruct (negb (Z.eqb nextlen prevlen)) eqn:Ep.
              ** apply (IH t maxc (n + 1) nextlen (t_len t (n + 1)) 0
                          (if Z.eqb (t_len t (n + 1)) 0 then 138
                           else if Z.eqb nextlen (t_len t (n + 1)) then 6 else 7)
                          (if Z.eqb (t_len t (n + 1)) 0 then 3
                           else if Z.eqb nextlen (t_len t (n + 1)) then 3 else 4)
                          _ (m + 1) M);
                   try assumption; try lia; try if_bound.
                 apply rbudget_two; try assumption;
                   try unfold REP_3_6; lia.
              ** apply (IH t maxc (n + 1) nextlen (t_len t (n + 1)) 0
                          (if Z.eqb (t_len t (n + 1)) 0 then 138
                           else if Z.eqb nextlen (t_len t (n + 1)) then 6 else 7)
                          (if Z.eqb (t_len t (n + 1)) 0 then 3
                           else if Z.eqb nextlen (t_len t (n + 1)) then 3 else 4)
                          _ (m + 1) M);
                   try assumption; try lia; try if_bound.
                 apply rbudget_one; try assumption;
                   try unfold REP_3_6; lia.
           ++ apply negb_false_iff, Z.eqb_eq in Ez.
              destruct (Z.leb (count + 1) 10) eqn:Eten.
              ** apply (IH t maxc (n + 1) nextlen (t_len t (n + 1)) 0
                          (if Z.eqb (t_len t (n + 1)) 0 then 138
                           else if Z.eqb nextlen (t_len t (n + 1)) then 6 else 7)
                          (if Z.eqb (t_len t (n + 1)) 0 then 3
                           else if Z.eqb nextlen (t_len t (n + 1)) then 3 else 4)
                          _ (m + 1) M);
                   try assumption; try lia; try if_bound.
                 apply rbudget_one; try assumption;
                   try unfold REPZ_3_10; lia.
              ** apply (IH t maxc (n + 1) nextlen (t_len t (n + 1)) 0
                          (if Z.eqb (t_len t (n + 1)) 0 then 138
                           else if Z.eqb nextlen (t_len t (n + 1)) then 6 else 7)
                          (if Z.eqb (t_len t (n + 1)) 0 then 3
                           else if Z.eqb nextlen (t_len t (n + 1)) then 3 else 4)
                          _ (m + 1) M);
                   try assumption; try lia; try if_bound.
                 apply rbudget_one; try assumption;
                   try unfold REPZ_11_138; lia.
Qed.

(** ** The counting theorem (ScanBase's [scan_go_counts_gen], range-restricted
    premise, TOTAL conclusion) *)

Lemma scan_go_counts_r : forall f t maxc n prevlen nextlen count maxcnt mincnt bl s m M,
  t_len t (maxc + 1) = 65535 ->
  (forall i, 0 <= i <= maxc -> 0 <= t_len t i <= 15) ->
  0 <= count -> 0 <= n - count -> n <= maxc + 1 -> 0 <= maxc <= 285 ->
  nextlen = t_len t n ->
  (maxc < n -> count = 0) ->
  (Z.to_nat (maxc + 1 - n) <= f)%nat ->
  mincnt <= 4 ->
  RBudget bl m -> 0 <= m ->
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
      * apply andb_prop in Eacc as [Emax Eeq]. apply Z.eqb_eq in Eeq.
        assert (Hlt : n < maxc).
        { destruct (Z.eq_dec n maxc) as [->|Hne]; [|lia]. rewrite Hguard in Eeq. lia. }
        apply (IH t maxc (n + 1) prevlen (t_len t (n + 1)) (count + 1) maxcnt
                 mincnt bl s m M); try assumption; try lia; try if_bound.
      * assert (Hcur : Z.of_nat (Z.to_nat nextlen) = nextlen) by lia.
        destruct (Z.ltb (count + 1) mincnt) eqn:Emin.
        -- apply Z.ltb_lt in Emin.
           rewrite items_syms_app, items_syms_repeat_lit, Hcur, hid_zcount_app.
           destruct (Hbud nextlen ltac:(lia)) as [Hf0 Hf1].
           rewrite (IH t maxc (n + 1) nextlen (t_len t (n + 1)) 0
                      (if Z.eqb (t_len t (n + 1)) 0 then 138
                       else if Z.eqb nextlen (t_len t (n + 1)) then 6 else 7)
                      (if Z.eqb (t_len t (n + 1)) 0 then 3
                       else if Z.eqb nextlen (t_len t (n + 1)) then 3 else 4)
                      _ _ (m + 1) M);
             try assumption; try lia; try if_bound.
           ++ rewrite (step_short bl nextlen (count + 1) s) by lia. lia.
           ++ apply rbudget_short; try assumption; lia.
        -- destruct (negb (Z.eqb nextlen 0)) eqn:Ez.
           ++ apply negb_true_iff, Z.eqb_neq in Ez.
              destruct (negb (Z.eqb nextlen prevlen)) eqn:Ep.
              ** rewrite items_syms_app, items_syms_lit_rep, Hcur, hid_zcount_app.
                 destruct (Hbud nextlen ltac:(lia)) as [Hf0 Hf1].
                 destruct (Hbud REP_3_6 ltac:(unfold REP_3_6; lia)) as [Hg0 Hg1].
                 rewrite (IH t maxc (n + 1) nextlen (t_len t (n + 1)) 0
                            (if Z.eqb (t_len t (n + 1)) 0 then 138
                             else if Z.eqb nextlen (t_len t (n + 1)) then 6 else 7)
                            (if Z.eqb (t_len t (n + 1)) 0 then 3
                             else if Z.eqb nextlen (t_len t (n + 1)) then 3 else 4)
                            _ _ (m + 1) M);
                   try assumption; try lia; try if_bound.
                 --- assert (Hne : nextlen <> REP_3_6) by (unfold REP_3_6; lia).
                     assert (Hfb : t_freq bl nextlen + 1 <= 65535) by lia.
                     assert (Hgb : t_freq bl REP_3_6 + 1 <= 65535) by lia.
                     rewrite (step_two bl nextlen REP_3_6 s Hne Hf0 Hfb Hg0 Hgb).
                     lia.
                 --- apply rbudget_two; try assumption;
                       try unfold REP_3_6; lia.
              ** rewrite items_syms_app, items_syms_rep, hid_zcount_app.
                 destruct (Hbud REP_3_6 ltac:(unfold REP_3_6; lia)) as [Hg0 Hg1].
                 rewrite (IH t maxc (n + 1) nextlen (t_len t (n + 1)) 0
                            (if Z.eqb (t_len t (n + 1)) 0 then 138
                             else if Z.eqb nextlen (t_len t (n + 1)) then 6 else 7)
                            (if Z.eqb (t_len t (n + 1)) 0 then 3
                             else if Z.eqb nextlen (t_len t (n + 1)) then 3 else 4)
                            _ _ (m + 1) M);
                   try assumption; try lia; try if_bound.
                 --- rewrite (step_one bl REP_3_6 s) by lia. lia.
                 --- apply rbudget_one; try assumption;
                       try unfold REP_3_6; lia.
           ++ apply negb_false_iff, Z.eqb_eq in Ez.
              destruct (Z.leb (count + 1) 10) eqn:Eten.
              ** rewrite items_syms_app, items_syms_z3, hid_zcount_app.
                 destruct (Hbud REPZ_3_10 ltac:(unfold REPZ_3_10; lia)) as [Hg0 Hg1].
                 rewrite (IH t maxc (n + 1) nextlen (t_len t (n + 1)) 0
                            (if Z.eqb (t_len t (n + 1)) 0 then 138
                             else if Z.eqb nextlen (t_len t (n + 1)) then 6 else 7)
                            (if Z.eqb (t_len t (n + 1)) 0 then 3
                             else if Z.eqb nextlen (t_len t (n + 1)) then 3 else 4)
                            _ _ (m + 1) M);
                   try assumption; try lia; try if_bound.
                 --- rewrite (step_one bl REPZ_3_10 s) by lia. lia.
                 --- apply rbudget_one; try assumption;
                       try unfold REPZ_3_10; lia.
              ** rewrite items_syms_app, items_syms_z11, hid_zcount_app.
                 destruct (Hbud REPZ_11_138 ltac:(unfold REPZ_11_138; lia)) as [Hg0 Hg1].
                 rewrite (IH t maxc (n + 1) nextlen (t_len t (n + 1)) 0
                            (if Z.eqb (t_len t (n + 1)) 0 then 138
                             else if Z.eqb nextlen (t_len t (n + 1)) then 6 else 7)
                            (if Z.eqb (t_len t (n + 1)) 0 then 3
                             else if Z.eqb nextlen (t_len t (n + 1)) then 3 else 4)
                            _ _ (m + 1) M);
                   try assumption; try lia; try if_bound.
                 --- rewrite (step_one bl REPZ_11_138 s) by lia. lia.
                 --- apply rbudget_one; try assumption;
                       try unfold REPZ_11_138; lia.
Qed.

(** ** Entry points, on the guarded tree [scan_tree] builds itself *)

Lemma scan_tree_budget_r : forall t maxc bl m M,
  0 <= maxc <= 285 ->
  (forall i, 0 <= i <= maxc -> 0 <= t_len t i <= 15) ->
  RBudget bl m -> 0 <= m -> m + (maxc + 1) <= M -> 3 * M <= 65535 ->
  RBudget (snd (scan_tree t maxc bl)) M.
Proof.
  intros t maxc bl m M Hmc Hlen15 Hbud Hm0 HmM HM.
  unfold scan_tree. cbn [snd].
  set (tg := t_setlen t (maxc + 1) 65535).
  assert (H15 : forall i, 0 <= i <= maxc -> 0 <= t_len tg i <= 15).
  { intros i Hi. unfold tg. rewrite t_len_setlen_other by lia. apply Hlen15. lia. }
  assert (H0 : t_len tg 0 = t_len t 0)
    by (unfold tg; apply t_len_setlen_other; lia).
  destruct (Z.eqb (t_len t 0) 0) eqn:E0;
    (eapply scan_go_budget_r; try eassumption; try lia).
Qed.

Theorem scan_tree_counts_r : forall t maxc bl s m M,
  0 <= maxc <= 285 ->
  (forall i, 0 <= i <= maxc -> 0 <= t_len t i <= 15) ->
  RBudget bl m -> 0 <= m -> m + (maxc + 1) <= M -> 3 * M <= 65535 ->
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
  destruct (Z.eqb (t_len t 0) 0) eqn:E0;
    (eapply (scan_go_counts_r _ _ _ _ _ _ _ _ _ _ _ m M);
       try eassumption; try lia).
Qed.

Set Printing All.
Set Printing Fully Qualified.
Set Printing Depth 10000000000.
Set Printing Width 2000.
Print Assumptions scan_tree_counts_r.
Print Assumptions scan_tree_budget_r.
Unset Printing All.
