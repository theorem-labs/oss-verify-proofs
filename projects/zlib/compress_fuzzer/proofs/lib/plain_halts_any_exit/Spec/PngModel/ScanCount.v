(** * ScanCount — (S): [scan_tree] counts exactly what [send_tree] will emit.

    OWNER: huffman-id.  TL ruled this next (§TL-ACK-COVER); it is the obligation
    HuffCover.v named as (S) and it completes that interface.

    WHAT IT SAYS.  [scan_tree] exists so [build_bl_tree] knows how often each
    code-length symbol will be used.  Its correctness property is therefore not
    about bits at all: it is that its frequency table IS the symbol multiset of
    the stream [send_tree] goes on to emit.  That is what this file proves, as an
    exact equation in both directions rather than a positivity bound, because
    HuffCover's (B) side wants "positive frequency" and a future optimality
    argument would want the counts.

    WHY IT IS THE SAME INDUCTION AS B1.  [Trees.v]'s own header says [scan_go] and
    [send_go] "share their control flow exactly; only the action differs".  So the
    proof walks the two in lockstep, and every arm's frequency increment has to
    match that arm's item symbols:

      count' < mincnt      scan: freq[curlen] += count'
                           send: repeat (CLit curlen) count'   -> count' copies
      curlen <> 0, <> prev scan: freq[curlen] += 1; freq[16] += 1
                           send: [CLit curlen; CRep curlen (count'-1)] -> [curlen;16]
      curlen <> 0,  = prev scan: freq[16] += 1
                           send: [CRep curlen count']          -> [16]
      curlen = 0, k <= 10  scan: freq[17] += 1     send: [CZ3 k]  -> [17]
      curlen = 0, k >  10  scan: freq[18] += 1     send: [CZ11 k] -> [18]

    THE TWO HYPOTHESES THAT ARE NOT DECORATION.
    (1) [t_setfreq] applies [u16] ([Trees.v:227]), so the equation is false if a
        count wraps.  A no-wrap budget is carried: each trip adds at most 3 to any
        single slot (the short-run arm is bounded by [mincnt <= 4], the others add
        1 twice), and there are at most 286 trips, so 858 is the true ceiling —
        far under 65536, but it has to be CARRIED rather than waved at.
    (2) Real code lengths are at most 15, which is what makes [curlen] and the
        repeat symbols 16/17/18 DIFFERENT SLOTS.  Without it the [curlen <> prev]
        arm's two increments could collide and the multiset would be wrong.  This
        is the same kind of index-disjointness the sentinel findings turned on.

    NOTE ON A SHARED SLOT, since it surprised me: [t_freq] and [t_code] are
    ALIASES for [tr_fc] ([Trees.v:219-221]) — zlib's [ct_data] union. So the
    frequencies this file counts and the codes [gen_codes] writes occupy the SAME
    physical array. That is sound in zlib's order (scan, then build, then gen) but
    it means a statement mentioning both at once needs care about which phase it
    is in. Nothing here mentions [t_code]. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff Trees DeflateSpec.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  HuffGenCodes ClStream SendItems SendGo SendGoLens SendGoWf HuffCover.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** ** Counting vocabulary *)

Definition hid_zcount (s : Z) (l : list Z) : Z := Z.of_nat (count_occ Z.eq_dec l s).

Lemma hid_zcount_app : forall s l1 l2, hid_zcount s (l1 ++ l2) = hid_zcount s l1 + hid_zcount s l2.
Proof.
  intros s l1 l2. unfold hid_zcount. rewrite count_occ_app, Nat2Z.inj_add. reflexivity.
Qed.

Lemma hid_zcount_nil : forall s, hid_zcount s [] = 0.
Proof. reflexivity. Qed.

Lemma hid_zcount_one_same : forall s, hid_zcount s [s] = 1.
Proof.
  intro s. unfold hid_zcount. cbn [count_occ].
  destruct (Z.eq_dec s s) as [_|Hne]; [reflexivity|exfalso; apply Hne; reflexivity].
Qed.

Lemma hid_zcount_one_diff : forall s a, a <> s -> hid_zcount s [a] = 0.
Proof.
  intros s a Hne. unfold hid_zcount. cbn [count_occ].
  destruct (Z.eq_dec a s) as [Heq|_]; [exfalso; apply Hne; exact Heq|reflexivity].
Qed.

Lemma hid_zcount_repeat_same : forall s k, hid_zcount s (repeat s k) = Z.of_nat k.
Proof.
  intros s k. induction k as [|k IH]; [reflexivity|].
  cbn [repeat]. unfold hid_zcount in *. cbn [count_occ].
  destruct (Z.eq_dec s s) as [_|Hne]; [|exfalso; apply Hne; reflexivity].
  rewrite Nat2Z.inj_succ. lia.
Qed.

Lemma hid_zcount_repeat_diff : forall s a k, a <> s -> hid_zcount s (repeat a k) = 0.
Proof.
  intros s a k Hne. induction k as [|k IH]; [reflexivity|].
  cbn [repeat]. unfold hid_zcount in *. cbn [count_occ].
  destruct (Z.eq_dec a s) as [Heq|_]; [exfalso; apply Hne; exact Heq|exact IH].
Qed.

Lemma items_syms_app : forall xs ys,
  items_syms (xs ++ ys) = items_syms xs ++ items_syms ys.
Proof. intros xs ys. unfold items_syms. apply flat_map_app. Qed.

Lemma items_syms_repeat_lit : forall c k,
  items_syms (repeat (CLit c) k) = repeat (Z.of_nat c) k.
Proof.
  intros c k. induction k as [|k IH]; [reflexivity|].
  cbn [repeat items_syms flat_map item_syms app]. f_equal. exact IH.
Qed.

(** The four arm shapes, kept as lemmas rather than reduced with [cbn]: a
    [cbn [app]] flattens the very [++] that [hid_zcount_app] has to match, and the
    failure then reads as if [hid_zcount_app] were wrong. *)
Lemma items_syms_lit_rep : forall c p k,
  items_syms [CLit c; CRep p k] = [Z.of_nat c; REP_3_6].
Proof. reflexivity. Qed.

Lemma items_syms_rep : forall p k, items_syms [CRep p k] = [REP_3_6].
Proof. reflexivity. Qed.

Lemma items_syms_z3 : forall k, items_syms [CZ3 k] = [REPZ_3_10].
Proof. reflexivity. Qed.

Lemma items_syms_z11 : forall k, items_syms [CZ11 k] = [REPZ_11_138].
Proof. reflexivity. Qed.

Lemma hid_zcount_two : forall s a b, hid_zcount s [a; b] = hid_zcount s [a] + hid_zcount s [b].
Proof. intros s a b. change [a; b] with ([a] ++ [b]). apply hid_zcount_app. Qed.

(** ** Reading a frequency back out of a [t_setfreq] *)

Lemma t_freq_setfreq_same : forall t i v, t_freq (t_setfreq t i v) i = u16 v.
Proof. intros t i v. unfold t_freq, t_setfreq. cbn [tr_fc]. apply zset_same. Qed.

Lemma t_freq_setfreq_other : forall t i v j,
  j <> i -> t_freq (t_setfreq t i v) j = t_freq t j.
Proof.
  intros t i v j H. unfold t_freq, t_setfreq. cbn [tr_fc]. apply zset_other. exact H.
Qed.

(** ** The per-trip steps, as standalone lemmas

    Factored out of the induction deliberately.  Written inline they nest five
    deep inside four arms, and every one of tonight's bullet-misalignment
    failures came from exactly that shape.  Each lemma below carries its own
    no-wrap side condition, so the induction only has to supply arithmetic. *)

Lemma step_short : forall bl i cnt s,
  0 <= t_freq bl i -> t_freq bl i + cnt <= 65535 -> 0 <= cnt ->
  t_freq (t_setfreq bl i (t_freq bl i + cnt)) s
  = t_freq bl s + hid_zcount s (repeat i (Z.to_nat cnt)).
Proof.
  intros bl i cnt s H0 H1 H2.
  destruct (Z.eq_dec s i) as [->|Hs].
  - rewrite t_freq_setfreq_same, hid_zcount_repeat_same.
    unfold u16. rewrite Z.mod_small by lia. lia.
  - rewrite t_freq_setfreq_other by lia.
    rewrite (hid_zcount_repeat_diff s i) by lia. lia.
Qed.

Lemma step_one : forall bl i s,
  0 <= t_freq bl i -> t_freq bl i + 1 <= 65535 ->
  t_freq (t_setfreq bl i (t_freq bl i + 1)) s = t_freq bl s + hid_zcount s [i].
Proof.
  intros bl i s H0 H1.
  destruct (Z.eq_dec s i) as [->|Hs].
  - rewrite t_freq_setfreq_same, hid_zcount_one_same.
    unfold u16. rewrite Z.mod_small by lia. lia.
  - rewrite t_freq_setfreq_other by lia.
    rewrite (hid_zcount_one_diff s i) by lia. lia.
Qed.

(** The two-slot arm.  [i <> j] is where "code lengths are at most 15, the repeat
    symbols are 16/17/18" earns its place: without it the two increments could
    land on one slot and the multiset would be wrong. *)
Lemma step_two : forall bl i j s,
  i <> j ->
  0 <= t_freq bl i -> t_freq bl i + 1 <= 65535 ->
  0 <= t_freq bl j -> t_freq bl j + 1 <= 65535 ->
  t_freq (t_setfreq (t_setfreq bl i (t_freq bl i + 1)) j
            (t_freq (t_setfreq bl i (t_freq bl i + 1)) j + 1)) s
  = t_freq bl s + hid_zcount s [i; j].
Proof.
  intros bl i j s Hij H0i H1i H0j H1j.
  (* name the intermediate tree: rewriting inside the VALUE argument of the outer
     t_setfreq does not find its pattern, and the failure reads as if
     t_freq_setfreq_other were wrong. *)
  set (b1 := t_setfreq bl i (t_freq bl i + 1)).
  assert (Hj1 : t_freq b1 j = t_freq bl j)
    by (unfold b1; apply t_freq_setfreq_other; lia).
  rewrite Hj1, hid_zcount_two.
  destruct (Z.eq_dec s j) as [->|Hsj].
  - rewrite t_freq_setfreq_same, hid_zcount_one_same.
    rewrite (hid_zcount_one_diff j i) by lia.
    unfold u16. rewrite Z.mod_small by lia. lia.
  - rewrite t_freq_setfreq_other by lia.
    rewrite (hid_zcount_one_diff s j) by lia.
    unfold b1.
    destruct (Z.eq_dec s i) as [->|Hsi].
    + rewrite t_freq_setfreq_same, hid_zcount_one_same.
      unfold u16. rewrite Z.mod_small by lia. lia.
    + rewrite t_freq_setfreq_other by lia.
      rewrite (hid_zcount_one_diff s i) by lia. lia.
Qed.

(** ** The budget, in monotone form

    [t_freq bl s <= 3 * n] rather than a shrinking allowance: each trip adds at
    most 3 to any one slot and advances [n] by one, so the bound grows exactly as
    fast as the counts can.  With [n <= 286] it gives [<= 858], far under the
    [u16] wrap at 65536 — but it has to be carried, because [t_setfreq] truncates.

    THE CEILING IS REAL, NOT DEFENSIVE: the short-run arm can add 3 at once
    (bounded by [mincnt <= 4]), and the two-slot arm adds 1 twice. *)
Definition Budget (bl : Tree) (n : Z) : Prop :=
  forall s, 0 <= t_freq bl s /\ t_freq bl s <= 3 * n.

(* [3 * (n + 1) <= 65535] is the no-wrap ceiling.  [Budget] alone does NOT bound
   [n], so without it the sum can exceed the u16 and the truncation bites; the
   caller supplies it from [n <= maxc + 1 <= 286]. *)
Lemma Budget_mono : forall bl n m, Budget bl n -> n <= m -> Budget bl m.
Proof. intros bl n m Hb Hnm s. destruct (Hb s) as [Ha Hbb]. lia. Qed.

Lemma budget_short : forall bl i cnt n,
  Budget bl n -> 0 <= n -> 0 <= cnt <= 3 -> 3 * (n + 1) <= 65535 ->
  Budget (t_setfreq bl i (t_freq bl i + cnt)) (n + 1).
Proof.
  intros bl i cnt n Hb Hn Hc Hceil s. destruct (Hb i) as [Hi0 Hi1].
  destruct (Z.eq_dec s i) as [->|Hs].
  - rewrite t_freq_setfreq_same. unfold u16.
    rewrite Z.mod_small by lia. lia.
  - rewrite t_freq_setfreq_other by lia. destruct (Hb s) as [Ha Hbb]. lia.
Qed.

Lemma budget_one : forall bl i n,
  Budget bl n -> 0 <= n -> 3 * (n + 1) <= 65535 ->
  Budget (t_setfreq bl i (t_freq bl i + 1)) (n + 1).
Proof.
  intros bl i n Hb Hn Hceil. apply (budget_short bl i 1 n Hb Hn); lia.
Qed.

(** The two-slot arm's budget concludes at [n + 1], NOT [n + 2], and that is the
    point: [i <> j] means each SLOT gains only one even though two slots move.  A
    proof that chained budget_one twice would conclude [n + 2], which is WEAKER
    (Budget at a larger index bounds less) and would not match the recursion — so
    the looser route is not merely inelegant, it does not compose. *)
Lemma budget_two : forall bl i j n,
  i <> j -> Budget bl n -> 0 <= n -> 3 * (n + 1) <= 65535 ->
  Budget (t_setfreq (t_setfreq bl i (t_freq bl i + 1)) j
            (t_freq (t_setfreq bl i (t_freq bl i + 1)) j + 1)) (n + 1).
Proof.
  intros bl i j n Hij Hb Hn Hceil.
  set (b1 := t_setfreq bl i (t_freq bl i + 1)).
  assert (Hb1j : t_freq b1 j = t_freq bl j)
    by (unfold b1; apply t_freq_setfreq_other; lia).
  intro s.
  destruct (Hb i) as [Hi0 Hi1]. destruct (Hb j) as [Hj0 Hj1].
  destruct (Hb s) as [Hs0 Hs1].
  destruct (Z.eq_dec s j) as [->|Hsj].
  - rewrite t_freq_setfreq_same, Hb1j. unfold u16.
    rewrite Z.mod_small by lia. lia.
  - rewrite t_freq_setfreq_other by lia. unfold b1.
    destruct (Z.eq_dec s i) as [->|Hsi].
    + rewrite t_freq_setfreq_same. unfold u16. rewrite Z.mod_small by lia. lia.
    + rewrite t_freq_setfreq_other by lia. lia.
Qed.

(** ** THE INDUCTION

    [scan_go] and [send_items] walked in lockstep.  With the per-trip steps
    factored out above, each arm is: rewrite the step, apply the IH, discharge the
    budget. *)
Lemma scan_go_counts : forall f t maxc n prevlen nextlen count maxcnt mincnt bl s,
  t_len t (maxc + 1) = 65535 ->
  (forall i, 0 <= i <= maxc -> 0 <= t_len t i <= 15) ->
  0 <= count -> 0 <= n - count -> n <= maxc + 1 -> 0 <= maxc <= 285 ->
  nextlen = t_len t n ->
  (maxc < n -> count = 0) ->
  (Z.to_nat (maxc + 1 - n) <= f)%nat ->
  mincnt <= 4 ->
  Budget bl n ->
  t_freq (scan_go f t maxc n prevlen nextlen count maxcnt mincnt bl) s
  = t_freq bl s
    + hid_zcount s (items_syms (send_items f t maxc n prevlen nextlen count maxcnt mincnt)).
Proof.
  induction f as [|f IH];
    intros t maxc n prevlen nextlen count maxcnt mincnt bl s
           Hguard Hlen15 Hc Hnc Hn Hmc Hnl Hexit Hf Hmn Hbud.
  - cbn [scan_go send_items items_syms]. rewrite hid_zcount_nil. lia.
  - cbn [scan_go send_items].
    destruct (Z.ltb maxc n) eqn:Eexit.
    + cbn [items_syms]. rewrite hid_zcount_nil. lia.
    + apply Z.ltb_ge in Eexit.
      assert (H15 : 0 <= t_len t n <= 15) by (apply Hlen15; lia).
      assert (Hceil : 3 * (n + 1) <= 65535) by lia.
      destruct ((Z.ltb (count + 1) maxcnt) && (Z.eqb nextlen (t_len t (n + 1))))
               eqn:Eacc.
      * (* ACCUMULATE: nothing counted, nothing emitted *)
        apply andb_prop in Eacc as [Emax Eeq]. apply Z.eqb_eq in Eeq.
        assert (Hlt : n < maxc).
        { destruct (Z.eq_dec n maxc) as [->|Hne]; [|lia]. rewrite Hguard in Eeq. lia. }
        apply IH; try assumption; try lia; try if_bound.
        apply (Budget_mono bl n); [exact Hbud | lia].
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
                       else if Z.eqb nextlen (t_len t (n + 1)) then 3 else 4));
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
                             else if Z.eqb nextlen (t_len t (n + 1)) then 3 else 4));
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
                             else if Z.eqb nextlen (t_len t (n + 1)) then 3 else 4));
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
                             else if Z.eqb nextlen (t_len t (n + 1)) then 3 else 4));
                   try assumption; try lia; try if_bound.
                 --- rewrite (step_one bl REPZ_3_10 s) by lia. lia.
                 --- apply budget_one; try assumption; lia.
              ** rewrite items_syms_app, items_syms_z11, hid_zcount_app.
                 destruct (Hbud REPZ_11_138) as [Hg0 Hg1].
                 rewrite (IH t maxc (n + 1) nextlen (t_len t (n + 1)) 0
                            (if Z.eqb (t_len t (n + 1)) 0 then 138
                             else if Z.eqb nextlen (t_len t (n + 1)) then 6 else 7)
                            (if Z.eqb (t_len t (n + 1)) 0 then 3
                             else if Z.eqb nextlen (t_len t (n + 1)) then 3 else 4));
                   try assumption; try lia; try if_bound.
                 --- rewrite (step_one bl REPZ_11_138 s) by lia. lia.
                 --- apply budget_one; try assumption; lia.
Qed.

(** ** (S), at the entry point

    [scan_tree] writes the 0xffff guard ITSELF ([Trees.v:733]) and then runs
    [scan_go] on the guarded tree, so the statement is over
    [fst (scan_tree ...)] on both sides — which is the tree whose items are being
    counted, and which satisfies the guard hypothesis by construction rather than
    by assumption. *)

Lemma t_len_setlen_other : forall t i v j, j <> i -> t_len (t_setlen t i v) j = t_len t j.
Proof.
  intros t i v j H. unfold t_len, t_setlen. cbn [tr_dl]. apply zset_other. exact H.
Qed.

Lemma t_len_setlen_same : forall t i v, t_len (t_setlen t i v) i = u16 v.
Proof. intros t i v. unfold t_len, t_setlen. cbn [tr_dl]. apply zset_same. Qed.

Theorem scan_tree_counts : forall t maxc bl s,
  0 <= maxc <= 285 ->
  (forall i, 0 <= i <= maxc -> 0 <= t_len t i <= 15) ->
  Budget bl 0 ->
  t_freq (snd (scan_tree t maxc bl)) s
  = t_freq bl s
    + hid_zcount s (items_syms (send_tree_items (fst (scan_tree t maxc bl)) maxc)).
Proof.
  intros t maxc bl s Hmc Hlen15 Hbud.
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
  (* after the destruct the mincnt [if] reduces, so [try lia] closes every side
     goal including the nextlen equation (lia reads H0 in either direction) --
     hence NO bullet list: predicting the count is what fails here. *)
  destruct (Z.eqb (t_len t 0) 0) eqn:E0;
    (apply scan_go_counts; try assumption; try lia).
Qed.

(** ** THE BRIDGE TO HuffCover'S (S)

    What HuffCover needs is not the counts but their POSITIVITY: every symbol the
    stream uses has a nonzero frequency, so [build_bl_tree] is obliged to give it
    a code.  With the counts proved, this is immediate — and with a fresh
    frequency table (which is what [init_block] leaves) the equation reads
    directly as "frequency = number of uses". *)
Theorem scan_tree_positive : forall t maxc bl s,
  0 <= maxc <= 285 ->
  (forall i, 0 <= i <= maxc -> 0 <= t_len t i <= 15) ->
  (forall s', t_freq bl s' = 0) ->
  In s (items_syms (send_tree_items (fst (scan_tree t maxc bl)) maxc)) ->
  0 < t_freq (snd (scan_tree t maxc bl)) s.
Proof.
  intros t maxc bl s Hmc Hlen15 Hzero Hin.
  assert (Hbud : Budget bl 0) by (intro s'; rewrite Hzero; lia).
  rewrite (scan_tree_counts t maxc bl s Hmc Hlen15 Hbud), Hzero.
  unfold hid_zcount.
  assert (Hpos : (0 < count_occ Z.eq_dec
                   (items_syms (send_tree_items (fst (scan_tree t maxc bl)) maxc)) s)%nat)
    by (apply (count_occ_In Z.eq_dec); exact Hin).
  lia.
Qed.

Print Assumptions scan_go_counts.
Print Assumptions scan_tree_counts.
Print Assumptions scan_tree_positive.
