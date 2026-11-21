(** * ZReproG6G — G6 bound-fit, part G: the dispatch-site counters.

    OWNER: g6-bound (zlib z-repro campaign, 2026-08-20).

    [dispatch_counters]: at [tr_flush_block]'s huffman dispatch state
    [snd (build_bl_tree (build_tree TK_D (build_tree TK_L ts)))], with the
    walk-supplied snapshot facts (zeroed counters, fresh BL freqs,
    [FreqInv], blcount support), the counters are PLAIN-Z values OL/SL
    (no u64 wrap), and OL + 6 dominates everything the dynamic arm emits
    (per-symbol data bits + EOB + the 5+5+4+3*(mbi+1) header + both
    RLE-coded length streams in part D's [hid_zcount] vocabulary), while
    SL dominates the static arm's data bits EXACTLY.

    Assembly: three [build_tree_counters] applications (parts E/F), the
    [scan_tree_counts_gen] two-scan count law (ScanBase), and frame
    lemmas along [build_bl_tree]'s pipeline.  Per ScanBase's fuel-
    conversion warning, [send_tree_items] spellings are kept syntactically
    identical throughout — equalities are rewritten INTO positions, never
    resolved by conversion.

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Chunk ZBitsOut BwStream Trees BtWin BtCensus1 BtCensus2
  BtCensus3 BtCensus4 BtCensus5 BtAccount BtAccount2 BtItem6b BtExports
  BtSized BtTerm BtBlSide BuildTree CbEmit ClStream SendItems SendGo
  SendGoWf ScanCount ScanBase HuffCover.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import ZReproL0 SwTally
  G3DynB ZReproG6A ZReproG6C ZReproG6D ZReproG6E ZReproG6F ZReproG6M.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ==========================================================================
   1.  Setter and pipeline frames (all conversion-level).
   ========================================================================== *)

Lemma g6_ol_settree : forall k t s, ts_optlen (set_tree k t s) = ts_optlen s.
Proof. reflexivity. Qed.
Lemma g6_sl_settree : forall k t s, ts_statlen (set_tree k t s) = ts_statlen s.
Proof. reflexivity. Qed.
Lemma g6_bc_settree : forall k t s j,
  ts_blcount (set_tree k t s) j = ts_blcount s j.
Proof. reflexivity. Qed.
Lemma g6_mc_settree : forall k t s j,
  ts_maxcode (set_tree k t s) j = ts_maxcode s j.
Proof. reflexivity. Qed.
Lemma g6_sl_setoptlen : forall v s, ts_statlen (set_optlen v s) = ts_statlen s.
Proof. reflexivity. Qed.
Lemma g6_tr_setoptlen : forall v s j, ts_trees (set_optlen v s) j = ts_trees s j.
Proof. reflexivity. Qed.
Lemma g6_mc_setoptlen : forall v s j,
  ts_maxcode (set_optlen v s) j = ts_maxcode s j.
Proof. reflexivity. Qed.

(* ==========================================================================
   2.  Item-stream size bounds.
   ========================================================================== *)

Lemma send_items_count : forall f t maxc n prevlen nextlen count maxcnt mincnt,
  mincnt <= 4 ->
  (length (send_items f t maxc n prevlen nextlen count maxcnt mincnt)
   <= 3 * f)%nat.
Proof.
  induction f as [|f IH];
    intros t maxc n prevlen nextlen count maxcnt mincnt Hmn;
    cbn [send_items].
  - cbn [length]. lia.
  - destruct (Z.ltb maxc n); [cbn [length]; lia|].
    destruct ((Z.ltb (count + 1) maxcnt)
              && (Z.eqb nextlen (t_len t (n + 1)))).
    + pose proof (IH t maxc (n + 1) prevlen (t_len t (n + 1))
                    (count + 1) maxcnt mincnt Hmn). lia.
    + rewrite length_app.
      match goal with
      | |- (length ?ITEMS + _ <= _)%nat =>
          assert (Hit : (length ITEMS <= 3)%nat)
      end.
      { destruct (Z.ltb_spec (count + 1) mincnt) as [Hlt|Hge].
        - rewrite repeat_length. lia.
        - destruct (negb (Z.eqb nextlen 0)).
          + destruct (negb (Z.eqb nextlen prevlen)); cbn [length]; lia.
          + destruct (Z.leb (count + 1) 10); cbn [length]; lia. }
      match goal with
      | |- (_ + length (send_items f t maxc (n + 1) ?PL ?NL ?C ?MC ?MN) <= _)%nat =>
          assert (Hrec : (length (send_items f t maxc (n + 1) PL NL C MC MN)
                          <= 3 * f)%nat)
            by (apply IH;
                destruct (Z.eqb (t_len t (n + 1)) 0);
                [lia|destruct (Z.eqb nextlen (t_len t (n + 1))); lia])
      end.
      lia.
Qed.

Lemma send_tree_items_count : forall t maxc,
  (length (send_tree_items t maxc) <= 867)%nat.
Proof.
  intros t maxc. unfold send_tree_items. cbv zeta.
  assert (Hmn : (if Z.eqb (t_len t 0) 0 then 3 else 4) <= 4)
    by (destruct (Z.eqb (t_len t 0) 0); lia).
  pose proof (send_items_count (Z.to_nat L_CODES + 3) t maxc 0 (-1)
                (t_len t 0) 0
                (if Z.eqb (t_len t 0) 0 then 138 else 7)
                (if Z.eqb (t_len t 0) 0 then 3 else 4) Hmn) as H.
  change (Z.to_nat L_CODES + 3)%nat with 289%nat in H |- *. lia.
Qed.

Lemma items_syms_length : forall items,
  length (items_syms items) = length items.
Proof.
  induction items as [|it tl IH]; [reflexivity|].
  cbn [items_syms flat_map length].
  destruct it; cbn [item_syms length]; rewrite <- IH; reflexivity.
Qed.

Lemma hid_le_length : forall s l, hid_zcount s l <= Z.of_nat (length l).
Proof.
  intros s l. unfold hid_zcount.
  pose proof (count_occ_bound Z.eq_dec s l). lia.
Qed.

Lemma hid_nonneg : forall s l, 0 <= hid_zcount s l.
Proof. intros s l. unfold hid_zcount. lia. Qed.

(* ==========================================================================
   3.  xbits and static-table ranges, per tree kind.
   ========================================================================== *)

Lemma xbits_L_range : forall v, 0 <= v < 286 ->
  0 <= xbits (sd_extra_base TK_L) (sd_extra TK_L) v <= 16.
Proof.
  intros v Hv.
  change (sd_extra_base TK_L) with (LITERALS + 1).
  change (sd_extra TK_L) with extra_lbits.
  unfold xbits.
  destruct (Z.leb_spec (LITERALS + 1) v) as [H|H]; [|lia].
  apply extra_lbits_range. unfold LITERALS in *. lia.
Qed.

Lemma xbits_D_range : forall v, 0 <= v < 30 ->
  0 <= xbits (sd_extra_base TK_D) (sd_extra TK_D) v <= 16.
Proof.
  intros v Hv.
  change (sd_extra_base TK_D) with 0.
  change (sd_extra TK_D) with extra_dbits.
  unfold xbits.
  destruct (Z.leb_spec 0 v) as [H|H]; [|lia].
  replace (v - 0) with v by ring.
  apply extra_dbits_range. lia.
Qed.

Lemma xbits_BL_range : forall v, 0 <= v < 19 ->
  0 <= xbits (sd_extra_base TK_BL) (sd_extra TK_BL) v <= 16.
Proof.
  intros v Hv.
  change (sd_extra_base TK_BL) with 0.
  change (sd_extra TK_BL) with extra_blbits.
  unfold xbits.
  destruct (Z.leb_spec 0 v) as [H|H]; [|lia].
  replace (v - 0) with v by ring.
  apply extra_blbits_range. lia.
Qed.

Definition g6_stl_at (v : Z) : bool :=
  (0 <=? t_len static_ltree v) && (t_len static_ltree v <=? 16).

Lemma g6_stl_all : forallb g6_stl_at (zseq 286 0) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma static_ltree_len_range : forall v, 0 <= v < 286 ->
  0 <= t_len static_ltree v <= 16.
Proof.
  intros v Hv.
  pose proof (forallb_zseq' g6_stl_at 286 286 v
                ltac:(vm_compute; reflexivity) g6_stl_all Hv) as H.
  unfold g6_stl_at in H.
  apply andb_true_iff in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.

Definition g6_std_at (v : Z) : bool :=
  (0 <=? t_len static_dtree v) && (t_len static_dtree v <=? 16).

Lemma g6_std_all : forallb g6_std_at (zseq 30 0) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma static_dtree_len_range : forall v, 0 <= v < 30 ->
  0 <= t_len static_dtree v <= 16.
Proof.
  intros v Hv.
  pose proof (forallb_zseq' g6_std_at 30 30 v
                ltac:(vm_compute; reflexivity) g6_std_all Hv) as H.
  unfold g6_std_at in H.
  apply andb_true_iff in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.

(* ==========================================================================
   4.  The shape wrapper: maxcode range, output lens, blcount support.
   ========================================================================== *)

Lemma build_tree_shape : forall k s,
  3 <= sd_elems k <= 286 ->
  1 <= sd_max_length k <= 15 ->
  4 * (sd_elems k - 1) < 2 ^ sd_max_length k ->
  (forall b, b < 0 \/ 15 < b -> ts_blcount s b = 0) ->
  0 <= ts_maxcode (build_tree k s) k < sd_elems k
  /\ (forall x, 0 <= x < sd_elems k ->
      0 <= t_len (ts_trees (build_tree k s) k) x <= sd_max_length k)
  /\ (forall b, b < 0 \/ 15 < b -> ts_blcount (build_tree k s) b = 0)
  /\ (forall v, 0 <= v < sd_elems k -> t_freq (ts_trees s k) v <> 0 ->
      v <= ts_maxcode (build_tree k s) k).
Proof.
  intros k s Hel HM HK4 Hbl0.
  assert (HLC : L_CODES = 286) by reflexivity.
  destruct (bt_init (Z.to_nat L_CODES + 2) 0 (sd_elems k) (ts_trees s k)
              (ts_heap s) (ts_depth s) 0 (-1))
    as [[[[t0 hp0] dep0] hlen0] maxc0] eqn:E0.
  destruct (bt_init_census_call (Z.to_nat L_CODES + 2) (sd_elems k)
              (ts_trees s k) (ts_heap s) (ts_depth s) t0 hp0 dep0 hlen0 maxc0
              E0
              ltac:(change (Z.of_nat (Z.to_nat L_CODES + 2)) with 288; lia)
              ltac:(lia)) as [Hout0 Hfr0].
  destruct (bt_force2 3%nat (sd_stree k) t0 hp0 dep0 hlen0 maxc0
              (ts_optlen s) (ts_statlen s))
    as [[[[[[t1 hp1] dep1] hlen1] maxc1] ol1] sl1] eqn:E2.
  assert (Hsz : 2 <= hlen1 <= L_CODES)
    by (eapply bt_sized; try eassumption; lia).
  destruct (bt_loop (Z.to_nat HEAP_SIZE)
              {| b_tree := t1;
                 b_heap := bt_heapify (Z.to_nat HEAP_SIZE) t1 dep1 hp1 hlen1
                             (hlen1 / 2);
                 b_dep := dep1; b_hlen := hlen1; b_hmax := HEAP_SIZE;
                 b_node := sd_elems k |}) as [stf|] eqn:Eloop.
  2:{ exfalso.
      eapply (bt_loop_terminates (Z.to_nat HEAP_SIZE)); [| | exact Eloop].
      - cbn [b_hlen]. lia.
      - cbn [b_hlen].
        rewrite Z2Nat.id by (unfold HEAP_SIZE, L_CODES; lia).
        unfold HEAP_SIZE, L_CODES in *. lia. }
  destruct (build_tree_parked k s t0 hp0 dep0 hlen0 maxc0
              t1 hp1 dep1 hlen1 maxc1 ol1 sl1
              (bt_heapify (Z.to_nat HEAP_SIZE) t1 dep1 hp1 hlen1 (hlen1 / 2))
              stf ltac:(lia) E0 E2 eq_refl Eloop)
    as [Hpk [Hout1 [Hsz' [Hcen Hfrt0]]]].
  assert (Hh1e : hlen1 <= sd_elems k).
  { rewrite (io_total _ _ _ _ _ Hout1). apply live_total_le. lia. }
  assert (HK : 4 * (hlen1 - 1) < 2 ^ sd_max_length k) by lia.
  destruct (BtItem6b.build_tree_out k s t0 hp0 dep0 hlen0 maxc0 t1 hp1 dep1
              hlen1 maxc1 ol1 sl1 stf ltac:(lia) HM HK Hbl0 E0 E2 Eloop)
    as (Hmc' & _ & _ & _ & _ & _ & Hlen7).
  destruct (bt_force2_full (sd_stree k) (sd_elems k) t0 hp0 dep0 hlen0 maxc0
              (ts_optlen s) (ts_statlen s) t1 hp1 dep1 hlen1 maxc1 ol1 sl1
              E2 ltac:(lia) Hout0) as [Hmcmono Hcases].
  assert (Hmc1nn : 0 <= maxc1).
  { destruct Hcases as
      [(Hh2 & _ & Emc & _)
      |[(v1 & _ & _ & _ & Hv1m & _ & _ & _)
       |(_ & _ & _ & _ & Emc1 & _ & _)]]; try lia.
    (* hlen0 >= 2: two live entry symbols force maxc0 >= 0 *)
    destruct (Z_le_gt_dec 0 maxc0) as [H|H]; [lia|].
    exfalso.
    assert (Hm1 : maxc0 = -1)
      by (pose proof (io_maxc _ _ _ _ _ Hout0); lia).
    pose proof (io_total _ _ _ _ _ Hout0) as Htot.
    rewrite Hm1 in Htot.
    unfold live_total in Htot.
    rewrite (wsum_ext (fun x => ind (live_b t0 (-1) x)) (fun _ => 0)
               0 (Z.to_nat (sd_elems k))) in Htot
      by (intros i _; rewrite live_b_m1; reflexivity).
    rewrite (g6_wsum_const 0 0 (Z.to_nat (sd_elems k))) in Htot.
    lia. }
  pose proof (bp_maxc _ _ _ _ _ _ _ Hpk) as Hbmc.
  split; [rewrite Hmc'; lia|].
  split; [exact Hlen7|].
  split.
  { intros b Hb.
    apply (build_tree_blc0 k s t0 hp0 dep0 hlen0 maxc0 t1 hp1 dep1 hlen1
             maxc1 ol1 sl1 stf ltac:(lia) HM HK Hbl0 E0 E2 Eloop).
    lia. }
  intros v Hv Hnz.
  rewrite Hmc'.
  destruct (Z_le_gt_dec v maxc0) as [H|H]; [lia|].
  exfalso. apply Hnz. rewrite <- (Hfr0 v).
  apply (io_gapz _ _ _ _ _ Hout0). lia.
Qed.

(* ==========================================================================
   5.  Count-to-frequency and vocabulary bridges.
   ========================================================================== *)

Lemma g6_countL_to_freq : forall ts toks (C : Z -> Z),
  (forall i, 0 <= i < L_CODES ->
   t_freq (ts_trees ts TK_L) i
   = count_L i toks + (if Z.eqb i END_BLOCK then 1 else 0)) ->
  wsum (fun i => t_freq (ts_trees ts TK_L) i * C i) 0 (Z.to_nat L_CODES)
  = wsum (fun i => count_L i toks * C i) 0 (Z.to_nat L_CODES) + C 256.
Proof.
  intros ts toks C HFL.
  rewrite (wsum_ext (fun i => t_freq (ts_trees ts TK_L) i * C i)
             (fun i => count_L i toks * C i
                       + (if Z.eqb 256 i then 1 else 0) * C i)
             0 (Z.to_nat L_CODES)).
  2:{ intros i Hi.
      change (Z.of_nat (Z.to_nat L_CODES)) with 286 in Hi.
      rewrite (HFL i) by (unfold L_CODES; lia).
      destruct (Z.eqb_spec i 256) as [->|Ne].
      - replace (Z.eqb 256 END_BLOCK) with true by reflexivity.
        replace (Z.eqb 256 256) with true by reflexivity.
        ring.
      - replace (Z.eqb i END_BLOCK) with false
          by (symmetry; apply Z.eqb_neq; unfold END_BLOCK; lia).
        replace (Z.eqb 256 i) with false
          by (symmetry; apply Z.eqb_neq; lia).
        ring. }
  rewrite wsum_plus.
  rewrite (wsum_delta C 256 0 (Z.to_nat L_CODES))
    by (change (Z.of_nat (Z.to_nat L_CODES)) with 286; lia).
  reflexivity.
Qed.

Lemma g6_countD_to_freq : forall ts toks (C : Z -> Z),
  (forall i, 0 <= i < D_CODES ->
   t_freq (ts_trees ts TK_D) i = count_D i toks) ->
  wsum (fun i => t_freq (ts_trees ts TK_D) i * C i) 0 (Z.to_nat D_CODES)
  = wsum (fun i => count_D i toks * C i) 0 (Z.to_nat D_CODES).
Proof.
  intros ts toks C HFD.
  apply wsum_ext. intros i Hi.
  change (Z.of_nat (Z.to_nat D_CODES)) with 30 in Hi.
  rewrite HFD by (unfold D_CODES; lia). reflexivity.
Qed.

(** Bridging the scanned (guarded) tree's lengths back to the built tree:
    the sentinel at [mc + 1] sits under a zero frequency. *)
Lemma g6_scan_len_bridge : forall (frq : Z -> Z) t mc bl (xb : Z -> Z) n,
  (forall i, 0 <= i < Z.of_nat n -> frq i <> 0 -> i <> mc + 1) ->
  wsum (fun i => frq i * (t_len (fst (scan_tree t mc bl)) i + xb i)) 0 n
  = wsum (fun i => frq i * (t_len t i + xb i)) 0 n.
Proof.
  intros frq t mc bl xb n H.
  apply wsum_ext. intros i Hi.
  destruct (Z.eq_dec (frq i) 0) as [->|Ne]; [ring|].
  rewrite scan_tree_len_other by (apply H; [lia | exact Ne]).
  reflexivity.
Qed.

Lemma g6_costL_vocab : forall lt i,
  cost_L lt i = t_len lt i + xbits (sd_extra_base TK_L) (sd_extra TK_L) i.
Proof.
  intros lt i. unfold cost_L.
  change (sd_extra_base TK_L) with (LITERALS + 1).
  change (sd_extra TK_L) with extra_lbits.
  unfold xbits. reflexivity.
Qed.

Lemma g6_costD_vocab : forall dt i, 0 <= i ->
  cost_D dt i = t_len dt i + xbits (sd_extra_base TK_D) (sd_extra TK_D) i.
Proof.
  intros dt i Hi. unfold cost_D.
  change (sd_extra_base TK_D) with 0.
  change (sd_extra TK_D) with extra_dbits.
  unfold xbits.
  replace (Z.leb 0 i) with true by (symmetry; apply Z.leb_le; lia).
  replace (i - 0) with i by ring.
  reflexivity.
Qed.

Lemma g6_costBL_vocab : forall bl i, 0 <= i ->
  t_len bl i + extra_blbits i
  = t_len bl i + xbits (sd_extra_base TK_BL) (sd_extra TK_BL) i.
Proof.
  intros bl i Hi.
  change (sd_extra_base TK_BL) with 0.
  change (sd_extra TK_BL) with extra_blbits.
  unfold xbits.
  replace (Z.leb 0 i) with true by (symmetry; apply Z.leb_le; lia).
  replace (i - 0) with i by ring.
  reflexivity.
Qed.

(** Per-token code-length windows at a pair of trees — the width premise
    the dynamic arm's length walk consumes (the guarded tree breaks a
    blanket [LenB], but every TALLIED code index sits at or below the
    maxcode, where the guard is invisible). *)
Definition tok_widths_ok (lt dt : Tree) (t : Tok) : Prop :=
  match t with
  | TLit b => 0 <= t_len lt b <= 15
  | TMatch len dist =>
      0 <= t_len lt (length_code (len - 3) + LITERALS + 1) <= 15
      /\ 0 <= t_len dt (d_code (dist - 1)) <= 15
  end.

(* ==========================================================================
   6.  The dispatch-site counters.
   ========================================================================== *)

Theorem dispatch_counters : forall ts toks,
  ts_optlen ts = 0 ->
  ts_statlen ts = 0 ->
  (forall b, b < 0 \/ 15 < b -> ts_blcount ts b = 0) ->
  FreqInv toks ts ->
  cEnc toks ->
  Z.of_nat (length toks) <= 16383 ->
  (forall v, 0 <= v < 19 -> t_freq (ts_trees ts TK_BL) v = 0) ->
  (forall i, 0 <= t_len (ts_trees ts TK_L) i) ->
  (forall i, 0 <= t_len (ts_trees ts TK_D) i) ->
  exists OL SL,
    ts_optlen (snd (build_bl_tree (build_tree TK_D (build_tree TK_L ts))))
      = OL
    /\ ts_statlen (snd (build_bl_tree (build_tree TK_D (build_tree TK_L ts))))
       = SL
    /\ 11 <= OL <= 2 ^ 40
    /\ 0 <= SL <= 2 ^ 40
    /\ 2 <= fst (build_bl_tree (build_tree TK_D (build_tree TK_L ts))) <= 18
    /\ 0 <= ts_maxcode
              (snd (build_bl_tree (build_tree TK_D (build_tree TK_L ts))))
              TK_L <= 285
    /\ 0 <= ts_maxcode
              (snd (build_bl_tree (build_tree TK_D (build_tree TK_L ts))))
              TK_D <= 285
    /\ t_len (ts_trees
                (snd (build_bl_tree (build_tree TK_D (build_tree TK_L ts))))
                TK_L)
             (ts_maxcode
                (snd (build_bl_tree (build_tree TK_D (build_tree TK_L ts))))
                TK_L + 1) = 65535
    /\ t_len (ts_trees
                (snd (build_bl_tree (build_tree TK_D (build_tree TK_L ts))))
                TK_D)
             (ts_maxcode
                (snd (build_bl_tree (build_tree TK_D (build_tree TK_L ts))))
                TK_D + 1) = 65535
    /\ (forall i, 0 <= i <= ts_maxcode
                    (snd (build_bl_tree (build_tree TK_D (build_tree TK_L ts))))
                    TK_L ->
        0 <= t_len (ts_trees
                      (snd (build_bl_tree (build_tree TK_D (build_tree TK_L ts))))
                      TK_L) i <= 15)
    /\ (forall i, 0 <= i <= ts_maxcode
                    (snd (build_bl_tree (build_tree TK_D (build_tree TK_L ts))))
                    TK_D ->
        0 <= t_len (ts_trees
                      (snd (build_bl_tree (build_tree TK_D (build_tree TK_L ts))))
                      TK_D) i <= 15)
    /\ (forall i, 0 <= t_len (ts_trees
                      (snd (build_bl_tree (build_tree TK_D (build_tree TK_L ts))))
                      TK_L) i)
    /\ (forall i, 0 <= t_len (ts_trees
                      (snd (build_bl_tree (build_tree TK_D (build_tree TK_L ts))))
                      TK_D) i)
    /\ LenBL (ts_trees
                (snd (build_bl_tree (build_tree TK_D (build_tree TK_L ts))))
                TK_BL)
    /\ Forall (tok_widths_ok
                 (ts_trees
                    (snd (build_bl_tree (build_tree TK_D (build_tree TK_L ts))))
                    TK_L)
                 (ts_trees
                    (snd (build_bl_tree (build_tree TK_D (build_tree TK_L ts))))
                    TK_D)) toks
    /\ 0 <= t_len (ts_trees
                     (snd (build_bl_tree (build_tree TK_D (build_tree TK_L ts))))
                     TK_L) END_BLOCK <= 15
    /\ toks_cost (ts_trees
                    (snd (build_bl_tree (build_tree TK_D (build_tree TK_L ts))))
                    TK_L)
                 (ts_trees
                    (snd (build_bl_tree (build_tree TK_D (build_tree TK_L ts))))
                    TK_D) toks
         + t_len (ts_trees
                    (snd (build_bl_tree (build_tree TK_D (build_tree TK_L ts))))
                    TK_L) END_BLOCK
         + (14 + 3 * (fst (build_bl_tree (build_tree TK_D (build_tree TK_L ts)))
                      + 1))
         + wsum (fun sy =>
             hid_zcount sy
               (items_syms
                  (send_tree_items
                     (ts_trees
                        (snd (build_bl_tree (build_tree TK_D (build_tree TK_L ts))))
                        TK_L)
                     (ts_maxcode
                        (snd (build_bl_tree (build_tree TK_D (build_tree TK_L ts))))
                        TK_L)))
             * (t_len (ts_trees
                         (snd (build_bl_tree (build_tree TK_D (build_tree TK_L ts))))
                         TK_BL) sy + extra_blbits sy)) 0 19
         + wsum (fun sy =>
             hid_zcount sy
               (items_syms
                  (send_tree_items
                     (ts_trees
                        (snd (build_bl_tree (build_tree TK_D (build_tree TK_L ts))))
                        TK_D)
                     (ts_maxcode
                        (snd (build_bl_tree (build_tree TK_D (build_tree TK_L ts))))
                        TK_D)))
             * (t_len (ts_trees
                         (snd (build_bl_tree (build_tree TK_D (build_tree TK_L ts))))
                         TK_BL) sy + extra_blbits sy)) 0 19
       <= OL + 6
    /\ toks_cost static_ltree static_dtree toks
         + t_len static_ltree END_BLOCK
       <= SL
    /\ SL <= toks_cost static_ltree static_dtree toks
            + t_len static_ltree END_BLOCK + 64.
Proof.
  intros ts toks Hol0 Hsl0 Hbl0 HFI Henc Hlen HblZ HnnL HnnD.
  destruct HFI as [HFL HFD].
  (* --- entry frequency bounds from the counts --- *)
  assert (HfrL : forall i, 0 <= i < sd_elems TK_L ->
                 0 <= t_freq (ts_trees ts TK_L) i <= 65535).
  { intros i Hi. change (sd_elems TK_L) with 286 in Hi.
    rewrite (HFL i) by (unfold L_CODES; lia).
    pose proof (count_L_nonneg i toks).
    pose proof (count_L_le_len i toks).
    destruct (Z.eqb i END_BLOCK); lia. }
  assert (HfrD0 : forall i, 0 <= i < sd_elems TK_D ->
                  0 <= t_freq (ts_trees ts TK_D) i <= 65535).
  { intros i Hi. change (sd_elems TK_D) with 30 in Hi.
    rewrite (HFD i) by (unfold D_CODES; lia).
    pose proof (count_D_nonneg i toks).
    pose proof (count_D_le_len i toks). lia. }
  (* --- the L build --- *)
  set (BL' := build_tree TK_L ts) in *.
  assert (HelL : 3 <= sd_elems TK_L <= 286)
    by (change (sd_elems TK_L) with 286; lia).
  assert (HML : 1 <= sd_max_length TK_L <= 15)
    by (change (sd_max_length TK_L) with 15; lia).
  assert (HKL : 4 * (sd_elems TK_L - 1) < 2 ^ sd_max_length TK_L)
    by (change (sd_elems TK_L) with 286;
        change (2 ^ sd_max_length TK_L) with 32768; lia).
  assert (HstbL : forall st, sd_stree TK_L = Some st ->
                  forall v, 0 <= v < sd_elems TK_L -> 0 <= t_len st v <= 16).
  { intros st Est v Hv.
    change (sd_stree TK_L) with (Some static_ltree) in Est.
    injection Est as <-.
    change (sd_elems TK_L) with 286 in Hv.
    apply static_ltree_len_range. exact Hv. }
  assert (HxbL : forall v, 0 <= v < sd_elems TK_L ->
                 0 <= xbits (sd_extra_base TK_L) (sd_extra TK_L) v <= 16)
    by (intros v Hv; change (sd_elems TK_L) with 286 in Hv;
        apply xbits_L_range; exact Hv).
  destruct (build_tree_counters TK_L ts HelL HML HKL Hbl0 HfrL HxbL HstbL
              ltac:(rewrite Hol0; reflexivity)
              ltac:(rewrite Hsl0; reflexivity))
    as (BTCL & BTSL & EolL & EslL & HbLr & HbSLr & HdomL & HdomSLg & HupSLg).
  fold BL' in EolL, EslL, HdomL, HdomSLg.
  change (sd_stree TK_L) with (Some static_ltree) in EslL.
  cbv iota in EslL.
  pose proof (HdomSLg static_ltree eq_refl) as HdomSL.
  clear HdomSLg.
  pose proof (HupSLg static_ltree eq_refl) as HupSL.
  clear HupSLg.
  destruct (build_tree_shape TK_L ts HelL HML HKL Hbl0)
    as (HmcLr & HlenL & HblL & HcapL).
  fold BL' in HmcLr, HlenL, HblL, HcapL.
  (* --- the D build --- *)
  set (BD' := build_tree TK_D BL') in *.
  assert (NEQ_D_L : TK_D <> TK_L)
    by (change TK_D with 1; change TK_L with 0; lia).
  assert (NEQ_L_D : TK_L <> TK_D)
    by (change TK_L with 0; change TK_D with 1; lia).
  assert (NEQ_L_BL : TK_L <> TK_BL)
    by (change TK_L with 0; change TK_BL with 2; lia).
  assert (NEQ_D_BL : TK_D <> TK_BL)
    by (change TK_D with 1; change TK_BL with 2; lia).
  assert (NEQ_BL_L : TK_BL <> TK_L)
    by (change TK_BL with 2; change TK_L with 0; lia).
  assert (NEQ_BL_D : TK_BL <> TK_D)
    by (change TK_BL with 2; change TK_D with 1; lia).
  assert (EfrD : ts_trees BL' TK_D = ts_trees ts TK_D)
    by (unfold BL'; apply build_tree_tree_other; exact NEQ_D_L).
  assert (HelD : 3 <= sd_elems TK_D <= 286)
    by (change (sd_elems TK_D) with 30; lia).
  assert (HMD : 1 <= sd_max_length TK_D <= 15)
    by (change (sd_max_length TK_D) with 15; lia).
  assert (HKD : 4 * (sd_elems TK_D - 1) < 2 ^ sd_max_length TK_D)
    by (change (sd_elems TK_D) with 30;
        change (2 ^ sd_max_length TK_D) with 32768; lia).
  assert (HstbD : forall st, sd_stree TK_D = Some st ->
                  forall v, 0 <= v < sd_elems TK_D -> 0 <= t_len st v <= 16).
  { intros st Est v Hv.
    change (sd_stree TK_D) with (Some static_dtree) in Est.
    injection Est as <-.
    change (sd_elems TK_D) with 30 in Hv.
    apply static_dtree_len_range. exact Hv. }
  assert (HxbD : forall v, 0 <= v < sd_elems TK_D ->
                 0 <= xbits (sd_extra_base TK_D) (sd_extra TK_D) v <= 16)
    by (intros v Hv; change (sd_elems TK_D) with 30 in Hv;
        apply xbits_D_range; exact Hv).
  assert (HfrD : forall i, 0 <= i < sd_elems TK_D ->
                 0 <= t_freq (ts_trees BL' TK_D) i <= 65535)
    by (intros i Hi; rewrite EfrD; apply HfrD0; exact Hi).
  destruct (build_tree_counters TK_D BL' HelD HMD HKD HblL HfrD HxbD HstbD
              ltac:(rewrite EolL; symmetry; apply g6_u64_idem)
              ltac:(rewrite EslL; symmetry; apply g6_u64_idem))
    as (BTCD & BTSD & EolD & EslD & HbDr & HbSDr & HdomD0 & HdomSDg & HupSDg).
  fold BD' in EolD, EslD, HdomD0.
  change (sd_stree TK_D) with (Some static_dtree) in EslD.
  cbv iota in EslD.
  pose proof (HdomSDg static_dtree eq_refl) as HdomSD0.
  clear HdomSDg.
  pose proof (HupSDg static_dtree eq_refl) as HupSD0.
  clear HupSDg.
  destruct (build_tree_shape TK_D BL' HelD HMD HKD HblL)
    as (HmcDr & HlenD & HblD & HcapD).
  fold BD' in HmcDr, HlenD, HblD, HcapD.
  (* restate the D dominations over the entry (ts) frequencies *)
  assert (HdomD : wsum (fun v => t_freq (ts_trees ts TK_D) v
                          * (t_len (ts_trees BD' TK_D) v
                             + xbits (sd_extra_base TK_D) (sd_extra TK_D) v))
                    0 (Z.to_nat (sd_elems TK_D))
                  <= BTCD + 2).
  { rewrite (wsum_ext _ (fun v => t_freq (ts_trees BL' TK_D) v
                          * (t_len (ts_trees BD' TK_D) v
                             + xbits (sd_extra_base TK_D) (sd_extra TK_D) v))
               0 (Z.to_nat (sd_elems TK_D)))
      by (intros i _; rewrite EfrD; reflexivity).
    exact HdomD0. }
  assert (HdomSD : wsum (fun v => t_freq (ts_trees ts TK_D) v
                           * (t_len static_dtree v
                              + xbits (sd_extra_base TK_D) (sd_extra TK_D) v))
                     0 (Z.to_nat (sd_elems TK_D))
                   <= BTSD).
  { rewrite (wsum_ext _ (fun v => t_freq (ts_trees BL' TK_D) v
                           * (t_len static_dtree v
                              + xbits (sd_extra_base TK_D) (sd_extra TK_D) v))
               0 (Z.to_nat (sd_elems TK_D)))
      by (intros i _; rewrite EfrD; reflexivity).
    exact HdomSD0. }
  assert (HupSD : BTSD <= wsum (fun v => t_freq (ts_trees ts TK_D) v
                           * (t_len static_dtree v
                              + xbits (sd_extra_base TK_D) (sd_extra TK_D) v))
                     0 (Z.to_nat (sd_elems TK_D)) + 32).
  { rewrite (wsum_ext _ (fun v => t_freq (ts_trees BL' TK_D) v
                           * (t_len static_dtree v
                              + xbits (sd_extra_base TK_D) (sd_extra TK_D) v))
               0 (Z.to_nat (sd_elems TK_D)))
      by (intros i _; rewrite EfrD; reflexivity).
    exact HupSD0. }
  (* --- the build_bl_tree pipeline, destructured --- *)
  set (tL := ts_trees BD' TK_L) in *.
  set (mcL := ts_maxcode BD' TK_L) in *.
  set (bl0 := ts_trees BD' TK_BL) in *.
  set (p1 := scan_tree tL mcL bl0) in *.
  set (s1' := set_tree TK_BL (snd p1) (set_tree TK_L (fst p1) BD')) in *.
  set (tD := ts_trees s1' TK_D) in *.
  set (mcD := ts_maxcode s1' TK_D) in *.
  set (bl1 := ts_trees s1' TK_BL) in *.
  set (p2 := scan_tree tD mcD bl1) in *.
  set (s2' := set_tree TK_BL (snd p2) (set_tree TK_D (fst p2) s1')) in *.
  set (s3 := build_tree TK_BL s2') in *.
  set (mbi := bbl_scan (Z.to_nat BL_CODES + 1) (ts_trees s3 TK_BL)
                (BL_CODES - 1)) in *.
  assert (EP : build_bl_tree BD'
               = (mbi, set_optlen
                         (u64 (ts_optlen s3 + 3 * (mbi + 1) + 5 + 5 + 4))
                         s3)).
  { unfold build_bl_tree. cbv zeta. reflexivity. }
  (* --- frames along the pipeline --- *)
  assert (EtL : tL = ts_trees BL' TK_L)
    by (unfold tL, BD'; apply build_tree_tree_other; exact NEQ_L_D).
  assert (EmcL0 : mcL = ts_maxcode BL' TK_L)
    by (unfold mcL, BD'; apply build_tree_maxcode_other; exact NEQ_L_D).
  assert (Ebl0 : forall v, 0 <= v < 19 -> t_freq bl0 v = 0).
  { intros v Hv. unfold bl0, BD'.
    rewrite (build_tree_tree_other TK_D BL' TK_BL) by exact NEQ_BL_D.
    unfold BL'.
    rewrite (build_tree_tree_other TK_L ts TK_BL) by exact NEQ_BL_L.
    apply HblZ. exact Hv. }
  assert (EtD : tD = ts_trees BD' TK_D).
  { unfold tD, s1'.
    rewrite (set_tree_other TK_BL (snd p1) (set_tree TK_L (fst p1) BD') TK_D)
      by exact NEQ_D_BL.
    rewrite (set_tree_other TK_L (fst p1) BD' TK_D) by exact NEQ_D_L.
    reflexivity. }
  assert (EmcD0 : mcD = ts_maxcode BD' TK_D)
    by (unfold mcD, s1'; rewrite !g6_mc_settree; reflexivity).
  assert (Ebl1 : bl1 = snd p1)
    by (unfold bl1, s1'; apply set_tree_same).
  assert (EtrL : ts_trees (snd (build_bl_tree BD')) TK_L = fst p1).
  { rewrite EP. cbn [snd]. rewrite g6_tr_setoptlen.
    unfold s3.
    rewrite (build_tree_tree_other TK_BL s2' TK_L) by exact NEQ_L_BL.
    unfold s2'.
    rewrite (set_tree_other TK_BL (snd p2) (set_tree TK_D (fst p2) s1') TK_L)
      by exact NEQ_L_BL.
    rewrite (set_tree_other TK_D (fst p2) s1' TK_L) by exact NEQ_L_D.
    unfold s1'.
    rewrite (set_tree_other TK_BL (snd p1) (set_tree TK_L (fst p1) BD') TK_L)
      by exact NEQ_L_BL.
    apply set_tree_same. }
  assert (EtrD : ts_trees (snd (build_bl_tree BD')) TK_D = fst p2).
  { rewrite EP. cbn [snd]. rewrite g6_tr_setoptlen.
    unfold s3.
    rewrite (build_tree_tree_other TK_BL s2' TK_D) by exact NEQ_D_BL.
    unfold s2'.
    rewrite (set_tree_other TK_BL (snd p2) (set_tree TK_D (fst p2) s1') TK_D)
      by exact NEQ_D_BL.
    apply set_tree_same. }
  assert (EtrB : ts_trees (snd (build_bl_tree BD')) TK_BL = ts_trees s3 TK_BL)
    by (rewrite EP; cbn [snd]; apply g6_tr_setoptlen).
  assert (EmcLf : ts_maxcode (snd (build_bl_tree BD')) TK_L = mcL).
  { rewrite EP. cbn [snd]. rewrite g6_mc_setoptlen.
    unfold s3.
    rewrite (build_tree_maxcode_other TK_BL s2' TK_L) by exact NEQ_L_BL.
    unfold s2'. rewrite !g6_mc_settree.
    reflexivity. }
  assert (EmcDf : ts_maxcode (snd (build_bl_tree BD')) TK_D = mcD).
  { rewrite EP. cbn [snd]. rewrite g6_mc_setoptlen.
    unfold s3.
    rewrite (build_tree_maxcode_other TK_BL s2' TK_D) by exact NEQ_D_BL.
    unfold s2'. rewrite !g6_mc_settree.
    reflexivity. }
  (* --- the scan count laws --- *)
  assert (Hbud0 : RBudget bl0 0)
    by (intros v Hv; rewrite (Ebl0 v Hv); lia).
  assert (HmcL285 : 0 <= mcL <= 285)
    by (rewrite EmcL0; change (sd_elems TK_L) with 286 in HmcLr; lia).
  assert (HlentL : forall i, 0 <= i <= mcL -> 0 <= t_len tL i <= 15).
  { intros i Hi. rewrite EtL.
    assert (Hi' : 0 <= i < sd_elems TK_L)
      by (change (sd_elems TK_L) with 286; lia).
    pose proof (HlenL i Hi').
    change (sd_max_length TK_L) with 15 in *. lia. }
  assert (Cnt1 : forall v, t_freq (snd p1) v
                 = t_freq bl0 v
                   + hid_zcount v (items_syms (send_tree_items (fst p1) mcL))).
  { intro v.
    apply (scan_tree_counts_r tL mcL bl0 v 0 287 HmcL285 HlentL Hbud0);
      lia. }
  assert (Hbud1 : RBudget bl1 286).
  { rewrite Ebl1.
    apply (scan_tree_budget_r tL mcL bl0 0 286 HmcL285 HlentL Hbud0); lia. }
  assert (HmcD285 : 0 <= mcD <= 285)
    by (rewrite EmcD0; change (sd_elems TK_D) with 30 in HmcDr; lia).
  assert (HlentD : forall i, 0 <= i <= mcD -> 0 <= t_len tD i <= 15).
  { intros i Hi. rewrite EtD.
    assert (Hi' : 0 <= i < sd_elems TK_D)
      by (change (sd_elems TK_D) with 30; rewrite EmcD0 in Hi;
          change (sd_elems TK_D) with 30 in HmcDr; lia).
    pose proof (HlenD i Hi').
    change (sd_max_length TK_D) with 15 in *. lia. }
  assert (Cnt2 : forall v, t_freq (snd p2) v
                 = t_freq bl1 v
                   + hid_zcount v (items_syms (send_tree_items (fst p2) mcD))).
  { intro v.
    apply (scan_tree_counts_r tD mcD bl1 v 286 572 HmcD285 HlentD Hbud1);
      lia. }
  assert (CntB : forall v, 0 <= v < 19 ->
                 t_freq (ts_trees s2' TK_BL) v
                 = hid_zcount v (items_syms (send_tree_items (fst p1) mcL))
                   + hid_zcount v (items_syms (send_tree_items (fst p2) mcD))).
  { intros v Hv.
    unfold s2'. rewrite set_tree_same.
    rewrite (Cnt2 v). rewrite Ebl1. rewrite (Cnt1 v). rewrite (Ebl0 v Hv).
    ring. }
  (* --- the BL build --- *)
  assert (HelB : 3 <= sd_elems TK_BL <= 286)
    by (change (sd_elems TK_BL) with 19; lia).
  assert (HMB : 1 <= sd_max_length TK_BL <= 15)
    by (change (sd_max_length TK_BL) with 7; lia).
  assert (HKB : 4 * (sd_elems TK_BL - 1) < 2 ^ sd_max_length TK_BL)
    by (change (sd_elems TK_BL) with 19;
        change (2 ^ sd_max_length TK_BL) with 128; lia).
  assert (HblS2 : forall b, b < 0 \/ 15 < b -> ts_blcount s2' b = 0).
  { intros b Hb. unfold s2'. rewrite !g6_bc_settree.
    unfold s1'. rewrite !g6_bc_settree. apply HblD. exact Hb. }
  assert (HhidL : forall v,
            0 <= hid_zcount v (items_syms (send_tree_items (fst p1) mcL))
            <= 867).
  { intro v. split; [apply hid_nonneg|].
    eapply Z.le_trans; [apply hid_le_length|].
    rewrite items_syms_length.
    pose proof (send_tree_items_count (fst p1) mcL). lia. }
  assert (HhidD : forall v,
            0 <= hid_zcount v (items_syms (send_tree_items (fst p2) mcD))
            <= 867).
  { intro v. split; [apply hid_nonneg|].
    eapply Z.le_trans; [apply hid_le_length|].
    rewrite items_syms_length.
    pose proof (send_tree_items_count (fst p2) mcD). lia. }
  assert (HfrB : forall i, 0 <= i < sd_elems TK_BL ->
                 0 <= t_freq (ts_trees s2' TK_BL) i <= 65535).
  { intros i Hi. change (sd_elems TK_BL) with 19 in Hi.
    rewrite (CntB i Hi).
    pose proof (HhidL i). pose proof (HhidD i). lia. }
  assert (HxbB : forall v, 0 <= v < sd_elems TK_BL ->
                 0 <= xbits (sd_extra_base TK_BL) (sd_extra TK_BL) v <= 16)
    by (intros v Hv; change (sd_elems TK_BL) with 19 in Hv;
        apply xbits_BL_range; exact Hv).
  assert (HstbB : forall st, sd_stree TK_BL = Some st ->
                  forall v, 0 <= v < sd_elems TK_BL -> 0 <= t_len st v <= 16).
  { intros st Est.
    change (sd_stree TK_BL) with (@None Tree) in Est.
    discriminate Est. }
  assert (EolS2 : ts_optlen s2' = ts_optlen BD').
  { unfold s2'. rewrite !g6_ol_settree.
    unfold s1'. rewrite !g6_ol_settree. reflexivity. }
  assert (EslS2 : ts_statlen s2' = ts_statlen BD').
  { unfold s2'. rewrite !g6_sl_settree.
    unfold s1'. rewrite !g6_sl_settree. reflexivity. }
  destruct (build_tree_counters TK_BL s2' HelB HMB HKB HblS2 HfrB HxbB HstbB
              ltac:(rewrite EolS2, EolD; symmetry; apply g6_u64_idem)
              ltac:(rewrite EslS2, EslD; symmetry; apply g6_u64_idem))
    as (BTCB & BTSB & EolB & EslB & HbBr & HbSBr & HdomB & _ & _).
  fold s3 in EolB, EslB, HdomB.
  change (sd_stree TK_BL) with (@None Tree) in EslB.
  cbv iota in EslB.
  destruct (build_tree_shape TK_BL s2' HelB HMB HKB HblS2)
    as (HmcBr & HlenB & _ & _).
  fold s3 in HmcBr, HlenB.
  (* --- mbi --- *)
  assert (Hmbi : 2 <= mbi <= 18).
  { unfold mbi.
    change (Z.to_nat BL_CODES + 1)%nat with 20%nat.
    change (BL_CODES - 1) with 18.
    destruct (bbl_scan_spec 20%nat (ts_trees s3 TK_BL) 18
                ltac:(change (Z.of_nat 20) with 20; lia)
                ltac:(lia)) as [Hr _].
    exact Hr. }
  (* --- the counter values --- *)
  set (OL := BTCL + BTCD + BTCB + 3 * (mbi + 1) + 5 + 5 + 4).
  set (SL := BTSL + BTSD).
  assert (EOL : ts_optlen (snd (build_bl_tree BD')) = OL).
  { rewrite EP. cbn [snd]. rewrite ol_optlen.
    rewrite EolB.
    replace (u64 (ts_optlen s2' + BTCB) + 3 * (mbi + 1) + 5 + 5 + 4)
      with (u64 (ts_optlen s2' + BTCB) + (3 * (mbi + 1) + 5 + 5 + 4))
      by ring.
    rewrite g6_u64_shift.
    rewrite EolS2, EolD.
    replace (u64 (ts_optlen BL' + BTCD) + BTCB + (3 * (mbi + 1) + 5 + 5 + 4))
      with (u64 (ts_optlen BL' + BTCD)
            + (BTCB + (3 * (mbi + 1) + 5 + 5 + 4))) by ring.
    rewrite g6_u64_shift.
    rewrite EolL, Hol0.
    replace (u64 (0 + BTCL) + BTCD + (BTCB + (3 * (mbi + 1) + 5 + 5 + 4)))
      with (u64 (0 + BTCL)
            + (BTCD + (BTCB + (3 * (mbi + 1) + 5 + 5 + 4)))) by ring.
    rewrite g6_u64_shift.
    replace (0 + BTCL + (BTCD + (BTCB + (3 * (mbi + 1) + 5 + 5 + 4))))
      with OL by (unfold OL; ring).
    unfold u64. apply Z.mod_small. unfold OL. lia. }
  assert (ESL : ts_statlen (snd (build_bl_tree BD')) = SL).
  { rewrite EP. cbn [snd]. rewrite g6_sl_setoptlen.
    rewrite EslB, EslS2, EslD, EslL, Hsl0.
    rewrite g6_u64_shift.
    replace (0 + BTSL + BTSD) with SL by (unfold SL; ring).
    unfold u64. apply Z.mod_small. unfold SL. lia. }
  (* --- the sums the arms emit, dominated --- *)
  assert (HcapL' : forall i, 0 <= i < 286 ->
                   t_freq (ts_trees ts TK_L) i <> 0 -> i <> mcL + 1).
  { intros i Hi Hnz Heq.
    assert (Hle : i <= ts_maxcode BL' TK_L).
    { apply HcapL; [change (sd_elems TK_L) with 286; lia | exact Hnz]. }
    rewrite <- EmcL0 in Hle. lia. }
  assert (HcapD' : forall i, 0 <= i < 30 ->
                   t_freq (ts_trees ts TK_D) i <> 0 -> i <> mcD + 1).
  { intros i Hi Hnz Heq.
    assert (Hle : i <= ts_maxcode BD' TK_D).
    { apply HcapD; [change (sd_elems TK_D) with 30; lia |].
      rewrite EfrD. exact Hnz. }
    rewrite <- EmcD0 in Hle. lia. }
  assert (HL1 : wsum (fun i => t_freq (ts_trees ts TK_L) i * cost_L (fst p1) i)
                  0 (Z.to_nat L_CODES)
                <= BTCL + 2).
  { rewrite (wsum_ext (fun i => t_freq (ts_trees ts TK_L) i * cost_L (fst p1) i)
               (fun i => t_freq (ts_trees ts TK_L) i
                         * (t_len (fst p1) i
                            + xbits (sd_extra_base TK_L) (sd_extra TK_L) i))
               0 (Z.to_nat L_CODES))
      by (intros i _; rewrite g6_costL_vocab; reflexivity).
    unfold p1.
    rewrite (g6_scan_len_bridge (t_freq (ts_trees ts TK_L)) tL mcL bl0
               (xbits (sd_extra_base TK_L) (sd_extra TK_L)) (Z.to_nat L_CODES)).
    2:{ intros i Hi Hnz.
        apply HcapL'; [|exact Hnz].
        change (Z.of_nat (Z.to_nat L_CODES)) with 286 in Hi. lia. }
    rewrite (wsum_ext (fun i => t_freq (ts_trees ts TK_L) i
                        * (t_len tL i
                           + xbits (sd_extra_base TK_L) (sd_extra TK_L) i))
               (fun i => t_freq (ts_trees ts TK_L) i
                         * (t_len (ts_trees BL' TK_L) i
                            + xbits (sd_extra_base TK_L) (sd_extra TK_L) i))
               0 (Z.to_nat L_CODES))
      by (intros i _; rewrite EtL; reflexivity).
    exact HdomL. }
  assert (HD1 : wsum (fun i => t_freq (ts_trees ts TK_D) i * cost_D (fst p2) i)
                  0 (Z.to_nat D_CODES)
                <= BTCD + 2).
  { rewrite (wsum_ext (fun i => t_freq (ts_trees ts TK_D) i * cost_D (fst p2) i)
               (fun i => t_freq (ts_trees ts TK_D) i
                         * (t_len (fst p2) i
                            + xbits (sd_extra_base TK_D) (sd_extra TK_D) i))
               0 (Z.to_nat D_CODES))
      by (intros i Hi; rewrite g6_costD_vocab by lia; reflexivity).
    unfold p2.
    rewrite (g6_scan_len_bridge (t_freq (ts_trees ts TK_D)) tD mcD bl1
               (xbits (sd_extra_base TK_D) (sd_extra TK_D)) (Z.to_nat D_CODES)).
    2:{ intros i Hi Hnz.
        apply HcapD'; [|exact Hnz].
        change (Z.of_nat (Z.to_nat D_CODES)) with 30 in Hi. lia. }
    rewrite (wsum_ext (fun i => t_freq (ts_trees ts TK_D) i
                        * (t_len tD i
                           + xbits (sd_extra_base TK_D) (sd_extra TK_D) i))
               (fun i => t_freq (ts_trees ts TK_D) i
                         * (t_len (ts_trees BD' TK_D) i
                            + xbits (sd_extra_base TK_D) (sd_extra TK_D) i))
               0 (Z.to_nat D_CODES))
      by (intros i _; rewrite EtD; reflexivity).
    exact HdomD. }
  assert (HB1 : wsum (fun sy =>
                    hid_zcount sy (items_syms (send_tree_items (fst p1) mcL))
                    * (t_len (ts_trees s3 TK_BL) sy + extra_blbits sy)) 0 19
                + wsum (fun sy =>
                    hid_zcount sy (items_syms (send_tree_items (fst p2) mcD))
                    * (t_len (ts_trees s3 TK_BL) sy + extra_blbits sy)) 0 19
                <= BTCB + 2).
  { rewrite <- wsum_plus.
    rewrite (wsum_ext (fun sy =>
               hid_zcount sy (items_syms (send_tree_items (fst p1) mcL))
               * (t_len (ts_trees s3 TK_BL) sy + extra_blbits sy)
               + hid_zcount sy (items_syms (send_tree_items (fst p2) mcD))
                 * (t_len (ts_trees s3 TK_BL) sy + extra_blbits sy))
               (fun sy => t_freq (ts_trees s2' TK_BL) sy
                          * (t_len (ts_trees s3 TK_BL) sy
                             + xbits (sd_extra_base TK_BL) (sd_extra TK_BL) sy))
               0 19).
    2:{ intros sy Hsy.
        rewrite (CntB sy ltac:(lia)).
        rewrite <- (g6_costBL_vocab (ts_trees s3 TK_BL) sy) by lia.
        ring. }
    exact HdomB. }
  (* --- static side --- *)
  assert (HSL1 : wsum (fun i => t_freq (ts_trees ts TK_L) i
                          * cost_L static_ltree i) 0 (Z.to_nat L_CODES)
                 <= BTSL).
  { rewrite (wsum_ext (fun i => t_freq (ts_trees ts TK_L) i
                         * cost_L static_ltree i)
               (fun i => t_freq (ts_trees ts TK_L) i
                         * (t_len static_ltree i
                            + xbits (sd_extra_base TK_L) (sd_extra TK_L) i))
               0 (Z.to_nat L_CODES))
      by (intros i _; rewrite g6_costL_vocab; reflexivity).
    exact HdomSL. }
  assert (HSD1 : wsum (fun i => t_freq (ts_trees ts TK_D) i
                          * cost_D static_dtree i) 0 (Z.to_nat D_CODES)
                 <= BTSD).
  { rewrite (wsum_ext (fun i => t_freq (ts_trees ts TK_D) i
                         * cost_D static_dtree i)
               (fun i => t_freq (ts_trees ts TK_D) i
                         * (t_len static_dtree i
                            + xbits (sd_extra_base TK_D) (sd_extra TK_D) i))
               0 (Z.to_nat D_CODES))
      by (intros i Hi; rewrite g6_costD_vocab by lia; reflexivity).
    exact HdomSD. }
  (* --- assemble --- *)
  exists OL, SL.
  split; [exact EOL|].
  split; [exact ESL|].
  split; [unfold OL; lia|].
  split; [unfold SL; lia|].
  split; [rewrite EP; cbn [fst]; exact Hmbi|].
  split; [rewrite EmcLf; exact HmcL285|].
  split; [rewrite EmcDf; exact HmcD285|].
  split.
  { rewrite EtrL, EmcLf. unfold p1. apply scan_tree_guard. }
  split.
  { rewrite EtrD, EmcDf. unfold p2. apply scan_tree_guard. }
  split.
  { intros i Hi. rewrite EmcLf in Hi. rewrite EtrL.
    unfold p1. rewrite scan_tree_len_other by lia.
    apply HlentL. exact Hi. }
  split.
  { intros i Hi. rewrite EmcDf in Hi. rewrite EtrD.
    unfold p2. rewrite scan_tree_len_other by lia.
    apply HlentD. exact Hi. }
  split.
  { intro i. rewrite EtrL.
    destruct (Z.eq_dec i (mcL + 1)) as [->|Ne].
    - unfold p1. rewrite scan_tree_guard. lia.
    - unfold p1. rewrite scan_tree_len_other by exact Ne.
      rewrite EtL. unfold BL'. apply build_tree_len_nonneg. exact HnnL. }
  split.
  { intro i. rewrite EtrD.
    destruct (Z.eq_dec i (mcD + 1)) as [->|Ne].
    - unfold p2. rewrite scan_tree_guard. lia.
    - unfold p2. rewrite scan_tree_len_other by exact Ne.
      rewrite EtD. unfold BD'.
      apply build_tree_len_nonneg.
      rewrite EfrD. exact HnnD. }
  split.
  { intros sy Hsy. rewrite EtrB.
    assert (Hsy' : 0 <= sy < sd_elems TK_BL)
      by (change (sd_elems TK_BL) with 19; lia).
    pose proof (HlenB sy Hsy').
    change (sd_max_length TK_BL) with 7 in *. lia. }
  split.
  { (* per-token widths at the (guarded) dispatch trees *)
    rewrite EtrL, EtrD.
    rewrite Forall_forall. intros t Hin.
    assert (Ht : tok_enc t)
      by (unfold cEnc in Henc; rewrite Forall_forall in Henc;
          exact (Henc t Hin)).
    destruct t as [b | len dist]; cbn [tok_widths_ok] in *.
    - destruct Ht as [Hb0 Hb1].
      assert (Hfnz : t_freq (ts_trees ts TK_L) b <> 0).
      { rewrite (HFL b) by (unfold L_CODES; lia).
        pose proof (count_L_in_lit toks b Hin).
        destruct (Z.eqb b END_BLOCK); lia. }
      assert (Hble : b <= mcL)
        by (rewrite EmcL0; apply HcapL;
            [change (sd_elems TK_L) with 286; lia | exact Hfnz]).
      unfold p1. rewrite scan_tree_len_other by lia.
      rewrite EtL.
      pose proof (HlenL b ltac:(change (sd_elems TK_L) with 286; lia)).
      change (sd_max_length TK_L) with 15 in *. lia.
    - destruct Ht as [[Hl0 Hl1] [Hd0 Hd1]].
      unfold MIN_MATCH in Hl0. unfold MAX_MATCH in Hl1.
      destruct (lcode_range (len - 3) ltac:(lia)) as [Hc _].
      destruct (DcodeRange_all (dist - 1) ltac:(lia)) as [Hdc _].
      split.
      + assert (Hfnz : t_freq (ts_trees ts TK_L)
                         (length_code (len - 3) + LITERALS + 1) <> 0).
        { rewrite (HFL (length_code (len - 3) + LITERALS + 1))
            by (unfold L_CODES, LITERALS in *; lia).
          pose proof (count_L_in_match toks len dist Hin).
          destruct (Z.eqb (length_code (len - 3) + LITERALS + 1) END_BLOCK);
            lia. }
        assert (Hble : length_code (len - 3) + LITERALS + 1 <= mcL)
          by (rewrite EmcL0; apply HcapL;
              [change (sd_elems TK_L) with 286; unfold LITERALS in *; lia
              | exact Hfnz]).
        unfold p1. rewrite scan_tree_len_other by lia.
        rewrite EtL.
        pose proof (HlenL (length_code (len - 3) + LITERALS + 1)
                      ltac:(change (sd_elems TK_L) with 286;
                            unfold LITERALS in *; lia)).
        change (sd_max_length TK_L) with 15 in *. lia.
      + assert (Hfnz : t_freq (ts_trees ts TK_D) (d_code (dist - 1)) <> 0).
        { rewrite (HFD (d_code (dist - 1))) by (unfold D_CODES; lia).
          pose proof (count_D_in_match toks len dist Hin). lia. }
        assert (Hble : d_code (dist - 1) <= mcD).
        { rewrite EmcD0. apply HcapD;
            [change (sd_elems TK_D) with 30; lia|].
          rewrite EfrD. exact Hfnz. }
        unfold p2. rewrite scan_tree_len_other by lia.
        rewrite EtD.
        pose proof (HlenD (d_code (dist - 1))
                      ltac:(change (sd_elems TK_D) with 30; lia)).
        change (sd_max_length TK_D) with 15 in *. lia. }
  split.
  { (* the EOB width *)
    rewrite EtrL.
    assert (Hfnz : t_freq (ts_trees ts TK_L) 256 <> 0).
    { rewrite (HFL 256) by (unfold L_CODES; lia).
      replace (Z.eqb 256 END_BLOCK) with true by reflexivity.
      pose proof (count_L_nonneg 256 toks). lia. }
    assert (Hble : 256 <= mcL)
      by (rewrite EmcL0; apply HcapL;
          [change (sd_elems TK_L) with 286; lia | exact Hfnz]).
    unfold END_BLOCK.
    unfold p1. rewrite scan_tree_len_other by lia.
    rewrite EtL.
    pose proof (HlenL 256 ltac:(change (sd_elems TK_L) with 286; lia)).
    change (sd_max_length TK_L) with 15 in *. lia. }
  split.
  { (* the dynamic arm *)
    rewrite EtrL, EtrD, EtrB, EmcLf, EmcDf.
    rewrite EP. cbn [fst].
    rewrite (toks_cost_regroup (fst p1) (fst p2) toks Henc).
    assert (EL : wsum (fun i => count_L i toks * cost_L (fst p1) i)
                   0 (Z.to_nat L_CODES)
                 + t_len (fst p1) END_BLOCK
                 = wsum (fun i => t_freq (ts_trees ts TK_L) i
                           * cost_L (fst p1) i) 0 (Z.to_nat L_CODES)).
    { rewrite (g6_countL_to_freq ts toks (cost_L (fst p1)) HFL).
      replace (cost_L (fst p1) 256) with (t_len (fst p1) END_BLOCK).
      2:{ unfold cost_L.
          replace (Z.leb (LITERALS + 1) 256) with false by reflexivity.
          unfold END_BLOCK. ring. }
      ring. }
    rewrite (g6_countD_to_freq ts toks (cost_D (fst p2)) HFD) in *.
    lia. }
  split.
  { (* the static arm *)
    rewrite (toks_cost_regroup static_ltree static_dtree toks Henc).
    assert (ELs : wsum (fun i => count_L i toks * cost_L static_ltree i)
                    0 (Z.to_nat L_CODES)
                  + t_len static_ltree END_BLOCK
                  = wsum (fun i => t_freq (ts_trees ts TK_L) i
                            * cost_L static_ltree i) 0 (Z.to_nat L_CODES)).
    { rewrite (g6_countL_to_freq ts toks (cost_L static_ltree) HFL).
      replace (cost_L static_ltree 256) with (t_len static_ltree END_BLOCK).
      2:{ unfold cost_L.
          replace (Z.leb (LITERALS + 1) 256) with false by reflexivity.
          unfold END_BLOCK. ring. }
      ring. }
    rewrite (g6_countD_to_freq ts toks (cost_D static_dtree) HFD) in *.
    lia. }
  { (* the static-counter upper: SL never exceeds the true static cost
       by more than the two builds' manufactured-slot slack *)
    rewrite (toks_cost_regroup static_ltree static_dtree toks Henc).
    assert (ELs : wsum (fun i => count_L i toks * cost_L static_ltree i)
                    0 (Z.to_nat L_CODES)
                  + t_len static_ltree END_BLOCK
                  = wsum (fun i => t_freq (ts_trees ts TK_L) i
                            * cost_L static_ltree i) 0 (Z.to_nat L_CODES)).
    { rewrite (g6_countL_to_freq ts toks (cost_L static_ltree) HFL).
      replace (cost_L static_ltree 256) with (t_len static_ltree END_BLOCK).
      2:{ unfold cost_L.
          replace (Z.leb (LITERALS + 1) 256) with false by reflexivity.
          unfold END_BLOCK. ring. }
      ring. }
    assert (HSL1u : BTSL <= wsum (fun i => t_freq (ts_trees ts TK_L) i
                              * cost_L static_ltree i)
                              0 (Z.to_nat L_CODES) + 32).
    { rewrite (wsum_ext (fun i => t_freq (ts_trees ts TK_L) i
                           * cost_L static_ltree i)
                 (fun i => t_freq (ts_trees ts TK_L) i
                           * (t_len static_ltree i
                              + xbits (sd_extra_base TK_L) (sd_extra TK_L) i))
                 0 (Z.to_nat L_CODES))
        by (intros i _; rewrite g6_costL_vocab; reflexivity).
      exact HupSL. }
    assert (HSD1u : BTSD <= wsum (fun i => t_freq (ts_trees ts TK_D) i
                              * cost_D static_dtree i)
                              0 (Z.to_nat D_CODES) + 32).
    { rewrite (wsum_ext (fun i => t_freq (ts_trees ts TK_D) i
                           * cost_D static_dtree i)
                 (fun i => t_freq (ts_trees ts TK_D) i
                           * (t_len static_dtree i
                              + xbits (sd_extra_base TK_D) (sd_extra TK_D) i))
                 0 (Z.to_nat D_CODES))
        by (intros i Hi; rewrite g6_costD_vocab by lia; reflexivity).
      exact HupSD. }
    rewrite (g6_countD_to_freq ts toks (cost_D static_dtree) HFD) in *.
    unfold SL. lia. }
Qed.

Set Printing All.
Set Printing Fully Qualified.
Set Printing Depth 10000000000.
Set Printing Width 2000.
Print Assumptions build_tree_shape.
Print Assumptions dispatch_counters.
Unset Printing All.


Set Printing All.
Set Printing Fully Qualified.
Set Printing Depth 10000000000.
Set Printing Width 2000.
Print Assumptions build_tree_shape.
Print Assumptions send_tree_items_count.
Print Assumptions static_ltree_len_range.
Unset Printing All.
