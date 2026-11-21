(** * ZReproG6F — G6 bound-fit, part F: per-build counter domination.

    OWNER: g6-bound (zlib z-repro campaign, 2026-08-19/20).

    [build_tree_counters]: one [build_tree k] call turns the entry
    counters into [u64 (entry + BTC)] / [u64 (entry + BTS)] for plain-Z
    values BTC/BTS such that

      * the TALLIED opt sum  (entry freqs x final code lens + extras)
        is at most [BTC + 2]  — the force loop's opt decrements are
        repaid only up to its manufactured slots' unknown lengths, and
        2 bits of slack is what part G's amortized budget absorbs;
      * the TALLIED static sum is at most [BTS] EXACTLY — each
        manufactured slot's own window term repays its static delta;
      * both sit inside [[-2, 2^36]], so the u64 wrap never fires on
        the composed dispatch-site counters.

    Route: BtAccount2's [build_tree_account] (window sums, u64-mod) +
    ZReproG6E's [bt_force2_full] (manufactured slots, exact deltas) +
    [wsum_by_value] over [BtParked.bp_cnt] (each live leaf parks exactly
    once; internals sit above [maxc1] where the guard vanishes).

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Chunk ZBitsOut BwStream Trees BtWin BtCensus1 BtCensus2
  BtCensus3 BtCensus4 BtCensus5 BtAccount BtAccount2 BtItem6b BtExports
  BtSized BtTerm.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import ZReproL0 ZReproG6A
  ZReproG6C ZReproG6E.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ==========================================================================
   1.  Small algebra.
   ========================================================================== *)

Lemma g6_u64_idem : forall x, u64 (u64 x) = u64 x.
Proof. intro x. unfold u64. apply Z.mod_mod. lia. Qed.

Lemma g6_u64_shift : forall a b, u64 (u64 a + b) = u64 (a + b).
Proof. intros a b. unfold u64. apply Zplus_mod_idemp_l. Qed.

Lemma live_total_le : forall t maxc elems,
  0 <= elems -> live_total t maxc elems <= elems.
Proof.
  intros t maxc elems He. unfold live_total.
  pose proof (wsum_le (fun s => ind (live_b t maxc s)) (fun _ => 1)
                0 (Z.to_nat elems)
                ltac:(intros i _; apply ind_0_1)) as H.
  rewrite g6_wsum_const in H.
  rewrite Z2Nat.id in H by lia. lia.
Qed.

(* ==========================================================================
   2.  The window kit: what one parked window gives a value-sum.
   ========================================================================== *)

Section WindowKit.

Variable elems maxc1 : Z.
Variable t1 tf : Tree.
Variable hp3 : zarr.
Variable hmax ndf : Z.
Variable C : Z -> Z.

Hypothesis Hpk : BtParked elems maxc1 t1 tf hp3 hmax ndf.
Hypothesis Hel : 3 <= elems <= 286.
Hypothesis Hnd : ndf - elems <= 285.
Hypothesis Hfr1nn : forall v, 0 <= v < elems -> 0 <= t_freq t1 v <= 65535.
Hypothesis HC : forall v, 0 <= v < elems -> 0 <= C v <= 32.

(** The window function, as a function of the parked VALUE. *)
Definition wF (v : Z) : Z :=
  ind (v <=? maxc1) * (t_freq tf v * C v).

Definition NW : nat := Z.to_nat (HEAP_SIZE - (hmax + 1)).

Definition wcw (v : Z) : Z := wcount hp3 (hmax + 1) NW v.

Lemma kit_hmax : 2 <= hmax /\ hmax + 1 < HEAP_SIZE /\ ndf < HEAP_SIZE.
Proof.
  pose proof (bp_hmax _ _ _ _ _ _ _ Hpk) as Hh.
  pose proof (bp_ndf _ _ _ _ _ _ _ Hpk) as Hn.
  unfold HEAP_SIZE in *. lia.
Qed.

Lemma kit_mc : -1 <= maxc1 < elems.
Proof. exact (bp_maxc _ _ _ _ _ _ _ Hpk). Qed.

(** Every window value is a node index below HEAP_SIZE. *)
Lemma kit_range : forall p,
  hmax + 1 <= p < hmax + 1 + Z.of_nat NW -> 0 <= hp3 p < HEAP_SIZE.
Proof.
  intros p Hp.
  destruct kit_hmax as (Hh2 & Hh1 & HndH).
  assert (HpH : hmax <= p < HEAP_SIZE)
    by (unfold NW in Hp; rewrite Z2Nat.id in Hp by lia; lia).
  pose proof (pcount_member hp3 hmax p HpH) as Hm.
  pose proof (bp_cnt _ _ _ _ _ _ _ Hpk (hp3 p)) as Hc.
  pose proof (kit_mc) as Hmc.
  assert (HHS : HEAP_SIZE = 573) by reflexivity.
  unfold live_b in Hc.
  destruct (Z.leb_spec 0 (hp3 p)) as [H0|H0];
    destruct (Z.leb_spec (hp3 p) maxc1) as [H1|H1];
    destruct (Z.leb_spec elems (hp3 p)) as [H2|H2];
    destruct (Z.ltb_spec (hp3 p) ndf) as [H3|H3];
    cbn [andb negb ind] in Hc; try lia;
    destruct (Z.eqb (t_freq t1 (hp3 p)) 0); cbn [negb ind] in Hc; lia.
Qed.

(** The whole window sum, exchanged to a value sum; the tail above
    [elems] vanishes (internals fail the [maxc1] guard). *)
Lemma kit_exchange :
  wsum (fun p => wF (hp3 p)) (hmax + 1) NW
  = wsum (fun v => wcw v * wF v) 0 (Z.to_nat elems).
Proof.
  destruct kit_hmax as (Hh2 & Hh1 & HndH).
  pose proof kit_mc as Hmc.
  rewrite (wsum_by_value NW hp3 wF (hmax + 1) HEAP_SIZE
             ltac:(unfold HEAP_SIZE; lia) kit_range).
  replace (Z.to_nat HEAP_SIZE)
    with (Z.to_nat elems + Z.to_nat (HEAP_SIZE - elems))%nat
    by (unfold HEAP_SIZE in *; lia).
  rewrite g6_wsum_split.
  rewrite (g6_wsum_zero
             (fun v => wcount hp3 (hmax + 1) NW v * wF v)
             (0 + Z.of_nat (Z.to_nat elems)) (Z.to_nat (HEAP_SIZE - elems))).
  - unfold wcw. ring.
  - intros v Hv.
    rewrite Z2Nat.id in Hv by lia.
    unfold wF.
    replace (v <=? maxc1) with false
      by (symmetry; apply Z.leb_gt; lia).
    cbn [ind]. ring.
Qed.

(** A live leaf parks exactly once, at a window position (never the root
    slot), and its window term is its own frequency-weighted cost. *)
Lemma kit_live : forall v,
  0 <= v < elems -> v <= maxc1 -> t_freq t1 v <> 0 ->
  wcw v = 1 /\ wF v = t_freq t1 v * C v.
Proof.
  intros v Hv Hvm Hf.
  destruct kit_hmax as (Hh2 & Hh1 & HndH).
  pose proof (bp_cnt _ _ _ _ _ _ _ Hpk v) as Hc.
  pose proof (bp_root _ _ _ _ _ _ _ Hpk) as Hroot.
  pose proof (bp_ndf _ _ _ _ _ _ _ Hpk) as Hn.
  assert (Hlive : live_b t1 maxc1 v = true)
    by (apply live_b_true; [lia | exact Hf]).
  rewrite Hlive in Hc.
  replace ((elems <=? v) && (v <? ndf)) with false in Hc
    by (symmetry; apply andb_false_iff; left; apply Z.leb_gt; lia).
  cbn [ind] in Hc.
  (* pcount over [hmax, HS) = the root slot + the window *)
  unfold pcount in Hc.
  replace (Z.to_nat (HEAP_SIZE - hmax)) with (S NW) in Hc
    by (unfold NW; lia).
  unfold wcount in Hc.
  rewrite (wsum_split_first (fun i => ind (Z.eqb (hp3 i) v)) hmax NW) in Hc.
  rewrite Hroot in Hc.
  replace (ndf - 1 =? v) with false in Hc
    by (symmetry; apply Z.eqb_neq; lia).
  cbn [ind] in Hc.
  replace (hmax + 1) with (hmax + 1) in Hc by lia.
  split.
  - unfold wcw, wcount. lia.
  - unfold wF.
    replace (v <=? maxc1) with true
      by (symmetry; apply Z.leb_le; lia).
    cbn [ind].
    rewrite (bp_frq _ _ _ _ _ _ _ Hpk v) by lia.
    ring.
Qed.

Lemma kit_term_nonneg : forall v,
  0 <= v < elems -> 0 <= wcw v * wF v.
Proof.
  intros v Hv.
  pose proof kit_mc as Hmc.
  assert (Hw : 0 <= wcw v) by (unfold wcw; apply wcount_nonneg).
  assert (HF : 0 <= wF v).
  { unfold wF.
    destruct (Z.leb_spec v maxc1) as [H1|H1]; cbn [ind]; [|lia].
    rewrite (bp_frq _ _ _ _ _ _ _ Hpk v) by lia.
    pose proof (Hfr1nn v Hv). pose proof (HC v Hv).
    apply Z.mul_nonneg_nonneg; [lia|].
    apply Z.mul_nonneg_nonneg; lia. }
  apply Z.mul_nonneg_nonneg; lia.
Qed.

(** The reverse exchange: the window sum never exceeds the plain
    [t1]-frequency-weighted cost sum.  Dead values contribute nothing
    ([wF] vanishes at frequency 0 and above [maxc1]); live in-code
    values park exactly once and contribute their own term. *)
Lemma kit_upper :
  wsum (fun p => wF (hp3 p)) (hmax + 1) NW
  <= wsum (fun v => t_freq t1 v * C v) 0 (Z.to_nat elems).
Proof.
  pose proof kit_mc as Hmc.
  rewrite kit_exchange.
  apply wsum_le. intros v Hv.
  rewrite Z2Nat.id in Hv by lia.
  assert (Hv' : 0 <= v < elems) by lia.
  pose proof (Hfr1nn v Hv') as Hf. pose proof (HC v Hv') as Hc.
  destruct (Z.leb_spec v maxc1) as [Hle|Hgt].
  - destruct (Z.eq_dec (t_freq t1 v) 0) as [Ez|Enz].
    + assert (EF : wF v = 0).
      { unfold wF.
        replace (v <=? maxc1) with true
          by (symmetry; apply Z.leb_le; lia).
        cbn [ind].
        rewrite (bp_frq _ _ _ _ _ _ _ Hpk v) by lia.
        rewrite Ez. ring. }
      rewrite EF, Ez.
      replace (wcw v * 0) with 0 by ring.
      replace (0 * C v) with 0 by ring.
      lia.
    + destruct (kit_live v Hv' Hle Enz) as [Ew EF].
      rewrite Ew, EF. lia.
  - assert (EF : wF v = 0).
    { unfold wF.
      replace (v <=? maxc1) with false
        by (symmetry; apply Z.leb_gt; lia).
      cbn [ind]. ring. }
    rewrite EF.
    replace (wcw v * 0) with 0 by ring.
    apply Z.mul_nonneg_nonneg; lia.
Qed.

(** The window sum's crude size bound. *)
Lemma kit_bound :
  0 <= wsum (fun p => wF (hp3 p)) (hmax + 1) NW <= 68719476736.
Proof.
  destruct kit_hmax as (Hh2 & Hh1 & HndH).
  pose proof kit_mc as Hmc.
  assert (Hterm : forall p, hmax + 1 <= p < hmax + 1 + Z.of_nat NW ->
                  0 <= wF (hp3 p) <= 2097120).
  { intros p Hp.
    pose proof (kit_range p Hp) as Hr.
    unfold wF.
    destruct (Z.leb_spec (hp3 p) maxc1) as [H1|H1]; cbn [ind].
    - assert (Hin : 0 <= hp3 p < elems) by lia.
      rewrite (bp_frq _ _ _ _ _ _ _ Hpk (hp3 p)) by lia.
      pose proof (Hfr1nn (hp3 p) Hin).
      pose proof (HC (hp3 p) Hin).
      split; nia.
    - lia. }
  split.
  - apply wsum_nonneg. intros p Hp. apply (Hterm p Hp).
  - pose proof (wsum_le (fun p => wF (hp3 p)) (fun _ => 2097120)
                  (hmax + 1) NW
                  ltac:(intros p Hp; apply (Hterm p Hp))) as H.
    rewrite g6_wsum_const in H.
    assert (HNW : Z.of_nat NW <= 573)
      by (unfold NW, HEAP_SIZE in *; lia).
    assert (0 <= Z.of_nat NW) by lia.
    nia.
Qed.

End WindowKit.

(* ==========================================================================
   3.  The per-build wrapper.
   ========================================================================== *)

Theorem build_tree_counters : forall k s,
  3 <= sd_elems k <= 286 ->
  1 <= sd_max_length k <= 15 ->
  4 * (sd_elems k - 1) < 2 ^ sd_max_length k ->
  (forall b, b < 0 \/ 15 < b -> ts_blcount s b = 0) ->
  (forall i, 0 <= i < sd_elems k -> 0 <= t_freq (ts_trees s k) i <= 65535) ->
  (forall v, 0 <= v < sd_elems k ->
     0 <= xbits (sd_extra_base k) (sd_extra k) v <= 16) ->
  (forall st, sd_stree k = Some st ->
     forall v, 0 <= v < sd_elems k -> 0 <= t_len st v <= 16) ->
  ts_optlen s = u64 (ts_optlen s) ->
  ts_statlen s = u64 (ts_statlen s) ->
  exists BTC BTS,
    ts_optlen (build_tree k s) = u64 (ts_optlen s + BTC)
    /\ ts_statlen (build_tree k s)
       = match sd_stree k with
         | None => ts_statlen s
         | Some _ => u64 (ts_statlen s + BTS)
         end
    /\ -2 <= BTC <= 68719476736
    /\ 0 <= BTS <= 68719476736
    /\ wsum (fun v => t_freq (ts_trees s k) v
               * (t_len (ts_trees (build_tree k s) k) v
                  + xbits (sd_extra_base k) (sd_extra k) v))
         0 (Z.to_nat (sd_elems k))
       <= BTC + 2
    /\ (forall st, sd_stree k = Some st ->
        wsum (fun v => t_freq (ts_trees s k) v
                * (t_len st v + xbits (sd_extra_base k) (sd_extra k) v))
          0 (Z.to_nat (sd_elems k))
        <= BTS)
    /\ (forall st, sd_stree k = Some st ->
        BTS
        <= wsum (fun v => t_freq (ts_trees s k) v
                  * (t_len st v + xbits (sd_extra_base k) (sd_extra k) v))
             0 (Z.to_nat (sd_elems k)) + 32).
Proof.
  intros k s Hel HM HK4 Hbl0 Hfr Hxb Hstb Hido Hids.
  assert (HLC : L_CODES = 286) by reflexivity.
  set (frq := t_freq (ts_trees s k)) in *.
  (* open the three internal calls *)
  destruct (bt_init (Z.to_nat L_CODES + 2) 0 (sd_elems k) (ts_trees s k)
              (ts_heap s) (ts_depth s) 0 (-1))
    as [[[[t0 hp0] dep0] hlen0] maxc0] eqn:E0.
  destruct (bt_init_census_call (Z.to_nat L_CODES + 2) (sd_elems k)
              (ts_trees s k) (ts_heap s) (ts_depth s) t0 hp0 dep0 hlen0 maxc0
              E0
              ltac:(change (Z.of_nat (Z.to_nat L_CODES + 2)) with 288; lia)
              ltac:(lia)) as [Hout0 Hfr0].
  fold frq in Hfr0.
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
  fold frq in Hfrt0.
  assert (Hh1e : hlen1 <= sd_elems k).
  { rewrite (io_total _ _ _ _ _ Hout1). apply live_total_le. lia. }
  assert (HK : 4 * (hlen1 - 1) < 2 ^ sd_max_length k) by lia.
  destruct (bt_force2_full (sd_stree k) (sd_elems k) t0 hp0 dep0 hlen0 maxc0
              (ts_optlen s) (ts_statlen s) t1 hp1 dep1 hlen1 maxc1 ol1 sl1
              E2 ltac:(lia) Hout0) as [Hmcmono Hcases].
  assert (Hol_sl : ol1 = u64 ol1 /\ sl1 = u64 sl1).
  { destruct Hcases as
      [(_ & _ & _ & Ho & Hs2)
      |[(v1 & _ & _ & _ & _ & _ & Ho & Hs2)
       |(_ & _ & _ & _ & _ & Ho & Hs2)]].
    - rewrite Ho, Hs2. split; [exact Hido | exact Hids].
    - split.
      + rewrite Ho. symmetry. apply g6_u64_idem.
      + rewrite Hs2. destruct (sd_stree k);
          [symmetry; apply g6_u64_idem | exact Hids].
    - split.
      + rewrite Ho. symmetry. apply g6_u64_idem.
      + rewrite Hs2. destruct (sd_stree k);
          [symmetry; apply g6_u64_idem | exact Hids]. }
  destruct Hol_sl as [Holu Hslu].
  destruct (build_tree_account k s t0 hp0 dep0 hlen0 maxc0 t1 hp1 dep1 hlen1
              maxc1 ol1 sl1 stf ltac:(lia) HM HK Hbl0 Holu Hslu E0 E2 Eloop)
    as [Gol Gsl].
  destruct (BtItem6b.build_tree_out k s t0 hp0 dep0 hlen0 maxc0 t1 hp1 dep1
              hlen1 maxc1 ol1 sl1 stf ltac:(lia) HM HK Hbl0 E0 E2 Eloop)
    as (_ & _ & _ & _ & _ & _ & Hlen7).
  set (TFIN := ts_trees (build_tree k s) k) in *.
  set (hp3 := zset (b_heap stf) (b_hmax stf - 1) (b_heap stf 1)) in *.
  set (hmax := b_hmax stf - 1) in *.
  set (ndf := b_node stf) in *.
  assert (Hnd : ndf - sd_elems k <= 285) by lia.
  pose proof (bp_maxc _ _ _ _ _ _ _ Hpk) as Hbmc.
  (* the case-independent frequency facts *)
  assert (Hfr1 : forall v, 0 <= v < sd_elems k -> 0 <= t_freq t1 v <= 65535).
  { intros v Hv.
    destruct Hcases as
      [(_ & Et1 & _)
      |[(v1 & _ & Et1 & _ & _ & _ & _ & _)
       |(_ & Et1 & _)]]; rewrite Et1.
    - rewrite Hfrt0. apply Hfr. exact Hv.
    - destruct (Z.eq_dec v v1) as [->|Hne].
      + rewrite g6_t_freq_setfreq_same.
        change (u16 1) with 1. lia.
      + rewrite g6_t_freq_setfreq_other by exact Hne.
        rewrite Hfrt0. apply Hfr. exact Hv.
    - destruct (Z.eq_dec v 1) as [->|Hne1].
      + rewrite g6_t_freq_setfreq_same.
        change (u16 1) with 1. lia.
      + rewrite g6_t_freq_setfreq_other by exact Hne1.
        destruct (Z.eq_dec v 0) as [->|Hne0].
        * rewrite g6_t_freq_setfreq_same.
          change (u16 1) with 1. lia.
        * rewrite g6_t_freq_setfreq_other by exact Hne0.
          rewrite Hfrt0. apply Hfr. exact Hv. }
  assert (Hcap : forall v, 0 <= v < sd_elems k -> frq v <> 0 -> v <= maxc1).
  { intros v Hv Hnz.
    destruct (Z.le_gt_cases v maxc0) as [Hle|Hgt]; [lia|].
    exfalso. apply Hnz.
    rewrite <- (Hfr0 v).
    apply (io_gapz _ _ _ _ _ Hout0). lia. }
  assert (Hfr1eq : forall v, 0 <= v < sd_elems k -> frq v <> 0 ->
                   t_freq t1 v = frq v).
  { intros v Hv Hnz.
    destruct Hcases as
      [(_ & Et1 & _)
      |[(v1 & _ & Et1 & Ef0 & _ & _ & _ & _)
       |(_ & Et1 & Ef00 & Ef01 & _)]]; rewrite Et1.
    - apply Hfrt0.
    - destruct (Z.eq_dec v v1) as [->|Hne].
      + exfalso. apply Hnz. rewrite <- (Hfrt0 v1). exact Ef0.
      + rewrite g6_t_freq_setfreq_other by exact Hne. apply Hfrt0.
    - assert (Hne0 : v <> 0)
        by (intros ->; apply Hnz; rewrite <- (Hfrt0 0); exact Ef00).
      assert (Hne1 : v <> 1)
        by (intros ->; apply Hnz; rewrite <- (Hfrt0 1); exact Ef01).
      rewrite g6_t_freq_setfreq_other by exact Hne1.
      rewrite g6_t_freq_setfreq_other by exact Hne0.
      apply Hfrt0. }
  (* the opt-side cost function *)
  set (Cop := fun v => t_len TFIN v + xbits (sd_extra_base k) (sd_extra k) v)
    in *.
  assert (HCop : forall v, 0 <= v < sd_elems k -> 0 <= Cop v <= 32).
  { intros v Hv. unfold Cop.
    pose proof (Hlen7 v Hv). pose proof (Hxb v Hv). lia. }
  (* the opt window sum, tied to the kit's spelling *)
  set (WSo := wsum (olterm maxc1 t1 hp3 (sd_extra_base k) (sd_extra k) TFIN)
                (hmax + 1) (Z.to_nat (HEAP_SIZE - (hmax + 1)))) in *.
  assert (EWo : WSo = wsum (fun p => wF maxc1 (b_tree stf) Cop (hp3 p))
                        (hmax + 1) (NW hmax)).
  { unfold WSo, NW. apply wsum_ext. intros p _.
    unfold wF, olterm, Cop.
    destruct (Z.leb_spec (hp3 p) maxc1) as [Hle|Hgt]; cbn [ind].
    - rewrite (bp_frq _ _ _ _ _ _ _ Hpk (hp3 p)) by lia. reflexivity.
    - ring. }
  pose proof (kit_exchange (sd_elems k) maxc1 t1 (b_tree stf) hp3 hmax ndf Cop
                Hpk ltac:(lia) Hnd) as EXo.
  pose proof (kit_bound (sd_elems k) maxc1 t1 (b_tree stf) hp3 hmax ndf Cop
                Hpk ltac:(lia) Hnd Hfr1 HCop) as BDo.
  (* the shared domination scheme: any per-symbol lower bound that is
     pointwise below wcw*wF sums below the window *)
  assert (DOMSCHEME : forall (C : Z -> Z) (L : Z -> Z),
    (forall v, 0 <= v < sd_elems k -> 0 <= C v <= 32) ->
    (forall v, 0 <= v < sd_elems k -> L v <= wcw hp3 hmax v * wF maxc1 (b_tree stf) C v) ->
    wsum L 0 (Z.to_nat (sd_elems k))
    <= wsum (fun p => wF maxc1 (b_tree stf) C (hp3 p)) (hmax + 1) (NW hmax)).
  { intros C L HC HL.
    rewrite (kit_exchange (sd_elems k) maxc1 t1 (b_tree stf) hp3 hmax ndf C
               Hpk ltac:(lia) Hnd).
    apply wsum_le. intros v Hv.
    apply HL. rewrite Z2Nat.id in Hv by lia. lia. }
  (* the standard pointwise bound: tallied term is below the window term *)
  assert (PTW : forall (C : Z -> Z), (forall v, 0 <= v < sd_elems k -> 0 <= C v <= 32) ->
    forall v, 0 <= v < sd_elems k ->
    frq v * C v <= wcw hp3 hmax v * wF maxc1 (b_tree stf) C v).
  { intros C HC v Hv.
    destruct (Z.eq_dec (frq v) 0) as [Ez|Enz].
    - rewrite Ez.
      replace (0 * C v) with 0 by ring.
      apply (kit_term_nonneg (sd_elems k) maxc1 t1 (b_tree stf) hp3 hmax ndf C
               Hpk Hfr1 HC v Hv).
    - assert (Hvm : v <= maxc1) by (apply Hcap; assumption).
      destruct (kit_live (sd_elems k) maxc1 t1 (b_tree stf) hp3 hmax ndf C
                  Hpk ltac:(lia) Hnd v Hv Hvm
                  ltac:(rewrite (Hfr1eq v Hv Enz); exact Enz)) as [Ew EF].
      rewrite Ew, EF, (Hfr1eq v Hv Enz). lia. }
  assert (EOPT : wsum (fun v => frq v * (t_len TFIN v
                        + xbits (sd_extra_base k) (sd_extra k) v))
                   0 (Z.to_nat (sd_elems k))
                 = wsum (fun v => frq v * Cop v) 0 (Z.to_nat (sd_elems k))).
  { apply wsum_ext. intros i _. unfold Cop. reflexivity. }
  (* now the three force-loop cases *)
  destruct Hcases as
    [(Hh2 & Et1 & Emc & Eol & Esl)
    |[(v1 & Hh1 & Et1 & Ef0 & Hv1m & Hv1e & Eol & Esl)
     |(Hh0 & Et1 & Ef00 & Ef01 & Emc1 & Eol & Esl)]].
  - (* no manufactured slot *)
    destruct (sd_stree k) as [st|] eqn:Est.
    + set (Cst := fun v => t_len st v
                           + xbits (sd_extra_base k) (sd_extra k) v) in *.
      assert (HCst : forall v, 0 <= v < sd_elems k -> 0 <= Cst v <= 32).
      { intros v Hv. unfold Cst.
        pose proof (Hstb st eq_refl v Hv). pose proof (Hxb v Hv). lia. }
      assert (ESTT : wsum (fun v => frq v * (t_len st v
                            + xbits (sd_extra_base k) (sd_extra k) v))
                       0 (Z.to_nat (sd_elems k))
                     = wsum (fun v => frq v * Cst v)
                         0 (Z.to_nat (sd_elems k)))
        by (apply wsum_ext; intros i _; unfold Cst; reflexivity).
      set (WSs := wsum (slterm maxc1 t1 hp3 (sd_extra_base k) (sd_extra k) st)
                    (hmax + 1) (Z.to_nat (HEAP_SIZE - (hmax + 1)))) in *.
      assert (EWs : WSs = wsum (fun p => wF maxc1 (b_tree stf) Cst (hp3 p))
                            (hmax + 1) (NW hmax)).
      { unfold WSs, NW. apply wsum_ext. intros p _.
        unfold wF, slterm, Cst.
        destruct (Z.leb_spec (hp3 p) maxc1) as [Hle|Hgt]; cbn [ind].
        - rewrite (bp_frq _ _ _ _ _ _ _ Hpk (hp3 p)) by lia. reflexivity.
        - ring. }
      pose proof (kit_bound (sd_elems k) maxc1 t1 (b_tree stf) hp3 hmax ndf Cst
                    Hpk ltac:(lia) Hnd Hfr1 HCst) as BDs.
      exists WSo, WSs.
      split.
      { rewrite Gol, Eol. reflexivity. }
      split.
      { rewrite Gsl, Esl. reflexivity. }
      split; [rewrite EWo; lia|].
      split; [rewrite EWs; lia|].
      split.
      { rewrite EOPT, EWo.
        apply Z.le_trans with
          (wsum (fun p => wF maxc1 (b_tree stf) Cop (hp3 p)) (hmax + 1) (NW hmax));
          [|lia].
        apply (DOMSCHEME Cop (fun v => frq v * Cop v) HCop (PTW Cop HCop)). }
      split.
      { intros st0 Est0.
        assert (Est' : st0 = st) by congruence. subst st0.
        rewrite ESTT, EWs.
        apply (DOMSCHEME Cst (fun v => frq v * Cst v) HCst (PTW Cst HCst)). }
      { intros st0 Est0.
        assert (Est' : st0 = st) by congruence. subst st0.
        rewrite ESTT.
        pose proof (kit_upper (sd_elems k) maxc1 t1 (b_tree stf) hp3 hmax ndf
                      Cst Hpk ltac:(lia) Hnd Hfr1 HCst) as UP.
        rewrite <- EWs in UP.
        assert (EQ1 : wsum (fun v => t_freq t1 v * Cst v)
                        0 (Z.to_nat (sd_elems k))
                      = wsum (fun v => frq v * Cst v)
                          0 (Z.to_nat (sd_elems k))).
        { apply wsum_ext. intros v _. rewrite Et1, Hfrt0. reflexivity. }
        lia. }
    + exists WSo, 0.
      split.
      { rewrite Gol, Eol. reflexivity. }
      split.
      { rewrite Gsl, Esl. reflexivity. }
      split; [rewrite EWo; lia|].
      split; [lia|].
      split.
      { rewrite EOPT, EWo.
        apply Z.le_trans with
          (wsum (fun p => wF maxc1 (b_tree stf) Cop (hp3 p)) (hmax + 1) (NW hmax));
          [|lia].
        apply (DOMSCHEME Cop (fun v => frq v * Cop v) HCop (PTW Cop HCop)). }
      split.
      { intros st0 Est0. discriminate Est0. }
      { intros st0 Est0. discriminate Est0. }
  - (* one manufactured slot v1 *)
    assert (Hfrq0 : frq v1 = 0) by (rewrite <- (Hfrt0 v1); exact Ef0).
    assert (Hft1v1 : t_freq t1 v1 = 1).
    { rewrite Et1, g6_t_freq_setfreq_same. reflexivity. }
    assert (Hv1r : 0 <= v1 < sd_elems k) by lia.
    (* the delta-strengthened pointwise bound *)
    assert (PTW1 : forall (C : Z -> Z),
      (forall v, 0 <= v < sd_elems k -> 0 <= C v <= 32) ->
      forall v, 0 <= v < sd_elems k ->
      frq v * C v + (if Z.eqb v1 v then 1 else 0) * C v1
      <= wcw hp3 hmax v * wF maxc1 (b_tree stf) C v).
    { intros C HC v Hv.
      destruct (Z.eqb_spec v1 v) as [<-|Hne].
      - rewrite Hfrq0.
        destruct (kit_live (sd_elems k) maxc1 t1 (b_tree stf) hp3 hmax ndf C
                    Hpk ltac:(lia) Hnd v1 Hv1r ltac:(lia)
                    ltac:(rewrite Hft1v1; lia)) as [Ew EF].
        rewrite Ew, EF, Hft1v1. lia.
      - replace (if Z.eqb v1 v then 1 else 0) with 0
          by (symmetry; apply Z.eqb_neq in Hne;
              destruct (Z.eqb v1 v); congruence).
        pose proof (PTW C HC v Hv). lia. }
    destruct (sd_stree k) as [st|] eqn:Est.
    + set (Cst := fun v => t_len st v
                           + xbits (sd_extra_base k) (sd_extra k) v) in *.
      assert (HCst : forall v, 0 <= v < sd_elems k -> 0 <= Cst v <= 32).
      { intros v Hv. unfold Cst.
        pose proof (Hstb st eq_refl v Hv). pose proof (Hxb v Hv). lia. }
      assert (ESTT : wsum (fun v => frq v * (t_len st v
                            + xbits (sd_extra_base k) (sd_extra k) v))
                       0 (Z.to_nat (sd_elems k))
                     = wsum (fun v => frq v * Cst v)
                         0 (Z.to_nat (sd_elems k)))
        by (apply wsum_ext; intros i _; unfold Cst; reflexivity).
      set (WSs := wsum (slterm maxc1 t1 hp3 (sd_extra_base k) (sd_extra k) st)
                    (hmax + 1) (Z.to_nat (HEAP_SIZE - (hmax + 1)))) in *.
      assert (EWs : WSs = wsum (fun p => wF maxc1 (b_tree stf) Cst (hp3 p))
                            (hmax + 1) (NW hmax)).
      { unfold WSs, NW. apply wsum_ext. intros p _.
        unfold wF, slterm, Cst.
        destruct (Z.leb_spec (hp3 p) maxc1) as [Hle|Hgt]; cbn [ind].
        - rewrite (bp_frq _ _ _ _ _ _ _ Hpk (hp3 p)) by lia. reflexivity.
        - ring. }
      pose proof (kit_bound (sd_elems k) maxc1 t1 (b_tree stf) hp3 hmax ndf Cst
                    Hpk ltac:(lia) Hnd Hfr1 HCst) as BDs.
      (* the strengthened static domination *)
      assert (DSs : wsum (fun v => frq v * Cst v) 0 (Z.to_nat (sd_elems k))
                      + Cst v1
                    <= WSs).
      { rewrite EWs.
        pose proof (DOMSCHEME Cst
                      (fun v => frq v * Cst v
                                + (if Z.eqb v1 v then 1 else 0) * Cst v1)
                      HCst (PTW1 Cst HCst)) as H.
        rewrite wsum_plus in H.
        rewrite (wsum_delta (fun _ => Cst v1) v1 0 (Z.to_nat (sd_elems k)))
          in H by (rewrite Z2Nat.id by lia; lia).
        exact H. }
      assert (HSnn : 0 <= wsum (fun v => frq v * Cst v)
                            0 (Z.to_nat (sd_elems k))).
      { apply wsum_nonneg. intros v Hv.
        assert (Hv' : 0 <= v < sd_elems k)
          by (rewrite Z2Nat.id in Hv by lia; lia).
        pose proof (Hfr v Hv'). pose proof (HCst v Hv').
        apply Z.mul_nonneg_nonneg; lia. }
      assert (HCv1 : 0 <= t_len st v1 <= Cst v1).
      { unfold Cst. pose proof (Hstb st eq_refl v1 Hv1r).
        pose proof (Hxb v1 Hv1r). lia. }
      exists (WSo - 1), (WSs - t_len st v1).
      split.
      { rewrite Gol, Eol, g6_u64_shift. f_equal. ring. }
      split.
      { rewrite Gsl, Esl, g6_u64_shift. f_equal. ring. }
      split; [rewrite EWo; lia|].
      split; [lia|].
      split.
      { rewrite EOPT, EWo.
        pose proof (DOMSCHEME Cop (fun v => frq v * Cop v)
                      HCop (PTW Cop HCop)) as H.
        lia. }
      split.
      { intros st0 Est0.
        assert (Est' : st0 = st) by congruence. subst st0.
        rewrite ESTT. lia. }
      { intros st0 Est0.
        assert (Est' : st0 = st) by congruence. subst st0.
        rewrite ESTT.
        pose proof (kit_upper (sd_elems k) maxc1 t1 (b_tree stf) hp3 hmax ndf
                      Cst Hpk ltac:(lia) Hnd Hfr1 HCst) as UP.
        rewrite <- EWs in UP.
        assert (EQ2 : wsum (fun v => t_freq t1 v * Cst v)
                        0 (Z.to_nat (sd_elems k))
                      = wsum (fun v => frq v * Cst v)
                          0 (Z.to_nat (sd_elems k)) + Cst v1).
        { etransitivity.
          { apply (wsum_ext (fun v => t_freq t1 v * Cst v)
                     (fun v => frq v * Cst v
                               + (if Z.eqb v1 v then 1 else 0) * Cst v1)
                     0 (Z.to_nat (sd_elems k))).
            intros v _.
            destruct (Z.eqb_spec v1 v) as [<-|Hne].
            - rewrite Hft1v1, Hfrq0. ring.
            - rewrite Et1.
              rewrite g6_t_freq_setfreq_other by lia.
              rewrite Hfrt0. ring. }
          rewrite wsum_plus.
          rewrite (wsum_delta (fun _ => Cst v1) v1 0 (Z.to_nat (sd_elems k)))
            by (rewrite Z2Nat.id by lia; lia).
          reflexivity. }
        assert (HXv1 : Cst v1 <= t_len st v1 + 16)
          by (unfold Cst; pose proof (Hxb v1 Hv1r); lia).
        lia. }
    + exists (WSo - 1), 0.
      split.
      { rewrite Gol, Eol, g6_u64_shift. f_equal. ring. }
      split.
      { rewrite Gsl, Esl. reflexivity. }
      split; [rewrite EWo; lia|].
      split; [lia|].
      split.
      { rewrite EOPT, EWo.
        pose proof (DOMSCHEME Cop (fun v => frq v * Cop v)
                      HCop (PTW Cop HCop)) as H.
        lia. }
      split.
      { intros st0 Est0. discriminate Est0. }
      { intros st0 Est0. discriminate Est0. }
  - (* two manufactured slots: 0 and 1 *)
    assert (Hfrq00 : frq 0 = 0) by (rewrite <- (Hfrt0 0); exact Ef00).
    assert (Hfrq01 : frq 1 = 0) by (rewrite <- (Hfrt0 1); exact Ef01).
    assert (Hft10 : t_freq t1 0 = 1).
    { rewrite Et1.
      rewrite g6_t_freq_setfreq_other by lia.
      rewrite g6_t_freq_setfreq_same. reflexivity. }
    assert (Hft11 : t_freq t1 1 = 1).
    { rewrite Et1, g6_t_freq_setfreq_same. reflexivity. }
    assert (H0r : 0 <= 0 < sd_elems k) by lia.
    assert (H1r : 0 <= 1 < sd_elems k) by lia.
    assert (PTW2 : forall (C : Z -> Z),
      (forall v, 0 <= v < sd_elems k -> 0 <= C v <= 32) ->
      forall v, 0 <= v < sd_elems k ->
      frq v * C v + (if Z.eqb 0 v then 1 else 0) * C 0
                  + (if Z.eqb 1 v then 1 else 0) * C 1
      <= wcw hp3 hmax v * wF maxc1 (b_tree stf) C v).
    { intros C HC v Hv.
      destruct (Z.eqb_spec 0 v) as [<-|Hne0].
      - rewrite Hfrq00. cbn [Z.eqb].
        destruct (kit_live (sd_elems k) maxc1 t1 (b_tree stf) hp3 hmax ndf C
                    Hpk ltac:(lia) Hnd 0 H0r ltac:(lia)
                    ltac:(rewrite Hft10; lia)) as [Ew EF].
        rewrite Ew, EF, Hft10. lia.
      - destruct (Z.eqb_spec 1 v) as [<-|Hne1].
        + rewrite Hfrq01. cbn [Z.eqb].
          destruct (kit_live (sd_elems k) maxc1 t1 (b_tree stf) hp3 hmax ndf C
                      Hpk ltac:(lia) Hnd 1 H1r ltac:(lia)
                      ltac:(rewrite Hft11; lia)) as [Ew EF].
          rewrite Ew, EF, Hft11. lia.
        + replace (if Z.eqb 0 v then 1 else 0) with 0
            by (destruct (Z.eqb_spec 0 v); congruence).
          replace (if Z.eqb 1 v then 1 else 0) with 0
            by (destruct (Z.eqb_spec 1 v); congruence).
          pose proof (PTW C HC v Hv). lia. }
    destruct (sd_stree k) as [st|] eqn:Est.
    + set (Cst := fun v => t_len st v
                           + xbits (sd_extra_base k) (sd_extra k) v) in *.
      assert (HCst : forall v, 0 <= v < sd_elems k -> 0 <= Cst v <= 32).
      { intros v Hv. unfold Cst.
        pose proof (Hstb st eq_refl v Hv). pose proof (Hxb v Hv). lia. }
      assert (ESTT : wsum (fun v => frq v * (t_len st v
                            + xbits (sd_extra_base k) (sd_extra k) v))
                       0 (Z.to_nat (sd_elems k))
                     = wsum (fun v => frq v * Cst v)
                         0 (Z.to_nat (sd_elems k)))
        by (apply wsum_ext; intros i _; unfold Cst; reflexivity).
      set (WSs := wsum (slterm maxc1 t1 hp3 (sd_extra_base k) (sd_extra k) st)
                    (hmax + 1) (Z.to_nat (HEAP_SIZE - (hmax + 1)))) in *.
      assert (EWs : WSs = wsum (fun p => wF maxc1 (b_tree stf) Cst (hp3 p))
                            (hmax + 1) (NW hmax)).
      { unfold WSs, NW. apply wsum_ext. intros p _.
        unfold wF, slterm, Cst.
        destruct (Z.leb_spec (hp3 p) maxc1) as [Hle|Hgt]; cbn [ind].
        - rewrite (bp_frq _ _ _ _ _ _ _ Hpk (hp3 p)) by lia. reflexivity.
        - ring. }
      pose proof (kit_bound (sd_elems k) maxc1 t1 (b_tree stf) hp3 hmax ndf Cst
                    Hpk ltac:(lia) Hnd Hfr1 HCst) as BDs.
      assert (DSs : wsum (fun v => frq v * Cst v) 0 (Z.to_nat (sd_elems k))
                      + Cst 0 + Cst 1
                    <= WSs).
      { rewrite EWs.
        pose proof (DOMSCHEME Cst
                      (fun v => frq v * Cst v
                                + (if Z.eqb 0 v then 1 else 0) * Cst 0
                                + (if Z.eqb 1 v then 1 else 0) * Cst 1)
                      HCst (PTW2 Cst HCst)) as H.
        rewrite wsum_plus in H.
        rewrite (wsum_delta (fun _ => Cst 1) 1 0 (Z.to_nat (sd_elems k))) in H
          by (rewrite Z2Nat.id by lia; lia).
        rewrite wsum_plus in H.
        rewrite (wsum_delta (fun _ => Cst 0) 0 0 (Z.to_nat (sd_elems k))) in H
          by (rewrite Z2Nat.id by lia; lia).
        lia. }
      assert (HSnn : 0 <= wsum (fun v => frq v * Cst v)
                            0 (Z.to_nat (sd_elems k))).
      { apply wsum_nonneg. intros v Hv.
        assert (Hv' : 0 <= v < sd_elems k)
          by (rewrite Z2Nat.id in Hv by lia; lia).
        pose proof (Hfr v Hv'). pose proof (HCst v Hv').
        apply Z.mul_nonneg_nonneg; lia. }
      assert (HC0 : 0 <= t_len st 0 <= Cst 0).
      { unfold Cst. pose proof (Hstb st eq_refl 0 H0r).
        pose proof (Hxb 0 H0r). lia. }
      assert (HC1 : 0 <= t_len st 1 <= Cst 1).
      { unfold Cst. pose proof (Hstb st eq_refl 1 H1r).
        pose proof (Hxb 1 H1r). lia. }
      exists (WSo - 2), (WSs - t_len st 0 - t_len st 1).
      split.
      { rewrite Gol, Eol, g6_u64_shift. f_equal. ring. }
      split.
      { rewrite Gsl, Esl, g6_u64_shift. f_equal. ring. }
      split; [rewrite EWo; lia|].
      split; [lia|].
      split.
      { rewrite EOPT, EWo.
        pose proof (DOMSCHEME Cop (fun v => frq v * Cop v)
                      HCop (PTW Cop HCop)) as H.
        lia. }
      split.
      { intros st0 Est0.
        assert (Est' : st0 = st) by congruence. subst st0.
        rewrite ESTT. lia. }
      { intros st0 Est0.
        assert (Est' : st0 = st) by congruence. subst st0.
        rewrite ESTT.
        pose proof (kit_upper (sd_elems k) maxc1 t1 (b_tree stf) hp3 hmax ndf
                      Cst Hpk ltac:(lia) Hnd Hfr1 HCst) as UP.
        rewrite <- EWs in UP.
        assert (EQ3 : wsum (fun v => t_freq t1 v * Cst v)
                        0 (Z.to_nat (sd_elems k))
                      = wsum (fun v => frq v * Cst v)
                          0 (Z.to_nat (sd_elems k)) + Cst 0 + Cst 1).
        { etransitivity.
          { apply (wsum_ext (fun v => t_freq t1 v * Cst v)
                     (fun v => frq v * Cst v
                               + (if Z.eqb 0 v then 1 else 0) * Cst 0
                               + (if Z.eqb 1 v then 1 else 0) * Cst 1)
                     0 (Z.to_nat (sd_elems k))).
            intros v _.
            destruct (Z.eqb_spec 0 v) as [<-|Hne0].
            - rewrite Hft10, Hfrq00.
              replace (Z.eqb 1 0) with false by reflexivity. ring.
            - destruct (Z.eqb_spec 1 v) as [<-|Hne1].
              + rewrite Hft11, Hfrq01. ring.
              + rewrite Et1.
                rewrite g6_t_freq_setfreq_other by lia.
                rewrite g6_t_freq_setfreq_other by lia.
                rewrite Hfrt0. ring. }
          rewrite wsum_plus.
          rewrite (wsum_delta (fun _ => Cst 1) 1 0 (Z.to_nat (sd_elems k)))
            by (rewrite Z2Nat.id by lia; lia).
          rewrite wsum_plus.
          rewrite (wsum_delta (fun _ => Cst 0) 0 0 (Z.to_nat (sd_elems k)))
            by (rewrite Z2Nat.id by lia; lia).
          ring. }
        assert (HX0 : Cst 0 <= t_len st 0 + 16)
          by (unfold Cst; pose proof (Hxb 0 H0r); lia).
        assert (HX1 : Cst 1 <= t_len st 1 + 16)
          by (unfold Cst; pose proof (Hxb 1 H1r); lia).
        lia. }
    + exists (WSo - 2), 0.
      split.
      { rewrite Gol, Eol, g6_u64_shift. f_equal. ring. }
      split.
      { rewrite Gsl, Esl. reflexivity. }
      split; [rewrite EWo; lia|].
      split; [lia|].
      split.
      { rewrite EOPT, EWo.
        pose proof (DOMSCHEME Cop (fun v => frq v * Cop v)
                      HCop (PTW Cop HCop)) as H.
        lia. }
      split.
      { intros st0 Est0. discriminate Est0. }
      { intros st0 Est0. discriminate Est0. }
Qed.

Set Printing All.
Set Printing Fully Qualified.
Set Printing Depth 10000000000.
Set Printing Width 2000.
Print Assumptions kit_exchange.
Print Assumptions kit_live.
Print Assumptions kit_bound.
Print Assumptions build_tree_counters.
Unset Printing All.
