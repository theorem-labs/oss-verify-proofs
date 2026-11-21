(** * ZHOFibN — ZHOFib with the entry freq-nonneg premise NARROWED to the
      symbol range [0, elems) (R39 consumer-review dry run).  Identical to
      the frozen ZHOFib.v except: the theorem premise, the [fc_nn] clause
      (now range-bounded to [0, b_node st), extended by one index per trip),
      the census value-range helper [zhfn_live_val_range] that re-derives
      live values' ranges, and the standalone fib lemmas taking the two
      freq-nonneg facts they actually use (at [zho_n st]/[zho_m st]).

    OWNER: huffman-opt.  L4 piece (F).  A second walk over [bt_loop] (the
    ZHOSim pattern) carrying:
      (LP)   a last-pop watermark: every live freq is >= LP (lp1), every
             parked freq is <= LP (lp2);
      (fib)  along every dad-chain x ->^d i ending at a live-or-created
             endpoint i: fibZ (d+1) * freq x <= freq i.  Preservation at a
             merge (n, m -> node): F(d+2) f(x) <= f(n) + f(m) via the old
             chain at n [fib], the penultimate chain node c parked below n
             [fib at c] and f(c) <= LP <= f(m) [lp2, lp1];
      (wmono) the parked window is freq-monotone: ascending position =
             descending pop time = freq nonincreasing;
      (mass) the live freq total is conserved (<= 65535), so [t_setfreq]'s
             u16 collapses (Z.mod_small) and created freqs are TRUE sums.

    Exports (at [Some stf], after the root-parking epilogue):
      FIB-A: dad-chain Fibonacci at the exit tree, endpoint = the root;
      FIB-B: window freq-monotonicity over the FULL parked window [hp3];
      FIB-C: the root freq equals the live entry mass (total T).
    The len<->chain bridge (pass-1 lens = capped chain depths) is the
    consumer's job (window induction on Pass1Inv + bp_ord), not this walk's.

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT. *)

From Stdlib Require Import ZArith List Lia Bool Arith Sorting.Permutation.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff Trees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  BtWin BtStep BtCensus1 BtCensus2 BtCensus3 BtCensus4.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.ZHO Require Import ZHOHeap ZHOSim.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** Fibonacci over Z, F(1) = F(2) = 1 *)
Fixpoint fibZ (n : nat) : Z :=
  match n with
  | O => 0
  | S m => match m with
           | O => 1
           | S p => fibZ m + fibZ p
           end
  end.

(** dad-chains: [dchainN t x i d] = following [t_dad] from [x] reaches [i]
    in exactly [d] steps *)
Fixpoint dchainN (t : Tree) (x i : Z) (d : nat) : Prop :=
  match d with
  | O => x = i
  | S d' => dchainN t (t_dad t x) i d'
  end.

(** iterated dad *)
Fixpoint dpow (t : Tree) (k : nat) (x : Z) : Z :=
  match k with O => x | S k' => dpow t k' (t_dad t x) end.

(** ** fibZ / dpow / dchainN algebra *)

Lemma fibZ_SS : forall p, fibZ (S (S p)) = fibZ (S p) + fibZ p.
Proof. reflexivity. Qed.

Lemma fibZ_nonneg : forall n, 0 <= fibZ n.
Proof.
  intro n.
  assert (H : 0 <= fibZ n /\ 0 <= fibZ (S n)); [|tauto].
  induction n as [|k IH].
  - cbn. lia.
  - split; [tauto|]. rewrite fibZ_SS. lia.
Qed.

Lemma dpow_dad : forall t k x, dpow t (S k) x = t_dad t (dpow t k x).
Proof.
  intros t k. induction k as [|k IH]; intro x.
  - reflexivity.
  - cbn [dpow]. apply (IH (t_dad t x)).
Qed.

Lemma dchain_dpow : forall t d x i, dchainN t x i d <-> dpow t d x = i.
Proof.
  intros t d. induction d as [|d IH]; intros x i.
  - cbn. tauto.
  - cbn [dchainN dpow]. apply IH.
Qed.

Lemma dpow_transport : forall (t t' : Tree) (d : nat) (x : Z),
  (forall k, (k < d)%nat -> t_dad t' (dpow t' k x) = t_dad t (dpow t' k x)) ->
  forall j, (j <= d)%nat -> dpow t' j x = dpow t j x.
Proof.
  intros t t' d x Hd j.
  induction j as [|j IH]; intro Hj.
  - reflexivity.
  - rewrite dpow_dad, dpow_dad.
    rewrite <- (IH ltac:(lia)).
    apply Hd. lia.
Qed.

Section ZHOFib.

Variables (elems maxc1 : Z) (t1 : Tree) (dep1 hp1 : zarr) (hlen1 : Z).

Definition zhof_st0 : BtSt :=
  {| b_tree := t1;
     b_heap := bt_heapify (Z.to_nat HEAP_SIZE) t1 dep1 hp1 hlen1 (hlen1 / 2);
     b_dep := dep1; b_hlen := hlen1; b_hmax := HEAP_SIZE; b_node := elems |}.

(** the conserved live mass *)
Local Notation M0 :=
  (wsum (fun x => ind (live_b t1 maxc1 x) * t_freq t1 x) 0 (Z.to_nat elems)).

(** ** The walk invariant *)

Record FibCore (st : BtSt) (LP : Z) : Prop := mkFibCore {
  fc_census : CensusInv elems maxc1 t1 hlen1 st;
  fc_nn     : forall x, 0 <= x < b_node st -> 0 <= t_freq (b_tree st) x;
  fc_lp1    : forall p, 1 <= p <= b_hlen st ->
              LP <= t_freq (b_tree st) (b_heap st p);
  fc_lp2    : forall p, b_hmax st <= p < HEAP_SIZE ->
              t_freq (b_tree st) (b_heap st p) <= LP;
  fc_wmono  : forall p q, b_hmax st <= p -> p <= q -> q < HEAP_SIZE ->
              t_freq (b_tree st) (b_heap st q)
              <= t_freq (b_tree st) (b_heap st p);
  fc_mass   : zsumF (zho_win (b_heap st) (b_hlen st)) (t_freq (b_tree st))
              = M0;
  fc_fib    : forall p i d, b_hmax st <= p < HEAP_SIZE ->
              elems <= i < b_node st ->
              dchainN (b_tree st) (b_heap st p) i d ->
              (forall k, (1 <= k < d)%nat ->
                 1 <= pcount (b_heap st) (b_hmax st)
                        (dpow (b_tree st) k (b_heap st p))) ->
              fibZ (d + 1) * t_freq (b_tree st) (b_heap st p)
              <= t_freq (b_tree st) i
}.

(** live-window values sit in [0, b_node st): census classification *)
Lemma zhfn_live_val_range : forall st v,
  0 <= elems -> maxc1 < elems ->
  CensusInv elems maxc1 t1 hlen1 st ->
  1 <= lcount (b_heap st) (b_hlen st) v ->
  0 <= v < b_node st.
Proof.
  intros st v Hel0 Hme Hcen Hlc.
  pose proof (cv_nd _ _ _ _ _ Hcen) as Hnd0.
  pose proof (cv_cons _ _ _ _ _ Hcen v) as Hc.
  pose proof (wcount_nonneg (b_heap st) (b_hmax st)
                (Z.to_nat (HEAP_SIZE - b_hmax st)) v) as Hp0.
  unfold pcount in Hc.
  destruct (live_b t1 maxc1 v) eqn:El.
  - pose proof (zho_live_b_range maxc1 t1 v El). lia.
  - cbn [ind] in Hc.
    destruct ((elems <=? v) && (v <? b_node st)) eqn:Ec.
    + apply andb_true_iff in Ec as [E1 E2].
      apply Z.leb_le in E1. apply Z.ltb_lt in E2. lia.
    + cbn [ind] in Hc. lia.
Qed.

(** ** Entry *)

Lemma zhf_entry_val_live :
  InitOut elems t1 hp1 hlen1 maxc1 -> 0 <= hlen1 ->
  forall p, 1 <= p <= hlen1 -> live_b t1 maxc1 (b_heap zhof_st0 p) = true.
Proof.
  intros Hio Hh0 p Hp.
  assert (H1 : 1 <= lcount (b_heap zhof_st0) hlen1 (b_heap zhof_st0 p))
    by (apply lcount_member; exact Hp).
  cbn [b_heap zhof_st0] in H1 |- *.
  rewrite bt_heapify_count in H1 by (apply Z.div_le_upper_bound; lia).
  rewrite (io_spec _ _ _ _ _ Hio) in H1.
  apply zho_ind_pos_true. exact H1.
Qed.

Lemma zhf_entry :
  0 < elems <= L_CODES -> maxc1 < elems ->
  2 <= hlen1 <= L_CODES ->
  (forall n, 0 <= n < elems -> 0 <= t_freq t1 n) ->
  InitOut elems t1 hp1 hlen1 maxc1 ->
  FibCore zhof_st0 0 /\ StepPre zhof_st0.
Proof.
  intros Hel Hme Hh1 Hnn Hio.
  assert (Hdiv : 2 * (hlen1 / 2) <= hlen1 /\ hlen1 <= 2 * (hlen1 / 2) + 1).
  { pose proof (Z.div_mod hlen1 2 ltac:(lia)).
    pose proof (Z.mod_pos_bound hlen1 2 ltac:(lia)). lia. }
  assert (Hpre : StepPre zhof_st0).
  { constructor.
    - cbn [b_hlen zhof_st0]. lia.
    - cbn [b_hlen b_hmax zhof_st0]. unfold HEAP_SIZE, L_CODES in *. lia.
    - cbn [b_tree b_dep b_heap b_hlen zhof_st0].
      apply bt_heapify_heapok.
      + rewrite Z2Nat.id by (unfold HEAP_SIZE; lia).
        unfold HEAP_SIZE, L_CODES in *. lia.
      + lia.
      + unfold L_CODES in *. lia.
      + apply heapokfrom_vacuous. lia.
    - intros p Hp.
      cbn [b_node zhof_st0]. cbn [b_hlen zhof_st0] in Hp.
      pose proof (zhf_entry_val_live Hio ltac:(lia) p Hp) as Hlv.
      pose proof (zho_live_b_range maxc1 t1 _ Hlv). lia. }
  split; [|exact Hpre].
  constructor.
  - exact (census_entry elems maxc1 t1 hp1 dep1 hlen1
             (Z.to_nat HEAP_SIZE) ltac:(lia) Hio).
  - intros x Hx. cbn [b_node zhof_st0] in Hx.
    cbn [b_tree zhof_st0]. apply Hnn. lia.
  - intros p Hp. cbn [b_hlen zhof_st0] in Hp.
    pose proof (zho_live_b_range maxc1 t1 _
                  (zhf_entry_val_live Hio ltac:(lia) p Hp)) as Hr.
    change (b_tree zhof_st0) with t1. apply Hnn. lia.
  - intros p Hp. cbn [b_hmax zhof_st0] in Hp. lia.
  - intros p q Hp Hpq Hq. cbn [b_hmax zhof_st0] in Hp. lia.
  - cbn [b_tree b_heap b_hlen zhof_st0].
    rewrite (zsumF_counts
               (zho_win (bt_heapify (Z.to_nat HEAP_SIZE) t1 dep1 hp1 hlen1
                           (hlen1 / 2)) hlen1)
               (t_freq t1) 0 (Z.to_nat elems)).
    + apply wsum_ext. intros x Hx.
      f_equal.
      rewrite zho_win_count by lia.
      rewrite bt_heapify_count by (apply Z.div_le_upper_bound; lia).
      apply (io_spec _ _ _ _ _ Hio).
    + intros v Hin.
      destruct (zho_win_in_inv _ _ _ Hin) as (p & Hp & Hv).
      pose proof (zho_live_b_range maxc1 t1 _
                    (zhf_entry_val_live Hio ltac:(lia) p Hp)) as Hr.
      cbn [b_heap zhof_st0] in Hr.
      rewrite Hv in Hr.
      rewrite Z2Nat.id by lia. lia.
  - intros p i d Hp Hi Hch Hint.
    cbn [b_hmax zhof_st0] in Hp. lia.
Qed.

(** the fib-clause preservation, standalone so its Qed cost is isolated *)
(** the deep i=nd case of the fib preservation, standalone (Qed isolation) *)
Lemma zhf_fib_nd : forall (st st' : BtSt) (LP : Z),
  b_hmax st' = b_hmax st - 2 ->
  b_node st' = b_node st + 1 ->
  b_hmax st <= HEAP_SIZE ->
  0 <= t_freq (b_tree st) (zho_n st) ->
  0 <= t_freq (b_tree st) (zho_m st) ->
  (forall p, b_hmax st <= p < HEAP_SIZE ->
     elems <= t_dad (b_tree st) (b_heap st p) < b_node st) ->
  (forall p, b_hmax st <= p < HEAP_SIZE ->
     t_freq (b_tree st) (b_heap st p) <= LP) ->
  LP <= t_freq (b_tree st) (zho_n st) ->
  LP <= t_freq (b_tree st) (zho_m st) ->
  (forall p i d, b_hmax st <= p < HEAP_SIZE ->
     elems <= i < b_node st ->
     dchainN (b_tree st) (b_heap st p) i d ->
     (forall k, (1 <= k < d)%nat ->
        1 <= pcount (b_heap st) (b_hmax st)
               (dpow (b_tree st) k (b_heap st p))) ->
     fibZ (d + 1) * t_freq (b_tree st) (b_heap st p)
     <= t_freq (b_tree st) i) ->
  (forall p, b_hmax st <= p < HEAP_SIZE -> b_heap st' p = b_heap st p) ->
  b_heap st' (b_hmax st - 1) = zho_n st ->
  b_heap st' (b_hmax st - 2) = zho_m st ->
  t_freq (b_tree st') (b_node st)
    = t_freq (b_tree st) (zho_n st) + t_freq (b_tree st) (zho_m st) ->
  (forall x, x <> b_node st ->
     t_freq (b_tree st') x = t_freq (b_tree st) x) ->
  t_dad (b_tree st') (zho_n st) = b_node st ->
  t_dad (b_tree st') (zho_m st) = b_node st ->
  (forall w, w <> zho_n st -> w <> zho_m st ->
     t_dad (b_tree st') w = t_dad (b_tree st) w) ->
  (forall w, pcount (b_heap st') (b_hmax st') w
     = pcount (b_heap st) (b_hmax st) w
       + ind (Z.eqb (zho_n st) w) + ind (Z.eqb (zho_m st) w)) ->
  pcount (b_heap st') (b_hmax st') (b_node st) = 0 ->
  pcount (b_heap st) (b_hmax st) (zho_n st) = 0 ->
  pcount (b_heap st) (b_hmax st) (zho_m st) = 0 ->
  pcount (b_heap st) (b_hmax st) (b_node st) = 0 ->
  zho_n st < b_node st -> zho_m st < b_node st ->
  forall p (d2 : nat),
  b_hmax st <= p < HEAP_SIZE ->
  1 <= pcount (b_heap st) (b_hmax st) (b_heap st p) ->
  dpow (b_tree st') (S (S d2)) (b_heap st p) = b_node st ->
  (forall k, (1 <= k < S (S d2))%nat ->
     1 <= pcount (b_heap st') (b_hmax st')
            (dpow (b_tree st') k (b_heap st p))) ->
  fibZ (S (S d2) + 1) * t_freq (b_tree st) (b_heap st p)
  <= t_freq (b_tree st) (zho_n st) + t_freq (b_tree st) (zho_m st).
Proof.
  intros st st' LP Ehmz Endz Hhs Hfn_nn Hfn_mm Hordp Hlp2 HLPn HLPm Hfib
         Hpark_frozen Hslot_n Hslot_m Efrq_nd Efrq_o Edad_n Edad_m Edad_o
         Hpc' Hpcnd' Hpc_n0 Hpc_m0 Hpc_nd0 Hn_lt Hm_lt
         p d2 Hpo Hxpc Hch Hint.
  set (hp := b_heap st) in *.
  set (hm := b_hmax st) in *.
  set (nd := b_node st) in *.
  set (tr := b_tree st) in *.
  set (nn := zho_n st) in *.
  set (mm := zho_m st) in *.
  set (x := hp p) in *.
  assert (Hxn : x <> nn) by (intro E; rewrite E in Hxpc; lia).
  assert (Hxm : x <> mm) by (intro E; rewrite E in Hxpc; lia).
  assert (Hxd : x <> nd) by (intro E; rewrite E in Hxpc; lia).
  assert (Hparked_facts : forall w, 1 <= pcount hp hm w ->
            w <> nd /\ elems <= t_dad tr w < nd /\ t_freq tr w <= LP).
  { intros w Hw.
    assert (Hwnd : w <> nd)
      by (intro E; rewrite E in Hw; lia).
    unfold pcount in Hw.
    destruct (wcount_pos_inv hp hm (Z.to_nat (HEAP_SIZE - hm)) w Hw)
      as (q & Hq & Hqe).
    rewrite Z2Nat.id in Hq by lia.
    assert (Hq' : hm <= q < HEAP_SIZE) by lia.
    split; [exact Hwnd|]. split.
    - pose proof (Hordp q Hq') as Hdr. rewrite Hqe in Hdr. exact Hdr.
    - rewrite <- Hqe. apply Hlp2. exact Hq'. }
      assert (Havoid : forall k, (k < S d2)%nat ->
                dpow (b_tree st') k x <> nn /\ dpow (b_tree st') k x <> mm).
      { intros k Hk. destruct k as [|k1].
        - cbn [dpow]. split; assumption.
        - split; intro E.
          + assert (Ednd : dpow (b_tree st') (S (S k1)) x = nd)
              by (rewrite dpow_dad, E; exact Edad_n).
            specialize (Hint (S (S k1)) ltac:(lia)).
            rewrite Ednd, Hpcnd' in Hint. lia.
          + assert (Ednd : dpow (b_tree st') (S (S k1)) x = nd)
              by (rewrite dpow_dad, E; exact Edad_m).
            specialize (Hint (S (S k1)) ltac:(lia)).
            rewrite Ednd, Hpcnd' in Hint. lia. }
      assert (Htrans : forall j, (j <= S d2)%nat ->
                dpow (b_tree st') j x = dpow tr j x).
      { apply dpow_transport. intros k Hk.
        destruct (Havoid k Hk) as [H1 H2]. apply Edad_o; assumption. }
      set (y' := dpow (b_tree st') (S d2) x).
      assert (Hylast : t_dad (b_tree st') y' = nd).
      { rewrite dpow_dad in Hch. exact Hch. }
      assert (Hy_nm : y' = nn \/ y' = mm).
      { destruct (Z.eqb_spec y' nn) as [->|Hyn]; [left; reflexivity|].
        destruct (Z.eqb_spec y' mm) as [->|Hym]; [right; reflexivity|].
        exfalso.
        rewrite (Edad_o y' Hyn Hym) in Hylast.
        specialize (Hint (S d2) ltac:(lia)).
        fold y' in Hint.
        rewrite Hpc' in Hint.
        replace (Z.eqb nn y') with false in Hint
          by (symmetry; apply Z.eqb_neq; congruence).
        replace (Z.eqb mm y') with false in Hint
          by (symmetry; apply Z.eqb_neq; congruence).
        cbn [ind] in Hint.
        destruct (Hparked_facts y' ltac:(lia)) as (_ & Hdy & _). lia. }
      assert (Hpref_pc : forall k, (1 <= k < S d2)%nat ->
                1 <= pcount hp hm (dpow tr k x)).
      { intros k Hk.
        specialize (Hint k ltac:(lia)).
        rewrite (Htrans k ltac:(lia)) in Hint.
        rewrite Hpc' in Hint.
        destruct (Havoid k ltac:(lia)) as [H1 H2].
        rewrite (Htrans k ltac:(lia)) in H1, H2.
        replace (Z.eqb nn (dpow tr k x)) with false in Hint
          by (symmetry; apply Z.eqb_neq; congruence).
        replace (Z.eqb mm (dpow tr k x)) with false in Hint
          by (symmetry; apply Z.eqb_neq; congruence).
        cbn [ind] in Hint. lia. }
      set (y := dpow tr (S d2) x).
      assert (Eyy : y' = y) by (apply Htrans; lia).
      assert (Hc_parked : 1 <= pcount hp hm (dpow tr d2 x)).
      { destruct d2 as [|d3].
        - cbn [dpow]. exact Hxpc.
        - apply Hpref_pc. lia. }
      assert (Hy_rng : elems <= y < nd).
      { destruct (Hparked_facts (dpow tr d2 x) Hc_parked) as (_ & Hdc & _).
        rewrite <- dpow_dad in Hdc. exact Hdc. }
      assert (Hfib_y : fibZ (S d2 + 1) * t_freq tr x <= t_freq tr y).
      { apply (Hfib p y (S d2) Hpo Hy_rng).
        - apply dchain_dpow. reflexivity.
        - intros k Hk. exact (Hpref_pc k Hk). }
      assert (Hfib_c : fibZ (d2 + 1) * t_freq tr x <= LP).
      { destruct d2 as [|d3].
        - change (fibZ (0 + 1)) with 1.
          destruct (Hparked_facts x Hxpc) as (_ & _ & HxLP). lia.
        - set (c := dpow tr (S d3) x).
          assert (Hc_pc : 1 <= pcount hp hm c) by (apply Hpref_pc; lia).
          assert (Hcpred_pc : 1 <= pcount hp hm (dpow tr d3 x)).
          { destruct d3 as [|d4].
            - cbn [dpow]. exact Hxpc.
            - apply Hpref_pc. lia. }
          assert (Hc_rng : elems <= c < nd).
          { destruct (Hparked_facts (dpow tr d3 x) Hcpred_pc)
              as (_ & Hdc & _).
            rewrite <- dpow_dad in Hdc. exact Hdc. }
          assert (HH : fibZ (S d3 + 1) * t_freq tr x <= t_freq tr c).
          { apply (Hfib p c (S d3) Hpo Hc_rng).
            - apply dchain_dpow. reflexivity.
            - intros k Hk. apply Hpref_pc. lia. }
          destruct (Hparked_facts c Hc_pc) as (_ & _ & HcLP). lia. }
      replace (S (S d2) + 1)%nat with (S (S (S d2)))%nat by lia.
      rewrite fibZ_SS.
      rewrite Z.mul_add_distr_r.
      replace (S d2 + 1)%nat with (S (S d2))%nat in Hfib_y by lia.
      replace (d2 + 1)%nat with (S d2)%nat in Hfib_c by lia.
      destruct Hy_nm as [Eyn|Eym].
      + assert (Ey : y = nn) by congruence.
        rewrite Ey in Hfib_y. lia.
      + assert (Ey : y = mm) by congruence.
        rewrite Ey in Hfib_y. lia.
Qed.

(** the i-below-node case of the fib preservation, standalone *)
Lemma zhf_fib_lt : forall (st st' : BtSt) (LP : Z),
  b_hmax st' = b_hmax st - 2 ->
  b_node st' = b_node st + 1 ->
  b_hmax st <= HEAP_SIZE ->
  0 <= t_freq (b_tree st) (zho_n st) ->
  0 <= t_freq (b_tree st) (zho_m st) ->
  (forall p, b_hmax st <= p < HEAP_SIZE ->
     elems <= t_dad (b_tree st) (b_heap st p) < b_node st) ->
  (forall p, b_hmax st <= p < HEAP_SIZE ->
     t_freq (b_tree st) (b_heap st p) <= LP) ->
  LP <= t_freq (b_tree st) (zho_n st) ->
  LP <= t_freq (b_tree st) (zho_m st) ->
  (forall p i d, b_hmax st <= p < HEAP_SIZE ->
     elems <= i < b_node st ->
     dchainN (b_tree st) (b_heap st p) i d ->
     (forall k, (1 <= k < d)%nat ->
        1 <= pcount (b_heap st) (b_hmax st)
               (dpow (b_tree st) k (b_heap st p))) ->
     fibZ (d + 1) * t_freq (b_tree st) (b_heap st p)
     <= t_freq (b_tree st) i) ->
  (forall p, b_hmax st <= p < HEAP_SIZE -> b_heap st' p = b_heap st p) ->
  b_heap st' (b_hmax st - 1) = zho_n st ->
  b_heap st' (b_hmax st - 2) = zho_m st ->
  t_freq (b_tree st') (b_node st)
    = t_freq (b_tree st) (zho_n st) + t_freq (b_tree st) (zho_m st) ->
  (forall x, x <> b_node st ->
     t_freq (b_tree st') x = t_freq (b_tree st) x) ->
  t_dad (b_tree st') (zho_n st) = b_node st ->
  t_dad (b_tree st') (zho_m st) = b_node st ->
  (forall w, w <> zho_n st -> w <> zho_m st ->
     t_dad (b_tree st') w = t_dad (b_tree st) w) ->
  (forall w, pcount (b_heap st') (b_hmax st') w
     = pcount (b_heap st) (b_hmax st) w
       + ind (Z.eqb (zho_n st) w) + ind (Z.eqb (zho_m st) w)) ->
  pcount (b_heap st') (b_hmax st') (b_node st) = 0 ->
  pcount (b_heap st) (b_hmax st) (zho_n st) = 0 ->
  pcount (b_heap st) (b_hmax st) (zho_m st) = 0 ->
  pcount (b_heap st) (b_hmax st) (b_node st) = 0 ->
  zho_n st < b_node st -> zho_m st < b_node st ->
  forall p i d,
  b_hmax st <= p < HEAP_SIZE ->
  1 <= pcount (b_heap st) (b_hmax st) (b_heap st p) ->
  elems <= i < b_node st ->
  dpow (b_tree st') d (b_heap st p) = i ->
  (forall k, (1 <= k < d)%nat ->
     1 <= pcount (b_heap st') (b_hmax st')
            (dpow (b_tree st') k (b_heap st p))) ->
  fibZ (d + 1) * t_freq (b_tree st) (b_heap st p)
  <= t_freq (b_tree st) i.
Proof.
  intros st st' LP Ehmz Endz Hhs Hfn_nn Hfn_mm Hordp Hlp2 HLPn HLPm Hfib
         Hpark_frozen Hslot_n Hslot_m Efrq_nd Efrq_o Edad_n Edad_m Edad_o
         Hpc' Hpcnd' Hpc_n0 Hpc_m0 Hpc_nd0 Hn_lt Hm_lt
         p i d Hpo Hxpc Hi' Hch Hint.
  set (hp := b_heap st) in *.
  set (hm := b_hmax st) in *.
  set (nd := b_node st) in *.
  set (tr := b_tree st) in *.
  set (nn := zho_n st) in *.
  set (mm := zho_m st) in *.
  set (x := hp p) in *.
  assert (Hxn : x <> nn) by (intro E; rewrite E in Hxpc; lia).
  assert (Hxm : x <> mm) by (intro E; rewrite E in Hxpc; lia).
  assert (Hxd : x <> nd) by (intro E; rewrite E in Hxpc; lia).
  assert (Hind : i <> nd) by lia.
      assert (Havoid : forall k, (k < d)%nat ->
                dpow (b_tree st') k x <> nn /\ dpow (b_tree st') k x <> mm).
      { intros k Hk. destruct k as [|k1].
        - cbn [dpow]. split; assumption.
        - split; intro E.
          + assert (Ednd : dpow (b_tree st') (S (S k1)) x = nd)
              by (rewrite dpow_dad, E; exact Edad_n).
            destruct (Nat.eq_dec (S (S k1)) d) as [Ed|Hne].
            * rewrite Ed in Ednd. congruence.
            * specialize (Hint (S (S k1)) ltac:(lia)).
              rewrite Ednd, Hpcnd' in Hint. lia.
          + assert (Ednd : dpow (b_tree st') (S (S k1)) x = nd)
              by (rewrite dpow_dad, E; exact Edad_m).
            destruct (Nat.eq_dec (S (S k1)) d) as [Ed|Hne].
            * rewrite Ed in Ednd. congruence.
            * specialize (Hint (S (S k1)) ltac:(lia)).
              rewrite Ednd, Hpcnd' in Hint. lia. }
      assert (Htrans : forall j, (j <= d)%nat ->
                dpow (b_tree st') j x = dpow tr j x).
      { apply dpow_transport. intros k Hk.
        destruct (Havoid k Hk) as [H1 H2]. apply Edad_o; assumption. }
      assert (Hold_pc : forall k, (1 <= k < d)%nat ->
                1 <= pcount hp hm (dpow tr k x)).
      { intros k Hk.
        specialize (Hint k ltac:(lia)).
        rewrite (Htrans k ltac:(lia)) in Hint.
        rewrite Hpc' in Hint.
        destruct (Havoid k ltac:(lia)) as [H1 H2].
        rewrite (Htrans k ltac:(lia)) in H1, H2.
        replace (Z.eqb nn (dpow tr k x)) with false in Hint
          by (symmetry; apply Z.eqb_neq; congruence).
        replace (Z.eqb mm (dpow tr k x)) with false in Hint
          by (symmetry; apply Z.eqb_neq; congruence).
        cbn [ind] in Hint. lia. }
      apply (Hfib p i d Hpo Hi').
      + apply dchain_dpow. fold x.
        rewrite <- (Htrans d ltac:(lia)). exact Hch.
      + exact Hold_pc.
Qed.

Lemma zhf_fib_step : forall (st st' : BtSt) (LP : Z),
  b_hmax st' = b_hmax st - 2 ->
  b_node st' = b_node st + 1 ->
  b_hmax st <= HEAP_SIZE ->
  0 <= t_freq (b_tree st) (zho_n st) ->
  0 <= t_freq (b_tree st) (zho_m st) ->
  (forall p, b_hmax st <= p < HEAP_SIZE ->
     elems <= t_dad (b_tree st) (b_heap st p) < b_node st) ->
  (forall p, b_hmax st <= p < HEAP_SIZE ->
     t_freq (b_tree st) (b_heap st p) <= LP) ->
  LP <= t_freq (b_tree st) (zho_n st) ->
  LP <= t_freq (b_tree st) (zho_m st) ->
  (forall p i d, b_hmax st <= p < HEAP_SIZE ->
     elems <= i < b_node st ->
     dchainN (b_tree st) (b_heap st p) i d ->
     (forall k, (1 <= k < d)%nat ->
        1 <= pcount (b_heap st) (b_hmax st)
               (dpow (b_tree st) k (b_heap st p))) ->
     fibZ (d + 1) * t_freq (b_tree st) (b_heap st p)
     <= t_freq (b_tree st) i) ->
  (forall p, b_hmax st <= p < HEAP_SIZE -> b_heap st' p = b_heap st p) ->
  b_heap st' (b_hmax st - 1) = zho_n st ->
  b_heap st' (b_hmax st - 2) = zho_m st ->
  t_freq (b_tree st') (b_node st)
    = t_freq (b_tree st) (zho_n st) + t_freq (b_tree st) (zho_m st) ->
  (forall x, x <> b_node st ->
     t_freq (b_tree st') x = t_freq (b_tree st) x) ->
  t_dad (b_tree st') (zho_n st) = b_node st ->
  t_dad (b_tree st') (zho_m st) = b_node st ->
  (forall w, w <> zho_n st -> w <> zho_m st ->
     t_dad (b_tree st') w = t_dad (b_tree st) w) ->
  (forall w, pcount (b_heap st') (b_hmax st') w
     = pcount (b_heap st) (b_hmax st) w
       + ind (Z.eqb (zho_n st) w) + ind (Z.eqb (zho_m st) w)) ->
  pcount (b_heap st') (b_hmax st') (b_node st) = 0 ->
  pcount (b_heap st) (b_hmax st) (zho_n st) = 0 ->
  pcount (b_heap st) (b_hmax st) (zho_m st) = 0 ->
  pcount (b_heap st) (b_hmax st) (b_node st) = 0 ->
  zho_n st < b_node st -> zho_m st < b_node st ->
  forall p i d, b_hmax st' <= p < HEAP_SIZE ->
  elems <= i < b_node st' ->
  dchainN (b_tree st') (b_heap st' p) i d ->
  (forall k, (1 <= k < d)%nat ->
     1 <= pcount (b_heap st') (b_hmax st')
            (dpow (b_tree st') k (b_heap st' p))) ->
  fibZ (d + 1) * t_freq (b_tree st') (b_heap st' p)
  <= t_freq (b_tree st') i.
Proof.
  intros st st' LP Ehmz Endz Hhs Hfn_nn Hfn_mm Hordp Hlp2 HLPn HLPm Hfib
         Hpark_frozen Hslot_n Hslot_m Efrq_nd Efrq_o Edad_n Edad_m Edad_o
         Hpc' Hpcnd' Hpc_n0 Hpc_m0 Hpc_nd0 Hn_lt Hm_lt.
  set (hp := b_heap st) in *.
  set (hm := b_hmax st) in *.
  set (nd := b_node st) in *.
  set (tr := b_tree st) in *.
  set (nn := zho_n st) in *.
  set (mm := zho_m st) in *.
  assert (Hparked_facts : forall w, 1 <= pcount hp hm w ->
            w <> nd /\ elems <= t_dad tr w < nd /\ t_freq tr w <= LP).
  { intros w Hw.
    assert (Hwnd : w <> nd)
      by (intro E; rewrite E in Hw; lia).
    unfold pcount in Hw.
    destruct (wcount_pos_inv hp hm (Z.to_nat (HEAP_SIZE - hm)) w Hw)
      as (q & Hq & Hqe).
    rewrite Z2Nat.id in Hq by lia.
    assert (Hq' : hm <= q < HEAP_SIZE) by lia.
    split; [exact Hwnd|]. split.
    - pose proof (Hordp q Hq') as Hdr. rewrite Hqe in Hdr. exact Hdr.
    - rewrite <- Hqe. apply Hlp2. exact Hq'. }
 intros p i d Hp Hi Hch Hint.
    apply (proj1 (dchain_dpow (b_tree st') d (b_heap st' p) i)) in Hch.
    rewrite Ehmz in Hp. fold hm in Hp.
    rewrite Endz in Hi. fold nd in Hi.
    destruct (Z.eqb_spec p (hm - 2)) as [->|Hpa].
    { (* start = mm; Hch/Hint stay at the raw slot read so dpow's argument
         is an application, never the tower-valued let variable mm (kernel
         conversion diverges expanding it inside dpow casts) *)
      rewrite Hslot_m.
      destruct d as [|d1].
      - cbn [dpow] in Hch. rewrite Hslot_m in Hch. subst i.
        change (fibZ (0 + 1)) with 1. lia.
      - assert (E1 : dpow (b_tree st') 1 (b_heap st' (hm - 2)) = nd)
          by (cbn [dpow]; rewrite Hslot_m; exact Edad_m).
        destruct d1 as [|d2].
        + cbn [dpow] in Hch. rewrite Hslot_m in Hch.
          rewrite Edad_m in Hch. subst i.
          rewrite Efrq_nd, (Efrq_o mm) by lia.
          change (fibZ (1 + 1)) with 1.
          pose proof Hfn_nn. lia.
        + exfalso.
          specialize (Hint 1%nat ltac:(lia)).
          rewrite E1, Hpcnd' in Hint. lia. }
    destruct (Z.eqb_spec p (hm - 1)) as [->|Hpb].
    { (* start = nn; same slot-read discipline as the mm branch *)
      rewrite Hslot_n.
      destruct d as [|d1].
      - cbn [dpow] in Hch. rewrite Hslot_n in Hch. subst i.
        change (fibZ (0 + 1)) with 1. lia.
      - assert (E1 : dpow (b_tree st') 1 (b_heap st' (hm - 1)) = nd)
          by (cbn [dpow]; rewrite Hslot_n; exact Edad_n).
        destruct d1 as [|d2].
        + cbn [dpow] in Hch. rewrite Hslot_n in Hch.
          rewrite Edad_n in Hch. subst i.
          rewrite Efrq_nd, (Efrq_o nn) by lia.
          change (fibZ (1 + 1)) with 1.
          pose proof Hfn_mm. lia.
        + exfalso.
          specialize (Hint 1%nat ltac:(lia)).
          rewrite E1, Hpcnd' in Hint. lia. }
    (* start = an old parked value *)
    assert (Hpo : hm <= p < HEAP_SIZE) by lia.
    rewrite (Hpark_frozen p Hpo) in Hch, Hint |- *.
    set (x := hp p) in *.
    assert (Hxpc : 1 <= pcount hp hm x) by (apply pcount_member; exact Hpo).
    assert (Hxn : x <> nn) by (intro E; rewrite E in Hxpc; lia).
    assert (Hxm : x <> mm) by (intro E; rewrite E in Hxpc; lia).
    assert (Hxd : x <> nd)
      by (intro E; rewrite E in Hxpc; lia).
    assert (Efx : t_freq (b_tree st') x = t_freq tr x)
      by (apply Efrq_o; exact Hxd).
    destruct (Z.eqb_spec i nd) as [->|Hind].
    - (* endpoint nd *)
      destruct d as [|d1].
      { cbn [dpow] in Hch. congruence. }
      destruct d1 as [|d2].
      { exfalso. cbn [dpow] in Hch.
        rewrite (Edad_o x Hxn Hxm) in Hch.
        destruct (Hparked_facts x Hxpc) as (_ & Hdx & _). lia. }
      (* d = S (S d2): delegated to zhf_fib_nd *)
      rewrite Efrq_nd, Efx.
      exact (zhf_fib_nd st st' LP Ehmz Endz Hhs Hfn_nn Hfn_mm Hordp Hlp2
               HLPn HLPm Hfib
               Hpark_frozen Hslot_n Hslot_m Efrq_nd Efrq_o Edad_n Edad_m
               Edad_o Hpc' Hpcnd' Hpc_n0 Hpc_m0 Hpc_nd0 Hn_lt Hm_lt
               p d2 Hpo Hxpc Hch Hint).
    - (* endpoint below nd: delegated to zhf_fib_lt *)
      assert (Hi' : elems <= i < nd) by lia.
      rewrite Efx, (Efrq_o i) by lia.
      exact (zhf_fib_lt st st' LP Ehmz Endz Hhs Hfn_nn Hfn_mm Hordp Hlp2
               HLPn HLPm Hfib
               Hpark_frozen Hslot_n Hslot_m Efrq_nd Efrq_o Edad_n Edad_m
               Edad_o Hpc' Hpcnd' Hpc_n0 Hpc_m0 Hpc_nd0 Hn_lt Hm_lt
               p i d Hpo Hxpc Hi' Hch Hint).
Qed.

(** ** One trip preserves the invariant *)

Lemma zhf_step : forall st LP st',
  M0 <= 65535 ->
  maxc1 < elems -> 0 < elems <= L_CODES -> hlen1 <= L_CODES ->
  FibCore st LP -> StepPre st ->
  (bt_step st = BtCont st' \/ bt_step st = BtDone st') ->
  exists LP',
    FibCore st' LP'
    /\ (2 <= b_hlen st' -> StepPre st')
    /\ b_hlen st' = b_hlen st - 1
    /\ (b_hlen st = 2 -> b_heap st' 1 = b_node st).
Proof.
  intros st LP st' Hmass Hme Hel Hh1 Hcore Hpre Hstep.
  destruct (bt_step_minima st Hpre) as (Hmin1 & Hmin2 & Hcnt2 & Hiv).
  destruct (Hiv st' Hstep) as (Endz & Ehlz & Hcnt6 & Hpres).
  clear Hiv.
  destruct Hcore as [Hcen Hnn Hlp1 Hlp2 Hwmono HmassI Hfib].
  pose proof (sp_hlen _ Hpre) as Hhl2.
  pose proof (sp_cap _ Hpre) as [Hgap Hhs].
  pose proof (sp_fresh _ Hpre) as Hfr.
  destruct (census_step elems maxc1 t1 hlen1 st st' Hme Hel Hh1
              Hhl2 Hgap Hhs Hstep Hcen)
    as (Hcen' & _ & Ehmz & _ & Hroot2).
  pose proof Hcen as Hcen_c.
  destruct Hcen_c as [Hnd0 Ehm0 Ehl0 Hcons0 Hdad0 Hord0 Hfrq0 Hdlf0].
  pose proof (bt_step_succ st st' Hstep) as Est'.
  assert (Etr' : b_tree st'
                 = t_setdad (t_setdad (t_setfreq (b_tree st) (b_node st)
                     (t_freq (b_tree st) (zho_n st)
                      + t_freq (b_tree st) (zho_m st)))
                   (zho_m st) (b_node st)) (zho_n st) (b_node st)).
  { rewrite Est'. unfold zho_succ, zho_m, zho_hp2, zho_n. cbv zeta.
    cbn [b_tree]. reflexivity. }
  assert (Ehp' : b_heap st'
                 = pqdownheap (b_tree st') (b_dep st')
                     (zset (zset (zset (zho_hp2 st) (b_hmax st - 1) (zho_n st))
                                 (b_hmax st - 1 - 1) (zho_m st))
                           1 (b_node st))
                     (b_hlen st - 1) 1).
  { rewrite Est'. unfold zho_succ, zho_m, zho_hp2, zho_n. cbv zeta.
    cbn [b_heap b_tree b_dep]. reflexivity. }
  replace (b_hmax st - 1 - 1) with (b_hmax st - 2) in Ehp' by lia.
  set (hp := b_heap st) in *.
  set (hl := b_hlen st) in *.
  set (hm := b_hmax st) in *.
  set (nd := b_node st) in *.
  set (tr := b_tree st) in *.
  set (nn := zho_n st) in *.
  set (hp2 := zho_hp2 st) in *.
  set (mm := zho_m st) in *.
  (* --- window memberships and counts --- *)
  assert (Hn_in : In nn (zho_win hp hl))
    by (apply (zho_win_in hp hl 1); lia).
  assert (Hm_in2 : In mm (zho_win hp2 (hl - 1)))
    by (apply (zho_win_in hp2 (hl - 1) 1); lia).
  destruct (in_split mm (zho_win hp2 (hl - 1)) Hm_in2) as (w1 & w2 & Ew).
  set (rest := w1 ++ w2).
  assert (Hp2rest : Permutation (zho_win hp2 (hl - 1)) (mm :: rest)).
  { rewrite Ew. symmetry. apply Permutation_middle. }
  assert (Hcrest : forall x,
      Z.of_nat (count_occ Z.eq_dec rest x)
      = lcount hp2 (hl - 1) x - ind (Z.eqb mm x)).
  { intro x.
    pose proof (proj1 (Permutation_count_occ Z.eq_dec _ _) Hp2rest x) as Hc.
    assert (Hz : Z.of_nat (count_occ Z.eq_dec (zho_win hp2 (hl - 1)) x)
                 = lcount hp2 (hl - 1) x)
      by (apply zho_win_count; lia).
    rewrite Hc in Hz. rewrite (zho_count_cons mm rest x) in Hz. lia. }
  assert (HP1 : Permutation (zho_win hp hl) (nn :: mm :: rest)).
  { apply zho_perm_counts. intro x.
    rewrite (zho_win_count hp hl x) by lia.
    rewrite (zho_count_cons nn (mm :: rest) x).
    rewrite (zho_count_cons mm rest x).
    rewrite Hcrest.
    pose proof (Hcnt2 x). lia. }
  assert (HP2 : Permutation (zho_win (b_heap st') (b_hlen st')) (nd :: rest)).
  { apply zho_perm_counts. intro x.
    rewrite (zho_win_count (b_heap st') (b_hlen st') x) by lia.
    rewrite Hcnt6.
    rewrite (zho_count_cons nd rest x).
    rewrite Hcrest. lia. }
  assert (Hrest_val : forall v, In v rest ->
            exists q, 1 <= q <= hl /\ hp q = v).
  { intros v Hv.
    assert (Hc : (count_occ Z.eq_dec rest v > 0)%nat)
      by (apply count_occ_In; exact Hv).
    pose proof (Hcrest v) as Hc'.
    pose proof (ind_0_1 (Z.eqb mm v)).
    assert (H2 : 1 <= lcount hp2 (hl - 1) v) by lia.
    pose proof (Hcnt2 v) as Hc2.
    pose proof (ind_0_1 (Z.eqb nn v)).
    assert (H3 : 1 <= lcount hp hl v) by lia.
    exact (lcount_pos_inv hp hl v H3). }
  assert (Hrest_lt : forall v, In v rest -> v < nd).
  { intros v Hv. destruct (Hrest_val v Hv) as (q & Hq & <-).
    apply Hfr. exact Hq. }
  assert (Hlc1 : forall x, lcount hp hl x <= 1).
  { intro x. pose proof (Hcons0 x).
    pose proof (total_le_1 elems maxc1 t1 nd x Hme).
    pose proof (wcount_nonneg hp hm (Z.to_nat (HEAP_SIZE - hm)) x).
    unfold pcount in *. lia. }
  assert (Hm_c2 : 1 <= lcount hp2 (hl - 1) mm)
    by (apply (lcount_member hp2 (hl - 1) 1); lia).
  assert (Hnm_ne : nn <> mm).
  { intro E. pose proof (Hcnt2 mm) as Hc.
    rewrite <- E in Hc. rewrite Z.eqb_refl in Hc. cbn [ind] in Hc.
    pose proof (Hlc1 mm). rewrite <- E in *. lia. }
  assert (Hm_lc : 1 <= lcount hp hl mm).
  { pose proof (Hcnt2 mm) as Hc.
    pose proof (ind_0_1 (Z.eqb nn mm)). lia. }
  assert (Hm_orig : exists q, 1 <= q <= hl /\ hp q = mm)
    by (apply lcount_pos_inv; exact Hm_lc).
  assert (Hn_lt : nn < nd) by (apply (Hfr 1); lia).
  assert (Hm_lt : mm < nd)
    by (destruct Hm_orig as (q & Hq & <-); apply Hfr; exact Hq).
  assert (Hnd_bound : 0 <= nd < 65536)
    by (unfold L_CODES in *; lia).
  assert (Hnd_lc : lcount hp hl nd = 0 /\ pcount hp hm nd = 0).
  { pose proof (Hcons0 nd) as Hc.
    rewrite (live_b_false_high t1 maxc1 nd) in Hc by lia.
    replace ((elems <=? nd) && (nd <? nd)) with false in Hc
      by (symmetry; apply andb_false_intro2; apply Z.ltb_ge; lia).
    cbn [ind] in Hc.
    pose proof (wcount_nonneg hp 1 (Z.to_nat hl) nd).
    pose proof (wcount_nonneg hp hm (Z.to_nat (HEAP_SIZE - hm)) nd).
    unfold lcount, pcount in *. lia. }
  assert (Hpc_n : pcount hp hm nn = 0).
  { pose proof (Hcons0 nn).
    pose proof (total_le_1 elems maxc1 t1 nd nn Hme).
    assert (1 <= lcount hp hl nn) by (apply (lcount_member hp hl 1); lia).
    pose proof (wcount_nonneg hp hm (Z.to_nat (HEAP_SIZE - hm)) nn).
    unfold pcount in *. lia. }
  assert (Hpc_m : pcount hp hm mm = 0).
  { pose proof (Hcons0 mm).
    pose proof (total_le_1 elems maxc1 t1 nd mm Hme).
    pose proof (wcount_nonneg hp hm (Z.to_nat (HEAP_SIZE - hm)) mm).
    unfold pcount in *. lia. }
  assert (Hfn_nn : 0 <= t_freq tr nn).
  { apply Hnn.
    apply (zhfn_live_val_range st nn ltac:(lia) Hme Hcen).
    apply (lcount_member hp hl 1). lia. }
  assert (Hfn_mm : 0 <= t_freq tr mm).
  { apply Hnn.
    exact (zhfn_live_val_range st mm ltac:(lia) Hme Hcen Hm_lc). }
  set (fv := t_freq tr nn + t_freq tr mm) in *.
  assert (Hpark_frozen : forall p, hm <= p < HEAP_SIZE ->
            b_heap st' p = hp p).
  { intros p Hp. rewrite Ehp'.
    rewrite pqdownheap_outside by lia.
    rewrite zset_other by lia.
    rewrite zset_other by lia.
    rewrite zset_other by lia.
    unfold hp2, zho_hp2, SMALLEST.
    fold hp. fold hl.
    rewrite pqdownheap_outside by lia.
    rewrite zset_other by lia.
    reflexivity. }
  assert (Hslot_n : b_heap st' (hm - 1) = nn).
  { rewrite Ehp'. rewrite pqdownheap_outside by lia.
    rewrite zset_other by lia.
    rewrite zset_other by lia.
    apply zset_same. }
  assert (Hslot_m : b_heap st' (hm - 2) = mm).
  { rewrite Ehp'. rewrite pqdownheap_outside by lia.
    rewrite zset_other by lia.
    apply zset_same. }
  (* --- freq/dad reads at the successor --- *)
  assert (Hfv_nn : 0 <= fv).
  { unfold fv. lia. }
  assert (Hfv_ub : fv <= 65535).
  { assert (Hz : zsumF (zho_win hp hl) (t_freq tr) = M0) by exact HmassI.
    rewrite (zsumF_perm (t_freq tr) _ _ HP1) in Hz.
    cbn [zsumF fold_right] in Hz. fold (zsumF rest (t_freq tr)) in Hz.
    assert (0 <= zsumF rest (t_freq tr))
      by (apply zsumF_nonneg; intros v Hv; apply Hnn;
          destruct (Hrest_val v Hv) as (q & Hq & Hqe);
          rewrite <- Hqe;
          apply (zhfn_live_val_range st (hp q) ltac:(lia) Hme Hcen);
          apply lcount_member; exact Hq).
    unfold fv. lia. }
  assert (Efrq_nd : t_freq (b_tree st') nd = fv).
  { rewrite Etr'. rewrite !t_freq_setdad.
    rewrite zho_t_freq_setfreq_same.
    unfold u16. apply Z.mod_small. lia. }
  assert (Efrq_o : forall x, x <> nd -> t_freq (b_tree st') x = t_freq tr x).
  { intros x Hx. rewrite Etr'. apply trip_freq. exact Hx. }
  assert (Edad : forall x, t_dad (b_tree st') x
                 = if Z.eqb x nn then nd
                   else if Z.eqb x mm then nd else t_dad tr x).
  { intro x. rewrite Etr'. apply trip_dad; [exact Hnm_ne | exact Hnd_bound]. }
  assert (Edad_n : t_dad (b_tree st') nn = nd).
  { rewrite (Edad nn), Z.eqb_refl. reflexivity. }
  assert (Edad_m : t_dad (b_tree st') mm = nd).
  { rewrite (Edad mm).
    replace (Z.eqb mm nn) with false
      by (symmetry; apply Z.eqb_neq; congruence).
    rewrite Z.eqb_refl. reflexivity. }
  assert (Edad_o : forall w, w <> nn -> w <> mm ->
            t_dad (b_tree st') w = t_dad tr w).
  { intros w Hw1 Hw2. rewrite (Edad w).
    replace (Z.eqb w nn) with false
      by (symmetry; apply Z.eqb_neq; exact Hw1).
    replace (Z.eqb w mm) with false
      by (symmetry; apply Z.eqb_neq; exact Hw2).
    reflexivity. }
  (* --- watermark facts --- *)
  assert (Enn1 : hp 1 = nn) by reflexivity.
  assert (HLPn : LP <= t_freq tr nn).
  { rewrite <- Enn1. apply Hlp1. lia. }
  assert (HLPm : LP <= t_freq tr mm).
  { destruct Hm_orig as (q & Hq & Hqe). rewrite <- Hqe. apply Hlp1. lia. }
  assert (Hfnm : t_freq tr nn <= t_freq tr mm).
  { destruct Hm_orig as (q & Hq & Hqe).
    pose proof (Hmin1 q Hq) as Hs. rewrite Hqe in Hs.
    exact (zho_smaller_freq_le _ _ _ _ Hs). }
  set (LP' := t_freq tr mm).
  (* --- the successor parked-window count --- *)
  assert (Hpc' : forall w, pcount (b_heap st') (b_hmax st') w
                 = pcount hp hm w + ind (Z.eqb nn w) + ind (Z.eqb mm w)).
  { intro w. unfold pcount. rewrite Ehmz.
    fold hm.
    replace (Z.to_nat (HEAP_SIZE - (hm - 2)))
      with (S (S (Z.to_nat (HEAP_SIZE - hm)))) by lia.
    unfold wcount.
    rewrite wsum_split_first.
    rewrite wsum_split_first.
    replace (hm - 2 + 1) with (hm - 1) by lia.
    replace (hm - 1 + 1) with hm by lia.
    rewrite Hslot_m, Hslot_n.
    fold (wcount (b_heap st') hm (Z.to_nat (HEAP_SIZE - hm)) w).
    rewrite (wcount_ext_window (b_heap st') hp hm
               (Z.to_nat (HEAP_SIZE - hm)) w)
      by (intros i Hi; apply Hpark_frozen;
          rewrite Z2Nat.id in Hi by lia; lia).
    fold (wcount hp hm (Z.to_nat (HEAP_SIZE - hm)) w).
    fold (pcount hp hm w). cbv beta. lia. }
  assert (Hpcnd' : pcount (b_heap st') (b_hmax st') nd = 0).
  { rewrite Hpc'.
    replace (Z.eqb nn nd) with false by (symmetry; apply Z.eqb_neq; lia).
    replace (Z.eqb mm nd) with false by (symmetry; apply Z.eqb_neq; lia).
    cbn [ind]. destruct Hnd_lc as [_ HndP]. lia. }
  (* --- clause preservations --- *)
  assert (Hnn' : forall x, 0 <= x < b_node st' -> 0 <= t_freq (b_tree st') x).
  { intros x Hxr. destruct (Z.eqb_spec x nd) as [->|Hx].
    - rewrite Efrq_nd. exact Hfv_nn.
    - rewrite (Efrq_o x Hx). apply Hnn. rewrite Endz in Hxr. lia. }
  assert (Hlp1' : forall p, 1 <= p <= b_hlen st' ->
            LP' <= t_freq (b_tree st') (b_heap st' p)).
  { intros p Hp.
    assert (Hc : 1 <= lcount (b_heap st') (b_hlen st') (b_heap st' p))
      by (apply lcount_member; exact Hp).
    rewrite Hcnt6 in Hc.
    destruct (Z.eqb_spec (b_heap st' p) nd) as [Ev|Hv].
    - rewrite Ev, Efrq_nd. unfold LP', fv. pose proof Hfn_nn. lia.
    - replace (Z.eqb nd (b_heap st' p)) with false in Hc
        by (symmetry; apply Z.eqb_neq; congruence).
      cbn [ind] in Hc.
      pose proof (ind_0_1 (Z.eqb mm (b_heap st' p))).
      assert (H2 : 1 <= lcount hp2 (hl - 1) (b_heap st' p)) by lia.
      destruct (lcount_pos_inv hp2 (hl - 1) _ H2) as (q & Hq & Hqe).
      rewrite (Efrq_o _ Hv).
      rewrite <- Hqe.
      apply (zho_smaller_freq_le tr (b_dep st)).
      apply Hmin2. lia. }
  assert (Hlp2' : forall p, b_hmax st' <= p < HEAP_SIZE ->
            t_freq (b_tree st') (b_heap st' p) <= LP').
  { intros p Hp. rewrite Ehmz in Hp. fold hm in Hp.
    destruct (Z.eqb_spec p (hm - 2)) as [->|Hp2].
    - rewrite Hslot_m. rewrite (Efrq_o mm) by lia. unfold LP'. lia.
    - destruct (Z.eqb_spec p (hm - 1)) as [->|Hp1].
      + rewrite Hslot_n. rewrite (Efrq_o nn) by lia. exact Hfnm.
      + assert (Hpo : hm <= p < HEAP_SIZE) by lia.
        rewrite (Hpark_frozen p Hpo).
        assert (Hne : hp p <> nd).
        { intro E.
          assert (1 <= pcount hp hm nd)
            by (rewrite <- E; apply pcount_member; exact Hpo).
          destruct Hnd_lc. lia. }
        rewrite (Efrq_o _ Hne).
        pose proof (Hlp2 p Hpo). unfold LP'. lia. }
  assert (Hwmono' : forall p q, b_hmax st' <= p -> p <= q -> q < HEAP_SIZE ->
            t_freq (b_tree st') (b_heap st' q)
            <= t_freq (b_tree st') (b_heap st' p)).
  { intros p q Hp Hpq Hq. rewrite Ehmz in Hp. fold hm in Hp.
    assert (Hval : forall r, hm <= r < HEAP_SIZE ->
              t_freq (b_tree st') (b_heap st' r) <= LP).
    { intros r Hr. rewrite (Hpark_frozen r Hr).
      assert (Hne : hp r <> nd).
      { intro E.
        assert (1 <= pcount hp hm nd)
          by (rewrite <- E; apply pcount_member; exact Hr).
        destruct Hnd_lc. lia. }
      rewrite (Efrq_o _ Hne). apply Hlp2. exact Hr. }
    destruct (Z.eqb_spec p (hm - 2)) as [->|Hpa].
    - rewrite Hslot_m, (Efrq_o mm) by lia.
      destruct (Z.eqb_spec q (hm - 2)) as [->|Hqa].
      + rewrite Hslot_m, (Efrq_o mm) by lia. lia.
      + destruct (Z.eqb_spec q (hm - 1)) as [->|Hqb].
        * rewrite Hslot_n, (Efrq_o nn) by lia. exact Hfnm.
        * assert (Hqo : hm <= q < HEAP_SIZE) by lia.
          pose proof (Hval q Hqo). lia.
    - destruct (Z.eqb_spec p (hm - 1)) as [->|Hpb].
      + rewrite Hslot_n, (Efrq_o nn) by lia.
        destruct (Z.eqb_spec q (hm - 1)) as [->|Hqb].
        * rewrite Hslot_n, (Efrq_o nn) by lia. lia.
        * assert (Hqo : hm <= q < HEAP_SIZE) by lia.
          pose proof (Hval q Hqo). lia.
      + assert (Hpo : hm <= p < HEAP_SIZE) by lia.
        assert (Hqo : hm <= q < HEAP_SIZE) by lia.
        rewrite (Hpark_frozen p Hpo), (Hpark_frozen q Hqo).
        assert (Hnep : hp p <> nd).
        { intro E.
          assert (1 <= pcount hp hm nd)
            by (rewrite <- E; apply pcount_member; exact Hpo).
          destruct Hnd_lc. lia. }
        assert (Hneq : hp q <> nd).
        { intro E.
          assert (1 <= pcount hp hm nd)
            by (rewrite <- E; apply pcount_member; exact Hqo).
          destruct Hnd_lc. lia. }
        rewrite (Efrq_o _ Hnep), (Efrq_o _ Hneq).
        apply Hwmono; lia. }
  assert (Hmass' : zsumF (zho_win (b_heap st') (b_hlen st'))
                     (t_freq (b_tree st')) = M0).
  { rewrite (zsumF_perm (t_freq (b_tree st')) _ _ HP2).
    cbn [zsumF fold_right].
    fold (zsumF rest (t_freq (b_tree st'))).
    rewrite Efrq_nd.
    rewrite (zsumF_ext_in (t_freq (b_tree st')) (t_freq tr) rest)
      by (intros v Hv; apply Efrq_o; pose proof (Hrest_lt v Hv); lia).
    assert (Hz : zsumF (zho_win hp hl) (t_freq tr) = M0) by exact HmassI.
    rewrite (zsumF_perm (t_freq tr) _ _ HP1) in Hz.
    cbn [zsumF fold_right] in Hz. fold (zsumF rest (t_freq tr)) in Hz.
    unfold fv. lia. }
  (* --- the fib clause --- *)
  assert (Hparked_facts : forall w, 1 <= pcount hp hm w ->
            w <> nd /\ elems <= t_dad tr w < nd /\ t_freq tr w <= LP).
  { intros w Hw.
    assert (Hwnd : w <> nd)
      by (intro E; rewrite E in Hw; destruct Hnd_lc; lia).
    unfold pcount in Hw.
    destruct (wcount_pos_inv hp hm (Z.to_nat (HEAP_SIZE - hm)) w Hw)
      as (q & Hq & Hqe).
    rewrite Z2Nat.id in Hq by lia.
    assert (Hq' : hm <= q < HEAP_SIZE) by lia.
    split; [exact Hwnd|]. split.
    - pose proof (Hord0 q Hq') as [Hdr _]. rewrite Hqe in Hdr. exact Hdr.
    - rewrite <- Hqe. apply Hlp2. exact Hq'. }
  assert (Hfib' : forall p i d, b_hmax st' <= p < HEAP_SIZE ->
            elems <= i < b_node st' ->
            dchainN (b_tree st') (b_heap st' p) i d ->
            (forall k, (1 <= k < d)%nat ->
               1 <= pcount (b_heap st') (b_hmax st')
                      (dpow (b_tree st') k (b_heap st' p))) ->
            fibZ (d + 1) * t_freq (b_tree st') (b_heap st' p)
            <= t_freq (b_tree st') i).
  { refine (zhf_fib_step st st' LP Ehmz Endz ltac:(lia) Hfn_nn Hfn_mm _ Hlp2
              HLPn HLPm Hfib Hpark_frozen Hslot_n Hslot_m Efrq_nd Efrq_o
              Edad_n Edad_m Edad_o Hpc' Hpcnd' Hpc_n Hpc_m
              ltac:(destruct Hnd_lc; assumption) Hn_lt Hm_lt).
    intros p Hp. exact (proj1 (Hord0 p Hp)). }
  exists LP'.
  split; [|split; [|split]].
  - constructor; [exact Hcen' | exact Hnn' | exact Hlp1' | exact Hlp2'
                  | exact Hwmono' | exact Hmass' | exact Hfib'].
  - exact Hpres.
  - exact Ehlz.
  - exact Hroot2.
Qed.

(** ** The loop walk *)

Lemma zhf_loop : forall fuel st LP,
  M0 <= 65535 ->
  maxc1 < elems -> 0 < elems <= L_CODES -> hlen1 <= L_CODES ->
  FibCore st LP -> StepPre st ->
  match bt_loop fuel st with
  | Some stf => exists LPf, FibCore stf LPf /\ b_hlen stf = 1
                /\ b_heap stf 1 = b_node stf - 1
  | None => True
  end.
Proof.
  induction fuel as [|f IH]; intros st LP Hmass Hme Hel Hh1 Hcore Hpre.
  - cbn [bt_loop]. exact I.
  - cbn [bt_loop].
    destruct (bt_step st) as [st'|st'] eqn:Est.
    + assert (Hor : bt_step st = BtCont st' \/ bt_step st = BtDone st')
        by (left; exact Est).
      destruct (zhf_step st LP st' Hmass Hme Hel Hh1 Hcore Hpre Hor)
        as (LP' & Hcore' & Hpre' & Ehl' & _).
      assert (Hhl' : 2 <= b_hlen st').
      { rewrite bt_step_eq in Est.
        destruct (Z.leb_spec 2 (b_hlen st - 1)) as [Hle|Hgt];
          [lia | discriminate]. }
      exact (IH st' LP' Hmass Hme Hel Hh1 Hcore' (Hpre' Hhl')).
    + assert (Hor : bt_step st = BtCont st' \/ bt_step st = BtDone st')
        by (right; exact Est).
      destruct (zhf_step st LP st' Hmass Hme Hel Hh1 Hcore Hpre Hor)
        as (LP' & Hcore' & _ & Ehl' & Hroot).
      assert (Hhl2 : b_hlen st = 2).
      { rewrite bt_step_eq in Est.
        destruct (Z.leb_spec 2 (b_hlen st - 1)) as [Hle|Hgt];
          [discriminate |].
        pose proof (sp_hlen _ Hpre). lia. }
      assert (End' : b_node st' = b_node st + 1).
      { pose proof (cv_hl _ _ _ _ _ (fc_census _ _ Hcore')) as E1.
        pose proof (cv_hl _ _ _ _ _ (fc_census _ _ Hcore)) as E0.
        lia. }
      exists LP'. split; [exact Hcore'|]. split; [lia|].
      rewrite (Hroot Hhl2). lia.
Qed.

(** ** The exports *)

Theorem zho_fib_main : forall stf,
  0 < elems <= L_CODES -> maxc1 < elems ->
  2 <= hlen1 <= L_CODES ->
  (forall n, 0 <= n < elems -> 0 <= t_freq t1 n) ->
  wsum (fun x => ind (live_b t1 maxc1 x) * t_freq t1 x)
       0 (Z.to_nat elems) <= 65535 ->
  InitOut elems t1 hp1 hlen1 maxc1 ->
  bt_loop (Z.to_nat HEAP_SIZE) zhof_st0 = Some stf ->
  (* FIB-A: dad-chain Fibonacci for PARKED nodes with PARKED intermediates
     (the root's own dad slot is never written, so unrestricted chains can
     spin on entry garbage — countermodel in ZHOFibDefect.v; genuine
     Pass1Inv/bp_ord chains have parked intermediates) *)
  (forall p d, b_hmax stf <= p < HEAP_SIZE ->
     dchainN (b_tree stf) (b_heap stf p) (b_node stf - 1) d ->
     (forall k, (1 <= k < d)%nat ->
        1 <= pcount (b_heap stf) (b_hmax stf)
               (dpow (b_tree stf) k (b_heap stf p))) ->
     fibZ (d + 1) * t_freq (b_tree stf) (b_heap stf p)
     <= t_freq (b_tree stf) (b_node stf - 1))
  (* FIB-B: parked-window freq monotonicity, INCLUDING the root slot
     (hp3 = the post-epilogue window array) *)
  /\ (forall p q,
        b_hmax stf - 1 <= p -> p <= q -> q < HEAP_SIZE ->
        t_freq (b_tree stf)
          (zset (b_heap stf) (b_hmax stf - 1) (b_heap stf 1) q)
        <= t_freq (b_tree stf)
          (zset (b_heap stf) (b_hmax stf - 1) (b_heap stf 1) p))
  (* FIB-C: the root carries the live entry mass *)
  /\ t_freq (b_tree stf) (b_node stf - 1)
     = wsum (fun n => ind (live_b t1 maxc1 n) * t_freq t1 n)
            0 (Z.to_nat elems).
Proof.
  intros stf Hel Hme Hh1 Hnn Hmass Hio Hloop.
  destruct (zhf_entry Hel Hme Hh1 Hnn Hio) as (Hcore0 & Hpre0).
  pose proof (zhf_loop (Z.to_nat HEAP_SIZE) zhof_st0 0
                Hmass Hme Hel (proj2 Hh1) Hcore0 Hpre0) as HL.
  rewrite Hloop in HL.
  destruct HL as (LPf & Hcoref & Hhlf & Hrootf).
  assert (Hnd_rng : elems + 1 <= b_node stf).
  { pose proof (cv_hl _ _ _ _ _ (fc_census _ _ Hcoref)) as E1. lia. }
  split; [|split].
  - intros p d Hp Hch Hint.
    apply (fc_fib _ _ Hcoref p (b_node stf - 1) d Hp ltac:(lia) Hch Hint).
  - intros p q Hp Hpq Hq.
    destruct (Z.eqb_spec q (b_hmax stf - 1)) as [->|Hqz].
    + assert (Ep : p = b_hmax stf - 1) by lia. subst p.
      apply Z.le_refl.
    + destruct (Z.eqb_spec p (b_hmax stf - 1)) as [->|Hpz].
      * rewrite zset_same.
        rewrite zset_other by lia.
        assert (Hq' : b_hmax stf <= q < HEAP_SIZE) by lia.
        pose proof (fc_lp2 _ _ Hcoref q Hq').
        pose proof (fc_lp1 _ _ Hcoref 1 ltac:(lia)).
        lia.
      * rewrite zset_other by lia. rewrite zset_other by lia.
        apply (fc_wmono _ _ Hcoref); lia.
  - pose proof (fc_mass _ _ Hcoref) as HM.
    rewrite Hhlf in HM.
    unfold zho_win, zho_slots in HM.
    change (Z.to_nat 1) with 1%nat in HM.
    cbn [seq map zsumF fold_right] in HM.
    change (Z.of_nat 1) with 1 in HM.
    rewrite Hrootf in HM. lia.
Qed.

End ZHOFib.
