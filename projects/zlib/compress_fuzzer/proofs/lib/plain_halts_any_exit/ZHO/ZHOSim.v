(** * ZHOSim — the combine loop simulates Théry's [build] relation, so the
      built tree's weight is cover-minimal.

    OWNER: huffman-opt.  L2's simulation leg (STRATEGY-MEMO §3).  Joint
    walk of [bt_loop] carrying, per trip:
      - the landed [CensusInv] (BtCensus3.census_step — content/distinctness),
      - [StepPre] (ZHOHeap — heap order; [bt_step_minima] gives the two
        lex-minima, whose freq components make Théry's [one_step]),
      - the abstract forest [F : Z -> btree Z] (updated at the created
        index), with:
          (wtie)  sum_leaves zho_f (F (hp p)) = Z.to_nat (freq (hp p))
                  for live slots p,
          (wagg)  weight_tree_list zho_f (live forest)
                  = Z.to_nat (sum of created freqs),
          (btrace) forall T, build zho_f (live forest) T ->
                   build zho_f zho_forest0 T,
          (chld)  each created index's freq = the freq-sum of the parked
                  slots whose dad points at it,
          (ltot)  the live freq total = the entry live total.
    At [Some stf]: hlen = 1, the forest is [[F root]], [build_one] +
    (btrace) + Théry [build_correct] give cover-minimality; (wagg)
    converts the abstract weight to the created-freq sum (SIM-A); (chld),
    the root total (SIM-C) and the entry content (SIM-D) are exported for
    the model-side Fubini (ZHOFubini) and the assembly (ZHOMain).

    TRUST BOUNDARY: pure Gallina over the vendored Huffman library
    (coq-community/huffman, LGPL-2.1-or-later) + the model + Stdlib. *)

From Stdlib Require Import ZArith List Lia Bool Arith Sorting.Permutation.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff Trees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  BtWin BtStep BtCensus1 BtCensus2 BtCensus3 BtCensus4.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.ZHO Require Import ZHOHeap.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Huffman Require Import BTree WeightTree Ordered ISort OneStep Cover
  CoverMin Build.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

Section ZHOSim.

Variables (elems maxc1 : Z) (t1 : Tree) (dep1 hp1 : zarr) (hlen1 : Z).

(** the weight function: ENTRY freqs (live-symbol freqs never change
    through the loop; created indices never occur as leaves) *)
Definition zho_f : Z -> nat := fun s => Z.to_nat (t_freq t1 s).

Definition zho_st0 : BtSt :=
  {| b_tree := t1;
     b_heap := bt_heapify (Z.to_nat HEAP_SIZE) t1 dep1 hp1 hlen1 (hlen1 / 2);
     b_dep := dep1; b_hlen := hlen1; b_hmax := HEAP_SIZE; b_node := elems |}.

Definition zho_slots (hlen : Z) : list Z :=
  map Z.of_nat (seq 1 (Z.to_nat hlen)).
Definition zho_live_idx (st : BtSt) : list Z :=
  map (b_heap st) (zho_slots (b_hlen st)).
Definition zho_forest0 : list (btree Z) :=
  map (@leaf Z) (zho_live_idx zho_st0).

(** ** Helpers, stage 1: counts, window lists, fold sums *)

Lemma zho_smaller_freq_le : forall t dep a b,
  smaller t dep a b = true -> t_freq t a <= t_freq t b.
Proof.
  intros t dep a b H. unfold smaller in H.
  apply orb_true_iff in H.
  destruct H as [H|H].
  - apply Z.ltb_lt in H. lia.
  - apply andb_true_iff in H as [He _]. apply Z.eqb_eq in He. lia.
Qed.

Lemma zho_t_freq_setfreq_same : forall t i v,
  t_freq (t_setfreq t i v) i = u16 v.
Proof.
  intros t i v. unfold t_freq, t_setfreq. cbn [tr_fc].
  apply zset_same.
Qed.

Lemma zho_live_b_range : forall x,
  live_b t1 maxc1 x = true -> 0 <= x <= maxc1.
Proof.
  intros x H. unfold live_b in H.
  apply andb_true_iff in H as [H _].
  apply andb_true_iff in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.

(** window lists *)

Definition zho_win (a : zarr) (hlen : Z) : list Z := map a (zho_slots hlen).

Lemma zho_slots_last : forall h, 1 <= h ->
  zho_slots h = zho_slots (h - 1) ++ [h].
Proof.
  intros h Hh. unfold zho_slots.
  replace (Z.to_nat h) with (S (Z.to_nat (h - 1))) by lia.
  rewrite seq_S, map_app. cbn [map].
  do 2 f_equal. lia.
Qed.

Lemma zho_count_cons : forall (v : Z) l x,
  Z.of_nat (count_occ Z.eq_dec (v :: l) x)
  = ind (Z.eqb v x) + Z.of_nat (count_occ Z.eq_dec l x).
Proof.
  intros v l x.
  destruct (Z.eqb v x) eqn:Eb.
  - apply Z.eqb_eq in Eb.
    rewrite (count_occ_cons_eq Z.eq_dec l Eb). cbn [ind]. lia.
  - apply Z.eqb_neq in Eb.
    rewrite (count_occ_cons_neq Z.eq_dec l Eb). cbn [ind]. lia.
Qed.

Lemma zho_win_count : forall a h x, 0 <= h ->
  Z.of_nat (count_occ Z.eq_dec (zho_win a h) x) = lcount a h x.
Proof.
  intros a h x Hh.
  remember (Z.to_nat h) as k eqn:Ek. revert h Hh Ek.
  induction k as [|k IH]; intros h Hh Ek.
  - assert (h = 0) by lia. subst h.
    cbn. unfold lcount, wcount. cbn. reflexivity.
  - unfold zho_win. rewrite (zho_slots_last h) by lia.
    rewrite map_app, count_occ_app.
    rewrite Nat2Z.inj_add.
    fold (zho_win a (h - 1)).
    rewrite (IH (h - 1)) by lia.
    rewrite (lcount_shrink a h x) by lia.
    cbn [map].
    rewrite (zho_count_cons (a h) [] x).
    cbn [count_occ]. lia.
Qed.

Lemma zho_win_in : forall a h p, 1 <= p <= h -> In (a p) (zho_win a h).
Proof.
  intros a h p Hp. unfold zho_win, zho_slots.
  apply in_map. apply in_map_iff.
  exists (Z.to_nat p). split; [lia|].
  apply in_seq. lia.
Qed.

Lemma zho_win_in_inv : forall a h x,
  In x (zho_win a h) -> exists p, 1 <= p <= h /\ a p = x.
Proof.
  intros a h x H. unfold zho_win, zho_slots in H.
  apply in_map_iff in H as (q & Hq & Hin).
  apply in_map_iff in Hin as (qn & Hqn & Hin).
  apply in_seq in Hin.
  exists q. split; [lia | exact Hq].
Qed.

Lemma zho_perm_counts : forall l1 l2 : list Z,
  (forall x, Z.of_nat (count_occ Z.eq_dec l1 x)
             = Z.of_nat (count_occ Z.eq_dec l2 x)) ->
  Permutation l1 l2.
Proof.
  intros l1 l2 H.
  apply (Permutation_count_occ Z.eq_dec).
  intro x. specialize (H x). lia.
Qed.

(** fold sums over lists of indices *)

Definition zsumF (l : list Z) (g : Z -> Z) : Z :=
  fold_right (fun x acc => g x + acc) 0 l.

Lemma zsumF_perm : forall g l1 l2,
  Permutation l1 l2 -> zsumF l1 g = zsumF l2 g.
Proof.
  intros g l1 l2 H. induction H.
  - reflexivity.
  - cbn [zsumF fold_right]. unfold zsumF in IHPermutation. lia.
  - cbn [zsumF fold_right]. lia.
  - lia.
Qed.

Lemma zsumF_ext_in : forall g g' l,
  (forall x, In x l -> g x = g' x) -> zsumF l g = zsumF l g'.
Proof.
  intros g g' l H. induction l as [|v l IH].
  - reflexivity.
  - cbn [zsumF fold_right]. fold (zsumF l g). fold (zsumF l g').
    rewrite (H v) by (left; reflexivity).
    rewrite IH by (intros; apply H; right; assumption). reflexivity.
Qed.

Lemma zsumF_nonneg : forall g l,
  (forall x, In x l -> 0 <= g x) -> 0 <= zsumF l g.
Proof.
  intros g l H. induction l as [|v l IH]; cbn [zsumF fold_right]; [lia|].
  assert (0 <= g v) by (apply H; left; reflexivity).
  assert (0 <= zsumF l g) by (apply IH; intros; apply H; right; assumption).
  unfold zsumF in *. lia.
Qed.

Lemma zho_wsum_zero : forall lo k, wsum (fun _ => 0) lo k = 0.
Proof.
  intros lo k. revert lo. induction k as [|k IH]; intro lo; cbn [wsum]; [lia|].
  rewrite IH. lia.
Qed.

Lemma zsumF_counts : forall (l : list Z) (g : Z -> Z) (lo : Z) (k : nat),
  (forall v, In v l -> lo <= v < lo + Z.of_nat k) ->
  zsumF l g
  = wsum (fun x => Z.of_nat (count_occ Z.eq_dec l x) * g x) lo k.
Proof.
  induction l as [|v l IH]; intros g lo k Hin.
  - cbn [zsumF fold_right count_occ].
    rewrite <- (zho_wsum_zero lo k) at 1.
    apply wsum_ext. intros; cbn; lia.
  - cbn [zsumF fold_right]. fold (zsumF l g).
    rewrite (IH g lo k) by (intros; apply Hin; right; assumption).
    assert (Hv : lo <= v < lo + Z.of_nat k) by (apply Hin; left; reflexivity).
    rewrite (wsum_point_delta
               (fun x => Z.of_nat (count_occ Z.eq_dec l x) * g x)
               (fun x => Z.of_nat (count_occ Z.eq_dec (v :: l) x) * g x)
               lo k v Hv).
    + rewrite (zho_count_cons v l v). rewrite Z.eqb_refl. cbn [ind]. lia.
    + intros i Hi Hne. rewrite (zho_count_cons v l i).
      replace (Z.eqb v i) with false
        by (symmetry; apply Z.eqb_neq; congruence).
      cbn [ind]. lia.
Qed.

(** seq / filter counts (SIM-D) *)

Lemma zho_count_seq : forall (k : nat) (x : Z),
  Z.of_nat (count_occ Z.eq_dec (map Z.of_nat (seq 0 k)) x)
  = ind ((0 <=? x) && (x <? Z.of_nat k)).
Proof.
  induction k as [|k IH]; intro x.
  - cbn [seq map count_occ].
    change (Z.of_nat 0) with 0.
    destruct (Z.leb_spec 0 x); destruct (Z.ltb_spec x 0);
      cbn [andb ind Z.of_nat]; lia.
  - rewrite seq_S, map_app, count_occ_app. cbn [map].
    rewrite Nat2Z.inj_add, IH.
    rewrite (zho_count_cons (Z.of_nat (0 + k)) [] x).
    cbn [count_occ].
    replace (0 + k)%nat with k by lia.
    rewrite Nat2Z.inj_succ.
    destruct (Z.eqb (Z.of_nat k) x) eqn:E;
      [apply Z.eqb_eq in E | apply Z.eqb_neq in E];
      destruct (Z.leb_spec 0 x); destruct (Z.ltb_spec x (Z.of_nat k));
      destruct (Z.ltb_spec x (Z.succ (Z.of_nat k)));
      cbn [ind andb]; lia.
Qed.

Lemma zho_count_filter : forall (g : Z -> bool) l (x : Z),
  Z.of_nat (count_occ Z.eq_dec (filter g l) x)
  = if g x then Z.of_nat (count_occ Z.eq_dec l x) else 0.
Proof.
  intros g l x. induction l as [|v l IH].
  - cbn [filter count_occ]. destruct (g x); reflexivity.
  - cbn [filter].
    destruct (g v) eqn:Egv.
    + rewrite (zho_count_cons v (filter g l) x), IH,
              (zho_count_cons v l x).
      destruct (Z.eqb v x) eqn:Evx.
      * apply Z.eqb_eq in Evx. subst v. rewrite Egv. cbn [ind]. lia.
      * cbn [ind]. destruct (g x); lia.
    + rewrite IH, (zho_count_cons v l x).
      destruct (Z.eqb v x) eqn:Evx.
      * apply Z.eqb_eq in Evx. subst v. rewrite Egv. cbn [ind]. lia.
      * cbn [ind]. destruct (g x); lia.
Qed.

(** weight_tree_list on leaf forests and singletons *)

Lemma zho_wtl_leaves : forall l : list Z,
  weight_tree_list zho_f (map (@leaf Z) l) = 0%nat.
Proof.
  induction l as [|v l IH]; cbn [map weight_tree_list fold_right]; [reflexivity|].
  unfold weight_tree_list in *. cbn [fold_right weight_tree]. lia.
Qed.

Lemma zho_wtl_single : forall t : btree Z,
  weight_tree_list zho_f [t] = weight_tree zho_f t.
Proof.
  intro t. unfold weight_tree_list. cbn [fold_right]. lia.
Qed.

(** ** Helpers, stage 2: the invariant record and its entry *)

Record SimCore (st : BtSt) (F : Z -> btree Z) : Prop := mkSimCore {
  sc_census : CensusInv elems maxc1 t1 hlen1 st;
  sc_nn     : forall x, 0 <= x < b_node st -> 0 <= t_freq (b_tree st) x;
  sc_wtie   : forall p, 1 <= p <= b_hlen st ->
              sum_leaves zho_f (F (b_heap st p))
              = Z.to_nat (t_freq (b_tree st) (b_heap st p));
  sc_wagg   : weight_tree_list zho_f (map F (zho_live_idx st))
              = Z.to_nat (wsum (fun i => t_freq (b_tree st) i) elems
                               (Z.to_nat (b_node st - elems)));
  sc_btr    : forall T, build zho_f (map F (zho_live_idx st)) T ->
              build zho_f zho_forest0 T;
  sc_chld   : forall i, elems <= i < b_node st ->
              t_freq (b_tree st) i
              = wsum (fun p => ind (Z.eqb (t_dad (b_tree st) (b_heap st p)) i)
                               * t_freq (b_tree st) (b_heap st p))
                     (b_hmax st) (Z.to_nat (HEAP_SIZE - b_hmax st));
  sc_ltot   : zsumF (zho_live_idx st) (t_freq (b_tree st))
              = wsum (fun x => ind (live_b t1 maxc1 x) * t_freq t1 x)
                     0 (Z.to_nat elems)
}.

Lemma zho_ind_pos_true : forall b, 1 <= ind b -> b = true.
Proof. intros [|]; cbn [ind]; [reflexivity | lia]. Qed.

(** entry-window values are live symbols *)
Lemma zho_entry_val_live :
  InitOut elems t1 hp1 hlen1 maxc1 ->
  forall v, In v (zho_live_idx zho_st0) -> live_b t1 maxc1 v = true.
Proof.
  intros Hio v Hin.
  pose proof (io_hlen _ _ _ _ _ Hio) as Hh0.
  destruct (zho_win_in_inv _ _ _ Hin) as (p & Hp & Hv).
  assert (H1 : 1 <= lcount (b_heap zho_st0) hlen1 v)
    by (rewrite <- Hv; apply lcount_member; exact Hp).
  cbn [b_heap zho_st0] in H1.
  rewrite bt_heapify_count in H1
    by (apply Z.div_le_upper_bound; lia).
  rewrite (io_spec _ _ _ _ _ Hio) in H1.
  apply zho_ind_pos_true. exact H1.
Qed.

Lemma zho_entry :
  0 < elems <= L_CODES -> maxc1 < elems ->
  2 <= hlen1 <= L_CODES ->
  (forall n, 0 <= n < elems -> 0 <= t_freq t1 n) ->
  InitOut elems t1 hp1 hlen1 maxc1 ->
  SimCore zho_st0 (@leaf Z) /\ StepPre zho_st0.
Proof.
  intros Hel Hme Hh1 Hnn Hio.
  assert (Hdiv : 2 * (hlen1 / 2) <= hlen1 /\ hlen1 <= 2 * (hlen1 / 2) + 1).
  { pose proof (Z.div_mod hlen1 2 ltac:(lia)).
    pose proof (Z.mod_pos_bound hlen1 2 ltac:(lia)). lia. }
  assert (Hpre : StepPre zho_st0).
  { constructor.
    - cbn [b_hlen zho_st0]. lia.
    - cbn [b_hlen b_hmax zho_st0]. unfold HEAP_SIZE, L_CODES in *. lia.
    - cbn [b_tree b_dep b_heap b_hlen zho_st0].
      apply bt_heapify_heapok.
      + rewrite Z2Nat.id by (unfold HEAP_SIZE; lia).
        unfold HEAP_SIZE, L_CODES in *. lia.
      + lia.
      + unfold L_CODES in *. lia.
      + apply heapokfrom_vacuous. lia.
    - intros p Hp.
      cbn [b_node zho_st0].
      assert (Hlv : live_b t1 maxc1 (b_heap zho_st0 p) = true).
      { apply (zho_entry_val_live Hio).
        apply (zho_win_in (b_heap zho_st0) (b_hlen zho_st0) p).
        cbn [b_hlen zho_st0]. exact Hp. }
      pose proof (zho_live_b_range _ Hlv). lia. }
  split; [|exact Hpre].
  constructor.
  - exact (census_entry elems maxc1 t1 hp1 dep1 hlen1
             (Z.to_nat HEAP_SIZE) ltac:(lia) Hio).
  - cbn [b_tree b_node zho_st0]. exact Hnn.
  - intros p Hp. cbn [b_tree zho_st0]. reflexivity.
  - cbn [b_node zho_st0].
    replace (elems - elems) with 0 by lia.
    change (Z.to_nat 0) with 0%nat. cbn [wsum].
    rewrite zho_wtl_leaves. reflexivity.
  - intros T H. exact H.
  - cbn [b_node zho_st0]. intros i Hi. lia.
  - cbn [b_tree zho_st0].
    rewrite (zsumF_counts (zho_live_idx zho_st0) (t_freq t1) 0
               (Z.to_nat elems)).
    + apply wsum_ext. intros x Hx.
      f_equal.
      change (zho_live_idx zho_st0)
        with (zho_win (b_heap zho_st0) hlen1).
      rewrite zho_win_count by lia.
      cbn [b_heap zho_st0].
      rewrite bt_heapify_count by (apply Z.div_le_upper_bound; lia).
      apply (io_spec _ _ _ _ _ Hio).
    + intros v Hin.
      pose proof (zho_live_b_range _ (zho_entry_val_live Hio v Hin)).
      rewrite Z2Nat.id by lia. lia.
Qed.

(** ** Helpers, stage 3: one combine trip preserves the invariant *)

Lemma zho_ordered_cons_all : forall (b : btree Z) (l : list (btree Z)),
  (forall x, In x l -> sum_order zho_f b x) ->
  ordered (sum_order zho_f) l ->
  ordered (sum_order zho_f) (b :: l).
Proof.
  intros b l Hall Hord. destruct l as [|h l'].
  - apply ordered_one.
  - apply ordered_cons; [apply Hall; left; reflexivity | exact Hord].
Qed.

Lemma zho_step : forall st F st',
  wsum (fun x => ind (live_b t1 maxc1 x) * t_freq t1 x) 0 (Z.to_nat elems)
    <= 65535 ->
  maxc1 < elems -> 0 < elems <= L_CODES -> hlen1 <= L_CODES ->
  SimCore st F -> StepPre st ->
  (bt_step st = BtCont st' \/ bt_step st = BtDone st') ->
  exists F',
    SimCore st' F'
    /\ (2 <= b_hlen st' -> StepPre st')
    /\ b_hlen st' = b_hlen st - 1
    /\ (b_hlen st = 2 -> b_heap st' 1 = b_node st).
Proof.
  intros st F st' Hmass Hme Hel Hh1 Hcore Hpre Hstep.
  destruct (bt_step_minima st Hpre) as (Hmin1 & Hmin2 & Hcnt2 & Hiv).
  destruct (Hiv st' Hstep) as (Endz & Ehlz & Hcnt6 & Hpres).
  clear Hiv.
  destruct Hcore as [Hcen Hnn Hwtie Hwagg Hbtr Hchld Hltot].
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
  (* --- value provenance --- *)
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
  assert (Hm_c2 : 1 <= lcount hp2 (hl - 1) mm)
    by (apply (lcount_member hp2 (hl - 1) 1); lia).
  assert (Hlc1 : forall x, lcount hp hl x <= 1).
  { intro x. pose proof (Hcons0 x).
    pose proof (total_le_1 elems maxc1 t1 nd x Hme).
    pose proof (wcount_nonneg hp hm (Z.to_nat (HEAP_SIZE - hm)) x).
    unfold pcount in *. lia. }
  assert (Hnm_ne : nn <> mm).
  { intro E. pose proof (Hcnt2 mm) as Hc.
    rewrite <- E in Hc. rewrite Z.eqb_refl in Hc. cbn [ind] in Hc.
    pose proof (Hlc1 mm). rewrite <- E in *. lia. }
  assert (Hm_lc : 1 <= lcount hp hl mm).
  { pose proof (Hcnt2 mm) as Hc. pose proof (ind_0_1 (Z.eqb nn mm)). lia. }
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
  assert (Hlive_rng : forall v, 1 <= lcount hp hl v -> 0 <= v < nd).
  { intros v Hv.
    pose proof (Hcons0 v) as Hc.
    pose proof (wcount_nonneg hp hm (Z.to_nat (HEAP_SIZE - hm)) v) as Hp0.
    unfold pcount in Hc.
    destruct (live_b t1 maxc1 v) eqn:Elv.
    - pose proof (zho_live_b_range v Elv). lia.
    - cbn [ind] in Hc.
      destruct ((elems <=? v) && (v <? nd)) eqn:Ecr.
      + apply andb_true_iff in Ecr as [E1 E2].
        apply Z.leb_le in E1. apply Z.ltb_lt in E2. lia.
      + cbn [ind] in Hc. lia. }
  assert (Hnn_n : 0 <= t_freq tr nn).
  { apply Hnn. apply Hlive_rng. apply (lcount_member hp hl 1). lia. }
  assert (Hnn_m : 0 <= t_freq tr mm)
    by (apply Hnn; apply Hlive_rng; exact Hm_lc).
  assert (Hnn_rest : forall v, In v rest -> 0 <= t_freq tr v).
  { intros v Hv. apply Hnn. apply Hlive_rng.
    destruct (Hrest_val v Hv) as (q & Hq & Hqe).
    rewrite <- Hqe. apply lcount_member. exact Hq. }
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
  { unfold fv. pose proof Hnn_n. pose proof Hnn_m. lia. }
  assert (Hfv_ub : fv <= 65535).
  { assert (Hz : zsumF (zho_win hp hl) (t_freq tr)
                 = wsum (fun x => ind (live_b t1 maxc1 x) * t_freq t1 x)
                        0 (Z.to_nat elems))
      by (exact Hltot).
    rewrite (zsumF_perm (t_freq tr) _ _ HP1) in Hz.
    cbn [zsumF fold_right] in Hz. fold (zsumF rest (t_freq tr)) in Hz.
    assert (0 <= zsumF rest (t_freq tr))
      by (apply zsumF_nonneg; exact Hnn_rest).
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
  (* --- the successor forest --- *)
  set (F' := fun x => if Z.eqb x nd then node (F nn) (F mm) else F x).
  assert (EF'nd : F' nd = node (F nn) (F mm))
    by (unfold F'; rewrite Z.eqb_refl; reflexivity).
  assert (EF'o : forall x, x <> nd -> F' x = F x).
  { intros x Hx. unfold F'.
    replace (Z.eqb x nd) with false
      by (symmetry; apply Z.eqb_neq; exact Hx).
    reflexivity. }
  (* --- weight ties at the popped pair --- *)
  assert (Hwt : forall v, (exists q, 1 <= q <= hl /\ hp q = v) ->
          sum_leaves zho_f (F v) = Z.to_nat (t_freq tr v)).
  { intros v (q & Hq & <-). exact (Hwtie q Hq). }
  assert (Hsl_n : sum_leaves zho_f (F nn) = Z.to_nat (t_freq tr nn))
    by (apply Hwt; exists 1; split; [lia | reflexivity]).
  assert (Hsl_m : sum_leaves zho_f (F mm) = Z.to_nat (t_freq tr mm))
    by (apply Hwt; exact Hm_orig).
  assert (Hrest_sl : forall v, In v rest ->
          sum_leaves zho_f (F v) = Z.to_nat (t_freq tr v))
    by (intros v Hv; apply Hwt; apply Hrest_val; exact Hv).
  assert (Hfr_m_le : forall v, In v rest -> t_freq tr mm <= t_freq tr v).
  { intros v Hv.
    assert (Hin2 : In v (zho_win hp2 (hl - 1))).
    { apply (Permutation_in _ (Permutation_sym Hp2rest)).
      right. exact Hv. }
    destruct (zho_win_in_inv _ _ _ Hin2) as (q & Hq & <-).
    eapply zho_smaller_freq_le. apply Hmin2. exact Hq. }
  (* --- the one_step witness --- *)
  set (l3 := isort (le_sum zho_f) (map F rest)).
  assert (Hl3perm : Permutation (map F rest) l3)
    by (unfold l3; apply isort_permutation).
  assert (Hl3ord : ordered (sum_order zho_f) l3).
  { unfold l3. apply isort_ordered.
    - intros a b. apply le_sum_correct1.
    - intros a b. apply le_sum_correct2. }
  assert (Hord : ordered (sum_order zho_f) (F nn :: F mm :: l3)).
  { apply ordered_cons.
    - unfold sum_order. rewrite Hsl_n, Hsl_m.
      apply Z2Nat.inj_le; [exact Hnn_n | exact Hnn_m |].
      eapply zho_smaller_freq_le.
      destruct Hm_orig as (q & Hq & Hqe). rewrite <- Hqe.
      apply Hmin1. exact Hq.
    - apply zho_ordered_cons_all.
      + intros x Hx.
        assert (Hx' : In x (map F rest))
          by (apply (Permutation_in _ (Permutation_sym Hl3perm)); exact Hx).
        apply in_map_iff in Hx' as (v & Hveq & Hv).
        rewrite <- Hveq.
        unfold sum_order. rewrite Hsl_m, (Hrest_sl v Hv).
        apply Z2Nat.inj_le; [exact Hnn_m | apply (Hnn_rest v Hv) |].
        apply Hfr_m_le. exact Hv.
      + exact Hl3ord. }
  assert (Hmap_rest : map F' rest = map F rest).
  { apply map_ext_in. intros v Hv. apply EF'o.
    pose proof (Hrest_lt v Hv). lia. }
  assert (HPm' : Permutation (map F' (zho_live_idx st'))
                             (node (F nn) (F mm) :: map F rest)).
  { change (zho_live_idx st')
      with (zho_win (b_heap st') (b_hlen st')).
    eapply Permutation_trans;
      [apply Permutation_map; exact HP2|].
    cbn [map]. rewrite EF'nd, Hmap_rest. apply Permutation_refl. }
  assert (HPo : Permutation (map F (zho_live_idx st))
                            (F nn :: F mm :: map F rest)).
  { change (zho_live_idx st) with (zho_win hp hl).
    exact (Permutation_map F HP1). }
  assert (Hone : one_step zho_f (map F (zho_live_idx st))
                          (map F' (zho_live_idx st'))).
  { unfold one_step. exists l3, (F nn), (F mm).
    split; [exact Hord|]. split.
    - eapply Permutation_trans; [exact HPo|].
      apply perm_skip, perm_skip. exact Hl3perm.
    - eapply Permutation_trans; [exact HPm'|].
      apply perm_skip. exact Hl3perm. }
  (* --- SimCore at the successor --- *)
  assert (Hnn' : forall x, 0 <= x < b_node st' -> 0 <= t_freq (b_tree st') x).
  { intros x Hxr. destruct (Z.eqb_spec x nd) as [->|Hx].
    - rewrite Efrq_nd. exact Hfv_nn.
    - rewrite (Efrq_o x Hx). apply Hnn. lia. }
  assert (Hval6 : forall v, In v (zho_win (b_heap st') (b_hlen st')) ->
                  v = nd \/ (exists q, 1 <= q <= hl /\ hp q = v)).
  { intros v Hv.
    apply (Permutation_in _ HP2) in Hv.
    destruct Hv as [E|Hv]; [left; symmetry; exact E|].
    right. apply Hrest_val. exact Hv. }
  assert (Hwtie' : forall p, 1 <= p <= b_hlen st' ->
          sum_leaves zho_f (F' (b_heap st' p))
          = Z.to_nat (t_freq (b_tree st') (b_heap st' p))).
  { intros p Hp.
    assert (Hv : In (b_heap st' p) (zho_win (b_heap st') (b_hlen st')))
      by (apply zho_win_in; exact Hp).
    destruct (Hval6 _ Hv) as [Ev|Hor].
    - rewrite Ev. rewrite EF'nd, Efrq_nd.
      cbn [sum_leaves]. rewrite Hsl_n, Hsl_m.
      unfold fv.
      rewrite Z2Nat.inj_add; [reflexivity | exact Hnn_n | exact Hnn_m].
    - assert (Hvne : b_heap st' p <> nd).
      { destruct Hor as (q & Hq & Hqe). rewrite <- Hqe.
        pose proof (Hfr q Hq). lia. }
      rewrite (EF'o _ Hvne), (Efrq_o _ Hvne).
      apply Hwt. exact Hor. }
  assert (Hwagg' : weight_tree_list zho_f (map F' (zho_live_idx st'))
        = Z.to_nat (wsum (fun i => t_freq (b_tree st') i) elems
                         (Z.to_nat (b_node st' - elems)))).
  { rewrite (weight_tree_list_permutation _ zho_f _ _ HPm').
    rewrite weight_tree_list_node.
    rewrite <- (weight_tree_list_permutation _ zho_f _ _ HPo).
    rewrite Hwagg.
    rewrite Endz.
    replace (nd + 1 - elems) with (Z.succ (nd - elems)) by lia.
    rewrite Z2Nat.inj_succ by lia.
    rewrite wsum_split_last.
    replace (elems + Z.of_nat (Z.to_nat (nd - elems))) with nd
      by (rewrite Z2Nat.id by lia; lia).
    rewrite Efrq_nd.
    rewrite (wsum_ext (fun i => t_freq (b_tree st') i) (fun i => t_freq tr i))
      by (intros i Hi; apply Efrq_o; rewrite Z2Nat.id in Hi by lia; lia).
    rewrite Hsl_n, Hsl_m.
    pose proof (wsum_nonneg (fun i => t_freq tr i) elems
                  (Z.to_nat (nd - elems))
                  ltac:(intros i Hi; apply Hnn;
                        rewrite Z2Nat.id in Hi by lia; lia)).
    pose proof Hnn_n. pose proof Hnn_m.
    unfold fv. lia. }
  assert (Hbtr' : forall T, build zho_f (map F' (zho_live_idx st')) T ->
          build zho_f zho_forest0 T).
  { intros T HT. apply Hbtr.
    exact (build_step Z zho_f T _ _ Hone HT). }
  assert (Hrestw : forall j,
      wsum (fun p => ind (Z.eqb (t_dad (b_tree st') (b_heap st' p)) j)
                     * t_freq (b_tree st') (b_heap st' p))
           hm (Z.to_nat (HEAP_SIZE - hm))
      = wsum (fun p => ind (Z.eqb (t_dad tr (hp p)) j) * t_freq tr (hp p))
             hm (Z.to_nat (HEAP_SIZE - hm))).
  { intro j. apply wsum_ext. intros p Hp.
    rewrite Z2Nat.id in Hp by lia.
    rewrite (Hpark_frozen p) by lia.
    assert (Hne_n : hp p <> nn).
    { intro E.
      assert (1 <= pcount hp hm nn).
      { unfold pcount. apply (wcount_of_member hp hm _ nn p);
          [rewrite Z2Nat.id by lia; lia | exact E]. }
      lia. }
    assert (Hne_m : hp p <> mm).
    { intro E.
      assert (1 <= pcount hp hm mm).
      { unfold pcount. apply (wcount_of_member hp hm _ mm p);
          [rewrite Z2Nat.id by lia; lia | exact E]. }
      lia. }
    assert (Hne_d : hp p <> nd).
    { intro E.
      assert (1 <= pcount hp hm nd).
      { unfold pcount. apply (wcount_of_member hp hm _ nd p);
          [rewrite Z2Nat.id by lia; lia | exact E]. }
      lia. }
    rewrite (Edad (hp p)).
    replace (Z.eqb (hp p) nn) with false
      by (symmetry; apply Z.eqb_neq; exact Hne_n).
    replace (Z.eqb (hp p) mm) with false
      by (symmetry; apply Z.eqb_neq; exact Hne_m).
    rewrite (Efrq_o (hp p) Hne_d).
    reflexivity. }
  assert (Hchld' : forall i, elems <= i < b_node st' ->
      t_freq (b_tree st') i
      = wsum (fun p => ind (Z.eqb (t_dad (b_tree st') (b_heap st' p)) i)
                       * t_freq (b_tree st') (b_heap st' p))
             (b_hmax st') (Z.to_nat (HEAP_SIZE - b_hmax st'))).
  { intros i Hi. rewrite Endz in Hi. rewrite Ehmz.
    replace (Z.to_nat (HEAP_SIZE - (hm - 2)))
      with (S (S (Z.to_nat (HEAP_SIZE - hm)))) by lia.
    rewrite wsum_split_first.
    rewrite wsum_split_first.
    replace (hm - 2 + 1) with (hm - 1) by lia.
    replace (hm - 1 + 1) with hm by lia.
    rewrite Hslot_m, Hslot_n, Edad_m, Edad_n.
    rewrite (Efrq_o mm) by lia.
    rewrite (Efrq_o nn) by lia.
    rewrite Hrestw.
    destruct (Z.eqb_spec nd i) as [Ei|Hne].
    - (* i = nd: the two fresh slots carry the mass, old dads miss nd *)
      subst i. cbn [ind].
      rewrite Efrq_nd.
      assert (Hz : wsum (fun p => ind (Z.eqb (t_dad tr (hp p)) nd)
                                  * t_freq tr (hp p))
                        hm (Z.to_nat (HEAP_SIZE - hm)) = 0).
      { etransitivity.
        - apply (wsum_ext _ (fun _ => 0)). intros p Hp.
          rewrite Z2Nat.id in Hp by lia.
          destruct (Hord0 p ltac:(lia)) as [Hdr _].
          replace (Z.eqb (t_dad tr (hp p)) nd) with false
            by (symmetry; apply Z.eqb_neq; lia).
          cbn [ind]. lia.
        - apply zho_wsum_zero. }
      rewrite Hz. unfold fv. lia.
    - (* i < nd: fresh slots contribute 0, the old census equation stands *)
      cbn [ind].
      rewrite (Efrq_o i) by lia.
      rewrite (Hchld i) by lia.
      lia. }
  assert (Hltot' : zsumF (zho_live_idx st') (t_freq (b_tree st'))
        = wsum (fun x => ind (live_b t1 maxc1 x) * t_freq t1 x)
               0 (Z.to_nat elems)).
  { change (zho_live_idx st')
      with (zho_win (b_heap st') (b_hlen st')).
    rewrite (zsumF_perm (t_freq (b_tree st')) _ _ HP2).
    cbn [zsumF fold_right].
    fold (zsumF rest (t_freq (b_tree st'))).
    rewrite Efrq_nd.
    rewrite (zsumF_ext_in (t_freq (b_tree st')) (t_freq tr) rest)
      by (intros v Hv; apply Efrq_o; pose proof (Hrest_lt v Hv); lia).
    assert (Hz : zsumF (zho_win hp hl) (t_freq tr)
                 = wsum (fun x => ind (live_b t1 maxc1 x) * t_freq t1 x)
                        0 (Z.to_nat elems))
      by (exact Hltot).
    rewrite (zsumF_perm (t_freq tr) _ _ HP1) in Hz.
    cbn [zsumF fold_right] in Hz. fold (zsumF rest (t_freq tr)) in Hz.
    unfold fv. lia. }
  exists F'. split; [|split; [|split]].
  - constructor; [exact Hcen' | exact Hnn' | exact Hwtie' | exact Hwagg'
                  | exact Hbtr' | exact Hchld' | exact Hltot'].
  - exact Hpres.
  - exact Ehlz.
  - exact Hroot2.
Qed.

(** ** Helpers, stage 4: the loop walk *)

Lemma zho_loop : forall fuel st F,
  wsum (fun x => ind (live_b t1 maxc1 x) * t_freq t1 x) 0 (Z.to_nat elems)
    <= 65535 ->
  maxc1 < elems -> 0 < elems <= L_CODES -> hlen1 <= L_CODES ->
  SimCore st F -> StepPre st ->
  match bt_loop fuel st with
  | Some stf => exists Ff, SimCore stf Ff /\ b_hlen stf = 1
                /\ b_heap stf 1 = b_node stf - 1
  | None => True
  end.
Proof.
  induction fuel as [|f IH]; intros st F Hmass Hme Hel Hh1 Hcore Hpre.
  - cbn [bt_loop]. exact I.
  - cbn [bt_loop].
    destruct (bt_step st) as [st'|st'] eqn:Est.
    + assert (Hor : bt_step st = BtCont st' \/ bt_step st = BtDone st')
        by (left; exact Est).
      destruct (zho_step st F st' Hmass Hme Hel Hh1 Hcore Hpre Hor)
        as (F' & Hcore' & Hpre' & Ehl' & _).
      assert (Hhl' : 2 <= b_hlen st').
      { rewrite bt_step_eq in Est.
        destruct (Z.leb_spec 2 (b_hlen st - 1)) as [Hle|Hgt];
          [lia | discriminate]. }
      exact (IH st' F' Hmass Hme Hel Hh1 Hcore' (Hpre' Hhl')).
    + assert (Hor : bt_step st = BtCont st' \/ bt_step st = BtDone st')
        by (right; exact Est).
      destruct (zho_step st F st' Hmass Hme Hel Hh1 Hcore Hpre Hor)
        as (F' & Hcore' & _ & Ehl' & Hroot).
      assert (Hhl2 : b_hlen st = 2).
      { rewrite bt_step_eq in Est.
        destruct (Z.leb_spec 2 (b_hlen st - 1)) as [Hle|Hgt];
          [discriminate |].
        pose proof (sp_hlen _ Hpre). lia. }
      assert (End' : b_node st' = b_node st + 1).
      { pose proof (cv_hl _ _ _ _ _ (sc_census _ _ Hcore')) as E1.
        pose proof (cv_hl _ _ _ _ _ (sc_census _ _ Hcore)) as E0.
        lia. }
      exists F'. split; [exact Hcore'|]. split; [lia|].
      rewrite (Hroot Hhl2). lia.
Qed.

Theorem zho_sim_main : forall stf,
  0 < elems <= L_CODES -> maxc1 < elems ->
  2 <= hlen1 <= L_CODES ->
  (forall n, 0 <= n < elems -> 0 <= t_freq t1 n) ->
  (* live entry mass fits u16: every created freq is the TRUE sum (the
     model's t_setfreq stores u16 v; without this bound SIM-B/C are FALSE —
     countermodel in DEFECT-zho-sim-main.md).  The consumer discharges it
     from its total <= 16384. *)
  wsum (fun x => ind (live_b t1 maxc1 x) * t_freq t1 x)
       0 (Z.to_nat elems) <= 65535 ->
  InitOut elems t1 hp1 hlen1 maxc1 ->
  bt_loop (Z.to_nat HEAP_SIZE) zho_st0 = Some stf ->
  (* SIM-A: the built weight (= created-freq sum) is cover-minimal *)
  (forall T, cover zho_forest0 T ->
     (Z.to_nat (wsum (fun i => t_freq (b_tree stf) i) elems
                     (Z.to_nat (b_node stf - elems)))
      <= weight_tree zho_f T)%nat)
  (* SIM-B: each created index's freq is the freq-sum of the parked slots
     whose dad points at it (read at the loop-exit state) *)
  /\ (forall i, elems <= i < b_node stf ->
        t_freq (b_tree stf) i
        = wsum (fun p => ind (Z.eqb (t_dad (b_tree stf) (b_heap stf p)) i)
                         * t_freq (b_tree stf) (b_heap stf p))
               (b_hmax stf) (Z.to_nat (HEAP_SIZE - b_hmax stf)))
  (* SIM-C: the root (created last) carries the whole live entry mass *)
  /\ t_freq (b_tree stf) (b_node stf - 1)
     = wsum (fun n => ind (live_b t1 maxc1 n) * t_freq t1 n)
            0 (Z.to_nat elems)
  (* SIM-D: the entry forest is the live symbols *)
  /\ Permutation (zho_live_idx zho_st0)
       (filter (live_b t1 maxc1) (map Z.of_nat (seq 0 (Z.to_nat elems))))
  (* SIM-E: created freqs are the sums, in particular nonneg *)
  /\ (forall i, elems <= i < b_node stf -> 0 <= t_freq (b_tree stf) i).
Proof.
  intros stf Hel Hme Hh1 Hnn Hmass Hio Hloop.
  destruct (zho_entry Hel Hme Hh1 Hnn Hio) as (Hcore0 & Hpre0).
  pose proof (zho_loop (Z.to_nat HEAP_SIZE) zho_st0 (@leaf Z)
                Hmass Hme Hel (proj2 Hh1) Hcore0 Hpre0) as HL.
  rewrite Hloop in HL.
  destruct HL as (Ff & Hcoref & Hhlf & Hrootf).
  assert (Hidx : zho_live_idx stf = [b_heap stf 1]).
  { unfold zho_live_idx. rewrite Hhlf. reflexivity. }
  assert (Hbuild : build zho_f zho_forest0 (Ff (b_heap stf 1))).
  { apply (sc_btr _ _ Hcoref).
    rewrite Hidx. cbn [map]. apply build_one. }
  assert (Hne0 : zho_forest0 <> []).
  { unfold zho_forest0.
    destruct (zho_live_idx zho_st0) eqn:Eidx.
    - exfalso.
      assert (HIn : In (b_heap zho_st0 1)
                       (zho_win (b_heap zho_st0) (b_hlen zho_st0)))
        by (apply zho_win_in; cbn [b_hlen zho_st0]; lia).
      change (zho_win (b_heap zho_st0) (b_hlen zho_st0))
        with (zho_live_idx zho_st0) in HIn.
      rewrite Eidx in HIn. exact HIn.
    - cbn [map]. discriminate. }
  destruct (build_correct Z zho_f zho_forest0 (Ff (b_heap stf 1))
              Hne0 Hbuild) as (Hcov & Hminw).
  assert (Hwroot : weight_tree zho_f (Ff (b_heap stf 1))
                   = Z.to_nat (wsum (fun i => t_freq (b_tree stf) i) elems
                                    (Z.to_nat (b_node stf - elems)))).
  { pose proof (sc_wagg _ _ Hcoref) as HW.
    rewrite Hidx in HW. cbn [map] in HW.
    rewrite zho_wtl_single in HW. exact HW. }
  split; [|split; [|split; [|split]]].
  - intros T HcovT. rewrite <- Hwroot. apply Hminw. exact HcovT.
  - exact (sc_chld _ _ Hcoref).
  - pose proof (sc_ltot _ _ Hcoref) as HL3.
    rewrite Hidx in HL3. cbn [zsumF fold_right] in HL3.
    rewrite Hrootf in HL3. lia.
  - apply zho_perm_counts. intro x.
    change (zho_live_idx zho_st0) with (zho_win (b_heap zho_st0) hlen1).
    rewrite (zho_win_count _ _ x) by lia.
    cbn [b_heap zho_st0].
    rewrite bt_heapify_count by (apply Z.div_le_upper_bound; lia).
    rewrite (io_spec _ _ _ _ _ Hio).
    rewrite (zho_count_filter (live_b t1 maxc1)
               (map Z.of_nat (seq 0 (Z.to_nat elems))) x).
    rewrite zho_count_seq.
    destruct (live_b t1 maxc1 x) eqn:Elv.
    + pose proof (zho_live_b_range x Elv).
      replace ((0 <=? x) && (x <? Z.of_nat (Z.to_nat elems))) with true;
        [reflexivity|].
      symmetry. apply andb_true_iff.
      split; [apply Z.leb_le; lia
             | apply Z.ltb_lt; rewrite Z2Nat.id by lia; lia].
    + cbn [ind]. reflexivity.
  - intros i Hi. apply (sc_nn _ _ Hcoref). lia.
Qed.

End ZHOSim.
