(** * BtCensus2 — the live heap at the combine loop's entry is EXACTLY the live
      symbols, one slot each.

    OWNER: an earlier development run.

    BtCover (ported) proved the >= 1 direction: every nonzero-frequency symbol
    is SOMEWHERE in the initial heap.  The Kraft census needs the exact count:
    the heap window holds ONE slot per live symbol and nothing else, because
    (i) the union-typed [tr_dl] walk needs parked-value distinctness, which is
    downstream of entry distinctness, and (ii) "leaves at the combine loop =
    live symbols" is where the [bl_count] histogram meets [tr_tally]'s
    frequencies.

    THE CHARACTERIZATION.  [live_b t maxc x] — x is a symbol in [0 .. maxc]
    with nonzero frequency.  [InitOut] pins four coupled facts at once:
    per-value counts are the characteristic function of [live_b], the heap
    length is the TOTAL of that function, everything above [maxc] (up to
    [elems]) has frequency zero, and [maxc] itself is live (or -1).  The
    per-step proofs below are where each clause pays for the others:
    [bt_force2]'s node-0 arm needs "frequency 0 is dead", which falls out of
    the TOTAL clause by a two-points bound — not from any per-value fact.

    Every [constructor] here dispatches its fields with an EXPLICIT slot list:
    [try assumption]/[try lia] dispatch is nondeterministic in the presence of
    conversion ([t_setlen] is invisible to [t_freq]) and of [lia]'s own intro
    behaviour, and cost two bullet miscounts before this file went explicit. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff Trees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  BtWin BtCensus1 BtCover.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

Definition live_b (t : Tree) (maxc x : Z) : bool :=
  (0 <=? x) && (x <=? maxc) && negb (Z.eqb (t_freq t x) 0).

Definition live_total (t : Tree) (maxc elems : Z) : Z :=
  wsum (fun s => ind (live_b t maxc s)) 0 (Z.to_nat elems).

Lemma live_b_true : forall t maxc x,
  0 <= x <= maxc -> t_freq t x <> 0 -> live_b t maxc x = true.
Proof.
  intros t maxc x Hr Hf. unfold live_b.
  destruct (Z.leb 0 x) eqn:E1; [|apply Z.leb_gt in E1; lia].
  destruct (Z.leb x maxc) eqn:E2; [|apply Z.leb_gt in E2; lia].
  destruct (Z.eqb (t_freq t x) 0) eqn:E3; [apply Z.eqb_eq in E3; lia|].
  reflexivity.
Qed.

Lemma live_b_false_high : forall t maxc x, maxc < x -> live_b t maxc x = false.
Proof.
  intros t maxc x H. unfold live_b.
  destruct (Z.leb x maxc) eqn:E2; [apply Z.leb_le in E2; lia|].
  rewrite andb_false_r. reflexivity.
Qed.

Lemma live_b_false_dead : forall t maxc x, t_freq t x = 0 -> live_b t maxc x = false.
Proof.
  intros t maxc x H. unfold live_b. rewrite H. cbn [Z.eqb negb].
  rewrite andb_false_r. reflexivity.
Qed.

Lemma live_b_m1 : forall t x, live_b t (-1) x = false.
Proof.
  intros t x. unfold live_b.
  destruct (Z.leb 0 x) eqn:E1; [|reflexivity].
  apply Z.leb_le in E1.
  replace (Z.leb x (-1)) with false by (symmetry; apply Z.leb_gt; lia).
  reflexivity.
Qed.

Lemma live_b_freq_ext : forall t t' maxc x,
  t_freq t x = t_freq t' x -> live_b t maxc x = live_b t' maxc x.
Proof. intros t t' maxc x H. unfold live_b. rewrite H. reflexivity. Qed.

(** Raising [maxc] to a fresh live symbol [n] changes [live_b] at [n] alone,
    PROVIDED the interval it newly admits is dead. *)
Lemma live_b_raise : forall t maxc n x,
  -1 <= maxc < n ->
  (forall y, maxc < y < n -> t_freq t y = 0) ->
  x <> n ->
  live_b t n x = live_b t maxc x.
Proof.
  intros t maxc n x Hm Hgap Hne.
  destruct (Z_le_gt_dec x maxc) as [Hle|Hgt].
  - unfold live_b.
    destruct (Z.leb x maxc) eqn:E2; [|apply Z.leb_gt in E2; lia].
    destruct (Z.leb x n) eqn:E3; [reflexivity|apply Z.leb_gt in E3; lia].
  - rewrite (live_b_false_high t maxc x) by lia.
    destruct (Z_le_gt_dec x n) as [Hxn|Hxn].
    + apply live_b_false_dead. apply Hgap. lia.
    + apply live_b_false_high. lia.
Qed.

(** ** The exit shape of the initial-heap construction *)

Record InitOut (elems : Z) (t : Tree) (hp : zarr) (hlen maxc : Z) : Prop :=
mkInitOut {
  io_spec  : forall x, lcount hp hlen x = ind (live_b t maxc x);
  io_total : hlen = live_total t maxc elems;
  io_maxc  : -1 <= maxc < elems;
  io_gapz  : forall x, maxc < x < elems -> t_freq t x = 0;
  io_live  : maxc = -1 \/ t_freq t maxc <> 0;
  io_hlen  : 0 <= hlen
}.

(** One appended slot: window grows at the high end with value [v]. *)
Lemma lcount_append : forall hp hlen v x,
  0 <= hlen ->
  lcount (zset hp (hlen + 1) v) (hlen + 1) x
  = lcount hp hlen x + ind (Z.eqb v x).
Proof.
  intros hp hlen v x Hh. unfold lcount.
  replace (Z.to_nat (hlen + 1)) with (S (Z.to_nat hlen))
    by (rewrite <- Z2Nat.inj_succ by lia; f_equal; lia).
  rewrite wcount_grow_high.
  rewrite Z2Nat.id by lia.
  replace (1 + hlen) with (hlen + 1) by lia.
  rewrite zset_same.
  f_equal.
  apply wcount_ext_window. intros i Hi.
  rewrite Z2Nat.id in Hi by lia.
  apply zset_other. lia.
Qed.

(** Raising the total by the fresh point [n]. *)
Lemma live_total_raise : forall t maxc n elems,
  -1 <= maxc < n -> 0 <= n < elems ->
  (forall y, maxc < y < n -> t_freq t y = 0) ->
  t_freq t n <> 0 ->
  live_total t n elems = live_total t maxc elems + 1.
Proof.
  intros t maxc n elems Hm Hn Hgap Hf.
  unfold live_total.
  rewrite (wsum_point_delta (fun s => ind (live_b t maxc s))
             (fun s => ind (live_b t n s)) 0 (Z.to_nat elems) n)
    by (try (rewrite Z2Nat.id by lia; lia);
        intros i _ Hne; rewrite (live_b_raise t maxc n i Hm Hgap Hne);
        reflexivity).
  rewrite (live_b_false_high t maxc n) by lia.
  rewrite (live_b_true t n n) by lia.
  cbn [ind]. lia.
Qed.

(** ** [bt_init]: the walked prefix is characterized

    [InitInv] is [InitOut] with the walk cursor [n] in place of [elems]; the
    exit lemma converts one into the other when the walk has covered
    [0 .. elems). *)
Record InitInv (elems n : Z) (t : Tree) (hp : zarr) (hlen maxc : Z) : Prop :=
mkInitInv {
  in_spec  : forall x, lcount hp hlen x = ind (live_b t maxc x);
  in_total : hlen = live_total t maxc elems;
  in_maxc  : -1 <= maxc < n;
  in_melems: maxc < elems;
  in_gapz  : forall x, maxc < x < n -> t_freq t x = 0;
  in_live  : maxc = -1 \/ t_freq t maxc <> 0;
  in_hlen  : 0 <= hlen
}.

Lemma bt_init_census : forall fuel n elems t hp dep hlen maxc
                              t0 hp0 dep0 hlen0 maxc0,
  bt_init fuel n elems t hp dep hlen maxc = (t0, hp0, dep0, hlen0, maxc0) ->
  elems <= n + Z.of_nat fuel ->
  0 <= n ->
  InitInv elems n t hp hlen maxc ->
  InitOut elems t0 hp0 hlen0 maxc0
  /\ (forall i, t_freq t0 i = t_freq t i).
Proof.
  induction fuel as [|f IH];
    intros n elems t hp dep hlen maxc t0 hp0 dep0 hlen0 maxc0 E Hfuel Hn Hinv.
  - cbn [bt_init] in E. inversion E; subst t0 hp0 dep0 hlen0 maxc0.
    cbn [Z.of_nat] in Hfuel.
    destruct Hinv as [Hspec Htot Hm Hme Hgap Hlv Hh].
    split; [|reflexivity].
    constructor;
      [ exact Hspec | exact Htot | lia
      | intros x Hx; apply Hgap; lia | exact Hlv | exact Hh ].
  - cbn [bt_init] in E.
    destruct (Z.leb elems n) eqn:Eguard.
    + apply Z.leb_le in Eguard.
      inversion E; subst t0 hp0 dep0 hlen0 maxc0.
      destruct Hinv as [Hspec Htot Hm Hme Hgap Hlv Hh].
      split; [|reflexivity].
      constructor;
        [ exact Hspec | exact Htot | lia
        | intros x Hx; apply Hgap; lia | exact Hlv | exact Hh ].
    + apply Z.leb_gt in Eguard.
      destruct (Z.eqb (t_freq t n) 0) eqn:Efr.
      * (* dead symbol: length write only — [t_setlen] is invisible to
           [t_freq] by conversion, so most fields transfer by [exact] *)
        apply Z.eqb_eq in Efr.
        destruct Hinv as [Hspec Htot Hm Hme Hgap Hlv Hh].
        destruct (IH (n + 1) elems (t_setlen t n 0) hp dep hlen maxc
                     t0 hp0 dep0 hlen0 maxc0 E) as [Hout Hfr];
          [ lia | lia
          | constructor;
            [ exact Hspec | exact Htot | lia | exact Hme
            | intros x Hx; change (t_freq t x = 0);
              destruct (Z.eq_dec x n) as [->|Hne];
                [exact Efr | apply Hgap; lia]
            | exact Hlv | exact Hh ]
          | split; [exact Hout | intro i; rewrite Hfr; reflexivity] ].
      * (* live symbol: appended, maxc raised *)
        apply Z.eqb_neq in Efr.
        destruct Hinv as [Hspec Htot Hm Hme Hgap Hlv Hh].
        destruct (IH (n + 1) elems t (zset hp (hlen + 1) n) (zset dep n 0)
                     (hlen + 1) n t0 hp0 dep0 hlen0 maxc0 E) as [Hout Hfr];
          [ lia | lia
          | constructor;
            [ intros x; rewrite (lcount_append hp hlen n x Hh), Hspec;
              destruct (Z.eq_dec n x) as [<-|Hne];
              [ rewrite (live_b_false_high t maxc n) by lia;
                rewrite (live_b_true t n n) by lia;
                rewrite Z.eqb_refl; reflexivity
              | rewrite (live_b_raise t maxc n x Hm Hgap)
                  by (auto using not_eq_sym);
                replace (Z.eqb n x) with false
                  by (symmetry; apply Z.eqb_neq; exact Hne);
                cbn [ind]; lia ]
            | rewrite (live_total_raise t maxc n elems Hm)
                by (try lia; assumption);
              lia
            | lia | exact Eguard
            | intros x Hx; lia
            | right; exact Efr
            | lia ]
          | split; [exact Hout | exact Hfr] ].
Qed.

(** The call shape [build_tree] uses: cursor 0, empty heap, [maxc = -1]. *)
Lemma bt_init_census_call : forall fuel elems t hp dep t0 hp0 dep0 hlen0 maxc0,
  bt_init fuel 0 elems t hp dep 0 (-1) = (t0, hp0, dep0, hlen0, maxc0) ->
  elems <= Z.of_nat fuel -> 0 < elems ->
  InitOut elems t0 hp0 hlen0 maxc0
  /\ (forall i, t_freq t0 i = t_freq t i).
Proof.
  intros fuel elems t hp dep t0 hp0 dep0 hlen0 maxc0 E Hfuel He.
  apply (bt_init_census fuel 0 elems t hp dep 0 (-1) t0 hp0 dep0 hlen0 maxc0);
    try assumption; try lia.
  constructor;
    [ intros x; rewrite (live_b_m1 t x);
      cbn [ind]; unfold lcount; cbn [Z.to_nat wcount wsum]; reflexivity
    | unfold live_total;
      rewrite (wsum_ext (fun s => ind (live_b t (-1) s)) (fun _ => 0))
        by (intros i _; rewrite (live_b_m1 t i); reflexivity);
      assert (Hz : forall n lo, wsum (fun _ : Z => 0) lo n = 0)
        by (induction n as [|k IHk]; intro lo;
            [reflexivity | cbn [wsum]; rewrite IHk; lia]);
      rewrite Hz; reflexivity
    | lia | lia
    | intros x Hx; lia
    | left; reflexivity
    | lia ].
Qed.

(** ** [bt_force2]: at most two forced slots, and the characterization survives

    The node-0 arm's "0 is dead" is the two-points argument promised in the
    header: were 0 live, the total would be at least 2 and the arm untaken. *)
Lemma force2_trip : forall elems t hp hlen maxc node,
  3 <= elems -> hlen < 2 ->
  node = (if Z.ltb maxc 2 then maxc + 1 else 0) ->
  InitOut elems t hp hlen maxc ->
  InitOut elems (t_setfreq t node 1) (zset hp (hlen + 1) node) (hlen + 1)
          (if Z.ltb maxc 2 then maxc + 1 else maxc).
Proof.
  intros elems t hp hlen maxc node Hel Hh2 En Hout.
  destruct Hout as [Hspec Htot Hm Hgap Hlv Hh].
  assert (Hfr : forall x, x <> node -> t_freq (t_setfreq t node 1) x = t_freq t x).
  { intros x Hx. unfold t_setfreq, t_freq. cbn [tr_fc].
    apply zset_other. exact Hx. }
  assert (Hfrn : t_freq (t_setfreq t node 1) node = 1).
  { unfold t_setfreq, t_freq. cbn [tr_fc]. rewrite zset_same. reflexivity. }
  destruct (Z.ltb maxc 2) eqn:Emc.
  - (* forced node maxc+1, maxc raised *)
    apply Z.ltb_lt in Emc. subst node.
    assert (Hdead : t_freq t (maxc + 1) = 0) by (apply Hgap; lia).
    constructor;
      [ intros x; rewrite (lcount_append hp hlen (maxc + 1) x Hh), Hspec;
        destruct (Z.eq_dec (maxc + 1) x) as [<-|Hne];
        [ rewrite (live_b_false_high t maxc (maxc + 1)) by lia;
          rewrite Z.eqb_refl;
          rewrite (live_b_true (t_setfreq t (maxc + 1) 1) (maxc + 1) (maxc + 1))
            by (rewrite ?Hfrn; lia);
          reflexivity
        | replace (Z.eqb (maxc + 1) x) with false
            by (symmetry; apply Z.eqb_neq; exact Hne);
          cbn [ind]; rewrite Z.add_0_r;
          rewrite (live_b_freq_ext (t_setfreq t (maxc + 1) 1) t (maxc + 1) x)
            by (apply Hfr; auto using not_eq_sym);
          f_equal; symmetry;
          apply (live_b_raise t maxc (maxc + 1) x); [lia | intros y Hy; lia
          | auto using not_eq_sym] ]
      | rewrite Htot;
        assert (Hstep : live_total (t_setfreq t (maxc + 1) 1) (maxc + 1) elems
                        = live_total (t_setfreq t (maxc + 1) 1) maxc elems + 1)
          by (apply live_total_raise;
              [lia | lia | intros y Hy; lia | rewrite Hfrn; lia]);
        rewrite Hstep;
        assert (Hsame : live_total (t_setfreq t (maxc + 1) 1) maxc elems
                        = live_total t maxc elems)
          by (unfold live_total; apply wsum_ext; intros i Hi;
              destruct (Z.eq_dec i (maxc + 1)) as [->|Hne];
              [ rewrite (live_b_false_high _ maxc (maxc + 1)) by lia;
                rewrite (live_b_false_high t maxc (maxc + 1)) by lia;
                reflexivity
              | f_equal; apply live_b_freq_ext; apply Hfr; exact Hne ]);
        rewrite Hsame; lia
      | lia
      | intros x Hx; rewrite Hfr by lia; apply Hgap; lia
      | right; rewrite Hfrn; lia
      | lia ].
  - (* forced node 0; 0 must be dead or the arm is unreachable *)
    apply Z.ltb_ge in Emc. subst node.
    assert (Hlvm : t_freq t maxc <> 0) by (destruct Hlv; [lia | assumption]).
    assert (Hdead0 : t_freq t 0 = 0).
    { destruct (Z.eq_dec (t_freq t 0) 0) as [?|Hne]; [assumption|exfalso].
      assert (H0 : ind (live_b t maxc 0) = 1)
        by (rewrite (live_b_true t maxc 0) by lia; reflexivity).
      assert (HM : ind (live_b t maxc maxc) = 1)
        by (rewrite (live_b_true t maxc maxc) by lia; reflexivity).
      assert (Hge2 : 2 <= live_total t maxc elems).
      { unfold live_total.
        pose proof (wsum_two_points (fun s => ind (live_b t maxc s))
                      0 (Z.to_nat elems) 0 maxc) as HW.
        cbn beta in HW.
        rewrite H0, HM in HW.
        apply HW.
        - intros i _. apply ind_0_1.
        - rewrite Z2Nat.id by lia. lia.
        - rewrite Z2Nat.id by lia. lia.
        - lia. }
      lia. }
    constructor;
      [ intros x; rewrite (lcount_append hp hlen 0 x Hh), Hspec;
        destruct (Z.eq_dec 0 x) as [<-|Hne];
        [ rewrite (live_b_false_dead t maxc 0 Hdead0), Z.eqb_refl;
          rewrite (live_b_true (t_setfreq t 0 1) maxc 0)
            by (rewrite ?Hfrn; lia);
          reflexivity
        | replace (Z.eqb 0 x) with false
            by (symmetry; apply Z.eqb_neq; exact Hne);
          cbn [ind]; rewrite Z.add_0_r;
          f_equal; apply live_b_freq_ext;
          rewrite Hfr by auto using not_eq_sym; reflexivity ]
      | rewrite Htot;
        unfold live_total;
        rewrite (wsum_point_delta (fun s => ind (live_b t maxc s))
                   (fun s => ind (live_b (t_setfreq t 0 1) maxc s))
                   0 (Z.to_nat elems) 0)
          by (try (rewrite Z2Nat.id by lia; lia);
              intros i _ Hne; f_equal; apply live_b_freq_ext;
              rewrite Hfr by auto using not_eq_sym; reflexivity);
        rewrite (live_b_false_dead t maxc 0 Hdead0);
        rewrite (live_b_true (t_setfreq t 0 1) maxc 0) by (rewrite ?Hfrn; lia);
        cbn [ind]; lia
      | lia
      | intros x Hx; rewrite Hfr by lia; apply Hgap; lia
      | right; rewrite Hfr by lia; exact Hlvm
      | lia ].
Qed.

Lemma bt_force2_census : forall stree elems t hp dep hlen maxc ol sl
                                t1 hp1 dep1 hlen1 maxc1 ol1 sl1,
  bt_force2 3%nat stree t hp dep hlen maxc ol sl
    = (t1, hp1, dep1, hlen1, maxc1, ol1, sl1) ->
  3 <= elems ->
  InitOut elems t hp hlen maxc ->
  InitOut elems t1 hp1 hlen1 maxc1 /\ 2 <= hlen1.
Proof.
  intros stree elems t hp dep hlen maxc ol sl
         t1 hp1 dep1 hlen1 maxc1 ol1 sl1 E Hel Hout.
  cbn [bt_force2] in E.
  destruct (Z.leb 2 hlen) eqn:E2.
  { apply Z.leb_le in E2. inversion E; subst. split; assumption. }
  apply Z.leb_gt in E2.
  pose proof (io_hlen _ _ _ _ _ Hout) as Hh0.
  pose proof (force2_trip elems t hp hlen maxc
                (if Z.ltb maxc 2 then maxc + 1 else 0) Hel E2 eq_refl Hout)
    as Hout'.
  set (node := if Z.ltb maxc 2 then maxc + 1 else 0) in *.
  set (mc' := if Z.ltb maxc 2 then maxc + 1 else maxc) in *.
  destruct (Z.leb 2 (hlen + 1)) eqn:E3.
  { apply Z.leb_le in E3. inversion E; subst. split; [exact Hout' | lia]. }
  apply Z.leb_gt in E3.
  pose proof (force2_trip elems (t_setfreq t node 1) (zset hp (hlen + 1) node)
                (hlen + 1) mc'
                (if Z.ltb mc' 2 then mc' + 1 else 0) Hel E3 eq_refl Hout')
    as Hout''.
  destruct (Z.leb 2 (hlen + 1 + 1)) eqn:E4.
  { apply Z.leb_le in E4. inversion E; subst. split; [exact Hout'' | lia]. }
  apply Z.leb_gt in E4. lia.
Qed.

Print Assumptions bt_init_census.
Print Assumptions bt_init_census_call.
Print Assumptions force2_trip.
Print Assumptions bt_force2_census.
