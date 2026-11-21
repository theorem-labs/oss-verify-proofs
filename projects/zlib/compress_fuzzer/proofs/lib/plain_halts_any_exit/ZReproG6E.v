(** * ZReproG6E — G6 bound-fit, part E: the u64->Z counter adapter.

    OWNER: g6-bound (zlib z-repro campaign, 2026-08-19).

    BtAccount2 accounts [opt_len]/[static_len] as u64-mod sums over the
    parked HEAP WINDOW at [build_tree]'s internal call shape.  The emit
    side (parts C/D) speaks frequency-weighted sums over SYMBOLS.  This
    file writes the adapter, one [build_tree] call at a time
    ([build_tree_counters]):

      * [wsum_by_value] — the position-sum / value-sum exchange, keyed by
        [wcount]; with [BtParked.bp_cnt] (every live leaf parks exactly
        once, internals sit above [maxc1] where [olterm]'s guard is 0)
        the window sum DOMINATES the tallied symbol sum.
      * [bt_force2_full] — the manufactured-node spec: which slots the
        force loop invents, that their entry frequency is ZERO (so they
        are disjoint from the tallied sum), and the exact counter deltas.
        The STATIC delta is repaid exactly by the manufactured slots' own
        window terms; the OPT delta is repaid only up to 2 bits, which
        the amortized per-block budget absorbs (part F's arithmetic).
      * [build_tree_counters] — the per-build wrapper in G3DynA's
        [inst_*] recipe: [ts_optlen (build_tree k s)] is [u64] of the
        entry counter plus a plain-Z value [BTC] that dominates (within
        2) the tallied opt sum, and likewise [BTS] dominating the tallied
        static sum EXACTLY; both bounded well inside u64.

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Chunk ZBitsOut BwStream Trees BtWin BtCensus1 BtCensus2
  BtCensus3 BtCensus4 BtCensus5 BtAccount BtAccount2 BtItem6b BtExports
  BtSized BtTerm.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import ZReproL0 ZReproG6A
  ZReproG6C.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ==========================================================================
   1.  wsum glue.
   ========================================================================== *)

Lemma g6_wsum_split : forall (f : Z -> Z) lo m n,
  wsum f lo (m + n)%nat = wsum f lo m + wsum f (lo + Z.of_nat m) n.
Proof.
  intros f lo m; revert lo; induction m as [|m IH]; intros lo n.
  - cbn [Nat.add wsum]. replace (lo + Z.of_nat 0) with lo by lia. ring.
  - cbn [Nat.add wsum].
    rewrite IH.
    replace (lo + 1 + Z.of_nat m) with (lo + Z.of_nat (S m)) by lia.
    ring.
Qed.

Lemma g6_wsum_const : forall (c : Z) lo n,
  wsum (fun _ => c) lo n = Z.of_nat n * c.
Proof.
  intros c lo n; revert lo; induction n as [|n IH]; intro lo;
    cbn [wsum]; [ring|].
  rewrite IH. rewrite Nat2Z.inj_succ. ring.
Qed.

(** The position-sum / value-sum exchange. *)
Lemma wsum_by_value : forall n (hp : zarr) (F : Z -> Z) lo V,
  0 <= V ->
  (forall p, lo <= p < lo + Z.of_nat n -> 0 <= hp p < V) ->
  wsum (fun p => F (hp p)) lo n
  = wsum (fun v => wcount hp lo n v * F v) 0 (Z.to_nat V).
Proof.
  induction n as [|n IH]; intros hp F lo V HV Hr.
  - cbn [wsum].
    symmetry. apply g6_wsum_zero.
    intros v _. unfold wcount. cbn [wsum]. ring.
  - rewrite (wsum_split_first (fun p => F (hp p)) lo n).
    rewrite (IH hp F (lo + 1) V HV
               ltac:(intros p Hp; apply Hr; lia)).
    rewrite (wsum_ext (fun v => wcount hp lo (S n) v * F v)
               (fun v => (if Z.eqb (hp lo) v then 1 else 0) * F v
                         + wcount hp (lo + 1) n v * F v)
               0 (Z.to_nat V)).
    2:{ intros v _.
        unfold wcount at 1.
        rewrite (wsum_split_first (fun i => ind (Z.eqb (hp i) v)) lo n).
        unfold ind at 1. unfold wcount. ring. }
    rewrite wsum_plus.
    rewrite (wsum_delta F (hp lo) 0 (Z.to_nat V))
      by (rewrite Z2Nat.id by lia;
          pose proof (Hr lo ltac:(lia)); lia).
    ring.
Qed.

(* ==========================================================================
   2.  bt_force2, in full.
   ========================================================================== *)

Lemma g6_t_freq_setfreq_same : forall t i v, t_freq (t_setfreq t i v) i = u16 v.
Proof.
  intros t i v. unfold t_setfreq, t_freq. cbn [tr_fc]. apply zset_same.
Qed.

Lemma g6_t_freq_setfreq_other : forall t i v j,
  j <> i -> t_freq (t_setfreq t i v) j = t_freq t j.
Proof.
  intros t i v j Hne. unfold t_setfreq, t_freq. cbn [tr_fc].
  apply zset_other. exact Hne.
Qed.

Lemma g6_t_len_setfreq : forall t i v j, t_len (t_setfreq t i v) j = t_len t j.
Proof. intros t i v j. reflexivity. Qed.

(** The full spec of the force loop at real fuel: which node(s) it invents,
    that their entry frequency is zero, and the counter deltas. *)
Lemma bt_force2_full : forall stree elems t hp dep hlen maxc ol sl
                              t1 hp1 dep1 hlen1 maxc1 ol1 sl1,
  bt_force2 3%nat stree t hp dep hlen maxc ol sl
    = (t1, hp1, dep1, hlen1, maxc1, ol1, sl1) ->
  3 <= elems ->
  InitOut elems t hp hlen maxc ->
  maxc <= maxc1
  /\ ( (2 <= hlen /\ t1 = t /\ maxc1 = maxc /\ ol1 = ol /\ sl1 = sl)
     \/ (exists v1,
           hlen = 1 /\ t1 = t_setfreq t v1 1
           /\ t_freq t v1 = 0 /\ 0 <= v1 <= maxc1 /\ v1 < elems
           /\ ol1 = u64 (ol - 1)
           /\ sl1 = match stree with
                    | None => sl
                    | Some st => u64 (sl - t_len st v1)
                    end)
     \/ (hlen = 0 /\ t1 = t_setfreq (t_setfreq t 0 1) 1 1
         /\ t_freq t 0 = 0 /\ t_freq t 1 = 0 /\ maxc1 = 1
         /\ ol1 = u64 (ol - 2)
         /\ sl1 = match stree with
                  | None => sl
                  | Some st => u64 (sl - t_len st 0 - t_len st 1)
                  end) ).
Proof.
  intros stree elems t hp dep hlen maxc ol sl
         t1 hp1 dep1 hlen1 maxc1 ol1 sl1 E Hel Hout.
  pose proof (io_hlen _ _ _ _ _ Hout) as Hh0.
  pose proof (io_maxc _ _ _ _ _ Hout) as Hmc0.
  cbn [bt_force2] in E.
  cbv zeta in E.
  destruct (Z.leb 2 hlen) eqn:E2.
  { apply Z.leb_le in E2. inversion E; subst.
    split; [lia|]. left. tauto. }
  apply Z.leb_gt in E2.
  (* the first manufactured node, and its dead entry frequency *)
  set (node := if Z.ltb maxc 2 then maxc + 1 else 0) in *.
  set (mc' := if Z.ltb maxc 2 then maxc + 1 else maxc) in *.
  assert (Hdead : t_freq t node = 0).
  { unfold node. destruct (Z.ltb_spec maxc 2) as [Hm|Hm].
    - apply (io_gapz _ _ _ _ _ Hout). lia.
    - (* node 0: were 0 live, the live total would be >= 2 > hlen *)
      destruct (Z.eq_dec (t_freq t 0) 0) as [?|Hne]; [assumption|exfalso].
      assert (Hlvm : t_freq t maxc <> 0)
        by (destruct (io_live _ _ _ _ _ Hout); [lia | assumption]).
      assert (H0 : ind (live_b t maxc 0) = 1)
        by (rewrite (live_b_true t maxc 0) by lia; reflexivity).
      assert (HM : ind (live_b t maxc maxc) = 1)
        by (rewrite (live_b_true t maxc maxc) by lia; reflexivity).
      assert (Hge2 : 2 <= live_total t maxc elems).
      { unfold live_total.
        assert (Hnn : forall i, 0 <= i < 0 + Z.of_nat (Z.to_nat elems) ->
                      0 <= (fun s => ind (live_b t maxc s)) i)
          by (intros i _; apply ind_0_1).
        assert (Hp0 : 0 <= 0 < 0 + Z.of_nat (Z.to_nat elems))
          by (rewrite Z2Nat.id by lia; lia).
        assert (Hq0 : 0 <= maxc < 0 + Z.of_nat (Z.to_nat elems))
          by (rewrite Z2Nat.id by lia; lia).
        pose proof (wsum_two_points (fun s => ind (live_b t maxc s))
                      0 (Z.to_nat elems) 0 maxc Hnn Hp0 Hq0
                      ltac:(lia)) as HW.
        cbn beta in HW.
        lia. }
      rewrite <- (io_total _ _ _ _ _ Hout) in Hge2. lia. }
  destruct (Z.leb 2 (hlen + 1)) eqn:E3.
  { (* one trip: hlen = 1 *)
    apply Z.leb_le in E3.
    inversion E; subst.
    assert (Hh1 : hlen = 1) by lia.
    split.
    { unfold mc'. destruct (Z.ltb_spec maxc 2); lia. }
    right. left.
    exists node.
    split; [exact Hh1|].
    split; [reflexivity|].
    split; [exact Hdead|].
    split.
    { unfold node, mc'. destruct (Z.ltb_spec maxc 2); lia. }
    split.
    { unfold node. destruct (Z.ltb_spec maxc 2); lia. }
    split; [reflexivity|].
    destruct stree as [st|]; reflexivity. }
  apply Z.leb_gt in E3.
  assert (Hh0' : hlen = 0) by lia.
  subst hlen.
  (* the entry state has NO live symbol: maxc = -1 *)
  assert (Hmm1 : maxc = -1).
  { destruct (Z.eq_dec maxc (-1)) as [->|Hne]; [reflexivity|exfalso].
    assert (Hlv : t_freq t maxc <> 0)
      by (destruct (io_live _ _ _ _ _ Hout); [lia | assumption]).
    assert (HM : ind (live_b t maxc maxc) = 1)
      by (rewrite (live_b_true t maxc maxc) by lia; reflexivity).
    assert (Hge1 : 1 <= live_total t maxc elems).
    { unfold live_total.
      assert (Hnn : forall i, 0 <= i < 0 + Z.of_nat (Z.to_nat elems) ->
                    0 <= (fun s => ind (live_b t maxc s)) i)
        by (intros i _; apply ind_0_1).
      assert (Hq0 : 0 <= maxc < 0 + Z.of_nat (Z.to_nat elems))
        by (rewrite Z2Nat.id by lia; lia).
      pose proof (wsum_one_point (fun s => ind (live_b t maxc s))
                    0 (Z.to_nat elems) maxc Hnn Hq0) as HW.
      cbn beta in HW.
      lia. }
    rewrite <- (io_total _ _ _ _ _ Hout) in Hge1. lia. }
  subst maxc.
  assert (En : node = 0) by reflexivity.
  assert (Emc : mc' = 0) by reflexivity.
  rewrite En, Emc in E.
  (* second trip: the remaining test is closed *)
  destruct (Z.leb 2 (0 + 1 + 1)) eqn:E4; [|discriminate E4].
  inversion E; subst.
  split; [lia|].
  right. right.
  assert (Hd1 : t_freq t 1 = 0)
    by (apply (io_gapz _ _ _ _ _ Hout); lia).
  split; [reflexivity|].
  split; [reflexivity|].
  split; [exact Hdead|].
  split; [exact Hd1|].
  split; [reflexivity|].
  split.
  { rewrite u64_sub_l. f_equal. ring. }
  destruct stree as [st|]; [|reflexivity].
  rewrite u64_sub_l. reflexivity.
Qed.

Set Printing All.
Set Printing Fully Qualified.
Set Printing Depth 10000000000.
Set Printing Width 2000.
Print Assumptions wsum_by_value.
Print Assumptions bt_force2_full.
Unset Printing All.
