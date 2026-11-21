(** * BtCensus4 — the census at the loop's two ends.

    OWNER: an earlier development run.

    ENTRY: [InitOut] (BtCensus2) plus the heapify's count-neutrality
    (BtCensus1) IS the [CensusInv] at the combine loop's start state — empty
    parked window, cursor at [elems].

    EXIT: after [bt_loop] and the [:695] root write, the parked window
    [hmaxf .. HEAP_SIZE) holds every node exactly once — the live symbols and
    the created internals — with the root ([b_node - 1]) at the LOW end and
    every non-root node's dad parked strictly below it.  [BtParked] is the
    package [gb_pass1]'s Kraft walk consumes; nothing downstream needs [BtSt]
    or the loop. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff Trees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  BtWin BtCensus1 BtCensus2 BtCensus3 BtStep.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

Lemma lcount_one : forall hp x, lcount hp 1 x = ind (Z.eqb (hp 1) x).
Proof.
  intros hp x. unfold lcount.
  change (Z.to_nat 1) with 1%nat.
  cbn [wcount wsum]. lia.
Qed.

Lemma created_empty : forall elems x, ((elems <=? x) && (x <? elems)) = false.
Proof.
  intros elems x.
  destruct (Z.leb elems x) eqn:E1.
  - apply Z.leb_le in E1.
    replace (Z.ltb x elems) with false
      by (symmetry; apply Z.ltb_ge; lia).
    reflexivity.
  - reflexivity.
Qed.

(** ** Entry *)

Lemma census_entry : forall elems maxc1 t1 hp1 dep1 hlen1 fuel,
  0 <= hlen1 ->
  InitOut elems t1 hp1 hlen1 maxc1 ->
  CensusInv elems maxc1 t1 hlen1
    {| b_tree := t1;
       b_heap := bt_heapify fuel t1 dep1 hp1 hlen1 (hlen1 / 2);
       b_dep := dep1; b_hlen := hlen1; b_hmax := HEAP_SIZE;
       b_node := elems |}.
Proof.
  intros elems maxc1 t1 hp1 dep1 hlen1 fuel Hh1 Hout.
  destruct Hout as [Hspec Htot Hm Hgap Hlv Hh].
  assert (Hhalf : hlen1 / 2 <= hlen1)
    by (apply Z.div_le_upper_bound; lia).
  constructor; cbn [b_tree b_heap b_dep b_hlen b_hmax b_node].
  - lia.
  - lia.
  - lia.
  - intro x.
    rewrite bt_heapify_count by exact Hhalf.
    unfold pcount.
    replace (HEAP_SIZE - HEAP_SIZE) with 0 by lia.
    cbn [Z.to_nat wcount wsum].
    rewrite created_empty. cbn [ind].
    rewrite Hspec. lia.
  - intro c.
    replace (HEAP_SIZE - HEAP_SIZE) with 0 by lia.
    cbn [Z.to_nat wsum].
    rewrite created_empty. cbn [ind]. lia.
  - intros p Hp. exfalso. lia.
  - intros x _. reflexivity.
  - intros y _. reflexivity.
Qed.

(** ** Exit: the parked-window package *)

Record BtParked (elems maxc1 : Z) (t1 tf : Tree) (hp3 : zarr)
                (hmaxf ndf : Z) : Prop :=
mkBtParked {
  bp_maxc  : -1 <= maxc1 < elems;
  bp_ndf   : elems + 1 <= ndf;
  bp_hmax  : hmaxf = HEAP_SIZE - 2 * (ndf - elems) - 1;
  bp_cnt   : forall x, pcount hp3 hmaxf x
             = ind (live_b t1 maxc1 x)
               + ind ((elems <=? x) && (x <? ndf));
  bp_root  : hp3 hmaxf = ndf - 1;
  bp_dad   : forall c,
      wsum (fun p => ind (Z.eqb (t_dad tf (hp3 p)) c))
           (hmaxf + 1) (Z.to_nat (HEAP_SIZE - (hmaxf + 1)))
      = 2 * ind ((elems <=? c) && (c <? ndf));
  bp_ord   : forall p, hmaxf + 1 <= p < HEAP_SIZE ->
      elems <= t_dad tf (hp3 p) < ndf
      /\ exists p', hmaxf <= p' < p /\ hp3 p' = t_dad tf (hp3 p);
  bp_frq   : forall x, x < elems -> t_freq tf x = t_freq t1 x;
  bp_dlf   : forall y, pcount hp3 hmaxf y = 0 -> tr_dl tf y = tr_dl t1 y
}.

Lemma census_exit : forall elems maxc1 t1 hlen1 stf,
  CensusInv elems maxc1 t1 hlen1 stf ->
  -1 <= maxc1 < elems ->
  2 <= hlen1 ->
  b_hlen stf = 1 ->
  b_heap stf 1 = b_node stf - 1 ->
  BtParked elems maxc1 t1 (b_tree stf)
    (zset (b_heap stf) (b_hmax stf - 1) (b_heap stf 1))
    (b_hmax stf - 1) (b_node stf).
Proof.
  intros elems maxc1 t1 hlen1 stf Hinv Hmc Hh2 Hl1 Hroot.
  destruct Hinv as [Hnd Ehm Ehl Hcons Hdad Hord Hfrq Hdlf].
  assert (Hnd1 : elems + 1 <= b_node stf) by lia.
  assert (Hmx : b_hmax stf <= HEAP_SIZE) by lia.
  set (hp3 := zset (b_heap stf) (b_hmax stf - 1) (b_heap stf 1)).
  assert (Hfroz : forall p, b_hmax stf <= p < HEAP_SIZE ->
                  hp3 p = b_heap stf p).
  { intros p Hp. unfold hp3. apply zset_other. lia. }
  assert (Hat : hp3 (b_hmax stf - 1) = b_node stf - 1).
  { unfold hp3. rewrite zset_same. exact Hroot. }
  constructor.
  - exact Hmc.
  - exact Hnd1.
  - lia.
  - intro x.
    rewrite (pcount_grow hp3 (b_hmax stf) x Hmx).
    replace (b_hmax stf - 1) with (b_hmax stf - 1) by lia.
    rewrite Hat.
    rewrite (pcount_ext (b_heap stf) hp3 (b_hmax stf) x Hfroz).
    pose proof (Hcons x) as Hc.
    rewrite Hl1 in Hc. rewrite lcount_one in Hc.
    rewrite Hroot in Hc.
    lia.
  - exact Hat.
  - intro c.
    replace (b_hmax stf - 1 + 1) with (b_hmax stf) by lia.
    rewrite <- (Hdad c).
    apply wsum_ext. intros p Hp.
    assert (Hp' : b_hmax stf <= p < HEAP_SIZE).
    { split; [lia|].
      destruct Hp as [_ Hp2].
      destruct (Z_le_gt_dec (b_hmax stf) HEAP_SIZE) as [?|?];
        [rewrite Z2Nat.id in Hp2 by lia; lia|].
      replace (Z.to_nat (HEAP_SIZE - b_hmax stf)) with O in Hp2 by lia.
      cbn [Z.of_nat] in Hp2. lia. }
    rewrite (Hfroz p Hp'). reflexivity.
  - intros p Hp.
    assert (Hp' : b_hmax stf <= p < HEAP_SIZE) by lia.
    rewrite (Hfroz p Hp').
    destruct (Hord p Hp') as [Hrange Hdisj].
    split; [exact Hrange|].
    destruct Hdisj as [Hlive|[p' [Hp'' Heq]]].
    + exists (b_hmax stf - 1). split; [lia|].
      rewrite Hl1, lcount_one in Hlive.
      destruct (Z.eqb (b_heap stf 1) (t_dad (b_tree stf) (b_heap stf p)))
        eqn:Ee; cbn [ind] in Hlive; [|lia].
      apply Z.eqb_eq in Ee.
      rewrite Hat, <- Hroot. exact Ee.
    + exists p'. split; [lia|].
      rewrite (Hfroz p' ltac:(lia)). exact Heq.
  - exact Hfrq.
  - intros y Hy.
    apply Hdlf.
    assert (Hexp : pcount hp3 (b_hmax stf - 1) y
                   = ind (Z.eqb (b_heap stf 1) y)
                     + pcount (b_heap stf) (b_hmax stf) y).
    { rewrite (pcount_grow hp3 (b_hmax stf) y Hmx).
      rewrite Hat, Hroot.
      rewrite (pcount_ext (b_heap stf) hp3 (b_hmax stf) y Hfroz).
      reflexivity. }
    rewrite Hexp in Hy.
    rewrite Hl1, lcount_one.
    pose proof (ind_0_1 (Z.eqb (b_heap stf 1) y)).
    pose proof (wcount_nonneg (b_heap stf) (b_hmax stf)
                  (Z.to_nat (HEAP_SIZE - b_hmax stf)) y).
    unfold pcount in *. lia.
Qed.

Print Assumptions census_entry.
Print Assumptions census_exit.
