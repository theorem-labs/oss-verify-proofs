(** * BtCensus1 — the sift-down and heapify preserve per-value COUNTS.

    OWNER: an earlier development run.  Continues PqDown.v (ported), which proved MEMBERSHIP
    preservation and deliberately stopped there because its consumer needed no
    more.  The Kraft census does need more: [tr_dl] is a UNION (dad and len are
    one array, [Trees.v:222-233]), so [gb_pass1]'s dad reads survive its len
    writes only if no node is parked twice — a COUNT fact, not a membership
    fact.  This file supplies the counting analogue of PqDown's three lemmas.

    THE SHAPE.  [pq_down] sifts a HOLE: mid-flight one value is duplicated and
    the held value [v] is missing (PqDown's header tells the story).  In count
    vocabulary that is one exact equation, no disjunction:

        count (pq_down ... v k) x  =  count hp x - [hp k = x] + [v = x]

    — each trip moves the hole ([hp k := hp j']; the removed duplicate and the
    added one cancel), and the final write closes it with [v].  At
    [pqdownheap]'s call shape [v = hp k], the two indicators cancel and counts
    are preserved exactly. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Huff Trees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import BtWin.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import BtStep.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** The live window [1 .. hlen], as a [wcount] window. *)
Definition lcount (hp : zarr) (hlen x : Z) : Z :=
  wcount hp 1 (Z.to_nat hlen) x.

Lemma lcount_in_window : forall hlen i,
  0 <= hlen -> 1 <= i <= hlen -> 1 <= i < 1 + Z.of_nat (Z.to_nat hlen).
Proof. intros. rewrite Z2Nat.id by lia. lia. Qed.

Lemma lcount_zset : forall hp hlen i v x,
  1 <= i <= hlen ->
  lcount (zset hp i v) hlen x
  = lcount hp hlen x - ind (Z.eqb (hp i) x) + ind (Z.eqb v x).
Proof.
  intros hp hlen i v x Hi. unfold lcount.
  apply wcount_zset_in. apply lcount_in_window; lia.
Qed.

Lemma pq_down_count : forall fuel t dep hp hlen v k x,
  1 <= k <= hlen ->
  lcount (pq_down fuel t dep hp hlen v k) hlen x
  = lcount hp hlen x - ind (Z.eqb (hp k) x) + ind (Z.eqb v x).
Proof.
  induction fuel as [|f IH]; intros t dep hp hlen v k x Hk.
  - cbn [pq_down]. apply lcount_zset. exact Hk.
  - cbn [pq_down].
    destruct (Z.leb (2 * k) hlen) eqn:Ej;
      [apply Z.leb_le in Ej | apply lcount_zset; exact Hk].
    remember (if (Z.ltb (2 * k) hlen)
                 && smaller t dep (hp (2 * k + 1)) (hp (2 * k))
              then 2 * k + 1 else 2 * k) as j' eqn:Ejp.
    assert (Hj' : 1 <= j' <= hlen /\ k < j').
    { subst j'.
      destruct ((Z.ltb (2 * k) hlen)
                  && smaller t dep (hp (2 * k + 1)) (hp (2 * k))) eqn:Eb.
      - apply andb_prop in Eb as [Hlt _]. apply Z.ltb_lt in Hlt. lia.
      - lia. }
    destruct Hj' as [Hj'r Hj'k].
    destruct (smaller t dep v (hp j')) eqn:Es.
    + apply lcount_zset. exact Hk.
    + rewrite (IH t dep (zset hp k (hp j')) hlen v j' x Hj'r).
      rewrite (lcount_zset hp hlen k (hp j') x Hk).
      rewrite zset_other by lia.
      lia.
Qed.

Theorem pqdownheap_count : forall t dep hp hlen k x,
  1 <= k <= hlen ->
  lcount (pqdownheap t dep hp hlen k) hlen x = lcount hp hlen x.
Proof.
  intros t dep hp hlen k x Hk. unfold pqdownheap.
  rewrite (pq_down_count 12%nat t dep hp hlen (hp k) k x Hk). lia.
Qed.

Theorem bt_heapify_count : forall fuel t dep hp hlen n x,
  n <= hlen ->
  lcount (bt_heapify fuel t dep hp hlen n) hlen x = lcount hp hlen x.
Proof.
  induction fuel as [|f IH]; intros t dep hp hlen n x Hn.
  - reflexivity.
  - cbn [bt_heapify].
    destruct (Z.ltb n 1) eqn:E1; [reflexivity|].
    apply Z.ltb_ge in E1.
    rewrite (IH t dep (pqdownheap t dep hp hlen n) hlen (n - 1) x) by lia.
    apply pqdownheap_count. lia.
Qed.

(** Values outside the live window are untouched — count form of
    [BtStep.pqdownheap_outside], stated over an arbitrary window disjoint
    from [1 .. hlen] so both the parked window and single positions consume
    it. *)
Lemma pqdownheap_wcount_out : forall t dep hp hlen k lo n x,
  1 <= k <= hlen -> hlen < lo ->
  wcount (pqdownheap t dep hp hlen k) lo n x = wcount hp lo n x.
Proof.
  intros t dep hp hlen k lo n x Hk Hlo.
  apply wcount_ext_window. intros i Hi.
  apply pqdownheap_outside; [exact Hk | lia].
Qed.

Lemma bt_heapify_wcount_out : forall fuel t dep hp hlen m lo n x,
  m <= hlen -> hlen < lo ->
  wcount (bt_heapify fuel t dep hp hlen m) lo n x = wcount hp lo n x.
Proof.
  induction fuel as [|f IH]; intros t dep hp hlen m lo n x Hm Hlo.
  - reflexivity.
  - cbn [bt_heapify].
    destruct (Z.ltb m 1) eqn:E1; [reflexivity|].
    apply Z.ltb_ge in E1.
    rewrite (IH t dep (pqdownheap t dep hp hlen m) hlen (m - 1) lo n x)
      by lia.
    apply pqdownheap_wcount_out; lia.
Qed.

Print Assumptions pq_down_count.
Print Assumptions pqdownheap_count.
Print Assumptions bt_heapify_count.
Print Assumptions pqdownheap_wcount_out.
Print Assumptions bt_heapify_wcount_out.
