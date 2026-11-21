(** * ZReproG6K — G6 bound-fit, part K: the whole-stream fold.

    OWNER: g6-bound (zlib z-repro campaign, 2026-08-20).

    The per-event budget (part J, [flush_block_only_acct]) summed along
    q5-emitter's [EvChain] output ledger and [EvTile] input ledger: the
    whole run's [ceil8] potential grows by at most [8 * (total input
    span) + 40 * (#blocks)].  Combined with the room lemma (part I) — which
    bounds [40 * #blocks] i.e. [5 bytes * #blocks] by the [deflateBound]
    shift terms — this is the whole-stream bound-fit inequality.

    SPELLING-INDEPENDENT by design: the fold takes the per-event budget as
    an abstract per-event predicate [EvBudget], exactly the projection
    [flush_block_only_acct] proves.  It therefore does not depend on how
    the walk spells its snapshot facts; the walk lane discharges
    [Forall EvBudget evs] however it likes.

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Chunk ZBitsOut BwStream Trees CbFold Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import ZReproL0 SwTally
  SwWin SwFill SwChain SwLm SwInv SwEv SwArmPre SwArm2 SwArm3 SwArm1a
  SwArm1b SwDrain SwStep ZReproG6A.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(** The chain-level potential, from an accumulator pair. *)
Definition cb_tot (bw : BW) (out : list Z) : Z :=
  8 * zlen out + zbits bw.

(** The per-event budget, as the walk must supply it (= part J's
    conclusion projected onto the [ceil8]/monotone clauses). *)
Definition EvBudget (ev : FlushEv) : Prop :=
  let s := fe_s ev in
  let s' := flush_block_only (fe_last ev) (fe_s ev) in
  cb_tot (ts_bw (d_ts s)) (zs_out (d_strm s))
    <= cb_tot (ts_bw (d_ts s')) (zs_out (d_strm s'))
  /\ ceil8 (cb_tot (ts_bw (d_ts s')) (zs_out (d_strm s')))
     <= ceil8 (cb_tot (ts_bw (d_ts s)) (zs_out (d_strm s)))
        + 8 * (fe_end ev - fe_start ev) + 40
  /\ fe_start ev <= fe_end ev.

(** THE FOLD.  [EvChain] threads the exact accumulators [cb_tot] reads,
    and [EvTile] telescopes the per-event spans into [bst' - bst]. *)
Theorem evchain_ceil8 : forall evs bw out avo bw' out' avo' bst bst',
  EvChain evs bw out avo bw' out' avo' ->
  EvTile evs bst bst' ->
  Forall EvBudget evs ->
  cb_tot bw out <= cb_tot bw' out'
  /\ ceil8 (cb_tot bw' out')
     <= ceil8 (cb_tot bw out) + 8 * (bst' - bst) + 40 * Z.of_nat (length evs).
Proof.
  induction evs as [|ev evs IH];
    intros bw out avo bw' out' avo' bst bst' HCh HTl HFa.
  - (* empty chain: accumulators unchanged, no span *)
    cbn [EvChain] in HCh. destruct HCh as (-> & -> & _).
    cbn [EvTile] in HTl. subst bst'.
    cbn [length].
    split; [lia|].
    replace (bst - bst) with 0 by lia.
    replace (Z.of_nat 0) with 0 by reflexivity. lia.
  - (* one event, then the tail *)
    cbn [EvChain] in HCh.
    destruct HCh as (Hbw & Hout & Havo & HCh').
    cbn [EvTile] in HTl. destruct HTl as (Hst & HTl').
    inversion HFa as [|ev0 evs0 HB HFa' [Eev0 Eevs0]].
    unfold EvBudget in HB.
    set (s := fe_s ev) in *.
    set (s' := flush_block_only (fe_last ev) s) in *.
    destruct HB as (HBmono & HBceil & HBspan).
    (* the tail runs from the flush's accumulators *)
    destruct (IH (ts_bw (d_ts s')) (zs_out (d_strm s'))
                 (zs_availout (d_strm s')) bw' out' avo'
                 (fe_end ev) bst' HCh' HTl' HFa')
      as [IHmono IHceil].
    (* connect this event's start accumulators to (bw, out) *)
    unfold cb_tot in *.
    rewrite <- Hbw, <- Hout.
    split.
    + (* monotone across the whole chain *)
      eapply Z.le_trans; [exact HBmono | exact IHmono].
    + (* ceil8 telescopes *)
      cbn [length]. rewrite Nat2Z.inj_succ.
      eapply Z.le_trans; [exact IHceil|].
      rewrite <- Hst.
      (* now: ceil8(s') + 8(bst'-fe_end) + 40|evs|
              <= ceil8(s) + 8(bst'-fe_start) + 40*succ|evs|,
         closed by HBceil (ceil8 s' <= ceil8 s + 8(fe_end-fe_start) + 40) *)
      lia.
Qed.

(** The whole-run budget in [tot_bits] terms, at a run that starts and
    ends on the SAME output-vs-writer accumulators the walk reports (so a
    consumer can read it straight off [deflate_slow_finish]'s EvChain). *)
Corollary evchain_tot_bits : forall evs s0 s1 avo0 avo1 bst bst',
  EvChain evs (ts_bw (d_ts s0)) (zs_out (d_strm s0)) avo0
              (ts_bw (d_ts s1)) (zs_out (d_strm s1)) avo1 ->
  EvTile evs bst bst' ->
  Forall EvBudget evs ->
  tot_bits s0 <= tot_bits s1
  /\ ceil8 (tot_bits s1)
     <= ceil8 (tot_bits s0) + 8 * (bst' - bst) + 40 * Z.of_nat (length evs).
Proof.
  intros evs s0 s1 avo0 avo1 bst bst' HCh HTl HFa.
  destruct (evchain_ceil8 evs _ _ _ _ _ _ _ _ HCh HTl HFa)
    as [Hmono Hceil].
  unfold cb_tot in Hmono, Hceil.
  unfold tot_bits, zbw.
  split.
  - rewrite (Z.add_comm (8 * zlen (zs_out (d_strm s0)))).
    rewrite (Z.add_comm (8 * zlen (zs_out (d_strm s1)))). lia.
  - rewrite (Z.add_comm (8 * zlen (zs_out (d_strm s0)))
                        (zbits (ts_bw (d_ts s0)))) in Hceil.
    rewrite (Z.add_comm (8 * zlen (zs_out (d_strm s1)))
                        (zbits (ts_bw (d_ts s1)))) in Hceil.
    unfold tot_bits, zbw.
    rewrite (Z.add_comm (8 * zlen (zs_out (d_strm s0)))
                        (zbits (ts_bw (d_ts s0)))).
    rewrite (Z.add_comm (8 * zlen (zs_out (d_strm s1)))
                        (zbits (ts_bw (d_ts s1)))).
    exact Hceil.
Qed.

Set Printing All.
Set Printing Fully Qualified.
Set Printing Depth 10000000000.
Set Printing Width 2000.
Print Assumptions evchain_ceil8.
Print Assumptions evchain_tot_bits.
Unset Printing All.
