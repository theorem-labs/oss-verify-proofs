
From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Chunk ZBitsOut BwStream Trees CbFold Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import ZReproL0 SwTally
  SwWin SwEv SwStep G3Event ZRepro ZReproG6A ZReproG6H ZReproG6I ZReproG6J
  ZReproG6K.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ==========================================================================
   1.  The per-event step (= flush_block_only_acct's conclusion), and the
       availout-drain fold.
   ========================================================================== *)

Definition EvStepBudget (ev : FlushEv) : Prop :=
  let s := fe_s ev in
  let s' := flush_block_only (fe_last ev) s in
  cb_tot (ts_bw (d_ts s)) (zs_out (d_strm s))
    <= cb_tot (ts_bw (d_ts s')) (zs_out (d_strm s'))
  /\ ceil8 (cb_tot (ts_bw (d_ts s')) (zs_out (d_strm s')))
     <= ceil8 (cb_tot (ts_bw (d_ts s)) (zs_out (d_strm s)))
        + 8 * (fe_end ev - fe_start ev) + 40
  /\ fe_start ev <= fe_end ev
  /\ zs_availout (d_strm s')
     = zs_availout (d_strm s)
       - (zlen (zs_out (d_strm s')) - zlen (zs_out (d_strm s)))
  /\ zlen (zs_out (d_strm s)) <= zlen (zs_out (d_strm s')).

(** [EvStepBudget] is stronger than part K's [EvBudget]. *)
Lemma evstep_to_evbudget : forall ev, EvStepBudget ev -> EvBudget ev.
Proof.
  intros ev (H1 & H2 & H3 & _ & _). unfold EvBudget. tauto.
Qed.

(** The availout-drain fold: [avail_out] falls by exactly the emitted
    bytes, and output only grows. *)
Lemma evchain_avo : forall evs bw out avo bw' out' avo',
  EvChain evs bw out avo bw' out' avo' ->
  Forall EvStepBudget evs ->
  avo' = avo - (zlen out' - zlen out) /\ zlen out <= zlen out'.
Proof.
  induction evs as [|ev evs IH];
    intros bw out avo bw' out' avo' HCh HFa.
  - cbn [EvChain] in HCh. destruct HCh as (-> & -> & ->).
    split; [ring | lia].
  - cbn [EvChain] in HCh.
    destruct HCh as (Hbw & Hout & Havo & HCh').
    inversion HFa as [|ev0 evs0 HB HFa' [Eev0 Eevs0]].
    unfold EvStepBudget in HB.
    destruct HB as (_ & _ & _ & HBavo & HBout).
    destruct (IH (ts_bw (d_ts (flush_block_only (fe_last ev) (fe_s ev))))
                 (zs_out (d_strm (flush_block_only (fe_last ev) (fe_s ev))))
                 (zs_availout (d_strm (flush_block_only (fe_last ev) (fe_s ev))))
                 bw' out' avo' HCh' HFa')
      as [IHavo IHout].
    rewrite <- Hout, <- Havo.
    split; [rewrite IHavo, HBavo; ring | lia].
Qed.

(* ==========================================================================
   2.  The bridge: part J discharges EvStepBudget from the walk facts.
   ========================================================================== *)

Lemma flush_from_acct : forall g wrap done ev,
  EvOk g wrap done ev ->
  0 < dg_level g -> dg_strategy g = 0 -> dg_sym_end g <= 49149 ->
  bwv (ts_bw (d_ts (fe_s ev))) ->
  0 <= zs_availout (d_strm (fe_s ev)) ->
  0 <= ls_blockstart (d_ls (fe_s ev)) ->
  ts_optlen (d_ts (fe_s ev)) = 0 ->
  ts_statlen (d_ts (fe_s ev)) = 0 ->
  (forall b, b < 0 \/ 15 < b -> ts_blcount (d_ts (fe_s ev)) b = 0) ->
  (forall v, 0 <= v < 19 -> t_freq (ts_trees (d_ts (fe_s ev)) TK_BL) v = 0) ->
  (forall i, 0 <= t_len (ts_trees (d_ts (fe_s ev)) TK_L) i) ->
  (forall i, 0 <= t_len (ts_trees (d_ts (fe_s ev)) TK_D) i) ->
  EvStepBudget ev.
Proof.
  intros g wrap done ev HE Hlev Hstrat Hsend Hbwv Havo Hbs Hol Hsl Hbl
         HblZ HnnL HnnD.
  destruct (flush_block_only_acct g wrap done ev HE Hlev Hstrat Hsend Hbwv
              Havo Hbs Hol Hsl Hbl HblZ HnnL HnnD)
    as (Hm & Hc & Hbwv' & Havorel & Hgrow & _).
  (* EvOk gives the span equation [fe_start <= fe_end] *)
  destruct HE as (_ & _ & _ & _ & _ & _ & Hspan & _).
  unfold EvStepBudget, cb_tot.
  unfold tot_bits, zbw in Hm, Hc.
  repeat split.
  - exact Hm.
  - exact Hc.
  - lia.
  - exact Havorel.
  - exact Hgrow.
Qed.

(* ==========================================================================
   3.  The bound-fit capstone (NeedMore refutation), conditional.
   ========================================================================== *)

Section BoundFit.

  Variable x : list Z.
  Variable evs : list FlushEv.
  Variable bw0 bwf : BW.
  Variable out0 outf : list Z.
  Variable avo0 avof : Z.

  (** input under the driver cap ([ZR_Input]'s size clause) *)
  Hypothesis Hx : 0 <= zlen x < ZR_MAX_INPUT.

  (** the walk's output ledger, from the body start to the last block *)
  Hypothesis Hchain : EvChain evs bw0 out0 avo0 bwf outf avof.
  (** the input position the last block reached (= |zs_done| there); in the
      final-block arm it equals [zlen x], in the NeedMore arm a prefix *)
  Variable T : Z.
  Hypothesis HT : 0 <= T <= zlen x.
  (** the walk's input ledger: blocks tile the consumed prefix *)
  Hypothesis Htile  : EvTile evs 0 T.
  (** the per-event budget (part J discharges each) *)
  Hypothesis Hbudget : Forall EvStepBudget evs.
  (** block count: full blocks cover >= 16383 input bytes (walk fact) *)
  Hypothesis Hblocks : Z.of_nat (length evs) <= zr_hnblocks (zlen x).

  (** the body starts on a drained writer at the two zlib-header bytes,
      with [avail_out] the bound minus those two bytes *)
  Hypothesis Hout0 : zlen out0 = 2.
  Hypothesis Hbw0  : zbits bw0 = 0.
  Hypothesis Havo0 : avo0 = zr_deflate_bound 15 (zlen x) - 2.

  (** THE BOUND FITS: the last block leaves >= 4 output bytes — exactly the
      zlib trailer's room — so the walk never exits [NeedMore]. *)
  Theorem zr_bound_fits : 4 <= avof.
  Proof.
    set (B := zr_deflate_bound 15 (zlen x)) in *.
    pose proof (zlen_nonneg x) as Hxn.
    (* the whole-run ceil8 bound (part K) *)
    destruct (evchain_ceil8 evs bw0 out0 avo0 bwf outf avof 0 T
                Hchain Htile
                (Forall_impl _ evstep_to_evbudget Hbudget))
      as [_ Hceil].
    (* the availout drain (this file) *)
    destruct (evchain_avo evs bw0 out0 avo0 bwf outf avof Hchain Hbudget)
      as [Havof Hgrow].
    (* start potential is exactly 16 *)
    assert (Hstart : cb_tot bw0 out0 = 16)
      by (unfold cb_tot; rewrite Hout0, Hbw0; reflexivity).
    rewrite Hstart in Hceil.
    replace (ceil8 16) with 16 in Hceil by reflexivity.
    (* the room lemma (part I), scaled by 8 *)
    pose proof (zr_room_bound (zlen x) Hx) as Hroom.
    unfold zr_hnblocks in Hblocks, Hroom.
    fold B in Hroom.
    (* 8 * |outf| <= cb_tot bwf outf <= ceil8(cb_tot bwf outf) *)
    pose proof (ceil8_ge (cb_tot bwf outf)) as Hcg.
    pose proof (zbits_nonneg bwf) as Hbf.
    assert (Hcb : 8 * zlen outf <= cb_tot bwf outf)
      by (unfold cb_tot; lia).
    (* chain the inequalities: |outf| <= B - 4 *)
    assert (Houtf : zlen outf <= B - 4).
    { assert (Hbnd : 8 * zlen outf
                     <= 16 + 8 * (zlen x - 0) + 40 * Z.of_nat (length evs))
        by lia.
      assert (Hblk8 : 40 * Z.of_nat (length evs)
                      <= 40 * (zlen x / 16383 + 1)) by lia.
      lia. }
    (* avof = B - |outf| >= 4 *)
    rewrite Havof, Hout0, Havo0. fold B. lia.
  Qed.

  (** ...hence the [NeedMore] arm (exported with [avail_out = 0]) is
      contradictory: the harness's bound-violation path is dead. *)
  Corollary zr_needmore_refuted : avof = 0 -> False.
  Proof. intro H0. pose proof zr_bound_fits. lia. Qed.

End BoundFit.

Set Printing All.
Set Printing Fully Qualified.
Set Printing Depth 10000000000.
Set Printing Width 2000.
Print Assumptions zr_bound_fits.
Print Assumptions zr_needmore_refuted.
Print Assumptions flush_from_acct.
Print Assumptions evchain_avo.
Unset Printing All.
