(** * SwInv — the slow-path walk, part W3c: the composite per-trip invariant
      [DsInv], its stability kit, and preservation through the top-of-trip
      fill ([ds_fill]).

    OWNER: q5-emitter (zlib z-repro campaign, 2026-08-19).  G4/W3 of the Q5
    plan; design in WALK-DESIGN.md §DsInv.

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT.

    COORDINATES.  Positions are INPUT indices ([slid + window-index]); the
    consumed input is [zs_done] (SwWin's ghost).  [di_res] is the value
    spine: the tokens tallied since the last flush resolve — against the
    input prefix ending at the block start — to exactly the input consumed
    up to the tally point ([strstart - matchavail]; the [- matchavail] is
    the lazy loop's pending literal). *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk ZBitsOut BwStream Deflate Trees CresChain CbFold.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  SwWin SwFill SwTally SwChain SwLm.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

Local Ltac dsimp :=
  cbn [d_cfg d_status d_lastflush d_wrap d_ts d_ls d_strm
       setD_cfg setD_status setD_lastflush setD_wrap setD_ts setD_ls
       setD_strm fst snd].

(** ** 1. The record *)

Record DsInv (g : DeflGeom) (wrap slid : Z) (Ins : Z -> Prop)
             (toks : list Tok) (s : DSt) : Prop := mkDsInv {
  di_cfg  : d_cfg s = g;
  di_wrap : d_wrap s = wrap;
  di_win  : WinInv g slid (d_ls s) (d_strm s);
  di_ck   : CkInv wrap (d_strm s);
  di_chain: ChainCl g Ins (d_ls s);
  di_buf  : BufToks (ts_symbuf (d_ts s)) 0 (ts_symnext (d_ts s)) toks;
  di_freq : FreqInv toks (d_ts s);
  di_enc  : cEnc toks;
  di_res  : resolve (firstn (Z.to_nat (slid + ls_blockstart (d_ls s)))
                       (zs_done (d_strm s))) toks
            = Some (firstn (Z.to_nat (slid + ls_strstart (d_ls s)
                                      - ls_matchavail (d_ls s)))
                       (zs_done (d_strm s)));
  di_bb0  : 0 <= slid + ls_blockstart (d_ls s);
  di_bble : ls_blockstart (d_ls s)
            <= ls_strstart (d_ls s) - ls_matchavail (d_ls s);
  di_ma   : ls_matchavail (d_ls s) = 0 \/ ls_matchavail (d_ls s) = 1;
  di_ma1  : ls_matchavail (d_ls s) = 1 -> 1 <= ls_strstart (d_ls s);
  di_cand : MatchCand g slid (d_ls s) (zs_done (d_strm s));
  di_pl   : 0 <= ls_prevlen (d_ls s) <= MAX_MATCH;
  di_ml   : 0 <= ls_matchlen (d_ls s) <= MAX_MATCH;
  di_sn   : ts_symnext (d_ts s) < dg_sym_end g
  (* NO bw_wf clause: the bit writer's well-formedness across flushes is
     G1-gated (garbage tree lengths could break it), and the walk never
     reads the writer — the assembly chains wf over the flush events
     instead. *)
}.

(** ** 2. Stability helpers *)

Lemma firstn_app_stable : forall (l nd : list Z) n,
  (n <= length l)%nat ->
  firstn n (l ++ nd) = firstn n l.
Proof.
  intros l nd n Hn.
  rewrite firstn_app.
  replace (n - length l)%nat with 0%nat by lia.
  cbn [firstn]. now rewrite app_nil_r.
Qed.

(** The value spine rides a [StepPres] move: both cut points are conserved
    input indices, and the consumed input only extends. *)
Lemma res_steppres : forall g slid slid' l l' st st' toks,
  WinInv g slid l st ->
  StepPres g slid slid' l l' st st' ->
  0 <= slid + ls_blockstart l ->
  ls_blockstart l <= ls_strstart l - ls_matchavail l ->
  0 <= ls_matchavail l ->
  resolve (firstn (Z.to_nat (slid + ls_blockstart l)) (zs_done st)) toks
    = Some (firstn (Z.to_nat (slid + ls_strstart l - ls_matchavail l))
              (zs_done st)) ->
  resolve (firstn (Z.to_nat (slid' + ls_blockstart l')) (zs_done st')) toks
    = Some (firstn (Z.to_nat (slid' + ls_strstart l' - ls_matchavail l'))
              (zs_done st')).
Proof.
  intros g slid slid' l l' st st' toks HW HP Hbb0 Hbble Hma0 Hres.
  pose proof (sp_bs _ _ _ _ _ _ _ HP) as Ebs.
  pose proof (sp_ss _ _ _ _ _ _ _ HP) as Ess.
  pose proof (sp_ma _ _ _ _ _ _ _ HP) as Ema.
  destruct (sp_donex _ _ _ _ _ _ _ HP) as [nd Ednx].
  pose proof (wi_done _ _ _ _ HW) as Hdn.
  pose proof (wi_la _ _ _ _ HW) as Hla.
  replace (Z.to_nat (slid' + ls_blockstart l'))
    with (Z.to_nat (slid + ls_blockstart l)) by lia.
  replace (Z.to_nat (slid' + ls_strstart l' - ls_matchavail l'))
    with (Z.to_nat (slid + ls_strstart l - ls_matchavail l)) by lia.
  rewrite Ednx.
  rewrite !firstn_app_stable by (unfold zlen in Hdn; lia).
  exact Hres.
Qed.

(** [MatchCand] rides a [StepPres] move: everything it mentions is either
    conserved in input coordinates or grows in its favour. *)
Lemma matchcand_steppres : forall g slid slid' l l' st st',
  WinInv g slid l st ->
  StepPres g slid slid' l l' st st' ->
  MatchCand g slid l (zs_done st) ->
  MatchCand g slid' l' (zs_done st').
Proof.
  intros g slid slid' l l' st st' HW HP HC Hml.
  rewrite (sp_ml _ _ _ _ _ _ _ HP) in Hml.
  destruct (HC Hml) as (Hma & Hms0 & Hd & Hlen & Hla & Hag).
  pose proof (sp_ss _ _ _ _ _ _ _ HP) as Ess.
  pose proof (sp_ms _ _ _ _ _ _ _ HP) as Ems.
  pose proof (sp_lagrow _ _ _ _ _ _ _ HP) as Ela.
  pose proof (sp_ml _ _ _ _ _ _ _ HP) as Eml.
  pose proof (sp_ma _ _ _ _ _ _ _ HP) as Ema.
  destruct (sp_donex _ _ _ _ _ _ _ HP) as [nd Ednx].
  pose proof (wi_done _ _ _ _ HW) as Hdn.
  pose proof (wi_slid _ _ _ _ HW) as Hslid.
  pose proof (wi_la _ _ _ _ HW) as Hlaw.
  repeat split; try lia.
  intros k Hk.
  rewrite Eml in Hk.
  rewrite Ednx.
  unfold zlen in Hdn.
  rewrite !app_nth1 by lia.
  replace (Z.to_nat (slid' + ls_matchstart l' + k))
    with (Z.to_nat (slid + ls_matchstart l + k)) by lia.
  replace (Z.to_nat (slid' + (ls_strstart l' - 1) + k))
    with (Z.to_nat (slid + (ls_strstart l - 1) + k)) by lia.
  apply Hag. exact Hk.
Qed.

(** ** 3. The top-of-trip fill preserves [DsInv] *)

Theorem dsinv_fill : forall g wbits hbits wrap slid Ins toks s,
  GeomOk2 g wbits hbits ->
  DsInv g wrap slid Ins toks s ->
  exists slid' Ins',
    DsInv g wrap slid' Ins' toks (ds_fill s)
    /\ StepPres g slid slid' (d_ls s) (d_ls (ds_fill s))
                (d_strm s) (d_strm (ds_fill s))
    /\ d_ts (ds_fill s) = d_ts s
    /\ d_status (ds_fill s) = d_status s
    /\ d_cfg (ds_fill s) = d_cfg s
    /\ d_wrap (ds_fill s) = d_wrap s.
Proof.
  intros g wbits hbits wrap slid Ins toks s Hg HI.
  pose proof (di_win _ _ _ _ _ _ HI) as HW.
  pose proof (di_ck _ _ _ _ _ _ HI) as HK.
  pose proof (di_chain _ _ _ _ _ _ HI) as HC.
  pose proof (di_cfg _ _ _ _ _ _ HI) as Ecfg.
  pose proof (di_wrap _ _ _ _ _ _ HI) as Ewrap.
  unfold ds_fill, fill_if.
  destruct (ds_need s).
  - (* a real fill *)
    rewrite Ecfg, Ewrap.
    destruct (fill_window_pres g wrap (d_ls s) (d_strm s) slid
                (g2_geom _ _ _ Hg) HW HK) as (slid1 & HP & HK1).
    destruct (fill_window_chain g wbits hbits wrap (d_ls s) (d_strm s) slid
                Ins Hg HW HK HC) as (Ins1 & HC1).
    exists slid1, Ins1.
    split;
      [| split;
         [exact HP
         | dsimp; repeat split;
           first [reflexivity | exact Ecfg | exact Ewrap]]].
    constructor; dsimp; try (rewrite Ecfg + rewrite Ewrap; reflexivity);
      try reflexivity.
    + exact (sp_inv _ _ _ _ _ _ _ HP).
    + exact HK1.
    + exact HC1.
    + exact (di_buf _ _ _ _ _ _ HI).
    + exact (di_freq _ _ _ _ _ _ HI).
    + exact (di_enc _ _ _ _ _ _ HI).
    + apply (res_steppres g slid slid1 (d_ls s) _ (d_strm s) _ toks HW HP).
      * exact (di_bb0 _ _ _ _ _ _ HI).
      * exact (di_bble _ _ _ _ _ _ HI).
      * destruct (di_ma _ _ _ _ _ _ HI) as [E|E]; lia.
      * exact (di_res _ _ _ _ _ _ HI).
    + pose proof (sp_bs _ _ _ _ _ _ _ HP).
      pose proof (di_bb0 _ _ _ _ _ _ HI). lia.
    + (* blockstart <= strstart - matchavail, via conserved input indices *)
      pose proof (sp_bs _ _ _ _ _ _ _ HP).
      pose proof (sp_ss _ _ _ _ _ _ _ HP).
      pose proof (sp_ma _ _ _ _ _ _ _ HP) as Ema.
      pose proof (di_bble _ _ _ _ _ _ HI).
      rewrite Ema. lia.
    + pose proof (sp_ma _ _ _ _ _ _ _ HP) as Ema.
      rewrite Ema. exact (di_ma _ _ _ _ _ _ HI).
    + (* the pending literal stays in-window: unchanged strstart, or the
         post-slide strstart is >= MAX_DIST >= 250 *)
      pose proof (sp_ma _ _ _ _ _ _ _ HP) as Ema.
      pose proof (sp_sslb _ _ _ _ _ _ _ HP) as Esslb.
      pose proof (di_ma1 _ _ _ _ _ _ HI) as Hma1.
      pose proof (go_maxd _ (g2_geom _ _ _ Hg)).
      pose proof (go_ws_lo _ (g2_geom _ _ _ Hg)).
      rewrite Ema. intros E1.
      destruct Esslb as [E|E]; [rewrite E; exact (Hma1 E1) | lia].
    + apply (matchcand_steppres g slid slid1 (d_ls s) _ (d_strm s) _ HW HP).
      exact (di_cand _ _ _ _ _ _ HI).
    + rewrite (sp_pl _ _ _ _ _ _ _ HP). exact (di_pl _ _ _ _ _ _ HI).
    + rewrite (sp_ml _ _ _ _ _ _ _ HP). exact (di_ml _ _ _ _ _ _ HI).
    + exact (di_sn _ _ _ _ _ _ HI).
  - (* no fill: identity *)
    exists slid, Ins.
    split; [exact HI|].
    split; [apply steppres_refl; exact HW|].
    repeat split; first [reflexivity | exact Ecfg | exact Ewrap].
Qed.

Print Assumptions dsinv_fill.
