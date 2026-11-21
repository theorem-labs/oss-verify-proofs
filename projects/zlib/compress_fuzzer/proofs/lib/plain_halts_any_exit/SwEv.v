(** * SwEv — the slow-path walk, part W4a: flush events, and what one
      [flush_block_only] does to the invariant.

    OWNER: q5-emitter (zlib z-repro campaign, 2026-08-19).  G4/W4 of the Q5
    plan.

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT.

    THE EVENT DESIGN.  A flush event snapshots the WHOLE pre-flush [DSt]
    ([fe_s]) plus the [last] flag and the block's input-index span; the
    block's bits are then RECOMPUTABLE ([flush_block_only fe_last fe_s] is a
    function), so the walk does not carry bit-level facts at all.  What the
    per-block assembly needs from the walk is captured by [EvOk]: the token
    facts of the snapshot ([BufToks]/[FreqInv]/[cEnc] — the G1 interface's
    s1-premises), the value spine (the tokens resolve to the block's input
    slice), and the stored-arm's [buf]-is-the-input-slice equation.

    WHY THIS IS ENOUGH, and measured: between two flushes NOTHING touches
    the bit writer or [zs_out] — tallies write [sym_buf]/freqs only
    (SwTally's [TallyFrame]) and the fill machinery never touches [d_ts] at
    all — so the bw of one event's snapshot IS the bw of the previous
    event's flush output, and the assembly's wf/delta induction chains
    event by event with G1's tree facts. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk ZBitsOut BwStream Deflate Trees CresChain CbFold.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  SwWin SwFill SwTally SwChain SwLm SwInv.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

Local Ltac dsimp :=
  cbn [d_cfg d_status d_lastflush d_wrap d_ts d_ls d_strm
       setD_cfg setD_status setD_lastflush setD_wrap setD_ts setD_ls
       setD_strm
       zs_in zs_done zs_out zs_availout zs_totalin zs_totalout zs_adler
       zs_datatype
       setZ_in setZ_done setZ_out setZ_availout setZ_totalin setZ_totalout
       setZ_adler setZ_datatype
       ls_window ls_prev ls_head ls_insh ls_blockstart ls_matchlen
       ls_prevmatch ls_matchavail ls_strstart ls_matchstart ls_lookahead
       ls_prevlen ls_insert ls_highwater ls_windowsize
       setL_window setL_prev setL_head setL_insh setL_blockstart
       setL_matchlen setL_prevmatch setL_matchavail setL_strstart
       setL_matchstart setL_lookahead setL_prevlen setL_insert
       setL_highwater setL_windowsize
       ts_trees ts_maxcode ts_blcount ts_heap ts_heaplen ts_heapmax ts_depth
       ts_symbuf ts_symnext ts_optlen ts_statlen ts_matches ts_bw
       set_trees set_maxcode set_blcount set_heap set_heaplen set_heapmax
       set_depth set_symbuf set_symnext set_optlen set_statlen set_matches
       set_bw set_tree set_max
       fst snd].

(** ** 1. The event *)

Record FlushEv : Type := mkFlushEv {
  fe_s     : DSt;      (** the WHOLE state handed to [flush_block_only] *)
  fe_last  : Z;
  fe_start : Z;        (** input index of the block's first byte *)
  fe_end   : Z;        (** input index one past the block's last byte *)
  fe_toks  : list Tok
}.

Definition EvOk (g : DeflGeom) (wrap : Z) (done : list Z) (ev : FlushEv)
  : Prop :=
  d_cfg (fe_s ev) = g
  /\ d_wrap (fe_s ev) = wrap
  /\ BufToks (ts_symbuf (d_ts (fe_s ev))) 0 (ts_symnext (d_ts (fe_s ev)))
             (fe_toks ev)
  /\ FreqInv (fe_toks ev) (d_ts (fe_s ev))
  /\ cEnc (fe_toks ev)
  /\ 0 <= ts_symnext (d_ts (fe_s ev)) <= dg_sym_end g
  /\ 0 <= fe_start ev <= fe_end ev
  /\ fe_end ev <= zlen done
  /\ resolve (firstn (Z.to_nat (fe_start ev)) done) (fe_toks ev)
       = Some (firstn (Z.to_nat (fe_end ev)) done)
  /\ fe_end ev - fe_start ev
       = ls_strstart (d_ls (fe_s ev)) - ls_blockstart (d_ls (fe_s ev))
  /\ (0 <= ls_blockstart (d_ls (fe_s ev)) ->
      win_take (ls_window (d_ls (fe_s ev)))
               (ls_blockstart (d_ls (fe_s ev)))
               (ls_strstart (d_ls (fe_s ev))
                - ls_blockstart (d_ls (fe_s ev)))
      = firstn (Z.to_nat (fe_end ev - fe_start ev))
          (skipn (Z.to_nat (fe_start ev)) done))
  /\ 0 <= fe_last ev <= 1.

(** Events survive input extension: every clause reads [done] through
    bounded [firstn]/[skipn] windows. *)
Lemma evok_append : forall g wrap done nd ev,
  EvOk g wrap done ev ->
  EvOk g wrap (done ++ nd) ev.
Proof.
  intros g wrap done nd ev HE.
  destruct HE as (H1&H2&H3&[H4a H4b]&H5&H6&H7&H8&H9&H10&H11&H12).
  assert (Hlen : (Z.to_nat (fe_end ev) <= length done)%nat)
    by (unfold zlen in H8; lia).
  assert (Hskip : skipn (Z.to_nat (fe_start ev)) (done ++ nd)
                  = skipn (Z.to_nat (fe_start ev)) done ++ nd).
  { rewrite skipn_app.
    replace (Z.to_nat (fe_start ev) - length done)%nat with 0%nat by lia.
    now cbn [skipn]. }
  repeat split; try assumption; try lia.
  all: try (unfold zlen in *; rewrite length_app; lia).
  all: try (rewrite !firstn_app_stable by lia; exact H9).
  all: intros Hbs;
       rewrite (H11 Hbs), Hskip;
       rewrite firstn_app_stable by (rewrite length_skipn; lia);
       reflexivity.
Qed.

(** ** 2. What the flush machinery does NOT touch *)

Lemma flush_pending_frame : forall s,
  d_ls (flush_pending s) = d_ls s
  /\ d_cfg (flush_pending s) = d_cfg s
  /\ d_wrap (flush_pending s) = d_wrap s
  /\ d_status (flush_pending s) = d_status s
  /\ zs_in (d_strm (flush_pending s)) = zs_in (d_strm s)
  /\ zs_done (d_strm (flush_pending s)) = zs_done (d_strm s)
  /\ zs_adler (d_strm (flush_pending s)) = zs_adler (d_strm s)
  /\ zs_totalin (d_strm (flush_pending s)) = zs_totalin (d_strm s)
  /\ zs_datatype (d_strm (flush_pending s)) = zs_datatype (d_strm s)
  /\ ts_symbuf (d_ts (flush_pending s)) = ts_symbuf (d_ts s)
  /\ ts_symnext (d_ts (flush_pending s)) = ts_symnext (d_ts s)
  /\ ts_trees (d_ts (flush_pending s)) = ts_trees (d_ts s)
  /\ (0 <= zs_availout (d_strm s) ->
      zs_availout (d_strm (flush_pending s)) <= zs_availout (d_strm s)).
Proof.
  intros s. unfold flush_pending, tr_flush_bits. cbv zeta.
  destruct (Z.eqb _ 0) eqn:E; dsimp; repeat split; try reflexivity.
  (* the availout clause, both branches: the move subtracts
     len = min(availout, pending) which is nonnegative *)
  all: intros Havo;
       repeat match goal with
              | |- context [if Z.ltb ?a ?b then _ else _] =>
                  destruct (Z.ltb_spec a b)
              end;
       try lia;
       pose proof (Zle_0_nat (length (bw_out (bw_flush (ts_bw (d_ts s))))));
       unfold zlen in *; lia.
Qed.

Lemma tr_flush_block_post : forall buf slen last level strat dtype ts,
  ts_symnext (snd (tr_flush_block buf slen last level strat dtype ts)) = 0
  /\ FreqInv [] (snd (tr_flush_block buf slen last level strat dtype ts)).
Proof.
  intros buf slen last level strat dtype ts.
  assert (Hinit : forall X, ts_symnext (init_block X) = 0
                  /\ FreqInv [] (init_block X)).
  { intros X. split; [|apply freqinv_init_block].
    unfold init_block. cbv zeta. dsimp. reflexivity. }
  assert (Hbw : forall b Y, ts_symnext (set_bw b Y) = ts_symnext Y
                /\ (FreqInv [] Y -> FreqInv [] (set_bw b Y))).
  { intros b Y. split; [dsimp; reflexivity|].
    intros [HL HD]. split; intros i Hi; dsimp;
      [exact (HL i Hi) | exact (HD i Hi)]. }
  unfold tr_flush_block. cbv zeta.
  destruct (Z.ltb 0 level); cbn [snd];
    (destruct (Z.eqb last 0);
     [ apply Hinit
     | match goal with
       | |- context [set_bw ?b ?Y] => destruct (Hbw b Y) as [Hs Hf]
       end;
       split;
       [ rewrite Hs; exact (proj1 (Hinit _))
       | apply Hf; exact (proj2 (Hinit _)) ] ]).
Qed.

(** ** 3. One [flush_block_only]: the event, and the state that comes back

    Stated on the components rather than on [DsInv], because arm 2 flushes
    at a moment where the [matchavail] bookkeeping is mid-update; the arm
    lemmas re-assemble [DsInv] after their own [strstart] bookkeeping. *)

Theorem flush_block_only_step :
  forall g wbits hbits wrap slid toks s last,
  GeomOk2 g wbits hbits ->
  d_cfg s = g -> d_wrap s = wrap ->
  WinInv g slid (d_ls s) (d_strm s) ->
  CkInv wrap (d_strm s) ->
  BufToks (ts_symbuf (d_ts s)) 0 (ts_symnext (d_ts s)) toks ->
  FreqInv toks (d_ts s) ->
  cEnc toks ->
  ts_symnext (d_ts s) <= dg_sym_end g ->
  0 <= last <= 1 ->
  0 <= slid + ls_blockstart (d_ls s) ->
  ls_blockstart (d_ls s) <= ls_strstart (d_ls s) ->
  resolve (firstn (Z.to_nat (slid + ls_blockstart (d_ls s)))
             (zs_done (d_strm s))) toks
    = Some (firstn (Z.to_nat (slid + ls_strstart (d_ls s)))
              (zs_done (d_strm s))) ->
  let s' := flush_block_only last s in
  let ev := {| fe_s := s; fe_last := last;
               fe_start := slid + ls_blockstart (d_ls s);
               fe_end := slid + ls_strstart (d_ls s);
               fe_toks := toks |} in
  EvOk g wrap (zs_done (d_strm s')) ev
  /\ d_cfg s' = g /\ d_wrap s' = wrap
  /\ WinInv g slid (d_ls s') (d_strm s')
  /\ CkInv wrap (d_strm s')
  /\ BufToks (ts_symbuf (d_ts s')) 0 (ts_symnext (d_ts s')) []
  /\ FreqInv [] (d_ts s')
  /\ ts_symnext (d_ts s') = 0
  /\ ls_blockstart (d_ls s') = ls_strstart (d_ls s)
  /\ ls_strstart (d_ls s') = ls_strstart (d_ls s)
  /\ ls_lookahead (d_ls s') = ls_lookahead (d_ls s)
  /\ ls_matchavail (d_ls s') = ls_matchavail (d_ls s)
  /\ ls_matchlen (d_ls s') = ls_matchlen (d_ls s)
  /\ ls_prevlen (d_ls s') = ls_prevlen (d_ls s)
  /\ ls_prevmatch (d_ls s') = ls_prevmatch (d_ls s)
  /\ ls_matchstart (d_ls s') = ls_matchstart (d_ls s)
  /\ ls_window (d_ls s') = ls_window (d_ls s)
  /\ ls_prev (d_ls s') = ls_prev (d_ls s)
  /\ ls_head (d_ls s') = ls_head (d_ls s)
  /\ ls_insh (d_ls s') = ls_insh (d_ls s)
  /\ ls_insert (d_ls s') = ls_insert (d_ls s)
  /\ ls_windowsize (d_ls s') = ls_windowsize (d_ls s)
  /\ zs_done (d_strm s') = zs_done (d_strm s)
  /\ zs_in (d_strm s') = zs_in (d_strm s)
  /\ zs_totalin (d_strm s') = zs_totalin (d_strm s)
  /\ (0 <= zs_availout (d_strm s) ->
      zs_availout (d_strm s') <= zs_availout (d_strm s)).
Proof.
  intros g wbits hbits wrap slid toks s last
         Hg Ecfg Ewrap HW HK Hbuf Hfreq Henc Hsn Hlast Hbb0 Hbble Hres
         s' ev.
  (* the state shape: flush_pending (setD_ls .. (setD_ts .. (setD_strm ..))) *)
  unfold s', flush_block_only. cbv zeta.
  set (r := tr_flush_block _ _ _ _ _ _ _).
  set (s2 := setD_ls _ _).
  destruct (flush_pending_frame s2)
    as (Fls & Fcfg & Fwrap & Fstat & Fin & Fdone & Fad & Fti & Fdt
        & Fsb & Fsn & Ftr & Favo).
  assert (Es2ls : d_ls s2 = setL_blockstart (ls_strstart (d_ls s)) (d_ls s))
    by (unfold s2; dsimp; reflexivity).
  assert (Es2strm : zs_done (d_strm s2) = zs_done (d_strm s)
                    /\ zs_in (d_strm s2) = zs_in (d_strm s)
                    /\ zs_adler (d_strm s2) = zs_adler (d_strm s)
                    /\ zs_totalin (d_strm s2) = zs_totalin (d_strm s))
    by (unfold s2; dsimp; repeat split; reflexivity).
  destruct Es2strm as (E2done & E2in & E2ad & E2ti).
  assert (E2ts : d_ts s2 = snd r) by (unfold s2; dsimp; reflexivity).
  destruct (tr_flush_block_post
              (if Z.leb 0 (ls_blockstart (d_ls s))
               then Some (win_take (ls_window (d_ls s))
                            (ls_blockstart (d_ls s))
                            (ls_strstart (d_ls s) - ls_blockstart (d_ls s)))
               else None)
              (ls_strstart (d_ls s) - ls_blockstart (d_ls s))
              last (dg_level (d_cfg s)) (dg_strategy (d_cfg s))
              (zs_datatype (d_strm s)) (d_ts s)) as [Hpsn Hpfreq].
  assert (Ednfinal : zs_done (d_strm (flush_pending s2))
                     = zs_done (d_strm s)) by (rewrite Fdone; exact E2done).
  split.
  { (* the event *)
    unfold EvOk, ev. cbn [fe_s fe_last fe_start fe_end fe_toks].
    rewrite Ednfinal.
    pose proof (wi_done _ _ _ _ HW) as Hdn.
    pose proof (wi_la _ _ _ _ HW) as Hla.
    pose proof (wi_slid _ _ _ _ HW) as Hslid.
    pose proof (wi_ss _ _ _ _ HW) as Hss.
    pose proof (buftoks_extent _ _ _ _ Hbuf) as Hext.
    repeat split; try assumption; try lia.
    all: try (exact (proj1 Hfreq)).
    all: try (exact (proj2 Hfreq)).
    (* the buf clause *)
    all: intros Hbs;
      replace (slid + ls_strstart (d_ls s) - (slid + ls_blockstart (d_ls s)))
        with (ls_strstart (d_ls s) - ls_blockstart (d_ls s)) by lia;
      apply (wininv_take g slid (d_ls s) (d_strm s)); try assumption; lia. }
  repeat apply conj.
  (* the [d_ls] projections (blockstart set, everything else framed) *)
  all: try (rewrite Fls, Es2ls; dsimp; reflexivity).
  (* untouched stream fields *)
  all: try (rewrite Fin, E2in; reflexivity).
  all: try (rewrite Fdone, E2done; reflexivity).
  all: try (rewrite Fti, E2ti; reflexivity).
  (* cfg / wrap through both layers *)
  all: try (rewrite Fcfg; unfold s2; dsimp; assumption).
  all: try (rewrite Fwrap; unfold s2; dsimp; assumption).
  (* symnext = 0, and the empty token reading *)
  all: try (rewrite Fsn, E2ts; unfold r; exact Hpsn).
  all: try (rewrite Fsn, E2ts; unfold r; rewrite Hpsn; constructor).
  (* the two FreqInv components *)
  all: try (intros i Hi; rewrite Ftr, E2ts; exact (proj1 Hpfreq i Hi)).
  all: try (intros i Hi; rewrite Ftr, E2ts; exact (proj2 Hpfreq i Hi)).
  (* availout can only shrink *)
  all: try (intros Havo;
            assert (E2avo : zs_availout (d_strm s2) = zs_availout (d_strm s))
              by (unfold s2; dsimp; reflexivity);
            specialize (Favo ltac:(lia)); lia).
  (* CkInv's two components ([apply conj] splits the definition) *)
  all: try (intros ->; rewrite Fad, E2ad, Fdone, E2done;
            exact (proj1 HK eq_refl)).
  all: try (intros ->; rewrite Fad, E2ad, Fdone, E2done;
            exact (proj2 HK eq_refl)).
  (* WinInv *)
  all: try (destruct HW as [W1 W2 W3 W4 W5 W6 W7 W8 W9 W10];
            rewrite Fls, Es2ls;
            constructor; dsimp; try assumption;
            [ rewrite Fdone, E2done; assumption
            | rewrite Fti, E2ti, Fdone, E2done; assumption
            | rewrite Fdone, E2done; assumption
            | rewrite Fin, E2in; assumption
            | intros i Hi; rewrite Fdone, E2done; now apply W10 ]).
Qed.

Print Assumptions flush_block_only_step.
Print Assumptions evok_append.
