(** * DfArm — the fast-path walk, part F1: [df_body]'s dispatch-point facts.

    OWNER: q5-emitter (zlib z-repro campaign, 2026-08-20; GAP7 D1, the
    deflate_fast walk toward [zr_emitter_l1_raw_frame]).

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT.

    [df_body] shares [deflate_slow]'s top step verbatim ([dsb_ph] IS the
    fast hash-insert conditional), then goes straight to a fresh
    [longest_match] under a two-conjunct guard — no lazy shift, no
    TOO_FAR filter.  This file derives, from [DsInv] plus the fast-path
    side facts [DfSide], everything the two arms consume at the
    dispatch point [MIN_MATCH <=? ls_matchlen l1].

    [DfSide]: on the fast walk [matchavail] is never set and [prevlen]
    is never rebound after the reset (no lazy bookkeeping), so both ride
    as an invariant pair.  They matter twice: [di_cand]'s conclusion
    forces [matchavail = 1] on any inherited candidate, refuting the
    guard-fail-with-a-match case, and [longest_match]'s prev-dominates
    arm returns [prevlen]-bounded lengths, refuted below [MIN_MATCH]. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk ZBitsOut BwStream Deflate Trees CresChain CbFold.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  SwWin SwFill SwTally SwChain SwLm SwInv SwArmPre ZRTreeState.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

Local Ltac lsimp :=
  cbn [ls_window ls_prev ls_head ls_strstart ls_lookahead ls_blockstart
       ls_matchstart ls_matchlen ls_prevlen ls_prevmatch ls_matchavail
       ls_windowsize ls_insert ls_insh
       setL_window setL_prev setL_head setL_strstart setL_lookahead
       setL_blockstart setL_matchstart setL_matchlen setL_prevlen
       setL_prevmatch setL_matchavail setL_windowsize setL_insert
       setL_insh fst snd].

(** The fast-path side pins (an earlier development run census W11/W12: [prev_length]
    is never written after the reset, and [match_length] lands on 0 at
    both match sub-arm exits — the stale value is the init 2; 1 never
    occurs). *)
Definition DfSide (l : LSt) : Prop :=
  ls_matchavail l = 0
  /\ ls_prevlen l = 2
  /\ (ls_matchlen l = 0 \/ ls_matchlen l = 2).

(** The per-snapshot tree bundle the raw shell's decode engine consumes
    (the fast-path analog of the slow walk's EvSnapOk, REDUCED: no
    es_far — deflate_fast has no TOO_FAR filter, so that clause is
    false on this path and nothing here consumes it). *)
Definition DfSnap (ts : TSt) : Prop :=
  ZRTreeInv ts /\ ts_optlen ts = 0 /\ ts_statlen ts = 0.

(** The slide-span floor: whenever a window slide has pushed
    [block_start] negative, the pending block already spans more than
    [dg_max_dist g] bytes.  A NEW inductive state invariant threaded
    beside [DsInv] (not a field: the constructor sites are fleet-wide);
    stream-entry states have [blockstart = 0], so the premise is
    vacuous there.  Preservation: body steps only grow [strstart] with
    [blockstart] fixed; a fill's slide moves both down together
    ([sp_ss]/[sp_bs]) and lands [strstart] at or above [dg_max_dist]
    ([sp_sslb], the birth case); a flush resets
    [blockstart := strstart >= 0]. *)
Definition BsFloor (g : DeflGeom) (s : DSt) : Prop :=
  ls_blockstart (d_ls s) < 0 ->
  dg_max_dist g < ls_strstart (d_ls s) - ls_blockstart (d_ls s).

(** [BsFloor] survives any [StepPres] move (in particular [ds_fill]'s
    slide): the span is conserved and a slide that can newly expose a
    negative [blockstart] leaves [strstart] at or above
    [dg_max_dist]. *)
Lemma bsfloor_steppres : forall g slid slid' l l' st st',
  StepPres g slid slid' l l' st st' ->
  (ls_blockstart l < 0 ->
   dg_max_dist g < ls_strstart l - ls_blockstart l) ->
  (ls_blockstart l' < 0 ->
   dg_max_dist g < ls_strstart l' - ls_blockstart l').
Proof.
  intros g slid slid' l l' st st' HP HF Hneg.
  pose proof (sp_ss _ _ _ _ _ _ _ HP) as Ess.
  pose proof (sp_bs _ _ _ _ _ _ _ HP) as Ebs.
  destruct (sp_sslb _ _ _ _ _ _ _ HP) as [E|E].
  - assert (Hbs : ls_blockstart l < 0) by lia.
    pose proof (HF Hbs). lia.
  - lia.
Qed.

(** [df_body]'s let-tower, exposed for the step lemma (mirror of
    [ds_body_shape]). *)
Lemma df_body_shape : forall flush p0,
  df_body flush p0
  = (let g := d_cfg p0 in
     let ph := dsb_ph g (d_ls p0) in
     let hash_head := fst ph in
     let l0 := snd ph in
     let l1 := if negb (Z.eqb hash_head NIL)
                  && (Z.leb (ls_strstart l0 - hash_head) (dg_max_dist g))
               then let r := longest_match g l0 hash_head in
                    setL_matchstart (snd r) (setL_matchlen (fst r) l0)
               else l0 in
     let s2 := setD_ls l1 p0 in
     if Z.leb MIN_MATCH (ls_matchlen l1) then
       let tt := tr_tally_dist (ls_strstart l1 - ls_matchstart l1)
                               (ls_matchlen l1 - MIN_MATCH)
                               (dg_sym_end g) (d_ts s2) in
       let l2 := setL_lookahead (ls_lookahead l1 - ls_matchlen l1) l1 in
       let l4 :=
         if (Z.leb (ls_matchlen l2) (dg_max_lazy_match g))
            && (Z.leb MIN_MATCH (ls_lookahead l2)) then
           let l3 := setL_matchlen (ls_matchlen l2 - 1) l2 in
           let l3b := df_insert (Z.to_nat (ls_matchlen l3) + 1) g
                        (ls_matchlen l3) l3 in
           setL_strstart (ls_strstart l3b + 1) (setL_matchlen 0 l3b)
         else
           let l3 := setL_matchlen 0
                       (setL_strstart (ls_strstart l2 + ls_matchlen l2) l2) in
           let h0 := ls_window l3 (ls_strstart l3) in
           setL_insh (update_hash g h0 (ls_window l3 (ls_strstart l3 + 1))) l3 in
       let s3 := setD_ls l4 (setD_ts (snd tt) s2) in
       if fst tt then
         match flush_block 0 s3 with
         | (Some bs, s4) => DsRet bs s4
         | (None, s4) => DsCont s4
         end
       else DsCont s3
     else
       let tt := tr_tally_lit (ls_window l1 (ls_strstart l1)) (dg_sym_end g)
                              (d_ts s2) in
       let s3 := setD_ls (setL_strstart (ls_strstart l1 + 1)
                           (setL_lookahead (ls_lookahead l1 - 1) l1))
                         (setD_ts (snd tt) s2) in
       if fst tt then
         match flush_block 0 s3 with
         | (Some bs, s4) => DsRet bs s4
         | (None, s4) => DsCont s4
         end
       else DsCont s3).
Proof.
  intros flush p0.
  unfold df_body, dsb_ph. cbv zeta.
  reflexivity.
Qed.

(** The dispatch-point facts. *)
Theorem df_top_facts : forall g wbits hbits wrap slid Ins toks s,
  GeomOk2 g wbits hbits ->
  DsInv g wrap slid Ins toks s ->
  DfSide (d_ls s) ->
  exists Ins2,
    let l := d_ls s in
    let ph := dsb_ph g l in
    let hash_head := fst ph in
    let l0 := snd ph in
    let l1 := if negb (Z.eqb hash_head NIL)
                 && (Z.leb (ls_strstart l0 - hash_head) (dg_max_dist g))
              then let r := longest_match g l0 hash_head in
                   setL_matchstart (snd r) (setL_matchlen (fst r) l0)
              else l0 in
    ChainInv g (ls_window l1) (ls_prev l1) (ls_head l1)
             (ls_strstart l1) (ls_lookahead l1) Ins2
    /\ (forall p, Ins2 p -> p <= ls_strstart l)
    /\ ls_window l1 = ls_window l
    /\ ls_strstart l1 = ls_strstart l
    /\ ls_lookahead l1 = ls_lookahead l
    /\ ls_blockstart l1 = ls_blockstart l
    /\ ls_matchavail l1 = 0
    /\ ls_windowsize l1 = ls_windowsize l
    /\ ls_insert l1 = ls_insert l
    /\ ls_prevlen l1 = 2
    /\ (ls_matchlen l1 = ls_matchlen l \/ ls_matchlen l1 = 2
        \/ MIN_MATCH <= ls_matchlen l1)
    /\ (MIN_MATCH <= ls_lookahead l ->
        ls_insh l1 = h3 g (ls_window l) (ls_strstart l))
    /\ 0 <= ls_matchlen l1 <= MAX_MATCH
    /\ (MIN_MATCH <= ls_matchlen l1 ->
        ls_matchlen l1 <= ls_lookahead l
        /\ 0 <= slid + ls_matchstart l1
        /\ 1 <= ls_strstart l - ls_matchstart l1 <= dg_max_dist g
        /\ forall k, 0 <= k < ls_matchlen l1 ->
             nth (Z.to_nat (slid + ls_matchstart l1 + k))
                 (zs_done (d_strm s)) 0
             = nth (Z.to_nat (slid + ls_strstart l + k))
                   (zs_done (d_strm s)) 0).
Proof.
  intros g wbits hbits wrap slid Ins toks s Hg HI (Hma0 & Hpl2 & Hml02).
  pose proof (di_win _ _ _ _ _ _ HI) as HW.
  pose proof (di_chain _ _ _ _ _ _ HI) as HC.
  pose proof (di_cand _ _ _ _ _ _ HI) as Hcand0.
  pose proof (di_ml _ _ _ _ _ _ HI) as Hml0.
  destruct HC as [Hcinv Hchi Hcins0 Hcsync].
  pose proof (wi_ss _ _ _ _ HW) as Hss.
  pose proof (wi_la _ _ _ _ HW) as Hla.
  pose proof (wi_room _ _ _ _ HW) as Hroom.
  pose proof (wi_wsize _ _ _ _ HW) as Hwsz.
  pose proof (wi_slid _ _ _ _ HW) as Hslid.
  pose proof (g2_u16 _ _ _ Hg) as Hu16g.
  cbv zeta.
  unfold dsb_ph.
  destruct (Z.leb_spec MIN_MATCH (ls_lookahead (d_ls s))) as [Hla3|Hla3].
  - (* the insert runs *)
    destruct (insert_string_fields g (d_ls s) (ls_strstart (d_ls s)))
      as (Ehead & Einsh & Ehd & Epr & Ewin & Ess & Ela).
    cbv zeta in Ehead, Einsh, Ehd, Epr, Ewin, Ess, Ela.
    set (hh := update_hash g (ls_insh (d_ls s))
                 (ls_window (d_ls s)
                    (ls_strstart (d_ls s) + MIN_MATCH - 1))) in *.
    assert (Ehh : hh = h3 g (ls_window (d_ls s)) (ls_strstart (d_ls s))).
    { unfold hh.
      replace (ls_strstart (d_ls s) + MIN_MATCH - 1)
        with (ls_strstart (d_ls s) + 2) by (unfold MIN_MATCH; lia).
      apply Hcsync; [exact Hcins0 | lia]. }
    assert (Hhh : 0 <= hh < dg_hash_size g).
    { unfold hh, update_hash.
      rewrite (g2_hm _ _ _ Hg), (g2_hs _ _ _ Hg).
      replace (2 ^ hbits - 1) with (Z.ones hbits)
        by (rewrite Z.ones_equiv; lia).
      rewrite Z.land_ones by (exact (g2_hb0 _ _ _ Hg)).
      apply Z.mod_pos_bound.
      apply Z.pow_pos_nonneg; [lia | exact (g2_hb0 _ _ _ Hg)]. }
    (* projection frames of the post-insert state *)
    assert (Emsli : ls_matchstart (snd (insert_string g (ls_strstart (d_ls s)) (d_ls s)))
                    = ls_matchstart (d_ls s))
      by (unfold insert_string; lsimp; reflexivity).
    assert (Emlli : ls_matchlen (snd (insert_string g (ls_strstart (d_ls s)) (d_ls s)))
                    = ls_matchlen (d_ls s))
      by (unfold insert_string; lsimp; reflexivity).
    assert (Ebsli : ls_blockstart (snd (insert_string g (ls_strstart (d_ls s)) (d_ls s)))
                    = ls_blockstart (d_ls s))
      by (unfold insert_string; lsimp; reflexivity).
    assert (Emali : ls_matchavail (snd (insert_string g (ls_strstart (d_ls s)) (d_ls s)))
                    = ls_matchavail (d_ls s))
      by (unfold insert_string; lsimp; reflexivity).
    assert (Einsli : ls_insert (snd (insert_string g (ls_strstart (d_ls s)) (d_ls s)))
                     = ls_insert (d_ls s))
      by (unfold insert_string; lsimp; reflexivity).
    assert (Ewsli : ls_windowsize (snd (insert_string g (ls_strstart (d_ls s)) (d_ls s)))
                    = ls_windowsize (d_ls s))
      by (unfold insert_string; lsimp; reflexivity).
    assert (Eplli : ls_prevlen (snd (insert_string g (ls_strstart (d_ls s)) (d_ls s)))
                    = ls_prevlen (d_ls s))
      by (unfold insert_string; lsimp; reflexivity).
    (* the chain after the insert *)
    assert (Hchain2 : ChainInv g (ls_window (d_ls s))
              (ls_prev (snd (insert_string g (ls_strstart (d_ls s)) (d_ls s))))
              (ls_head (snd (insert_string g (ls_strstart (d_ls s)) (d_ls s))))
              (ls_strstart (d_ls s)) (ls_lookahead (d_ls s))
              (fun p => Ins p \/ p = ls_strstart (d_ls s))).
    { rewrite Ehd, Epr.
      destruct (Z.eq_dec (ls_strstart (d_ls s)) 0) as [E0|Hpos].
      - rewrite E0 in *.
        apply (insert_inv_zero g wbits hbits); try assumption.
      - assert (Hfresh : forall h, 0 <= h < dg_hash_size g ->
                  ls_head (d_ls s) h < ls_strstart (d_ls s)).
        { intros h Hh.
          destruct (ci_head_ins _ _ _ _ _ _ _ Hcinv h Hh) as [E|[HIh _]];
            [rewrite E; unfold NIL; lia | exact (Hchi _ HIh)]. }
        assert (Hflrlt : flr g (ls_strstart (d_ls s)) < ls_strstart (d_ls s)).
        { unfold flr.
          pose proof (go_ws_lo _ (g2_geom _ _ _ Hg)).
          destruct (Z.max_spec 0 (ls_strstart (d_ls s) - dg_w_size g))
            as [[Hm ->]|[Hm ->]]; lia. }
        unfold hh.
        replace (ls_strstart (d_ls s) + MIN_MATCH - 1)
          with (ls_strstart (d_ls s) + 2) by (unfold MIN_MATCH; lia).
        eapply (insert_inv g wbits hbits);
          first [ exact Hcinv | exact Hfresh | exact Hflrlt
                | exact (g2_wb0 _ _ _ Hg) | exact (g2_hb0 _ _ _ Hg)
                | exact (g2_ws _ _ _ Hg) | exact (g2_wm _ _ _ Hg)
                | exact (g2_hs _ _ _ Hg) | exact (g2_hm _ _ _ Hg)
                | exact (go_maxd _ (g2_geom _ _ _ Hg))
                | (rewrite <- Ehh; unfold hh;
                   replace (ls_strstart (d_ls s) + 2)
                     with (ls_strstart (d_ls s) + MIN_MATCH - 1)
                     by (unfold MIN_MATCH; lia);
                   reflexivity)
                | (unfold MIN_MATCH in Hla3; lia)
                | lia ]. }
    exists (fun p => Ins p \/ p = ls_strstart (d_ls s)).
    lsimp.
    rewrite Ehead.
    destruct (negb (Z.eqb (ls_head (d_ls s) hh) NIL)
              && (Z.leb (ls_strstart
                           (snd (insert_string g (ls_strstart (d_ls s))
                                   (d_ls s))) - ls_head (d_ls s) hh)
                        (dg_max_dist g))) eqn:Hguard.
    + (* the call *)
      apply andb_true_iff in Hguard as [Hg1 Hg3].
      apply negb_true_iff in Hg1. apply Z.eqb_neq in Hg1.
      apply Z.leb_le in Hg3.
      rewrite Ess in Hg3.
      unfold NIL in Hg1.
      assert (Hcand : Ins (ls_head (d_ls s) hh)
                      /\ 0 <= ls_head (d_ls s) hh
                      /\ ls_head (d_ls s) hh < ls_strstart (d_ls s)).
      { destruct (ci_head_ins _ _ _ _ _ _ _ Hcinv hh Hhh) as [E|[HIh Hle]];
          [unfold NIL in E; congruence|].
        split; [exact HIh|].
        split; [exact (ci_ins_lo _ _ _ _ _ _ _ Hcinv _ HIh)|].
        exact (Hchi _ HIh). }
      destruct Hcand as (HIhh & Hh0 & Hhlt).
      assert (Hflrlt : flr g (ls_strstart (d_ls s)) < ls_strstart (d_ls s)).
      { unfold flr.
        pose proof (go_ws_lo _ (g2_geom _ _ _ Hg)).
        destruct (Z.max_spec 0 (ls_strstart (d_ls s) - dg_w_size g))
          as [[Hm ->]|[Hm ->]]; lia. }
      (* name the l0 the call receives *)
      set (l0i := snd (insert_string g (ls_strstart (d_ls s)) (d_ls s))) in *.
      assert (El0w : ls_window l0i = ls_window (d_ls s))
        by (unfold l0i; exact Ewin).
      assert (El0ss : ls_strstart l0i = ls_strstart (d_ls s))
        by (unfold l0i; exact Ess).
      assert (El0la : ls_lookahead l0i = ls_lookahead (d_ls s))
        by (unfold l0i; exact Ela).
      assert (El0pl : ls_prevlen l0i = ls_prevlen (d_ls s))
        by (unfold l0i; exact Eplli).
      assert (HR : Reach g (ls_prev l0i) (ls_head l0i)
                     (flr g (ls_strstart (d_ls s))) hh
                     (ls_head (d_ls s) hh)).
      { assert (Hh2 : ls_head l0i hh = ls_strstart (d_ls s)).
        { rewrite Ehd, zset_same. apply u16_id.
          unfold MIN_MATCH in Hla3. lia. }
        assert (Hp2 : ls_prev l0i (idx g (ls_strstart (d_ls s)))
                      = ls_head (d_ls s) hh).
        { rewrite Epr. unfold idx. rewrite zset_same.
          exact Ehead. }
        assert (Hflr_cand : flr g (ls_strstart (d_ls s))
                            < ls_head (d_ls s) hh).
        { unfold flr.
          pose proof (go_maxd _ (g2_geom _ _ _ Hg)).
          pose proof (go_ws_lo _ (g2_geom _ _ _ Hg)).
          destruct (Z.max_spec 0 (ls_strstart (d_ls s) - dg_w_size g))
            as [[Hm ->]|[Hm ->]]; lia. }
        rewrite <- Hp2.
        apply reachS.
        - assert (R0 : Reach g (ls_prev l0i) (ls_head l0i)
                         (flr g (ls_strstart (d_ls s))) hh
                         (ls_head l0i hh)).
          { apply reach0. rewrite Hh2. exact Hflrlt. }
          rewrite Hh2 in R0. exact R0.
        - rewrite Hp2. exact Hflr_cand. }
      assert (Hchain1 : ChainInv g (ls_window l0i) (ls_prev l0i)
                (ls_head l0i) (ls_strstart (d_ls s)) (ls_lookahead (d_ls s))
                (fun p => Ins p \/ p = ls_strstart (d_ls s)))
        by (rewrite El0w; exact Hchain2).
      assert (Hbytes1 : forall i,
                 0 <= i < ls_strstart (d_ls s) + ls_lookahead (d_ls s) ->
                 0 <= ls_window l0i i < 256).
      { intros i Hi. rewrite El0w.
        exact (wininv_bytes g slid (d_ls s) (d_strm s) HW i Hi). }
      destruct (longest_match_out g wbits hbits l0i (ls_head (d_ls s) hh)
                  (ls_prev l0i) (ls_head l0i)
                  (ls_strstart (d_ls s)) (ls_lookahead (d_ls s))
                  (fun p => Ins p \/ p = ls_strstart (d_ls s)) hh
                  Hg Hchain1 Hbytes1 eq_refl El0ss El0la Hla3
                  ltac:(rewrite El0w; symmetry; exact Ehh)
                  Hhh HR Hhlt Hg3)
        as (Hfstle & Hout).
      set (r := longest_match g l0i (ls_head (d_ls s) hh)) in *.
      lsimp.
      repeat apply conj;
        try congruence;
        try (unfold l0i; congruence).
      all: first
        [ (rewrite El0w, El0ss, El0la; exact Hchain2)
        | (intros p [Hp|Hp]; [pose proof (Hchi _ Hp); lia | lia])
        | (intros _; unfold l0i; rewrite Einsh; exact Ehh)
        | (rewrite El0pl; exact Hpl2)
        | (destruct Hout as [[E1 _]|[_ Hmm]];
           [ right; left;
             rewrite E1, El0pl, Hpl2;
             destruct (Z.leb_spec 2 (ls_lookahead (d_ls s)));
             unfold MIN_MATCH in *; lia
           | right; right; exact Hmm ])
        | (destruct Hout as [[E1 _]|[HV _]];
           [ rewrite E1, ?El0pl;
             destruct (Z.leb_spec (ls_prevlen (d_ls s))
                         (ls_lookahead (d_ls s)));
             rewrite ?El0pl in *;
             unfold MIN_MATCH, MAX_MATCH in *; lia
           | destruct HV as (Hr & _);
             unfold MIN_MATCH, MAX_MATCH in *; lia ])
        | (intros H3le;
           destruct Hout as [[E1 _]|[HV Hmm]];
           [ exfalso;
             rewrite E1, El0pl in H3le;
             destruct (Z.leb_spec (ls_prevlen (d_ls s))
                         (ls_lookahead (d_ls s)));
             unfold MIN_MATCH in *; lia
           | rewrite El0w in HV;
             destruct (validfound_done g wbits hbits slid (d_ls s) (d_strm s)
                         (fst r) (snd r) Hg HW Hfstle HV)
               as (Hms0 & Hd & Hag);
             split; [exact Hfstle|];
             split; [exact Hms0|];
             split; [exact Hd|];
             exact Hag ]) ].
    + (* guard fails: l1 = post-insert state *)
      lsimp.
      repeat apply conj;
        try (unfold NIL; congruence).
      all: first
        [ (rewrite Ewin, Ess, Ela; exact Hchain2)
        | (intros p [Hp|Hp]; [pose proof (Hchi _ Hp); lia | lia])
        | (intros _; rewrite Einsh; exact Ehh)
        | (rewrite Eplli; exact Hpl2)
        | (left; exact Emlli)
        | (rewrite Emlli; unfold MAX_MATCH in *; lia)
        | (rewrite Emlli; intros H3le;
           destruct (Hcand0 H3le) as (Hma1 & _);
           congruence) ].
  - (* no insert: ph = (NIL, l); the guard is dead *)
    exists Ins.
    lsimp.
    replace (negb (Z.eqb NIL NIL)) with false by reflexivity.
    cbn [andb].
    repeat apply conj; try reflexivity; try congruence.
    all: first
      [ exact Hcinv
      | (intros p Hp; pose proof (Hchi p Hp); lia)
      | (intros Habs; unfold MIN_MATCH in *; lia)
      | exact Hpl2
      | (left; reflexivity)
      | (unfold MAX_MATCH in *; lia)
      | (intros H3le;
         destruct (Hcand0 H3le) as (Hma1 & _);
         congruence) ].
Qed.

Print Assumptions df_body_shape.
Print Assumptions df_top_facts.
Print Assumptions bsfloor_steppres.
