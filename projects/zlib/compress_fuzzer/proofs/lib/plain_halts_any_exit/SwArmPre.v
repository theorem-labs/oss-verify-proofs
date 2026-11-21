(** * SwArmPre — the slow-path walk, part W3d: the top of one [ds_body]
      trip, from the INSERT_STRING to the three-way arm dispatch.

    OWNER: q5-emitter (zlib z-repro campaign, 2026-08-19).  G4/W3 of the Q5
    plan; lm-level findings in WALK-DESIGN.md.

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT.

    WHAT THIS FILE PROVES.  [ds_body]'s preamble (deflate.c:1932-1962)
    inserts [strstart] into the hash chain (when three bytes of lookahead
    exist), shuffles the previous trip's candidate into
    [prev_length]/[prev_match], and may call [longest_match] — with the
    strategy-0 filter applied to the result.  [dsb_top_facts]
    characterises the dispatch-point state:

      * the chain with [Ins2 = Ins + {strstart}] and the WEAK bound
        [p <= strstart] (the arms re-strictify after they advance);
      * [ins_h] freshly synced AT [strstart] when the insert ran;
      * the candidate-shuffle equations;
      * the new candidate: if [match_length >= MIN_MATCH] survives to a
        deferral arm then it is a VALID match stated on the consumed input
        (WALK-DESIGN finding 2: the garbage arm cannot reach a deferral,
        because its length is always <= prev_length).

    THE ss = 0 INSERT.  [insert_inv] wants [flr ss < ss], false at the
    first trip's [ss = 0]; inserting 0 writes [u16 0 = NIL], so the bucket
    looks empty and the invariant survives outright ([insert_inv_zero]).
    The [longest_match] call guard is then dead too ([hash_head = NIL]). *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk ZBitsOut BwStream Deflate Trees CresChain CbFold.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  SwWin SwFill SwTally SwChain SwLm SwInv SwEv.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

Local Ltac lsimp :=
  cbn [ls_window ls_prev ls_head ls_insh ls_blockstart ls_matchlen
       ls_prevmatch ls_matchavail ls_strstart ls_matchstart ls_lookahead
       ls_prevlen ls_insert ls_highwater ls_windowsize
       setL_window setL_prev setL_head setL_insh setL_blockstart
       setL_matchlen setL_prevmatch setL_matchavail setL_strstart
       setL_matchstart setL_lookahead setL_prevlen setL_insert
       setL_highwater setL_windowsize
       fst snd].

(** ** 1. The named pieces of [ds_body]'s preamble *)

Definition dsb_l1 (l0 : LSt) : LSt :=
  setL_matchlen (MIN_MATCH - 1)
    (setL_prevmatch (ls_matchstart l0) (setL_prevlen (ls_matchlen l0) l0)).

Definition dsb_ph (g : DeflGeom) (l : LSt) : Z * LSt :=
  if Z.leb MIN_MATCH (ls_lookahead l)
  then insert_string g (ls_strstart l) l
  else (NIL, l).

Definition dsb_l2 (g : DeflGeom) (hash_head : Z) (l1 : LSt) : LSt :=
  if negb (Z.eqb hash_head NIL)
     && (Z.ltb (ls_prevlen l1) (dg_max_lazy_match g))
     && (Z.leb (ls_strstart l1 - hash_head) (dg_max_dist g)) then
    let r := longest_match g l1 hash_head in
    let l1a := setL_matchstart (snd r) (setL_matchlen (fst r) l1) in
    if (Z.leb (ls_matchlen l1a) 5)
       && ((Z.eqb (dg_strategy g) Z_FILTERED)
           || ((Z.eqb (ls_matchlen l1a) MIN_MATCH)
               && (Z.ltb TOO_FAR (ls_strstart l1a - ls_matchstart l1a))))
    then setL_matchlen (MIN_MATCH - 1) l1a else l1a
  else l1.

(** [ds_body], refactored onto the named pieces — pure zeta. *)
Lemma ds_body_shape : forall flush p0,
  ds_body flush p0
  = (let g := d_cfg p0 in
     let ph := dsb_ph g (d_ls p0) in
     let l2 := dsb_l2 g (fst ph) (dsb_l1 (snd ph)) in
     let s2 := setD_ls l2 p0 in
     if (Z.leb MIN_MATCH (ls_prevlen l2))
        && (Z.leb (ls_matchlen l2) (ls_prevlen l2)) then
       let max_insert := ls_strstart l2 + ls_lookahead l2 - MIN_MATCH in
       let tt := tr_tally_dist (ls_strstart l2 - 1 - ls_prevmatch l2)
                               (ls_prevlen l2 - MIN_MATCH)
                               (dg_sym_end g) (d_ts s2) in
       let bflush := fst tt in
       let l3 := setL_prevlen (ls_prevlen l2 - 2)
                   (setL_lookahead (ls_lookahead l2 - (ls_prevlen l2 - 1)) l2) in
       let l4 := ds_insert (Z.to_nat (ls_prevlen l3) + 1) g max_insert l3 in
       let l5 := setL_strstart (ls_strstart l4 + 1)
                   (setL_matchlen (MIN_MATCH - 1) (setL_matchavail 0 l4)) in
       let s3 := setD_ls l5 (setD_ts (snd tt) s2) in
       if bflush then
         match flush_block 0 s3 with
         | (Some bs, s4) => DsRet bs s4
         | (None, s4) => DsCont s4
         end
       else DsCont s3
     else if negb (Z.eqb (ls_matchavail l2) 0) then
       let tt := tr_tally_lit (ls_window l2 (ls_strstart l2 - 1))
                              (dg_sym_end g) (d_ts s2) in
       let s3 := setD_ts (snd tt) s2 in
       let s4 := if fst tt then flush_block_only 0 s3 else s3 in
       let s5 := setD_ls (setL_lookahead (ls_lookahead (d_ls s4) - 1)
                           (setL_strstart (ls_strstart (d_ls s4) + 1) (d_ls s4))) s4 in
       if Z.eqb (zs_availout (d_strm s5)) 0 then DsRet NeedMore s5 else DsCont s5
     else
       DsCont (setD_ls (setL_lookahead (ls_lookahead l2 - 1)
                         (setL_strstart (ls_strstart l2 + 1)
                           (setL_matchavail 1 l2))) s2)).
Proof.
  intros flush p0.
  unfold ds_body, dsb_ph, dsb_l1, dsb_l2. cbv zeta.
  reflexivity.
Qed.

(** ** 2. Inserting position 0 writes NIL: the chain shrugs *)

Lemma insert_inv_zero : forall g wbits hbits w P Hd la Ins hh,
  GeomOk2 g wbits hbits ->
  0 <= hh < dg_hash_size g ->
  MIN_MATCH <= la ->
  ChainInv g w P Hd 0 la Ins ->
  ChainInv g w (zset P (idx g 0) (Hd hh)) (zset Hd hh (u16 0)) 0 la
           (fun p => Ins p \/ p = 0).
Proof.
  intros g wbits hbits w P Hd la Ins hh Hg Hhh Hla IV.
  assert (Hu16 : u16 0 = 0) by reflexivity.
  assert (Hflr0 : flr g 0 = 0).
  { unfold flr. rewrite Z.max_l; [reflexivity|].
    pose proof (go_ws_lo _ (g2_geom _ _ _ Hg)). lia. }
  unfold MIN_MATCH in Hla.
  constructor.
  - intros p [Hp|Hp]; [exact (ci_ins_lo _ _ _ _ _ _ _ IV p Hp) | lia].
  - intros p [Hp|Hp]; [exact (ci_ins_hi _ _ _ _ _ _ _ IV p Hp) | lia].
  - intros p [Hp|Hp]; [exact (ci_ins_fill _ _ _ _ _ _ _ IV p Hp) | lia].
  - intros h Hh.
    destruct (Z.eq_dec h hh) as [->|Hne].
    + rewrite zset_same, Hu16. left. reflexivity.
    + rewrite zset_other by congruence.
      destruct (ci_head_ins _ _ _ _ _ _ _ IV h Hh) as [E|[HIh Hle]];
        [now left | right; split; [now left | exact Hle]].
  - intros h Hh Hgt. exfalso.
    rewrite Hflr0 in Hgt.
    destruct (Z.eq_dec h hh) as [->|Hne].
    + rewrite zset_same, Hu16 in Hgt. lia.
    + rewrite zset_other in Hgt by congruence.
      destruct (ci_head_ins _ _ _ _ _ _ _ IV h Hh) as [E|[HIh Hle]];
        [rewrite E in Hgt; unfold NIL in Hgt; lia | lia].
  - intros p Hp Hlo Hhi. exfalso.
    rewrite Hflr0 in Hlo. lia.
  - intros p Hp.
    destruct (Z.eq_dec (idx g p) (idx g 0)) as [E|Hne].
    + rewrite E, zset_same.
      destruct (ci_head_ins _ _ _ _ _ _ _ IV hh Hhh) as [E2|[HIh Hle]];
        [rewrite E2; unfold NIL; lia | exact Hle].
    + rewrite zset_other by congruence.
      assert (HIp : Ins p).
      { destruct Hp as [Hp|Hp]; [exact Hp|]. subst p. contradiction. }
      exact (ci_prev_hi _ _ _ _ _ _ _ IV p HIp).
Qed.

(** ** 3. Byte reads, and translating a valid match onto the input *)

Lemma wininv_bytes : forall g slid l st,
  WinInv g slid l st ->
  forall i, 0 <= i < ls_strstart l + ls_lookahead l ->
  0 <= ls_window l i < 256.
Proof.
  intros g slid l st HW i Hi.
  rewrite (wi_win _ _ _ _ HW i Hi).
  pose proof (wi_bytes _ _ _ _ HW) as Hb.
  pose proof (wi_done _ _ _ _ HW) as Hdn.
  pose proof (wi_slid _ _ _ _ HW) as Hslid.
  assert (Hin : (Z.to_nat (slid + i) < length (zs_done st))%nat)
    by (unfold zlen in Hdn; lia).
  rewrite Forall_forall in Hb.
  apply Hb, nth_In. exact Hin.
Qed.

Lemma validfound_done : forall g wbits hbits slid l st len ms,
  GeomOk2 g wbits hbits ->
  WinInv g slid l st ->
  len <= ls_lookahead l ->
  ValidFound g (ls_window l) (ls_strstart l) (ls_lookahead l) len ms ->
  0 <= slid + ms
  /\ 1 <= ls_strstart l - ms <= dg_max_dist g
  /\ forall k, 0 <= k < len ->
       nth (Z.to_nat (slid + ms + k)) (zs_done st) 0
       = nth (Z.to_nat (slid + ls_strstart l + k)) (zs_done st) 0.
Proof.
  intros g wbits hbits slid l st len ms Hg HW Hlenla HV.
  destruct HV as (Hrange & Hms & Hd & Hag).
  pose proof (wi_slid _ _ _ _ HW) as Hslid.
  pose proof (wi_ss _ _ _ _ HW) as Hss.
  split; [lia|].
  split; [exact Hd|].
  intros k Hk.
  replace (slid + ms + k) with (slid + (ms + k)) by lia.
  replace (slid + ls_strstart l + k)
    with (slid + (ls_strstart l + k)) by lia.
  rewrite <- (wi_win _ _ _ _ HW (ms + k)) by lia.
  rewrite <- (wi_win _ _ _ _ HW (ls_strstart l + k)) by lia.
  apply Hag. exact Hk.
Qed.

(** ** 4. The dispatch-point facts *)

Theorem dsb_top_facts : forall g wbits hbits wrap slid Ins toks s,
  GeomOk2 g wbits hbits ->
  dg_strategy g = 0 ->
  DsInv g wrap slid Ins toks s ->
  exists Ins2,
    let l := d_ls s in
    let ph := dsb_ph g l in
    let l2 := dsb_l2 g (fst ph) (dsb_l1 (snd ph)) in
    ChainInv g (ls_window l2) (ls_prev l2) (ls_head l2)
             (ls_strstart l2) (ls_lookahead l2) Ins2
    /\ (forall p, Ins2 p -> p <= ls_strstart l)
    /\ ls_window l2 = ls_window l
    /\ ls_strstart l2 = ls_strstart l
    /\ ls_lookahead l2 = ls_lookahead l
    /\ ls_blockstart l2 = ls_blockstart l
    /\ ls_matchavail l2 = ls_matchavail l
    /\ ls_windowsize l2 = ls_windowsize l
    /\ ls_insert l2 = 0
    /\ ls_prevlen l2 = ls_matchlen l
    /\ ls_prevmatch l2 = ls_matchstart l
    /\ (MIN_MATCH <= ls_lookahead l ->
        ls_insh l2 = h3 g (ls_window l) (ls_strstart l))
    /\ 0 <= ls_matchlen l2 <= MAX_MATCH
    /\ (MIN_MATCH <= ls_matchlen l2 ->
        ls_matchlen l2 <= ls_lookahead l
        /\ (ls_matchlen l2 <= ls_prevlen l2
            \/ (0 <= slid + ls_matchstart l2
                /\ 1 <= ls_strstart l - ls_matchstart l2 <= dg_max_dist g
                /\ forall k, 0 <= k < ls_matchlen l2 ->
                     nth (Z.to_nat (slid + ls_matchstart l2 + k))
                         (zs_done (d_strm s)) 0
                     = nth (Z.to_nat (slid + ls_strstart l + k))
                           (zs_done (d_strm s)) 0)))
    /\ (ls_matchlen l2 = MIN_MATCH ->
        ls_strstart l2 - ls_matchstart l2 <= TOO_FAR).
Proof.
  intros g wbits hbits wrap slid Ins toks s Hg Hstrat HI.
  pose proof (di_win _ _ _ _ _ _ HI) as HW.
  pose proof (di_chain _ _ _ _ _ _ HI) as HC.
  pose proof (di_ml _ _ _ _ _ _ HI) as Hml.
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
    assert (Hss65536 : ls_strstart (d_ls s) < 65536)
      by (unfold MIN_MATCH in Hla3; lia).
    (* the small projection facts of the post-insert state, raw form *)
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
    unfold dsb_l2, dsb_l1. lsimp.
    rewrite Ehead, Ess, Emlli.
    destruct (negb (Z.eqb (ls_head (d_ls s) hh) NIL)
              && (Z.ltb (ls_matchlen (d_ls s)) (dg_max_lazy_match g))
              && (Z.leb (ls_strstart (d_ls s) - ls_head (d_ls s) hh)
                        (dg_max_dist g))) eqn:Hguard.
    + (* the call *)
      apply andb_true_iff in Hguard as [Hg12 Hg3].
      apply andb_true_iff in Hg12 as [Hg1 Hg2].
      apply negb_true_iff in Hg1. apply Z.eqb_neq in Hg1.
      apply Z.leb_le in Hg3.
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
      (* name the l1 the call receives — the goal's exact tower *)
      match goal with
      | |- context [longest_match g ?L (ls_head (d_ls s) hh)] =>
          set (l1 := L) in *
      end.
      assert (El1w : ls_window l1 = ls_window (d_ls s))
        by (unfold l1; lsimp; exact Ewin).
      assert (El1p : ls_prev l1
                     = ls_prev (snd (insert_string g (ls_strstart (d_ls s))
                                       (d_ls s))))
        by (unfold l1; lsimp; reflexivity).
      assert (El1h : ls_head l1
                     = ls_head (snd (insert_string g (ls_strstart (d_ls s))
                                       (d_ls s))))
        by (unfold l1; lsimp; reflexivity).
      assert (El1ss : ls_strstart l1 = ls_strstart (d_ls s))
        by (unfold l1; lsimp; exact Ess).
      assert (El1la : ls_lookahead l1 = ls_lookahead (d_ls s))
        by (unfold l1; lsimp; exact Ela).
      assert (El1pl : ls_prevlen l1 = ls_matchlen (d_ls s))
        by (unfold l1; lsimp; exact Emlli).
      assert (HR : Reach g
                     (ls_prev (snd (insert_string g (ls_strstart (d_ls s))
                                      (d_ls s))))
                     (ls_head (snd (insert_string g (ls_strstart (d_ls s))
                                      (d_ls s))))
                     (flr g (ls_strstart (d_ls s))) hh
                     (ls_head (d_ls s) hh)).
      { assert (Hh2 : ls_head (snd (insert_string g (ls_strstart (d_ls s))
                                      (d_ls s))) hh
                      = ls_strstart (d_ls s)).
        { rewrite Ehd, zset_same. apply u16_id. lia. }
        assert (Hp2 : ls_prev (snd (insert_string g (ls_strstart (d_ls s))
                                      (d_ls s)))
                        (idx g (ls_strstart (d_ls s)))
                      = ls_head (d_ls s) hh).
        { rewrite Epr. unfold idx. rewrite zset_same. exact Ehead. }
        assert (Hflr_cand : flr g (ls_strstart (d_ls s))
                            < ls_head (d_ls s) hh).
        { unfold flr.
          pose proof (go_maxd _ (g2_geom _ _ _ Hg)).
          pose proof (go_ws_lo _ (g2_geom _ _ _ Hg)).
          destruct (Z.max_spec 0 (ls_strstart (d_ls s) - dg_w_size g))
            as [[Hm ->]|[Hm ->]]; lia. }
        rewrite <- Hp2.
        apply reachS.
        - assert (R0 : Reach g
              (ls_prev (snd (insert_string g (ls_strstart (d_ls s)) (d_ls s))))
              (ls_head (snd (insert_string g (ls_strstart (d_ls s)) (d_ls s))))
              (flr g (ls_strstart (d_ls s))) hh
              (ls_head (snd (insert_string g (ls_strstart (d_ls s)) (d_ls s)))
                 hh)).
          { apply reach0. rewrite Hh2. exact Hflrlt. }
          rewrite Hh2 in R0. exact R0.
        - rewrite Hp2. exact Hflr_cand. }
      assert (Hchain1 : ChainInv g (ls_window l1)
                (ls_prev (snd (insert_string g (ls_strstart (d_ls s)) (d_ls s))))
                (ls_head (snd (insert_string g (ls_strstart (d_ls s)) (d_ls s))))
                (ls_strstart (d_ls s)) (ls_lookahead (d_ls s))
                (fun p => Ins p \/ p = ls_strstart (d_ls s)))
        by (rewrite El1w; exact Hchain2).
      assert (Hbytes1 : forall i,
                 0 <= i < ls_strstart (d_ls s) + ls_lookahead (d_ls s) ->
                 0 <= ls_window l1 i < 256).
      { intros i Hi. rewrite El1w.
        exact (wininv_bytes g slid (d_ls s) (d_strm s) HW i Hi). }
      destruct (longest_match_out g wbits hbits l1 (ls_head (d_ls s) hh)
                  (ls_prev (snd (insert_string g (ls_strstart (d_ls s)) (d_ls s))))
                  (ls_head (snd (insert_string g (ls_strstart (d_ls s)) (d_ls s))))
                  (ls_strstart (d_ls s)) (ls_lookahead (d_ls s))
                  (fun p => Ins p \/ p = ls_strstart (d_ls s)) hh
                  Hg Hchain1 Hbytes1 El1p El1ss El1la Hla3
                  ltac:(rewrite El1w; symmetry; exact Ehh)
                  Hhh HR Hhlt Hg3)
        as (Hfstle & Hout).
      set (r := longest_match g l1 (ls_head (d_ls s) hh)) in *.
      destruct ((Z.leb (fst r) 5)
                && ((Z.eqb (dg_strategy g) Z_FILTERED)
                    || ((Z.eqb (fst r) MIN_MATCH)
                        && (Z.ltb TOO_FAR
                             (ls_strstart (d_ls s) - snd r))))) eqn:Hfilt;
        lsimp.
      * (* demoted to MIN_MATCH-1: the deferral clause is vacuous;
           congruence closes the chain, the projections and the insh sync *)
        repeat apply conj;
          try (unfold l1; lsimp; congruence).
        all: try (intros p [Hp|Hp]; [pose proof (Hchi _ Hp); lia | lia]).
        all: try (intros Habs; exfalso; unfold MIN_MATCH in Habs; lia).
        all: unfold MIN_MATCH, MAX_MATCH; lia.
      * (* kept: matchlen := fst r; congruence closes chain/projections/insh *)
        repeat apply conj;
          try (unfold l1; lsimp; congruence).
        all: try (intros p [Hp|Hp]; [pose proof (Hchi _ Hp); lia | lia]).
        all: try (destruct Hout as [[E1 _]|[HV Hmm]];
                  [ rewrite E1, El1pl;
                    destruct (Z.leb_spec (ls_matchlen (d_ls s))
                                (ls_lookahead (d_ls s)));
                    unfold MIN_MATCH, MAX_MATCH in *; lia
                  | destruct HV as (Hr & _);
                    unfold MIN_MATCH, MAX_MATCH in *; lia ]).
        (* the deferral clause is the one goal left *)
        intros H3le.
        split; [exact Hfstle|].
        destruct Hout as [[E1 E2]|[HV Hmm]].
        -- left.
           rewrite E1, El1pl.
           rewrite El1pl in E1.
           destruct (Z.leb_spec (ls_matchlen (d_ls s))
                       (ls_lookahead (d_ls s))); lia.
        -- right.
           destruct (validfound_done g wbits hbits slid (d_ls s)
                       (d_strm s) (fst r) (snd r) Hg HW Hfstle
                       ltac:(rewrite <- El1w, <- El1ss, <- El1la;
                             exact HV))
             as (Hc1 & Hc2 & Hc3).
           split; [exact Hc1|].
           split; [exact Hc2|].
           exact Hc3.
        (* the TOO_FAR residue: the filter kept a length-3 match only
           because it was near *)
        -- intros H3.
           revert H3. lsimp. intros H3.
           apply andb_false_iff in Hfilt.
           destruct Hfilt as [Hf5 | Hforb].
           ++ exfalso.
              rewrite H3 in Hf5.
              vm_compute in Hf5. discriminate Hf5.
           ++ apply orb_false_iff in Hforb.
              destruct Hforb as [_ Hfar].
              apply andb_false_iff in Hfar.
              destruct Hfar as [Hne | Hlt].
              ** exfalso.
                 rewrite H3 in Hne.
                 vm_compute in Hne. discriminate Hne.
              ** apply Z.ltb_ge in Hlt.
                 lia.
    + (* no call: match_length parked at MIN_MATCH-1 *)
      repeat apply conj;
        try (lsimp; congruence).
      all: try (intros p [Hp|Hp]; [pose proof (Hchi _ Hp); lia | lia]).
      all: lsimp.
      all: try (intros Habs; exfalso; unfold MIN_MATCH in Habs; lia).
      all: unfold MIN_MATCH, MAX_MATCH; lia.
  - (* no insert: nothing changes, no call either *)
    exists Ins.
    unfold dsb_l2, dsb_l1. lsimp.
    replace (negb (Z.eqb NIL NIL)) with false by reflexivity.
    cbn [andb].
    lsimp.
    repeat apply conj; try (lsimp; congruence); try reflexivity.
    all: try (intros p Hp; pose proof (Hchi _ Hp); lia).
    all: lsimp.
    all: try (intros Habs; exfalso; unfold MIN_MATCH in *; lia).
    all: unfold MIN_MATCH, MAX_MATCH; lia.
Qed.

Print Assumptions dsb_top_facts.

(* ==========================================================================
   EXPORT-WIDENING SUPPORT (an earlier development run M4-MODEL-2, 2026-09-07; q7 RULING
   F1b; TL f15 : SwArmPre passes to an earlier development run on filing,
   author q5-emitter).  The dispatch-point pieces of ONE [ds_body] trip, named
   at the model so that SwStep.ds_step_finish can identify a step's flush
   event's STATE with the trip files' site1_state / site2_state
   (DslowTripBody :672 / :688 — the same let-chains; DslowPInv's
   dsb_site1_state / dsb_site2_state prove the identity by reflexivity).
   ========================================================================== *)

Definition sw_body_l2 (p0 : DSt) : LSt :=
  let g := d_cfg p0 in
  let ph := dsb_ph g (d_ls p0) in
  dsb_l2 g (fst ph) (dsb_l1 (snd ph)).

Definition sw_body_s2 (p0 : DSt) : DSt := setD_ls (sw_body_l2 p0) p0.

Definition sw_site1_state (p0 : DSt) : DSt :=
  let g := d_cfg p0 in
  let l2 := sw_body_l2 p0 in
  let s2 := sw_body_s2 p0 in
  let max_insert := ls_strstart l2 + ls_lookahead l2 - MIN_MATCH in
  let tt := tr_tally_dist (ls_strstart l2 - 1 - ls_prevmatch l2)
                          (ls_prevlen l2 - MIN_MATCH)
                          (dg_sym_end g) (d_ts s2) in
  let l3 := setL_prevlen (ls_prevlen l2 - 2)
              (setL_lookahead (ls_lookahead l2 - (ls_prevlen l2 - 1)) l2) in
  let l4 := ds_insert (Z.to_nat (ls_prevlen l3) + 1) g max_insert l3 in
  let l5 := setL_strstart (ls_strstart l4 + 1)
              (setL_matchlen (MIN_MATCH - 1) (setL_matchavail 0 l4)) in
  setD_ls l5 (setD_ts (snd tt) s2).

Definition sw_site2_state (p0 : DSt) : DSt :=
  let g := d_cfg p0 in
  let l2 := sw_body_l2 p0 in
  let s2 := sw_body_s2 p0 in
  let tt := tr_tally_lit (ls_window l2 (ls_strstart l2 - 1))
                         (dg_sym_end g) (d_ts s2) in
  setD_ts (snd tt) s2.

Definition sw_arm1_taken (p0 : DSt) : bool :=
  (Z.leb MIN_MATCH (ls_prevlen (sw_body_l2 p0)))
    && (Z.leb (ls_matchlen (sw_body_l2 p0)) (ls_prevlen (sw_body_l2 p0))).

Definition sw_site1_bflush (p0 : DSt) : bool :=
  fst (tr_tally_dist
        (ls_strstart (sw_body_l2 p0) - 1 - ls_prevmatch (sw_body_l2 p0))
        (ls_prevlen (sw_body_l2 p0) - MIN_MATCH)
        (dg_sym_end (d_cfg p0)) (d_ts (sw_body_s2 p0))).

Definition sw_arm2_taken (p0 : DSt) : bool :=
  negb (Z.eqb (ls_matchavail (sw_body_l2 p0)) 0).

Definition sw_site2_bflush (p0 : DSt) : bool :=
  fst (tr_tally_lit
        (ls_window (sw_body_l2 p0) (ls_strstart (sw_body_l2 p0) - 1))
        (dg_sym_end (d_cfg p0)) (d_ts (sw_body_s2 p0))).

(** What ONE [ds_step] says about the STATES of its flush events, per arm:
    arm 1 flushes at [sw_site1_state] iff its tally flag is set, arm 2 at
    [sw_site2_state] iff its tally flag is set, arm 3 never. *)
Definition sw_step_sites (p0 : DSt) (evs : list FlushEv) : Prop :=
  (sw_arm1_taken p0 = true ->
     (sw_site1_bflush p0 = false /\ evs = [])
     \/ (sw_site1_bflush p0 = true
         /\ exists ev, evs = [ev] /\ fe_s ev = sw_site1_state p0))
  /\ (sw_arm1_taken p0 = false -> sw_arm2_taken p0 = true ->
     (sw_site2_bflush p0 = false /\ evs = [])
     \/ (sw_site2_bflush p0 = true
         /\ exists ev, evs = [ev] /\ fe_s ev = sw_site2_state p0))
  /\ (sw_arm1_taken p0 = false -> sw_arm2_taken p0 = false -> evs = []).

(** The closer for [ds_step_finish]'s new conjunct at each of its six leaves:
    reads the proof's own names ([sf], [l2], [Ecfg1], [Eg1], [Hma1] / [Eg2],
    the arm lemma's flags [Eflag] / [E1], its event identities [Efes] /
    [Efes2], or the undestructed arm-2 disjunction [Hdisj]). *)
Ltac sw_sites_close l2 Ecfg1 HI Hma1 Eg2 Hdisj :=
  lazymatch goal with
  | |- sw_step_sites ?sf0 ?evs0 =>
      let El2 := fresh "El2" in
      assert (El2 : sw_body_l2 sf0 = l2)
        by (unfold sw_body_l2; rewrite Ecfg1; rewrite (di_cfg _ _ _ _ _ _ HI); reflexivity);
      unfold sw_step_sites, sw_arm1_taken, sw_arm2_taken, sw_site1_bflush,
             sw_site2_bflush, sw_site1_state, sw_site2_state, sw_body_s2;
      rewrite El2; try rewrite Ecfg1; try rewrite (di_cfg _ _ _ _ _ _ HI); cbv zeta;
      repeat split; intros;
      first
        [ congruence
        | (rewrite Hma1 in *; discriminate)
        | (rewrite Eg2 in *; discriminate)
        | reflexivity
        | (left; split; [assumption | reflexivity])
        | (right; split; [assumption | eexists; split; [reflexivity | assumption]])
        | (destruct Hdisj as [(E1 & E2 & _)
                             | (ev & E1 & E2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Efes2 & _)];
           subst;
           [ left; split; [exact E1 | reflexivity]
           | right; split; [exact E1 | exists ev; split; [reflexivity | exact Efes2]] ]) ]
  end.
