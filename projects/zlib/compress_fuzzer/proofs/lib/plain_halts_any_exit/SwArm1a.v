(** * SwArm1a — the slow-path walk, part W3g(i): the two engines of the
      match-tally arm — the LZ77 copy-is-the-input-slice lemma, and the
      [ds_insert] loop's chain walk.

    OWNER: q5-emitter (zlib z-repro campaign, 2026-08-19).  G4/W3.

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT.

    THE CHAIN ANCHOR (measured on the transcription): [ds_insert] bumps
    [strstart] while [lookahead] was already debited, so the ChainInv
    anchor that stays honest is [(ss_cur, S - ss_cur)] with
    [S := strstart + lookahead] of the dispatch state — constant physical
    region.  zlib's [max_insert = S - MIN_MATCH] guard IS [ci_ins_fill]'s
    bound at that anchor.

    THE SYNC DISJUNCT: a skipped insert leaves [ins_h] stale, but skips
    happen only past [max_insert], and then the post-arm lookahead is
    below [MIN_MATCH], so the next trip's sync guard is off.  [InsSync]
    carries exactly that disjunction. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk ZBitsOut BwStream Deflate Trees CresChain CbFold.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  SwWin SwFill SwTally SwChain SwLm SwInv SwEv SwArmPre SwArm2.
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

(** ** 1. The copied bytes are the next input slice *)

Lemma copy_n_slice_aux : forall m done d e n j,
  1 <= d -> d <= e -> 0 <= j ->
  j + Z.of_nat m = n ->
  e + n <= zlen done ->
  (forall k, 0 <= k < n ->
     nth (Z.to_nat (e - d + k)) done 0 = nth (Z.to_nat (e + k)) done 0) ->
  copy_n m d (firstn (Z.to_nat (e + j)) done)
  = firstn (Z.to_nat (e + n)) done.
Proof.
  induction m as [|m IH]; intros done d e n j Hd Hde Hj Hjn Hbound Hag.
  - cbn [copy_n]. do 2 f_equal. lia.
  - cbn [copy_n].
    assert (Hlenf : zlen (firstn (Z.to_nat (e + j)) done) = e + j).
    { unfold zlen. rewrite length_firstn. unfold zlen in Hbound. lia. }
    rewrite Hlenf.
    assert (Hnthf : nth (Z.to_nat (e + j - d))
                        (firstn (Z.to_nat (e + j)) done) 0
                    = nth (Z.to_nat (e + j - d)) done 0).
    { apply nth_firstn_local. lia. }
    rewrite Hnthf.
    assert (Hbyte : nth (Z.to_nat (e + j - d)) done 0
                    = nth (Z.to_nat (e + j)) done 0).
    { replace (e + j - d) with (e - d + j) by lia.
      apply (Hag j). lia. }
    rewrite Hbyte.
    assert (Hsnoc : firstn (Z.to_nat (e + j)) done
                      ++ [nth (Z.to_nat (e + j)) done 0]
                    = firstn (S (Z.to_nat (e + j))) done).
    { symmetry. apply firstn_snoc_nth. unfold zlen in Hbound. lia. }
    rewrite Hsnoc.
    replace (S (Z.to_nat (e + j))) with (Z.to_nat (e + (j + 1))) by lia.
    apply (IH done d e n (j + 1)); try lia; assumption.
Qed.

Lemma copy_n_slice : forall done d e n,
  1 <= d -> d <= e -> 0 <= n ->
  e + n <= zlen done ->
  (forall k, 0 <= k < n ->
     nth (Z.to_nat (e - d + k)) done 0 = nth (Z.to_nat (e + k)) done 0) ->
  copy_n (Z.to_nat n) d (firstn (Z.to_nat e) done)
  = firstn (Z.to_nat (e + n)) done.
Proof.
  intros done d e n Hd Hde Hn Hb Hag.
  replace (Z.to_nat e) with (Z.to_nat (e + 0)) by (f_equal; lia).
  apply (copy_n_slice_aux (Z.to_nat n) done d e n 0); try lia; assumption.
Qed.

(** ** 2. The [ds_insert] loop *)

Definition InsSync (g : DeflGeom) (S : Z) (l : LSt) : Prop :=
  ls_insh l = h3 g (ls_window l) (ls_strstart l)
  \/ S - MIN_MATCH < ls_strstart l.

(** One trip of the loop body: advance, then insert if within the fill. *)
Lemma ds_insert_step : forall g wbits hbits S Ins l,
  GeomOk2 g wbits hbits ->
  ChainInv g (ls_window l) (ls_prev l) (ls_head l)
           (ls_strstart l) (S - ls_strstart l) Ins ->
  (forall p, Ins p -> p <= ls_strstart l) ->
  InsSync g S l ->
  0 <= ls_strstart l ->
  ls_strstart l + 1 <= S ->
  S <= 65538 ->
  let l1 := setL_strstart (ls_strstart l + 1) l in
  let l2 := if Z.leb (ls_strstart l1) (S - MIN_MATCH)
            then snd (insert_string g (ls_strstart l1) l1) else l1 in
  exists Ins',
    ChainInv g (ls_window l2) (ls_prev l2) (ls_head l2)
             (ls_strstart l2) (S - ls_strstart l2) Ins'
    /\ (forall p, Ins' p -> p <= ls_strstart l2)
    /\ InsSync g S l2
    /\ ls_window l2 = ls_window l
    /\ ls_blockstart l2 = ls_blockstart l
    /\ ls_matchavail l2 = ls_matchavail l
    /\ ls_matchlen l2 = ls_matchlen l
    /\ ls_matchstart l2 = ls_matchstart l
    /\ ls_lookahead l2 = ls_lookahead l
    /\ ls_windowsize l2 = ls_windowsize l
    /\ ls_insert l2 = ls_insert l
    /\ ls_prevlen l2 = ls_prevlen l
    /\ ls_prevmatch l2 = ls_prevmatch l
    /\ ls_strstart l2 = ls_strstart l + 1.
Proof.
  intros g wbits hbits S Ins l Hg HC Hhi Hsync Hss0 Hroom Hu16.
  cbv zeta.
  destruct (Z.leb_spec (ls_strstart (setL_strstart (ls_strstart l + 1) l))
              (S - MIN_MATCH)) as [Hin|Hskip]; lsimp.
  - (* insert at ss+1 *)
    cbn [ls_strstart setL_strstart] in Hin.
    destruct (insert_string_fields g (setL_strstart (ls_strstart l + 1) l)
                (ls_strstart l + 1))
      as (Ehead & Einsh & Ehd & Epr & Ewin & Ess & Ela).
    cbv zeta in Ehead, Einsh, Ehd, Epr, Ewin, Ess, Ela.
    cbn [ls_window setL_strstart] in Ewin.
    (* the sync is live: a skip would contradict [Hin] *)
    assert (Hs : ls_insh l = h3 g (ls_window l) (ls_strstart l)).
    { destruct Hsync as [Hs|Hpast]; [exact Hs|].
      unfold MIN_MATCH in *. lia. }
    assert (Hsync' : update_hash g (ls_insh l)
                       (ls_window l (ls_strstart l + 1 + 2))
                     = h3 g (ls_window l) (ls_strstart l + 1)).
    { rewrite Hs.
      replace (ls_strstart l + 1 + 2) with (ls_strstart l + 3) by lia.
      apply (h3_roll g wbits hbits _ _ Hg). }
    exists (fun p => Ins p \/ p = ls_strstart l + 1).
    assert (HIV : ChainInv g (ls_window l)
              (zset (ls_prev l) (idx g (ls_strstart l + 1)) (ls_head l
                 (update_hash g (ls_insh l)
                    (ls_window l (ls_strstart l + 1 + 2)))))
              (zset (ls_head l)
                 (update_hash g (ls_insh l)
                    (ls_window l (ls_strstart l + 1 + 2)))
                 (u16 (ls_strstart l + 1)))
              (ls_strstart l + 1) (S - (ls_strstart l + 1))
              (fun p => Ins p \/ p = ls_strstart l + 1)).
    { assert (Hflrlt : flr g (ls_strstart l + 1) < ls_strstart l + 1).
      { unfold flr.
        pose proof (go_ws_lo _ (g2_geom _ _ _ Hg)).
        destruct (Z.max_spec 0 (ls_strstart l + 1 - dg_w_size g))
          as [[Hm ->]|[Hm ->]]; lia. }
      eapply (advance_insert_inv g wbits hbits);
        first [ exact HC | exact Hflrlt | exact Hsync'
              | exact (g2_wb0 _ _ _ Hg) | exact (g2_hb0 _ _ _ Hg)
              | exact (g2_ws _ _ _ Hg) | exact (g2_wm _ _ _ Hg)
              | exact (g2_hs _ _ _ Hg) | exact (g2_hm _ _ _ Hg)
              | exact (go_maxd _ (g2_geom _ _ _ Hg))
              | (unfold MIN_MATCH in *; lia)
              | lia ]. }
    (* transport onto the record's projections *)
    rewrite Ehd, Epr, Ewin.
    lsimp.
    repeat apply conj; try reflexivity.
    + replace (ls_strstart l + 1 + MIN_MATCH - 1)
        with (ls_strstart l + 1 + 2) by (unfold MIN_MATCH; lia).
      rewrite Ess. cbn [ls_strstart setL_strstart].
      exact HIV.
    + rewrite Ess. cbn [ls_strstart setL_strstart].
      intros p [Hp|Hp]; [pose proof (Hhi _ Hp); lia | lia].
    + left.
      rewrite Einsh, Ewin, Ess. lsimp.
      replace (ls_strstart l + 1 + MIN_MATCH - 1)
        with (ls_strstart l + 1 + 2) by (unfold MIN_MATCH; lia).
      exact Hsync'.
  - (* skip: past max_insert *)
    exists Ins.
    repeat apply conj; try reflexivity; lsimp.
    + eapply (flr_advance g wbits hbits);
        first [ exact HC
              | exact (g2_wb0 _ _ _ Hg) | exact (g2_hb0 _ _ _ Hg)
              | exact (g2_ws _ _ _ Hg) | exact (g2_wm _ _ _ Hg)
              | exact (g2_hs _ _ _ Hg) | exact (g2_hm _ _ _ Hg)
              | exact (go_maxd _ (g2_geom _ _ _ Hg))
              | lia ].
    + intros p Hp. pose proof (Hhi _ Hp). lia.
    + unfold InsSync. lsimp.
      cbn [ls_strstart setL_strstart] in Hskip.
      right. lia.
Qed.

(** The whole loop: [prevlen] iterations, each advancing one. *)
Lemma ds_insert_walk : forall f g wbits hbits S Ins l,
  GeomOk2 g wbits hbits ->
  ChainInv g (ls_window l) (ls_prev l) (ls_head l)
           (ls_strstart l) (S - ls_strstart l) Ins ->
  (forall p, Ins p -> p <= ls_strstart l) ->
  InsSync g S l ->
  0 <= ls_strstart l ->
  1 <= ls_prevlen l ->
  ls_prevlen l < Z.of_nat f ->
  ls_strstart l + ls_prevlen l <= S ->
  S <= 65538 ->
  let r := ds_insert f g (S - MIN_MATCH) l in
  exists Ins',
    ChainInv g (ls_window r) (ls_prev r) (ls_head r)
             (ls_strstart r) (S - ls_strstart r) Ins'
    /\ (forall p, Ins' p -> p <= ls_strstart r)
    /\ InsSync g S r
    /\ ls_window r = ls_window l
    /\ ls_blockstart r = ls_blockstart l
    /\ ls_matchavail r = ls_matchavail l
    /\ ls_matchlen r = ls_matchlen l
    /\ ls_matchstart r = ls_matchstart l
    /\ ls_lookahead r = ls_lookahead l
    /\ ls_windowsize r = ls_windowsize l
    /\ ls_insert r = ls_insert l
    /\ ls_prevlen r = 0
    /\ ls_strstart r = ls_strstart l + ls_prevlen l.
Proof.
  induction f as [|f IH]; intros g wbits hbits S Ins l
    Hg HC Hhi Hsync Hss0 Hpl1 Hplf Hfit Hu16.
  - cbn [Z.of_nat] in Hplf. lia.
  - cbn [ds_insert]. cbv zeta.
    destruct (ds_insert_step g wbits hbits S Ins l Hg HC Hhi Hsync Hss0
                ltac:(lia) Hu16)
      as (Ins1 & HC1 & Hhi1 & Hsync1 & Ew1 & Ebs1 & Ema1 & Eml1 & Ems1
          & Ela1 & Ews1 & Eins1 & Epl1 & Epm1 & Ess1).
    cbv zeta in HC1, Hhi1, Hsync1, Ew1, Ebs1, Ema1, Eml1, Ems1, Ela1,
      Ews1, Eins1, Epl1, Epm1, Ess1.
    (* name the body's l2 and align with the step lemma *)
    match goal with
    | |- context [setL_prevlen (ls_prevlen ?L2 - 1) ?L2] =>
        set (l2 := L2) in *
    end.
    set (l3 := setL_prevlen (ls_prevlen l2 - 1) l2).
    assert (E3pl : ls_prevlen l3 = ls_prevlen l - 1)
      by (unfold l3; lsimp; lia).
    destruct (Z.eqb_spec (ls_prevlen l3) 0) as [E0|Hne].
    + (* last iteration *)
      exists Ins1.
      assert (Efin : ls_prevlen l = 1) by lia.
      repeat apply conj;
        try (unfold l3; lsimp; congruence);
        try (unfold l3; lsimp; lia).
      all: try (unfold l3; lsimp; exact HC1).
      all: try (unfold l3; lsimp; exact Hhi1).
      all: try (destruct Hsync1 as [Hs|Hp]; [left|right];
                unfold l3; lsimp; assumption).
    + (* recurse *)
      destruct (IH g wbits hbits S Ins1 l3 Hg
                  ltac:(unfold l3; lsimp; exact HC1)
                  ltac:(unfold l3; lsimp; exact Hhi1)
                  ltac:(destruct Hsync1 as [Hs|Hp]; [left|right];
                        unfold l3; lsimp; assumption)
                  ltac:(unfold l3; lsimp; lia)
                  ltac:(unfold l3; lsimp; lia)
                  ltac:(unfold l3; lsimp; lia)
                  ltac:(unfold l3; lsimp; lia)
                  Hu16)
        as (Ins2 & HC2 & Hhi2 & Hsync2 & Ew2 & Ebs2 & Ema2 & Eml2 & Ems2
            & Ela2 & Ews2 & Eins2 & Epl2 & Ess2).
      cbv zeta in HC2, Hhi2, Hsync2, Ew2, Ebs2, Ema2, Eml2, Ems2, Ela2,
        Ews2, Eins2, Epl2, Ess2.
      exists Ins2.
      repeat apply conj; try assumption;
        try (rewrite ?Ew2, ?Ebs2, ?Ema2, ?Eml2, ?Ems2, ?Ela2, ?Ews2,
               ?Eins2; unfold l3; lsimp; congruence).
      rewrite Ess2. unfold l3. lsimp. lia.
Qed.

Print Assumptions copy_n_slice.
Print Assumptions ds_insert_walk.
