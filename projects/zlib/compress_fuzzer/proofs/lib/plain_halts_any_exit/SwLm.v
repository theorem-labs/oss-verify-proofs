(** * SwLm — the slow-path walk, part W3b: what [longest_match] returns is
      either the caller's own previous candidate or a VALID match.

    OWNER: q5-emitter (zlib z-repro campaign, 2026-08-19).  G4/W3 of the Q5
    plan; design notes §"lm-level findings" in WALK-DESIGN.md.

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT.

    REACH, NOT LIVE (finding 1): the first candidate arrives under the
    caller's NON-strict guard [ss - cur <= MAX_DIST], which [Live]'s strict
    tail constructor does not cover at equality.  Everything the hit path
    needs is available at the [Reach (flr ss)] level ([reach_props] gives
    membership, floor-strictness, [<= ss] and h3-soundness), so this file
    packages byte-2 via [skip_scan2_ok] directly and never mentions [Live].

    THE OUTCOME SHAPE (finding 2): when no candidate beats [prev_length],
    the C returns [prev_length] with [match_start] garbage ([deflate.c:1341]
    says so in as many words).  So the theorem's conclusion is a
    disjunction: the no-hit arm pins the result to the ARGUMENTS (clamped
    best = [prev_length], start untouched), and only the hit arm claims
    validity.  The dispatch analysis in SwArms shows the garbage arm always
    flows into the tally-previous branch, never into a deferral. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk Deflate Trees CresChain.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import SwWin SwTally.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** ** 1. A valid found match, in window coordinates *)

Definition ValidFound (g : DeflGeom) (w : zarr) (ss la len ms : Z) : Prop :=
  MIN_MATCH <= len <= MAX_MATCH
  /\ 0 <= ms
  /\ 1 <= ss - ms <= dg_max_dist g
  /\ (forall k, 0 <= k < len -> w (ms + k) = w (ss + k)).

(** NOTE the deliberately ABSENT fit clause [ms + len <= ss + la]: the raw
    compare loop may match beyond the valid region (uninitialised bytes can
    agree), and the equality claim is still true of the raw window there.
    In-region-ness is recovered by the CLAMP (the returned length is
    [<= lookahead]), at the consumer. *)

(** ** 2. One hit is valid *)

Lemma lm_hit_valid : forall g wbits hbits c P Hd ss la Ins h st,
  GeomOk2 g wbits hbits ->
  ChainInv g (x_win c) P Hd ss la Ins ->
  (forall i, 0 <= i < ss + la -> 0 <= x_win c i < 256) ->
  x_scan c = ss ->
  MIN_MATCH <= la ->
  h3 g (x_win c) ss = h ->
  0 <= h < dg_hash_size g ->
  Reach g P Hd (flr g ss) h (m_cur st) ->
  m_cur st < ss ->
  ss - m_cur st <= dg_max_dist g ->
  lm_ok c st = true ->
  ValidFound g (x_win c) ss la (lm_len c st) (m_cur st).
Proof.
  intros g wbits hbits c P Hd ss la Ins h st
         Hg Hinv Hbytes Hsc Hla Hh3 Hh HR Hlt Hdist Hok.
  assert (HRP : Ins (m_cur st) /\ flr g ss < m_cur st /\ m_cur st <= ss
                /\ h3 g (x_win c) (m_cur st) = h).
  { eapply (reach_props g wbits hbits);
      first [ exact Hinv | exact HR
            | exact (g2_wb0 _ _ _ Hg) | exact (g2_hb0 _ _ _ Hg)
            | exact (g2_ws _ _ _ Hg) | exact (g2_wm _ _ _ Hg)
            | exact (g2_hs _ _ _ Hg) | exact (g2_hm _ _ _ Hg)
            | exact (go_maxd _ (g2_geom _ _ _ Hg)) | lia ]. }
  destruct HRP as (HIns & Hflr & Hle & Hh3p).
  assert (Hfill : m_cur st + 3 <= ss + la)
    by (exact (ci_ins_fill _ _ _ _ _ _ _ Hinv _ HIns)).
  assert (Hms0 : 0 <= m_cur st)
    by (exact (ci_ins_lo _ _ _ _ _ _ _ Hinv _ HIns)).
  unfold MIN_MATCH in Hla.
  (* the four byte checks of lm_ok, in named form (keep the original) *)
  pose proof Hok as Hok0.
  unfold lm_ok in Hok.
  apply andb_true_iff in Hok as [Hok3 Hb1].
  apply andb_true_iff in Hok3 as [_ Hb0].
  apply Z.eqb_eq in Hb0. apply Z.eqb_eq in Hb1.
  rewrite Hsc in Hb0, Hb1.
  (* byte 2 via the hash *)
  assert (Hb2 : x_win c (m_cur st + 2) = x_win c (ss + 2)).
  { eapply (skip_scan2_ok g wbits hbits);
      first [ exact (g2_hb8 _ _ _ Hg)
            | exact (g2_wb0 _ _ _ Hg) | exact (g2_hb0 _ _ _ Hg)
            | exact (g2_ws _ _ _ Hg) | exact (g2_wm _ _ _ Hg)
            | exact (g2_hs _ _ _ Hg) | exact (g2_hm _ _ _ Hg)
            | exact (go_maxd _ (g2_geom _ _ _ Hg))
            | exact Hb0 | exact Hb1
            | (rewrite Hh3p, <- Hh3; reflexivity)
            | (apply Hbytes; lia) ]. }
  (* the compare loop: agreement out to lm_len *)
  pose proof (lm_match_valid c st Hok0
                ltac:(rewrite Hsc; exact Hb2)) as Hagree.
  assert (Hlen : lm_len c st
                 = lm_cpl (Z.to_nat MAX_MATCH) (x_win c) (x_scan c)
                     (m_cur st) 3).
  { unfold lm_len. now rewrite Hok0. }
  assert (Hcple : lm_len c st <= MAX_MATCH).
  { rewrite Hlen. apply lm_cpl_le. unfold MAX_MATCH; lia. }
  assert (Hcplg : 3 <= lm_len c st).
  { rewrite Hlen. apply lm_cpl_ge. unfold MAX_MATCH; lia. }
  repeat split; try (unfold MIN_MATCH; lia).
  intros k Hk.
  symmetry.
  rewrite <- Hsc.
  apply (Hagree k Hk).
Qed.

(** ** 3. The loop invariant carries the outcome disjunction *)

Definition LmOut (g : DeflGeom) (w : zarr) (ss la bl0 ms0 : Z)
                 (st : LmSt) : Prop :=
  (m_best st = bl0 /\ m_start st = ms0)
  \/ ValidFound g w ss la (m_best st) (m_start st).

Lemma lm_loop_out : forall fuel g wbits hbits c P Hd ss la Ins h bl0 ms0 st,
  GeomOk2 g wbits hbits ->
  ChainInv g (x_win c) P Hd ss la Ins ->
  (forall i, 0 <= i < ss + la -> 0 <= x_win c i < 256) ->
  x_prev c = P -> x_scan c = ss ->
  x_wmask c = dg_w_mask g ->
  x_limit c = lim g ss ->
  MIN_MATCH <= la ->
  h3 g (x_win c) ss = h ->
  0 <= h < dg_hash_size g ->
  Reach g P Hd (flr g ss) h (m_cur st) ->
  m_cur st < ss ->
  ss - m_cur st <= dg_max_dist g ->
  LmOut g (x_win c) ss la bl0 ms0 st ->
  LmOut g (x_win c) ss la bl0 ms0 (lm_loop fuel c st).
Proof.
  induction fuel as [|fuel IH];
    intros g wbits hbits c P Hd ss la Ins h bl0 ms0 st
           Hg Hinv Hbytes Hxp Hxs Hxm Hxl Hla Hh3 Hh HR Hltss Hdist Hout;
    cbn [lm_loop]; [exact Hout|].
  (* one [lm_step]: the hit updates best/start validly; the walk to the
     next candidate preserves Reach (strictly decreasing). *)
  assert (Hout1 : LmOut g (x_win c) ss la bl0 ms0 (lm_next c st)).
  { unfold lm_next, lm_hit.
    destruct (lm_ok c st) eqn:Eok; cbn [andb];
      [|exact Hout].
    destruct (Z.ltb (m_best st) (lm_len c st)); [|exact Hout].
    right. cbn [m_best m_start].
    exact (lm_hit_valid g wbits hbits c P Hd ss la Ins h st Hg Hinv Hbytes
             Hxs Hla Hh3 Hh HR Hltss Hdist Eok). }
  assert (Hnextcur : m_cur (lm_next c st) = m_cur st).
  { unfold lm_next. destruct (lm_hit c st); reflexivity. }
  unfold lm_step. cbv zeta.
  destruct (lm_hit c st && Z.leb (x_nice c) (lm_len c st)).
  - exact Hout1.
  - (* step to prev[idx cur]; continue only above the limit *)
    destruct (Z.ltb_spec (x_limit c) (x_prev c (Z.land (m_cur st) (x_wmask c))))
      as [Hgt|Hng]; cbn [andb].
    + destruct (Z.eqb (m_chain (lm_next c st) - 1) 0) eqn:Ech; cbn [negb].
      * (* chain exhausted: done with the post-hit state *)
        destruct Hout1 as [A|B]; [left|right]; cbn [m_best m_start];
          assumption.
      * (* continue: the new cur is reached and strictly decreasing *)
        rewrite Hxp, Hxm in Hgt |- *.
        rewrite Hxl in Hgt.
        assert (Hfl : flr g ss <= lim g ss).
        { unfold flr, lim. apply Z.max_le_compat_l.
          pose proof (go_maxd _ (g2_geom _ _ _ Hg)).
          pose proof (go_ws_lo _ (g2_geom _ _ _ Hg)). lia. }
        assert (HR' : Reach g P Hd (flr g ss) h (P (idx g (m_cur st)))).
        { eapply reachS; [exact HR|]. unfold idx. lia. }
        assert (HRP : Ins (m_cur st) /\ flr g ss < m_cur st
                      /\ m_cur st <= ss /\ h3 g (x_win c) (m_cur st) = h).
        { eapply (reach_props g wbits hbits);
            first [ exact Hinv | exact HR
                  | exact (g2_wb0 _ _ _ Hg) | exact (g2_hb0 _ _ _ Hg)
                  | exact (g2_ws _ _ _ Hg) | exact (g2_wm _ _ _ Hg)
                  | exact (g2_hs _ _ _ Hg) | exact (g2_hm _ _ _ Hg)
                  | exact (go_maxd _ (g2_geom _ _ _ Hg)) | lia ]. }
        destruct HRP as (HIns & Hflr & Hle & _).
        assert (Hdec : P (idx g (m_cur st)) < m_cur st).
        { assert (Hflr2 : flr g ss < P (idx g (m_cur st)))
            by (unfold idx in *; lia).
          destruct (ci_prev _ _ _ _ _ _ _ Hinv (m_cur st) HIns Hflr Hle Hflr2)
            as (_ & Hdlt & _).
          exact Hdlt. }
        assert (Hlim : lim g ss <= dg_max_dist g \/ True) by (right; exact I).
        apply (IH g wbits hbits c P Hd ss la Ins h bl0 ms0 _
                 Hg Hinv Hbytes Hxp Hxs Hxm Hxl Hla Hh3 Hh);
          cbn [m_cur].
        -- exact HR'.
        -- unfold idx in Hdec. lia.
        -- (* above the limit means within MAX_DIST of strstart *)
           unfold lim in Hgt.
           pose proof (Z.le_max_l 0 (ss - dg_max_dist g)).
           pose proof (Z.le_max_r 0 (ss - dg_max_dist g)).
           lia.
        -- exact Hout1.
    + (* below the limit: done with the post-hit state *)
      destruct Hout1 as [A|B]; [left|right]; cbn [m_best m_start];
        assumption.
Qed.

(** ** 4. [longest_match] itself *)

Theorem longest_match_out : forall g wbits hbits l cm P Hd ss la Ins h,
  GeomOk2 g wbits hbits ->
  ChainInv g (ls_window l) P Hd ss la Ins ->
  (forall i, 0 <= i < ss + la -> 0 <= ls_window l i < 256) ->
  ls_prev l = P -> ls_strstart l = ss -> ls_lookahead l = la ->
  MIN_MATCH <= la ->
  h3 g (ls_window l) ss = h ->
  0 <= h < dg_hash_size g ->
  Reach g P Hd (flr g ss) h cm ->
  cm < ss ->
  ss - cm <= dg_max_dist g ->
  fst (longest_match g l cm) <= la
  /\ ( (fst (longest_match g l cm)
          = (if Z.leb (ls_prevlen l) la then ls_prevlen l else la)
        /\ snd (longest_match g l cm) = ls_matchstart l)
     \/ (ValidFound g (ls_window l) ss la
           (fst (longest_match g l cm)) (snd (longest_match g l cm))
         /\ MIN_MATCH <= fst (longest_match g l cm)) ).
Proof.
  intros g wbits hbits l cm P Hd ss la Ins h
         Hg Hinv Hbytes Hxp Hxs Hxla Hla Hh3 Hh HR Hltss Hdist.
  unfold longest_match. cbv zeta. cbn [fst snd].
  set (c := {| x_win := ls_window l; x_prev := ls_prev l;
               x_scan := ls_strstart l;
               x_nice := if Z.ltb (ls_lookahead l) (dg_nice_match g)
                         then ls_lookahead l else dg_nice_match g;
               x_limit := if Z.ltb (dg_max_dist g) (ls_strstart l)
                          then ls_strstart l - dg_max_dist g else NIL;
               x_wmask := dg_w_mask g |}).
  set (st0 := {| m_cur := cm; m_best := ls_prevlen l;
                 m_start := ls_matchstart l;
                 m_end1 := ls_window l (ls_strstart l + ls_prevlen l - 1);
                 m_end := ls_window l (ls_strstart l + ls_prevlen l);
                 m_chain := if Z.leb (dg_good_match g) (ls_prevlen l)
                            then Z.shiftr (dg_max_chain_length g) 2
                            else dg_max_chain_length g |}).
  assert (Hxl : x_limit c = lim g ss).
  { unfold c. cbn [x_limit]. rewrite Hxs. unfold lim, NIL.
    destruct (Z.ltb_spec (dg_max_dist g) ss) as [H1|H1].
    - rewrite Z.max_r by lia. reflexivity.
    - rewrite Z.max_l by lia. reflexivity. }
  pose proof (lm_loop_out (Z.to_nat (dg_max_chain_length g) + 2)
                g wbits hbits c P Hd ss la Ins h
                (ls_prevlen l) (ls_matchstart l) st0
                Hg Hinv Hbytes ltac:(unfold c; cbn [x_prev]; exact Hxp)
                ltac:(unfold c; cbn [x_scan]; exact Hxs)
                ltac:(unfold c; cbn [x_wmask]; reflexivity)
                Hxl Hla Hh3 Hh
                ltac:(unfold st0; cbn [m_cur]; exact HR)
                ltac:(unfold st0; cbn [m_cur]; exact Hltss)
                ltac:(unfold st0; cbn [m_cur]; exact Hdist)
                ltac:(left; unfold st0; cbn [m_best m_start];
                      split; reflexivity))
    as Hout.
  set (stf := lm_loop (Z.to_nat (dg_max_chain_length g) + 2) c st0) in *.
  rewrite Hxla.
  destruct Hout as [[Eb Es]|HV].
  - split.
    + destruct (Z.leb_spec (m_best stf) la); lia.
    + left. rewrite Eb, Es.
      destruct (Z.leb_spec (ls_prevlen l) la) as [H1|H1];
        destruct (Z.leb_spec (m_best stf) la) as [H2|H2];
        split; try reflexivity; lia.
  - destruct HV as (Hrange & Hms02 & Hdd & Hagree).
    split.
    + destruct (Z.leb_spec (m_best stf) la); lia.
    + right.
      destruct (Z.leb_spec (m_best stf) la) as [H2|H2].
      * split; [|unfold MIN_MATCH in *; lia].
        repeat split; try lia.
        intros k Hk. apply Hagree. lia.
      * (* clamped to the lookahead *)
        split; [|unfold MIN_MATCH in *; lia].
        repeat split; try lia.
        intros k Hk. apply Hagree. lia.
Qed.

Print Assumptions longest_match_out.
