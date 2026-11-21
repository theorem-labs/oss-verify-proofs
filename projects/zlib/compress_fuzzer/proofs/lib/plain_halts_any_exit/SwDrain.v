(** * SwDrain — the slow-path walk, part W4a: a fill that ends short of
      [MIN_LOOKAHEAD] has drained the input.

    OWNER: q5-emitter (zlib z-repro campaign, 2026-08-19).  G4/W4.

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT.

    WHY THIS IS TRUE (and where the fuel argument hides): [fw_loop] exits
    on (a) [fw_step]'s early flag — which fires exactly on empty input —
    or (b) the C loop condition [lookahead < MIN_LOOKAHEAD && avail_in]
    going false.  Both exits with a short lookahead force [zs_in = []].
    The only other way out is fuel exhaustion, and that cannot happen:
    whenever [lookahead < MIN_LOOKAHEAD], the window has strictly positive
    room ([more > 0] — no-slide leaves [strstart < w_size + max_dist], a
    slide frees a whole [w_size]), so every continuing iteration reads at
    least one byte and [|zs_in| + 2] outlasts the loop. *)

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

Local Ltac lsimp :=
  cbn [ls_window ls_prev ls_head ls_insh ls_blockstart ls_matchlen
       ls_prevmatch ls_matchavail ls_strstart ls_matchstart ls_lookahead
       ls_prevlen ls_insert ls_highwater ls_windowsize
       setL_window setL_prev setL_head setL_insh setL_blockstart
       setL_matchlen setL_prevmatch setL_matchavail setL_strstart
       setL_matchstart setL_lookahead setL_prevlen setL_insert
       setL_highwater setL_windowsize
       d_cfg d_status d_lastflush d_wrap d_ts d_ls d_strm
       setD_cfg setD_status setD_lastflush setD_wrap setD_ts setD_ls
       setD_strm
       fst snd].

Lemma zlen_nil : forall (l : list Z), zlen l = 0 -> l = [].
Proof.
  intros [|x r] H; [reflexivity|].
  unfold zlen in H. cbn [length] in H. lia.
Qed.

Lemma zlen_nonneg : forall (l : list Z), 0 <= zlen l.
Proof. intros l. unfold zlen. lia. Qed.

Lemma zlen_skipn_le : forall n (l : list Z),
  zlen (skipn n l) = Z.max 0 (zlen l - Z.of_nat n).
Proof. intros n l. unfold zlen. rewrite length_skipn. lia. Qed.

(** The room is strictly positive whenever the lookahead is short. *)
Lemma fwp_pre_more_pos : forall g l st slid,
  GeomOk g -> WinInv g slid l st ->
  ls_lookahead l < MIN_LOOKAHEAD ->
  0 < snd (fwp_pre g l).
Proof.
  intros g l st slid Hg HW Hshort.
  pose proof (wi_ss _ _ _ _ HW) as Hss.
  pose proof (wi_la _ _ _ _ HW) as Hla.
  pose proof (wi_room _ _ _ _ HW) as Hroom.
  pose proof (wi_wsize _ _ _ _ HW) as Hwsz.
  pose proof (go_ws_lo _ Hg) as Hws262.
  pose proof (go_ws_hi _ Hg) as Hws32.
  pose proof (go_maxd _ Hg) as Hmd.
  unfold fwp_pre. cbv zeta.
  assert (Hm0 : u32 (ls_windowsize l - ls_lookahead l - ls_strstart l)
                = ls_windowsize l - ls_lookahead l - ls_strstart l).
  { unfold u32. apply Z.mod_small. lia. }
  unfold MIN_LOOKAHEAD in Hshort.
  destruct (Z.leb_spec (dg_w_size g + dg_max_dist g) (ls_strstart l))
    as [Hsl|Hsl]; lsimp; rewrite Hm0; lia.
Qed.

(** One [fw_loop]: a short-lookahead exit means the input is gone. *)
Lemma fw_loop_drain : forall fuel g wrap l st slid l' st',
  GeomOk g -> WinInv g slid l st -> CkInv wrap st ->
  ls_lookahead l < MIN_LOOKAHEAD ->
  zlen (zs_in st) < Z.of_nat fuel ->
  fw_loop fuel g wrap l st = (l', st') ->
  ls_lookahead l' < MIN_LOOKAHEAD ->
  zs_in st' = [].
Proof.
  induction fuel as [|f IH];
    intros g wrap l st slid l' st' Hg HW HK Hshort Hfuel Erun Hshort'.
  - pose proof (zlen_nonneg (zs_in st)). cbn [Z.of_nat] in Hfuel. lia.
  - cbn [fw_loop] in Erun.
    destruct (fw_step_pres g wrap l st slid Hg HW HK) as (slid1 & HP1 & HK1).
    rewrite fw_step_shape in Erun, HP1, HK1.
    destruct (Z.eqb_spec (zlen (zs_in st)) 0) as [Ein|Ein];
      cbn [fst snd] in Erun, HP1, HK1.
    + (* empty input: the early flag *)
      injection Erun as <- <-.
      apply zlen_nil. exact Ein.
    + (* a real read *)
      pose proof (fwp_pre_more_pos g l st slid Hg HW Hshort) as Hmore.
      destruct (read_buf_spec wrap (snd (fwp_pre g l)) st ltac:(lia))
        as (Edat & Ein' & Edn' & Eti' & Eout' & Eavo' & Etot').
      set (st1 := snd (read_buf wrap (snd (fwp_pre g l)) st)) in *.
      set (l1 := fw_seed g (fwp_blit
                   (fst (read_buf wrap (snd (fwp_pre g l)) st))
                   (fst (fwp_pre g l)))) in *.
      assert (Hin1 : zlen (zs_in st1) < zlen (zs_in st)).
      { rewrite Ein'.
        pose proof (zlen_nonneg (zs_in st)).
        destruct (Z.min_spec (snd (fwp_pre g l)) (zlen (zs_in st)))
          as [[Hm Em]|[Hm Em]];
          rewrite Em, zlen_skipn_le, Z2Nat.id by lia;
          rewrite Z.max_r by lia; lia. }
      destruct ((Z.ltb (ls_lookahead l1) MIN_LOOKAHEAD)
                && negb (Z.eqb (zlen (zs_in st1)) 0)) eqn:Eguard.
      * (* recurse *)
        apply andb_true_iff in Eguard.
        destruct Eguard as [Eg1 _]. apply Z.ltb_lt in Eg1.
        exact (IH g wrap l1 st1 slid1 l' st' Hg
                 (sp_inv _ _ _ _ _ _ _ HP1) HK1 Eg1
                 ltac:(lia) Erun Hshort').
      * (* exit by the loop condition *)
        injection Erun as <- <-.
        apply andb_false_iff in Eguard.
        destruct Eguard as [Eg|Eg].
        -- apply Z.ltb_ge in Eg. lia.
        -- apply negb_false_iff in Eg. apply Z.eqb_eq in Eg.
           apply zlen_nil. exact Eg.
Qed.

(** [fill_window]: same statement, through the highwater wrapper. *)
Lemma fw_highwater_la : forall l,
  ls_lookahead (fw_highwater l) = ls_lookahead l.
Proof.
  intros l. unfold fw_highwater. cbv zeta.
  repeat (destruct (Z.ltb _ _)); lsimp; reflexivity.
Qed.

Lemma fill_window_drain : forall g wrap l st slid,
  GeomOk g -> WinInv g slid l st -> CkInv wrap st ->
  ls_lookahead l < MIN_LOOKAHEAD ->
  ls_lookahead (fst (fill_window g wrap l st)) < MIN_LOOKAHEAD ->
  zs_in (snd (fill_window g wrap l st)) = [].
Proof.
  intros g wrap l st slid Hg HW HK Hshort Hshort'.
  unfold fill_window in *. cbv zeta in *.
  destruct (fw_loop (Z.to_nat (zlen (zs_in st)) + 2) g wrap l st)
    as [lf stf] eqn:Erun.
  cbn [fst snd] in *.
  rewrite fw_highwater_la in Hshort'.
  apply (fw_loop_drain (Z.to_nat (zlen (zs_in st)) + 2) g wrap l st slid
           lf stf Hg HW HK Hshort
           ltac:(pose proof (zlen_nonneg (zs_in st));
                 rewrite Nat2Z.inj_add, Z2Nat.id by lia;
                 cbn [Z.of_nat]; lia)
           Erun Hshort').
Qed.

(** At the [ds_fill] level, phrased on [DsInv]. *)
Lemma ds_fill_drain : forall g wbits hbits wrap slid Ins toks s,
  GeomOk2 g wbits hbits ->
  DsInv g wrap slid Ins toks s ->
  ls_lookahead (d_ls (ds_fill s)) < MIN_LOOKAHEAD ->
  zs_in (d_strm (ds_fill s)) = [].
Proof.
  intros g wbits hbits wrap slid Ins toks s Hg HI Hshort'.
  pose proof (di_win _ _ _ _ _ _ HI) as HW.
  pose proof (di_ck _ _ _ _ _ _ HI) as HK.
  pose proof (di_cfg _ _ _ _ _ _ HI) as Ecfg.
  pose proof (di_wrap _ _ _ _ _ _ HI) as Ewrap.
  destruct (ds_need s) eqn:Eneed.
  - unfold ds_fill in *. rewrite Eneed in *.
    unfold fill_if in *. cbv zeta in *.
    cbn [d_ls d_strm setD_ls setD_strm fst snd] in Hshort' |- *.
    rewrite Ecfg, Ewrap in *.
    unfold ds_need in Eneed. apply Z.ltb_lt in Eneed.
    apply (fill_window_drain g wrap (d_ls s) (d_strm s) slid
             (g2_geom _ _ _ Hg) HW HK Eneed Hshort').
  - unfold ds_fill in *. rewrite Eneed in *.
    unfold fill_if in *.
    unfold ds_need in Eneed. apply Z.ltb_ge in Eneed. lia.
Qed.

Print Assumptions ds_fill_drain.
