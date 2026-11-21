(** * Bridge.DMatch.MFill2 — group M: pair D17b, one trip of [fill_window]'s loop.

    [m_s5_body_shape] / [m_rt_body_shape] cut each model's trip at the same
    seams: the slide ([s5_pre] / [rt_pre]), the no-input stop, the
    [read_buf] into the window, the lookahead bump and the re-seed.  The
    trip lemma [m_fw_body] relates the two trips under [dst_rel] and the
    RT-side loop invariant [fw_inv], and returns the progress facts the loop
    induction ([MFill3]) needs: a trip that does not stop reads at least one
    byte, so the lookahead grows and the unread input shrinks. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require DeflateState DeflateLz.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base Chunk ZBitsOut Trees Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelDefl S5Fields.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DEmit Require DEmitDefs.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DMatch Require Import DMatchDefs MBasic MLz MReadBuf MFill1.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Module SLz := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.

(* ------------------------------------------------------------------------- *)
(* 1.  The loop invariant (RT side)                                          *)
(* ------------------------------------------------------------------------- *)

(** What one trip needs and keeps, on RT's state.  [mt_inv] gives it
    ([m_fw_inv_of_mt]); with group R's [ms_fill] it gives [mt_inv] back. *)
Record fw_inv (t : RD.DSt) : Prop := mkFwInv {
  fi_cfg   : cfg_facts (RD.d_cfg t);
  fi_wrap  : RD.d_wrap t = 1;
  fi_rb    : rb_ok t;
  fi_ws    : RD.ls_windowsize (RD.d_ls t) = 65536;
  fi_ss    : 0 <= RD.ls_strstart (RD.d_ls t);
  fi_la    : 0 <= RD.ls_lookahead (RD.d_ls t);
  fi_room  : RD.ls_strstart (RD.d_ls t) + RD.ls_lookahead (RD.d_ls t) <= 65536;
  fi_ins   : 0 <= RD.ls_insert (RD.d_ls t) <= RD.ls_strstart (RD.d_ls t);
  fi_win   : forall i, 0 <= i < 65536 -> 0 <= RD.ls_window (RD.d_ls t) i < 256;
  fi_ma    : RD.ls_matchavail (RD.d_ls t) = 0
             \/ (RD.ls_matchavail (RD.d_ls t) = 1 /\ 1 <= RD.ls_strstart (RD.d_ls t));
  fi_bs    : RD.ls_blockstart (RD.d_ls t) <= RD.ls_strstart (RD.d_ls t);
  fi_hw    : 0 <= RD.ls_highwater (RD.d_ls t) <= 65536;
  fi_slid  : exists slid, 0 <= slid
             /\ Chunk.zlen (RD.zs_done (RD.d_strm t))
                = slid + RD.ls_strstart (RD.d_ls t) + RD.ls_lookahead (RD.d_ls t)
             /\ 0 <= slid + RD.ls_blockstart (RD.d_ls t)
             /\ 0 <= slid + RD.ls_matchstart (RD.d_ls t)
             /\ RD.ls_matchstart (RD.d_ls t) <= RD.ls_strstart (RD.d_ls t);
  fi_inlen : Chunk.zlen (RD.zs_done (RD.d_strm t)) + Chunk.zlen (RD.zs_in (RD.d_strm t)) < 2 ^ 32;
  fi_pend  : RC.MIN_MATCH <= RD.ls_matchlen (RD.d_ls t) -> 1 <= RD.ls_strstart (RD.d_ls t)
}.

Lemma m_fw_inv_of_mt : forall t, mt_inv t -> fw_inv t.
Proof.
  intros t H. pose proof (m_cfg_facts t H) as Hc.
  destruct H as [Hlev Hcfg Hwr Hrb Hms Hfa Hsl Hwin Hma Hml Hbs Hhw Hslid Hinl].
  destruct Hms as [Hch Hws Hmd Hwz Hstr Hlk Hrm Hins].
  rewrite (cf_w_size _ Hc) in Hwz.
  constructor; try assumption; lia.
Qed.

Lemma m_em_of_nonlz : forall s s',
  nonlz_view s' = nonlz_view s -> DEmitDefs.em_view s' = DEmitDefs.em_view s.
Proof.
  intros s s' Hv. destruct s, s'. unfold nonlz_view in Hv. cbn in Hv.
  injection Hv; intros; subst. reflexivity.
Qed.

(* ------------------------------------------------------------------------- *)
(* 2.  The trip, cut at the same seams in both models                        *)
(* ------------------------------------------------------------------------- *)

Definition s5_slide (s : DS.deflate_state) (wsize more : Z) : DS.deflate_state :=
  let s := DS.set_window s (arr_blit (DS.ds_window s) 0 (DS.ds_window s) wsize (wrap32 (wsize - more))) in
  let s := DS.set_match_start s (wrap32 (DS.ds_match_start s - wsize)) in
  let s := DS.set_strstart s (DS.ds_strstart s - wsize) in
  let s := DS.set_block_start s (DS.ds_block_start s - wsize) in
  let s := if Z.ltb (DS.ds_strstart s) (DS.ds_insert s) then DS.set_insert s (DS.ds_strstart s) else s in
  SLz.slide_hash s.

Definition s5_pre (s : DS.deflate_state) (wsize : Z) : DS.deflate_state * Z :=
  let more := wrap32 (DS.ds_window_size s - DS.ds_lookahead s - DS.ds_strstart s) in
  if Z.leb (wsize + (DS.ds_w_size s - DS.MIN_LOOKAHEAD)) (DS.ds_strstart s)
  then (s5_slide s wsize more, wrap32 (more + wsize)) else (s, more).

Lemma m_s5_body_shape : forall s wsize,
  SLz.fill_window_body s wsize
  = match s5_pre s wsize with
    | (s1, more) =>
        if Z.eqb (DS.cs_avail_in (DS.ds_strm s1)) 0 then (s1, true)
        else match SLz.read_buf s1 (SLz.RB_window (DS.ds_strstart s1 + DS.ds_lookahead s1)) more with
             | (s2, n) => (s5_seed (DS.set_lookahead s2 (DS.ds_lookahead s2 + n)), false)
             end
    end.
Proof. reflexivity. Qed.

Definition rt_slide (g : RC.DeflGeom) (l : RD.LSt) (more0 : Z) : RD.LSt :=
  let wsize := RC.dg_w_size g in
  let l1 := RD.setL_window (RD.win_move 0 wsize (wsize - more0) (RD.ls_window l)) l in
  let l2 := RD.setL_matchstart (RD.ls_matchstart l1 - wsize) l1 in
  let l3 := RD.setL_strstart (RD.ls_strstart l2 - wsize) l2 in
  let l4 := RD.setL_blockstart (RD.ls_blockstart l3 - wsize) l3 in
  let l5 := if Z.ltb (RD.ls_strstart l4) (RD.ls_insert l4)
            then RD.setL_insert (RD.ls_strstart l4) l4 else l4 in
  RD.slide_hash g l5.

Definition rt_pre (g : RC.DeflGeom) (l : RD.LSt) : RD.LSt * Z :=
  let wsize := RC.dg_w_size g in
  let more0 := Base.u32 (RD.ls_windowsize l - RD.ls_lookahead l - RD.ls_strstart l) in
  if Z.leb (wsize + RC.dg_max_dist g) (RD.ls_strstart l)
  then (rt_slide g l more0, more0 + wsize) else (l, more0).

Definition rt_blit (dat : list Z) (l : RD.LSt) : RD.LSt :=
  let l6 := RD.setL_window (RD.win_blit dat (RD.ls_strstart l + RD.ls_lookahead l) (RD.ls_window l)) l in
  RD.setL_lookahead (RD.ls_lookahead l6 + Chunk.zlen dat) l6.

Lemma m_rt_body_shape : forall g wrap l st,
  RD.fw_step g wrap l st
  = if Z.eqb (Chunk.zlen (RD.zs_in st)) 0 then (true, fst (rt_pre g l), st)
    else (false,
          RD.fw_seed g (rt_blit (fst (RD.read_buf wrap (snd (rt_pre g l)) st)) (fst (rt_pre g l))),
          snd (RD.read_buf wrap (snd (rt_pre g l)) st)).
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------------- *)
(* 3.  The slide                                                             *)
(* ------------------------------------------------------------------------- *)

Lemma m_wrap32_sub : forall a b, wrap32 (wrap32 a - b) = wrap32 (a - b).
Proof.
  intros a b. rewrite !wrap32_mod. rewrite Zminus_mod_idemp_l. reflexivity.
Qed.

(** The slide before [slide_hash], LZ half. *)
Lemma m_slide_pre_hash : forall s t more,
  lz_rel s t -> s5_geom s -> RD.ls_windowsize (RD.d_ls t) = 65536 ->
  0 <= more <= 262 ->
  let s1 := DS.set_window s (arr_blit (DS.ds_window s) 0 (DS.ds_window s) 32768 (wrap32 (32768 - more))) in
  let s2 := DS.set_match_start s1 (wrap32 (DS.ds_match_start s1 - 32768)) in
  let s3 := DS.set_strstart s2 (DS.ds_strstart s2 - 32768) in
  let s4 := DS.set_block_start s3 (DS.ds_block_start s3 - 32768) in
  let s5 := if Z.ltb (DS.ds_strstart s4) (DS.ds_insert s4) then DS.set_insert s4 (DS.ds_strstart s4) else s4 in
  let l := RD.d_ls t in
  let l1 := RD.setL_window (RD.win_move 0 32768 (32768 - more) (RD.ls_window l)) l in
  let l2 := RD.setL_matchstart (RD.ls_matchstart l1 - 32768) l1 in
  let l3 := RD.setL_strstart (RD.ls_strstart l2 - 32768) l2 in
  let l4 := RD.setL_blockstart (RD.ls_blockstart l3 - 32768) l3 in
  let l5 := if Z.ltb (RD.ls_strstart l4) (RD.ls_insert l4)
            then RD.setL_insert (RD.ls_strstart l4) l4 else l4 in
  lz_rel s5 (RD.setD_ls l5 t) /\ nonlz_view s5 = nonlz_view s.
Proof.
  intros s t more Hl Hg Hws Hmore s1 s2 s3 s4 s5 l l1 l2 l3 l4 l5.
  assert (Hl0 : lz_rel s (RD.setD_ls l t)) by exact Hl.
  pose proof (lzr_win _ _ Hl) as Hrw. pose proof (lzr_wlen _ _ Hl) as Hlw. rewrite Hws in Hrw, Hlw.
  assert (H1 : lz_rel s1 (RD.setD_ls l1 t)).
  { apply lz_set_window; [exact Hl0 | apply arr_len_blit |].
    unfold l. rewrite Hws.
    intros j Hj. rewrite arr_get_blit. unfold arr_inb, RD.win_move. rewrite Hlw.
    rewrite wrap32_id by (mpow; lia).
    destruct (Z.leb_spec 0 j); destruct (Z.ltb_spec j (0 + Z.max 0 (32768 - more)));
      destruct (Z.ltb_spec j 65536); destruct (Z.ltb_spec j (0 + (32768 - more))); cbn [andb]; try lia.
    - replace (j - 0 + 32768) with (32768 + (j - 0)) by lia. apply Hrw. lia.
    - apply Hrw. lia. }
  assert (H2 : lz_rel s2 (RD.setD_ls l2 t)).
  { apply lz_set_match_start; [exact H1|].
    subst s1. rewrite ds_match_start__set_window, (lzr_ms _ _ Hl).
    subst l1. cbn [RD.setL_window RD.ls_matchstart]. apply m_wrap32_sub. }
  assert (H3 : lz_rel s3 (RD.setD_ls l3 t)).
  { apply lz_set_strstart; [exact H2|].
    pose proof (lzr_ss _ _ H2) as E. cbn [RD.d_ls RD.setD_ls] in E. rewrite E. reflexivity. }
  assert (H4 : lz_rel s4 (RD.setD_ls l4 t)).
  { apply lz_set_block_start; [exact H3|].
    pose proof (lzr_bs _ _ H3) as E. cbn [RD.d_ls RD.setD_ls] in E. rewrite E. reflexivity. }
  pose proof (lzr_ss _ _ H4) as Hss4. pose proof (lzr_ins _ _ H4) as Hin4.
  cbn [RD.d_ls RD.setD_ls] in Hss4, Hin4.
  subst s5 l5. rewrite Hss4, Hin4.
  destruct (Z.ltb (RD.ls_strstart l4) (RD.ls_insert l4)).
  - split; [apply lz_set_insert; [exact H4 | reflexivity] | reflexivity].
  - split; [exact H4 | reflexivity].
Qed.
