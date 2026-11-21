(** * SwFill — the slow-path walk, part W1b: [fill_window] preserves the
      window/input correspondence and the checksum thread.

    OWNER: q5-emitter (zlib z-repro campaign, 2026-08-19).  G4/W1 of the Q5
    plan.  Consumes SwWin.v's records and [read_buf] contract; concludes
    [StepPres] for the whole [fill_window] call, which is the ONLY way the
    deflate loop touches the input stream.

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT.

    SHAPE.  [fw_step]'s body is re-stated as three named pieces
    ([fwp_slide], [fwp_blit], [fw_step_shape] — the [cb_step_split] pattern
    from CbFold.v) so each piece gets its own preservation lemma:
      * [fwp_slide]: the window slide.  Everything moves down by [w_size];
        the invariant's [slid] absorbs it, and every position field the C
        adjusts ([match_start]/[strstart]/[block_start]) is adjusted by
        exactly the amount the conservation equations say.
      * [read_buf] + [fwp_blit]: consumed bytes land at the end of the
        valid region, exactly where [zs_done] says they should.
      * [fw_seed]/[fw_insert]: hash bookkeeping only — a frame lemma.
      * [fw_highwater]: writes strictly ABOVE the valid region.  *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Checksum Chunk Deflate StoredRt.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  GtAdlerChunk GtCrcChunk SwWin.
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
       zs_in zs_done zs_out zs_availout zs_totalin zs_totalout zs_adler
       zs_datatype
       setZ_in setZ_done setZ_out setZ_availout setZ_totalin setZ_totalout
       setZ_adler setZ_datatype
       fst snd].

(** ** 1. Small byte plumbing *)

Lemma forall_map_u8 : forall l,
  Forall (fun b => 0 <= b < 256) (map u8 l).
Proof.
  induction l as [|x l IH]; cbn [map]; constructor; [|exact IH].
  unfold u8. apply Z.mod_pos_bound. lia.
Qed.

(** ** 2. The named pieces of [fw_step] *)

Definition fwp_slide (g : DeflGeom) (l : LSt) : LSt :=
  let wsize := dg_w_size g in
  let more0 := u32 (ls_windowsize l - ls_lookahead l - ls_strstart l) in
  let l1 := setL_window (win_move 0 wsize (wsize - more0) (ls_window l)) l in
  let l2 := setL_matchstart (ls_matchstart l1 - wsize) l1 in
  let l3 := setL_strstart (ls_strstart l2 - wsize) l2 in
  let l4 := setL_blockstart (ls_blockstart l3 - wsize) l3 in
  let l5 := if Z.ltb (ls_strstart l4) (ls_insert l4)
            then setL_insert (ls_strstart l4) l4 else l4 in
  slide_hash g l5.

Definition fwp_pre (g : DeflGeom) (l : LSt) : LSt * Z :=
  let wsize := dg_w_size g in
  let more0 := u32 (ls_windowsize l - ls_lookahead l - ls_strstart l) in
  if Z.leb (wsize + dg_max_dist g) (ls_strstart l)
  then (fwp_slide g l, more0 + wsize)
  else (l, more0).

Definition fwp_blit (dat : list Z) (l : LSt) : LSt :=
  let l6 := setL_window (win_blit dat (ls_strstart l + ls_lookahead l)
                                  (ls_window l)) l in
  setL_lookahead (ls_lookahead l6 + zlen dat) l6.

Lemma fw_step_shape : forall g wrap l st,
  fw_step g wrap l st
  = if Z.eqb (zlen (zs_in st)) 0
    then (true, fst (fwp_pre g l), st)
    else (false,
          fw_seed g (fwp_blit (fst (read_buf wrap (snd (fwp_pre g l)) st))
                              (fst (fwp_pre g l))),
          snd (read_buf wrap (snd (fwp_pre g l)) st)).
Proof.
  intros g wrap l st.
  unfold fw_step, fwp_pre, fwp_slide, fwp_blit. cbv zeta.
  destruct (Z.leb (dg_w_size g + dg_max_dist g) (ls_strstart l));
    destruct (Z.eqb (zlen (zs_in st)) 0); reflexivity.
Qed.

(** ** 3. Frame lemmas: the hash bookkeeping never touches the region *)

Definition lst_frame (l l' : LSt) : Prop :=
  ls_window l' = ls_window l
  /\ ls_strstart l' = ls_strstart l
  /\ ls_lookahead l' = ls_lookahead l
  /\ ls_blockstart l' = ls_blockstart l
  /\ ls_matchstart l' = ls_matchstart l
  /\ ls_matchlen l' = ls_matchlen l
  /\ ls_prevlen l' = ls_prevlen l
  /\ ls_prevmatch l' = ls_prevmatch l
  /\ ls_matchavail l' = ls_matchavail l
  /\ ls_windowsize l' = ls_windowsize l.

Lemma lst_frame_refl : forall l, lst_frame l l.
Proof. intros l. repeat split. Qed.

Lemma lst_frame_trans : forall l1 l2 l3,
  lst_frame l1 l2 -> lst_frame l2 l3 -> lst_frame l1 l3.
Proof.
  unfold lst_frame. intros l1 l2 l3 A B.
  destruct A as (?&?&?&?&?&?&?&?&?&?), B as (?&?&?&?&?&?&?&?&?&?).
  repeat split; congruence.
Qed.

Lemma fw_insert_frame : forall f g str l,
  lst_frame l (fw_insert f g str l).
Proof.
  induction f as [|f IH]; intros g str l; cbn [fw_insert].
  - apply lst_frame_refl.
  - destruct (Z.eqb (ls_insert l) 0); [apply lst_frame_refl|].
    cbv zeta.
    match goal with
    | |- context [if ?b then ?l4 else fw_insert _ _ _ ?l4] =>
        assert (Hf : lst_frame l l4)
          by (unfold lst_frame; lsimp; repeat split; reflexivity);
        destruct b; [exact Hf|]
    end.
    eapply lst_frame_trans; [| apply IH].
    assumption.
Qed.

Lemma fw_seed_frame : forall g l, lst_frame l (fw_seed g l).
Proof.
  intros g l. unfold fw_seed. cbv zeta.
  destruct (Z.leb MIN_MATCH (ls_lookahead l + ls_insert l));
    [|apply lst_frame_refl].
  eapply lst_frame_trans; [|apply fw_insert_frame].
  unfold lst_frame; lsimp; repeat split; reflexivity.
Qed.

(** A framed move is a [StepPres] no-op. *)
Lemma steppres_of_frame : forall g slid l l' st,
  lst_frame l l' -> WinInv g slid l st -> StepPres g slid slid l l' st st.
Proof.
  intros g slid l l' st Hf Hinv.
  destruct Hf as (Ew&Ess&Ela&Ebs&Ems&Eml&Epl&Epm&Ema&Ews).
  destruct Hinv as [Hss Hla Hroom Hwsz Hslid Hdone Hti Hby Hib Hwin].
  constructor; try lia; try congruence.
  - constructor; try lia; try congruence.
    intros i Hi. rewrite Ew. apply Hwin. lia.
  - exists []. now rewrite app_nil_r.
Qed.

(** ** 4. The slide *)

Lemma fwp_slide_pres : forall g l st slid,
  GeomOk g -> WinInv g slid l st ->
  dg_w_size g + dg_max_dist g <= ls_strstart l ->
  StepPres g slid (slid + dg_w_size g) l (fwp_slide g l) st st.
Proof.
  intros g l st slid Hg Hinv Hsl.
  pose proof (go_ws_lo _ Hg) as Hws262.
  pose proof (go_ws_hi _ Hg) as Hws32.
  pose proof (go_maxd _ Hg) as Hmd.
  pose proof (wi_ss _ _ _ _ Hinv) as Hss.
  pose proof (wi_la _ _ _ _ Hinv) as Hla.
  pose proof (wi_room _ _ _ _ Hinv) as Hroom.
  pose proof (wi_wsize _ _ _ _ Hinv) as Hwsz.
  pose proof (wi_slid _ _ _ _ Hinv) as Hslid.
  pose proof (wi_done _ _ _ _ Hinv) as Hdone.
  pose proof (wi_totin _ _ _ _ Hinv) as Hti.
  pose proof (wi_bytes _ _ _ _ Hinv) as Hby.
  pose proof (wi_inbytes _ _ _ _ Hinv) as Hib.
  assert (Hm0 : u32 (ls_windowsize l - ls_lookahead l - ls_strstart l)
                = ls_windowsize l - ls_lookahead l - ls_strstart l).
  { unfold u32. apply Z.mod_small. lia. }
  unfold fwp_slide. cbv zeta. rewrite Hm0.
  unfold slide_hash. cbv zeta.
  set (wsz := dg_w_size g) in *.
  assert (Hcnt : wsz - (ls_windowsize l - ls_lookahead l - ls_strstart l)
                 = ls_strstart l + ls_lookahead l - wsz) by lia.
  (* the insert clamp changes only [ls_insert]; both branches run the same
     script *)
  destruct (Z.ltb _ _); lsimp;
    (constructor; lsimp; try lia; try reflexivity;
     try (right; lia);
     try (exists []; now rewrite app_nil_r);
     constructor; lsimp; try lia; try assumption;
     intros i Hi;
     unfold win_move;
     rewrite Hcnt;
     destruct (Z.leb_spec 0 i) as [Hi0|Hi0]; [|lia];
     destruct (Z.ltb_spec i (0 + (ls_strstart l + ls_lookahead l - wsz)))
       as [Hi1|Hi1]; [|lia];
     cbn [andb];
     rewrite (wi_win _ _ _ _ Hinv (i - 0 + wsz)) by lia;
     f_equal; lia).
Qed.

(** ** 5. The read + blit *)

Lemma fwp_read_pres : forall g wrap l st slid more,
  WinInv g slid l st -> CkInv wrap st ->
  0 <= more ->
  ls_strstart l + ls_lookahead l + more <= ls_windowsize l ->
  StepPres g slid slid l
    (fwp_blit (fst (read_buf wrap more st)) l)
    st (snd (read_buf wrap more st))
  /\ CkInv wrap (snd (read_buf wrap more st)).
Proof.
  intros g wrap l st slid more Hinv Hck Hm Hfit.
  destruct (read_buf_spec wrap more st Hm)
    as (Hdat & Hin & Hdone & Htot & Hout & Havo & Htoto & Hdt).
  pose proof (read_buf_len wrap more st Hm) as Hlen.
  pose proof (wi_ss _ _ _ _ Hinv) as Hss.
  pose proof (wi_la _ _ _ _ Hinv) as Hla.
  pose proof (wi_room _ _ _ _ Hinv) as Hroom.
  pose proof (wi_wsize _ _ _ _ Hinv) as Hwsz.
  pose proof (wi_slid _ _ _ _ Hinv) as Hslid.
  pose proof (wi_done _ _ _ _ Hinv) as Hdn.
  pose proof (wi_totin _ _ _ _ Hinv) as Hti.
  pose proof (wi_bytes _ _ _ _ Hinv) as Hby.
  pose proof (wi_inbytes _ _ _ _ Hinv) as Hib.
  assert (Hdb : Forall (fun b => 0 <= b < 256) (fst (read_buf wrap more st)))
    by (rewrite Hdat; apply forall_map_u8).
  assert (Hdl : 0 <= zlen (fst (read_buf wrap more st)) <= more).
  { rewrite Hlen. unfold zlen in *. lia. }
  split; [|apply read_buf_ckinv; assumption].
  unfold fwp_blit. cbv zeta.
  constructor; lsimp; try lia; try assumption;
    try (left; reflexivity).
  - (* the invariant at the new state *)
    constructor; lsimp; try lia.
    + (* done length *) rewrite Hdone. unfold zlen in *.
      rewrite length_app. lia.
    + (* totalin *) rewrite Htot, Hdone. unfold zlen in *.
      rewrite length_app. lia.
    + (* done bytes *) rewrite Hdone. apply Forall_app. now split.
    + (* input bytes *) rewrite Hin. now apply forall_skipn.
    + (* the window read *)
      intros i Hi.
      unfold win_blit. cbv zeta.
      rewrite Hdone.
      destruct (Z.leb_spec (ls_strstart l + ls_lookahead l) i) as [Hge|Hlt].
      * (* the fresh bytes *)
        destruct (Z.ltb_spec i (ls_strstart l + ls_lookahead l
                                + zlen (fst (read_buf wrap more st))))
          as [Hi2|Hi2]; [|unfold zlen in *; lia].
        cbn [andb].
        unfold zlist.
        rewrite app_nth2 by (unfold zlen in *; lia).
        f_equal. unfold zlen in *. lia.
      * (* the old region *)
        cbn [andb].
        rewrite app_nth1 by (unfold zlen in *; lia).
        apply (wi_win _ _ _ _ Hinv). lia.
  - (* done extension *) exists (fst (read_buf wrap more st)). exact Hdone.
  - (* conservation *)
    rewrite Hdone, Hin, Hdat, <- app_assoc.
    f_equal.
    rewrite stored_map_u8_id by (apply forall_firstn; exact Hib).
    apply firstn_skipn.
Qed.

(** ** 6. One [fw_step] *)

Lemma fwp_pre_pres : forall g l st slid,
  GeomOk g -> WinInv g slid l st ->
  exists slid',
    StepPres g slid slid' l (fst (fwp_pre g l)) st st
    /\ ls_strstart (fst (fwp_pre g l)) + ls_lookahead (fst (fwp_pre g l))
         + snd (fwp_pre g l)
       = ls_windowsize (fst (fwp_pre g l))
    /\ 0 <= snd (fwp_pre g l).
Proof.
  intros g l st slid Hg Hinv.
  pose proof (wi_room _ _ _ _ Hinv) as Hroom.
  pose proof (wi_ss _ _ _ _ Hinv) as Hss.
  pose proof (wi_la _ _ _ _ Hinv) as Hla.
  pose proof (wi_wsize _ _ _ _ Hinv) as Hwsz.
  pose proof (go_ws_lo _ Hg) as Hws262.
  pose proof (go_ws_hi _ Hg) as Hws32.
  pose proof (go_maxd _ Hg) as Hmd.
  assert (Hm0 : u32 (ls_windowsize l - ls_lookahead l - ls_strstart l)
                = ls_windowsize l - ls_lookahead l - ls_strstart l).
  { unfold u32. apply Z.mod_small. lia. }
  unfold fwp_pre. cbv zeta. rewrite Hm0.
  destruct (Z.leb_spec (dg_w_size g + dg_max_dist g) (ls_strstart l))
    as [Hsl|Hsl]; cbn [fst snd].
  - exists (slid + dg_w_size g).
    pose proof (fwp_slide_pres g l st slid Hg Hinv Hsl) as HP.
    split; [exact HP|].
    pose proof (sp_ss _ _ _ _ _ _ _ HP) as Ess.
    pose proof (sp_lagrow _ _ _ _ _ _ _ HP) as Ela.
    pose proof (wi_wsize _ _ _ _ (sp_inv _ _ _ _ _ _ _ HP)) as Ewsz.
    pose proof (wi_la _ _ _ _ (sp_inv _ _ _ _ _ _ _ HP)) as Hla'.
    (* lookahead is UNCHANGED by the slide, but [sp_lagrow] only gives <=;
       read it off the invariant's done-length equation instead, which pins
       ss' + la' exactly. *)
    pose proof (wi_done _ _ _ _ (sp_inv _ _ _ _ _ _ _ HP)) as Edone'.
    pose proof (wi_done _ _ _ _ Hinv) as Edone.
    split; lia.
  - exists slid.
    split; [apply steppres_refl; exact Hinv|].
    split; lia.
Qed.

Lemma fw_step_pres : forall g wrap l st slid,
  GeomOk g -> WinInv g slid l st -> CkInv wrap st ->
  exists slid',
    StepPres g slid slid' l (snd (fst (fw_step g wrap l st)))
             st (snd (fw_step g wrap l st))
    /\ CkInv wrap (snd (fw_step g wrap l st)).
Proof.
  intros g wrap l st slid Hg Hinv Hck.
  rewrite fw_step_shape.
  destruct (fwp_pre_pres g l st slid Hg Hinv)
    as (slid1 & HP1 & Hfit & Hm0).
  destruct (Z.eqb (zlen (zs_in st)) 0); cbn [fst snd].
  - exists slid1. split; [exact HP1 | exact Hck].
  - pose proof (sp_inv _ _ _ _ _ _ _ HP1) as Hinv1.
    destruct (fwp_read_pres g wrap (fst (fwp_pre g l)) st slid1
                (snd (fwp_pre g l)) Hinv1 Hck Hm0 ltac:(lia))
      as [HP2 Hck2].
    exists slid1. split; [|exact Hck2].
    eapply steppres_trans; [exact HP1|].
    eapply steppres_trans; [exact HP2|].
    apply steppres_of_frame.
    + apply fw_seed_frame.
    + exact (sp_inv _ _ _ _ _ _ _ HP2).
Qed.

(** ** 7. The loop, the high-water bump, and [fill_window] itself *)

Lemma fw_loop_pres : forall f g wrap l st slid,
  GeomOk g -> WinInv g slid l st -> CkInv wrap st ->
  exists slid',
    StepPres g slid slid' l (fst (fw_loop f g wrap l st))
             st (snd (fw_loop f g wrap l st))
    /\ CkInv wrap (snd (fw_loop f g wrap l st)).
Proof.
  induction f as [|f IH]; intros g wrap l st slid Hg Hinv Hck.
  - cbn [fw_loop fst snd]. exists slid.
    split; [apply steppres_refl; exact Hinv | exact Hck].
  - cbn [fw_loop].
    destruct (fw_step_pres g wrap l st slid Hg Hinv Hck) as (slid1 & HP1 & Hck1).
    destruct (fw_step g wrap l st) as [[brk l1] st1] eqn:Estep.
    cbn [fst snd] in HP1, Hck1.
    destruct brk.
    + exists slid1. split; [exact HP1 | exact Hck1].
    + destruct ((Z.ltb (ls_lookahead l1) MIN_LOOKAHEAD)
                  && negb (Z.eqb (zlen (zs_in st1)) 0)).
      * destruct (IH g wrap l1 st1 slid1 Hg
                    (sp_inv _ _ _ _ _ _ _ HP1) Hck1)
          as (slid2 & HP2 & Hck2).
        exists slid2. split; [|exact Hck2].
        eapply steppres_trans; [exact HP1 | exact HP2].
      * exists slid1. split; [exact HP1 | exact Hck1].
Qed.

Lemma fw_highwater_pres : forall g l st slid,
  WinInv g slid l st ->
  StepPres g slid slid l (fw_highwater l) st st.
Proof.
  intros g l st slid Hinv.
  pose proof (wi_ss _ _ _ _ Hinv) as Hss.
  pose proof (wi_la _ _ _ _ Hinv) as Hla.
  unfold fw_highwater. cbv zeta.
  (* every arm writes the window only at or above [strstart + lookahead] *)
  destruct (Z.ltb (ls_highwater l) (ls_windowsize l)) eqn:H1;
    [|apply steppres_refl; exact Hinv].
  destruct (Z.ltb (ls_highwater l) (ls_strstart l + ls_lookahead l)) eqn:H2.
  - destruct Hinv as [Hss2 Hla2 Hroom Hwsz Hslid Hdone Hti Hby Hib Hwin].
    constructor; lsimp; try lia;
      try (exists []; now rewrite app_nil_r);
      try (now rewrite app_nil_r); try reflexivity;
      try (left; reflexivity).
    constructor; lsimp; try lia; try assumption.
    intros i Hi.
    unfold win_zero.
    replace ((ls_strstart l + ls_lookahead l <=? i) && _) with false
      by (symmetry; apply andb_false_iff; left; apply Z.leb_gt; lia).
    now apply Hwin.
  - destruct (Z.ltb (ls_highwater l)
                (ls_strstart l + ls_lookahead l + WIN_INIT)) eqn:H3;
      [|apply steppres_refl; exact Hinv].
    apply Z.ltb_ge in H2.
    destruct Hinv as [Hss2 Hla2 Hroom Hwsz Hslid Hdone Hti Hby Hib Hwin].
    constructor; lsimp; try lia;
      try (exists []; now rewrite app_nil_r);
      try (now rewrite app_nil_r); try reflexivity;
      try (left; reflexivity).
    constructor; lsimp; try lia; try assumption.
    intros i Hi.
    unfold win_zero.
    replace ((ls_highwater l <=? i) && _) with false
      by (symmetry; apply andb_false_iff; left; apply Z.leb_gt; lia).
    now apply Hwin.
Qed.

Theorem fill_window_pres : forall g wrap l st slid,
  GeomOk g -> WinInv g slid l st -> CkInv wrap st ->
  exists slid',
    StepPres g slid slid' l (fst (fill_window g wrap l st))
             st (snd (fill_window g wrap l st))
    /\ CkInv wrap (snd (fill_window g wrap l st)).
Proof.
  intros g wrap l st slid Hg Hinv Hck.
  unfold fill_window. cbv zeta. cbn [fst snd].
  destruct (fw_loop_pres (Z.to_nat (zlen (zs_in st)) + 2) g wrap l st slid
              Hg Hinv Hck) as (slid1 & HP1 & Hck1).
  exists slid1. split; [|exact Hck1].
  eapply steppres_trans; [exact HP1|].
  apply fw_highwater_pres.
  exact (sp_inv _ _ _ _ _ _ _ HP1).
Qed.

Print Assumptions fill_window_pres.
