(** * Bridge.DMatch.MFast1 — group M: what both block loops (D14, D15) share.

    - [rt_fb_frame], [rt_fbo_frame]: RT's flushes touch only the trees, the
      output side of the stream, and [block_start := strstart].
    - [m_fill_measure]: RT's [fill_window] moves bytes from the unread input
      to the lookahead, so [zlen zs_in + lookahead] is unchanged (the loop
      measure of both [deflate_fast] and [deflate_slow]).
    - [mt_inv_trip]: [mt_inv] after a trip, from group R's invariants and
      the window facts a trip keeps.
    - [s5_early] / [m_early]: the top-of-trip fill and its two early exits,
      identical in [deflate_fast_body] and [deflate_slow_body], against RT's
      [ds_need] / [ds_fill] tests in [df_step] and [ds_step]. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require DeflateState DeflateLz DeflateBlk.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base Chunk ZBitsOut Trees Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelDefl S5Fields.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DEmit Require Import DEmitDefs.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DMatch Require Import DMatchDefs MBasic MLz MReadBuf
  MFill1 MFill2 MFill3 MFill4.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Module SLz := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.
Module SBlk := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.DeflateBlk.

(* ------------------------------------------------------------------------- *)
(* 1.  RT's flushes                                                          *)
(* ------------------------------------------------------------------------- *)

Record rt_frame (t t' : RD.DSt) : Prop := mkRtFrame {
  rf_cfg  : RD.d_cfg t' = RD.d_cfg t;
  rf_wrap : RD.d_wrap t' = RD.d_wrap t;
  rf_in   : RD.zs_in (RD.d_strm t') = RD.zs_in (RD.d_strm t);
  rf_done : RD.zs_done (RD.d_strm t') = RD.zs_done (RD.d_strm t);
  rf_tin  : RD.zs_totalin (RD.d_strm t') = RD.zs_totalin (RD.d_strm t)
}.

Lemma rt_flush_pending_frame : forall s,
  rt_frame s (RD.flush_pending s) /\ RD.d_ls (RD.flush_pending s) = RD.d_ls s.
Proof.
  intros s. unfold RD.flush_pending. cbv zeta.
  destruct (Z.eqb _ 0); (split; [constructor|]); reflexivity.
Qed.

Lemma rt_fbo_frame : forall last s,
  rt_frame s (RD.flush_block_only last s)
  /\ RD.d_ls (RD.flush_block_only last s)
     = RD.setL_blockstart (RD.ls_strstart (RD.d_ls s)) (RD.d_ls s).
Proof.
  intros last s. unfold RD.flush_block_only. cbv zeta.
  match goal with |- context [RD.flush_pending ?x] => destruct (rt_flush_pending_frame x) as [[F1 F2 F3 F4 F5] F6] end.
  rewrite F6. cbn [RD.d_ls RD.setD_ls RD.setD_ts RD.setD_strm] in *.
  split; [constructor|reflexivity].
  - rewrite F1. reflexivity.
  - rewrite F2. reflexivity.
  - rewrite F3. reflexivity.
  - rewrite F4. reflexivity.
  - rewrite F5. reflexivity.
Qed.

Lemma rt_fb_frame : forall last s,
  rt_frame s (snd (RD.flush_block last s))
  /\ RD.d_ls (snd (RD.flush_block last s))
     = RD.setL_blockstart (RD.ls_strstart (RD.d_ls s)) (RD.d_ls s).
Proof.
  intros last s. unfold RD.flush_block. destruct (Z.eqb _ 0); apply rt_fbo_frame.
Qed.

(* ------------------------------------------------------------------------- *)
(* 2.  The loop measure across a fill                                        *)
(* ------------------------------------------------------------------------- *)

Lemma rt_fw_insert_la : forall f g str l, RD.ls_lookahead (RD.fw_insert f g str l) = RD.ls_lookahead l.
Proof.
  induction f as [|f IH]; intros g str l; cbn [RD.fw_insert]; [reflexivity|].
  destruct (Z.eqb (RD.ls_insert l) 0); [reflexivity|]. cbv zeta.
  match goal with |- context [if ?c then _ else _] => destruct c end; [rt_ls; reflexivity|].
  rewrite IH. rt_ls. reflexivity.
Qed.

Lemma rt_fw_seed_la : forall g l, RD.ls_lookahead (RD.fw_seed g l) = RD.ls_lookahead l.
Proof.
  intros g l. unfold RD.fw_seed. destruct (Z.leb _ _); [|reflexivity]. cbv zeta.
  rewrite rt_fw_insert_la. rt_ls. reflexivity.
Qed.

Lemma rt_fw_loop_measure : forall n g wrap l st,
  RC.dg_w_size g = 32768 ->
  Chunk.zlen (RD.zs_in (snd (RD.fw_loop n g wrap l st))) + RD.ls_lookahead (fst (RD.fw_loop n g wrap l st))
  = Chunk.zlen (RD.zs_in st) + RD.ls_lookahead l.
Proof.
  induction n as [|n IH]; intros g wrap l st Hw; [reflexivity|].
  cbn [RD.fw_loop]. rewrite m_rt_body_shape.
  assert (Hm : 0 <= snd (rt_pre g l)).
  { unfold rt_pre. cbv zeta. rewrite Hw.
    assert (0 <= Base.u32 (RD.ls_windowsize l - RD.ls_lookahead l - RD.ls_strstart l))
      by (unfold Base.u32; apply Z.mod_pos_bound; lia).
    destruct (Z.leb _ _); cbn [snd]; lia. }
  assert (Hla : RD.ls_lookahead (fst (rt_pre g l)) = RD.ls_lookahead l).
  { unfold rt_pre. cbv zeta. destruct (Z.leb _ _); cbn [fst]; [|reflexivity].
    unfold rt_slide, RD.slide_hash. cbv zeta.
    match goal with |- context [if ?c then _ else _] => destruct c end; rt_ls; reflexivity. }
  destruct (m_rt_rb_lens wrap (snd (rt_pre g l)) st Hm) as (K1 & K2 & _ & _).
  destruct (Z.eqb (Chunk.zlen (RD.zs_in st)) 0); cbn [fst snd]; [rewrite Hla; reflexivity|].
  set (st' := snd (RD.read_buf wrap (snd (rt_pre g l)) st)) in *.
  set (l' := RD.fw_seed g (rt_blit (fst (RD.read_buf wrap (snd (rt_pre g l)) st)) (fst (rt_pre g l)))).
  assert (Hl' : RD.ls_lookahead l' = RD.ls_lookahead l + Chunk.zlen (fst (RD.read_buf wrap (snd (rt_pre g l)) st))).
  { subst l'. rewrite rt_fw_seed_la. unfold rt_blit. rt_ls. rewrite Hla. reflexivity. }
  destruct (Z.ltb (RD.ls_lookahead l') RC.MIN_LOOKAHEAD && negb (Z.eqb (Chunk.zlen (RD.zs_in st')) 0));
    [rewrite IH by exact Hw|cbn [fst snd]]; lia.
Qed.

Lemma rt_hw_la : forall l, RD.ls_lookahead (RD.fw_highwater l) = RD.ls_lookahead l.
Proof.
  intros l. unfold RD.fw_highwater. cbv zeta.
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; rt_ls; reflexivity.
Qed.

Lemma m_fill_measure : forall t, RC.dg_w_size (RD.d_cfg t) = 32768 ->
  Chunk.zlen (RD.zs_in (RD.d_strm (RD.fill_if true t))) + RD.ls_lookahead (RD.d_ls (RD.fill_if true t))
  = Chunk.zlen (RD.zs_in (RD.d_strm t)) + RD.ls_lookahead (RD.d_ls t).
Proof.
  intros t Hw. unfold RD.fill_if, RD.fill_window. cbv zeta. cbn [RD.d_ls RD.d_strm RD.setD_ls RD.setD_strm fst snd].
  rewrite rt_hw_la. apply rt_fw_loop_measure. exact Hw.
Qed.

(* ------------------------------------------------------------------------- *)
(* 3.  mt_inv after a trip                                                   *)
(* ------------------------------------------------------------------------- *)

Lemma mt_inv_trip : forall p t',
  mt_inv p -> RK.ms_inv t' ->
  (RC.dg_level (RD.d_cfg t') <= 3 -> RK.ms_fast_inv t') ->
  (4 <= RC.dg_level (RD.d_cfg t') -> RK.ms_slow_inv t') ->
  rt_frame p t' ->
  RD.ls_window (RD.d_ls t') = RD.ls_window (RD.d_ls p) ->
  RD.ls_highwater (RD.d_ls t') = RD.ls_highwater (RD.d_ls p) ->
  (RD.ls_matchavail (RD.d_ls t') = 0
   \/ (RD.ls_matchavail (RD.d_ls t') = 1 /\ 1 <= RD.ls_strstart (RD.d_ls t'))) ->
  0 <= RD.ls_matchlen (RD.d_ls t') <= 258 -> 0 <= RD.ls_prevlen (RD.d_ls t') <= 258 ->
  RD.ls_strstart (RD.d_ls t') + RD.ls_lookahead (RD.d_ls t')
    = RD.ls_strstart (RD.d_ls p) + RD.ls_lookahead (RD.d_ls p) ->
  RD.ls_strstart (RD.d_ls p) <= RD.ls_strstart (RD.d_ls t') ->
  (RD.ls_blockstart (RD.d_ls t') = RD.ls_blockstart (RD.d_ls p)
   \/ RD.ls_strstart (RD.d_ls p) <= RD.ls_blockstart (RD.d_ls t') <= RD.ls_strstart (RD.d_ls t')) ->
  (RD.ls_matchstart (RD.d_ls t') = RD.ls_matchstart (RD.d_ls p)
   \/ 0 <= RD.ls_matchstart (RD.d_ls t') <= RD.ls_strstart (RD.d_ls t')) ->
  (RC.MIN_MATCH <= RD.ls_matchlen (RD.d_ls t') -> 1 <= RD.ls_strstart (RD.d_ls t')) ->
  mt_inv t'.
Proof.
  intros p t' Hp Hms Hfa Hsl [F1 F2 F3 F4 F5] Hwin Hhw Hma Hml Hpl Hsum Hss Hbs Hmst Hpend.
  pose proof (RK.mi_str _ Hms) as Hstr. pose proof (RK.mi_look _ Hms) as Hlk.
  pose proof (RK.mi_str _ (mt_ms p Hp)) as Hstr0.
  destruct Hp as [Hlev Hcfg Hwr Hrb Hms0 Hfa0 Hsl0 Hwin0 Hma0 Hml0 Hbs0 Hhw0 Hslid Hinl Hpend0].
  destruct Hslid as (slid & Z0 & Z1 & Z2 & Z3 & Z4).
  constructor.
  - rewrite F1; exact Hlev.
  - rewrite F1; exact Hcfg.
  - rewrite F2; exact Hwr.
  - unfold rb_ok in *; rewrite F2, F3, F5; exact Hrb.
  - exact Hms.
  - exact Hfa.
  - exact Hsl.
  - rewrite Hwin; exact Hwin0.
  - exact Hma.
  - split; assumption.
  - destruct Hbs as [E|E]; [rewrite E|]; lia.
  - rewrite Hhw; exact Hhw0.
  - exists slid. rewrite F4. destruct Hbs as [E|E]; destruct Hmst as [E'|E']; rewrite ?E, ?E'; lia.
  - rewrite F4, F3; exact Hinl.
  - exact Hpend.
Qed.

(* ------------------------------------------------------------------------- *)
(* 4.  The top-of-trip fill                                                  *)
(* ------------------------------------------------------------------------- *)

Definition s5_early (s : DS.deflate_state) (flush : Z) : DS.deflate_state * option SBlk.loop_out :=
  if Z.ltb (DS.ds_lookahead s) DS.MIN_LOOKAHEAD then
    let s := SLz.fill_window s in
    if Z.ltb (DS.ds_lookahead s) DS.MIN_LOOKAHEAD && Z.eqb flush Z_NO_FLUSH
    then (s, Some (SBlk.LRet SLz.need_more))
    else if Z.eqb (DS.ds_lookahead s) 0 then (s, Some SBlk.LBreak)
    else (s, None)
  else (s, None).

Theorem m_early : forall s t po pi flush,
  dst_rel s t po pi -> mt_inv t -> em_inv s ->
  let e := s5_early s flush in
  let p0 := RD.ds_fill t in
  dst_rel (fst e) p0 po pi /\ mt_inv p0 /\ em_inv (fst e)
  /\ RD.ls_strstart (RD.d_ls p0) + 262 <= 65536
  /\ Chunk.zlen (RD.zs_in (RD.d_strm p0)) + RD.ls_lookahead (RD.d_ls p0)
     = Chunk.zlen (RD.zs_in (RD.d_strm t)) + RD.ls_lookahead (RD.d_ls t)
  /\ match snd e with
     | Some (SBlk.LRet b) =>
         b = SLz.need_more /\ (RD.ds_need t && RD.ds_need p0 && Z.eqb flush 0) = true
     | Some SBlk.LBreak =>
         (RD.ds_need t && RD.ds_need p0 && Z.eqb flush 0) = false
         /\ (RD.ds_need t && Z.eqb (RD.ls_lookahead (RD.d_ls p0)) 0) = true
     | Some SBlk.LCont => False
     | None =>
         (RD.ds_need t && RD.ds_need p0 && Z.eqb flush 0) = false
         /\ (RD.ds_need t && Z.eqb (RD.ls_lookahead (RD.d_ls p0)) 0) = false
         /\ 1 <= RD.ls_lookahead (RD.d_ls p0)
     end.
Proof.
  intros s t po pi flush Hd Hm He e p0.
  pose proof (lzr_la _ _ (proj1 (proj1 (m_dst_split _ _ _ _) Hd))) as Ela.
  pose proof (m_cfg_facts t Hm) as Hc.
  subst e p0. unfold s5_early, RD.ds_fill, RD.ds_need.
  change DS.MIN_LOOKAHEAD with 262. change RC.MIN_LOOKAHEAD with 262. change Z_NO_FLUSH with 0.
  rewrite Ela.
  destruct (Z.ltb_spec (RD.ls_lookahead (RD.d_ls t)) 262) as [Lt|Ge]; cbn [andb fst snd].
  - destruct (m_fill_window s t po pi Hd Hm Lt) as (F1 & F2 & F3 & F4).
    pose proof (m_fill_measure t (cf_w_size _ Hc)) as Fm.
    pose proof (lzr_la _ _ (proj1 (proj1 (m_dst_split _ _ _ _) F1))) as Ela'.
    rewrite Ela'.
    assert (He' : em_inv (SLz.fill_window s)) by (exact (em_inv_frame s _ F4 He)).
    pose proof (fi_la _ (m_fw_inv_of_mt _ F2)) as Hla0.
    destruct (Z.ltb_spec (RD.ls_lookahead (RD.d_ls (RD.fill_if true t))) 262) as [Lt'|Ge'];
      destruct (Z.eqb_spec flush 0) as [Fz|Fz]; cbn [andb];
      [ | destruct (Z.eqb_spec (RD.ls_lookahead (RD.d_ls (RD.fill_if true t))) 0) as [L0|L0]
        | destruct (Z.eqb_spec (RD.ls_lookahead (RD.d_ls (RD.fill_if true t))) 0) as [L0|L0]
        | destruct (Z.eqb_spec (RD.ls_lookahead (RD.d_ls (RD.fill_if true t))) 0) as [L0|L0] ];
      cbn [fst snd andb];
      (split; [exact F1|]); (split; [exact F2|]); (split; [exact He'|]); (split; [exact F3|]);
      (split; [exact Fm|]);
      first [ split; reflexivity | split; [reflexivity|]; split; [reflexivity|]; lia | lia ].
  - change (RD.fill_if false t) with t. pose proof (m_fw_inv_of_mt t Hm) as Hf.
    split; [exact Hd|]. split; [exact Hm|]. split; [exact He|].
    split; [pose proof (fi_room t Hf); lia|]. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. lia.
Qed.
