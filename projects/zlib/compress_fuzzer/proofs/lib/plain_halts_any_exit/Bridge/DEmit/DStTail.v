(** * Bridge.DEmit.DStTail — pair D13 ([deflate_stored]), part 4: the tail ([deflate.c:1757-1798]).

    When the loop stops without having written the last block, both models
    slide the window if the input would not fit ([st_slide3] / the triple [p]
    of [dst_tail]), refill it from the input ([st_fillw] / [read_buf] into the
    window, group M's [dm_read_buf_window]), update [high_water], and emit one
    more stored block from the window if enough is there ([st_final] / the
    last [if] of [dst_tail]).

    RT's [dst_tail] is a single let-tower; [rt_tail_eq] splits it at the same
    seams as S5's own [post_hw_eq] / [post_slide_eq] ([rt_t_slide],
    [rt_t_fill], [RD.dst_highwater], [rt_tail_final]), by conversion only.

    Ownership: a worker (group D).  Reviewer: a worker. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require DeflateState Trees DeflateLz DeflateBlk
  RefDeflStored5 RefDeflStored6.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base Chunk ZBitsOut Trees Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelDefl S5Fields BrBits BrFlush.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DEmit Require Import DEmitDefs BrDFlush DTrStored DZHeader
  DStKit DStTrip DStWin.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DMatch Require Import DMatchDefs MLz.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DMatch Require MReadBuf DMatchIface.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Module T5 := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.RefDeflStored5.
Module T6 := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.RefDeflStored6.

(* ------------------------------------------------------------------------- *)
(* 1.  RT's tail at its seams                                                *)
(* ------------------------------------------------------------------------- *)

Definition rt_t_slide (g : RC.DeflGeom) (s3 : RD.DSt) : RD.DSt * Z :=
  let ws := RC.dg_w_size g in
  let l3 := RD.d_ls s3 in
  let havea := RD.ls_windowsize l3 - RD.ls_strstart l3 in
  let p := if (Z.ltb havea (RC.zlen (RD.zs_in (RD.d_strm s3)))) && (Z.leb ws (RD.ls_blockstart l3))
           then let ss := RD.ls_strstart l3 - ws in
                let l4 := RD.setL_strstart ss
                            (RD.setL_blockstart (RD.ls_blockstart l3 - ws)
                              (RD.setL_window (RD.win_move 0 ws ss (RD.ls_window l3)) l3)) in
                let l5 := if Z.ltb ss (RD.ls_insert l4) then RD.setL_insert ss l4 else l4 in
                (l5, havea + ws, true)
           else (l3, havea, false) in
  let l6 := fst (fst p) in
  let haveb := snd (fst p) in
  let bumped := snd p in
  let ts6 := if bumped && Z.ltb (RT.ts_matches (RD.d_ts s3)) 2
             then RT.set_matches (RT.ts_matches (RD.d_ts s3) + 1) (RD.d_ts s3) else RD.d_ts s3 in
  (RD.setD_ts ts6 (RD.setD_ls l6 s3), haveb).

Definition rt_t_fill (g : RC.DeflGeom) (s4 : RD.DSt) (haveb : Z) : RD.DSt :=
  let ws := RC.dg_w_size g in
  let l6 := RD.d_ls s4 in
  let have := RD.zmin haveb (RC.zlen (RD.zs_in (RD.d_strm s4))) in
  if Z.eqb have 0 then s4
  else
    let r2 := RD.read_buf (RD.d_wrap s4) have (RD.d_strm s4) in
    let dat := fst r2 in
    let l7 := RD.setL_window (RD.win_blit dat (RD.ls_strstart l6) (RD.ls_window l6)) l6 in
    let l8 := RD.setL_insert (RD.ls_insert l7 + RD.zmin have (ws - RD.ls_insert l7))
                (RD.setL_strstart (RD.ls_strstart l7 + have) l7) in
    RD.setD_ls l8 (RD.setD_strm (snd r2) s4).

Definition rt_tail_final (g : RC.DeflGeom) (s6 : RD.DSt) : RD.BlockState * RD.DSt :=
  let have2a := Z.shiftr (ZBitsOut.bw_valid (RT.ts_bw (RD.d_ts s6)) + 42) 3 in
  let have2 := RD.zmin (RC.dg_pending_buf_size g - have2a) RD.MAX_STORED in
  let mb2 := RD.zmin have2 (RC.dg_w_size g) in
  let left := RD.ls_strstart (RD.d_ls s6) - RD.ls_blockstart (RD.d_ls s6) in
  if (Z.leb mb2 left)
     || ((negb (Z.eqb left 0) || Z.eqb Z_FINISH Base.Z_FINISH) && negb (Z.eqb Z_FINISH Base.Z_NO_FLUSH)
         && (Z.eqb (RC.zlen (RD.zs_in (RD.d_strm s6))) 0) && (Z.leb left have2))
  then
    let len := RD.zmin left have2 in
    let last := if (Z.eqb Z_FINISH Base.Z_FINISH) && (Z.eqb (RC.zlen (RD.zs_in (RD.d_strm s6))) 0)
                   && (Z.eqb len left) then 1 else 0 in
    let dat := RD.win_take (RD.ls_window (RD.d_ls s6)) (RD.ls_blockstart (RD.d_ls s6)) len in
    let s7 := RD.setD_ts (RT.tr_stored_block dat len last (RD.d_ts s6))
                (RD.setD_ls (RD.setL_blockstart (RD.ls_blockstart (RD.d_ls s6) + len) (RD.d_ls s6)) s6) in
    let s8 := RD.flush_pending s7 in
    (if Z.eqb last 0 then RD.NeedMore else RD.FinishStarted, s8)
  else (RD.NeedMore, s6).

Lemma rt_tail_eq : forall g s3,
  RD.dst_tail Z_FINISH g s3
  = rt_tail_final g (RD.dst_highwater (rt_t_fill g (fst (rt_t_slide g s3)) (snd (rt_t_slide g s3)))).
Proof.
  intros g s3. unfold RD.dst_tail, rt_tail_final, rt_t_fill, rt_t_slide, RD.dst_highwater. reflexivity.
Qed.

Lemma cfg_slide : forall g t, RD.d_cfg (fst (rt_t_slide g t)) = RD.d_cfg t.
Proof. intros g t. reflexivity. Qed.

Lemma cfg_fill : forall g t h, RD.d_cfg (rt_t_fill g t h) = RD.d_cfg t.
Proof. intros g t h. unfold rt_t_fill. cbv zeta. destruct (_ =? 0); reflexivity. Qed.

Lemma cfg_hw : forall t, RD.d_cfg (RD.dst_highwater t) = RD.d_cfg t.
Proof. intros t. unfold RD.dst_highwater. destruct (_ <? _); reflexivity. Qed.

(* ------------------------------------------------------------------------- *)
(* 2.  Small kit                                                             *)
(* ------------------------------------------------------------------------- *)

(** What the trailer pair (D9) needs after the block function. *)
Definition post_ok (s : DS.deflate_state) : Prop :=
  DS.ds_sym_next s = 0 /\ fp_ok s /\ (DS.cs_avail_out (DS.ds_strm s) <> 0 -> room s 10).

Lemma sti_post_ok : forall s t pre_out pre_in, sti s t pre_out pre_in -> post_ok s.
Proof.
  intros s t pre_out pre_in Si.
  pose proof Si as [Hrel Hp Hpo Hbv Hsn Hao Hto Hroom Hc _ _ _ _ _ _ _ _].
  destruct (rel_view _ _ _ _ Hrel Hc) as (_ & _ & Epbl & _).
  split; [exact Hsn|]. split; [unfold fp_ok; lia|]. intros _. split; [exact Hpo | lia].
Qed.

Lemma arr_rel_move : forall (a : arr) w n src cnt,
  arr_rel a w 0 n -> arr_len a = n -> 0 <= src -> 0 <= cnt -> src + cnt <= n ->
  arr_rel (arr_blit a 0 a src cnt) (RD.win_move 0 src cnt w) 0 n.
Proof.
  intros a w n src cnt H La Hs Hc Hn i Hi.
  rewrite arr_get_blit. unfold RD.win_move, arr_inb. cbv beta. rewrite La.
  replace (Z.max 0 cnt) with cnt by lia.
  destruct (Z.leb_spec 0 i); destruct (Z.ltb_spec i (0 + cnt)); destruct (Z.ltb_spec i n); cbn [andb]; try lia.
  - rewrite H by lia. f_equal. lia.
  - apply H. lia.
Qed.

Lemma rt_ts_ls_eta : forall t, RD.setD_ts (RD.d_ts t) (RD.setD_ls (RD.d_ls t) t) = t.
Proof. intros t. destruct t. reflexivity. Qed.

Lemma rt_ss_bs_win : forall a b w l,
  RD.setL_strstart a (RD.setL_blockstart b (RD.setL_window w l))
  = RD.setL_window w (RD.setL_strstart a (RD.setL_blockstart b l)).
Proof. intros a b w l. destruct l. reflexivity. Qed.

Lemma rt_ls_strm_ls : forall a z b t,
  RD.setD_ls a (RD.setD_strm z (RD.setD_ls b t)) = RD.setD_ls a (RD.setD_strm z t).
Proof. intros a z b t. destruct t. reflexivity. Qed.

Lemma lz_rel_same : forall s t l, RD.d_ls t = l -> lz_rel s t -> lz_rel s (RD.setD_ls l t).
Proof. intros s t l E H. subst l. rewrite rt_setD_ls_eta. exact H. Qed.

Lemma nonlz_ins_ss : forall X a b, nonlz_view (DS.set_insert (DS.set_strstart X a) b) = nonlz_view X.
Proof. intros. destruct X; reflexivity. Qed.

Lemma nonlz_bs : forall X b, nonlz_view (DS.set_block_start X b) = nonlz_view X.
Proof. intros. destruct X; reflexivity. Qed.

Lemma rt_read_buf_bytes : forall w n st x, In x (fst (RD.read_buf w n st)) -> 0 <= x < 256.
Proof.
  intros w n st x Hx. unfold RD.read_buf in Hx. cbv zeta in Hx.
  match type of Hx with context [if ?c then _ else _] => destruct c end.
  - cbn [fst In] in Hx. contradiction.
  - cbn [fst] in Hx. apply in_map_iff in Hx as (y & <- & _). unfold Base.u8. apply Z.mod_pos_bound. lia.
Qed.

Lemma tsb_biv : forall s buf len last, DS.ds_bi_valid (DT.tr_stored_block s buf len last) = 0.
Proof.
  intros s buf len last. rewrite tsb_unfold. cbv zeta. unfold tsb_copy.
  destruct (negb (len =? 0)); [destruct buf|]; s5bw; rewrite !biv_put_short;
    unfold DT.bi_windup; cbv zeta; s5bw; reflexivity.
Qed.

Ltac s5_lzs := autorewrite with s5f_block_start s5f_insert s5f_strstart s5f_window s5f_matches s5f_strm.

(* ------------------------------------------------------------------------- *)
(* 3.  The slide                                                             *)
(* ------------------------------------------------------------------------- *)

Lemma pair_t_slide : forall s t pre_out pre_in g, sti s t pre_out pre_in -> cfg_facts g ->
  let h := wrap32 (DS.ds_window_size s - DS.ds_strstart s) in
  sti (fst (T6.st_slide3 s h)) (fst (rt_t_slide g t)) pre_out pre_in
  /\ snd (T6.st_slide3 s h) = snd (rt_t_slide g t)
  /\ RD.ls_strstart (RD.d_ls (fst (rt_t_slide g t))) + snd (rt_t_slide g t) = 65536.
Proof.
  intros s t pre_out pre_in g Si Hg. cbv zeta.
  pose proof Si as [Hrel Hp Hpo Hbv Hsn Hao Hto Hroom Hc Hrb Hwsz Hbs Hss Hdone Hinl Hwin Hins].
  destruct (rel_view _ _ _ _ Hrel Hc)
    as (Ews & _ & _ & Ewsz & Ewl & Ess & Ebs & _ & Eai & _ & _ & Eins & _ & Emt & _).
  pose proof (cf_w_size _ Hg) as Cws.
  pose proof Hrel as (_ & Hlz & _). pose proof (lzr_win _ _ Hlz) as Rw. pose proof (lzr_wlen _ _ Hlz) as Lw.
  pose proof (proj1 (m_dst_split _ _ _ _) Hrel) as [_ Hnl].
  unfold T6.st_slide3, rt_t_slide. cbv zeta. rewrite Ewsz, Ess, Ews, Ebs, Eai, Cws, Hwsz.
  rewrite (wrap32_id (65536 - RD.ls_strstart (RD.d_ls t))) by lia.
  destruct ((65536 - RD.ls_strstart (RD.d_ls t) <? RC.zlen (RD.zs_in (RD.d_strm t)))
            && (32768 <=? RD.ls_blockstart (RD.d_ls t))) eqn:C.
  2: { cbn [fst snd andb]. rewrite rt_ts_ls_eta. split; [exact Si|]. split; [reflexivity|]. lia. }
  apply andb_true_iff in C as [C1 C2]. apply Z.ltb_lt in C1. apply Z.leb_le in C2.
  cbn [fst snd andb].
  match goal with |- context [DS.set_window ?A ?W] => remember (DS.set_window A W) as X3 eqn:EX3 end.
  assert (FX : DS.ds_matches X3 = RT.ts_matches (RD.d_ts t)
               /\ DS.ds_strstart X3 = RD.ls_strstart (RD.d_ls t) - 32768
               /\ DS.ds_insert X3 = RD.ls_insert (RD.d_ls t) /\ DS.ds_w_size X3 = 32768).
  { subst X3. s5_lzs. rewrite ?Ess, ?Ews. split; [exact Emt|]. split; [reflexivity|]. split; [exact Eins | reflexivity]. }
  destruct FX as (FXm & FXs & FXi & FXw).
  assert (Fr : DS.ds_pending X3 = 0 /\ DS.ds_pending_out X3 = 0 /\ DS.ds_bi_valid X3 = 0
               /\ DS.ds_sym_next X3 = 0 /\ DS.ds_strm X3 = DS.ds_strm s
               /\ arr_len (DS.ds_pending_buf X3) = arr_len (DS.ds_pending_buf s)).
  { subst X3. s5_lzs. repeat split; assumption. }
  destruct Fr as (P1 & P2 & P3 & P4 & P5 & P6).
  assert (Hlz3 : lz_rel X3 (RD.setD_ls (RD.setL_strstart (RD.ls_strstart (RD.d_ls t) - 32768)
                    (RD.setL_blockstart (RD.ls_blockstart (RD.d_ls t) - 32768)
                       (RD.setL_window (RD.win_move 0 32768 (RD.ls_strstart (RD.d_ls t) - 32768)
                          (RD.ls_window (RD.d_ls t))) (RD.d_ls t)))) t)).
  { subst X3. rewrite rt_ss_bs_win.
    apply lz_set_window.
    - apply lz_set_strstart; [|s5_lzs; rewrite ?Ess, ?Ews; reflexivity].
      apply lz_set_block_start; [rewrite rt_setD_ls_eta; exact Hlz | reflexivity].
    - rewrite arr_len_blit. s5_lzs. reflexivity.
    - s5_lzs. rewrite ?Ess, ?Ews. rt_lz. rewrite Hwsz in Rw |- *.
      apply arr_rel_move; [exact Rw | rewrite Lw; exact Hwsz | lia | lia | lia]. }
  assert (Eli : RD.ls_insert (RD.setL_strstart (RD.ls_strstart (RD.d_ls t) - 32768)
                  (RD.setL_blockstart (RD.ls_blockstart (RD.d_ls t) - 32768)
                     (RD.setL_window (RD.win_move 0 32768 (RD.ls_strstart (RD.d_ls t) - 32768)
                        (RD.ls_window (RD.d_ls t))) (RD.d_ls t))))
                = RD.ls_insert (RD.d_ls t)) by reflexivity.
  rewrite Eli. rewrite FXm.
  destruct (Z.ltb_spec (RT.ts_matches (RD.d_ts t)) 2) as [M|M]; cbv beta iota; s5_lzs; rewrite ?FXs, ?FXi;
    destruct (Z.ltb_spec (RD.ls_strstart (RD.d_ls t) - 32768) (RD.ls_insert (RD.d_ls t))) as [I|I];
    cbv beta iota; s5_lzs; rewrite ?FXw;
    (split; [|split; [rewrite wrap32_id by lia; reflexivity | rt_lz; lia]]);
    (apply mkSti;
     [ first [apply (dst_step_0 s) | apply (dst_step_m s)];
       [ exact Hrel
       | rewrite EX3; destruct s; reflexivity
       | first [ apply lz_set_insert; [apply lz_rel_matches; exact Hlz3 | reflexivity]
               | apply lz_rel_matches; exact Hlz3
               | apply lz_set_insert; [exact Hlz3 | reflexivity]
               | exact Hlz3 ] ]
     | s5_lzs; rewrite ?P5, ?P6; rt_lz;
       try first [assumption | lia | eapply rb_ok_frame; [| | | eassumption]; reflexivity
                 | intros i Hi; apply win_move_bytes; [exact Hwin | lia | lia | exact Hi]] ..]).
Qed.

(* ------------------------------------------------------------------------- *)
(* 4.  The refill                                                            *)
(* ------------------------------------------------------------------------- *)

Lemma pair_fill : forall s t pre_out pre_in n, sti s t pre_out pre_in ->
  0 < n <= DS.cs_avail_in (DS.ds_strm s) -> RD.ls_strstart (RD.d_ls t) + n <= 65536 ->
  let r := RD.read_buf (RD.d_wrap t) n (RD.d_strm t) in
  let l7 := RD.setL_window (RD.win_blit (fst r) (RD.ls_strstart (RD.d_ls t)) (RD.ls_window (RD.d_ls t)))
              (RD.d_ls t) in
  let l8 := RD.setL_insert (RD.ls_insert l7 + RD.zmin n (32768 - RD.ls_insert l7))
              (RD.setL_strstart (RD.ls_strstart l7 + n) l7) in
  sti (T6.st_fillw s n) (RD.setD_ls l8 (RD.setD_strm (snd r) (RD.setD_ls l7 t))) pre_out pre_in.
Proof.
  intros s t pre_out pre_in n Si Hn Hsn. cbv zeta.
  pose proof Si as [Hrel Hp Hpo Hbv Hsn0 Hao Hto Hroom Hc Hrb Hwsz Hbs Hss Hdone Hinl Hwin Hins].
  destruct (rel_view _ _ _ _ Hrel Hc)
    as (Ews & _ & Epbl & _ & _ & Ess & _ & _ & Eai & _ & _ & Eins & _ & _ & _).
  pose proof (zlen_done_rel _ _ _ _ Hrel) as D0.
  destruct (DMatchIface.dm_read_buf_window s t pre_out pre_in (RD.ls_strstart (RD.d_ls t)) n Hrel Hrb
              ltac:(lia) ltac:(lia) ltac:(rewrite Hwsz; lia)) as (_ & A2 & A3 & _).
  pose proof (MReadBuf.m_s5_read_buf_window_eq s (RD.ls_strstart (RD.d_ls t)) n) as E5. cbv zeta in E5.
  replace (Z.min n (DS.cs_avail_in (DS.ds_strm s))) with n in E5 by lia. specialize (E5 ltac:(lia)).
  rewrite E5 in A2. cbn [fst] in A2.
  destruct (MReadBuf.m_s5_rb_strm_fields (DS.ds_strm s) (DS.ds_wrap s) n []) as (R1 & R2 & R3 & _ & R5 & _ & R7 & _).
  unfold T6.st_fillw. replace (negb (n =? 0)) with true by (symmetry; apply negb_true_iff, Z.eqb_neq; lia).
  rewrite Ess, E5. cbv beta iota zeta. s5_lzs. rewrite ?Ess, ?Ews, ?Eins.
  assert (H6 : dst_rel
     (DS.set_insert
        (DS.set_strstart (DS.set_strm (DS.set_window s (arr_upd (DS.ds_window s) (RD.ls_strstart (RD.d_ls t))
                                (arr_slice (DS.cs_input (DS.ds_strm s)) (DS.cs_next_in (DS.ds_strm s)) n)))
                          (MReadBuf.s5_rb_strm (DS.ds_strm s) (DS.ds_wrap s) n []))
           (RD.ls_strstart (RD.d_ls t) + n))
        (RD.ls_insert (RD.d_ls t) + DB.MIN n (wrap32 (32768 - RD.ls_insert (RD.d_ls t)))))
     (RD.setD_ls
        (RD.setL_insert
           (RD.ls_insert (RD.setL_window (RD.win_blit (fst (RD.read_buf (RD.d_wrap t) n (RD.d_strm t)))
                 (RD.ls_strstart (RD.d_ls t)) (RD.ls_window (RD.d_ls t))) (RD.d_ls t))
            + RD.zmin n (32768 - RD.ls_insert (RD.setL_window (RD.win_blit (fst (RD.read_buf (RD.d_wrap t) n (RD.d_strm t)))
                 (RD.ls_strstart (RD.d_ls t)) (RD.ls_window (RD.d_ls t))) (RD.d_ls t))))
           (RD.setL_strstart
              (RD.ls_strstart (RD.setL_window (RD.win_blit (fst (RD.read_buf (RD.d_wrap t) n (RD.d_strm t)))
                 (RD.ls_strstart (RD.d_ls t)) (RD.ls_window (RD.d_ls t))) (RD.d_ls t)) + n)
              (RD.setL_window (RD.win_blit (fst (RD.read_buf (RD.d_wrap t) n (RD.d_strm t)))
                 (RD.ls_strstart (RD.d_ls t)) (RD.ls_window (RD.d_ls t))) (RD.d_ls t))))
        (RD.setD_strm (snd (RD.read_buf (RD.d_wrap t) n (RD.d_strm t)))
           (RD.setD_ls (RD.setL_window (RD.win_blit (fst (RD.read_buf (RD.d_wrap t) n (RD.d_strm t)))
                 (RD.ls_strstart (RD.d_ls t)) (RD.ls_window (RD.d_ls t))) (RD.d_ls t)) t)))
     pre_out pre_in).
  { apply (m_lz_step _ _ _ _ _ _ A2); [apply nonlz_ins_ss|].
    apply lz_set_insert; [|rt_lz; unfold DB.MIN, RD.zmin; rewrite wrap32_id by lia; reflexivity].
    apply lz_set_strstart; [|rt_lz; reflexivity].
    apply lz_rel_same; [reflexivity | exact (proj1 (proj2 A2))]. }
  pose proof (zlen_done_rel _ _ _ _ H6) as D1.
  pose proof (rel_view _ _ _ _ H6) as V6. cbn [RD.d_cfg RD.setD_ls RD.setD_strm] in V6.
  specialize (V6 Hc). destruct V6 as (_ & _ & _ & _ & _ & _ & _ & _ & Eai1 & _).
  autorewrite with s5f_block_start s5f_insert s5f_strstart s5f_window s5f_matches s5f_strm in D1, Eai1.
  cbn [RD.d_strm RD.setD_ls RD.setD_strm] in D1, Eai1.
  rewrite R2 in D1. rewrite R3 in Eai1.
  apply mkSti; [exact H6 | s5_lzs; rewrite ?R5, ?R7; rt_lz; cbn [RD.d_strm RD.setD_strm RD.setD_ls];
                           try first [assumption | lia] ..].
  all: first [ eapply rb_ok_frame; [| | | exact A3]; reflexivity
             | intros i Hi; apply win_blit_bytes; [apply rt_read_buf_bytes | apply Hwin; exact Hi]
             | unfold RD.zmin; destruct (Z.ltb_spec (32768 - RD.ls_insert (RD.d_ls t)) n); lia ].
Qed.

Lemma pair_t_fill : forall s t pre_out pre_in g h, sti s t pre_out pre_in -> cfg_facts g -> 0 <= h ->
  RD.ls_strstart (RD.d_ls t) + h <= 65536 ->
  sti (T6.st_fillw s (T5.fmin h (DS.cs_avail_in (DS.ds_strm s)))) (rt_t_fill g t h) pre_out pre_in.
Proof.
  intros s t pre_out pre_in g h Si Hg Hh Hsh.
  pose proof Si as [Hrel _ _ _ _ _ _ _ Hc _ _ _ _ _ _ _ _].
  destruct (rel_view _ _ _ _ Hrel Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & Eai & _).
  pose proof (cf_w_size _ Hg) as Cws.
  unfold rt_t_fill. cbv zeta. rewrite Cws, <- Eai.
  change (T5.fmin h (DS.cs_avail_in (DS.ds_strm s))) with (RD.zmin h (DS.cs_avail_in (DS.ds_strm s))).
  assert (Hn : 0 <= RD.zmin h (DS.cs_avail_in (DS.ds_strm s)) <= h
               /\ RD.zmin h (DS.cs_avail_in (DS.ds_strm s)) <= DS.cs_avail_in (DS.ds_strm s)).
  { pose proof (si_rel _ _ _ _ Si) as (_ & _ & _ & _ & _ & Hst). unfold strm_rel in Hst. cbv zeta in Hst.
    unfold RD.zmin. destruct (Z.ltb_spec (DS.cs_avail_in (DS.ds_strm s)) h); lia. }
  revert Hn. generalize (RD.zmin h (DS.cs_avail_in (DS.ds_strm s))) as n. intros n Hn.
  destruct (Z.eqb_spec n 0) as [N0|N0].
  - subst n. unfold T6.st_fillw. cbn [negb Z.eqb]. exact Si.
  - pose proof (pair_fill s t pre_out pre_in n Si ltac:(lia) ltac:(lia)) as H. cbv zeta in H.
    rewrite rt_ls_strm_ls in H. exact H.
Qed.

(* ------------------------------------------------------------------------- *)
(* 5.  The last block from the window                                        *)
(* ------------------------------------------------------------------------- *)

Lemma pair_final : forall s t pre_out pre_in g, sti s t pre_out pre_in -> cfg_facts g ->
  bs_of (snd (T6.st_final s Z_FINISH)) = fst (rt_tail_final g t)
  /\ dst_rel (fst (T6.st_final s Z_FINISH)) (snd (rt_tail_final g t)) pre_out pre_in
  /\ post_ok (fst (T6.st_final s Z_FINISH)).
Proof.
  intros s t pre_out pre_in g Si Hg.
  pose proof Si as [Hrel Hp Hpo Hbv Hsn Hao Hto Hroom Hc Hrb Hwsz Hbs Hss Hdone Hinl Hwin Hins].
  destruct (rel_view _ _ _ _ Hrel Hc)
    as (Ews & Epbs & Epbl & _ & _ & Ess & Ebs & _ & Eai & Eao & Eto & _ & _ & _ & Ebv).
  pose proof (cf_w_size _ Hg) as Cws. pose proof (cf_pbs _ Hg) as Cpbs.
  assert (Eth : T5.t_have s = 65531) by (unfold T5.t_have, DB.MIN, DS.MAX_STORED; rewrite Epbs, Hbv; reflexivity).
  assert (Etm : T5.t_mb s = 32768) by (unfold T5.t_mb, DB.MIN; rewrite Eth, Ews; reflexivity).
  unfold T6.st_final, rt_tail_final. cbv zeta.
  rewrite Eth, Etm, <- Ebv, Hbv, Cpbs, Cws.
  change (RD.zmin (65536 - Z.shiftr (0 + 42) 3) RD.MAX_STORED) with 65531.
  change (RD.zmin 65531 32768) with 32768.
  rewrite (wrap32_id (DS.ds_strstart s - DS.ds_block_start s)) by lia.
  rewrite <- Ess, <- Ebs, <- Eai.
  rewrite ?fin_eq_rt, ?fin_nf_rt, ?fin_eq_s5, ?fin_nf_s5.
  unfold DB.MIN, RD.zmin.
  match goal with |- context [if ?c then _ else (RD.NeedMore, t)] => destruct c eqn:Cf end.
  2: { cbn [fst snd bs_of]. split; [reflexivity|]. split; [exact Hrel | exact (sti_post_ok _ _ _ _ Si)]. }
  remember (if 65531 <? DS.ds_strstart s - DS.ds_block_start s then 65531
            else DS.ds_strstart s - DS.ds_block_start s) as LEN eqn:HLEN.
  assert (HL : 0 <= LEN <= 65531 /\ LEN <= DS.ds_strstart s - DS.ds_block_start s)
    by (subst LEN; destruct (Z.ltb_spec 65531 (DS.ds_strstart s - DS.ds_block_start s)); lia).
  remember (if true && (DS.cs_avail_in (DS.ds_strm s) =? 0) && (LEN =? DS.ds_strstart s - DS.ds_block_start s)
            then 1 else 0) as LAST eqn:HLAST.
  destruct (send_bits3_0 s (Z.shiftl DS.STORED_BLOCK 1 + LAST) Hbv) as (SB1 & SB2).
  destruct (bi_windup3 _ SB2) as (BW1 & _).
  pose proof (tsb_pending s (Some (DS.ds_block_start s)) LEN LAST) as TP. rewrite BW1, SB1, Hp in TP.
  assert (Hsrc : stored_src_rt t (Some (DS.ds_block_start s)) LEN
                   (RD.win_take (RD.ls_window (RD.d_ls t)) (DS.ds_block_start s) LEN)).
  { unfold stored_src_rt. split; [lia|]. split; [lia|]. split; [reflexivity|]. intros i Hi. apply Hwin. lia. }
  destruct (pair_tr_stored_block s t pre_out pre_in (Some (DS.ds_block_start s)) LEN LAST
              (RD.win_take (RD.ls_window (RD.d_ls t)) (DS.ds_block_start s) LEN) Hrel Hsn Hpo
              ltac:(lia) ltac:(lia) Hsrc) as (H1 & Hpo1 & Hsn1).
  pose proof (bw4_tr_stored_block s (Some (DS.ds_block_start s)) LEN LAST ltac:(lia)) as F1.
  destruct (bw4_proj _ _ F1) as (_ & Est1 & _ & _).
  assert (Ebs1 : DS.ds_block_start (DT.tr_stored_block s (Some (DS.ds_block_start s)) LEN LAST) = DS.ds_block_start s)
    by (destruct F1 as (E & _); rewrite E; unfold set4; s5bw; reflexivity).
  assert (L1 : arr_len (DS.ds_pending_buf (DT.tr_stored_block s (Some (DS.ds_block_start s)) LEN LAST)) = 65536)
    by (destruct F1 as (_ & L & _); lia).
  pose proof (tsb_biv s (Some (DS.ds_block_start s)) LEN LAST) as V1.
  clear F1.
  revert H1 Hpo1 Hsn1 Est1 Ebs1 L1 V1 TP.
  generalize (DT.tr_stored_block s (Some (DS.ds_block_start s)) LEN LAST) as x1.
  generalize (RT.tr_stored_block (RD.win_take (RD.ls_window (RD.d_ls t)) (DS.ds_block_start s) LEN) LEN LAST
                (RD.d_ts t)) as ts1.
  intros ts1 x1 H1 Hpo1 Hsn1 Est1 Ebs1 L1 V1 TP.
  rewrite Ebs1.
  (* the block start moves past the block, then the flush *)
  remember (RD.setD_ts ts1 (RD.setD_ls (RD.setL_blockstart (DS.ds_block_start s + LEN) (RD.d_ls t)) t))
    as T2 eqn:ET2.
  remember (DS.set_block_start x1 (DS.ds_block_start s + LEN)) as x2 eqn:EX2.
  assert (H2 : dst_rel x2 T2 pre_out pre_in).
  { subst x2 T2. rewrite <- rt_ls_ts. apply (m_lz_step _ _ _ _ _ _ H1); [apply nonlz_bs|].
    apply lz_set_block_start; [|reflexivity].
    apply lz_rel_same; [reflexivity | exact (proj1 (proj2 H1))]. }
  assert (Fx2 : DS.ds_pending x2 = 5 + LEN /\ DS.ds_pending_out x2 = 0 /\ DS.ds_bi_valid x2 = 0
                /\ DS.ds_sym_next x2 = 0 /\ DS.ds_strm x2 = DS.ds_strm s
                /\ arr_len (DS.ds_pending_buf x2) = 65536).
  { subst x2. autorewrite with s5f_block_start. repeat split; first [lia | assumption]. }
  destruct Fx2 as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6).
  assert (ET2s : RD.d_strm T2 = RD.d_strm t) by (subst T2; reflexivity).
  assert (ET2c : RD.d_cfg T2 = RD.d_cfg t) by (subst T2; reflexivity).
  assert (Hok2 : fp_ok x2) by (unfold fp_ok; rewrite Q5, Q6; lia).
  assert (Hfr2 : flush_room x2) by (left; lia).
  pose proof (dst_flush_pending x2 T2 pre_out pre_in H2 Q4 Hfr2 Hok2) as H3.
  cbn [fst snd].
  split; [destruct (LAST =? 0); reflexivity|]. split; [exact H3|].
  destruct (rt_flush_pending_frame T2) as (G1 & _).
  assert (Hc3 : cfg_facts (RD.d_cfg (RD.flush_pending T2))) by (rewrite G1, ET2c; exact Hc).
  destruct (rel_view _ _ _ _ H3 Hc3) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Eao3 & Eto3 & _).
  assert (Hav2 : 0 <= RD.zs_availout (RD.d_strm T2)) by (rewrite ET2s, <- Eao; lia).
  destruct (rt_flush_pending_out T2 Hav2) as (O1 & O2 & O3).
  rewrite ET2s in O2, O3.
  split; [rewrite flush_sym_next; exact Q4|]. split.
  - unfold fp_ok. rewrite flush_pending_pb_len, Q6, Eao3, Eto3. lia.
  - intros Hne. destruct (flush_pending_drained x2 Q2 ltac:(lia) ltac:(lia) ltac:(lia) Hne) as (D1 & D2 & _).
    split; [exact D2|]. rewrite D1, flush_pending_pb_len, Q6. lia.
Qed.

(* ------------------------------------------------------------------------- *)
(* 6.  The tail                                                              *)
(* ------------------------------------------------------------------------- *)

Theorem pair_tail : forall s t pre_out pre_in g, sti s t pre_out pre_in -> cfg_facts g ->
  bs_of (snd (T6.post_hw s 0 Z_FINISH)) = fst (RD.dst_tail Z_FINISH g t)
  /\ dst_rel (fst (T6.post_hw s 0 Z_FINISH)) (snd (RD.dst_tail Z_FINISH g t)) pre_out pre_in
  /\ post_ok (fst (T6.post_hw s 0 Z_FINISH)).
Proof.
  intros s t pre_out pre_in g Si Hg.
  rewrite T6.post_hw_eq, rt_tail_eq. rewrite fin_nf_s5, fin_eq_s5. cbn [negb andb Z.eqb].
  destruct (pair_t_slide s t pre_out pre_in g Si Hg) as (S4 & H4e & H4s).
  revert S4 H4e.
  destruct (T6.st_slide3 s (wrap32 (DS.ds_window_size s - DS.ds_strstart s))) as [s4 h4].
  cbn [fst snd]. intros S4 H4e.
  rewrite T6.post_slide_eq. subst h4.
  pose proof (si_ss _ _ _ _ S4) as Hss4.
  pose proof (pair_t_fill s4 (fst (rt_t_slide g t)) pre_out pre_in g (snd (rt_t_slide g t)) S4 Hg
                ltac:(lia) ltac:(lia)) as S5'.
  pose proof (pair_hw _ _ _ _ S5') as S6.
  exact (pair_final _ _ _ _ g S6 Hg).
Qed.

