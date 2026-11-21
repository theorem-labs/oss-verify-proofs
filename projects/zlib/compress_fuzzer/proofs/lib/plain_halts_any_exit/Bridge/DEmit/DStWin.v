(** * Bridge.DEmit.DStWin — pair D13 ([deflate_stored]), part 3: the window update after the loop.

    After the loop both models copy the last [used] bytes consumed by the
    call into the window ([deflate.c:1718-1743]): S5 from the call's input
    array ([st_wupd], split by its own [RefDeflStored7] into the three cases
    [st_wupd_sup] / [st_wupd_app] / [st_wupd_sla]), RT from [lastn] of its
    consumed list ([dst_win_update]).  [strm_rel] says the consumed list ends
    with the input array's prefix, so the two byte lists are equal
    ([lastn_slice]).  Then [high_water] ([hw_st] / [dst_highwater]).

    Each keeps [sti] ([pair_wupd], [pair_hw]).

    Ownership: a worker (group D).  Reviewer: a worker. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require DeflateState Trees DeflateLz DeflateBlk
  RefDeflStored5 RefDeflStored6 RefDeflStored7.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base Chunk ZBitsOut Trees Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelDefl S5Fields BrBits BrFlush.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DEmit Require Import DEmitDefs BrDFlush DTrStored DZHeader DStKit DStTrip.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DMatch Require Import DMatchDefs MLz.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DMatch Require MReadBuf.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Module W5 := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.RefDeflStored5.
Module W6 := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.RefDeflStored6.
Module W7 := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.RefDeflStored7.

(* ------------------------------------------------------------------------- *)
(* 1.  Window writes                                                         *)
(* ------------------------------------------------------------------------- *)

Lemma arr_rel_upd : forall (a : arr) w n base (l : list Z),
  arr_rel a w 0 n -> arr_len a = n -> 0 <= base -> base + zlength l <= n ->
  arr_rel (arr_upd a base l) (RD.win_blit l base w) 0 n.
Proof.
  intros a w n base l H La Hb Hl i Hi.
  rewrite (arr_get_upd _ _ _ _ 0). unfold RD.win_blit, arr_inb, Base.zlist. cbv beta zeta.
  change RC.zlen with (@zlength Z). rewrite La.
  destruct (Z.leb_spec base i); destruct (Z.ltb_spec i (base + zlength l));
    destruct (Z.leb_spec 0 i); destruct (Z.ltb_spec i n); cbn [andb]; try lia; try reflexivity; apply H; lia.
Qed.

(** S5 slides its window as [arr_upd w 0 (arr_slice w src n)] ([st_wupd_sla]),
    RT as [win_move 0 src n]. *)
Lemma arr_rel_slide : forall (a : arr) w n src cnt,
  arr_rel a w 0 n -> arr_len a = n -> 0 <= src -> 0 <= cnt -> src + cnt <= n ->
  arr_rel (arr_upd a 0 (arr_slice a src cnt)) (RD.win_move 0 src cnt w) 0 n.
Proof.
  intros a w n src cnt H La Hs Hc Hn i Hi.
  rewrite (arr_get_upd _ _ _ _ 0). unfold RD.win_move, arr_inb. cbv beta.
  rewrite arr_slice_length, La. replace (Z.max 0 cnt) with cnt by lia.
  destruct (Z.leb_spec 0 i); destruct (Z.ltb_spec i (0 + cnt)); destruct (Z.ltb_spec i n); cbn [andb];
    try lia.
  - unfold arr_slice. rewrite arr_slice_nat_nth by lia. rewrite H by lia. f_equal. lia.
  - apply H. lia.
Qed.

Lemma win_blit_bytes : forall (l : list Z) base w i,
  (forall x, In x l -> 0 <= x < 256) -> 0 <= w i < 256 -> 0 <= RD.win_blit l base w i < 256.
Proof.
  intros l base w i Hl Hw. unfold RD.win_blit, Base.zlist. cbv beta zeta.
  destruct ((base <=? i) && (i <? base + RC.zlen l)); [|exact Hw].
  destruct (Nat.lt_ge_cases (Z.to_nat (i - base)) (length l)) as [Hlt|Hge].
  - apply Hl. apply nth_In. exact Hlt.
  - rewrite nth_overflow by exact Hge. lia.
Qed.

Lemma win_move_bytes : forall src cnt w i,
  (forall j, 0 <= j < 65536 -> 0 <= w j < 256) -> 0 <= src -> src + cnt <= 65536 -> 0 <= i < 65536 ->
  0 <= RD.win_move 0 src cnt w i < 256.
Proof.
  intros src cnt w i Hw Hs Hc Hi. unfold RD.win_move. cbv beta.
  destruct (Z.leb_spec 0 i); destruct (Z.ltb_spec i (0 + cnt)); cbn [andb]; apply Hw; lia.
Qed.

Lemma lastn_slice : forall (pre : list Z) (inp : arr) ni k, 0 <= k <= ni ->
  RD.lastn k (pre ++ arr_slice inp 0 ni) = arr_slice inp (ni - k) k.
Proof.
  intros pre inp ni k Hk. unfold RD.lastn.
  change RC.zlen with (@zlength Z). rewrite zlength_app, arr_slice_length.
  replace (Z.to_nat (zlength pre + Z.max 0 ni - k)) with (length pre + Z.to_nat (ni - k))%nat
    by (unfold zlength; lia).
  rewrite skipn_app, skipn_all2 by lia.
  replace (length pre + Z.to_nat (ni - k) - length pre)%nat with (Z.to_nat (ni - k)) by lia.
  cbn [app]. rewrite <- slice_skipn by lia. f_equal; lia.
Qed.

(* ------------------------------------------------------------------------- *)
(* 2.  A window step: LZ fields and [matches]                                *)
(* ------------------------------------------------------------------------- *)

Lemma nl_matches : forall s t m pre_out pre_in, nl_rel s t pre_out pre_in ->
  nl_rel (DS.set_matches s m) (RD.setD_ts (RT.set_matches m (RD.d_ts t)) t) pre_out pre_in.
Proof.
  intros s t m pre_out pre_in H.
  unfold nl_rel, geom_rel, bw_rel, pend_rel, sym_rel, tree_rel, strm_rel, DS.sym_buf_get, DS.cs_output in *.
  cbv zeta in *.
  cbn [RD.d_cfg RD.d_status RD.d_wrap RD.d_lastflush RD.d_ts RD.d_strm RD.setD_ts RT.set_matches RT.ts_bw
       RT.ts_symnext RT.ts_symbuf RT.ts_trees RT.ts_blcount RT.ts_heap RT.ts_depth RT.ts_maxcode RT.ts_heaplen
       RT.ts_heapmax RT.ts_optlen RT.ts_statlen RT.ts_matches].
  autorewrite with s5f_matches.
  and_hyps. and_goal; first [assumption | reflexivity].
Qed.

Lemma lz_rel_matches : forall s t m, lz_rel s t -> lz_rel (DS.set_matches s m) t.
Proof. intros s t m H. unfold lz_rel in *. cbv zeta in *. autorewrite with s5f_matches. exact H. Qed.

Lemma rt_ls_ts : forall l ts t, RD.setD_ls l (RD.setD_ts ts t) = RD.setD_ts ts (RD.setD_ls l t).
Proof. intros l ts t. destruct t. reflexivity. Qed.

Lemma rt_ts_eta_ls : forall l t, RD.setD_ts (RD.d_ts t) (RD.setD_ls l t) = RD.setD_ls l t.
Proof. intros l t. destruct t. reflexivity. Qed.

Lemma rt_ss_win : forall a b l, RD.setL_strstart a (RD.setL_window b l) = RD.setL_window b (RD.setL_strstart a l).
Proof. intros a b l. destruct l. reflexivity. Qed.

Lemma dst_step_m : forall s s' t l m pre_out pre_in,
  dst_rel s t pre_out pre_in -> nonlz_view s' = nonlz_view (DS.set_matches s m) ->
  lz_rel s' (RD.setD_ls l t) ->
  dst_rel s' (RD.setD_ts (RT.set_matches m (RD.d_ts t)) (RD.setD_ls l t)) pre_out pre_in.
Proof.
  intros s s' t l m pre_out pre_in H Hv Hl.
  apply m_dst_split in H as [_ Hn]. apply m_dst_split. split.
  - revert Hl. unfold lz_rel. cbn [RD.d_ls RD.setD_ts RD.setD_ls]. exact (fun H => H).
  - rewrite <- rt_ls_ts. exact (m_nl_frame _ _ _ l pre_out pre_in Hv (nl_matches s t m pre_out pre_in Hn)).
Qed.

Lemma dst_step_0 : forall s s' t l pre_out pre_in,
  dst_rel s t pre_out pre_in -> nonlz_view s' = nonlz_view s -> lz_rel s' (RD.setD_ls l t) ->
  dst_rel s' (RD.setD_ts (RD.d_ts t) (RD.setD_ls l t)) pre_out pre_in.
Proof. intros s s' t l pre_out pre_in H Hv Hl. rewrite rt_ts_eta_ls. apply (m_lz_step s); assumption. Qed.

Ltac s5_lz := autorewrite with s5f_block_start s5f_insert s5f_strstart s5f_window s5f_matches s5f_high_water.
Ltac rt_lz :=
  cbn [RD.d_cfg RD.d_wrap RD.d_ls RD.d_strm RD.d_ts RD.setD_ts RD.setD_ls RD.setL_window RD.setL_strstart
       RD.setL_insert RD.setL_blockstart RD.setL_highwater RD.ls_windowsize RD.ls_blockstart RD.ls_strstart
       RD.ls_window RD.ls_insert RD.ls_highwater].
Ltac sti_tail :=
  s5_lz; rt_lz;
  try first [assumption | lia
             | eapply rb_ok_frame; [| | | eassumption]; reflexivity].


Lemma rt_setD_ts_eta' : forall t, RD.setD_ts (RD.d_ts t) t = t.
Proof. intros t. destruct t. reflexivity. Qed.

(** Over an abstract window value (a concrete one would let conversion
    unfold [arr_slice] 32768 times). *)
Lemma nonlz_lz4 : forall X w a b c,
  nonlz_view (DS.set_block_start (DS.set_insert (DS.set_strstart (DS.set_window X w) a) b) c) = nonlz_view X.
Proof. intros. destruct X; reflexivity. Qed.

(* ------------------------------------------------------------------------- *)
(* 3.  The window update                                                     *)
(* ------------------------------------------------------------------------- *)

(** The copy of the last [used] input bytes at [strstart], on a state [X]
    that has already slid (or not): the tail both cases share. *)
Definition s5_app (X : DS.deflate_state) (used ws : Z) : DS.deflate_state :=
  DS.set_block_start
    (DS.set_insert
       (DS.set_strstart
          (DS.set_window X (arr_upd (DS.ds_window X) (DS.ds_strstart X)
                              (arr_slice (DS.cs_input (DS.ds_strm X)) (DS.cs_next_in (DS.ds_strm X) - used) used)))
          (DS.ds_strstart X + used))
       (W5.ins_add (DS.ds_insert X) used ws))
    (DS.ds_strstart X + used).

Definition rt_app (la : RD.LSt) (ts : RT.TSt) (t : RD.DSt) (used : Z) : RD.DSt :=
  let lb := RD.setL_window (RD.win_blit (RD.lastn used (RD.zs_done (RD.d_strm t))) (RD.ls_strstart la)
                                        (RD.ls_window la)) la in
  let l' := RD.setL_insert (RD.ls_insert lb + RD.zmin used (32768 - RD.ls_insert lb))
              (RD.setL_strstart (RD.ls_strstart lb + used) lb) in
  RD.setD_ts ts (RD.setD_ls (RD.setL_blockstart (RD.ls_strstart l') l') t).

Lemma s5_app_noslide : forall s used, used <> 0 -> DS.ds_w_size s = 32768 -> used < 32768 ->
  used < DS.ds_window_size s - DS.ds_strstart s ->
  W6.st_wupd s used = s5_app s used 32768.
Proof.
  intros s used H0 Hws H1 H2. rewrite (W7.st_wupd_app s used H0 ltac:(lia) H2). cbv zeta.
  unfold s5_app. s5_lz. rewrite Hws. reflexivity.
Qed.

Lemma s5_app_slide : forall s used, used <> 0 -> DS.ds_w_size s = 32768 -> used < 32768 ->
  DS.ds_window_size s - DS.ds_strstart s <= used ->
  W6.st_wupd s used
  = s5_app (W5.sl_fix (DS.set_window (DS.set_strstart s (DS.ds_strstart s - DS.ds_w_size s))
              (arr_upd (DS.ds_window (DS.set_strstart s (DS.ds_strstart s - DS.ds_w_size s))) 0
                 (arr_slice (DS.ds_window (DS.set_strstart s (DS.ds_strstart s - DS.ds_w_size s)))
                    (DS.ds_w_size s) (DS.ds_strstart s - DS.ds_w_size s))))) used 32768.
Proof.
  intros s used H0 Hws H1 H2. rewrite (W7.st_wupd_sla s used H0 ltac:(lia) H2). cbv zeta.
  generalize (W5.sl_fix (DS.set_window (DS.set_strstart s (DS.ds_strstart s - DS.ds_w_size s))
              (arr_upd (DS.ds_window (DS.set_strstart s (DS.ds_strstart s - DS.ds_w_size s))) 0
                 (arr_slice (DS.ds_window (DS.set_strstart s (DS.ds_strstart s - DS.ds_w_size s)))
                    (DS.ds_w_size s) (DS.ds_strstart s - DS.ds_w_size s))))) as X3.
  intros X3. unfold s5_app. s5_lz. rewrite Hws. reflexivity.
Qed.

Lemma rt_app_noslide : forall g t used, RC.dg_w_size g = 32768 -> used <> 0 -> used < 32768 ->
  used < RD.ls_windowsize (RD.d_ls t) - RD.ls_strstart (RD.d_ls t) ->
  RD.dst_win_update g used t = rt_app (RD.d_ls t) (RD.d_ts t) t used.
Proof.
  intros g t used Hws H0 H1 H2. unfold RD.dst_win_update, rt_app. cbv zeta. rewrite Hws.
  replace (used =? 0) with false by (symmetry; apply Z.eqb_neq; exact H0).
  replace (32768 <=? used) with false by (symmetry; apply Z.leb_gt; lia).
  replace (RD.ls_windowsize (RD.d_ls t) - RD.ls_strstart (RD.d_ls t) <=? used) with false
    by (symmetry; apply Z.leb_gt; lia).
  reflexivity.
Qed.

Lemma rt_app_slide : forall g t used, RC.dg_w_size g = 32768 -> used <> 0 -> used < 32768 ->
  RD.ls_windowsize (RD.d_ls t) - RD.ls_strstart (RD.d_ls t) <= used ->
  let ss := RD.ls_strstart (RD.d_ls t) - 32768 in
  let l1 := RD.setL_strstart ss (RD.setL_window (RD.win_move 0 32768 ss (RD.ls_window (RD.d_ls t))) (RD.d_ls t)) in
  RD.dst_win_update g used t
  = rt_app (if ss <? RD.ls_insert l1 then RD.setL_insert ss l1 else l1)
           (if RT.ts_matches (RD.d_ts t) <? 2
            then RT.set_matches (RT.ts_matches (RD.d_ts t) + 1) (RD.d_ts t) else RD.d_ts t) t used.
Proof.
  intros g t used Hws H0 H1 H2. cbv zeta. unfold RD.dst_win_update, rt_app. cbv zeta. rewrite Hws.
  replace (used =? 0) with false by (symmetry; apply Z.eqb_neq; exact H0).
  replace (32768 <=? used) with false by (symmetry; apply Z.leb_gt; lia).
  replace (RD.ls_windowsize (RD.d_ls t) - RD.ls_strstart (RD.d_ls t) <=? used) with true
    by (symmetry; apply Z.leb_le; lia).
  reflexivity.
Qed.

Lemma lz_rel_ts : forall s l ts t, lz_rel s (RD.setD_ls l t) -> lz_rel s (RD.setD_ts ts (RD.setD_ls l t)).
Proof. intros s l ts t H. revert H. unfold lz_rel. cbn [RD.d_ls RD.setD_ts RD.setD_ls]. exact (fun H => H). Qed.

(** The shared tail, from any [X] related on its LZ fields to [la] and on the
    rest to [ts]. *)
Lemma pair_app : forall s t pre_out pre_in X la ts used,
  sti s t pre_out pre_in -> 0 < used < 32768 -> used <= DS.cs_next_in (DS.ds_strm s) ->
  lz_rel X (RD.setD_ls la t) -> nl_rel X (RD.setD_ts ts t) pre_out pre_in ->
  DS.ds_pending X = 0 -> DS.ds_pending_out X = 0 -> DS.ds_bi_valid X = 0 -> DS.ds_sym_next X = 0 ->
  DS.ds_strm X = DS.ds_strm s -> arr_len (DS.ds_pending_buf X) = arr_len (DS.ds_pending_buf s) ->
  RD.ls_windowsize la = 65536 -> 0 <= RD.ls_strstart la -> RD.ls_strstart la + used <= 65536 ->
  RD.ls_strstart la + used <= RC.zlen (RD.zs_done (RD.d_strm t)) -> 0 <= RD.ls_insert la <= 32768 ->
  (forall i, 0 <= i < 65536 -> 0 <= RD.ls_window la i < 256) ->
  sti (s5_app X used 32768) (rt_app la ts t used) pre_out pre_in.
Proof.
  intros s t pre_out pre_in X la ts used Si Hu Hun Hlz Hnl Hp Hpo Hbv Hsn Hst Hpb Hwsz Hss0 Hss Hdone Hins Hwin.
  pose proof Si as [Hrel _ _ _ _ Hao Hto Hroom Hc Hrb _ _ _ _ Hinl _ _].
  pose proof Hrel as (_ & _ & _ & _ & _ & Hstr).
  pose proof Hstr as Hst'. unfold strm_rel in Hst'. cbv zeta in Hst'.
  destruct Hst' as (Hni & Hai & Hfit & Hby & _ & Hdn & _).
  assert (Hlast : RD.lastn used (RD.zs_done (RD.d_strm t))
                  = arr_slice (DS.cs_input (DS.ds_strm X)) (DS.cs_next_in (DS.ds_strm X) - used) used).
  { rewrite Hst, Hdn. apply lastn_slice. lia. }
  assert (Hslb : forall x, In x (arr_slice (DS.cs_input (DS.ds_strm X)) (DS.cs_next_in (DS.ds_strm X) - used) used) ->
                 0 <= x < 256).
  { intros x Hx. rewrite Hst in Hx.
    assert (Hk1 : 0 <= DS.cs_next_in (DS.ds_strm s) - used) by lia.
    assert (Hk2 : DS.cs_next_in (DS.ds_strm s) - used + used <= arr_len (DS.cs_input (DS.ds_strm s))) by lia.
    exact (MReadBuf.m_slice_bytes _ _ _ Hby Hk1 Hk2 x Hx). }
  pose proof (lzr_ss _ _ Hlz) as Ess. pose proof (lzr_ins _ _ Hlz) as Eins.
  pose proof (lzr_win _ _ Hlz) as Rw. pose proof (lzr_wlen _ _ Hlz) as Lw.
  cbn [RD.d_ls RD.setD_ls] in Ess, Eins, Rw, Lw.
  assert (Ein : W5.ins_add (DS.ds_insert X) used 32768
                = RD.ls_insert la + RD.zmin used (32768 - RD.ls_insert la)).
  { unfold W5.ins_add, DB.MIN, RD.zmin. rewrite Eins, wrap32_id by lia. reflexivity. }
  assert (Hnv : nonlz_view (s5_app X used 32768) = nonlz_view X) by (unfold s5_app; destruct X; reflexivity).
  apply mkSti.
  - apply m_dst_split. split.
    + unfold rt_app. cbv zeta. apply lz_rel_ts. unfold s5_app.
      apply lz_set_block_start; [|rt_lz; rewrite Ess; reflexivity].
      apply lz_set_insert; [|rt_lz; exact Ein].
      apply lz_set_strstart; [|rt_lz; rewrite Ess; reflexivity].
      apply lz_set_window; [exact Hlz | rewrite arr_len_upd; reflexivity |].
      rewrite Hlast, Ess. apply arr_rel_upd; [exact Rw | exact Lw | exact Hss0 |].
      rewrite arr_slice_length. lia.
    + unfold rt_app. cbv zeta. rewrite <- rt_ls_ts. exact (m_nl_frame _ _ _ _ pre_out pre_in Hnv Hnl).
  - unfold s5_app. s5_lz. exact Hp.
  - unfold s5_app. s5_lz. exact Hpo.
  - unfold s5_app. s5_lz. exact Hbv.
  - unfold s5_app. s5_lz. exact Hsn.
  - unfold s5_app. s5_lz. rewrite Hst. exact Hao.
  - unfold s5_app. s5_lz. rewrite Hst. exact Hto.
  - unfold s5_app. s5_lz. rewrite Hst, Hpb. exact Hroom.
  - unfold rt_app. cbv zeta. rt_lz. exact Hc.
  - unfold rt_app. cbv zeta. eapply rb_ok_frame; [| | | exact Hrb]; reflexivity.
  - unfold rt_app. cbv zeta. rt_lz. exact Hwsz.
  - unfold rt_app. cbv zeta. rt_lz. lia.
  - unfold rt_app. cbv zeta. rt_lz. exact Hss.
  - unfold rt_app. cbv zeta. rt_lz. exact Hdone.
  - unfold rt_app. cbv zeta. rt_lz. exact Hinl.
  - unfold rt_app. cbv zeta. rt_lz. intros i Hi. rewrite Hlast.
    apply win_blit_bytes; [exact Hslb | apply Hwin; exact Hi].
  - unfold rt_app. cbv zeta. rt_lz. unfold RD.zmin.
    destruct (Z.ltb_spec (32768 - RD.ls_insert la) used); lia.
Qed.

(** The slide of the window by [w_size] before the copy. *)
Lemma slide_facts : forall s t pre_out pre_in, sti s t pre_out pre_in ->
  32768 <= RD.ls_strstart (RD.d_ls t) ->
  let X2 := DS.set_window (DS.set_strstart s (DS.ds_strstart s - DS.ds_w_size s))
              (arr_upd (DS.ds_window (DS.set_strstart s (DS.ds_strstart s - DS.ds_w_size s))) 0
                 (arr_slice (DS.ds_window (DS.set_strstart s (DS.ds_strstart s - DS.ds_w_size s)))
                    (DS.ds_w_size s) (DS.ds_strstart s - DS.ds_w_size s))) in
  let ss := RD.ls_strstart (RD.d_ls t) - 32768 in
  let l1 := RD.setL_strstart ss (RD.setL_window (RD.win_move 0 32768 ss (RD.ls_window (RD.d_ls t))) (RD.d_ls t)) in
  let la := if ss <? RD.ls_insert l1 then RD.setL_insert ss l1 else l1 in
  let ts := if RT.ts_matches (RD.d_ts t) <? 2
            then RT.set_matches (RT.ts_matches (RD.d_ts t) + 1) (RD.d_ts t) else RD.d_ts t in
  lz_rel (W5.sl_fix X2) (RD.setD_ls la t) /\ nl_rel (W5.sl_fix X2) (RD.setD_ts ts t) pre_out pre_in
  /\ DS.ds_pending (W5.sl_fix X2) = DS.ds_pending s /\ DS.ds_pending_out (W5.sl_fix X2) = DS.ds_pending_out s
  /\ DS.ds_bi_valid (W5.sl_fix X2) = DS.ds_bi_valid s /\ DS.ds_sym_next (W5.sl_fix X2) = DS.ds_sym_next s
  /\ DS.ds_strm (W5.sl_fix X2) = DS.ds_strm s
  /\ arr_len (DS.ds_pending_buf (W5.sl_fix X2)) = arr_len (DS.ds_pending_buf s).
Proof.
  intros s t pre_out pre_in Si H32. cbv zeta.
  pose proof Si as [Hrel _ _ _ _ _ _ _ Hc _ Hwsz _ Hss _ _ _ _].
  destruct (rel_view _ _ _ _ Hrel Hc)
    as (Ews & _ & _ & Ewsz & Ewl & Ess & _ & _ & _ & _ & _ & Eins & _ & Emt & _).
  pose proof Hrel as (_ & Hlz & _). apply m_dst_split in Hrel as [_ Hnl].
  pose proof (lzr_win _ _ Hlz) as Rw.
  rewrite Ews, Ess.
  match goal with |- context [W5.sl_fix ?X] => remember X as X2 eqn:EX2 end.
  assert (FX : DS.ds_matches X2 = RT.ts_matches (RD.d_ts t)
               /\ DS.ds_strstart X2 = RD.ls_strstart (RD.d_ls t) - 32768
               /\ DS.ds_insert X2 = RD.ls_insert (RD.d_ls t)).
  { subst X2. s5_lz. split; [exact Emt|]. split; [reflexivity|exact Eins]. }
  destruct FX as (FXm & FXs & FXi).
  assert (Hlz2 : lz_rel X2 (RD.setD_ls (RD.setL_strstart (RD.ls_strstart (RD.d_ls t) - 32768)
                    (RD.setL_window (RD.win_move 0 32768 (RD.ls_strstart (RD.d_ls t) - 32768)
                       (RD.ls_window (RD.d_ls t))) (RD.d_ls t))) t)).
  { subst X2. rewrite rt_ss_win.
    apply lz_set_window.
    - apply lz_set_strstart; [rewrite rt_setD_ls_eta; exact Hlz | reflexivity].
    - rewrite arr_len_upd. reflexivity.
    - s5_lz. rt_lz. rewrite Hwsz in Rw |- *.
      apply arr_rel_slide; [exact Rw | rewrite (lzr_wlen _ _ Hlz); exact Hwsz | lia | lia | lia]. }
  assert (Hv2 : nonlz_view X2 = nonlz_view s) by (subst X2; destruct s; reflexivity).
  assert (Hnl2 : nl_rel X2 t pre_out pre_in).
  { rewrite <- (rt_setD_ls_eta t). exact (m_nl_frame _ _ _ _ pre_out pre_in Hv2 Hnl). }
  assert (Fr : DS.ds_pending X2 = DS.ds_pending s /\ DS.ds_pending_out X2 = DS.ds_pending_out s
               /\ DS.ds_bi_valid X2 = DS.ds_bi_valid s /\ DS.ds_sym_next X2 = DS.ds_sym_next s
               /\ DS.ds_strm X2 = DS.ds_strm s
               /\ arr_len (DS.ds_pending_buf X2) = arr_len (DS.ds_pending_buf s))
    by (subst X2; s5_lz; repeat split; reflexivity).
  clear EX2.
  assert (Eli : RD.ls_insert (RD.setL_strstart (RD.ls_strstart (RD.d_ls t) - 32768)
                  (RD.setL_window (RD.win_move 0 32768 (RD.ls_strstart (RD.d_ls t) - 32768)
                                     (RD.ls_window (RD.d_ls t))) (RD.d_ls t)))
                = RD.ls_insert (RD.d_ls t)) by reflexivity.
  rewrite Eli.
  unfold W5.sl_fix. cbv zeta. rewrite FXm.
  destruct (Z.ltb_spec (RT.ts_matches (RD.d_ts t)) 2) as [M|M]; cbv beta iota; s5_lz; rewrite ?FXs, ?FXi;
    destruct (Z.ltb_spec (RD.ls_strstart (RD.d_ls t) - 32768) (RD.ls_insert (RD.d_ls t))) as [I|I];
    cbv beta iota; s5_lz.
  - split; [apply lz_set_insert; [apply lz_rel_matches; exact Hlz2 | reflexivity]|].
    split; [|exact Fr].
    rewrite <- (rt_setD_ls_eta (RD.setD_ts (RT.set_matches (RT.ts_matches (RD.d_ts t) + 1) (RD.d_ts t)) t)).
    refine (m_nl_frame _ _ _ _ pre_out pre_in _ (nl_matches X2 t _ pre_out pre_in Hnl2)).
    destruct X2; reflexivity.
  - split; [apply lz_rel_matches; exact Hlz2|].
    split; [|exact Fr]. exact (nl_matches X2 t _ pre_out pre_in Hnl2).
  - split; [apply lz_set_insert; [exact Hlz2 | reflexivity]|].
    split; [|exact Fr].
    rewrite (rt_setD_ts_eta' t). rewrite <- (rt_setD_ls_eta t).
    refine (m_nl_frame _ _ _ _ pre_out pre_in _ Hnl2). destruct X2; reflexivity.
  - split; [exact Hlz2|]. split; [|exact Fr]. rewrite (rt_setD_ts_eta' t). exact Hnl2.
Qed.

Theorem pair_wupd : forall s t pre_out pre_in used g,
  sti s t pre_out pre_in -> RC.dg_w_size g = 32768 -> 0 <= used <= DS.cs_next_in (DS.ds_strm s) ->
  RD.ls_strstart (RD.d_ls t) + used <= RC.zlen (RD.zs_done (RD.d_strm t)) ->
  sti (W6.st_wupd s used) (RD.dst_win_update g used t) pre_out pre_in.
Proof.
  intros s t pre_out pre_in used g Si Cws Hu Hsd.
  pose proof Si as [Hrel Hp Hpo Hbv Hsn Hao Hto Hroom Hc Hrb Hwsz Hbs Hss Hdone Hinl Hwin Hins].
  destruct (rel_view _ _ _ _ Hrel Hc)
    as (Ews & _ & _ & Ewsz & Ewl & Ess & Ebs & _ & _ & _ & _ & Eins & _ & Emt & _).
  pose proof (zlen_done_rel _ _ _ _ Hrel) as D0.
  assert (Hzp : 0 <= RC.zlen pre_in) by (unfold RC.zlen; lia).
  pose proof Hrel as (_ & Hlz & _ & _ & _ & Hst).
  pose proof Hst as Hst'. unfold strm_rel in Hst'. cbv zeta in Hst'.
  destruct Hst' as (Hni & Hai & Hfit & Hby & _ & Hdn & _).
  pose proof (lzr_win _ _ Hlz) as Rw.
  destruct (Z.eqb_spec used 0) as [U0|U0].
  { subst used. rewrite W7.st_wupd_0. unfold RD.dst_win_update. cbn [Z.eqb]. exact Si. }
  destruct (Z_le_gt_dec 32768 used) as [UA|UB].
  - (* the whole window comes from the input *)
    assert (Hlast : RD.lastn 32768 (RD.zs_done (RD.d_strm t))
                    = arr_slice (DS.cs_input (DS.ds_strm s)) (DS.cs_next_in (DS.ds_strm s) - 32768) 32768)
      by (rewrite Hdn; apply lastn_slice; lia).
    assert (Hslb : forall x, In x (arr_slice (DS.cs_input (DS.ds_strm s)) (DS.cs_next_in (DS.ds_strm s) - 32768) 32768) ->
                   0 <= x < 256).
    { intros x Hx.
      assert (Hk1 : 0 <= DS.cs_next_in (DS.ds_strm s) - 32768) by lia.
      assert (Hk2 : DS.cs_next_in (DS.ds_strm s) - 32768 + 32768 <= arr_len (DS.cs_input (DS.ds_strm s))) by lia.
      exact (MReadBuf.m_slice_bytes _ _ _ Hby Hk1 Hk2 x Hx). }
    unfold RD.dst_win_update. cbv zeta.
    replace (used =? 0) with false by (symmetry; apply Z.eqb_neq; exact U0).
    rewrite Cws. cbv beta iota.
    rewrite (W7.st_wupd_sup s used U0 ltac:(lia)). cbv zeta.
    replace (32768 <=? used) with true by (symmetry; apply Z.leb_le; lia). cbv beta iota.
    autorewrite with s5f_matches. rewrite Ews.
    apply mkSti; [|sti_tail ..].
    + apply (dst_step_m s); [exact Hrel | apply nonlz_lz4 |].
      apply lz_set_block_start; [|reflexivity].
      apply lz_set_insert; [|reflexivity].
      apply lz_set_strstart; [|reflexivity].
      apply lz_set_window.
      * apply lz_rel_matches. rewrite rt_setD_ls_eta. exact Hlz.
      * rewrite arr_len_upd. autorewrite with s5f_matches. reflexivity.
      * rewrite Hlast. apply arr_rel_upd; [exact Rw | exact (lzr_wlen _ _ Hlz) | lia |].
        rewrite arr_slice_length. lia.
    + intros i Hi. rewrite Hlast. apply win_blit_bytes; [exact Hslb | apply Hwin; exact Hi].
  - destruct (Z_le_gt_dec (RD.ls_windowsize (RD.d_ls t) - RD.ls_strstart (RD.d_ls t)) used) as [SL|NS].
    + (* the window slides first *)
      rewrite (s5_app_slide s used U0 Ews ltac:(lia) ltac:(lia)).
      pose proof (rt_app_slide g t used Cws U0 ltac:(lia) SL) as ER. cbv zeta in ER. rewrite ER. clear ER.
      destruct (slide_facts s t pre_out pre_in Si ltac:(lia)) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8).
      rewrite Ews in F1, F2, F3, F4, F5, F6, F7, F8 |- *.
      apply (pair_app s t pre_out pre_in _ _ _ used Si ltac:(lia) ltac:(lia) F1 F2);
        try (rewrite ?F3, ?F4, ?F5, ?F6, ?F7, ?F8; first [assumption | reflexivity]);
        rt_lz; match goal with |- context [if ?c then _ else _] => destruct c end; rt_lz; try lia;
        (intros i Hi; apply win_move_bytes; [exact Hwin | lia | lia | exact Hi]).
    + (* no slide *)
      rewrite (s5_app_noslide s used U0 Ews ltac:(lia) ltac:(lia)).
      rewrite (rt_app_noslide g t used Cws U0 ltac:(lia) ltac:(lia)).
      apply (pair_app s t pre_out pre_in s (RD.d_ls t) (RD.d_ts t) used Si ltac:(lia) ltac:(lia));
        try assumption; try reflexivity; try lia.
      all: first [rewrite rt_setD_ls_eta; exact Hlz
                 | rewrite (rt_setD_ts_eta' t); apply m_dst_split in Hrel as [_ Hn]; exact Hn].
Qed.

(* ------------------------------------------------------------------------- *)
(* 4.  [high_water]                                                          *)
(* ------------------------------------------------------------------------- *)

Theorem pair_hw : forall s t pre_out pre_in, sti s t pre_out pre_in ->
  sti (W5.hw_st s) (RD.dst_highwater t) pre_out pre_in.
Proof.
  intros s t pre_out pre_in Si.
  pose proof Si as [Hrel Hp Hpo Hbv Hsn Hao Hto Hroom Hc Hrb Hwsz Hbs Hss Hdone Hinl Hwin Hins].
  destruct (rel_view _ _ _ _ Hrel Hc) as (_ & _ & _ & _ & _ & Ess & _ & _ & _ & _ & _ & _ & Ehw & _).
  pose proof Hrel as (_ & Hlz & _).
  unfold W5.hw_st, RD.dst_highwater. rewrite Ehw, Ess.
  destruct (Z.ltb_spec (RD.ls_highwater (RD.d_ls t)) (RD.ls_strstart (RD.d_ls t))); [|exact Si].
  apply mkSti; [|sti_tail ..].
  apply (m_lz_step s); [exact Hrel | destruct s; reflexivity |].
  apply lz_set_high_water; [rewrite rt_setD_ls_eta; exact Hlz | reflexivity].
Qed.
