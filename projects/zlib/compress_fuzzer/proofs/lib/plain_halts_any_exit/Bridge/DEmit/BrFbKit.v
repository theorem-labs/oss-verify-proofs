(** * Bridge.DEmit.BrFbKit — the pieces pair D22 ([_tr_flush_block]) is assembled from.

    - [fb_entry_of]: [em_core] and [fb_lz] give S5's flush-entry record
      [fb_entry], so S5's closed safety facts for the flush apply ([E5]'s
      [emit_facts], [X6n], [tree_phase], and [FB_CALL]).
    - RT's [_tr_flush_block] at [level > 0] split the way S5's
      [FlushBlockModel.tr_flush_block_eq] splits S5's: the tree phase, the
      branch choice ([rt_branch]), the block's bits ([rt_emit_bw]) and the
      final [init_block] / [bi_windup] ([rt_fin]); [branch_agree] shows the
      two branch choices agree.
    - Frames: [gl_view] (every field [geom_rel] and [lz_rel] read is one S5
      [keeps], so S5's [fp_keep] carries it across the flush), [nbw] facts.
    - The room for a block body ([cb_all_ok]: S5's [sbs_ok] from the final
      bit position), the dynamic header as [send_all_trees] ([hX13_sat]),
      and the last [bi_windup] with exactly the room S5's [post_ok] gives
      ([br_bi_windup_fin]). *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require DeflateState Trees TreeModel SendModel FlushBlockModel DeflateOverlay
  RefDeflSafeFB RefDeflSafeE1 RefDeflSafeE4 RefDeflSafeE5 RefFlushBlk12 CompressModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base Chunk ZBitsOut Trees Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelDefl S5Fields BrBits.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.Risk Require OvKit.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DEmit Require Import DEmitDefs DTreeDefs BrSendAll BrStored.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DEmit Require BrBuildTree BrBlTree.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Module FB := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeFB.
Module E1 := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeE1.
Module E4 := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeE4.
Module E5 := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeE5.
Module FB12 := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk12.

(* ------------------------------------------------------------------------- *)
(* 1.  S5's flush-entry record from the bridge's side conditions             *)
(* ------------------------------------------------------------------------- *)

Lemma fb_entry_of : forall s t pre_out pre_in last,
  dst_rel s t pre_out pre_in -> em_core s -> fb_lz t -> 0 <= last <= 1 -> FB.fb_entry s last.
Proof.
  intros s t pre_out pre_in last (Hg & Hl & _ & _ & _ & _) H (W1 & W2 & W3 & W4 & W5 & W6 & W7) Hlast.
  unfold geom_rel in Hg. cbv zeta in Hg. destruct Hg as (_ & _ & _ & Hws & _).
  unfold lz_rel in Hl. cbv zeta in Hl.
  destruct Hl as (Lw & _ & _ & Rw & _ & _ & _ & _ & Lbs & _ & _ & _ & Lss & _ & Lla & _).
  destruct H as [Elev Estr Edt Elbs Elbs2 Epbl Esymend Epend Epout Ebiv Ebib Epbb Etout Eaout Eroom
                 Esn Ensym Esyms Ehist Eopt Estat Etl Efc Edl Edep Eblc].
  constructor.
  - exact Hlast.
  - rewrite Lss, Lbs. exact W5.
  - rewrite Lbs. exact W6.
  - rewrite Lss, Hws. lia.
  - rewrite Lla, Hws. lia.
  - rewrite Hws. exact W1.
  - rewrite Lw, Hws. exact W2.
  - intros j Hj. rewrite (Rw j) by lia. apply W7. lia.
  - exact Elev.
  - exact Estr.
  - exact Edt.
  - exact Elbs.
  - exact Epbl.
  - exact Esymend.
  - exact Epend.
  - exact Epout.
  - exact Ebiv.
  - exact Ebib.
  - exact Epbb.
  - lia.
  - exact Eaout.
  - exact Esn.
  - exact Ensym.
  - exact Esyms.
  - exact Ehist.
  - exact Eopt.
  - exact Estat.
  - exact Etl.
  - exact Efc.
  - exact Edl.
  - exact Edep.
  - exact Eblc.
  - exact Elbs2.
Qed.

(* ------------------------------------------------------------------------- *)
(* 2.  RT's [_tr_flush_block] split into phases                              *)
(* ------------------------------------------------------------------------- *)

(** The branch: 2 stored, 0 static, 1 dynamic (S5's [tfb_branch] numbering). *)
Definition rt_branch (buf : option (list Z)) (sl strategy : Z) (s2 : RT.TSt) : Z :=
  let static_lenb := RT.u64 (RT.ts_statlen s2 + 3 + 7) / 8 in
  let opt_lenb0 := RT.u64 (RT.ts_optlen s2 + 3 + 7) / 8 in
  let opt_lenb := if (Z.leb static_lenb opt_lenb0) || (Z.eqb strategy RT.Z_FIXED) then static_lenb else opt_lenb0 in
  if (match buf with Some _ => true | None => false end) && (sl + 4 <=? opt_lenb) then 2
  else if static_lenb =? opt_lenb then 0 else 1.

(** The bit writer after the block. *)
Definition rt_emit_bw (d : Z) (buf : option (list Z)) (sl last mbi : Z) (s2 : RT.TSt) : ZBitsOut.BW :=
  if d =? 2 then
    match buf with Some dat => RT.ts_bw (RT.tr_stored_block dat sl last s2) | None => RT.ts_bw s2 end
  else if d =? 0 then
    RT.compress_block (RT.ts_symbuf s2) (RT.ts_symnext s2) RT.static_ltree RT.static_dtree
      (ZBitsOut.bw_send_bits (Z.shiftl RT.STATIC_TREES 1 + last) 3 (RT.ts_bw s2))
  else
    RT.compress_block (RT.ts_symbuf s2) (RT.ts_symnext s2) (RT.ts_trees s2 RT.TK_L) (RT.ts_trees s2 RT.TK_D)
      (RT.send_all_trees (RT.ts_maxcode s2 RT.TK_L + 1) (RT.ts_maxcode s2 RT.TK_D + 1) (mbi + 1)
         (RT.set_bw (ZBitsOut.bw_send_bits (Z.shiftl RT.DYN_TREES 1 + last) 3 (RT.ts_bw s2)) s2)).

Definition rt_fin (last : Z) (s4 : RT.TSt) : RT.TSt :=
  let s5 := RT.init_block s4 in
  if Z.eqb last 0 then s5 else RT.set_bw (ZBitsOut.bw_windup (RT.ts_bw s5)) s5.

Lemma rt_fb_split : forall buf sl last level strategy dtype ts, 0 < level ->
  RT.tr_flush_block buf sl last level strategy dtype ts =
  (if Z.eqb dtype RT.Z_UNKNOWN then RT.detect_data_type (RT.ts_trees ts RT.TK_L) else dtype,
   let p := RT.build_bl_tree (RT.build_tree RT.TK_D (RT.build_tree RT.TK_L ts)) in
   rt_fin last (RT.set_bw (rt_emit_bw (rt_branch buf sl strategy (snd p)) buf sl last (fst p) (snd p)) (snd p))).
Proof.
  intros buf sl last level strategy dtype ts Hl.
  unfold RT.tr_flush_block. replace (0 <? level) with true by (symmetry; apply Z.ltb_lt; exact Hl).
  cbv beta iota. unfold rt_branch. cbv zeta.
  (* opaque from here on: no unification step may evaluate the tree phase *)
  generalize (RT.build_bl_tree (RT.build_tree RT.TK_D (RT.build_tree RT.TK_L ts))) as p. intros p.
  generalize (RT.u64 (RT.ts_statlen (snd p) + 3 + 7) / 8) as A. intros A.
  generalize (RT.u64 (RT.ts_optlen (snd p) + 3 + 7) / 8) as B. intros B.
  generalize (if (A <=? B) || (strategy =? RT.Z_FIXED) then A else B) as O. intros O.
  destruct buf as [dat|]; [destruct (sl + 4 <=? O)|]; cbn [andb]; [reflexivity| |]; destruct (A =? O); reflexivity.
Qed.

(** The two branch choices agree. *)
Lemma branch_agree : forall X6 s2 (sbuf : option Z) (rbuf : option (list Z)) len,
  trel X6 s2 -> 0 <= DS.ds_opt_len X6 < 2 ^ 40 -> 0 <= DS.ds_static_len X6 < 2 ^ 40 -> 0 <= len < 2 ^ 40 ->
  FBM.is_some sbuf = match rbuf with Some _ => true | None => false end ->
  FBM.tfb_branch X6 sbuf len = rt_branch rbuf len (DS.ds_strategy X6) s2.
Proof.
  intros X6 s2 sbuf rbuf len HT HO HS HL HB.
  pose proof HT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & EO & ES & _).
  unfold FBM.tfb_branch, rt_branch. cbv zeta.
  rewrite <- EO, <- ES.
  rewrite !wrap64_id by lia. rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  unfold RT.u64. rewrite !(Z.mod_small (_ + 3 + 7)) by lia.
  change RT.Z_FIXED with Z_FIXED.
  rewrite HB, andb_comm. reflexivity.
Qed.

(** RT's tree phase leaves the symbols and the bit writer alone. *)
Lemma rt_bbl_frame : forall ts,
  RT.ts_symbuf (snd (RT.build_bl_tree ts)) = RT.ts_symbuf ts
  /\ RT.ts_symnext (snd (RT.build_bl_tree ts)) = RT.ts_symnext ts
  /\ RT.ts_bw (snd (RT.build_bl_tree ts)) = RT.ts_bw ts.
Proof.
  intros ts. rewrite BrBlTree.rt_bbl_eq. cbv zeta. cbn [snd].
  set (t2 := scan_ts RT.TK_D (RT.ts_maxcode (scan_ts RT.TK_L (RT.ts_maxcode ts RT.TK_L) ts) RT.TK_D)
                (scan_ts RT.TK_L (RT.ts_maxcode ts RT.TK_L) ts)).
  destruct (BrBuildTree.rt_build_tree_frame RT.TK_BL t2) as (F1 & F2 & _ & F4).
  cbv zeta in F1, F2, F4.
  change (RT.ts_symbuf (RT.set_optlen ?x ?t)) with (RT.ts_symbuf t).
  change (RT.ts_symnext (RT.set_optlen ?x ?t)) with (RT.ts_symnext t).
  change (RT.ts_bw (RT.set_optlen ?x ?t)) with (RT.ts_bw t).
  rewrite F1, F2, F4. split; [reflexivity | split; reflexivity].
Qed.

(* ------------------------------------------------------------------------- *)
(* 3.  Frames                                                                *)
(* ------------------------------------------------------------------------- *)

(** Every S5 field [geom_rel] and [lz_rel] read (except the array length of
    [pending_buf]). *)
Definition gl_view (s : DS.deflate_state) :=
  (DS.ds_level s, DS.ds_strategy s, DS.ds_w_bits s, DS.ds_w_size s, DS.ds_w_mask s,
   DS.ds_hash_bits s, DS.ds_hash_size s, DS.ds_hash_mask s, DS.ds_hash_shift s, DS.ds_lit_bufsize s,
   (DS.ds_pending_buf_size s, DS.ds_sym_end s, DS.ds_good_match s, DS.ds_max_lazy_match s, DS.ds_nice_match s,
    DS.ds_max_chain_length s, DS.ds_status s, DS.ds_wrap s, DS.ds_last_flush s),
   (DS.ds_window s, DS.ds_prev s, DS.ds_head s, DS.ds_window_size s, DS.ds_ins_h s, DS.ds_block_start s,
    DS.ds_match_length s, DS.ds_prev_match s, DS.ds_match_available s, DS.ds_strstart s),
   (DS.ds_match_start s, DS.ds_lookahead s, DS.ds_prev_length s, DS.ds_insert s, DS.ds_high_water s)).

Lemma keeps_gl : FBM.keeps gl_view true true.
Proof.
  constructor; intros; try match goal with t : DS.tree_id |- _ => destruct t end;
    match goal with s : DS.deflate_state |- _ => destruct s; reflexivity end.
Qed.

Lemma gl_X0 : forall s, gl_view (FBM.tfb_X0 s) = gl_view s.
Proof. intros s. unfold FBM.tfb_X0. destruct (_ && _); [destruct s; reflexivity | reflexivity]. Qed.

Lemma gl_rel : forall s s' t t', gl_view s' = gl_view s ->
  arr_len (DS.ds_pending_buf s') = arr_len (DS.ds_pending_buf s) ->
  RD.d_cfg t' = RD.d_cfg t -> RD.d_status t' = RD.d_status t -> RD.d_wrap t' = RD.d_wrap t ->
  RD.d_lastflush t' = RD.d_lastflush t -> RD.d_ls t' = RD.d_ls t ->
  geom_rel s t -> lz_rel s t -> geom_rel s' t' /\ lz_rel s' t'.
Proof.
  intros s s' t t' E L C1 C2 C3 C4 C5 G Z. unfold gl_view in E. injection E. intros.
  unfold geom_rel, lz_rel in *. cbv zeta in *. rewrite C1, C2, C3, C4, C5, L.
  repeat match goal with H : ?f s' = ?f s |- _ => rewrite H; clear H end.
  split; assumption.
Qed.

Lemma nbw_set_strm : forall s c, nbw (DS.set_strm s c) = nbw s.
Proof. intros s c. unfold nbw. autorewrite with s5f_strm. reflexivity. Qed.

Lemma nbw_X0 : forall s, nbw (FBM.tfb_X0 s) = nbw s.
Proof. intros s. unfold FBM.tfb_X0. destruct (_ && _); [apply nbw_set_strm | reflexivity]. Qed.

Lemma nbw_dyn : forall a b, nbw a = nbw b ->
  DS.ds_dyn_ltree_fc a = DS.ds_dyn_ltree_fc b /\ DS.ds_dyn_ltree_dl a = DS.ds_dyn_ltree_dl b
  /\ DS.ds_dyn_dtree_fc a = DS.ds_dyn_dtree_fc b /\ DS.ds_dyn_dtree_dl a = DS.ds_dyn_dtree_dl b
  /\ DS.ds_l_max_code a = DS.ds_l_max_code b /\ DS.ds_d_max_code a = DS.ds_d_max_code b.
Proof. intros a b E. unfold nbw in E. injection E. intros. repeat split; assumption. Qed.

(* ------------------------------------------------------------------------- *)
(* 4.  Room for a block body                                                 *)
(* ------------------------------------------------------------------------- *)

Lemma cb_from_lens : forall s0 lfc ldl dfc ddl n j,
  (forall k, j <= k < j + Z.of_nat n -> 0 <= arr_get ldl (DO.sym_lcode s0 k) <= 15) ->
  (forall k, j <= k < j + Z.of_nat n -> DO.sym_isdist s0 k = true -> 0 <= arr_get ddl (DO.sym_dcode s0 k) <= 15) ->
  Forall (fun c => 0 <= snd c <= 16) (OvKit.cb_calls_from s0 lfc ldl dfc ddl j n).
Proof.
  induction n as [|n IH]; intros j HL HD; cbn [OvKit.cb_calls_from]; [constructor|].
  apply Forall_app. split.
  - apply E4.sym_calls_lens; [apply HL; lia | intros; apply HD; [lia | assumption]].
  - apply IH; intros k Hk; [apply HL; lia | intros; apply HD; [lia | assumption]].
Qed.

(** S5's room for the whole body from its final bit position. *)
Lemma cb_all_ok : forall y s0 lfc ldl dfc ddl N PBL,
  0 <= N -> 0 <= DS.ds_bi_valid y <= 16 ->
  (forall j, 0 <= j < N -> 0 <= arr_get ldl (DO.sym_lcode s0 j) <= 15) ->
  (forall j, 0 <= j < N -> DO.sym_isdist s0 j = true -> 0 <= arr_get ddl (DO.sym_dcode s0 j) <= 15) ->
  0 <= arr_get ldl DS.END_BLOCK <= 16 ->
  DO.ov_W (SM.sbs_run y (OvKit.cb_all s0 lfc ldl dfc ddl N)) <= 8 * PBL ->
  SM.sbs_ok PBL y (OvKit.cb_all s0 lfc ldl dfc ddl N).
Proof.
  intros y s0 lfc ldl dfc ddl N PBL HN Hb HL HD HE HW.
  apply E1.sbs_ok_of_bound; [exact Hb | | rewrite <- E1.sbs_W; exact HW].
  unfold OvKit.cb_all, OvKit.cb_calls. apply Forall_app. split.
  - apply cb_from_lens; intros k Hk; [apply HL; lia | intros; apply HD; [lia | assumption]].
  - repeat constructor; cbn [snd]; lia.
Qed.

(* ------------------------------------------------------------------------- *)
(* 5.  The dynamic header as [send_all_trees]                                *)
(* ------------------------------------------------------------------------- *)

Lemma hd_sat : forall X6 last mb,
  FB12.hd_calls last X6 mb
  = (4 + last, 3) :: FBM.sat_calls (DT.send_bits X6 (4 + last) 3)
                       (DS.ds_l_max_code X6 + 1) (DS.ds_d_max_code X6 + 1) (mb + 1).
Proof.
  intros X6 last mb. unfold FB12.hd_calls, FBM.sat_calls. cbn [app].
  replace (DS.ds_l_max_code X6 + 1 - 257) with (DS.ds_l_max_code X6 - 256) by lia.
  replace (DS.ds_d_max_code X6 + 1 - 1) with (DS.ds_d_max_code X6) by lia.
  replace (mb + 1 - 4) with (mb - 3) by lia.
  rewrite (FBM.bl_calls_ext X6 (DT.send_bits X6 (4 + last) 3)) by (intros; apply Len_nbw; apply nbw_send_bits).
  reflexivity.
Qed.

Lemma hX13_sat : forall X6 last mb, 0 <= mb <= 18 ->
  E5.hX13 X6 last mb
  = DT.send_all_trees (DT.send_bits X6 (4 + last) 3)
      (DS.ds_l_max_code X6 + 1) (DS.ds_d_max_code X6 + 1) (mb + 1).
Proof.
  intros X6 last mb Hmb. rewrite FBM.send_all_trees_eq by lia.
  unfold E5.hX13, E5.hX12, E5.hX11. rewrite hd_sat. cbn [SM.sbs_run].
  replace (DS.ds_l_max_code X6 + 1 - 1) with (DS.ds_l_max_code X6) by lia.
  replace (DS.ds_d_max_code X6 + 1 - 1) with (DS.ds_d_max_code X6) by lia.
  reflexivity.
Qed.

(** The branches of [tfb_emit] and [rt_emit_bw] as equations over abstract
    states.  Proofs that hold S5's concrete tree-phase state rewrite with
    these: a [change] or [cbn] there may try to convert a subterm such as
    [ds_l_max_code (ov_X6 s)] against a literal and evaluate the whole tree
    phase. *)
Lemma tfb_emit_0 : forall X6 mb buf len last,
  FBM.tfb_emit 0 X6 mb buf len last
  = DT.compress_block (DT.send_bits X6 (Z.shiftl DS.STATIC_TREES 1 + last) 3)
      DS.static_ltree_fc DS.static_ltree_dl DS.static_dtree_fc DS.static_dtree_dl.
Proof. reflexivity. Qed.

Lemma tfb_emit_2 : forall X6 mb buf len last,
  FBM.tfb_emit 2 X6 mb buf len last = DT.tr_stored_block X6 buf len last.
Proof. reflexivity. Qed.

Lemma rt_emit_bw_0 : forall buf sl last mbi s2,
  rt_emit_bw 0 buf sl last mbi s2
  = RT.compress_block (RT.ts_symbuf s2) (RT.ts_symnext s2) RT.static_ltree RT.static_dtree
      (ZBitsOut.bw_send_bits (Z.shiftl DS.STATIC_TREES 1 + last) 3 (RT.ts_bw s2)).
Proof. reflexivity. Qed.

Lemma rt_emit_bw_1 : forall buf sl last mbi s2,
  rt_emit_bw 1 buf sl last mbi s2
  = RT.compress_block (RT.ts_symbuf s2) (RT.ts_symnext s2) (RT.ts_trees s2 RT.TK_L) (RT.ts_trees s2 RT.TK_D)
      (RT.send_all_trees (RT.ts_maxcode s2 RT.TK_L + 1) (RT.ts_maxcode s2 RT.TK_D + 1) (mbi + 1)
         (RT.set_bw (ZBitsOut.bw_send_bits (4 + last) 3 (RT.ts_bw s2)) s2)).
Proof. reflexivity. Qed.

Lemma rt_emit_bw_2 : forall (b : bool) dat sl last mbi s2, b = true ->
  rt_emit_bw 2 (if b then Some dat else None) sl last mbi s2 = RT.ts_bw (RT.tr_stored_block dat sl last s2).
Proof. intros b dat sl last mbi s2 ->. reflexivity. Qed.

Lemma sbs_run_cons : forall s v l r, SM.sbs_run s ((v, l) :: r) = SM.sbs_run (DT.send_bits s v l) r.
Proof. reflexivity. Qed.

Lemma sbs_ok_cons_inv : forall PBL s v l r,
  SM.sbs_ok PBL s ((v, l) :: r) -> SM.sbs_ok PBL (DT.send_bits s v l) r.
Proof. intros PBL s v l r H. exact (proj2 (proj2 H)). Qed.

(* ------------------------------------------------------------------------- *)
(* 6.  The last [bi_windup]                                                  *)
(* ------------------------------------------------------------------------- *)

(** Room only for the bytes it writes (S5's [post_ok] gives exactly this). *)
Lemma br_bi_windup_fin : forall s b, bw_rel s b -> DS.ds_pending_out s = 0 ->
  DS.ds_pending (DT.bi_windup s) <= arr_len (DS.ds_pending_buf s) ->
  bw_rel (DT.bi_windup s) (ZBitsOut.bw_windup b).
Proof.
  intros s b (Hp & Hb & Hv) Hpo Hfin.
  unfold DT.bi_windup in *. unfold ZBitsOut.bw_windup. cbv zeta in *. rewrite <- Hv, <- Hb.
  autorewrite with s5f_bi_valid s5f_bi_buf in Hfin.
  unfold bw_rel. cbn [ZBitsOut.bw_out ZBitsOut.bw_buf ZBitsOut.bw_valid].
  revert Hfin. destruct (Z.ltb 8 (DS.ds_bi_valid s)); intros Hfin.
  - rewrite pending_put_short in Hfin.
    destruct (sim_put_short s _ (DS.ds_bi_buf s) Hp ltac:(split; lia)) as (Hp2 & _).
    rewrite ZBitsOut.bw_put_short_out. split; [exact Hp2|]. split; reflexivity.
  - revert Hfin. destruct (Z.ltb 0 (DS.ds_bi_valid s)); intros Hfin.
    + rewrite pending_put_byte in Hfin.
      destruct (sim_put_byte s _ (DS.ds_bi_buf s) Hp ltac:(split; lia)) as (Hp2 & _).
      cbn [ZBitsOut.bw_put_byte ZBitsOut.bw_out]. split; [exact Hp2|]. split; reflexivity.
    + split; [exact Hp|]. split; reflexivity.
Qed.

(** [init_block] leaves the bit writer alone. *)
Lemma bw_rel_init_block : forall s b, bw_rel s b -> bw_rel (DT.init_block s) b
  /\ DS.ds_pending_out (DT.init_block s) = DS.ds_pending_out s
  /\ arr_len (DS.ds_pending_buf (DT.init_block s)) = arr_len (DS.ds_pending_buf s)
  /\ DS.ds_pending (DT.init_block s) = DS.ds_pending s.
Proof.
  intros s b Hb. pose proof (E5.init_block_facts s) as IB.
  unfold bw_rel, pend_rel in *.
  rewrite (E5.ib_pb _ _ IB), (E5.ib_pend _ _ IB), (E5.ib_po _ _ IB), (E5.ib_bb _ _ IB), (E5.ib_bv _ _ IB).
  split; [exact Hb | split; [reflexivity | split; reflexivity]].
Qed.

Print Assumptions branch_agree.
Print Assumptions rt_fb_split.
Print Assumptions hX13_sat.
Print Assumptions br_bi_windup_fin.
