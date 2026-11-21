(** * Bridge.IRelDefl — INTERFACE (part C lead): the deflate state relation, S5 vs RT.

    S5 keeps one 66-field [deflate_state] ([Z/DeflateState.v:224]).  RT keeps
    [DSt] = config [DeflGeom] + status/lastflush/wrap + trees [TSt] (with the
    bit writer [BW]) + window/match [LSt] + stream [ZStrm]
    ([Spec/PngModel/Deflate.v:153]).  The relation is one conjunct per
    cluster, so a pair lemma states and re-establishes only the clusters its
    function touches and frames the rest:

      [geom_rel]  configuration, status, wrap, last_flush
      [lz_rel]    window / prev / head and the match scalars
      [bw_rel]    the pending queue and the bit buffer (with [pend_rel], [room])
      [sym_rel]   the symbol buffer (aliased into pending_buf in S5) and the
                  boundary no-overlap fact
      [tree_rel]  the three dynamic trees, heap, depth, bl_count, lengths
      [strm_rel]  the stream: input array vs unread/consumed lists, output
                  vs cumulative output, totals, adler

    [pre_out]/[pre_in] are RT's output/input from EARLIER calls ([] for
    compress_fuzzer's one-call compress): S5 rebuilds its stream record per
    call, RT's is cumulative.

    Every cluster has a boolean checker (for computed probes and for
    checking a relation on states the two models reach on test inputs) with
    a soundness lemma.

    Ownership: the part C lead.  Groups import this file and do not edit it;
    an interface change goes through the lead (PAIR-GROUPS.md). *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require DeflateState DeflateLz.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base Chunk ZBitsOut Trees Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Module DS := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.DeflateState.
Module RD := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel.Deflate.
Module RT := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel.Trees.
Module RC := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel.Chunk.
Module DL := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.

(* ------------------------------------------------------------------------- *)
(* 1.  Pending queue and bit buffer (moved here from BrBits)                 *)
(* ------------------------------------------------------------------------- *)

(** RT's pending list is S5's slice [[pending_out, pending_out + pending)],
    which lies inside the array.  As in the C, [pending] is a COUNT from
    [pending_out]; [put_byte] writes at [pending_buf[pending]]. *)
Definition pend_rel (s : DS.deflate_state) (out : list Z) : Prop :=
  0 <= DS.ds_pending_out s /\ 0 <= DS.ds_pending s
  /\ DS.ds_pending_out s + DS.ds_pending s <= arr_len (DS.ds_pending_buf s)
  /\ arr_slice (DS.ds_pending_buf s) (DS.ds_pending_out s) (DS.ds_pending s) = out.

Definition bw_rel (s : DS.deflate_state) (b : ZBitsOut.BW) : Prop :=
  pend_rel s (ZBitsOut.bw_out b)
  /\ DS.ds_bi_buf s = ZBitsOut.bw_buf b
  /\ DS.ds_bi_valid s = ZBitsOut.bw_valid b.

(** Room to append [k] bytes: the queue starts at 0 (so [pending] is the
    tail) and the array has [k] more slots. *)
Definition room (s : DS.deflate_state) (k : Z) : Prop :=
  DS.ds_pending_out s = 0 /\ DS.ds_pending s + k <= arr_len (DS.ds_pending_buf s).

(** [bi_flush] needs room only when it emits, i.e. when [bi_valid >= 8]. *)
Definition flush_room (s : DS.deflate_state) : Prop :=
  DS.ds_bi_valid s < 8 \/ room s 2.

(* ------------------------------------------------------------------------- *)
(* 2.  The clusters                                                          *)
(* ------------------------------------------------------------------------- *)

Definition geom_rel (s : DS.deflate_state) (t : RD.DSt) : Prop :=
  let g := RD.d_cfg t in
  DS.ds_level s = RC.dg_level g /\ DS.ds_strategy s = RC.dg_strategy g
  /\ DS.ds_w_bits s = RC.dg_w_bits g /\ DS.ds_w_size s = RC.dg_w_size g
  /\ DS.ds_w_mask s = RC.dg_w_mask g
  /\ DS.ds_hash_bits s = RC.dg_hash_bits g /\ DS.ds_hash_size s = RC.dg_hash_size g
  /\ DS.ds_hash_mask s = RC.dg_hash_mask g /\ DS.ds_hash_shift s = RC.dg_hash_shift g
  /\ DS.ds_lit_bufsize s = RC.dg_lit_bufsize g
  /\ DS.ds_pending_buf_size s = RC.dg_pending_buf_size g
  /\ DS.ds_sym_end s = RC.dg_sym_end g
  /\ DS.ds_good_match s = RC.dg_good_match g /\ DS.ds_max_lazy_match s = RC.dg_max_lazy_match g
  /\ DS.ds_nice_match s = RC.dg_nice_match g /\ DS.ds_max_chain_length s = RC.dg_max_chain_length g
  /\ DS.ds_status s = RD.d_status t /\ DS.ds_wrap s = RD.d_wrap t
  /\ DS.ds_last_flush s = RD.d_lastflush t
  /\ arr_len (DS.ds_pending_buf s) = RC.dg_pending_buf_size g.

(** [match_start]: S5 stores [wrap32 (ms - wsize)] after a window slide
    where RT lets it go negative, so the two agree mod 2^32 only (risk item;
    a pair that USES match_start must show the live value is in range).
    [prev_match] is copied from [match_start] on every deflate_slow trip, so
    it too agrees mod 2^32 only (a level 4-9 input over
    65274 bytes with no 3-byte repeat slides with match_start = 0, giving RT
    -32768 and S5 4294934528). *)
Definition lz_rel (s : DS.deflate_state) (t : RD.DSt) : Prop :=
  let l := RD.d_ls t in
  arr_len (DS.ds_window s) = RD.ls_windowsize l
  /\ arr_len (DS.ds_prev s) = DS.ds_w_size s
  /\ arr_len (DS.ds_head s) = DS.ds_hash_size s
  /\ arr_rel (DS.ds_window s) (RD.ls_window l) 0 (RD.ls_windowsize l)
  /\ arr_rel (DS.ds_prev s) (RD.ls_prev l) 0 (DS.ds_w_size s)
  /\ arr_rel (DS.ds_head s) (RD.ls_head l) 0 (DS.ds_hash_size s)
  /\ DS.ds_window_size s = RD.ls_windowsize l
  /\ DS.ds_ins_h s = RD.ls_insh l /\ DS.ds_block_start s = RD.ls_blockstart l
  /\ DS.ds_match_length s = RD.ls_matchlen l /\ DS.ds_prev_match s = wrap32 (RD.ls_prevmatch l)
  /\ DS.ds_match_available s = RD.ls_matchavail l /\ DS.ds_strstart s = RD.ls_strstart l
  /\ DS.ds_match_start s = wrap32 (RD.ls_matchstart l)
  /\ DS.ds_lookahead s = RD.ls_lookahead l /\ DS.ds_prev_length s = RD.ls_prevlen l
  /\ DS.ds_insert s = RD.ls_insert l /\ DS.ds_high_water s = RD.ls_highwater l.

(** The symbols written so far agree, and at a pair boundary the pending
    queue stays below the symbol area while symbols are live (zlib's
    sym_buf overlay argument; inside [compress_block] the risk group owns
    the stronger running invariant). *)
Definition sym_rel (s : DS.deflate_state) (t : RD.DSt) : Prop :=
  let ts := RD.d_ts t in
  DS.ds_sym_next s = RT.ts_symnext ts
  /\ 0 <= DS.ds_sym_next s <= DS.ds_sym_end s
  /\ (forall i, 0 <= i < DS.ds_sym_next s -> DS.sym_buf_get s i = RT.ts_symbuf ts i)
  /\ DS.ds_lit_bufsize s + DS.ds_sym_end s + 3 <= arr_len (DS.ds_pending_buf s)
  /\ (0 < DS.ds_sym_next s -> DS.ds_pending_out s + DS.ds_pending s <= DS.ds_lit_bufsize s).

Definition tree_rel (s : DS.deflate_state) (t : RD.DSt) : Prop :=
  let ts := RD.d_ts t in
  let L := RT.ts_trees ts RT.TK_L in
  let D := RT.ts_trees ts RT.TK_D in
  let B := RT.ts_trees ts RT.TK_BL in
  arr_rel (DS.ds_dyn_ltree_fc s) (RT.tr_fc L) 0 DS.HEAP_SIZE
  /\ arr_rel (DS.ds_dyn_ltree_dl s) (RT.tr_dl L) 0 DS.HEAP_SIZE
  /\ arr_rel (DS.ds_dyn_dtree_fc s) (RT.tr_fc D) 0 (2 * DS.D_CODES + 1)
  /\ arr_rel (DS.ds_dyn_dtree_dl s) (RT.tr_dl D) 0 (2 * DS.D_CODES + 1)
  /\ arr_rel (DS.ds_bl_tree_fc s) (RT.tr_fc B) 0 (2 * DS.BL_CODES + 1)
  /\ arr_rel (DS.ds_bl_tree_dl s) (RT.tr_dl B) 0 (2 * DS.BL_CODES + 1)
  /\ arr_rel (DS.ds_bl_count s) (RT.ts_blcount ts) 0 (DS.MAX_BITS + 1)
  /\ arr_rel (DS.ds_heap s) (RT.ts_heap ts) 0 DS.HEAP_SIZE
  /\ arr_rel (DS.ds_depth s) (RT.ts_depth ts) 0 DS.HEAP_SIZE
  /\ DS.ds_l_max_code s = RT.ts_maxcode ts RT.TK_L
  /\ DS.ds_d_max_code s = RT.ts_maxcode ts RT.TK_D
  /\ DS.ds_bl_max_code s = RT.ts_maxcode ts RT.TK_BL
  /\ DS.ds_heap_len s = RT.ts_heaplen ts /\ DS.ds_heap_max s = RT.ts_heapmax ts
  /\ DS.ds_opt_len s = RT.ts_optlen ts /\ DS.ds_static_len s = RT.ts_statlen ts
  /\ DS.ds_matches s = RT.ts_matches ts.

(** The stream.  Input: S5's call array from [next_in] on is RT's unread
    list, and its consumed prefix is the tail of RT's consumed list; input
    values are bytes (S5's [read_buf] does not mask, RT's does).  Output:
    RT's cumulative output is [pre_out] followed by this call's S5 output. *)
Definition strm_rel (s : DS.deflate_state) (t : RD.DSt) (pre_out pre_in : list Z) : Prop :=
  let st := DS.ds_strm s in
  let z := RD.d_strm t in
  0 <= DS.cs_next_in st /\ 0 <= DS.cs_avail_in st
  /\ DS.cs_next_in st + DS.cs_avail_in st <= arr_len (DS.cs_input st)
  /\ (forall i, 0 <= i < arr_len (DS.cs_input st) -> 0 <= arr_get (DS.cs_input st) i < 256)
  /\ arr_slice (DS.cs_input st) (DS.cs_next_in st) (DS.cs_avail_in st) = RD.zs_in z
  /\ RD.zs_done z = pre_in ++ arr_slice (DS.cs_input st) 0 (DS.cs_next_in st)
  /\ RD.zs_out z = pre_out ++ DS.cs_output st
  /\ RD.zs_availout z = DS.cs_avail_out st
  /\ RD.zs_totalin z = DS.cs_total_in st /\ RD.zs_totalout z = DS.cs_total_out st
  /\ RD.zs_adler z = DS.cs_adler st /\ RD.zs_datatype z = DS.cs_data_type st.

Definition dst_rel (s : DS.deflate_state) (t : RD.DSt) (pre_out pre_in : list Z) : Prop :=
  geom_rel s t /\ lz_rel s t /\ bw_rel s (RT.ts_bw (RD.d_ts t)) /\ sym_rel s t
  /\ tree_rel s t /\ strm_rel s t pre_out pre_in.

(** The two models' block-state results, one shared map (D and M). *)
Definition bs_of (b : DL.block_state) : RD.BlockState :=
  match b with
  | DL.need_more => RD.NeedMore
  | DL.block_done => RD.BlockDone
  | DL.finish_started => RD.FinishStarted
  | DL.finish_done => RD.FinishDone
  end.

(* ------------------------------------------------------------------------- *)
(* 3.  Checkers and their soundness                                          *)
(* ------------------------------------------------------------------------- *)

Definition zrange_forallb (lo hi : Z) (p : Z -> bool) : bool := zall lo hi p.

Lemma zrange_forallb_sound : forall lo hi p,
  zrange_forallb lo hi p = true -> forall i, lo <= i < hi -> p i = true.
Proof. exact zall_sound. Qed.

Definition pend_relb (s : DS.deflate_state) (out : list Z) : bool :=
  (0 <=? DS.ds_pending_out s) && (0 <=? DS.ds_pending s)
  && (DS.ds_pending_out s + DS.ds_pending s <=? arr_len (DS.ds_pending_buf s))
  && zlist_eqb (arr_slice (DS.ds_pending_buf s) (DS.ds_pending_out s) (DS.ds_pending s)) out.

Definition bw_relb (s : DS.deflate_state) (b : ZBitsOut.BW) : bool :=
  pend_relb s (ZBitsOut.bw_out b) && (DS.ds_bi_buf s =? ZBitsOut.bw_buf b)
  && (DS.ds_bi_valid s =? ZBitsOut.bw_valid b).

Definition geom_relb (s : DS.deflate_state) (t : RD.DSt) : bool :=
  let g := RD.d_cfg t in
  (DS.ds_level s =? RC.dg_level g) && (DS.ds_strategy s =? RC.dg_strategy g)
  && (DS.ds_w_bits s =? RC.dg_w_bits g) && (DS.ds_w_size s =? RC.dg_w_size g)
  && (DS.ds_w_mask s =? RC.dg_w_mask g)
  && (DS.ds_hash_bits s =? RC.dg_hash_bits g) && (DS.ds_hash_size s =? RC.dg_hash_size g)
  && (DS.ds_hash_mask s =? RC.dg_hash_mask g) && (DS.ds_hash_shift s =? RC.dg_hash_shift g)
  && (DS.ds_lit_bufsize s =? RC.dg_lit_bufsize g)
  && (DS.ds_pending_buf_size s =? RC.dg_pending_buf_size g)
  && (DS.ds_sym_end s =? RC.dg_sym_end g)
  && (DS.ds_good_match s =? RC.dg_good_match g) && (DS.ds_max_lazy_match s =? RC.dg_max_lazy_match g)
  && (DS.ds_nice_match s =? RC.dg_nice_match g) && (DS.ds_max_chain_length s =? RC.dg_max_chain_length g)
  && (DS.ds_status s =? RD.d_status t) && (DS.ds_wrap s =? RD.d_wrap t)
  && (DS.ds_last_flush s =? RD.d_lastflush t)
  && (arr_len (DS.ds_pending_buf s) =? RC.dg_pending_buf_size g).

Definition lz_relb (s : DS.deflate_state) (t : RD.DSt) : bool :=
  let l := RD.d_ls t in
  (arr_len (DS.ds_window s) =? RD.ls_windowsize l)
  && (arr_len (DS.ds_prev s) =? DS.ds_w_size s)
  && (arr_len (DS.ds_head s) =? DS.ds_hash_size s)
  && arr_relb (DS.ds_window s) (RD.ls_window l) 0 (RD.ls_windowsize l)
  && arr_relb (DS.ds_prev s) (RD.ls_prev l) 0 (DS.ds_w_size s)
  && arr_relb (DS.ds_head s) (RD.ls_head l) 0 (DS.ds_hash_size s)
  && (DS.ds_window_size s =? RD.ls_windowsize l)
  && (DS.ds_ins_h s =? RD.ls_insh l) && (DS.ds_block_start s =? RD.ls_blockstart l)
  && (DS.ds_match_length s =? RD.ls_matchlen l) && (DS.ds_prev_match s =? wrap32 (RD.ls_prevmatch l))
  && (DS.ds_match_available s =? RD.ls_matchavail l) && (DS.ds_strstart s =? RD.ls_strstart l)
  && (DS.ds_match_start s =? wrap32 (RD.ls_matchstart l))
  && (DS.ds_lookahead s =? RD.ls_lookahead l) && (DS.ds_prev_length s =? RD.ls_prevlen l)
  && (DS.ds_insert s =? RD.ls_insert l) && (DS.ds_high_water s =? RD.ls_highwater l).

Definition sym_relb (s : DS.deflate_state) (t : RD.DSt) : bool :=
  let ts := RD.d_ts t in
  (DS.ds_sym_next s =? RT.ts_symnext ts)
  && (0 <=? DS.ds_sym_next s) && (DS.ds_sym_next s <=? DS.ds_sym_end s)
  && zrange_forallb 0 (DS.ds_sym_next s) (fun i => DS.sym_buf_get s i =? RT.ts_symbuf ts i)
  && (DS.ds_lit_bufsize s + DS.ds_sym_end s + 3 <=? arr_len (DS.ds_pending_buf s))
  && (negb (0 <? DS.ds_sym_next s) || (DS.ds_pending_out s + DS.ds_pending s <=? DS.ds_lit_bufsize s)).

Definition tree_relb (s : DS.deflate_state) (t : RD.DSt) : bool :=
  let ts := RD.d_ts t in
  let L := RT.ts_trees ts RT.TK_L in
  let D := RT.ts_trees ts RT.TK_D in
  let B := RT.ts_trees ts RT.TK_BL in
  arr_relb (DS.ds_dyn_ltree_fc s) (RT.tr_fc L) 0 DS.HEAP_SIZE
  && arr_relb (DS.ds_dyn_ltree_dl s) (RT.tr_dl L) 0 DS.HEAP_SIZE
  && arr_relb (DS.ds_dyn_dtree_fc s) (RT.tr_fc D) 0 (2 * DS.D_CODES + 1)
  && arr_relb (DS.ds_dyn_dtree_dl s) (RT.tr_dl D) 0 (2 * DS.D_CODES + 1)
  && arr_relb (DS.ds_bl_tree_fc s) (RT.tr_fc B) 0 (2 * DS.BL_CODES + 1)
  && arr_relb (DS.ds_bl_tree_dl s) (RT.tr_dl B) 0 (2 * DS.BL_CODES + 1)
  && arr_relb (DS.ds_bl_count s) (RT.ts_blcount ts) 0 (DS.MAX_BITS + 1)
  && arr_relb (DS.ds_heap s) (RT.ts_heap ts) 0 DS.HEAP_SIZE
  && arr_relb (DS.ds_depth s) (RT.ts_depth ts) 0 DS.HEAP_SIZE
  && (DS.ds_l_max_code s =? RT.ts_maxcode ts RT.TK_L)
  && (DS.ds_d_max_code s =? RT.ts_maxcode ts RT.TK_D)
  && (DS.ds_bl_max_code s =? RT.ts_maxcode ts RT.TK_BL)
  && (DS.ds_heap_len s =? RT.ts_heaplen ts) && (DS.ds_heap_max s =? RT.ts_heapmax ts)
  && (DS.ds_opt_len s =? RT.ts_optlen ts) && (DS.ds_static_len s =? RT.ts_statlen ts)
  && (DS.ds_matches s =? RT.ts_matches ts).

Definition strm_relb (s : DS.deflate_state) (t : RD.DSt) (pre_out pre_in : list Z) : bool :=
  let st := DS.ds_strm s in
  let z := RD.d_strm t in
  (0 <=? DS.cs_next_in st) && (0 <=? DS.cs_avail_in st)
  && (DS.cs_next_in st + DS.cs_avail_in st <=? arr_len (DS.cs_input st))
  && zrange_forallb 0 (arr_len (DS.cs_input st))
       (fun i => (0 <=? arr_get (DS.cs_input st) i) && (arr_get (DS.cs_input st) i <? 256))
  && zlist_eqb (arr_slice (DS.cs_input st) (DS.cs_next_in st) (DS.cs_avail_in st)) (RD.zs_in z)
  && zlist_eqb (RD.zs_done z) (pre_in ++ arr_slice (DS.cs_input st) 0 (DS.cs_next_in st))
  && zlist_eqb (RD.zs_out z) (pre_out ++ DS.cs_output st)
  && (RD.zs_availout z =? DS.cs_avail_out st)
  && (RD.zs_totalin z =? DS.cs_total_in st) && (RD.zs_totalout z =? DS.cs_total_out st)
  && (RD.zs_adler z =? DS.cs_adler st) && (RD.zs_datatype z =? DS.cs_data_type st).

Definition dst_relb (s : DS.deflate_state) (t : RD.DSt) (pre_out pre_in : list Z) : bool :=
  geom_relb s t && lz_relb s t && bw_relb s (RT.ts_bw (RD.d_ts t)) && sym_relb s t
  && tree_relb s t && strm_relb s t pre_out pre_in.

(** Split [&&]-chains and decide the comparison atoms. *)
Ltac relb_split H :=
  repeat match type of H with
  | _ && _ = true => apply andb_prop in H; destruct H as [H ?H]
  end.

Ltac relb_atoms :=
  repeat match goal with
  | H : (_ =? _) = true |- _ => apply Z.eqb_eq in H
  | H : (_ <=? _) = true |- _ => apply Z.leb_le in H
  | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
  | H : zlist_eqb _ _ = true |- _ => apply zlist_eqb_eq in H
  | H : arr_relb _ _ _ _ = true |- _ => apply arr_relb_sound in H
  end.

Lemma pend_relb_sound : forall s out, pend_relb s out = true -> pend_rel s out.
Proof.
  intros s out H. unfold pend_relb in H. unfold pend_rel. relb_split H. relb_atoms.
  repeat split; assumption.
Qed.

Lemma bw_relb_sound : forall s b, bw_relb s b = true -> bw_rel s b.
Proof.
  intros s b H. unfold bw_relb in H. relb_split H. apply pend_relb_sound in H. relb_atoms.
  split; [exact H|]. split; assumption.
Qed.

Lemma geom_relb_sound : forall s t, geom_relb s t = true -> geom_rel s t.
Proof.
  intros s t H. unfold geom_relb in H. unfold geom_rel. cbv zeta in H |- *.
  relb_split H. relb_atoms. repeat split; assumption.
Qed.

Lemma lz_relb_sound : forall s t, lz_relb s t = true -> lz_rel s t.
Proof.
  intros s t H. unfold lz_relb in H. unfold lz_rel. cbv zeta in H |- *.
  relb_split H. relb_atoms. repeat split; assumption.
Qed.

Lemma sym_relb_sound : forall s t, sym_relb s t = true -> sym_rel s t.
Proof.
  intros s t H. unfold sym_relb in H. cbv zeta in H. relb_split H.
  match goal with Hf : zrange_forallb _ _ _ = true |- _ => pose proof (zrange_forallb_sound _ _ _ Hf) as Hall; clear Hf end.
  match goal with Hn : negb _ || _ = true |- _ => apply orb_prop in Hn; rename Hn into Hov end.
  relb_atoms.
  unfold sym_rel. cbv zeta. split; [assumption|]. split; [lia|]. split.
  - intros i Hi. apply Z.eqb_eq, Hall, Hi.
  - split; [assumption|]. intros Hpos. destruct Hov as [Hn|Hle].
    + apply negb_true_iff, Z.ltb_ge in Hn. lia.
    + apply Z.leb_le in Hle. exact Hle.
Qed.

Lemma tree_relb_sound : forall s t, tree_relb s t = true -> tree_rel s t.
Proof.
  intros s t H. unfold tree_relb in H. unfold tree_rel. cbv zeta in H |- *.
  relb_split H. relb_atoms. repeat split; assumption.
Qed.

Lemma strm_relb_sound : forall s t pre_out pre_in, strm_relb s t pre_out pre_in = true -> strm_rel s t pre_out pre_in.
Proof.
  intros s t pre_out pre_in H. unfold strm_relb in H. cbv zeta in H. relb_split H.
  match goal with Hf : zrange_forallb _ _ _ = true |- _ => pose proof (zrange_forallb_sound _ _ _ Hf) as Hall; clear Hf end.
  relb_atoms.
  unfold strm_rel. cbv zeta. split; [assumption|]. split; [assumption|]. split; [assumption|]. split.
  - intros i Hi. specialize (Hall i Hi). apply andb_prop in Hall as [Hlo Hhi].
    apply Z.leb_le in Hlo. apply Z.ltb_lt in Hhi. lia.
  - repeat split; assumption.
Qed.

Lemma dst_relb_sound : forall s t pre_out pre_in, dst_relb s t pre_out pre_in = true -> dst_rel s t pre_out pre_in.
Proof.
  intros s t pre_out pre_in H. unfold dst_relb in H. relb_split H.
  unfold dst_rel.
  split; [apply geom_relb_sound; assumption|].
  split; [apply lz_relb_sound; assumption|].
  split; [apply bw_relb_sound; assumption|].
  split; [apply sym_relb_sound; assumption|].
  split; [apply tree_relb_sound; assumption|].
  apply strm_relb_sound; assumption.
Qed.

(** [fp_rel] of [BrFlush] (the bit writer plus the output side of the
    stream) is a projection of [dst_rel]. *)
Lemma dst_rel_bw : forall s t pre_out pre_in, dst_rel s t pre_out pre_in -> bw_rel s (RT.ts_bw (RD.d_ts t)).
Proof. intros s t pre_out pre_in (_ & _ & H & _). exact H. Qed.
