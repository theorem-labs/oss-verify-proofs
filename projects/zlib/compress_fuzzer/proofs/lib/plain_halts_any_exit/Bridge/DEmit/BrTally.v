(** * Bridge.DEmit.BrTally — pair D21 of PAIRS.md: [_tr_tally_lit] / [_tr_tally_dist], S5 vs RT.

    Both models append one 3-byte symbol and bump one or two frequencies.
    S5 writes the symbol into [pending_buf] at [lit_bufsize + sym_next] (the
    C's [sym_buf] overlay); RT writes it into its separate [ts_symbuf].  The
    relation half ([tally_rel]) is one generic lemma: the queue is empty, so
    the three bytes cannot land inside it, and the two frequency updates are
    the same write on both sides ([arr_rel_set]).  The invariant half
    ([em_core] back) reuses S5's own tally lemmas
    ([RefDeflSafeFBT.BQ_tally_lit] / [BQ_tally_dist]), which already show
    that the symbol histogram and the frequencies stay in step.

    S5's state updates are handled by the projection-over-setter databases
    of [Bridge/S5Fields.v]; the one record equality per tally
    ([tally_lit_shape], [tally_dist_shape]) is proved by destructing the
    state, never by unfolding a setter in a goal. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require DeflateState Trees TreeModel DeflateOverlay CompressModel
  RefDeflSafeZ RefDeflSafeFBT TreesTab.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base Chunk ZBitsOut Trees Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelDefl S5Fields.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.DEmit Require Import DEmitDefs.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require BrBits.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Module FBT := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeFBT.
Module TT := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.TreesTab.

(* ------------------------------------------------------------------------- *)
(* 1.  The static tables agree                                               *)
(* ------------------------------------------------------------------------- *)

Lemma arr_of_list_zlist : forall l i, 0 <= i -> arr_get (arr_of_list l) i = Base.zlist l i.
Proof.
  intros l i Hi. unfold arr_of_list, parr_of_list, Base.zlist.
  rewrite (arr_get_upd l (arr_make (zlength l) 0) 0 i 0). unfold arr_inb. rewrite arr_len_make.
  destruct (Z.leb_spec 0 i); [|lia].
  destruct (Z.ltb_spec i (0 + zlength l)); destruct (Z.ltb_spec i (zlength l)); cbn [andb]; try lia.
  - rewrite Z.sub_0_r. reflexivity.
  - rewrite arr_get_make, nth_overflow; [reflexivity|]. unfold zlength in *. lia.
Qed.

Lemma length_code_agree : forall i, 0 <= i -> arr_get DS.length_code_a i = RT.length_code i.
Proof. intros i Hi. unfold DS.length_code_a, RT.length_code. rewrite arr_of_list_zlist by exact Hi. reflexivity. Qed.

Lemma d_code_agree : forall x, 0 <= x -> DS.d_code x = RT.d_code x.
Proof.
  intros x Hx. unfold DS.d_code, RT.d_code, DS.dist_code_a, RT.dist_code.
  destruct (x <? 256).
  - rewrite arr_of_list_zlist by exact Hx. reflexivity.
  - rewrite arr_of_list_zlist by (pose proof (Z.shiftr_nonneg x 7); lia). reflexivity.
Qed.

(* ------------------------------------------------------------------------- *)
(* 2.  The two S5 tallies as one setter chain each                           *)
(* ------------------------------------------------------------------------- *)

(** The pending buffer after the three symbol-byte stores at
    [lit_bufsize + sym_next]. *)
Definition sym3 (s : DS.deflate_state) (v0 v1 v2 : Z) : arr :=
  let lbs := DS.ds_lit_bufsize s in let sn := DS.ds_sym_next s in
  arr_set (arr_set (arr_set (DS.ds_pending_buf s) (lbs + sn) (wrap8 v0)) (lbs + (sn + 1)) (wrap8 v1))
          (lbs + (sn + 1 + 1)) (wrap8 v2).

(** One frequency bump, as S5's [set_Freq] stores it. *)
Definition bump (a : arr) (i : Z) : arr := arr_set a i (wrap16 (arr_get a i + 1)).

Definition tally_state (s : DS.deflate_state) (pb lfc dfc : arr) : DS.deflate_state :=
  DS.set_dyn_dtree_fc
    (DS.set_dyn_ltree_fc (DS.set_sym_next (DS.set_pending_buf s pb) (DS.ds_sym_next s + 1 + 1 + 1)) lfc) dfc.

Lemma tally_lit_shape : forall s c,
  fst (DT.tr_tally_lit s c)
  = tally_state s (sym3 s 0 0 (wrap8 c)) (bump (DS.ds_dyn_ltree_fc s) (wrap8 c)) (DS.ds_dyn_dtree_fc s)
  /\ snd (DT.tr_tally_lit s c) = (DS.ds_sym_next s + 1 + 1 + 1 =? DS.ds_sym_end s).
Proof. intros [] c. split; reflexivity. Qed.

Definition dist_lcode (length : Z) : Z := arr_get DS.length_code_a (wrap8 length) + DS.LITERALS + 1.
Definition dist_dcode (distance : Z) : Z := DS.d_code (wrap16 (wrap16 distance - 1)).

Lemma tally_dist_shape : forall s distance length,
  fst (DT.tr_tally_dist s distance length)
  = tally_state s (sym3 s (wrap16 distance) (Z.shiftr (wrap16 distance) 8) (wrap8 length))
      (bump (DS.ds_dyn_ltree_fc s) (dist_lcode length)) (bump (DS.ds_dyn_dtree_fc s) (dist_dcode distance))
  /\ snd (DT.tr_tally_dist s distance length) = (DS.ds_sym_next s + 1 + 1 + 1 =? DS.ds_sym_end s).
Proof. intros [] distance length. split; reflexivity. Qed.

Ltac tally_fields :=
  unfold tally_state; autorewrite with s5f_dyn_dtree_fc s5f_dyn_ltree_fc s5f_sym_next s5f_pending_buf.

(* ------------------------------------------------------------------------- *)
(* 3.  The relation half, once for both tallies                              *)
(* ------------------------------------------------------------------------- *)

Lemma slice_len0 : forall (a : arr) o, arr_slice a o 0 = [].
Proof. reflexivity. Qed.

Lemma tally_rel : forall s t pre_out pre_in pb lfc dfc (ts' : RT.TSt),
  dst_rel s t pre_out pre_in ->
  DS.ds_pending s = 0 -> DS.ds_pending_out s = 0 -> 0 <= DS.ds_lit_bufsize s ->
  DS.ds_sym_next s + 3 <= DS.ds_sym_end s ->
  arr_len pb = arr_len (DS.ds_pending_buf s) ->
  (forall i, 0 <= i < DS.ds_sym_next s + 3 -> arr_get pb (DS.ds_lit_bufsize s + i) = RT.ts_symbuf ts' i) ->
  RT.ts_symnext ts' = RT.ts_symnext (RD.d_ts t) + 3 ->
  arr_rel lfc (RT.tr_fc (RT.ts_trees ts' RT.TK_L)) 0 DS.HEAP_SIZE ->
  arr_rel dfc (RT.tr_fc (RT.ts_trees ts' RT.TK_D)) 0 (2 * DS.D_CODES + 1) ->
  RT.tr_dl (RT.ts_trees ts' RT.TK_L) = RT.tr_dl (RT.ts_trees (RD.d_ts t) RT.TK_L) ->
  RT.tr_dl (RT.ts_trees ts' RT.TK_D) = RT.tr_dl (RT.ts_trees (RD.d_ts t) RT.TK_D) ->
  RT.ts_trees ts' RT.TK_BL = RT.ts_trees (RD.d_ts t) RT.TK_BL ->
  RT.ts_maxcode ts' = RT.ts_maxcode (RD.d_ts t) -> RT.ts_blcount ts' = RT.ts_blcount (RD.d_ts t) ->
  RT.ts_heap ts' = RT.ts_heap (RD.d_ts t) -> RT.ts_heaplen ts' = RT.ts_heaplen (RD.d_ts t) ->
  RT.ts_heapmax ts' = RT.ts_heapmax (RD.d_ts t) -> RT.ts_depth ts' = RT.ts_depth (RD.d_ts t) ->
  RT.ts_optlen ts' = RT.ts_optlen (RD.d_ts t) -> RT.ts_statlen ts' = RT.ts_statlen (RD.d_ts t) ->
  RT.ts_matches ts' = RT.ts_matches (RD.d_ts t) -> RT.ts_bw ts' = RT.ts_bw (RD.d_ts t) ->
  dst_rel (tally_state s pb lfc dfc) (RD.setD_ts ts' t) pre_out pre_in.
Proof.
  intros s t pre_out pre_in pb lfc dfc ts' (Hg & Hl & Hb & Hs & Ht & Hm) Hp Hpo Hlbs Hroom Hlen Hsym Hsn
    HL HD HLd HDd HB Hmc Hblc Hhp Hhl Hhm Hdp Hol Hsl Hmt Hbw.
  unfold dst_rel. cbn [RD.d_ts RD.setD_ts]. split; [|split; [|split; [|split; [|split]]]].
  - unfold geom_rel in *. cbv zeta in *. tally_fields. cbn [RD.d_cfg RD.d_status RD.d_wrap RD.d_lastflush RD.setD_ts].
    rewrite Hlen. exact Hg.
  - unfold lz_rel in *. cbv zeta in *. tally_fields. cbn [RD.d_ls RD.setD_ts]. exact Hl.
  - rewrite Hbw. destruct Hb as ((Hpo0 & Hp0 & Hin & Hsl0) & Hbb & Hbv).
    unfold bw_rel, pend_rel. tally_fields. rewrite Hlen, Hp, Hpo in *. rewrite slice_len0 in *.
    split; [split; [lia|split; [lia|split; [lia|exact Hsl0]]]|split; assumption].
  - destruct Hs as (Hsn0 & Hsr & Hsy & Hsz & Hov).
    unfold sym_rel. cbv zeta. tally_fields. cbn [RD.d_ts RD.setD_ts]. rewrite Hlen.
    split; [rewrite Hsn, Hsn0; lia|]. split; [lia|]. split.
    + intros i Hi. unfold DS.sym_buf_get. tally_fields. apply Hsym. lia.
    + split; [exact Hsz|]. intros _. rewrite Hp, Hpo. lia.
  - unfold tree_rel in *. cbv zeta in *. tally_fields. cbn [RD.d_ts RD.setD_ts].
    rewrite HLd, HDd, HB, Hmc, Hblc, Hhp, Hhl, Hhm, Hdp, Hol, Hsl, Hmt.
    destruct Ht as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9 & T10).
    split; [exact HL|]. split; [exact T2|]. split; [exact HD|]. split; [exact T4|]. exact (conj T5 (conj T6 (conj T7 (conj T8 (conj T9 T10))))).
  - unfold strm_rel in *. cbv zeta in *. tally_fields. cbn [RD.d_strm RD.setD_ts]. exact Hm.
Qed.

(* ------------------------------------------------------------------------- *)
(* 4.  The RT tallies, field by field                                        *)
(* ------------------------------------------------------------------------- *)

Lemma rt_tally_lit_facts : forall c se (ts : RT.TSt),
  let sn := RT.ts_symnext ts in
  let ts' := snd (RT.tr_tally_lit c se ts) in
  let L := RT.ts_trees ts RT.TK_L in
  fst (RT.tr_tally_lit c se ts) = (sn + 3 =? se)
  /\ RT.ts_symnext ts' = sn + 3
  /\ RT.ts_symbuf ts' = Base.zset (Base.zset (Base.zset (RT.ts_symbuf ts) sn 0) (sn + 1) 0) (sn + 2) (Base.u8 c)
  /\ RT.ts_trees ts' RT.TK_L = RT.t_setfreq L (Base.u8 c) (RT.t_freq L (Base.u8 c) + 1)
  /\ RT.ts_trees ts' RT.TK_D = RT.ts_trees ts RT.TK_D /\ RT.ts_trees ts' RT.TK_BL = RT.ts_trees ts RT.TK_BL
  /\ RT.ts_maxcode ts' = RT.ts_maxcode ts /\ RT.ts_blcount ts' = RT.ts_blcount ts
  /\ RT.ts_heap ts' = RT.ts_heap ts /\ RT.ts_heaplen ts' = RT.ts_heaplen ts
  /\ RT.ts_heapmax ts' = RT.ts_heapmax ts /\ RT.ts_depth ts' = RT.ts_depth ts
  /\ RT.ts_optlen ts' = RT.ts_optlen ts /\ RT.ts_statlen ts' = RT.ts_statlen ts
  /\ RT.ts_matches ts' = RT.ts_matches ts /\ RT.ts_bw ts' = RT.ts_bw ts.
Proof. intros c se ts. repeat split; reflexivity. Qed.

Lemma rt_tally_dist_facts : forall distance length se (ts : RT.TSt),
  let sn := RT.ts_symnext ts in
  let ts' := snd (RT.tr_tally_dist distance length se ts) in
  let dist := Base.u16 distance in
  let len := Base.u8 length in
  let L := RT.ts_trees ts RT.TK_L in
  let D := RT.ts_trees ts RT.TK_D in
  let li := RT.length_code len + RT.LITERALS + 1 in
  let di := RT.d_code (dist - 1) in
  fst (RT.tr_tally_dist distance length se ts) = (sn + 3 =? se)
  /\ RT.ts_symnext ts' = sn + 3
  /\ RT.ts_symbuf ts' = Base.zset (Base.zset (Base.zset (RT.ts_symbuf ts) sn (Base.u8 dist))
                                             (sn + 1) (Base.u8 (Z.shiftr dist 8))) (sn + 2) len
  /\ RT.ts_trees ts' RT.TK_L = RT.t_setfreq L li (RT.t_freq L li + 1)
  /\ RT.ts_trees ts' RT.TK_D = RT.t_setfreq D di (RT.t_freq D di + 1)
  /\ RT.ts_trees ts' RT.TK_BL = RT.ts_trees ts RT.TK_BL
  /\ RT.ts_maxcode ts' = RT.ts_maxcode ts /\ RT.ts_blcount ts' = RT.ts_blcount ts
  /\ RT.ts_heap ts' = RT.ts_heap ts /\ RT.ts_heaplen ts' = RT.ts_heaplen ts
  /\ RT.ts_heapmax ts' = RT.ts_heapmax ts /\ RT.ts_depth ts' = RT.ts_depth ts
  /\ RT.ts_optlen ts' = RT.ts_optlen ts /\ RT.ts_statlen ts' = RT.ts_statlen ts
  /\ RT.ts_matches ts' = RT.ts_matches ts /\ RT.ts_bw ts' = RT.ts_bw ts.
Proof. intros distance length se ts. repeat split; reflexivity. Qed.

(* ------------------------------------------------------------------------- *)
(* 5.  Small array facts                                                     *)
(* ------------------------------------------------------------------------- *)

Lemma sym3_len : forall s v0 v1 v2, arr_len (sym3 s v0 v1 v2) = arr_len (DS.ds_pending_buf s).
Proof. intros. unfold sym3. rewrite !arr_len_set. reflexivity. Qed.

(** The three stores land where RT's three [zset]s do. *)
Lemma sym3_get : forall s v0 v1 v2 (sb : Base.zarr) i,
  0 <= DS.ds_lit_bufsize s -> 0 <= DS.ds_sym_next s ->
  DS.ds_lit_bufsize s + DS.ds_sym_next s + 3 <= arr_len (DS.ds_pending_buf s) ->
  0 <= i < DS.ds_sym_next s + 3 ->
  (forall j, 0 <= j < DS.ds_sym_next s -> arr_get (DS.ds_pending_buf s) (DS.ds_lit_bufsize s + j) = sb j) ->
  arr_get (sym3 s v0 v1 v2) (DS.ds_lit_bufsize s + i)
  = Base.zset (Base.zset (Base.zset sb (DS.ds_sym_next s) (wrap8 v0)) (DS.ds_sym_next s + 1) (wrap8 v1))
              (DS.ds_sym_next s + 2) (wrap8 v2) i.
Proof.
  intros s v0 v1 v2 sb i Hl Hn Hr Hi Hold. unfold sym3. cbv zeta.
  set (L := DS.ds_lit_bufsize s) in *. set (n := DS.ds_sym_next s) in *.
  rewrite !arr_get_set. unfold arr_inb. rewrite !arr_len_set. unfold Base.zset.
  destruct (Z.eqb_spec i (n + 2)) as [E2|N2].
  { subst i. replace (L + (n + 1 + 1) =? L + (n + 2)) with true by (symmetry; apply Z.eqb_eq; lia).
    replace (0 <=? L + (n + 1 + 1)) with true by (symmetry; apply Z.leb_le; lia).
    replace (L + (n + 1 + 1) <? arr_len (DS.ds_pending_buf s)) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
  replace (L + (n + 1 + 1) =? L + i) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb].
  destruct (Z.eqb_spec i (n + 1)) as [E1|N1].
  { subst i. rewrite Z.eqb_refl.
    replace (0 <=? L + (n + 1)) with true by (symmetry; apply Z.leb_le; lia).
    replace (L + (n + 1) <? arr_len (DS.ds_pending_buf s)) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
  replace (L + (n + 1) =? L + i) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb].
  destruct (Z.eqb_spec i n) as [E0|N0].
  { subst i. rewrite Z.eqb_refl.
    replace (0 <=? L + n) with true by (symmetry; apply Z.leb_le; lia).
    replace (L + n <? arr_len (DS.ds_pending_buf s)) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
  replace (L + n =? L + i) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb].
  apply Hold. lia.
Qed.

(** A frequency bump is RT's [t_setfreq] on the related array. *)
Lemma bump_rel : forall (a : arr) (tr : RT.Tree) i hi,
  arr_rel a (RT.tr_fc tr) 0 hi -> 0 <= i < hi -> hi <= arr_len a ->
  arr_rel (bump a i) (RT.tr_fc (RT.t_setfreq tr i (RT.t_freq tr i + 1))) 0 hi.
Proof.
  intros a tr i hi H Hi Hlen. unfold bump, RT.t_setfreq, RT.t_freq. cbn [RT.tr_fc].
  rewrite <- (H i Hi), BrBits.wrap16_u16. apply arr_rel_set; [exact H | intros; lia].
Qed.

Lemma bump_len : forall a i, arr_len (bump a i) = arr_len a.
Proof. intros. unfold bump. apply arr_len_set. Qed.

Lemma bump_range : forall a i j, (0 <= arr_get a j < 65536) -> 0 <= arr_get (bump a i) j < 65536.
Proof.
  intros a i j H. unfold bump. rewrite arr_get_set. destruct (_ && _); [|exact H].
  pose proof (wrap16_range (arr_get a i + 1)). lia.
Qed.

Lemma sym3_range : forall s v0 v1 v2 i,
  (0 <= i < arr_len (DS.ds_pending_buf s) -> 0 <= arr_get (DS.ds_pending_buf s) i < 256) ->
  0 <= i < arr_len (sym3 s v0 v1 v2) -> 0 <= arr_get (sym3 s v0 v1 v2) i < 256.
Proof.
  intros s v0 v1 v2 i H Hi. rewrite sym3_len in Hi. unfold sym3. cbv zeta. rewrite !arr_get_set.
  pose proof (wrap8_range v0). pose proof (wrap8_range v1). pose proof (wrap8_range v2).
  repeat (destruct (_ && _)); lia.
Qed.

(* ------------------------------------------------------------------------- *)
(* 6.  The invariant half                                                    *)
(* ------------------------------------------------------------------------- *)

Ltac em_names H :=
  destruct H as [Elev Estr Edt Elbs Elbs2 Epbl Esymend Epend Epout Ebiv Ebib Epbb Etout Eaout Eroom
                 Esn Ensym Esyms Ehist Eopt Estat Etl Efc Edl Edep Eblc].

(** What every tally preserves of [em_core], given the shape. *)
Lemma tally_em_core : forall s pb lfc dfc,
  em_core s ->
  FBT.BQ (tally_state s pb lfc dfc) ->
  DO.nsym (tally_state s pb lfc dfc) <= DS.ds_lit_bufsize s - 1 ->
  arr_len pb = arr_len (DS.ds_pending_buf s) ->
  (forall i, 0 <= i < arr_len pb -> 0 <= arr_get pb i < 256) ->
  arr_len lfc = arr_len (DS.ds_dyn_ltree_fc s) -> arr_len dfc = arr_len (DS.ds_dyn_dtree_fc s) ->
  (forall i, 0 <= arr_get lfc i < 65536) -> (forall i, 0 <= arr_get dfc i < 65536) ->
  em_core (tally_state s pb lfc dfc).
Proof.
  intros s pb lfc dfc H (BQ1 & BQ2 & BQ3 & BQ4) Hn Hlen Hpbb Hll Hdl Hlr Hdr.
  em_names H.
  assert (EL : DS.ds_lit_bufsize (tally_state s pb lfc dfc) = DS.ds_lit_bufsize s) by (tally_fields; reflexivity).
  constructor.
  - tally_fields; assumption.
  - tally_fields; assumption.
  - tally_fields; assumption.
  - tally_fields; assumption.
  - tally_fields; assumption.
  - tally_fields. rewrite Hlen. exact Epbl.
  - tally_fields. exact Esymend.
  - tally_fields; assumption.
  - tally_fields; assumption.
  - tally_fields; assumption.
  - tally_fields; assumption.
  - tally_fields. exact Hpbb.
  - tally_fields; assumption.
  - tally_fields; assumption.
  - tally_fields. rewrite Hlen. exact Eroom.
  - exact BQ1.
  - rewrite EL. lia.
  - exact BQ3.
  - exact BQ4.
  - tally_fields; assumption.
  - tally_fields; assumption.
  - unfold TM.tree_lens in *. tally_fields. rewrite Hll, Hdl. exact Etl.
  - intros [| |] i; cbn [DS.tree_fc]; tally_fields; [apply Hlr | apply Hdr | apply (Efc DS.TB)].
  - intros [| |] i; cbn [DS.tree_dl]; tally_fields; [apply (Edl DS.TL) | apply (Edl DS.TD) | apply (Edl DS.TB)].
  - tally_fields. exact Edep.
  - tally_fields. exact Eblc.
Qed.

Lemma em_core_BQ : forall s, em_core s -> FBT.BQ s.
Proof.
  intros s H. em_names H. unfold FBT.BQ. split; [exact Esn|]. split; [lia|]. split; [exact Esyms | exact Ehist].
Qed.

(** The invariant half of both pairs: [em_core] after any tally, and
    [em_inv] when the tally did not fill the symbol buffer. *)
Lemma tally_post_em : forall s pb lfc dfc,
  em_inv s ->
  FBT.BQ (tally_state s pb lfc dfc) ->
  DO.nsym (tally_state s pb lfc dfc) = DO.nsym s + 1 ->
  arr_len pb = arr_len (DS.ds_pending_buf s) ->
  (forall i, 0 <= i < arr_len pb -> 0 <= arr_get pb i < 256) ->
  arr_len lfc = arr_len (DS.ds_dyn_ltree_fc s) -> arr_len dfc = arr_len (DS.ds_dyn_dtree_fc s) ->
  (forall i, 0 <= arr_get lfc i < 65536) -> (forall i, 0 <= arr_get dfc i < 65536) ->
  em_core (tally_state s pb lfc dfc)
  /\ ((DS.ds_sym_next s + 1 + 1 + 1 =? DS.ds_sym_end s) = false -> em_inv (tally_state s pb lfc dfc)).
Proof.
  intros s pb lfc dfc [H Hr] HB HN Hlen Hpbb Hll Hdl Hlr Hdr.
  assert (C : em_core (tally_state s pb lfc dfc)) by (apply tally_em_core; try assumption; lia).
  split; [exact C|]. intros Hf. split; [exact C|].
  rewrite HN. replace (DS.ds_lit_bufsize (tally_state s pb lfc dfc)) with (DS.ds_lit_bufsize s)
    by (tally_fields; reflexivity).
  apply Z.eqb_neq in Hf. em_names H. lia.
Qed.

(** The facts both pairs read off [dst_rel] and [em_inv]. *)
Lemma tally_pre : forall s t pre_out pre_in,
  dst_rel s t pre_out pre_in -> em_inv s ->
  DS.ds_lit_bufsize s + DS.ds_sym_next s + 3 <= arr_len (DS.ds_pending_buf s)
  /\ DS.ds_sym_next s + 3 <= DS.ds_sym_end s
  /\ DS.ds_sym_next s = RT.ts_symnext (RD.d_ts t)
  /\ DS.ds_sym_end s = RC.dg_sym_end (RD.d_cfg t)
  /\ 0 <= DS.ds_sym_next s /\ 2048 <= DS.ds_lit_bufsize s
  /\ DO.nsym s + 2 < 65536
  /\ arr_len (DS.ds_dyn_ltree_fc s) = 573 /\ arr_len (DS.ds_dyn_dtree_fc s) = 61.
Proof.
  intros s t pre_out pre_in (Hg & _ & _ & Hs & _ & _) [H Hr].
  destruct Hs as (Hsn0 & _ & _ & Hsz & _).
  unfold geom_rel in Hg. cbv zeta in Hg. destruct Hg as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hse & _).
  em_names H. destruct Etl as (TL1 & _ & TL3 & _). repeat split; lia.
Qed.

(* ------------------------------------------------------------------------- *)
(* 7.  The two pairs                                                         *)
(* ------------------------------------------------------------------------- *)

Theorem br_tr_tally_lit : forall s t pre_out pre_in c,
  dst_rel s t pre_out pre_in -> em_inv s ->
  dst_rel (fst (DT.tr_tally_lit s c))
          (RD.setD_ts (snd (RT.tr_tally_lit c (RC.dg_sym_end (RD.d_cfg t)) (RD.d_ts t))) t)
          pre_out pre_in
  /\ snd (DT.tr_tally_lit s c) = fst (RT.tr_tally_lit c (RC.dg_sym_end (RD.d_cfg t)) (RD.d_ts t))
  /\ em_core (fst (DT.tr_tally_lit s c))
  /\ (snd (DT.tr_tally_lit s c) = false -> em_inv (fst (DT.tr_tally_lit s c))).
Proof.
  intros s t pre_out pre_in c Hrel Hinv.
  destruct (tally_pre s t pre_out pre_in Hrel Hinv) as (Hroom & Hsn3 & Hsn0 & Hse & Hsn & Hlbs & Hnsym & TL1 & TL3).
  pose proof Hinv as [Hem _]. pose proof (em_core_BQ s Hem) as HBQ. em_names Hem.
  pose proof Hrel as (_ & _ & _ & (_ & _ & Hsy & _ & _) & Ht & _).
  pose proof (FBT.BQ_tally_lit s HBQ Hroom ltac:(lia) Hnsym ltac:(unfold DS.L_CODES; lia) c) as (BQr & Nr & _).
  destruct (tally_lit_shape s c) as [ES EF]. rewrite ES in BQr, Nr |- *. rewrite EF.
  pose proof (rt_tally_lit_facts c (RC.dg_sym_end (RD.d_cfg t)) (RD.d_ts t)) as
    (RF & RSN & RSB & RL & RD' & RB & R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10).
  cbv zeta in RF, RSN, RSB, RL. rewrite <- BrBits.wrap8_u8 in RSB, RL.
  pose proof (wrap8_range c) as Rc. change (2 ^ 8) with 256 in Rc.
  destruct (tally_post_em s _ _ _ Hinv BQr Nr (sym3_len s 0 0 (wrap8 c))
              (fun i Hi => sym3_range s 0 0 (wrap8 c) i (Epbb i) Hi)
              (bump_len _ _) eq_refl (fun i => bump_range _ _ i (Efc DS.TL i)) (fun i => Efc DS.TD i))
    as [PC PI].
  split; [|split; [|split; [exact PC | exact PI]]].
  - apply tally_rel; try assumption; try lia.
    + apply sym3_len.
    + intros i Hi. rewrite RSB, (sym3_get s 0 0 (wrap8 c) (RT.ts_symbuf (RD.d_ts t)) i)
        by (try lia; intros j Hj; apply Hsy; lia).
      rewrite <- Hsn0, (wrap8_id 0) by lia. rewrite (wrap8_id (wrap8 c)) by lia. reflexivity.
    + rewrite RL. destruct Ht as (T1 & _). apply bump_rel; [exact T1 | unfold DS.HEAP_SIZE; lia | unfold DS.HEAP_SIZE; lia].
    + rewrite RD'. destruct Ht as (_ & _ & T3 & _). exact T3.
    + rewrite RL. reflexivity.
    + rewrite RD'. reflexivity.
  - rewrite RF, <- Hsn0, <- Hse. f_equal. lia.
Qed.

Theorem br_tr_tally_dist : forall s t pre_out pre_in distance length,
  dst_rel s t pre_out pre_in -> em_inv s -> 1 <= distance <= 32768 ->
  dst_rel (fst (DT.tr_tally_dist s distance length))
          (RD.setD_ts (snd (RT.tr_tally_dist distance length (RC.dg_sym_end (RD.d_cfg t)) (RD.d_ts t))) t)
          pre_out pre_in
  /\ snd (DT.tr_tally_dist s distance length)
     = fst (RT.tr_tally_dist distance length (RC.dg_sym_end (RD.d_cfg t)) (RD.d_ts t))
  /\ em_core (fst (DT.tr_tally_dist s distance length))
  /\ (snd (DT.tr_tally_dist s distance length) = false -> em_inv (fst (DT.tr_tally_dist s distance length))).
Proof.
  intros s t pre_out pre_in distance length Hrel Hinv Hd.
  destruct (tally_pre s t pre_out pre_in Hrel Hinv) as (Hroom & Hsn3 & Hsn0 & Hse & Hsn & Hlbs & Hnsym & TL1 & TL3).
  pose proof Hinv as [Hem _]. pose proof (em_core_BQ s Hem) as HBQ. em_names Hem.
  pose proof Hrel as (_ & _ & _ & (_ & _ & Hsy & _ & _) & Ht & _).
  pose proof (FBT.BQ_tally_dist s HBQ Hroom ltac:(lia) Hnsym ltac:(unfold DS.L_CODES; lia)
                ltac:(unfold DS.D_CODES; lia) distance length Hd) as (BQr & Nr & _).
  destruct (tally_dist_shape s distance length) as [ES EF]. rewrite ES in BQr, Nr |- *. rewrite EF.
  pose proof (rt_tally_dist_facts distance length (RC.dg_sym_end (RD.d_cfg t)) (RD.d_ts t)) as
    (RF & RSN & RSB & RL & RD' & RB & R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10).
  cbv zeta in RF, RSN, RSB, RL, RD'.
  assert (Hw16 : wrap16 distance = distance) by (apply wrap16_id; lia).
  assert (Hu16 : Base.u16 distance = distance) by (rewrite <- BrBits.wrap16_u16; exact Hw16).
  assert (Hlc : dist_lcode length = RT.length_code (Base.u8 length) + RT.LITERALS + 1).
  { unfold dist_lcode. rewrite length_code_agree by (pose proof (wrap8_range length); lia).
    rewrite BrBits.wrap8_u8. reflexivity. }
  assert (Hdc : dist_dcode distance = RT.d_code (Base.u16 distance - 1)).
  { unfold dist_dcode. rewrite Hw16, Hu16, (wrap16_id (distance - 1)) by lia. apply d_code_agree. lia. }
  assert (Hlcr : 0 <= dist_lcode length < 286).
  { unfold dist_lcode, DS.LITERALS. pose proof (TT.length_code_bound (wrap8 length)). lia. }
  assert (Hdcr : 0 <= dist_dcode distance < 30).
  { unfold dist_dcode, DS.d_code. destruct (_ <? 256); apply TT.dist_code_bound. }
  destruct (tally_post_em s _ _ _ Hinv BQr Nr (sym3_len s _ _ _)
              (fun i Hi => sym3_range s _ _ _ i (Epbb i) Hi)
              (bump_len _ _) (bump_len _ _)
              (fun i => bump_range _ _ i (Efc DS.TL i)) (fun i => bump_range _ _ i (Efc DS.TD i)))
    as [PC PI].
  split; [|split; [|split; [exact PC | exact PI]]].
  - apply tally_rel; try assumption; try lia.
    + apply sym3_len.
    + intros i Hi.
      rewrite RSB, (sym3_get s _ _ _ (RT.ts_symbuf (RD.d_ts t)) i) by (try lia; intros j Hj; apply Hsy; lia).
      rewrite <- Hsn0, Hw16, Hu16, (wrap8_id (wrap8 length)) by apply wrap8_range.
      rewrite !BrBits.wrap8_u8. reflexivity.
    + rewrite RL, <- Hlc. destruct Ht as (T1 & _).
      apply bump_rel; [exact T1 | unfold DS.HEAP_SIZE; lia | unfold DS.HEAP_SIZE; lia].
    + rewrite RD', <- Hdc. destruct Ht as (_ & _ & T3 & _).
      apply bump_rel; [exact T3 | unfold DS.D_CODES; lia | unfold DS.D_CODES; lia].
    + rewrite RL. reflexivity.
    + rewrite RD'. reflexivity.
  - rewrite RF, <- Hsn0, <- Hse. f_equal. lia.
Qed.

Print Assumptions br_tr_tally_lit.
Print Assumptions br_tr_tally_dist.
