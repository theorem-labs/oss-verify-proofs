(** * Bridge.DEmit.BrDFlush — [flush_pending] (pair D10) lifted from [fp_rel] to the whole [dst_rel].

    [BrFlush.br_flush_pending] relates the bit writer and the output side of
    the stream.  The callers in group D (the block flushes, the zlib header
    and trailer, the stored-block path) need the whole deflate relation
    afterwards, so this file adds the frame: [flush_pending] changes only
    [pending_buf], [pending], [pending_out], [bi_buf], [bi_valid] and the
    stream's output fields on S5's side ([flush_pending_shape]), and only
    the bit writer and the stream's output fields on RT's.

    The lifting is stated for an empty symbol buffer ([sym_next = 0]): every
    group D caller flushes between blocks or around the header/trailer,
    where no symbol is live (with live symbols the queue would also have to
    stay below the symbol area, which [sym_rel] tracks). *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require DeflateState Trees DeflateLz.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base Chunk ZBitsOut Trees Deflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelDefl S5Fields BrFlush.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Module DT := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.Trees.

(* ------------------------------------------------------------------------- *)
(* 1.  S5's frame                                                            *)
(* ------------------------------------------------------------------------- *)

(** [s] with the six fields [flush_pending] writes taken from [x]. *)
Definition bw6 (s x : DS.deflate_state) : DS.deflate_state :=
  DS.set_strm
    (DS.set_pending_out
       (DS.set_pending
          (DS.set_bi_valid (DS.set_bi_buf (DS.set_pending_buf s (DS.ds_pending_buf x)) (DS.ds_bi_buf x))
                           (DS.ds_bi_valid x))
          (DS.ds_pending x))
       (DS.ds_pending_out x))
    (DS.ds_strm x).

Ltac split_ifs := repeat match goal with |- context [if ?c then _ else _] => destruct c end.

Lemma flush_pending_shape : forall s, DL.flush_pending s = bw6 s (DL.flush_pending s).
Proof.
  intros s. unfold DL.flush_pending, DT.tr_flush_bits, DT.bi_flush, bw6. cbv zeta.
  split_ifs; first [reflexivity | destruct s; reflexivity].
Qed.

Ltac bw6_fields :=
  unfold bw6; autorewrite with s5f_strm s5f_pending_out s5f_pending s5f_bi_valid s5f_bi_buf s5f_pending_buf.

Lemma bi_flush_len_strm : forall s,
  arr_len (DS.ds_pending_buf (DT.bi_flush s)) = arr_len (DS.ds_pending_buf s)
  /\ DS.ds_strm (DT.bi_flush s) = DS.ds_strm s.
Proof.
  intros s. unfold DT.bi_flush, DT.put_short, DS.put_byte. cbv zeta.
  split_ifs; bw6_fields; rewrite ?arr_len_set; split; reflexivity.
Qed.

Ltac fp_split s :=
  unfold DL.flush_pending, DT.tr_flush_bits; cbv zeta;
  destruct (bi_flush_len_strm s) as [L1 S1]; revert L1 S1;
  generalize (DT.bi_flush s) as s1; intros s1 L1 S1;
  split_ifs;
  autorewrite with s5f_pending s5f_strm s5f_pending_out s5c_emit s5c_avail_out s5c_total_out.

Lemma flush_pending_pb_len : forall s,
  arr_len (DS.ds_pending_buf (DL.flush_pending s)) = arr_len (DS.ds_pending_buf s).
Proof. intros s. fp_split s; exact L1. Qed.

Lemma flush_pending_strm_in : forall s,
  let st := DS.ds_strm (DL.flush_pending s) in let st0 := DS.ds_strm s in
  DS.cs_input st = DS.cs_input st0 /\ DS.cs_next_in st = DS.cs_next_in st0
  /\ DS.cs_avail_in st = DS.cs_avail_in st0 /\ DS.cs_total_in st = DS.cs_total_in st0
  /\ DS.cs_adler st = DS.cs_adler st0 /\ DS.cs_data_type st = DS.cs_data_type st0.
Proof.
  intros s. cbv zeta. fp_split s; unfold DS.cs_emit;
    autorewrite with s5c_out_rev s5c_avail_out s5c_total_out; rewrite S1; repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------------- *)
(* 2.  RT's frame                                                            *)
(* ------------------------------------------------------------------------- *)

Lemma rt_flush_pending_frame : forall t,
  let t' := RD.flush_pending t in
  RD.d_cfg t' = RD.d_cfg t /\ RD.d_status t' = RD.d_status t /\ RD.d_lastflush t' = RD.d_lastflush t
  /\ RD.d_wrap t' = RD.d_wrap t /\ RD.d_ls t' = RD.d_ls t
  /\ RD.zs_in (RD.d_strm t') = RD.zs_in (RD.d_strm t) /\ RD.zs_done (RD.d_strm t') = RD.zs_done (RD.d_strm t)
  /\ RD.zs_totalin (RD.d_strm t') = RD.zs_totalin (RD.d_strm t)
  /\ RD.zs_adler (RD.d_strm t') = RD.zs_adler (RD.d_strm t)
  /\ RD.zs_datatype (RD.d_strm t') = RD.zs_datatype (RD.d_strm t)
  /\ RT.ts_trees (RD.d_ts t') = RT.ts_trees (RD.d_ts t) /\ RT.ts_maxcode (RD.d_ts t') = RT.ts_maxcode (RD.d_ts t)
  /\ RT.ts_blcount (RD.d_ts t') = RT.ts_blcount (RD.d_ts t) /\ RT.ts_heap (RD.d_ts t') = RT.ts_heap (RD.d_ts t)
  /\ RT.ts_heaplen (RD.d_ts t') = RT.ts_heaplen (RD.d_ts t) /\ RT.ts_heapmax (RD.d_ts t') = RT.ts_heapmax (RD.d_ts t)
  /\ RT.ts_depth (RD.d_ts t') = RT.ts_depth (RD.d_ts t) /\ RT.ts_symbuf (RD.d_ts t') = RT.ts_symbuf (RD.d_ts t)
  /\ RT.ts_symnext (RD.d_ts t') = RT.ts_symnext (RD.d_ts t) /\ RT.ts_optlen (RD.d_ts t') = RT.ts_optlen (RD.d_ts t)
  /\ RT.ts_statlen (RD.d_ts t') = RT.ts_statlen (RD.d_ts t) /\ RT.ts_matches (RD.d_ts t') = RT.ts_matches (RD.d_ts t).
Proof.
  intros t. unfold RD.flush_pending, RT.tr_flush_bits. cbv zeta. split_ifs; repeat split; reflexivity.
Qed.

(* ------------------------------------------------------------------------- *)
(* 3.  The lifted pair                                                       *)
(* ------------------------------------------------------------------------- *)

Theorem dst_flush_pending : forall s t pre_out pre_in,
  dst_rel s t pre_out pre_in -> DS.ds_sym_next s = 0 -> flush_room s -> fp_ok s ->
  dst_rel (DL.flush_pending s) (RD.flush_pending t) pre_out pre_in.
Proof.
  intros s t pre_out pre_in Hrel Hsn Hfr Hok.
  pose proof Hrel as (Hg & Hl & Hb & Hs & Ht & Hm).
  pose proof Hm as Hm'. unfold strm_rel in Hm'. cbv zeta in Hm'.
  destruct Hm' as (_ & _ & _ & _ & _ & _ & Hout & Hav & _ & Htot & _).
  destruct (br_flush_pending s t pre_out (conj Hb (conj Hout (conj Hav Htot))) Hfr Hok)
    as (Hb' & Hout' & Hav' & Htot').
  destruct (rt_flush_pending_frame t) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 &
                                          F15 & F16 & F17 & F18 & F19 & F20 & F21 & F22).
  pose proof (flush_pending_pb_len s) as PL.
  destruct (flush_pending_strm_in s) as (S1 & S2 & S3 & S4 & S5' & S6).
  unfold dst_rel. split; [|split; [|split; [|split; [|split]]]].
  - unfold geom_rel in *. cbv zeta in *. rewrite F1, F2, F3, F4, PL.
    rewrite flush_pending_shape. bw6_fields. exact Hg.
  - unfold lz_rel in *. cbv zeta in *. rewrite F5. rewrite flush_pending_shape. bw6_fields. exact Hl.
  - exact Hb'.
  - destruct Hs as (Hsn0 & Hsr & _ & Hsz & _). unfold sym_rel. cbv zeta.
    rewrite F19, PL. rewrite (flush_pending_shape s). bw6_fields.
    split; [exact Hsn0|]. split; [lia|]. split; [intros i Hi; lia|]. split; [exact Hsz|]. intros; lia.
  - unfold tree_rel in *. cbv zeta in *.
    rewrite F11, F12, F13, F14, F15, F16, F17, F20, F21, F22.
    rewrite flush_pending_shape. bw6_fields. exact Ht.
  - unfold strm_rel in *. cbv zeta in *.
    destruct Hm as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10 & M11 & M12).
    rewrite S1, S2, S3, S4, S5', S6, F6, F7, F8, F9, F10.
    split; [exact M1|]. split; [exact M2|]. split; [exact M3|]. split; [exact M4|].
    repeat split; assumption.
Qed.

(** After a flush that leaves room in the output, the queue is empty and
    starts at 0 again (S5 resets [pending_out] once [pending] reaches 0). *)
Lemma bi_flush_facts : forall s, 0 <= DS.ds_bi_valid s <= 16 ->
  DS.ds_pending s <= DS.ds_pending (DT.bi_flush s) <= DS.ds_pending s + 2
  /\ DS.ds_pending_out (DT.bi_flush s) = DS.ds_pending_out s
  /\ DS.ds_strm (DT.bi_flush s) = DS.ds_strm s
  /\ 0 <= DS.ds_bi_valid (DT.bi_flush s) <= 7.
Proof.
  intros s Hbv. unfold DT.bi_flush, DT.put_short, DS.put_byte. cbv zeta.
  destruct (Z.eqb_spec (DS.ds_bi_valid s) 16); [|destruct (Z.leb_spec 8 (DS.ds_bi_valid s))];
    bw6_fields; (split; [lia|]); (split; [reflexivity|]); (split; [reflexivity|]); lia.
Qed.

Lemma flush_pending_drained : forall s,
  DS.ds_pending_out s = 0 -> 0 <= DS.ds_pending s -> DS.ds_pending s + 2 < 2 ^ 32 ->
  0 <= DS.ds_bi_valid s <= 16 ->
  DS.cs_avail_out (DS.ds_strm (DL.flush_pending s)) <> 0 ->
  DS.ds_pending (DL.flush_pending s) = 0 /\ DS.ds_pending_out (DL.flush_pending s) = 0
  /\ 0 <= DS.ds_bi_valid (DL.flush_pending s) <= 7.
Proof.
  intros s Hpo Hp Hp32 Hbv. destruct (bi_flush_facts s Hbv) as (P1 & P2 & P3 & P4).
  unfold DL.flush_pending, DT.tr_flush_bits. cbv zeta.
  revert P1 P2 P3 P4. generalize (DT.bi_flush s) as s1. intros s1 P1 P2 P3 P4.
  rewrite (wrap32_id (DS.ds_pending s1)) by lia. rewrite P3.
  destruct (Z.ltb_spec (DS.cs_avail_out (DS.ds_strm s)) (DS.ds_pending s1)) as [Hlt|Hge].
  - destruct (Z.eqb_spec (DS.cs_avail_out (DS.ds_strm s)) 0) as [E0|E0].
    + rewrite P3. intros H. exfalso. exact (H E0).
    + split_ifs; autorewrite with s5f_pending s5f_strm s5f_pending_out s5c_emit s5c_avail_out s5c_total_out;
        intros H; exfalso; apply H; rewrite ?P3; lia.
  - destruct (Z.eqb_spec (DS.ds_pending s1) 0) as [E0|E0].
    + intros _. rewrite P2, Hpo. split; [exact E0|]. split; [reflexivity | exact P4].
    + autorewrite with s5f_pending s5f_strm s5f_pending_out s5c_emit s5c_avail_out s5c_total_out.
      replace (DS.ds_pending s1 - DS.ds_pending s1) with 0 by lia. cbn [Z.eqb].
      autorewrite with s5f_pending_out. intros _. split; [reflexivity|]. split; [reflexivity|].
      autorewrite with s5f_pending s5f_strm s5f_pending_out. exact P4.
Qed.

(** [flush_pending] stores only bytes ([bi_flush]'s [put_byte]s are [wrap8]). *)
Lemma bi_flush_pbb : forall s,
  (forall i, 0 <= i < arr_len (DS.ds_pending_buf s) -> 0 <= arr_get (DS.ds_pending_buf s) i < 256) ->
  forall i, 0 <= i < arr_len (DS.ds_pending_buf (DT.bi_flush s)) ->
  0 <= arr_get (DS.ds_pending_buf (DT.bi_flush s)) i < 256.
Proof.
  intros s H. unfold DT.bi_flush, DT.put_short, DS.put_byte. cbv zeta.
  split_ifs; bw6_fields; rewrite ?arr_len_set; intros i Hi; rewrite ?arr_get_set;
    repeat match goal with |- context [if ?c then _ else _] => destruct c end;
    first [apply wrap8_range | apply H; exact Hi].
Qed.

Lemma flush_pending_pbb : forall s,
  (forall i, 0 <= i < arr_len (DS.ds_pending_buf s) -> 0 <= arr_get (DS.ds_pending_buf s) i < 256) ->
  forall i, 0 <= i < arr_len (DS.ds_pending_buf (DL.flush_pending s)) ->
  0 <= arr_get (DS.ds_pending_buf (DL.flush_pending s)) i < 256.
Proof.
  intros s H. pose proof (bi_flush_pbb s H) as Q.
  unfold DL.flush_pending, DT.tr_flush_bits. cbv zeta.
  revert Q. generalize (DT.bi_flush s) as s1. intros s1 Q.
  split_ifs; autorewrite with s5f_pending s5f_strm s5f_pending_out; exact Q.
Qed.

(** RT moves bytes from the queue to the output without changing
    [total_out + avail_out]. *)
Lemma rt_flush_pending_out : forall t, 0 <= RD.zs_availout (RD.d_strm t) ->
  0 <= RD.zs_availout (RD.d_strm (RD.flush_pending t))
  /\ RD.zs_totalout (RD.d_strm (RD.flush_pending t)) + RD.zs_availout (RD.d_strm (RD.flush_pending t))
     = RD.zs_totalout (RD.d_strm t) + RD.zs_availout (RD.d_strm t)
  /\ RD.zs_totalout (RD.d_strm t) <= RD.zs_totalout (RD.d_strm (RD.flush_pending t)).
Proof.
  intros t H. unfold RD.flush_pending. cbv zeta.
  set (n := Chunk.zlen (ZBitsOut.bw_out (RT.ts_bw (RT.tr_flush_bits (RD.d_ts t))))).
  assert (Hn : 0 <= n) by (subst n; unfold Chunk.zlen; lia). clearbody n.
  destruct (Z.ltb_spec (RD.zs_availout (RD.d_strm t)) n);
    match goal with |- context [if ?c then _ else _] => destruct c eqn:E end;
    cbn [RD.d_strm RD.setD_strm RD.setD_ts RD.setZ_out RD.setZ_availout RD.setZ_totalout
         RD.zs_availout RD.zs_totalout]; lia.
Qed.
