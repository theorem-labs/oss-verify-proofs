(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import Trees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import CompressModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import FlushBlockModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeZ.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateOverlay.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma upd4_pending_buf : forall s pb pd bb bv, ds_pending_buf (upd4 s pb pd bb bv) = pb.
Proof. intros; destruct s; reflexivity. Qed.
Lemma upd4_pending : forall s pb pd bb bv, ds_pending (upd4 s pb pd bb bv) = pd.
Proof. intros; destruct s; reflexivity. Qed.
Lemma upd4_bi_buf : forall s pb pd bb bv, ds_bi_buf (upd4 s pb pd bb bv) = bb.
Proof. intros; destruct s; reflexivity. Qed.
Lemma upd4_bi_valid : forall s pb pd bb bv, ds_bi_valid (upd4 s pb pd bb bv) = bv.
Proof. intros; destruct s; reflexivity. Qed.

(* [comment removed for export] *)
Definition nb_view (s : deflate_state) :=
  (ds_lit_bufsize s, ds_sym_next s, ds_pending_out s, ds_strm s, ds_level s, ds_strategy s,
   (ds_dyn_ltree_fc s, ds_dyn_ltree_dl s, ds_dyn_dtree_fc s, ds_dyn_dtree_dl s, ds_bl_tree_fc s, ds_bl_tree_dl s),
   (ds_l_max_code s, ds_d_max_code s, ds_opt_len s, ds_static_len s, ds_block_start s, ds_strstart s),
   (ds_bl_count s, ds_heap s, ds_depth s, ds_matches s, ds_window s, ds_w_size s, ds_lookahead s, ds_match_length s)).
Lemma upd4_nb_view : forall s pb pd bb bv, nb_view (upd4 s pb pd bb bv) = nb_view s.
Proof. intros; destruct s; reflexivity. Qed.

(* [comment removed for export] *)
Lemma nb_view_facts : forall a b, nb_view b = nb_view a ->
  ds_lit_bufsize b = ds_lit_bufsize a /\ ds_sym_next b = ds_sym_next a /\ ds_pending_out b = ds_pending_out a
  /\ ds_strm b = ds_strm a /\ ds_level b = ds_level a /\ ds_strategy b = ds_strategy a
  /\ (forall t, tree_fc b t = tree_fc a t) /\ (forall t, tree_dl b t = tree_dl a t)
  /\ ds_l_max_code b = ds_l_max_code a /\ ds_d_max_code b = ds_d_max_code a
  /\ ds_opt_len b = ds_opt_len a /\ ds_static_len b = ds_static_len a
  /\ ds_block_start b = ds_block_start a /\ ds_strstart b = ds_strstart a
  /\ ds_bl_count b = ds_bl_count a /\ ds_heap b = ds_heap a /\ ds_depth b = ds_depth a /\ ds_matches b = ds_matches a
  /\ ds_window b = ds_window a /\ ds_w_size b = ds_w_size a /\ ds_lookahead b = ds_lookahead a /\ ds_match_length b = ds_match_length a.
Proof.
  intros a b E. unfold nb_view in E. injection E. intros.
  repeat split; try assumption; intros [| |]; cbn; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma send_bits_W : forall s v l, ov_W (send_bits s v l) = ov_W s + l.
Proof.
  intros s v l. unfold ov_W.
  destruct (Z_lt_le_dec (Buf_size - l) (ds_bi_valid s)) as [C|C].
  - rewrite (send_bits_flush_eq s v l C), upd4_pending, upd4_bi_valid. unfold Buf_size in *. lia.
  - rewrite (send_bits_keep_eq s v l ltac:(lia)), upd4_pending, upd4_bi_valid. lia.
Qed.

Lemma send_bits_nb_view : forall s v l, nb_view (send_bits s v l) = nb_view s.
Proof. intros. rewrite send_bits_shape. apply upd4_nb_view. Qed.

Lemma send_bits_pending_mono : forall s v l, ds_pending s <= ds_pending (send_bits s v l) <= ds_pending s + 2.
Proof.
  intros s v l. destruct (Z_lt_le_dec (Buf_size - l) (ds_bi_valid s)) as [C|C].
  - rewrite (send_bits_flush_eq s v l C), upd4_pending. lia.
  - rewrite (send_bits_keep_eq s v l ltac:(lia)), upd4_pending. lia.
Qed.

Lemma send_bits_biv : forall s v l, 0 <= ds_bi_valid s <= 16 -> 0 <= l <= 16 -> 0 <= ds_bi_valid (send_bits s v l) <= 16.
Proof.
  intros s v l Hb Hl. unfold Buf_size in *. destruct (Z_lt_le_dec (Buf_size - l) (ds_bi_valid s)) as [C|C]; unfold Buf_size in C.
  - rewrite (send_bits_flush_eq s v l C), upd4_bi_valid. unfold Buf_size. lia.
  - rewrite (send_bits_keep_eq s v l ltac:(unfold Buf_size; lia)), upd4_bi_valid. lia.
Qed.

Lemma send_bits_bib : forall s v l, ds_bi_valid s <= 16 -> 0 <= ds_bi_buf (send_bits s v l) < 2 ^ 16.
Proof.
  intros s v l Hbv. destruct (Z_lt_le_dec (Buf_size - l) (ds_bi_valid s)) as [C|C].
  - rewrite (send_bits_flush_eq s v l C), upd4_bi_buf. apply shiftr_wrap16_range. unfold Buf_size in *. lia.
  - rewrite (send_bits_keep_eq s v l ltac:(lia)), upd4_bi_buf. apply sb_nb_range.
Qed.

(* [comment removed for export] *)
Lemma send_bits_frame : forall s v l i,
  i < ds_pending s \/ ds_pending (send_bits s v l) <= i ->
  arr_get (ds_pending_buf (send_bits s v l)) i = arr_get (ds_pending_buf s) i.
Proof.
  intros s v l i Hi. destruct (Z_lt_le_dec (Buf_size - l) (ds_bi_valid s)) as [C|C].
  - rewrite (send_bits_flush_eq s v l C), upd4_pending_buf in *. rewrite upd4_pending in Hi.
    rewrite !arr_get_set_other by lia. reflexivity.
  - rewrite (send_bits_keep_eq s v l ltac:(lia)), upd4_pending_buf. reflexivity.
Qed.

Lemma send_bits_PBB : forall s v l, PBB s -> PBB (send_bits s v l).
Proof.
  intros s v l H. unfold PBB in *. rewrite sb_pbl.
  destruct (Z_lt_le_dec (Buf_size - l) (ds_bi_valid s)) as [C|C].
  - rewrite (send_bits_flush_eq s v l C), upd4_pending_buf. intros i Hi.
    rewrite !arr_get_set. destruct (_ && _); [apply wrap8_range|]. destruct (_ && _); [apply wrap8_range|]. apply H; exact Hi.
  - rewrite (send_bits_keep_eq s v l ltac:(lia)), upd4_pending_buf. exact H.
Qed.

(* [comment removed for export] *)
Lemma pending_of_W : forall x, 8 * ds_pending x = ov_W x - ds_bi_valid x.
Proof. intros; unfold ov_W; lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint clen (cs : list (Z * Z)) : Z :=
  match cs with [] => 0 | (_, l) :: r => l + clen r end.

Lemma clen_app : forall a b, clen (a ++ b) = clen a + clen b.
Proof. induction a as [|[v l] a IH]; intros; cbn [clen app]; [lia|]. rewrite IH. lia. Qed.

Lemma clen_nonneg : forall cs, Forall (fun c => 0 <= snd c <= 16) cs -> 0 <= clen cs.
Proof. induction cs as [|[v l] cs IH]; intros H; cbn [clen]; [lia|]. inversion H; subst. cbn in *. specialize (IH ltac:(assumption)). lia. Qed.

Lemma clen_repeat : forall c n, clen (repeat c n) = Z.of_nat n * snd c.
Proof. intros [v l] n. induction n as [|n IH]; [reflexivity|]. cbn [repeat clen snd] in *. rewrite IH. lia. Qed.

Lemma sbs_W : forall cs s, ov_W (sbs_run s cs) = ov_W s + clen cs.
Proof. induction cs as [|[v l] cs IH]; intros; cbn [sbs_run clen]; [lia|]. rewrite IH, send_bits_W. lia. Qed.

Lemma sbs_nb_view : forall cs s, nb_view (sbs_run s cs) = nb_view s.
Proof. induction cs as [|[v l] cs IH]; intros; cbn [sbs_run]; [reflexivity|]. rewrite IH. apply send_bits_nb_view. Qed.

Lemma sbs_pbl : forall cs s, arr_len (ds_pending_buf (sbs_run s cs)) = arr_len (ds_pending_buf s).
Proof. induction cs as [|[v l] cs IH]; intros; cbn [sbs_run]; [reflexivity|]. rewrite IH. apply sb_pbl. Qed.

Lemma sbs_pending_mono : forall cs s, ds_pending s <= ds_pending (sbs_run s cs).
Proof. induction cs as [|[v l] cs IH]; intros; cbn [sbs_run]; [lia|]. pose proof (send_bits_pending_mono s v l). specialize (IH (send_bits s v l)). lia. Qed.

Lemma sbs_biv : forall cs s, 0 <= ds_bi_valid s <= 16 -> Forall (fun c => 0 <= snd c <= 16) cs -> 0 <= ds_bi_valid (sbs_run s cs) <= 16.
Proof.
  induction cs as [|[v l] cs IH]; intros s Hb H; cbn [sbs_run]; [exact Hb|]. inversion H; subst. cbn in *.
  apply IH; [apply send_bits_biv; assumption | assumption].
Qed.

Lemma sbs_bib : forall cs s, 0 <= ds_bi_valid s <= 16 -> Forall (fun c => 0 <= snd c <= 16) cs ->
  0 <= ds_bi_buf s < 2 ^ 16 -> 0 <= ds_bi_buf (sbs_run s cs) < 2 ^ 16.
Proof.
  induction cs as [|[v l] cs IH]; intros s Hbv HF Hb; cbn [sbs_run]; [exact Hb|]. inversion HF; subst. cbn in *.
  apply IH; [apply send_bits_biv; assumption | assumption | apply send_bits_bib; lia].
Qed.

Lemma sbs_frame : forall cs s i,
  i < ds_pending s \/ ds_pending (sbs_run s cs) <= i ->
  arr_get (ds_pending_buf (sbs_run s cs)) i = arr_get (ds_pending_buf s) i.
Proof.
  induction cs as [|[v l] cs IH]; intros s i Hi; cbn [sbs_run] in *; [reflexivity|].
  pose proof (send_bits_pending_mono s v l). pose proof (sbs_pending_mono cs (send_bits s v l)).
  rewrite IH by lia. apply send_bits_frame. lia.
Qed.

Lemma sbs_PBB : forall cs s, PBB s -> PBB (sbs_run s cs).
Proof. induction cs as [|[v l] cs IH]; intros s H; cbn [sbs_run]; [exact H|]. apply IH. apply send_bits_PBB. exact H. Qed.

(* [comment removed for export] *)
Lemma sbs_ok_of_bound : forall PBL cs s,
  0 <= ds_bi_valid s <= 16 -> Forall (fun c => 0 <= snd c <= 16) cs ->
  ov_W s + clen cs <= 8 * PBL -> sbs_ok PBL s cs.
Proof.
  induction cs as [|[v l] cs IH]; intros s Hb HF HW; cbn [sbs_ok]; [exact I|].
  inversion HF; subst. cbn [snd clen] in *.
  split; [assumption|]. split.
  - unfold sb_room. intros C. pose proof (clen_nonneg cs ltac:(assumption)). unfold Buf_size, ov_W in *. lia.
  - apply IH; [apply send_bits_biv; assumption | assumption | rewrite send_bits_W; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bi_windup_facts : forall s, 0 <= ds_bi_valid s <= 16 ->
  let s' := bi_windup s in
  nb_view s' = nb_view s /\ ds_bi_valid s' = 0 /\ ds_bi_buf s' = 0
  /\ ds_pending s <= ds_pending s' /\ 8 * ds_pending s' <= ov_W s + 7
  /\ arr_len (ds_pending_buf s') = arr_len (ds_pending_buf s)
  /\ (forall i, i < ds_pending s \/ ds_pending s' <= i -> arr_get (ds_pending_buf s') i = arr_get (ds_pending_buf s) i)
  /\ (PBB s -> PBB s').
Proof.
  intros s Hb s'. subst s'. unfold ov_W, PBB.
  destruct (Z_lt_le_dec 8 (ds_bi_valid s)) as [C|C]; [| destruct (Z_lt_le_dec 0 (ds_bi_valid s)) as [C'|C']].
  - rewrite (bi_windup_eq2 s C), upd4_nb_view, upd4_bi_valid, upd4_bi_buf, upd4_pending, upd4_pending_buf, !arr_len_set.
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [reflexivity|]. split.
    + intros i Hi. rewrite !arr_get_set_other by lia. reflexivity.
    + intros HP i Hi. rewrite !arr_get_set. destruct (_ && _); [apply wrap8_range|]. destruct (_ && _); [apply wrap8_range|]. apply HP; exact Hi.
  - rewrite (bi_windup_eq1 s ltac:(lia)), upd4_nb_view, upd4_bi_valid, upd4_bi_buf, upd4_pending, upd4_pending_buf, !arr_len_set.
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [reflexivity|]. split.
    + intros i Hi. rewrite !arr_get_set_other by lia. reflexivity.
    + intros HP i Hi. rewrite !arr_get_set. destruct (_ && _); [apply wrap8_range|]. apply HP; exact Hi.
  - rewrite (bi_windup_eq0 s ltac:(lia)), upd4_nb_view, upd4_bi_valid, upd4_bi_buf, upd4_pending, upd4_pending_buf.
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [reflexivity|]. split.
    + intros; reflexivity.
    + intros HP; exact HP.
Qed.

Lemma bi_flush_facts : forall s, 0 <= ds_bi_valid s <= 16 -> 0 <= ds_bi_buf s < 2 ^ 16 ->
  let s' := bi_flush s in
  nb_view s' = nb_view s /\ 0 <= ds_bi_valid s' <= 7 /\ 0 <= ds_bi_buf s' < 2 ^ 16
  /\ ds_pending s <= ds_pending s' /\ 8 * ds_pending s' <= ov_W s /\ ov_W s' = ov_W s
  /\ arr_len (ds_pending_buf s') = arr_len (ds_pending_buf s)
  /\ (forall i, i < ds_pending s \/ ds_pending s' <= i -> arr_get (ds_pending_buf s') i = arr_get (ds_pending_buf s) i)
  /\ (PBB s -> PBB s').
Proof.
  intros s Hb Hbb s'. subst s'. unfold ov_W, PBB.
  destruct (Z.eq_dec (ds_bi_valid s) 16) as [C|C]; [| destruct (Z_le_gt_dec 8 (ds_bi_valid s)) as [C'|C']].
  - rewrite (bi_flush_eq16 s C), upd4_nb_view, upd4_bi_valid, upd4_bi_buf, upd4_pending, upd4_pending_buf, !arr_len_set.
    split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [reflexivity|]. split.
    + intros i Hi. rewrite !arr_get_set_other by lia. reflexivity.
    + intros HP i Hi. rewrite !arr_get_set. destruct (_ && _); [apply wrap8_range|]. destruct (_ && _); [apply wrap8_range|]. apply HP; exact Hi.
  - rewrite (bi_flush_eq8 s C' C), upd4_nb_view, upd4_bi_valid, upd4_bi_buf, upd4_pending, upd4_pending_buf, !arr_len_set.
    split; [reflexivity|]. split; [lia|]. split.
    { split; [apply Z.shiftr_nonneg; lia|]. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_lt_upper_bound; [lia|]. change (2 ^ 8 * 2 ^ 16) with (2 ^ 24). lia. }
    split; [lia|]. split; [lia|]. split; [lia|]. split; [reflexivity|]. split.
    + intros i Hi. rewrite !arr_get_set_other by lia. reflexivity.
    + intros HP i Hi. rewrite !arr_get_set. destruct (_ && _); [apply wrap8_range|]. apply HP; exact Hi.
  - rewrite (bi_flush_eq0 s ltac:(lia)), upd4_nb_view, upd4_bi_valid, upd4_bi_buf, upd4_pending, upd4_pending_buf.
    split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [reflexivity|]. split.
    + intros; reflexivity.
    + intros HP; exact HP.
Qed.
