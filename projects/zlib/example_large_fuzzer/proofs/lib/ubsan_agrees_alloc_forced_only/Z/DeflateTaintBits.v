(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import Trees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateBlk.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import Deflate.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import FlushBlockModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateTaintRel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition Bx (B : Z -> Prop) (lo hi : Z) : Z -> Prop := fun i => B i \/ lo <= i < hi.

Lemma rel_Bx_merge W C B bnd ms pm s1 s2 lo mid hi :
  REL W C (Bx (Bx B lo mid) mid hi) bnd ms pm s1 s2 -> lo <= mid <= hi -> REL W C (Bx B lo hi) bnd ms pm s1 s2.
Proof.
  intros R H. eapply rel_weaken; [exact R|intros i X; exact X| |lia].
  intros i. unfold Bx. intros [X|X]; [left; left; exact X|].
  destruct (Z_lt_le_dec i mid); [left; right; lia | right; lia].
Qed.
Lemma rel_Bx_same W C B bnd ms pm s1 s2 lo :
  REL W C B bnd ms pm s1 s2 -> REL W C (Bx B lo lo) bnd ms pm s1 s2.
Proof. intros R. eapply rel_weaken; [exact R|intros i X; exact X| |lia]. unfold Bx. intros i [X|X]; [exact X|lia]. Qed.

(* [comment removed for export] *)
Section RelFacts.
  Variable W : Z -> Prop.
Variable C : Z -> Prop.
Variable B : Z -> Prop.
Variable bnd : Z.
Variable ms : bool.
Variable pm : bool.
Variable s1 : deflate_state.
Variable s2 : deflate_state.
  Hypothesis R : REL W C B bnd ms pm s1 s2.
  Let EC := r_clean _ _ _ _ _ _ _ _ R.
  Lemma rel_pending : ds_pending s2 = ds_pending s1. Proof. symmetry. apply (clean_eq_fieldT ds_pending _ _ EC). reflexivity. Qed.
  Lemma rel_pending_out : ds_pending_out s2 = ds_pending_out s1. Proof. symmetry. apply (clean_eq_fieldT ds_pending_out _ _ EC). reflexivity. Qed.
  Lemma rel_bi_buf : ds_bi_buf s2 = ds_bi_buf s1. Proof. symmetry. apply (clean_eq_fieldT ds_bi_buf _ _ EC). reflexivity. Qed.
  Lemma rel_bi_valid : ds_bi_valid s2 = ds_bi_valid s1. Proof. symmetry. apply (clean_eq_fieldT ds_bi_valid _ _ EC). reflexivity. Qed.
  Lemma rel_sym_next : ds_sym_next s2 = ds_sym_next s1. Proof. symmetry. apply (clean_eq_fieldT ds_sym_next _ _ EC). reflexivity. Qed.
  Lemma rel_lbs : ds_lit_bufsize s2 = ds_lit_bufsize s1. Proof. symmetry. apply (clean_eq_fieldT ds_lit_bufsize _ _ EC). reflexivity. Qed.
  Lemma rel_strm : ds_strm s2 = ds_strm s1. Proof. symmetry. apply (clean_eq_fieldT ds_strm _ _ EC). reflexivity. Qed.
  Lemma rel_level : ds_level s2 = ds_level s1. Proof. symmetry. apply (clean_eq_fieldT ds_level _ _ EC). reflexivity. Qed.
  Lemma rel_strstart : ds_strstart s2 = ds_strstart s1. Proof. symmetry. apply (clean_eq_fieldT ds_strstart _ _ EC). reflexivity. Qed.
  Lemma rel_lookahead : ds_lookahead s2 = ds_lookahead s1. Proof. symmetry. apply (clean_eq_fieldT ds_lookahead _ _ EC). reflexivity. Qed.

  Lemma rel_wrap : ds_wrap s2 = ds_wrap s1. Proof. symmetry. apply (clean_eq_fieldT ds_wrap _ _ EC). reflexivity. Qed.

  Lemma rel_block_start : ds_block_start s2 = ds_block_start s1. Proof. symmetry. apply (clean_eq_fieldT ds_block_start _ _ EC). reflexivity. Qed.
  Lemma rel_match_length : ds_match_length s2 = ds_match_length s1. Proof. symmetry. apply (clean_eq_fieldT ds_match_length _ _ EC). reflexivity. Qed.
  Lemma rel_prev_length : ds_prev_length s2 = ds_prev_length s1. Proof. symmetry. apply (clean_eq_fieldT ds_prev_length _ _ EC). reflexivity. Qed.
  Lemma rel_insert : ds_insert s2 = ds_insert s1. Proof. symmetry. apply (clean_eq_fieldT ds_insert _ _ EC). reflexivity. Qed.
  Lemma rel_match_available : ds_match_available s2 = ds_match_available s1. Proof. symmetry. apply (clean_eq_fieldT ds_match_available _ _ EC). reflexivity. Qed.
End RelFacts.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma put_byte_pending s c : ds_pending (put_byte s c) = ds_pending s + 1.
Proof. reflexivity. Qed.
Lemma put_short_pending s w : ds_pending (put_short s w) = ds_pending s + 2.
Proof. unfold put_short. rewrite !put_byte_pending. lia. Qed.
Lemma bi_valid_put_byte s c : ds_bi_valid (put_byte s c) = ds_bi_valid s. Proof. reflexivity. Qed.
Lemma bi_buf_put_byte s c : ds_bi_buf (put_byte s c) = ds_bi_buf s. Proof. reflexivity. Qed.
Lemma bi_valid_put_short s w : ds_bi_valid (put_short s w) = ds_bi_valid s. Proof. reflexivity. Qed.
Lemma bi_buf_put_short s w : ds_bi_buf (put_short s w) = ds_bi_buf s. Proof. reflexivity. Qed.

Lemma INV_put_byte s c : INV s -> INV (put_byte s c).
Proof.
  intros I. pose proof (iv_pend s I). unfold put_byte. apply INV_set_pending; [dsr; lia|dsr; lia|].
  destruct I; constructor; dsr; try assumption. rewrite arr_len_set. assumption.
Qed.
Lemma INV_put_short s w : INV s -> INV (put_short s w).
Proof. intros I. unfold put_short. apply INV_put_byte, INV_put_byte, I. Qed.

Lemma put_byte_rel W C B bnd ms pm s1 s2 c :
  REL W C B bnd ms pm s1 s2 ->
  REL W C (Bx B (ds_pending s1) (ds_pending (put_byte s1 c))) bnd ms pm (put_byte s1 c) (put_byte s2 c).
Proof.
  intros R. rewrite put_byte_pending. pose proof (rel_pending _ _ _ _ _ _ _ _ R) as Ep.
  unfold put_byte. dsr. rewrite Ep. apply rel_set_pending.
  eapply rel_set_pending_buf; [exact R|].
  eapply aeq_mono; [exact (aeq_set B _ _ (ds_pending s1) (wrap8 c) (r_pb _ _ _ _ _ _ _ _ R))|].
  unfold Bx. intros i [X|X]; [left; exact X|right; lia].
Qed.

Lemma put_short_rel W C B bnd ms pm s1 s2 w :
  REL W C B bnd ms pm s1 s2 ->
  REL W C (Bx B (ds_pending s1) (ds_pending (put_short s1 w))) bnd ms pm (put_short s1 w) (put_short s2 w).
Proof.
  intros R. rewrite put_short_pending. unfold put_short.
  pose proof (put_byte_rel _ _ _ _ _ _ _ _ (Z.land w 255) R) as R1.
  pose proof (put_byte_rel _ _ _ _ _ _ _ _ (Z.shiftr (wrap16 w) 8) R1) as R2.
  rewrite !put_byte_pending in R2. apply (rel_Bx_merge _ _ _ _ _ _ _ _ _ (ds_pending s1 + 1)); [|lia].
  replace (ds_pending s1 + 2) with (ds_pending s1 + 1 + 1) by lia. exact R2.
Qed.

(* [comment removed for export] *)
Ltac bnorm := dsr; rewrite ?bi_valid_put_short, ?bi_buf_put_short, ?bi_valid_put_byte, ?bi_buf_put_byte,
                           ?put_short_pending, ?put_byte_pending in *; dsr.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma send_bits_pending s v l :
  ds_pending (send_bits s v l) = (if Z.ltb (Buf_size - l) (ds_bi_valid s) then ds_pending s + 2 else ds_pending s).
Proof. unfold send_bits. destruct (Z.ltb _ _); bnorm; reflexivity. Qed.

Lemma send_bits_rel W C B bnd ms pm s1 s2 v l :
  REL W C B bnd ms pm s1 s2 ->
  REL W C (Bx B (ds_pending s1) (ds_pending (send_bits s1 v l))) bnd ms pm (send_bits s1 v l) (send_bits s2 v l).
Proof.
  intros R. pose proof (rel_bi_valid _ _ _ _ _ _ _ _ R) as Ev. pose proof (rel_bi_buf _ _ _ _ _ _ _ _ R) as Eb.
  rewrite send_bits_pending. unfold send_bits. rewrite Ev, Eb.
  destruct (Z.ltb (Buf_size - l) (ds_bi_valid s1)); bnorm; rewrite ?Ev, ?Eb.
  - apply rel_set_bi_valid. apply rel_set_bi_buf.
    match goal with |- REL _ _ _ _ _ _ (put_short (set_bi_buf s1 ?x) _) _ =>
      pose proof (put_short_rel _ _ _ _ _ _ _ _ x (rel_set_bi_buf _ _ _ _ _ _ _ _ x R)) as R1 end.
    rewrite put_short_pending in R1. dsr. exact R1.
  - apply rel_Bx_same. apply rel_set_bi_valid. apply rel_set_bi_buf. exact R.
Qed.

Lemma bi_flush_pending s :
  ds_pending (bi_flush s) = (if Z.eqb (ds_bi_valid s) 16 then ds_pending s + 2 else if Z.leb 8 (ds_bi_valid s) then ds_pending s + 1 else ds_pending s).
Proof. unfold bi_flush. destruct (Z.eqb _ _); [|destruct (Z.leb _ _)]; bnorm; reflexivity. Qed.
Lemma bi_flush_pending_le s : ds_pending s <= ds_pending (bi_flush s) <= ds_pending s + 2.
Proof. rewrite bi_flush_pending. destruct (Z.eqb _ _); [|destruct (Z.leb _ _)]; lia. Qed.
Lemma INV_bi_flush s : INV s -> INV (bi_flush s).
Proof. intros I. unfold bi_flush. destruct (Z.eqb _ _); [|destruct (Z.leb _ _)]; repeat first [apply INV_set_bi_valid | apply INV_set_bi_buf | apply INV_put_short | apply INV_put_byte]; exact I. Qed.
Lemma bi_flush_rel W C B bnd ms pm s1 s2 :
  REL W C B bnd ms pm s1 s2 ->
  REL W C (Bx B (ds_pending s1) (ds_pending (bi_flush s1))) bnd ms pm (bi_flush s1) (bi_flush s2).
Proof.
  intros R. pose proof (rel_bi_valid _ _ _ _ _ _ _ _ R) as Ev. pose proof (rel_bi_buf _ _ _ _ _ _ _ _ R) as Eb.
  rewrite bi_flush_pending. unfold bi_flush. rewrite Ev, Eb.
  destruct (Z.eqb (ds_bi_valid s1) 16); [|destruct (Z.leb 8 (ds_bi_valid s1))]; bnorm; rewrite ?Ev, ?Eb.
  - apply rel_set_bi_valid. apply rel_set_bi_buf. pose proof (put_short_rel _ _ _ _ _ _ _ _ (ds_bi_buf s1) R) as R1. rewrite put_short_pending in R1. exact R1.
  - apply rel_set_bi_valid. apply rel_set_bi_buf. pose proof (put_byte_rel _ _ _ _ _ _ _ _ (ds_bi_buf s1) R) as R1. rewrite put_byte_pending in R1. exact R1.
  - apply rel_Bx_same. exact R.
Qed.
(* [comment removed for export] *)

Lemma bi_windup_pending s :
  ds_pending (bi_windup s) = (if Z.ltb 8 (ds_bi_valid s) then ds_pending s + 2 else if Z.ltb 0 (ds_bi_valid s) then ds_pending s + 1 else ds_pending s).
Proof. unfold bi_windup. destruct (Z.ltb 8 _); [|destruct (Z.ltb 0 _)]; bnorm; reflexivity. Qed.

Lemma bi_windup_rel W C B bnd ms pm s1 s2 :
  REL W C B bnd ms pm s1 s2 ->
  REL W C (Bx B (ds_pending s1) (ds_pending (bi_windup s1))) bnd ms pm (bi_windup s1) (bi_windup s2).
Proof.
  intros R. pose proof (rel_bi_valid _ _ _ _ _ _ _ _ R) as Ev. pose proof (rel_bi_buf _ _ _ _ _ _ _ _ R) as Eb.
  rewrite bi_windup_pending. unfold bi_windup. rewrite Ev, Eb.
  destruct (Z.ltb 8 (ds_bi_valid s1)); [|destruct (Z.ltb 0 (ds_bi_valid s1))]; bnorm; rewrite ?Ev, ?Eb.
  - apply rel_set_bi_valid. apply rel_set_bi_buf. pose proof (put_short_rel _ _ _ _ _ _ _ _ (ds_bi_buf s1) R) as R1. rewrite put_short_pending in R1. exact R1.
  - apply rel_set_bi_valid. apply rel_set_bi_buf. pose proof (put_byte_rel _ _ _ _ _ _ _ _ (ds_bi_buf s1) R) as R1. rewrite put_byte_pending in R1. exact R1.
  - apply rel_Bx_same. apply rel_set_bi_valid. apply rel_set_bi_buf. exact R.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma arr_slice_length' (a : arr) ofs n : 0 <= n -> zlength (arr_slice a ofs n) = n.
Proof. intros Hn. rewrite arr_slice_length; lia. Qed.
Lemma zlength_rev_append {A} (l r : list A) : zlength (List.rev_append l r) = zlength l + zlength r.
Proof. rewrite List.rev_append_rev, zlength_app. unfold zlength. rewrite List.length_rev. lia. Qed.

(* [comment removed for export] *)
Definition lzv (s : deflate_state) :=
  (ds_status s, ds_pending_buf_size s, ds_pending_out s, ds_wrap s, ds_gzhead s, ds_gzindex s, ds_method s, ds_last_flush s,
   (ds_w_size s, ds_w_bits s, ds_w_mask s, ds_window s, ds_window_size s, ds_prev s, ds_head s, ds_ins_h s,
   (ds_hash_size s, ds_hash_bits s, ds_hash_mask s, ds_hash_shift s, ds_block_start s, ds_match_length s, ds_prev_match s, ds_match_available s,
   (ds_strstart s, ds_match_start s, ds_lookahead s, ds_prev_length s, ds_max_chain_length s, ds_max_lazy_match s, ds_level s, ds_strategy s,
   (ds_good_match s, ds_nice_match s, ds_lit_bufsize s, ds_sym_end s, ds_insert s, ds_high_water s,
   (ds_self_blk s, ds_window_blk s, ds_prev_blk s, ds_head_blk s, ds_pending_buf_blk s)))))).

Lemma keeps_lzv : keeps lzv true true.
Proof. constructor; intros; try match goal with tt : tree_id |- _ => destruct tt end; match goal with ss : deflate_state |- _ => destruct ss; reflexivity end. Qed.
Lemma keeps_pending_out : keeps ds_pending_out true true.
Proof. constructor; intros; try match goal with tt : tree_id |- _ => destruct tt end; match goal with ss : deflate_state |- _ => destruct ss; reflexivity end. Qed.

(* [comment removed for export] *)
Lemma lzv_fields a b : lzv b = lzv a ->
  ds_status b = ds_status a /\ ds_pending_buf_size b = ds_pending_buf_size a /\ ds_pending_out b = ds_pending_out a /\ ds_wrap b = ds_wrap a /\ ds_gzhead b = ds_gzhead a /\ ds_gzindex b = ds_gzindex a /\ ds_method b = ds_method a /\ ds_last_flush b = ds_last_flush a /\ ds_w_size b = ds_w_size a /\ ds_w_bits b = ds_w_bits a /\ ds_w_mask b = ds_w_mask a /\ ds_window b = ds_window a /\ ds_window_size b = ds_window_size a /\ ds_prev b = ds_prev a /\ ds_head b = ds_head a /\ ds_ins_h b = ds_ins_h a /\ ds_hash_size b = ds_hash_size a /\ ds_hash_bits b = ds_hash_bits a /\ ds_hash_mask b = ds_hash_mask a /\ ds_hash_shift b = ds_hash_shift a /\ ds_block_start b = ds_block_start a /\ ds_match_length b = ds_match_length a /\ ds_prev_match b = ds_prev_match a /\ ds_match_available b = ds_match_available a /\ ds_strstart b = ds_strstart a /\ ds_match_start b = ds_match_start a /\ ds_lookahead b = ds_lookahead a /\ ds_prev_length b = ds_prev_length a /\ ds_max_chain_length b = ds_max_chain_length a /\ ds_max_lazy_match b = ds_max_lazy_match a /\ ds_level b = ds_level a /\ ds_strategy b = ds_strategy a /\ ds_good_match b = ds_good_match a /\ ds_nice_match b = ds_nice_match a /\ ds_lit_bufsize b = ds_lit_bufsize a /\ ds_sym_end b = ds_sym_end a /\ ds_insert b = ds_insert a /\ ds_high_water b = ds_high_water a /\ ds_self_blk b = ds_self_blk a /\ ds_window_blk b = ds_window_blk a /\ ds_prev_blk b = ds_prev_blk a /\ ds_head_blk b = ds_head_blk a /\ ds_pending_buf_blk b = ds_pending_buf_blk a.
Proof.
  intros E. unfold lzv in E.
  repeat match goal with H : (_, _) = (_, _) |- _ => apply pair_equal_spec in H; destruct H as [H ?] end.
  repeat split; assumption.
Qed.

(* [comment removed for export] *)
Ltac lzv_rw E :=
  let H := fresh in pose proof (lzv_fields _ _ E) as H;
  repeat match type of H with _ /\ _ => let H1 := fresh in destruct H as [H1 H]; rewrite ?H1 in *; clear H1 end;
  rewrite ?H in *; clear H.

Lemma bi_flush_len s : arr_len (ds_pending_buf (bi_flush s)) = arr_len (ds_pending_buf s).
Proof. unfold bi_flush, put_short, put_byte. destruct (Z.eqb _ _); [|destruct (Z.leb _ _)]; dsr; rewrite ?arr_len_set; reflexivity. Qed.

Lemma flush_pending_shape s : 0 <= cs_avail_out (ds_strm s) -> 0 <= ds_pending s -> ds_pending s + 2 < 2 ^ 32 ->
  let s' := bi_flush s in
  let len := Z.min (cs_avail_out (ds_strm s)) (ds_pending s') in
  exists po st,
    flush_pending s = set_pending_out (set_pending (set_strm s' st) (ds_pending s' - len)) po
    /\ cs_input st = cs_input (ds_strm s) /\ cs_next_in st = cs_next_in (ds_strm s) /\ cs_avail_in st = cs_avail_in (ds_strm s)
    /\ cs_avail_out st = cs_avail_out (ds_strm s) - len
    /\ zlength (cs_out_rev st) = zlength (cs_out_rev (ds_strm s)) + len
    /\ 0 <= len <= ds_pending s'
    /\ ((ds_pending s' - len = 0 /\ po = 0) \/ (ds_pending s' - len <> 0 /\ len = cs_avail_out (ds_strm s) /\ po = ds_pending_out s + len) \/ (len = 0 /\ po = ds_pending_out s))
    /\ (len <> 0 -> cs_out_rev st = List.rev_append (arr_slice (ds_pending_buf s') (ds_pending_out s) len) (cs_out_rev (ds_strm s))).
Proof.
  intros A0 P0 P32. pose proof (bi_flush_pending_le s) as Hp1.
  cbv zeta. unfold flush_pending, tr_flush_bits.
  pose proof (k_bi_flush ds_strm true true keeps_strm eq_refl s) as Est.
  pose proof (k_bi_flush ds_pending_out true true keeps_pending_out eq_refl s) as Epo.
  set (s' := bi_flush s) in *. clearbody s'. rewrite Est, Epo. set (p1 := ds_pending s') in *.
  rewrite (wrap32_id p1) by lia.
  set (len := if cs_avail_out (ds_strm s) <? p1 then cs_avail_out (ds_strm s) else p1).
  assert (Hlen : len = Z.min (cs_avail_out (ds_strm s)) p1) by (subst len; destruct (Z.ltb_spec (cs_avail_out (ds_strm s)) p1); lia).
  clearbody len. rewrite <- Hlen.
  destruct (Z.eqb_spec len 0) as [L0|L0].
  - exists (ds_pending_out s), (ds_strm s). rewrite L0, Z.sub_0_r.
    split; [subst p1; rewrite <- Est, <- Epo; destruct s'; reflexivity|].
    repeat match goal with |- _ /\ _ => split end; try reflexivity; try lia. all: intros X; exfalso; exact (X eq_refl).
  - unfold cs_emit. dsr. subst p1. destruct (Z.eqb_spec (ds_pending s' - len) 0) as [Z0|Z0]; dsr.
    + eexists 0, _. split; [destruct s'; reflexivity|]. dsr. rewrite zlength_rev_append, arr_slice_length' by lia.
      repeat match goal with |- _ /\ _ => split end; try reflexivity; try lia. all: intros _; reflexivity.
    + eexists (ds_pending_out s + len), _. split; [destruct s'; reflexivity|]. dsr. rewrite zlength_rev_append, arr_slice_length' by lia.
      repeat match goal with |- _ /\ _ => split end; try reflexivity; try lia. all: intros _; reflexivity.
Qed.

Lemma INV_upd3 s st p po :
  INV s -> 0 <= cs_avail_in st -> 0 <= cs_avail_out st -> 0 <= p -> (p = 0 -> po = 0) ->
  INV (set_pending_out (set_pending (set_strm s st) p) po).
Proof. intros I A1 A2 P1 P2. destruct I; constructor; dsr; solve [assumption | lia]. Qed.

Lemma INV_flush_pending s : INV s -> ds_pending s + 2 < 2 ^ 32 -> INV (flush_pending s).
Proof.
  intros I P32. pose proof (iv_aout s I) as A0. pose proof (iv_pend s I) as P0. pose proof (iv_ain s I) as AI.
  pose proof (flush_pending_shape s A0 P0 P32) as SH. cbv zeta in SH. destruct SH as (po & st & E & Ei & En & Ea & Eo & El & Hlen & Hpo & _).
  rewrite E. pose proof (INV_bi_flush s I) as I'. pose proof (bi_flush_pending_le s) as BL. pose proof (iv_po s I) as PO.
  set (s' := bi_flush s) in *. clearbody s'.
  apply INV_upd3; [exact I'|rewrite Ea; exact AI|rewrite Eo; lia|lia|intros Hp; lia].
Qed.

Lemma rel_upd3 W C B bnd ms pm s1 s2 st p po :
  REL W C B bnd ms pm s1 s2 ->
  REL W C B bnd ms pm (set_pending_out (set_pending (set_strm s1 st) p) po) (set_pending_out (set_pending (set_strm s2 st) p) po).
Proof. intros R. apply rel_set_pending_out, rel_set_pending, rel_set_strm, R. Qed.

(* [comment removed for export] *)
Lemma flush_pending_rel W C B bnd ms pm s1 s2 :
  REL W C B bnd ms pm s1 s2 -> INV s1 -> INV s2 ->
  0 <= ds_pending_out s1 -> ds_pending_out s1 + ds_pending (bi_flush s1) <= arr_len (ds_pending_buf s1) ->
  (forall i, ds_pending_out s1 <= i < ds_pending_out s1 + ds_pending s1 -> B i) ->
  (ds_pending_out s1 = 0 \/ ds_pending (bi_flush s1) = ds_pending s1) ->
  REL W C (Bx B (ds_pending s1) (ds_pending (bi_flush s1))) bnd ms pm (flush_pending s1) (flush_pending s2)
  /\ INV (flush_pending s1) /\ INV (flush_pending s2).
Proof.
  intros R I1 I2 PO0 HL PB PZ.
  pose proof (iv_bl s1 I1) as BL1. rewrite BL1 in HL. pose proof (bi_flush_pending_le s1) as PL0.
  assert (P32 : ds_pending s1 + 2 < 2 ^ 32) by lia.
  split; [|split; apply INV_flush_pending; try assumption; rewrite ?(rel_pending _ _ _ _ _ _ _ _ R); exact P32].
  pose proof (bi_flush_rel _ _ _ _ _ _ _ _ R) as R'. pose proof (INV_bi_flush s1 I1) as I1'. pose proof (INV_bi_flush s2 I2) as I2'.
  pose proof (bi_flush_pending_le s1) as PL1.
  pose proof (k_bi_flush ds_strm true true keeps_strm eq_refl s1) as Est.
  pose proof (k_bi_flush ds_pending_out true true keeps_pending_out eq_refl s1) as Epo.
  pose proof (bi_flush_len s1) as Ebl.
  unfold flush_pending, tr_flush_bits.
  set (s1' := bi_flush s1) in *. clearbody s1'. set (s2' := bi_flush s2) in *. clearbody s2'.
  rel_fields R'. rewrite Est, Epo in *.
  pose proof (iv_aout s1 I1) as A0. pose proof (iv_pend s1 I1) as P0.
  rewrite (wrap32_id (ds_pending s1')) by lia.
  set (len := if cs_avail_out (ds_strm s1) <? ds_pending s1' then cs_avail_out (ds_strm s1) else ds_pending s1').
  assert (Hlen : len = Z.min (cs_avail_out (ds_strm s1)) (ds_pending s1')) by (subst len; destruct (Z.ltb_spec (cs_avail_out (ds_strm s1)) (ds_pending s1')); lia).
  clearbody len.
  destruct (Z.eqb_spec len 0) as [L0|L0]; [exact R'|].
  assert (ES : arr_slice (ds_pending_buf s2') (ds_pending_out s1) len = arr_slice (ds_pending_buf s1') (ds_pending_out s1) len).
  { symmetry. apply (aeq_slice _ _ _ _ _ (r_pb _ _ _ _ _ _ _ _ R')); try lia; try (rewrite Ebl, BL1; lia).
    intros k Hk. unfold Bx. destruct PZ as [PO|PE].
    - rewrite PO in *. destruct (Z_lt_le_dec (0 + k) (ds_pending s1)); [left; apply PB; lia|right; lia].
    - left. apply PB. lia. }
  rewrite ES. unfold cs_emit. dsr. rel_fields R'.
  destruct (Z.eqb_spec (ds_pending s1' - len) 0); dsr; rel_fields R'.
  - match goal with |- REL _ _ _ _ _ _ (set_pending_out (set_pending (set_strm (set_pending_out s1' ?a) ?st) ?p) ?po) _ =>
      pose proof (rel_upd3 _ _ _ _ _ _ _ _ st p po (rel_set_pending_out _ _ _ _ _ _ _ _ a R')) as RR end.
    exact RR.
  - match goal with |- REL _ _ _ _ _ _ (set_pending (set_strm (set_pending_out s1' ?a) ?st) ?p) _ =>
      pose proof (rel_set_pending _ _ _ _ _ _ _ _ p (rel_set_strm _ _ _ _ _ _ _ _ st (rel_set_pending_out _ _ _ _ _ _ _ _ a R'))) as RR end.
    exact RR.
Qed.

Lemma INV_putShortMSB s b : INV s -> INV (putShortMSB s b).
Proof. intros I. unfold putShortMSB. apply INV_put_byte, INV_put_byte, I. Qed.
Lemma putShortMSB_pending s b : ds_pending (putShortMSB s b) = ds_pending s + 2.
Proof. unfold putShortMSB. rewrite !put_byte_pending. lia. Qed.
