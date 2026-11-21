(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Trees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateBlk.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Deflate.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Definition aeq (P : Z -> Prop) (a b : arr) : Prop :=
  arr_len a = arr_len b /\ forall i, 0 <= i < arr_len a -> P i -> arr_get a i = arr_get b i.

Lemma aeq_get P a b i : aeq P a b -> 0 <= i < arr_len a -> P i -> arr_get a i = arr_get b i.
Proof. intros [_ H]. apply H. Qed.
Lemma aeq_mono (P Q : Z -> Prop) a b : aeq P a b -> (forall i, Q i -> P i) -> aeq Q a b.
Proof. intros [L H] PQ. split; [exact L|]. intros i Hi Qi. apply H; auto. Qed.

Lemma aeq_set (P : Z -> Prop) a b i v :
  aeq P a b -> aeq (fun j => P j \/ j = i) (arr_set a i v) (arr_set b i v).
Proof.
  intros [L H]. split; [rewrite !arr_len_set; exact L|].
  intros j Hj Pj. rewrite arr_len_set in Hj. rewrite !arr_get_set. unfold arr_inb. rewrite <- L.
  destruct (Z.eqb_spec i j) as [<-|NE]; cbn [andb].
  - replace ((0 <=? i) && (i <? arr_len a)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia). reflexivity.
  - apply H; [exact Hj|]. destruct Pj as [Pj| ->]; [exact Pj|congruence].
Qed.
Lemma aeq_set_keep (P : Z -> Prop) a b i v : aeq P a b -> aeq P (arr_set a i v) (arr_set b i v).
Proof. intros H. apply (aeq_mono _ _ _ _ (aeq_set P a b i v H)). intros; left; assumption. Qed.

Lemma aeq_fill (P : Z -> Prop) a b ofs n v :
  aeq P a b -> aeq (fun j => P j \/ ofs <= j < ofs + n) (arr_fill a ofs n v) (arr_fill b ofs n v).
Proof.
  intros [L H]. split; [rewrite !arr_len_fill; exact L|].
  intros j Hj Pj. rewrite arr_len_fill in Hj. rewrite !arr_get_fill. unfold arr_inb. rewrite <- L.
  replace ((0 <=? j) && (j <? arr_len a)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
  destruct (Z.leb_spec ofs j); destruct (Z.ltb_spec j (ofs + Z.max 0 n)); cbn [andb]; try reflexivity; apply H; try assumption; destruct Pj; try assumption; lia.
Qed.

Lemma aeq_upd (P : Z -> Prop) a b ofs l :
  aeq P a b -> aeq (fun j => P j \/ ofs <= j < ofs + zlength l) (arr_upd a ofs l) (arr_upd b ofs l).
Proof.
  intros [L H]. split; [rewrite !arr_len_upd; exact L|].
  intros j Hj Pj. rewrite arr_len_upd in Hj. rewrite !(arr_get_upd l _ ofs j 0). unfold arr_inb. rewrite <- L.
  replace ((0 <=? j) && (j <? arr_len a)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
  destruct (Z.leb_spec ofs j); destruct (Z.ltb_spec j (ofs + zlength l)); cbn [andb]; try reflexivity; apply H; try assumption; destruct Pj; try assumption; lia.
Qed.

Lemma aeq_blit_self (P : Z -> Prop) a b dofs sofs n :
  aeq P a b -> 0 <= n -> 0 <= sofs -> sofs + n <= arr_len a -> (forall k, 0 <= k < n -> P (sofs + k)) ->
  aeq (fun j => P j \/ dofs <= j < dofs + n) (arr_blit a dofs a sofs n) (arr_blit b dofs b sofs n).
Proof.
  intros [L H] Hn Hs Hsn SP. split; [rewrite !arr_len_blit; exact L|].
  intros j Hj Pj. rewrite arr_len_blit in Hj. rewrite !arr_get_blit. unfold arr_inb. rewrite <- L.
  replace ((0 <=? j) && (j <? arr_len a)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
  destruct (Z.leb_spec dofs j); destruct (Z.ltb_spec j (dofs + Z.max 0 n)); cbn [andb].
  - apply H; [lia|]. apply SP. lia.
  - apply H; [assumption|destruct Pj; [assumption|lia]].
  - apply H; [assumption|destruct Pj; [assumption|lia]].
  - apply H; [assumption|destruct Pj; [assumption|lia]].
Qed.

Lemma aeq_slice (P : Z -> Prop) a b ofs n :
  aeq P a b -> 0 <= ofs -> 0 <= n -> ofs + n <= arr_len a -> (forall k, 0 <= k < n -> P (ofs + k)) ->
  arr_slice a ofs n = arr_slice b ofs n.
Proof.
  intros [L H] Ho N0 Hn SP. unfold arr_slice.
  assert (Hm : ofs + Z.of_nat (Z.to_nat n) <= arr_len a) by lia.
  assert (SP' : forall k, 0 <= k < Z.of_nat (Z.to_nat n) -> P (ofs + k)) by (intros; apply SP; lia).
  generalize dependent (Z.to_nat n). intros m. clear Hn SP. revert ofs Ho.
  induction m as [|m IH]; intros ofs Ho Hm SP'; cbn [arr_slice_nat]; [reflexivity|].
  f_equal.
  - apply H; [lia|]. replace ofs with (ofs + 0) by lia. apply SP'. lia.
  - apply IH; [lia|lia|]. intros k Hk. replace (ofs + 1 + k) with (ofs + (1 + k)) by lia. apply SP'. lia.
Qed.

Lemma aeq_slide (P : Z -> Prop) a b n ws : aeq P a b -> n = arr_len a -> 0 <= n ->
  aeq P (slide_hash_loop (Z.to_nat n) a n ws) (slide_hash_loop (Z.to_nat n) b n ws).
Proof.
  intros [L H] Hn N0. split; [rewrite !slide_hash_loop_len; exact L|].
  intros i Hi Pi. rewrite slide_hash_loop_len in Hi.
  rewrite !(slide_hash_loop_get (Z.to_nat n) _ ws i n) by lia. rewrite (H i Hi Pi). reflexivity.
Qed.


Definition arr0 : arr := arr_make 0 0.

Definition clean (s : deflate_state) : deflate_state :=
  mkDS (ds_status s) arr0 (ds_pending_buf_size s) (ds_pending_out s) (ds_pending s) (ds_wrap s) (ds_gzhead s)
       0 (ds_method s) (ds_last_flush s) (ds_w_size s) (ds_w_bits s) (ds_w_mask s) arr0 (ds_window_size s)
       arr0 arr0 (ds_ins_h s) (ds_hash_size s) (ds_hash_bits s) (ds_hash_mask s) (ds_hash_shift s) (ds_block_start s)
       (ds_match_length s) 0 (ds_match_available s) (ds_strstart s) 0 (ds_lookahead s)
       (ds_prev_length s) (ds_max_chain_length s) (ds_max_lazy_match s) (ds_level s) (ds_strategy s) (ds_good_match s)
       (ds_nice_match s) arr0 arr0 arr0 arr0 arr0 arr0 0 0 0 arr0 arr0 0 0 arr0 (ds_lit_bufsize s) (ds_sym_next s) (ds_sym_end s) (ds_opt_len s) (ds_static_len s)
       (ds_matches s) (ds_insert s) (ds_bi_buf s) (ds_bi_valid s) (ds_high_water s) (ds_self_blk s) (ds_window_blk s)
       (ds_prev_blk s) (ds_head_blk s) (ds_pending_buf_blk s) (ds_strm s).


Definition HWI4 (lvl look ss hw : Z) : Prop := lvl = 0 \/ look = 0 \/ Z.min (ss + look + 258) 65536 <= hw.
Definition HWI (s : deflate_state) : Prop := HWI4 (ds_level s) (ds_lookahead s) (ds_strstart s) (ds_high_water s).

Record INV (s : deflate_state) : Prop := {
  iv_wsize : ds_w_size s = 32768;
  iv_wmask : ds_w_mask s = 32767;
  iv_wbits : ds_w_bits s = 15;
  iv_wsz : ds_window_size s = 65536;
  iv_hsize : ds_hash_size s = 32768;
  iv_hmask : ds_hash_mask s = 32767;
  iv_hbits : ds_hash_bits s = 15;
  iv_hshift : ds_hash_shift s = 5;
  iv_lbs : ds_lit_bufsize s = 16384;
  iv_pbs : ds_pending_buf_size s = 65536;
  iv_symend : ds_sym_end s = 49149;
  iv_wl : arr_len (ds_window s) = 65536;
  iv_pl : arr_len (ds_prev s) = 32768;
  iv_hl : arr_len (ds_head s) = 32768;
  iv_bl : arr_len (ds_pending_buf s) = 65536;
  iv_tl : arr_len (ds_dyn_ltree_fc s) = 573 /\ arr_len (ds_dyn_ltree_dl s) = 573
          /\ arr_len (ds_dyn_dtree_fc s) = 61 /\ arr_len (ds_dyn_dtree_dl s) = 61
          /\ arr_len (ds_bl_tree_fc s) = 39 /\ arr_len (ds_bl_tree_dl s) = 39
          /\ arr_len (ds_bl_count s) = 16 /\ arr_len (ds_heap s) = 573 /\ arr_len (ds_depth s) = 573;
  iv_ss : 0 <= ds_strstart s;
  iv_look : 0 <= ds_lookahead s;
  iv_ins : 0 <= ds_insert s <= ds_strstart s;
  iv_sl : ds_strstart s + ds_lookahead s <= 65536;
  iv_hw : 0 <= ds_high_water s <= 65536;
  iv_ain : 0 <= cs_avail_in (ds_strm s);
  iv_ol : 0 <= ds_opt_len s < 2 ^ 64;
  iv_stl : 0 <= ds_static_len s < 2 ^ 64;
  iv_ml : 0 <= ds_match_length s <= 258;
  iv_pvl : 0 <= ds_prev_length s <= 258;
  iv_strat : ds_strategy s = 0;
  iv_pend : 0 <= ds_pending s;
  iv_po : ds_pending s = 0 -> ds_pending_out s = 0;
  iv_aout : 0 <= cs_avail_out (ds_strm s)
}.


Definition WHI (s : deflate_state) : Z := Z.max (ds_high_water s) (ds_strstart s + ds_lookahead s).
Definition PBOK (s : deflate_state) (i : Z) : Prop :=
  i < ds_pending_out s + ds_pending s \/ ds_lit_bufsize s <= i < ds_lit_bufsize s + ds_sym_next s.
Definition cv (C : Z -> Prop) (bnd v : Z) : Prop := 0 <= v < 65536 /\ (v = 0 \/ (v <= bnd /\ C (Z.land v 32767))).
Definition chain (C : Z -> Prop) (bnd : Z) (s : deflate_state) : Prop :=
  (forall h, 0 <= h < 32768 -> cv C bnd (arr_get (ds_head s) h))
  /\ (forall p, C p -> 0 <= p < 32768 /\ cv C bnd (arr_get (ds_prev s) p)).

Record REL (W C B : Z -> Prop) (bnd : Z) (ms pm : bool) (s1 s2 : deflate_state) : Prop := {
  r_clean : clean s1 = clean s2;
  r_win : aeq W (ds_window s1) (ds_window s2);
  r_head : aeq (fun _ => True) (ds_head s1) (ds_head s2);
  r_prev : aeq C (ds_prev s1) (ds_prev s2);
  r_chain : chain C bnd s1;
  r_pb : aeq B (ds_pending_buf s1) (ds_pending_buf s2);
  r_lfc : aeq (fun i => i < L_CODES) (ds_dyn_ltree_fc s1) (ds_dyn_ltree_fc s2);
  r_dfc : aeq (fun i => i < D_CODES) (ds_dyn_dtree_fc s1) (ds_dyn_dtree_fc s2);
  r_bfc : aeq (fun i => i < BL_CODES) (ds_bl_tree_fc s1) (ds_bl_tree_fc s2);
  r_ms : ms = true -> ds_match_start s1 = ds_match_start s2;
  r_pm : pm = true -> ds_prev_match s1 = ds_prev_match s2;
  r_g1 : MIN_MATCH <= ds_match_length s1 -> ms = true;
  r_g2 : MIN_MATCH <= ds_prev_length s1 -> pm = true;
  r_g3 : pm = true -> ms = true
}.

Lemma rel_weaken W W' C B B' bnd bnd' ms pm s1 s2 :
  REL W C B bnd ms pm s1 s2 ->
  (forall i, W' i -> W i) -> (forall i, B' i -> B i) -> bnd <= bnd' ->
  REL W' C B' bnd' ms pm s1 s2.
Proof.
  intros R HW HB Hb. destruct R as [RC RW RH RP [CH CP] RB RL RD RBL RMS RPM RG1 RG2 RG3]. constructor; auto.
  - eapply aeq_mono; eauto.
  - split.
    + intros h Hh. destruct (CH h Hh) as [A Bq]. split; [exact A|]. destruct Bq as [Bq|[B1 B2]]; [left; exact Bq|right; split; [lia|exact B2]].
    + intros p Cp. destruct (CP p Cp) as [A [A' Bq]]. split; [exact A|]. split; [exact A'|]. destruct Bq as [Bq|[B1 B2]]; [left; exact Bq|right; split; [lia|exact B2]].
  - eapply aeq_mono; eauto.
Qed.


Lemma clean_eq_fieldT {T} (f : deflate_state -> T) s1 s2 :
  clean s1 = clean s2 -> (forall s, f (clean s) = f s) -> f s1 = f s2.
Proof. intros E Hf. rewrite <- (Hf s1), <- (Hf s2), E. reflexivity. Qed.

Ltac eqc_fields EC :=
  lazymatch type of EC with clean ?s1 = clean ?s2 =>
  repeat match goal with
  | |- context [?f s2] =>
        lazymatch f with
        | ds_status => idtac | ds_pending_buf_size => idtac | ds_pending_out => idtac | ds_pending => idtac
        | ds_wrap => idtac | ds_gzhead => idtac | ds_method => idtac | ds_last_flush => idtac
        | ds_w_size => idtac | ds_w_bits => idtac | ds_w_mask => idtac | ds_window_size => idtac
        | ds_ins_h => idtac | ds_hash_size => idtac | ds_hash_bits => idtac | ds_hash_mask => idtac | ds_hash_shift => idtac
        | ds_block_start => idtac | ds_match_length => idtac | ds_match_available => idtac | ds_strstart => idtac
        | ds_lookahead => idtac | ds_prev_length => idtac | ds_max_chain_length => idtac | ds_max_lazy_match => idtac
        | ds_level => idtac | ds_strategy => idtac | ds_good_match => idtac | ds_nice_match => idtac
        | ds_lit_bufsize => idtac | ds_sym_next => idtac | ds_sym_end => idtac | ds_opt_len => idtac | ds_static_len => idtac
        | ds_matches => idtac | ds_insert => idtac | ds_bi_buf => idtac | ds_bi_valid => idtac | ds_high_water => idtac
        | ds_self_blk => idtac | ds_window_blk => idtac | ds_prev_blk => idtac | ds_head_blk => idtac | ds_pending_buf_blk => idtac
        | ds_strm => idtac
        end;
        let H := fresh in
        assert (H : f s2 = f s1) by (symmetry; apply (clean_eq_fieldT f s1 s2 EC); intros; reflexivity);
        rewrite H in *; clear H
  end end.
Ltac rel_fields R :=
  let E := fresh "EQC" in
  pose proof (r_clean _ _ _ _ _ _ _ _ R) as E; eqc_fields E; clear E.

Ltac dsr := cbv delta [WHI PBOK chain] in *; cbn [ds_status ds_pending_buf ds_pending_buf_size ds_pending_out ds_pending ds_wrap ds_gzhead ds_gzindex ds_method ds_last_flush ds_w_size ds_w_bits ds_w_mask ds_window ds_window_size ds_prev ds_head ds_ins_h ds_hash_size ds_hash_bits ds_hash_mask ds_hash_shift ds_block_start ds_match_length ds_prev_match ds_match_available ds_strstart ds_match_start ds_lookahead ds_prev_length ds_max_chain_length ds_max_lazy_match ds_level ds_strategy ds_good_match ds_nice_match ds_dyn_ltree_fc ds_dyn_ltree_dl ds_dyn_dtree_fc ds_dyn_dtree_dl ds_bl_tree_fc ds_bl_tree_dl ds_l_max_code ds_d_max_code ds_bl_max_code ds_bl_count ds_heap ds_heap_len ds_heap_max ds_depth ds_lit_bufsize ds_sym_next ds_sym_end ds_opt_len ds_static_len ds_matches ds_insert ds_bi_buf ds_bi_valid ds_high_water ds_self_blk ds_window_blk ds_prev_blk ds_head_blk ds_pending_buf_blk ds_strm set_status set_pending_buf set_pending_buf_size set_pending_out set_pending set_wrap set_gzhead set_gzindex set_method set_last_flush set_w_size set_w_bits set_w_mask set_window set_window_size set_prev set_head set_ins_h set_hash_size set_hash_bits set_hash_mask set_hash_shift set_block_start set_match_length set_prev_match set_match_available set_strstart set_match_start set_lookahead set_prev_length set_max_chain_length set_max_lazy_match set_level set_strategy set_good_match set_nice_match set_dyn_ltree_fc set_dyn_ltree_dl set_dyn_dtree_fc set_dyn_dtree_dl set_bl_tree_fc set_bl_tree_dl set_l_max_code set_d_max_code set_bl_max_code set_bl_count set_heap set_heap_len set_heap_max set_depth set_lit_bufsize set_sym_next set_sym_end set_opt_len set_static_len set_matches set_insert set_bi_buf set_bi_valid set_high_water set_self_blk set_window_blk set_prev_blk set_head_blk set_pending_buf_blk set_strm tree_fc tree_dl set_tree_fc set_tree_dl max_code set_max_code cset_input cset_next_in cset_avail_in cset_out_rev cset_avail_out cset_total_in cset_total_out cset_msg cset_data_type cset_adler cs_input cs_next_in cs_avail_in cs_out_rev cs_avail_out cs_total_in cs_total_out cs_msg cs_data_type cs_adler cs_emit fst snd] in *.
Lemma clean_set_status s v : clean (set_status s v) = set_status (clean s) v. Proof. reflexivity. Qed.

Lemma clean_set_pending_out s v : clean (set_pending_out s v) = set_pending_out (clean s) v. Proof. reflexivity. Qed.
Lemma clean_set_pending s v : clean (set_pending s v) = set_pending (clean s) v. Proof. reflexivity. Qed.
Lemma clean_set_wrap s v : clean (set_wrap s v) = set_wrap (clean s) v. Proof. reflexivity. Qed.

Lemma clean_set_last_flush s v : clean (set_last_flush s v) = set_last_flush (clean s) v. Proof. reflexivity. Qed.

Lemma clean_set_ins_h s v : clean (set_ins_h s v) = set_ins_h (clean s) v. Proof. reflexivity. Qed.

Lemma clean_set_block_start s v : clean (set_block_start s v) = set_block_start (clean s) v. Proof. reflexivity. Qed.
Lemma clean_set_match_length s v : clean (set_match_length s v) = set_match_length (clean s) v. Proof. reflexivity. Qed.

Lemma clean_set_match_available s v : clean (set_match_available s v) = set_match_available (clean s) v. Proof. reflexivity. Qed.
Lemma clean_set_strstart s v : clean (set_strstart s v) = set_strstart (clean s) v. Proof. reflexivity. Qed.

Lemma clean_set_lookahead s v : clean (set_lookahead s v) = set_lookahead (clean s) v. Proof. reflexivity. Qed.
Lemma clean_set_prev_length s v : clean (set_prev_length s v) = set_prev_length (clean s) v. Proof. reflexivity. Qed.
Lemma clean_set_max_chain_length s v : clean (set_max_chain_length s v) = set_max_chain_length (clean s) v. Proof. reflexivity. Qed.
Lemma clean_set_max_lazy_match s v : clean (set_max_lazy_match s v) = set_max_lazy_match (clean s) v. Proof. reflexivity. Qed.
Lemma clean_set_level s v : clean (set_level s v) = set_level (clean s) v. Proof. reflexivity. Qed.
Lemma clean_set_strategy s v : clean (set_strategy s v) = set_strategy (clean s) v. Proof. reflexivity. Qed.
Lemma clean_set_good_match s v : clean (set_good_match s v) = set_good_match (clean s) v. Proof. reflexivity. Qed.
Lemma clean_set_nice_match s v : clean (set_nice_match s v) = set_nice_match (clean s) v. Proof. reflexivity. Qed.

Lemma clean_set_l_max_code s v : clean (set_l_max_code s v) = clean s. Proof. reflexivity. Qed.
Lemma clean_set_d_max_code s v : clean (set_d_max_code s v) = clean s. Proof. reflexivity. Qed.
Lemma clean_set_bl_max_code s v : clean (set_bl_max_code s v) = clean s. Proof. reflexivity. Qed.

Lemma clean_set_heap_len s v : clean (set_heap_len s v) = clean s. Proof. reflexivity. Qed.
Lemma clean_set_heap_max s v : clean (set_heap_max s v) = clean s. Proof. reflexivity. Qed.

Lemma clean_set_sym_next s v : clean (set_sym_next s v) = set_sym_next (clean s) v. Proof. reflexivity. Qed.

Lemma clean_set_opt_len s v : clean (set_opt_len s v) = set_opt_len (clean s) v. Proof. reflexivity. Qed.
Lemma clean_set_static_len s v : clean (set_static_len s v) = set_static_len (clean s) v. Proof. reflexivity. Qed.
Lemma clean_set_matches s v : clean (set_matches s v) = set_matches (clean s) v. Proof. reflexivity. Qed.
Lemma clean_set_insert s v : clean (set_insert s v) = set_insert (clean s) v. Proof. reflexivity. Qed.
Lemma clean_set_bi_buf s v : clean (set_bi_buf s v) = set_bi_buf (clean s) v. Proof. reflexivity. Qed.
Lemma clean_set_bi_valid s v : clean (set_bi_valid s v) = set_bi_valid (clean s) v. Proof. reflexivity. Qed.
Lemma clean_set_high_water s v : clean (set_high_water s v) = set_high_water (clean s) v. Proof. reflexivity. Qed.

Lemma clean_set_strm s v : clean (set_strm s v) = set_strm (clean s) v. Proof. reflexivity. Qed.

Lemma rel_set_status W C B bnd ms pm s1 s2 v : REL W C B bnd ms pm s1 s2 -> REL W C B bnd ms pm (set_status s1 v) (set_status s2 v).
Proof.
  intros R. pose proof (r_clean _ _ _ _ _ _ _ _ R) as EC. destruct R; constructor;
  [rewrite !clean_set_status, EC; reflexivity | dsr; assumption ..].
Qed.

Lemma rel_set_pending_out W C B bnd ms pm s1 s2 v : REL W C B bnd ms pm s1 s2 -> REL W C B bnd ms pm (set_pending_out s1 v) (set_pending_out s2 v).
Proof.
  intros R. pose proof (r_clean _ _ _ _ _ _ _ _ R) as EC. destruct R; constructor;
  [rewrite !clean_set_pending_out, EC; reflexivity | dsr; assumption ..].
Qed.
Lemma rel_set_pending W C B bnd ms pm s1 s2 v : REL W C B bnd ms pm s1 s2 -> REL W C B bnd ms pm (set_pending s1 v) (set_pending s2 v).
Proof.
  intros R. pose proof (r_clean _ _ _ _ _ _ _ _ R) as EC. destruct R; constructor;
  [rewrite !clean_set_pending, EC; reflexivity | dsr; assumption ..].
Qed.
Lemma rel_set_wrap W C B bnd ms pm s1 s2 v : REL W C B bnd ms pm s1 s2 -> REL W C B bnd ms pm (set_wrap s1 v) (set_wrap s2 v).
Proof.
  intros R. pose proof (r_clean _ _ _ _ _ _ _ _ R) as EC. destruct R; constructor;
  [rewrite !clean_set_wrap, EC; reflexivity | dsr; assumption ..].
Qed.

Lemma rel_set_last_flush W C B bnd ms pm s1 s2 v : REL W C B bnd ms pm s1 s2 -> REL W C B bnd ms pm (set_last_flush s1 v) (set_last_flush s2 v).
Proof.
  intros R. pose proof (r_clean _ _ _ _ _ _ _ _ R) as EC. destruct R; constructor;
  [rewrite !clean_set_last_flush, EC; reflexivity | dsr; assumption ..].
Qed.

Lemma rel_set_ins_h W C B bnd ms pm s1 s2 v : REL W C B bnd ms pm s1 s2 -> REL W C B bnd ms pm (set_ins_h s1 v) (set_ins_h s2 v).
Proof.
  intros R. pose proof (r_clean _ _ _ _ _ _ _ _ R) as EC. destruct R; constructor;
  [rewrite !clean_set_ins_h, EC; reflexivity | dsr; assumption ..].
Qed.

Lemma rel_set_block_start W C B bnd ms pm s1 s2 v : REL W C B bnd ms pm s1 s2 -> REL W C B bnd ms pm (set_block_start s1 v) (set_block_start s2 v).
Proof.
  intros R. pose proof (r_clean _ _ _ _ _ _ _ _ R) as EC. destruct R; constructor;
  [rewrite !clean_set_block_start, EC; reflexivity | dsr; assumption ..].
Qed.
Lemma rel_set_match_length W C B bnd ms pm s1 s2 v : REL W C B bnd ms pm s1 s2 -> (MIN_MATCH <= v -> ms = true) ->
  REL W C B bnd ms pm (set_match_length s1 v) (set_match_length s2 v).
Proof.
  intros R G. pose proof (r_clean _ _ _ _ _ _ _ _ R) as EC. destruct R; constructor;
  [rewrite !clean_set_match_length, EC; reflexivity | dsr; assumption ..].
Qed.
Lemma rel_set_match_available W C B bnd ms pm s1 s2 v : REL W C B bnd ms pm s1 s2 -> REL W C B bnd ms pm (set_match_available s1 v) (set_match_available s2 v).
Proof.
  intros R. pose proof (r_clean _ _ _ _ _ _ _ _ R) as EC. destruct R; constructor;
  [rewrite !clean_set_match_available, EC; reflexivity | dsr; assumption ..].
Qed.
Lemma rel_set_strstart W C B bnd ms pm s1 s2 v : REL W C B bnd ms pm s1 s2 -> REL W C B bnd ms pm (set_strstart s1 v) (set_strstart s2 v).
Proof.
  intros R. pose proof (r_clean _ _ _ _ _ _ _ _ R) as EC. destruct R; constructor;
  [rewrite !clean_set_strstart, EC; reflexivity | dsr; assumption ..].
Qed.
Lemma rel_set_lookahead W C B bnd ms pm s1 s2 v : REL W C B bnd ms pm s1 s2 -> REL W C B bnd ms pm (set_lookahead s1 v) (set_lookahead s2 v).
Proof.
  intros R. pose proof (r_clean _ _ _ _ _ _ _ _ R) as EC. destruct R; constructor;
  [rewrite !clean_set_lookahead, EC; reflexivity | dsr; assumption ..].
Qed.
Lemma rel_set_prev_length W C B bnd ms pm s1 s2 v : REL W C B bnd ms pm s1 s2 -> (MIN_MATCH <= v -> pm = true) ->
  REL W C B bnd ms pm (set_prev_length s1 v) (set_prev_length s2 v).
Proof.
  intros R G. pose proof (r_clean _ _ _ _ _ _ _ _ R) as EC. destruct R; constructor;
  [rewrite !clean_set_prev_length, EC; reflexivity | dsr; assumption ..].
Qed.
Lemma rel_set_max_chain_length W C B bnd ms pm s1 s2 v : REL W C B bnd ms pm s1 s2 -> REL W C B bnd ms pm (set_max_chain_length s1 v) (set_max_chain_length s2 v).
Proof.
  intros R. pose proof (r_clean _ _ _ _ _ _ _ _ R) as EC. destruct R; constructor;
  [rewrite !clean_set_max_chain_length, EC; reflexivity | dsr; assumption ..].
Qed.
Lemma rel_set_max_lazy_match W C B bnd ms pm s1 s2 v : REL W C B bnd ms pm s1 s2 -> REL W C B bnd ms pm (set_max_lazy_match s1 v) (set_max_lazy_match s2 v).
Proof.
  intros R. pose proof (r_clean _ _ _ _ _ _ _ _ R) as EC. destruct R; constructor;
  [rewrite !clean_set_max_lazy_match, EC; reflexivity | dsr; assumption ..].
Qed.
Lemma rel_set_level W C B bnd ms pm s1 s2 v : REL W C B bnd ms pm s1 s2 -> REL W C B bnd ms pm (set_level s1 v) (set_level s2 v).
Proof.
  intros R. pose proof (r_clean _ _ _ _ _ _ _ _ R) as EC. destruct R; constructor;
  [rewrite !clean_set_level, EC; reflexivity | dsr; assumption ..].
Qed.
Lemma rel_set_strategy W C B bnd ms pm s1 s2 v : REL W C B bnd ms pm s1 s2 -> REL W C B bnd ms pm (set_strategy s1 v) (set_strategy s2 v).
Proof.
  intros R. pose proof (r_clean _ _ _ _ _ _ _ _ R) as EC. destruct R; constructor;
  [rewrite !clean_set_strategy, EC; reflexivity | dsr; assumption ..].
Qed.
Lemma rel_set_good_match W C B bnd ms pm s1 s2 v : REL W C B bnd ms pm s1 s2 -> REL W C B bnd ms pm (set_good_match s1 v) (set_good_match s2 v).
Proof.
  intros R. pose proof (r_clean _ _ _ _ _ _ _ _ R) as EC. destruct R; constructor;
  [rewrite !clean_set_good_match, EC; reflexivity | dsr; assumption ..].
Qed.
Lemma rel_set_nice_match W C B bnd ms pm s1 s2 v : REL W C B bnd ms pm s1 s2 -> REL W C B bnd ms pm (set_nice_match s1 v) (set_nice_match s2 v).
Proof.
  intros R. pose proof (r_clean _ _ _ _ _ _ _ _ R) as EC. destruct R; constructor;
  [rewrite !clean_set_nice_match, EC; reflexivity | dsr; assumption ..].
Qed.
Lemma rel_set_l_max_code W C B bnd ms pm s1 s2 v : REL W C B bnd ms pm s1 s2 -> REL W C B bnd ms pm (set_l_max_code s1 v) (set_l_max_code s2 v).
Proof.
  intros R. pose proof (r_clean _ _ _ _ _ _ _ _ R) as EC. destruct R; constructor;
  [rewrite !clean_set_l_max_code, EC; reflexivity | dsr; assumption ..].
Qed.
Lemma rel_set_d_max_code W C B bnd ms pm s1 s2 v : REL W C B bnd ms pm s1 s2 -> REL W C B bnd ms pm (set_d_max_code s1 v) (set_d_max_code s2 v).
Proof.
  intros R. pose proof (r_clean _ _ _ _ _ _ _ _ R) as EC. destruct R; constructor;
  [rewrite !clean_set_d_max_code, EC; reflexivity | dsr; assumption ..].
Qed.
Lemma rel_set_bl_max_code W C B bnd ms pm s1 s2 v : REL W C B bnd ms pm s1 s2 -> REL W C B bnd ms pm (set_bl_max_code s1 v) (set_bl_max_code s2 v).
Proof.
  intros R. pose proof (r_clean _ _ _ _ _ _ _ _ R) as EC. destruct R; constructor;
  [rewrite !clean_set_bl_max_code, EC; reflexivity | dsr; assumption ..].
Qed.
Lemma rel_set_heap_len W C B bnd ms pm s1 s2 v : REL W C B bnd ms pm s1 s2 -> REL W C B bnd ms pm (set_heap_len s1 v) (set_heap_len s2 v).
Proof.
  intros R. pose proof (r_clean _ _ _ _ _ _ _ _ R) as EC. destruct R; constructor;
  [rewrite !clean_set_heap_len, EC; reflexivity | dsr; assumption ..].
Qed.
Lemma rel_set_heap_max W C B bnd ms pm s1 s2 v : REL W C B bnd ms pm s1 s2 -> REL W C B bnd ms pm (set_heap_max s1 v) (set_heap_max s2 v).
Proof.
  intros R. pose proof (r_clean _ _ _ _ _ _ _ _ R) as EC. destruct R; constructor;
  [rewrite !clean_set_heap_max, EC; reflexivity | dsr; assumption ..].
Qed.

Lemma rel_set_sym_next W C B bnd ms pm s1 s2 v : REL W C B bnd ms pm s1 s2 -> REL W C B bnd ms pm (set_sym_next s1 v) (set_sym_next s2 v).
Proof.
  intros R. pose proof (r_clean _ _ _ _ _ _ _ _ R) as EC. destruct R; constructor;
  [rewrite !clean_set_sym_next, EC; reflexivity | dsr; assumption ..].
Qed.

Lemma rel_set_opt_len W C B bnd ms pm s1 s2 v : REL W C B bnd ms pm s1 s2 -> REL W C B bnd ms pm (set_opt_len s1 v) (set_opt_len s2 v).
Proof.
  intros R. pose proof (r_clean _ _ _ _ _ _ _ _ R) as EC. destruct R; constructor;
  [rewrite !clean_set_opt_len, EC; reflexivity | dsr; assumption ..].
Qed.
Lemma rel_set_static_len W C B bnd ms pm s1 s2 v : REL W C B bnd ms pm s1 s2 -> REL W C B bnd ms pm (set_static_len s1 v) (set_static_len s2 v).
Proof.
  intros R. pose proof (r_clean _ _ _ _ _ _ _ _ R) as EC. destruct R; constructor;
  [rewrite !clean_set_static_len, EC; reflexivity | dsr; assumption ..].
Qed.
Lemma rel_set_matches W C B bnd ms pm s1 s2 v : REL W C B bnd ms pm s1 s2 -> REL W C B bnd ms pm (set_matches s1 v) (set_matches s2 v).
Proof.
  intros R. pose proof (r_clean _ _ _ _ _ _ _ _ R) as EC. destruct R; constructor;
  [rewrite !clean_set_matches, EC; reflexivity | dsr; assumption ..].
Qed.
Lemma rel_set_insert W C B bnd ms pm s1 s2 v : REL W C B bnd ms pm s1 s2 -> REL W C B bnd ms pm (set_insert s1 v) (set_insert s2 v).
Proof.
  intros R. pose proof (r_clean _ _ _ _ _ _ _ _ R) as EC. destruct R; constructor;
  [rewrite !clean_set_insert, EC; reflexivity | dsr; assumption ..].
Qed.
Lemma rel_set_bi_buf W C B bnd ms pm s1 s2 v : REL W C B bnd ms pm s1 s2 -> REL W C B bnd ms pm (set_bi_buf s1 v) (set_bi_buf s2 v).
Proof.
  intros R. pose proof (r_clean _ _ _ _ _ _ _ _ R) as EC. destruct R; constructor;
  [rewrite !clean_set_bi_buf, EC; reflexivity | dsr; assumption ..].
Qed.
Lemma rel_set_bi_valid W C B bnd ms pm s1 s2 v : REL W C B bnd ms pm s1 s2 -> REL W C B bnd ms pm (set_bi_valid s1 v) (set_bi_valid s2 v).
Proof.
  intros R. pose proof (r_clean _ _ _ _ _ _ _ _ R) as EC. destruct R; constructor;
  [rewrite !clean_set_bi_valid, EC; reflexivity | dsr; assumption ..].
Qed.
Lemma rel_set_high_water W C B bnd ms pm s1 s2 v : REL W C B bnd ms pm s1 s2 -> REL W C B bnd ms pm (set_high_water s1 v) (set_high_water s2 v).
Proof.
  intros R. pose proof (r_clean _ _ _ _ _ _ _ _ R) as EC. destruct R; constructor;
  [rewrite !clean_set_high_water, EC; reflexivity | dsr; assumption ..].
Qed.

Lemma rel_set_strm W C B bnd ms pm s1 s2 v : REL W C B bnd ms pm s1 s2 -> REL W C B bnd ms pm (set_strm s1 v) (set_strm s2 v).
Proof.
  intros R. pose proof (r_clean _ _ _ _ _ _ _ _ R) as EC. destruct R; constructor;
  [rewrite !clean_set_strm, EC; reflexivity | dsr; assumption ..].
Qed.

Lemma rel_set_match_start W C B bnd ms pm s1 s2 v1 v2 :
  REL W C B bnd ms pm s1 s2 -> (ms = true -> v1 = v2) ->
  REL W C B bnd ms pm (set_match_start s1 v1) (set_match_start s2 v2).
Proof. intros R E. destruct R; constructor; dsr; assumption. Qed.
Lemma rel_set_prev_match W C B bnd ms pm pm' s1 s2 v1 v2 :
  REL W C B bnd ms pm s1 s2 -> (pm' = true -> v1 = v2) ->
  (MIN_MATCH <= ds_prev_length s1 -> pm' = true) -> (pm' = true -> ms = true) ->
  REL W C B bnd ms pm' (set_prev_match s1 v1) (set_prev_match s2 v2).
Proof. intros R E G2 G3. destruct R; constructor; dsr; assumption. Qed.

Lemma rel_set_window W W' C B bnd ms pm s1 s2 a1 a2 :
  REL W C B bnd ms pm s1 s2 -> aeq W' a1 a2 -> REL W' C B bnd ms pm (set_window s1 a1) (set_window s2 a2).
Proof. intros R A. destruct R; constructor; dsr; assumption. Qed.
Lemma rel_set_pending_buf W C B B' bnd ms pm s1 s2 a1 a2 :
  REL W C B bnd ms pm s1 s2 -> aeq B' a1 a2 -> REL W C B' bnd ms pm (set_pending_buf s1 a1) (set_pending_buf s2 a2).
Proof. intros R A. destruct R; constructor; dsr; assumption. Qed.
Lemma rel_set_prev W C C' B bnd bnd' ms pm s1 s2 a1 a2 :
  REL W C B bnd ms pm s1 s2 -> aeq C' a1 a2 -> chain C' bnd' (set_prev s1 a1) ->
  REL W C' B bnd' ms pm (set_prev s1 a1) (set_prev s2 a2).
Proof. intros R A CH. destruct R; constructor; dsr; assumption. Qed.
Lemma rel_set_head W C C' B bnd bnd' ms pm s1 s2 a1 a2 :
  REL W C B bnd ms pm s1 s2 -> aeq (fun _ => True) a1 a2 -> aeq C' (ds_prev s1) (ds_prev s2) -> chain C' bnd' (set_head s1 a1) ->
  REL W C' B bnd' ms pm (set_head s1 a1) (set_head s2 a2).
Proof. intros R A AP CH. destruct R; constructor; dsr; assumption. Qed.
Lemma rel_set_dyn_ltree_fc W C B bnd ms pm s1 s2 a1 a2 :
  REL W C B bnd ms pm s1 s2 -> aeq (fun i => i < L_CODES) a1 a2 -> REL W C B bnd ms pm (set_dyn_ltree_fc s1 a1) (set_dyn_ltree_fc s2 a2).
Proof. intros R A. destruct R; constructor; dsr; assumption. Qed.
Lemma rel_set_dyn_dtree_fc W C B bnd ms pm s1 s2 a1 a2 :
  REL W C B bnd ms pm s1 s2 -> aeq (fun i => i < D_CODES) a1 a2 -> REL W C B bnd ms pm (set_dyn_dtree_fc s1 a1) (set_dyn_dtree_fc s2 a2).
Proof. intros R A. destruct R; constructor; dsr; assumption. Qed.
Lemma rel_set_bl_tree_fc W C B bnd ms pm s1 s2 a1 a2 :
  REL W C B bnd ms pm s1 s2 -> aeq (fun i => i < BL_CODES) a1 a2 -> REL W C B bnd ms pm (set_bl_tree_fc s1 a1) (set_bl_tree_fc s2 a2).
Proof. intros R A. destruct R; constructor; dsr; assumption. Qed.
Lemma rel_set_dyn_ltree_dl W C B bnd ms pm s1 s2 a1 a2 : REL W C B bnd ms pm s1 s2 -> REL W C B bnd ms pm (set_dyn_ltree_dl s1 a1) (set_dyn_ltree_dl s2 a2).
Proof. intros R. destruct R; constructor; dsr; assumption. Qed.
Lemma rel_set_dyn_dtree_dl W C B bnd ms pm s1 s2 a1 a2 : REL W C B bnd ms pm s1 s2 -> REL W C B bnd ms pm (set_dyn_dtree_dl s1 a1) (set_dyn_dtree_dl s2 a2).
Proof. intros R. destruct R; constructor; dsr; assumption. Qed.
Lemma rel_set_bl_tree_dl W C B bnd ms pm s1 s2 a1 a2 : REL W C B bnd ms pm s1 s2 -> REL W C B bnd ms pm (set_bl_tree_dl s1 a1) (set_bl_tree_dl s2 a2).
Proof. intros R. destruct R; constructor; dsr; assumption. Qed.
Lemma rel_set_bl_count W C B bnd ms pm s1 s2 a1 a2 : REL W C B bnd ms pm s1 s2 -> REL W C B bnd ms pm (set_bl_count s1 a1) (set_bl_count s2 a2).
Proof. intros R. destruct R; constructor; dsr; assumption. Qed.
Lemma rel_set_heap W C B bnd ms pm s1 s2 a1 a2 : REL W C B bnd ms pm s1 s2 -> REL W C B bnd ms pm (set_heap s1 a1) (set_heap s2 a2).
Proof. intros R. destruct R; constructor; dsr; assumption. Qed.
Lemma rel_set_depth W C B bnd ms pm s1 s2 a1 a2 : REL W C B bnd ms pm s1 s2 -> REL W C B bnd ms pm (set_depth s1 a1) (set_depth s2 a2).
Proof. intros R. destruct R; constructor; dsr; assumption. Qed.
Lemma rel_rebnd W C B bnd bnd' ms pm s1 s2 :
  REL W C B bnd ms pm s1 s2 -> chain C bnd' s1 -> REL W C B bnd' ms pm s1 s2.
Proof. intros R CH. destruct R; constructor; assumption. Qed.

Lemma INV_set_status s v : INV s -> INV (set_status s v).
Proof. intros I; destruct I; constructor; dsr; assumption. Qed.
Lemma INV_set_wrap s v : INV s -> INV (set_wrap s v).
Proof. intros I; destruct I; constructor; dsr; assumption. Qed.

Lemma INV_set_last_flush s v : INV s -> INV (set_last_flush s v).
Proof. intros I; destruct I; constructor; dsr; assumption. Qed.
Lemma INV_set_ins_h s v : INV s -> INV (set_ins_h s v).
Proof. intros I; destruct I; constructor; dsr; assumption. Qed.
Lemma INV_set_block_start s v : INV s -> INV (set_block_start s v).
Proof. intros I; destruct I; constructor; dsr; assumption. Qed.
Lemma INV_set_match_length s v : 0 <= v <= 258 -> INV s -> INV (set_match_length s v).
Proof. intros; match goal with I : INV s |- _ => destruct I end; constructor; dsr; solve [assumption | lia]. Qed.
Lemma INV_set_match_available s v : INV s -> INV (set_match_available s v).
Proof. intros I; destruct I; constructor; dsr; assumption. Qed.
Lemma INV_set_prev_length s v : 0 <= v <= 258 -> INV s -> INV (set_prev_length s v).
Proof. intros; match goal with I : INV s |- _ => destruct I end; constructor; dsr; solve [assumption | lia]. Qed.

Lemma INV_set_bi_buf s v : INV s -> INV (set_bi_buf s v).
Proof. intros I; destruct I; constructor; dsr; assumption. Qed.
Lemma INV_set_bi_valid s v : INV s -> INV (set_bi_valid s v).
Proof. intros I; destruct I; constructor; dsr; assumption. Qed.

Lemma INV_set_pending s v : 0 <= v -> (v = 0 -> ds_pending_out s = 0) -> INV s -> INV (set_pending s v).
Proof. intros; match goal with I : INV s |- _ => destruct I end; constructor; dsr; solve [assumption | lia]. Qed.

Lemma INV_set_match_start s v : INV s -> INV (set_match_start s v).
Proof. intros I; destruct I; constructor; dsr; assumption. Qed.
Lemma INV_set_prev_match s v : INV s -> INV (set_prev_match s v).
Proof. intros I; destruct I; constructor; dsr; assumption. Qed.
Lemma INV_set_strstart s v : 0 <= v -> ds_insert s <= v -> v + ds_lookahead s <= 65536 -> INV s -> INV (set_strstart s v).
Proof. intros; match goal with I : INV s |- _ => destruct I end; constructor; dsr; solve [assumption | lia]. Qed.
Lemma INV_set_lookahead s v : 0 <= v -> ds_strstart s + v <= 65536 -> INV s -> INV (set_lookahead s v).
Proof. intros; match goal with I : INV s |- _ => destruct I end; constructor; dsr; solve [assumption | lia]. Qed.
Lemma INV_set_insert s v : 0 <= v <= ds_strstart s -> INV s -> INV (set_insert s v).
Proof. intros; match goal with I : INV s |- _ => destruct I end; constructor; dsr; solve [assumption | lia]. Qed.
Lemma INV_set_high_water s v : 0 <= v <= 65536 -> INV s -> INV (set_high_water s v).
Proof. intros; match goal with I : INV s |- _ => destruct I end; constructor; dsr; solve [assumption | lia]. Qed.

Lemma INV_set_strm s v : 0 <= cs_avail_in v -> 0 <= cs_avail_out v -> INV s -> INV (set_strm s v).
Proof. intros; match goal with I : INV s |- _ => destruct I end; constructor; dsr; solve [assumption | lia]. Qed.

Lemma rel_flags W C B bnd ms ms' pm pm' s1 s2 :
  REL W C B bnd ms pm s1 s2 ->
  (ms' = true -> ds_match_start s1 = ds_match_start s2) ->
  (pm' = true -> ds_prev_match s1 = ds_prev_match s2) ->
  (MIN_MATCH <= ds_match_length s1 -> ms' = true) ->
  (MIN_MATCH <= ds_prev_length s1 -> pm' = true) ->
  (pm' = true -> ms' = true) ->
  REL W C B bnd ms' pm' s1 s2.
Proof. intros R ? ? ? ? ?. destruct R; constructor; assumption. Qed.

Lemma HWI4_lvl0 look ss hw : HWI4 0 look ss hw.
Proof. left. reflexivity. Qed.
Lemma HWI4_look0 lvl ss hw : HWI4 lvl 0 ss hw.
Proof. right. left. reflexivity. Qed.
Lemma HWI4_hw lvl look ss hw : Z.min (ss + look + 258) 65536 <= hw -> HWI4 lvl look ss hw.
Proof. intros H. right. right. exact H. Qed.
Lemma HWI4_shift lvl look ss hw look' ss' hw' :
  HWI4 lvl look ss hw -> 0 <= look' -> (look' = 0 \/ (0 < look /\ ss' + look' <= ss + look)) -> hw <= hw' -> HWI4 lvl look' ss' hw'.
Proof.
  unfold HWI4. intros [H|[H|H]] Hl [X|[X1 X2]] Hh; try (left; exact H); try (right; left; exact X).
  - lia.
  - right. right. lia.
Qed.
Lemma HWI4_use lvl look ss hw i : HWI4 lvl look ss hw -> lvl <> 0 -> 0 < look -> i <= ss + 258 -> i < 65536 -> i < Z.max hw (ss + look).
Proof. unfold HWI4. intros [H|[H|H]] L K Hi Hi'; lia. Qed.
