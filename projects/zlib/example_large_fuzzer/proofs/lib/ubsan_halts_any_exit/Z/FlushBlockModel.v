(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Trees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ScanModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import CompressModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Section Keep.
Context {A : Type} (g : deflate_state -> A).

Variables wb wi : bool.

Record keeps : Prop := {
  k_tree_fc : forall s t a, g (set_tree_fc s t a) = g s;
  k_tree_dl : forall s t a, g (set_tree_dl s t a) = g s;
  k_heap : forall s a, g (set_heap s a) = g s;
  k_heap_len : forall s v, g (set_heap_len s v) = g s;
  k_heap_max : forall s v, g (set_heap_max s v) = g s;
  k_depth : forall s a, g (set_depth s a) = g s;
  k_bl_count : forall s a, g (set_bl_count s a) = g s;
  k_max_code : forall s t v, g (set_max_code s t v) = g s;
  k_opt_len : forall s v, g (set_opt_len s v) = g s;
  k_static_len : forall s v, g (set_static_len s v) = g s;
  k_sym_next : wi = true -> forall s v, g (set_sym_next s v) = g s;
  k_matches : wi = true -> forall s v, g (set_matches s v) = g s;
  k_bi_buf : wb = true -> forall s v, g (set_bi_buf s v) = g s;
  k_bi_valid : wb = true -> forall s v, g (set_bi_valid s v) = g s;
  k_pending : wb = true -> forall s v, g (set_pending s v) = g s;
  k_pending_buf : wb = true -> forall s a, g (set_pending_buf s a) = g s }.

Hypothesis K : keeps.

Local Ltac kr := rewrite ?(k_tree_fc K), ?(k_tree_dl K), ?(k_heap K), ?(k_heap_len K), ?(k_heap_max K), ?(k_depth K),
  ?(k_bl_count K), ?(k_max_code K), ?(k_opt_len K), ?(k_static_len K), ?(k_sym_next K), ?(k_matches K),
  ?(k_bi_buf K), ?(k_bi_valid K), ?(k_pending K), ?(k_pending_buf K).

Lemma k_heap_set : forall s i v, g (heap_set s i v) = g s.
Proof. intros. unfold heap_set. apply (k_heap K). Qed.
Lemma k_depth_set : forall s i v, g (depth_set s i v) = g s.
Proof. intros. unfold depth_set. apply (k_depth K). Qed.
Lemma k_bl_count_set : forall s i v, g (bl_count_set s i v) = g s.
Proof. intros. unfold bl_count_set. apply (k_bl_count K). Qed.
Lemma k_set_Freq : forall s t n v, g (set_Freq s t n v) = g s.
Proof. intros. unfold set_Freq. apply (k_tree_fc K). Qed.
Lemma k_set_Len : forall s t n v, g (set_Len s t n v) = g s.
Proof. intros. unfold set_Len, set_Dad. apply (k_tree_dl K). Qed.
Lemma k_set_Dad : forall s t n v, g (set_Dad s t n v) = g s.
Proof. intros. unfold set_Dad. apply (k_tree_dl K). Qed.
Lemma k_put_byte (WB : wb = true) : forall s c, g (put_byte s c) = g s.
Proof. intros. unfold put_byte. rewrite (k_pending K WB), (k_pending_buf K WB). reflexivity. Qed.
Lemma k_put_short (WB : wb = true) : forall s w, g (put_short s w) = g s.
Proof. intros. unfold put_short. rewrite !(k_put_byte WB). reflexivity. Qed.
Lemma k_send_bits (WB : wb = true) : forall s v l, g (send_bits s v l) = g s.
Proof.
  intros. unfold send_bits. destruct (Buf_size - l <? ds_bi_valid s).
  - rewrite (k_bi_valid K WB), (k_bi_buf K WB), (k_put_short WB), (k_bi_buf K WB). reflexivity.
  - rewrite (k_bi_valid K WB), (k_bi_buf K WB). reflexivity.
Qed.
Lemma k_sbs_run (WB : wb = true) : forall cs s, g (sbs_run s cs) = g s.
Proof. induction cs as [|[v l] cs IH]; intros; [reflexivity|]. cbn. rewrite IH. apply (k_send_bits WB). Qed.
Lemma k_bi_windup (WB : wb = true) : forall s, g (bi_windup s) = g s.
Proof.
  intros. unfold bi_windup. rewrite (k_bi_valid K WB), (k_bi_buf K WB).
  destruct (8 <? ds_bi_valid s); [apply (k_put_short WB)|]. destruct (0 <? ds_bi_valid s); [apply (k_put_byte WB) | reflexivity].
Qed.
Lemma k_bi_flush (WB : wb = true) : forall s, g (bi_flush s) = g s.
Proof.
  intros. unfold bi_flush. destruct (ds_bi_valid s =? 16).
  - rewrite (k_bi_valid K WB), (k_bi_buf K WB). apply (k_put_short WB).
  - destruct (8 <=? ds_bi_valid s); [|reflexivity]. rewrite (k_bi_valid K WB), (k_bi_buf K WB). apply (k_put_byte WB).
Qed.

Lemma k_pqdownheap : forall s t k, g (pqdownheap s t k) = g s.
Proof. intros. rewrite pqdownheap_shape. apply (k_heap K). Qed.

Lemma k_loop1 : forall f s t e n mc, g (fst (build_tree_loop1 f s t e n mc)) = g s.
Proof.
  induction f as [|f IH]; intros; cbn [build_tree_loop1]; [reflexivity|].
  destruct (n <? e); [|reflexivity]. destruct (negb (Freq s t n =? 0)).
  - rewrite IH. rewrite k_depth_set, k_heap_set, (k_heap_len K). reflexivity.
  - rewrite IH. apply k_set_Len.
Qed.
Lemma k_loop2 : forall f s t mc, g (fst (build_tree_loop2 f s t mc)) = g s.
Proof.
  induction f as [|f IH]; intros; cbn [build_tree_loop2]; [reflexivity|].
  destruct (ds_heap_len s <? 2); [|reflexivity].
  destruct (if mc <? 2 then (mc + 1, mc + 1) else (0, mc)) as [node mc'].
  rewrite IH. destruct (stree_has t); rewrite ?(k_static_len K), (k_opt_len K), k_depth_set, k_set_Freq, k_heap_set, (k_heap_len K); reflexivity.
Qed.
Lemma k_loop3 : forall f s t n, g (build_tree_loop3 f s t n) = g s.
Proof.
  induction f as [|f IH]; intros; cbn [build_tree_loop3]; [reflexivity|].
  destruct (1 <=? n); [|reflexivity]. rewrite IH. apply k_pqdownheap.
Qed.
Lemma k_loop4 : forall f s t node, g (build_tree_loop4 f s t node) = g s.
Proof.
  induction f as [|f IH]; intros; cbn [build_tree_loop4]; [reflexivity|].
  match goal with |- g (if ?c then ?a else ?b) = _ => destruct c end;
  rewrite ?IH, k_pqdownheap, k_heap_set, !k_set_Dad, k_depth_set, k_set_Freq, !k_heap_set, !(k_heap_max K), k_heap_set,
    (k_heap_max K), k_pqdownheap, (k_heap_len K), k_heap_set; reflexivity.
Qed.
Lemma k_gb1 : forall f s t mc b ml h ov, g (fst (gen_bitlen_loop1 f s t mc b ml h ov)) = g s.
Proof.
  induction f as [|f IH]; intros; cbn [gen_bitlen_loop1]; [reflexivity|].
  destruct (h <? HEAP_SIZE); [|reflexivity].
  destruct (if ml <? Len s t (Dad s t (heap_get s h)) + 1 then (ml, ov + 1) else (Len s t (Dad s t (heap_get s h)) + 1, ov)) as [bits ov'].
  destruct (mc <? heap_get s h).
  - rewrite IH. apply k_set_Len.
  - rewrite IH. destruct (stree_has t); rewrite ?(k_static_len K), (k_opt_len K), k_bl_count_set, k_set_Len; reflexivity.
Qed.
Lemma k_gb2 : forall f s ml ov, g (gen_bitlen_loop2 f s ml ov) = g s.
Proof.
  induction f as [|f IH]; intros; cbn [gen_bitlen_loop2]; [reflexivity|].
  destruct (0 <? ov - 2); rewrite ?IH, !k_bl_count_set; reflexivity.
Qed.
Lemma k_gb3i : forall f s t mc bits n h, g (fst (gen_bitlen_loop3i f s t mc bits n h)) = g s.
Proof.
  induction f as [|f IH]; intros; cbn [gen_bitlen_loop3i]; [reflexivity|].
  destruct (negb (n =? 0)); [|reflexivity]. destruct (mc <? heap_get s (h - 1)); [apply IH|].
  rewrite IH. destruct (negb (Len s t (heap_get s (h - 1)) =? bits)); [|reflexivity].
  rewrite k_set_Len, (k_opt_len K). reflexivity.
Qed.
Lemma k_gb3 : forall f s t mc bits h, g (gen_bitlen_loop3 f s t mc bits h) = g s.
Proof.
  induction f as [|f IH]; intros; cbn [gen_bitlen_loop3]; [reflexivity|].
  destruct (negb (bits =? 0)); [|reflexivity].
  destruct (gen_bitlen_loop3i 574 s t mc bits (bl_count_get s bits) h) as [s' h'] eqn:E.
  rewrite IH. pose proof (k_gb3i 574 s t mc bits (bl_count_get s bits) h) as H. rewrite E in H. exact H.
Qed.
Lemma k_gen_bitlen : forall s t, g (gen_bitlen s t) = g s.
Proof.
  intros. unfold gen_bitlen.
  destruct (gen_bitlen_loop1 573 _ t _ _ _ _ 0) as [s1 ov] eqn:E1.
  match type of E1 with gen_bitlen_loop1 ?f ?s0 ?t' ?mc ?b ?ml ?h ?o = _ => pose proof (k_gb1 f s0 t' mc b ml h o) as H1 end.
  rewrite E1 in H1. cbn [fst] in H1.
  destruct (ov =? 0).
  - rewrite H1. rewrite k_set_Len, (k_bl_count K). reflexivity.
  - rewrite k_gb3, k_gb2, H1, k_set_Len, (k_bl_count K). reflexivity.
Qed.
Lemma k_gc2 : forall f s t nc mc n, g (gen_codes_loop2 f s t nc mc n) = g s.
Proof.
  induction f as [|f IH]; intros; cbn [gen_codes_loop2]; [reflexivity|].
  destruct (n <=? mc); [|reflexivity]. destruct (Len s t n =? 0); [apply IH|].
  rewrite IH. unfold set_Code. apply k_set_Freq.
Qed.
Lemma k_gen_codes : forall s t mc, g (gen_codes s t mc) = g s.
Proof. intros. unfold gen_codes. apply k_gc2. Qed.

Lemma k_build_tree : forall s t, g (build_tree s t) = g s.
Proof.
  intros. unfold build_tree.
  destruct (build_tree_loop1 _ _ t _ 0 (-1)) as [s1 mc1] eqn:E1.
  destruct (build_tree_loop2 2 s1 t mc1) as [s2 mc] eqn:E2.
  rewrite k_gen_codes, k_gen_bitlen, k_heap_set, (k_heap_max K), k_loop4, k_loop3, (k_max_code K).
  pose proof (k_loop2 2 s1 t mc1) as H2. rewrite E2 in H2. cbn [fst] in H2. rewrite H2.
  match type of E1 with build_tree_loop1 ?f ?s0 _ ?e _ _ = _ => pose proof (k_loop1 f s0 t e 0 (-1)) as H1 end.
  rewrite E1 in H1. cbn [fst] in H1. rewrite H1. rewrite (k_heap_max K), (k_heap_len K). reflexivity.
Qed.

Lemma k_scan_loop : forall f s t mc n p q c mx mn, g (scan_tree_loop f s t mc n p q c mx mn) = g s.
Proof.
  induction f as [|f IH]; intros; cbn [scan_tree_loop]; [reflexivity|].
  destruct (n <=? mc); [|reflexivity]. cbv zeta.
  destruct ((c + 1 <? mx) && (q =? Len s t (n + 1))); [apply IH|].
  destruct (tree_counts q (Len s t (n + 1))) as [mx' mn'].
  rewrite IH.
  repeat first [ rewrite k_set_Freq | match goal with |- g (if ?c then _ else _) = _ => destruct c end ]; reflexivity.
Qed.
Lemma k_scan_tree : forall s t mc, g (scan_tree s t mc) = g s.
Proof.
  intros. unfold scan_tree. destruct (if Len s t 0 =? 0 then (138, 3) else (7, 4)) as [mx mn].
  rewrite k_scan_loop. apply k_set_Len.
Qed.

Lemma k_send_rep (WB : wb = true) : forall k s c cnt, g (send_tree_rep k s c cnt) = g s.
Proof.
  induction k as [|k IH]; intros; cbn [send_tree_rep]; [reflexivity|].
  destruct (negb (cnt - 1 =? 0)); rewrite ?IH; unfold send_dcode; apply (k_send_bits WB).
Qed.
Lemma k_send_loop (WB : wb = true) : forall f s t mc n p q c mx mn, g (send_tree_loop f s t mc n p q c mx mn) = g s.
Proof.
  induction f as [|f IH]; intros; cbn [send_tree_loop]; [reflexivity|].
  destruct (n <=? mc); [|reflexivity]. cbv zeta.
  destruct ((c + 1 <? mx) && (q =? Len s t (n + 1))); [apply IH|].
  destruct (tree_counts q (Len s t (n + 1))) as [mx' mn'] eqn:ET.
  rewrite IH.
  destruct (c + 1 <? mn); [apply (k_send_rep WB)|].
  destruct (negb (q =? 0)).
  - destruct (negb (q =? p)); cbv beta iota zeta; unfold send_dcode; rewrite !(k_send_bits WB); reflexivity.
  - destruct (c + 1 <=? 10); unfold send_dcode; rewrite !(k_send_bits WB); reflexivity.
Qed.
Lemma k_send_tree (WB : wb = true) : forall s t mc, g (send_tree s t mc) = g s.
Proof.
  intros. unfold send_tree. destruct (if Len s t 0 =? 0 then (138, 3) else (7, 4)) as [mx mn]. apply (k_send_loop WB).
Qed.

Lemma k_send_all_loop (WB : wb = true) : forall f s bc r, g (send_all_trees_loop f s bc r) = g s.
Proof.
  induction f as [|f IH]; intros; cbn [send_all_trees_loop]; [reflexivity|].
  destruct (r <? bc); [|reflexivity]. rewrite IH. apply (k_send_bits WB).
Qed.
Lemma k_send_all_trees (WB : wb = true) : forall s a b c, g (send_all_trees s a b c) = g s.
Proof. intros. unfold send_all_trees. rewrite !(k_send_tree WB), (k_send_all_loop WB), !(k_send_bits WB). reflexivity. Qed.

Lemma k_cb_loop (WB : wb = true) : forall f s lfc ldl dfc ddl sx, g (compress_block_loop f s lfc ldl dfc ddl sx) = g s.
Proof.
  induction f as [|f IH]; intros; [reflexivity|].
  rewrite cb_loop_S. cbv zeta.
  match goal with |- g (if ?c then _ else _) = _ => destruct c end; rewrite ?IH; apply (k_sbs_run WB).
Qed.
Lemma k_compress_block (WB : wb = true) : forall s lfc ldl dfc ddl, g (compress_block s lfc ldl dfc ddl) = g s.
Proof.
  intros. unfold compress_block, send_code. rewrite (k_send_bits WB).
  destruct (negb (ds_sym_next s =? 0)); [apply (k_cb_loop WB) | reflexivity].
Qed.

Lemma k_init_block (WI : wi = true) : forall s, g (init_block s) = g s.
Proof.
  intros. unfold init_block.
  rewrite (k_matches K WI), (k_sym_next K WI), (k_static_len K), (k_opt_len K), k_set_Freq.
  change (set_bl_tree_fc ?s ?a) with (set_tree_fc s TB a). rewrite (k_tree_fc K).
  change (set_dyn_dtree_fc ?s ?a) with (set_tree_fc s TD a). rewrite (k_tree_fc K).
  change (set_dyn_ltree_fc ?s ?a) with (set_tree_fc s TL a). apply (k_tree_fc K).
Qed.

Lemma k_tr_stored_block (WB : wb = true) : forall s buf len last, g (tr_stored_block s buf len last) = g s.
Proof.
  intros. unfold tr_stored_block. rewrite (k_pending K WB).
  destruct (negb (len =? 0)); [destruct buf|]; rewrite ?(k_pending_buf K WB), !(k_put_short WB), (k_bi_windup WB), (k_send_bits WB); reflexivity.
Qed.
End Keep.


Local Ltac keeps_tac := constructor; intros; try match goal with tt : tree_id |- _ => destruct tt end; match goal with ss : deflate_state |- _ => destruct ss; reflexivity end.

Lemma keeps_strm : keeps ds_strm true true.                 Proof. keeps_tac. Qed.
Lemma keeps_window : keeps ds_window true true.             Proof. keeps_tac. Qed.

Lemma keeps_lit_bufsize : keeps ds_lit_bufsize true true.   Proof. keeps_tac. Qed.
Lemma keeps_w_size : keeps ds_w_size true true.             Proof. keeps_tac. Qed.
Lemma keeps_sym_next : keeps ds_sym_next true false.
Proof. constructor; intros; try discriminate; try match goal with tt : tree_id |- _ => destruct tt end; match goal with ss : deflate_state |- _ => destruct ss; reflexivity end. Qed.

Definition bits4 (s : deflate_state) : Z * Z * Z * Z :=
  (ds_bi_valid s, ds_bi_buf s, ds_pending s, arr_len (ds_pending_buf s)).
Lemma keeps_bits4 : keeps bits4 false true.
Proof. constructor; intros; try discriminate; try match goal with tt : tree_id |- _ => destruct tt end; match goal with ss : deflate_state |- _ => destruct ss; reflexivity end. Qed.
Lemma bits4_set_strm : forall s c, bits4 (set_strm s c) = bits4 s.
Proof. intros. destruct s; reflexivity. Qed.
Lemma bits4_set_opt_len : forall s v, bits4 (set_opt_len s v) = bits4 s.
Proof. intros. destruct s; reflexivity. Qed.
Lemma BINV_bits4 : forall PBL s s', bits4 s' = bits4 s -> BINV PBL s -> BINV PBL s'.
Proof. intros PBL s s' E H. unfold BINV in *. unfold bits4 in E. injection E as E1 E2 E3 E4. rewrite E1, E2, E3. exact H. Qed.

Definition trees8 (s : deflate_state) :=
  (ds_dyn_ltree_fc s, ds_dyn_ltree_dl s, ds_dyn_dtree_fc s, ds_dyn_dtree_dl s, ds_bl_tree_fc s, ds_bl_tree_dl s,
   ds_l_max_code s, ds_d_max_code s).
Lemma trees8_upd4 : forall s A P B V, trees8 (upd4 s A P B V) = trees8 s.
Proof. intros. destruct s; reflexivity. Qed.
Lemma trees8_send_bits : forall s v l, trees8 (send_bits s v l) = trees8 s.
Proof. intros. rewrite send_bits_shape. apply trees8_upd4. Qed.
Lemma trees8_sbs_run : forall cs s, trees8 (sbs_run s cs) = trees8 s.
Proof. induction cs as [|[v l] cs IH]; intros; [reflexivity|]. cbn. rewrite IH. apply trees8_send_bits. Qed.

Definition tfb_X0 (s : deflate_state) : deflate_state :=
  if (0 <? ds_level s) && (cs_data_type (ds_strm s) =? Z_UNKNOWN)
  then set_strm s (cset_data_type (ds_strm s) (detect_data_type s)) else s.

Lemma k_tr_flush_block : forall {A} (g : deflate_state -> A), keeps g true true ->
  forall s buf len last, g (tr_flush_block s buf len last) = g (tfb_X0 s).
Proof.
  intros A g K s buf len last. unfold tr_flush_block, tfb_X0.
  remember (if cs_data_type (ds_strm s) =? Z_UNKNOWN
            then set_strm s (cset_data_type (ds_strm s) (detect_data_type s)) else s) as s0 eqn:E0.
  cbv zeta.
  destruct (build_bl_tree (build_tree (build_tree s0 TL) TD)) as [s5 mb] eqn:E5.
  unfold build_bl_tree in E5. cbv zeta in E5. apply (f_equal fst) in E5. cbn [fst] in E5.
  assert (H5 : g s5 = g s0).
  { rewrite <- E5. rewrite (k_opt_len _ _ _ K), !(k_build_tree _ _ _ K), !(k_scan_tree _ _ _ K), !(k_build_tree _ _ _ K). reflexivity. }
  destruct (0 <? ds_level s); cbn [andb]; cbv beta iota.
  - match goal with |- g (if ?c then _ else _) = _ => destruct c end;
    rewrite ?(k_bi_windup _ _ _ K eq_refl), (k_init_block _ _ _ K eq_refl);
    match goal with |- g (if ?c then _ else _) = _ => destruct c end;
    try (match goal with |- g (if ?c then _ else _) = _ => destruct c end);
    rewrite ?(k_tr_stored_block _ _ _ K eq_refl), ?(k_compress_block _ _ _ K eq_refl), ?(k_send_all_trees _ _ _ K eq_refl), ?(k_send_bits _ _ _ K eq_refl), H5, E0; reflexivity.
  - subst s0.
    match goal with |- g (if ?c then _ else _) = _ => destruct c end;
    rewrite ?(k_bi_windup _ _ _ K eq_refl), (k_init_block _ _ _ K eq_refl);
    match goal with |- g (if ?c then _ else _) = _ => destruct c end;
    try (match goal with |- g (if ?c then _ else _) = _ => destruct c end);
    rewrite ?(k_tr_stored_block _ _ _ K eq_refl), ?(k_compress_block _ _ _ K eq_refl), ?(k_send_all_trees _ _ _ K eq_refl), ?(k_send_bits _ _ _ K eq_refl); reflexivity.
Qed.

Lemma set_strm_strm : forall s c, ds_strm (set_strm s c) = c.
Proof. intros s c. destruct s; reflexivity. Qed.

Lemma tr_flush_block_strm : forall s buf len last,
  ds_strm (tr_flush_block s buf len last) =
    if (0 <? ds_level s) && (cs_data_type (ds_strm s) =? Z_UNKNOWN)
    then cset_data_type (ds_strm s) (detect_data_type s) else ds_strm s.
Proof.
  intros. rewrite (k_tr_flush_block ds_strm keeps_strm). unfold tfb_X0.
  destruct (_ && _); [apply set_strm_strm | reflexivity].
Qed.


Fixpoint bl_calls (s : deflate_state) (r : Z) (n : nat) : list (Z * Z) :=
  match n with
  | O => []
  | S n' => (Len s TB (arr_get bl_order_a r), 3) :: bl_calls s (r + 1) n'
  end.

Lemma bl_calls_ext : forall s s' r n, (forall c, Len s' TB c = Len s TB c) -> bl_calls s' r n = bl_calls s r n.
Proof. intros s s' r n H. revert r. induction n; intros; cbn; [reflexivity|]. rewrite H, IHn. reflexivity. Qed.

Lemma send_all_loop_fuel : forall f s bc r, (Z.to_nat (bc - r) <= f)%nat ->
  send_all_trees_loop f s bc r = sbs_run s (bl_calls s r (Z.to_nat (bc - r))).
Proof.
  induction f as [|f IH]; intros s bc r Hf.
  - replace (Z.to_nat (bc - r)) with 0%nat by lia. reflexivity.
  - cbn [send_all_trees_loop]. destruct (Z.ltb_spec r bc).
    + replace (Z.to_nat (bc - r)) with (S (Z.to_nat (bc - (r + 1)))) by lia. cbn [bl_calls sbs_run].
      rewrite IH by lia. rewrite (bl_calls_ext s (send_bits s (Len s TB (arr_get bl_order_a r)) 3)) by (intros; apply sb_Len).
      reflexivity.
    + replace (Z.to_nat (bc - r)) with 0%nat by lia. reflexivity.
Qed.

Definition sat_calls (s : deflate_state) (lcodes dcodes blcodes : Z) : list (Z * Z) :=
  [(lcodes - 257, 5); (dcodes - 1, 5); (blcodes - 4, 4)] ++ bl_calls s 0 (Z.to_nat blcodes).

Lemma send_all_trees_eq : forall s lc dc bc, 0 <= bc <= 19 ->
  send_all_trees s lc dc bc =
    send_tree (send_tree (sbs_run s (sat_calls s lc dc bc)) TL (lc - 1)) TD (dc - 1).
Proof.
  intros s lc dc bc Hbc. unfold send_all_trees, sat_calls. cbv zeta.
  rewrite send_all_loop_fuel by lia. replace (bc - 0) with bc by lia.
  rewrite sbs_run_app. cbn [sbs_run].
  set (s3 := send_bits (send_bits (send_bits s (lc - 257) 5) (dc - 1) 5) (bc - 4) 4).
  rewrite (bl_calls_ext s s3) by (intros; subst s3; rewrite !sb_Len; reflexivity). reflexivity.
Qed.


Lemma build_bl_tree_loop_range : forall f s mb, 2 <= mb -> 2 <= build_bl_tree_loop f s mb <= mb.
Proof.
  induction f as [|f IH]; intros s mb H; cbn [build_bl_tree_loop]; [lia|].
  destruct (Z.leb_spec 3 mb); [|lia].
  destruct (negb (Len s TB (arr_get bl_order_a mb) =? 0)); [lia|].
  specialize (IH s (mb - 1) ltac:(lia)). lia.
Qed.



Definition is_some (buf : option Z) : bool := match buf with Some _ => true | None => false end.

Definition tfb_X5 (X0 : deflate_state) : deflate_state :=
  let X1 := build_tree X0 TL in
  let X2 := build_tree X1 TD in
  let X3 := scan_tree X2 TL (ds_l_max_code X2) in
  let X4 := scan_tree X3 TD (ds_d_max_code X3) in
  build_tree X4 TB.
Definition tfb_mb (X5 : deflate_state) : Z := build_bl_tree_loop 17%nat X5 18.
Definition tfb_X6 (X5 : deflate_state) (mb : Z) : deflate_state :=
  set_opt_len X5 (wrap64 (ds_opt_len X5 + 3 * (mb + 1) + 5 + 5 + 4)).

Definition tfb_branch (X6 : deflate_state) (buf : option Z) (len : Z) : Z :=
  let opt_lenb := Z.shiftr (wrap64 (ds_opt_len X6 + 3 + 7)) 3 in
  let static_lenb := Z.shiftr (wrap64 (ds_static_len X6 + 3 + 7)) 3 in
  let opt_lenb' := if (static_lenb <=? opt_lenb) || (ds_strategy X6 =? Z_FIXED) then static_lenb else opt_lenb in
  if (wrap64 (len + 4) <=? opt_lenb') && is_some buf then 2
  else if static_lenb =? opt_lenb' then 0 else 1.

Definition tfb_emit (d : Z) (X6 : deflate_state) (mb : Z) (buf : option Z) (len last : Z) : deflate_state :=
  if d =? 2 then tr_stored_block X6 buf len last
  else if d =? 0 then
    compress_block (send_bits X6 (Z.shiftl STATIC_TREES 1 + last) 3) static_ltree_fc static_ltree_dl static_dtree_fc static_dtree_dl
  else
    let s := send_bits X6 (Z.shiftl DYN_TREES 1 + last) 3 in
    let s := send_all_trees s (ds_l_max_code s + 1) (ds_d_max_code s + 1) (mb + 1) in
    compress_block s (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) (ds_dyn_dtree_fc s) (ds_dyn_dtree_dl s).

Definition tfb_pre (s : deflate_state) (buf : option Z) (len last : Z) : deflate_state :=
  if 0 <? ds_level s then
    let X6 := tfb_X6 (tfb_X5 (tfb_X0 s)) (tfb_mb (tfb_X5 (tfb_X0 s))) in
    tfb_emit (tfb_branch X6 buf len) X6 (tfb_mb (tfb_X5 (tfb_X0 s))) buf len last
  else
    tfb_emit (if (wrap64 (len + 4) <=? wrap64 (len + 5)) && is_some buf then 2 else 0) s 0 buf len last.

Definition tfb_fin (last : Z) (pre : deflate_state) : deflate_state :=
  let s' := init_block pre in if negb (last =? 0) then bi_windup s' else s'.

Strategy expand [tfb_X0 tfb_X5 tfb_mb tfb_X6 tfb_branch tfb_emit tfb_pre tfb_fin is_some].

Lemma tfb_emit_cases : forall (c1 c2 : bool) X6 mb buf len last,
  tfb_emit (if c1 then 2 else if c2 then 0 else 1) X6 mb buf len last =
    if c1 then tr_stored_block X6 buf len last
    else if c2 then compress_block (send_bits X6 (Z.shiftl STATIC_TREES 1 + last) 3) static_ltree_fc static_ltree_dl static_dtree_fc static_dtree_dl
    else
      let s := send_bits X6 (Z.shiftl DYN_TREES 1 + last) 3 in
      let s := send_all_trees s (ds_l_max_code s + 1) (ds_d_max_code s + 1) (mb + 1) in
      compress_block s (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) (ds_dyn_dtree_fc s) (ds_dyn_dtree_dl s).
Proof. intros. destruct c1, c2; reflexivity. Qed.

Lemma tfb_emit_cases0 : forall (c : bool) X mb buf len last,
  tfb_emit (if c then 2 else 0) X mb buf len last =
    if c then tr_stored_block X buf len last
    else compress_block (send_bits X (Z.shiftl STATIC_TREES 1 + last) 3) static_ltree_fc static_ltree_dl static_dtree_fc static_dtree_dl.
Proof. intros. destruct c; reflexivity. Qed.

Lemma build_bl_tree_tfb : forall X0,
  build_bl_tree (build_tree (build_tree X0 TL) TD) = (tfb_X6 (tfb_X5 X0) (tfb_mb (tfb_X5 X0)), tfb_mb (tfb_X5 X0)).
Proof.
  intros X0. unfold build_bl_tree, tfb_X6, tfb_X5, tfb_mb. cbv zeta.
  replace (BL_CODES - 1) with 18 by reflexivity.
  match goal with |- ?a = ?b => constr_eq a b; exact (@eq_refl _ a) end.
Qed.

Lemma tr_flush_block_eq : forall s buf len last,
  tr_flush_block s buf len last = tfb_fin last (tfb_pre s buf len last).
Proof.
  intros s buf len last. unfold tr_flush_block, tfb_pre, tfb_X0.
  destruct (0 <? ds_level s); cbn [andb].
  - remember (if cs_data_type (ds_strm s) =? Z_UNKNOWN
              then set_strm s (cset_data_type (ds_strm s) (detect_data_type s)) else s) as X0 eqn:E0.
    cbv zeta. rewrite build_bl_tree_tfb. cbv beta iota zeta.
    set (s5 := tfb_X6 (tfb_X5 X0) (tfb_mb (tfb_X5 X0))). set (mb := tfb_mb (tfb_X5 X0)) in *.
    match goal with |- (if _ then bi_windup (init_block ?P) else _) = _ => set (PRE := P) end.
    change (tfb_fin last PRE = tfb_fin last (tfb_emit (tfb_branch s5 buf len) s5 mb buf len last)).
    apply (f_equal (tfb_fin last)). subst PRE.
    unfold tfb_branch, is_some. cbv zeta. rewrite tfb_emit_cases. cbv zeta.
    match goal with |- ?a = ?b => constr_eq a b; exact (@eq_refl deflate_state a) end.
  - cbv beta iota zeta.
    match goal with |- (if _ then bi_windup (init_block ?P) else _) = _ => set (PRE := P) end.
    change (tfb_fin last PRE = tfb_fin last (tfb_emit (if (wrap64 (len + 4) <=? wrap64 (len + 5)) && is_some buf then 2 else 0) s 0 buf len last)).
    apply (f_equal (tfb_fin last)). subst PRE.
    unfold is_some. rewrite tfb_emit_cases0.
    destruct (wrap64 (len + 5) =? wrap64 (len + 5)) eqn:E; [| exfalso; rewrite Z.eqb_refl in E; discriminate E].
    cbv beta iota. match goal with |- ?a = ?b => constr_eq a b; exact (@eq_refl deflate_state a) end.
Qed.


Lemma trees8_send_loop : forall f s t mc n p q c mx mn, 1 <= mn ->
  trees8 (send_tree_loop f s t mc n p q c mx mn) = trees8 s.
Proof.
  induction f as [|f IH]; intros s t mc n p q c mx mn Hmn; [reflexivity|].
  rewrite send_loop_S by exact Hmn.
  destruct (n <=? mc); [|reflexivity]. cbv zeta.
  destruct ((c + 1 <? mx) && (q =? Len s t (n + 1))); [apply IH; exact Hmn|].
  destruct (tree_counts q (Len s t (n + 1))) as [mx' mn'] eqn:E.
  pose proof (tree_counts_range _ _ _ _ E) as [_ Hmn'].
  rewrite IH by lia. apply trees8_sbs_run.
Qed.

Lemma trees8_send_tree : forall s t mc, trees8 (send_tree s t mc) = trees8 s.
Proof.
  intros s t mc. unfold send_tree. destruct (Len s t 0 =? 0); apply trees8_send_loop; lia.
Qed.

Lemma tfb_emit_2 : forall X mb buf len last, tfb_emit 2 X mb buf len last = tr_stored_block X buf len last.
Proof. reflexivity. Qed.
Lemma tfb_emit_0 : forall X mb buf len last,
  tfb_emit 0 X mb buf len last = compress_block (send_bits X (2 + last) 3) static_ltree_fc static_ltree_dl static_dtree_fc static_dtree_dl.
Proof. reflexivity. Qed.
