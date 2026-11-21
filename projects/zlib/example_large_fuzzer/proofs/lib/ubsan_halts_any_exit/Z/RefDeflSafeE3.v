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
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import CompressModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ScanModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FlushBlockModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import BuildTreeModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import GenBitlenModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import GenCodesModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeZ.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeB1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeB3.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeB4.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeB5.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeB6.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateOverlay.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeE1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeE2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac fit3_l2_prune :=
  repeat match goal with
         | H : _ \/ _ |- _ => clear H
         | H : ?fit3A -> ?fit3B |- _ => clear H
         | H : _ <-> _ |- _ => clear H
         | H : exists _, _ |- _ => clear H
         end.
Local Ltac lia ::= first [ solve [ fit3_l2_prune; Zify.zify; xlia zchecker ] | Zify.zify; xlia zchecker ].

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Lemma detect_loop1_range : forall f s n m r, detect_loop1 f s n m = Some r -> r = Z_BINARY.
Proof.
  induction f as [|f IH]; intros s n m r H; cbn [detect_loop1] in H; [discriminate|].
  destruct (Z.leb n 31); [|discriminate].
  destruct (_ && _); [injection H; intros <-; reflexivity | exact (IH _ _ _ _ H)].
Qed.

Lemma detect_loop2_range : forall f s n r, detect_loop2 f s n = Some r -> r = Z_TEXT.
Proof.
  induction f as [|f IH]; intros s n r H; cbn [detect_loop2] in H; [discriminate|].
  destruct (Z.ltb n LITERALS); [|discriminate].
  destruct (negb _); [injection H; intros <-; reflexivity | exact (IH _ _ _ H)].
Qed.

Lemma detect_data_type_range : forall s, 0 <= detect_data_type s <= 1.
Proof.
  intros s. unfold detect_data_type.
  destruct (detect_loop1 32 s 0 4093624447) eqn:E1; [apply detect_loop1_range in E1; subst; unfold Z_BINARY; lia|].
  destruct (_ || _); [unfold Z_TEXT; lia|].
  destruct (detect_loop2 224 s 32) eqn:E2; [apply detect_loop2_range in E2; subst|]; unfold Z_BINARY, Z_TEXT; lia.
Qed.

Lemma tfb_X0_eq : forall s, exists dt,
  tfb_X0 s = set_strm s (cset_data_type (ds_strm s) dt) /\ (dt = cs_data_type (ds_strm s) \/ 0 <= dt <= 1).
Proof.
  intros s. unfold tfb_X0.
  destruct ((0 <? ds_level s) && (cs_data_type (ds_strm s) =? Z_UNKNOWN)).
  - exists (detect_data_type s). split; [reflexivity | right; apply detect_data_type_range].
  - exists (cs_data_type (ds_strm s)). split; [| left; reflexivity]. destruct s; cbn; match goal with |- context [cset_data_type ?c _] => destruct c; reflexivity end.
Qed.

Definition nt_view (s : deflate_state) :=
  (ds_pending_buf s, ds_pending s, ds_bi_buf s, ds_bi_valid s, ds_lit_bufsize s, ds_sym_next s, ds_pending_out s,
   (ds_level s, ds_strategy s, ds_block_start s, ds_strstart s, ds_matches s, ds_window s, ds_w_size s, ds_lookahead s, ds_match_length s)).

Lemma nt_view_facts : forall a b, nt_view b = nt_view a ->
  ds_pending_buf b = ds_pending_buf a /\ ds_pending b = ds_pending a /\ ds_bi_buf b = ds_bi_buf a /\ ds_bi_valid b = ds_bi_valid a
  /\ ds_lit_bufsize b = ds_lit_bufsize a /\ ds_sym_next b = ds_sym_next a /\ ds_pending_out b = ds_pending_out a
  /\ ds_level b = ds_level a /\ ds_strategy b = ds_strategy a /\ ds_block_start b = ds_block_start a /\ ds_strstart b = ds_strstart a
  /\ ds_matches b = ds_matches a /\ ds_window b = ds_window a /\ ds_w_size b = ds_w_size a /\ ds_lookahead b = ds_lookahead a
  /\ ds_match_length b = ds_match_length a.
Proof. intros a b E. unfold nt_view in E. injection E. intros. repeat split; assumption. Qed.

Lemma nt_view_set_strm : forall s c, nt_view (set_strm s c) = nt_view s.
Proof. intros; destruct s; reflexivity. Qed.
Lemma nt_view_bt_upd : forall s t FC DL HP HL HM DP BC OL SL MC, nt_view (bt_upd s t FC DL HP HL HM DP BC OL SL MC) = nt_view s.
Proof. intros; destruct s, t; reflexivity. Qed.
Lemma nt_view_sbf : forall s b, nt_view (set_bl_tree_fc s b) = nt_view s.
Proof. intros; destruct s; reflexivity. Qed.
Lemma nt_view_set_Len : forall s t i v, nt_view (set_Len s t i v) = nt_view s.
Proof. intros s [| |] i v; unfold set_Len, set_Dad; destruct s; reflexivity. Qed.

Lemma strm_bt_upd : forall s t FC DL HP HL HM DP BC OL SL MC, ds_strm (bt_upd s t FC DL HP HL HM DP BC OL SL MC) = ds_strm s.
Proof. intros; destruct s, t; reflexivity. Qed.
Lemma strm_sbf : forall s b, ds_strm (set_bl_tree_fc s b) = ds_strm s.
Proof. intros; destruct s; reflexivity. Qed.
Lemma strm_set_Len : forall s t i v, ds_strm (set_Len s t i v) = ds_strm s.
Proof. intros s [| |] i v; unfold set_Len, set_Dad; destruct s; reflexivity. Qed.

Lemma strm_set_strm : forall s c, ds_strm (set_strm s c) = c.
Proof. intros; destruct s; reflexivity. Qed.

Lemma tree_fc_set_strm : forall s c t, tree_fc (set_strm s c) t = tree_fc s t.
Proof. intros s c [| |]; destruct s; reflexivity. Qed.
Lemma tree_dl_set_strm : forall s c t, tree_dl (set_strm s c) t = tree_dl s t.
Proof. intros s c [| |]; destruct s; reflexivity. Qed.
Lemma depth_set_strm : forall s c, ds_depth (set_strm s c) = ds_depth s.
Proof. intros; destruct s; reflexivity. Qed.
Lemma opt_len_set_strm : forall s c, ds_opt_len (set_strm s c) = ds_opt_len s.
Proof. intros; destruct s; reflexivity. Qed.
Lemma static_len_set_strm : forall s c, ds_static_len (set_strm s c) = ds_static_len s.
Proof. intros; destruct s; reflexivity. Qed.
Lemma tree_lens_set_strm : forall s c, tree_lens s -> tree_lens (set_strm s c).
Proof. intros s c H. unfold tree_lens in *. destruct s; exact H. Qed.

Lemma max_code_bt_upd : forall x t FC DL HP HL HM DP BC OL SL MC, max_code (bt_upd x t FC DL HP HL HM DP BC OL SL MC) t = MC.
Proof. intros x [| |]; intros; destruct x; reflexivity. Qed.
Lemma max_code_bt_other : forall s t t' FC DL HP HL HM DP BC OL SL MC, t' <> t ->
  max_code (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t' = max_code s t'.
Proof. intros s [| |] [| |] FC DL HP HL HM DP BC OL SL MC H; try (exfalso; apply H; reflexivity); destruct s; reflexivity. Qed.
Lemma max_code_sbf : forall s b t, max_code (set_bl_tree_fc s b) t = max_code s t.
Proof. intros s b [| |]; destruct s; reflexivity. Qed.
Lemma max_code_set_Len : forall s t i v t', max_code (set_Len s t i v) t' = max_code s t'.
Proof. intros s [| |] i v [| |]; unfold set_Len, set_Dad; destruct s; reflexivity. Qed.
Lemma depth_sbf : forall s b, ds_depth (set_bl_tree_fc s b) = ds_depth s.
Proof. intros; destruct s; reflexivity. Qed.
Lemma depth_set_Len : forall s t i v, ds_depth (set_Len s t i v) = ds_depth s.
Proof. intros s [| |] i v; unfold set_Len, set_Dad; destruct s; reflexivity. Qed.
Lemma opt_len_sbf : forall s b, ds_opt_len (set_bl_tree_fc s b) = ds_opt_len s.
Proof. intros; destruct s; reflexivity. Qed.
Lemma opt_len_set_Len : forall s t i v, ds_opt_len (set_Len s t i v) = ds_opt_len s.
Proof. intros s [| |] i v; unfold set_Len, set_Dad; destruct s; reflexivity. Qed.
Lemma static_len_sbf : forall s b, ds_static_len (set_bl_tree_fc s b) = ds_static_len s.
Proof. intros; destruct s; reflexivity. Qed.
Lemma static_len_set_Len : forall s t i v, ds_static_len (set_Len s t i v) = ds_static_len s.
Proof. intros s [| |] i v; unfold set_Len, set_Dad; destruct s; reflexivity. Qed.

Lemma tree_dl_set_Len_other : forall s t i v t', t' <> t -> tree_dl (set_Len s t i v) t' = tree_dl s t'.
Proof. intros s [| |] i v [| |] H; try (exfalso; apply H; reflexivity); unfold set_Len, set_Dad; destruct s; reflexivity. Qed.
Lemma tree_lens_sbf : forall s b, tree_lens s -> arr_len b = 39 -> tree_lens (set_bl_tree_fc s b).
Proof. intros s b H L. unfold tree_lens in *. destruct s; cbn in *. rewrite L. tauto. Qed.
Lemma tree_lens_set_Len : forall s t i v, tree_lens s -> tree_lens (set_Len s t i v).
Proof.
  intros s t i v H. unfold tree_lens in *. unfold set_Len, set_Dad. destruct t; destruct s; cbn in *; rewrite arr_len_set; exact H.
Qed.

Lemma tree_dl_set_Len_typed : forall s t i v t',
  (forall j, 0 <= arr_get (tree_dl s t') j < 65536) -> forall j, 0 <= arr_get (tree_dl (set_Len s t i v) t') j < 65536.
Proof.
  intros s t i v t' H j. unfold set_Len, set_Dad.
  destruct t, t'; destruct s; cbn [tree_dl set_tree_dl] in *; dsred; rewrite ?arr_get_set;
    first [apply H | destruct (_ && _); [apply wrap16_range | apply H]].
Qed.

Lemma xbits_small' : forall t c, 0 <= c <= 2 -> xbits t c = 0.
Proof.
  intros t c Hc. unfold xbits. destruct t; cbn [sd_extra_base sd_extra_bits].
  - unfold LITERALS. replace (256 + 1 <=? c) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
  - replace (0 <=? c) with true by (symmetry; apply Z.leb_le; lia). rewrite Z.sub_0_r.
    assert (c = 0 \/ c = 1 \/ c = 2) as [->|[->| ->]] by lia; reflexivity.
  - replace (0 <=? c) with true by (symmetry; apply Z.leb_le; lia). rewrite Z.sub_0_r.
    assert (c = 0 \/ c = 1 \/ c = 2) as [->|[->| ->]] by lia; reflexivity.
Qed.

Lemma fold_ge_len : forall (Fl : list Z) (g : Z -> Z),
  (forall f, In f Fl -> 1 <= g f) -> Z.of_nat (length Fl) <= fold_right (fun f acc => g f + acc) 0 Fl.
Proof.
  induction Fl as [|a l IH]; intros g H; cbn [length fold_right]; [lia|].
  pose proof (H a (or_introl eq_refl)). specialize (IH g ltac:(intros f Hf; apply H; right; exact Hf)). lia.
Qed.

Lemma fold_split : forall (Fl : list Z) (g h : Z -> Z),
  fold_right (fun f acc => g f + h f + acc) 0 Fl = fold_right (fun f acc => g f + acc) 0 Fl + fold_right (fun f acc => h f + acc) 0 Fl.
Proof. induction Fl as [|a l IH]; intros; cbn [fold_right]; [lia|]. rewrite IH. lia. Qed.

Lemma fold_zero : forall (Fl : list Z) (h : Z -> Z),
  (forall f, In f Fl -> h f = 0) -> fold_right (fun f acc => h f + acc) 0 Fl = 0.
Proof.
  induction Fl as [|a l IH]; intros h H; cbn [fold_right]; [lia|].
  rewrite (H a (or_introl eq_refl)), IH by (intros f Hf; apply H; right; exact Hf). lia.
Qed.

Lemma if_stree_TL : forall (x y : Z), (if stree_has TL then x else y) = x. Proof. reflexivity. Qed.
Lemma if_stree_TD : forall (x y : Z), (if stree_has TD then x else y) = x. Proof. reflexivity. Qed.
Lemma if_stree_TB : forall (x y : Z), (if stree_has TB then x else y) = y. Proof. reflexivity. Qed.

Lemma Len_eq : forall x t i, Len x t i = arr_get (tree_dl x t) i. Proof. reflexivity. Qed.
Lemma max_code_TL : forall x, max_code x TL = ds_l_max_code x. Proof. reflexivity. Qed.
Lemma max_code_TD : forall x, max_code x TD = ds_d_max_code x. Proof. reflexivity. Qed.
Lemma tree_fc_TL : forall x, tree_fc x TL = ds_dyn_ltree_fc x. Proof. reflexivity. Qed.
Lemma tree_fc_TD : forall x, tree_fc x TD = ds_dyn_dtree_fc x. Proof. reflexivity. Qed.
Lemma tree_fc_TB : forall x, tree_fc x TB = ds_bl_tree_fc x. Proof. reflexivity. Qed.
Lemma tree_dl_TL : forall x, tree_dl x TL = ds_dyn_ltree_dl x. Proof. reflexivity. Qed.
Lemma tree_dl_TD : forall x, tree_dl x TD = ds_dyn_dtree_dl x. Proof. reflexivity. Qed.
Lemma tree_dl_TB : forall x, tree_dl x TB = ds_bl_tree_dl x. Proof. reflexivity. Qed.


Record TPF (s : deflate_state) : Prop := {
  tp_nt6 : nt_view (ov_X6 s) = nt_view s;
  tp_strm6 : ds_strm (ov_X6 s) = ds_strm (ov_X0 s);
  tp_X0 : exists dt, ov_X0 s = set_strm s (cset_data_type (ds_strm s) dt) /\ (dt = cs_data_type (ds_strm s) \/ 0 <= dt <= 1);
  tp_tl6 : tree_lens (ov_X6 s);
  tp_fc6 : forall t i, 0 <= arr_get (tree_fc (ov_X6 s) t) i < 65536;
  tp_dl6 : forall t i, 0 <= arr_get (tree_dl (ov_X6 s) t) i < 65536;
  tp_depth6 : forall i, 0 <= arr_get (ds_depth (ov_X6 s)) i < 256;
  tp_blc6 : forall i, 0 <= i < 16 -> 0 <= arr_get (ds_bl_count (ov_X6 s)) i < 65536;
  tp_lmax : 0 <= ds_l_max_code (ov_X6 s) < L_CODES;
  tp_dmax : 0 <= ds_d_max_code (ov_X6 s) < D_CODES;
  tp_LD : forall i, 0 <= i <= ds_l_max_code (ov_X6 s) -> 0 <= Len (ov_X6 s) TL i <= 15;
  tp_DD : forall i, 0 <= i <= ds_d_max_code (ov_X6 s) -> 0 <= Len (ov_X6 s) TD i <= 15;
  tp_LDall : forall i, 0 <= i < L_CODES -> i <> ds_l_max_code (ov_X6 s) + 1 -> 0 <= Len (ov_X6 s) TL i <= 15;
  tp_DDall : forall i, 0 <= i < D_CODES -> i <> ds_d_max_code (ov_X6 s) + 1 -> 0 <= Len (ov_X6 s) TD i <= 15;
  tp_BD : forall x, 0 <= x < 19 -> 0 <= Len (ov_X6 s) TB x <= 7;
  tp_LDu : forall c, 0 <= c < L_CODES -> arr_get (ds_dyn_ltree_fc s) c <> 0 -> 1 <= Len (ov_X6 s) TL c <= 15 /\ c <= ds_l_max_code (ov_X6 s);
  tp_DDu : forall d, 0 <= d < D_CODES -> arr_get (ds_dyn_dtree_fc s) d <> 0 -> 1 <= Len (ov_X6 s) TD d <= 15 /\ d <= ds_d_max_code (ov_X6 s);
  tp_mb : 2 <= ov_mb s <= 18;
  tp_BC : forall x, 0 <= x < 19 ->
    arr_get (ov_BC s) x = TDcnt (fun i => Len (ov_X6 s) TL i) (ds_l_max_code (ov_X6 s)) x + TDcnt (fun i => Len (ov_X6 s) TD i) (ds_d_max_code (ov_X6 s)) x;
  tp_opt : 0 <= ds_opt_len (ov_X6 s) < 2 ^ 40;
  tp_opt_ge : 14 + 3 * (ov_mb s + 1)
              + zsum (fun x => arr_get (ov_BC s) x * (Len (ov_X6 s) TB x + arr_get extra_blbits_a x)) 0 19
              + zsum (fun c => arr_get (ds_dyn_ltree_fc s) c * (Len (ov_X6 s) TL c + xbits TL c)) 0 (Z.to_nat L_CODES)
              + zsum (fun d => arr_get (ds_dyn_dtree_fc s) d * (Len (ov_X6 s) TD d + xbits TD d)) 0 (Z.to_nat D_CODES)
              <= ds_opt_len (ov_X6 s);
  tp_stat : ds_static_len (ov_X6 s) =
              zsum (fun c => arr_get (ds_dyn_ltree_fc s) c * (stree_Len TL c + xbits TL c)) 0 (Z.to_nat L_CODES)
            + zsum (fun d => arr_get (ds_dyn_dtree_fc s) d * (stree_Len TD d + xbits TD d)) 0 (Z.to_nat D_CODES);
  tp_stat_range : 0 <= ds_static_len (ov_X6 s) < 2 ^ 40;
  tp_h1 : bt_safe (ov_X0 s) TL;
  tp_h2 : bt_safe (ov_X1 s) TD;
  tp_h3 : ds_l_max_code (ov_X2 s) = ds_l_max_code (ov_X6 s);
  tp_h4 : forall i, 0 <= i <= ds_l_max_code (ov_X2 s) -> 0 <= Len (ov_X2 s) TL i <= 15;
  tp_h5 : forall i, 0 <= arr_get (tree_dl (ov_X2 s) TL) i < 65536;
  tp_h6 : forall i, 0 <= arr_get (ds_bl_tree_fc (ov_X2 s)) i < 65536;
  tp_h7 : ds_d_max_code (ov_X3 s) = ds_d_max_code (ov_X6 s);
  tp_h8 : forall i, 0 <= i <= ds_d_max_code (ov_X3 s) -> 0 <= Len (ov_X3 s) TD i <= 15;
  tp_h9 : forall i, 0 <= arr_get (tree_dl (ov_X3 s) TD) i < 65536;
  tp_h10 : forall i, 0 <= arr_get (ds_bl_tree_fc (ov_X3 s)) i < 65536;
  tp_h11 : bt_safe (ov_X4 s) TB;
  tp_h12 : forall i, 0 <= i < 19 -> 0 <= arr_get (ds_bl_tree_dl (ov_X5 s)) i < 16;
  tp_h12' : forall i, 0 <= arr_get (ds_bl_tree_dl (ov_X5 s)) i < 65536;
  tp_h13 : 0 <= ds_opt_len (ov_X5 s) < 2 ^ 63 /\ 0 <= ds_static_len (ov_X5 s) < 2 ^ 63;
  tp_h14 : ds_strategy (ov_X5 s) = ds_strategy s;
  tp_h15 : ds_l_max_code (ov_X5 s) = ds_l_max_code (ov_X6 s) /\ ds_d_max_code (ov_X5 s) = ds_d_max_code (ov_X6 s)
           /\ ds_opt_len (ov_X6 s) = ds_opt_len (ov_X5 s) + 3 * (ov_mb s + 1) + 14
           /\ ds_static_len (ov_X6 s) = ds_static_len (ov_X5 s);
  tp_bp1 : bt_pre (ov_X1 s) TD;
  tp_bp4 : bt_pre (ov_X4 s) TB;
  tp_fc0L : tree_fc (ov_X0 s) TL = ds_dyn_ltree_fc s;
  tp_fc1D : tree_fc (ov_X1 s) TD = ds_dyn_dtree_fc s;
  tp_fc4B : tree_fc (ov_X4 s) TB = ov_BC s;
  tp_len1 : forall i, i <> ds_l_max_code (ov_X6 s) + 1 -> Len (ov_X6 s) TL i = arr_get (tree_dl (ov_X1 s) TL) i;
  tp_len2 : forall i, i <> ds_d_max_code (ov_X6 s) + 1 -> Len (ov_X6 s) TD i = arr_get (tree_dl (ov_X2 s) TD) i;
  tp_len5 : forall i, Len (ov_X6 s) TB i = arr_get (tree_dl (ov_X5 s) TB) i;
  tp_guard1 : Len (ov_X6 s) TL (ds_l_max_code (ov_X6 s) + 1) = 65535;
  tp_guard2 : Len (ov_X6 s) TD (ds_d_max_code (ov_X6 s) + 1) = 65535;
  tp_mc1 : max_code (ov_X1 s) TL = ds_l_max_code (ov_X6 s);
  tp_mc2 : max_code (ov_X2 s) TD = ds_d_max_code (ov_X6 s) }.

Section TreePhase.
Variable s : deflate_state.
Hypothesis OP : overlay_pre s.

Let TLs : tree_lens s := op_tl _ OP.

Lemma bt_pre_X0 : bt_pre (ov_X0 s) TL.
Proof.
  destruct (tfb_X0_eq s) as (dt & E & _). unfold ov_X0. rewrite E. constructor.
  - apply tree_lens_set_strm. exact TLs.
  - intros i. rewrite tree_fc_set_strm. apply (op_fc _ OP).
  - intros i. rewrite tree_dl_set_strm. apply (op_dl _ OP).
  - intros i. rewrite depth_set_strm. apply (op_depth _ OP).
  - rewrite opt_len_set_strm, (op_optlen _ OP). lia.
  - rewrite static_len_set_strm, (op_statlen _ OP). lia.
Qed.

Lemma zsum_bound : forall f lo n B, 0 <= B -> (forall i, lo <= i < lo + Z.of_nat n -> 0 <= f i <= B) -> 0 <= zsum f lo n <= Z.of_nat n * B.
Proof.
  intros f lo n B HB H. split; [apply zsum_nonneg; intros; apply H; assumption|].
  pose proof (zsum_mono f (fun _ => B) lo n ltac:(intros; apply H; assumption)) as M.
  assert (G : forall m l, zsum (fun _ => B) l m = Z.of_nat m * B) by (induction m; intros; [reflexivity | rewrite zsum_snoc, IHm; lia]).
  rewrite G in M. lia.
Qed.

Theorem tree_phase : TPF s.
Proof.
  pose proof OP as [Rlbs Lpb Bpb P0 Rbv Rlv Rst SN RN SY FH OL0 SL0 TL0 TFC TDL TDP].
  destruct FH as (FHL & FHD & FHB).
  destruct (tfb_X0_eq s) as (dt & EX0 & Rdt). change (tfb_X0 s) with (ov_X0 s) in EX0.
  pose proof bt_pre_X0 as BP0.
  destruct (build_tree_facts (ov_X0 s) TL BP0) as (FC1 & DL1 & HP1 & DP1 & BC1 & L1 & mc1 & Fl1 & SO1 & SS1 & EX1 & RL1 & Rmc1 & LF1 & ND1 & FF1 & LFC1 & LDL1 & LHP1 & LDP1 & LBC1 & TFC1 & TDL1 & TDP1 & RBC1 & Len1 & Use1 & Unu1 & ESO1 & ESS1 & RSO1 & RSS1).
  change (build_tree (ov_X0 s) TL) with (ov_X1 s) in EX1. rewrite if_stree_TL in EX1.
  cbn [sd_elems sd_max_length tsize] in RL1, Rmc1, FF1, LFC1, LDL1, Len1, Use1, Unu1, ESO1, ESS1, RSO1, RSS1.
  assert (FC0L : tree_fc (ov_X0 s) TL = ds_dyn_ltree_fc s) by (rewrite EX0, tree_fc_set_strm; reflexivity).
  rewrite FC0L in FF1, Use1, Unu1, ESO1, ESS1, RSO1, RSS1. rewrite EX0 in EX1. rewrite opt_len_set_strm, static_len_set_strm, OL0, SL0 in EX1.
  assert (BP1 : bt_pre (ov_X1 s) TD).
  { rewrite EX1. constructor.
    - apply bt_tree_lens; try assumption. all: apply tree_lens_set_strm; exact TLs.
    - intros i. rewrite bt_tree_fc_other by discriminate. rewrite tree_fc_set_strm. apply TFC.
    - intros i. rewrite bt_tree_dl_other by discriminate. rewrite tree_dl_set_strm. apply TDL.
    - intros i. rewrite bt_depth. apply TDP1.
    - rewrite bt_opt_len. apply wrap64_range.
    - rewrite bt_static_len. apply wrap64_range. }
  destruct (build_tree_facts (ov_X1 s) TD BP1) as (FC2 & DL2 & HP2 & DP2 & BC2 & L2 & mc2 & Fl2 & SO2 & SS2 & EX2 & RL2 & Rmc2 & LF2 & ND2 & FF2 & LFC2 & LDL2 & LHP2 & LDP2 & LBC2 & TFC2 & TDL2 & TDP2 & RBC2 & Len2 & Use2 & Unu2 & ESO2 & ESS2 & RSO2 & RSS2).
  change (build_tree (ov_X1 s) TD) with (ov_X2 s) in EX2. rewrite if_stree_TD in EX2.
  cbn [sd_elems sd_max_length tsize] in RL2, Rmc2, FF2, LFC2, LDL2, Len2, Use2, Unu2, ESO2, ESS2, RSO2, RSS2.
  assert (FC1D : tree_fc (ov_X1 s) TD = ds_dyn_dtree_fc s) by (rewrite EX1, bt_tree_fc_other, tree_fc_set_strm by discriminate; reflexivity).
  rewrite FC1D in FF2, Use2, Unu2, ESO2, ESS2, RSO2, RSS2.
  assert (EX2' : ov_X2 s = bt_upd (bt_upd (set_strm s (cset_data_type (ds_strm s) dt)) TL FC1 DL1 HP1 1 (574 - 2 * L1) DP1 BC1
                                  (wrap64 (0 - Z.of_nat (length Fl1) + SO1)) (wrap64 (0 - fold_right (fun f acc => stree_Len TL f + acc) 0 Fl1 + SS1)) mc1)
                      TD FC2 DL2 HP2 1 (574 - 2 * L2) DP2 BC2
                      (wrap64 (ds_opt_len (ov_X1 s) - Z.of_nat (length Fl2) + SO2)) (wrap64 (ds_static_len (ov_X1 s) - fold_right (fun f acc => stree_Len TD f + acc) 0 Fl2 + SS2)) mc2).
  { rewrite EX2, EX1. reflexivity. }
  assert (P2dlL : tree_dl (ov_X2 s) TL = DL1) by (rewrite EX2', bt_tree_dl_other, bt_tree_dl by discriminate; reflexivity).
  assert (P2dlD : tree_dl (ov_X2 s) TD = DL2) by (rewrite EX2', bt_tree_dl; reflexivity).
  assert (P2dlB : tree_dl (ov_X2 s) TB = tree_dl s TB) by (rewrite EX2', bt_tree_dl_other, bt_tree_dl_other, tree_dl_set_strm by discriminate; reflexivity).
  assert (P2fcL : tree_fc (ov_X2 s) TL = FC1) by (rewrite EX2', bt_tree_fc_other, bt_tree_fc by discriminate; reflexivity).
  assert (P2fcD : tree_fc (ov_X2 s) TD = FC2) by (rewrite EX2', bt_tree_fc; reflexivity).
  assert (P2fcB : ds_bl_tree_fc (ov_X2 s) = ds_bl_tree_fc s) by (rewrite <- !tree_fc_TB, EX2', !bt_tree_fc_other, tree_fc_set_strm by discriminate; reflexivity).
  assert (P2mcL : ds_l_max_code (ov_X2 s) = mc1) by (rewrite <- max_code_TL, EX2', max_code_bt_other, max_code_bt_upd by discriminate; reflexivity).
  assert (P2mcD : ds_d_max_code (ov_X2 s) = mc2) by (rewrite <- max_code_TD, EX2', max_code_bt_upd; reflexivity).
  assert (P2dp : ds_depth (ov_X2 s) = DP2) by (rewrite EX2', bt_depth; reflexivity).
  assert (P2tl : tree_lens (ov_X2 s)).
  { rewrite EX2. apply bt_tree_lens; try assumption. exact (bp_tl _ _ BP1). }
  assert (P2nt : nt_view (ov_X2 s) = nt_view s) by (rewrite EX2', !nt_view_bt_upd, nt_view_set_strm; reflexivity).
  assert (P2st : ds_strm (ov_X2 s) = ds_strm (ov_X0 s)) by (rewrite EX2', !strm_bt_upd, EX0; reflexivity).
  pose proof (elems_range TL) as REL. pose proof (elems_range TD) as RED. cbn [sd_elems tsize sd_max_length] in REL, RED.
  assert (LdlL : arr_len (tree_dl (ov_X2 s) TL) = 573) by (rewrite P2dlL; exact LDL1).
  assert (HL15 : forall i, 0 <= i <= mc1 -> 0 <= Len (ov_X2 s) TL i <= 15).
  { intros i Hi. unfold Len. rewrite P2dlL. pose proof (Len1 i ltac:(unfold L_CODES; lia)) as X. unfold MAX_BITS in X. lia. }
  assert (Bz : forall y, 0 <= y < 19 -> arr_get (ds_bl_tree_fc (ov_X2 s)) y = 0).
  { intros y Hy. rewrite P2fcB. apply FHB. unfold BL_CODES. exact Hy. }
  assert (Lb : arr_len (ds_bl_tree_fc (ov_X2 s)) = 39) by (pose proof P2tl as X; unfold tree_lens in X; tauto).
  destruct (scan_tree_cnt (ov_X2 s) (ds_bl_tree_fc (ov_X2 s)) TL mc1 ltac:(discriminate) ltac:(lia) ltac:(rewrite LdlL; unfold L_CODES in Rmc1; lia) HL15 ltac:(lia)
              ltac:(intros y Hy; rewrite Bz by exact Hy; lia) ltac:(intros y Hy; rewrite Bz by exact Hy; unfold L_CODES in Rmc1; lia))
    as (b3 & EX3 & Lb3 & Gb3 & EL3 & GL3).
  rewrite sbf_self in EX3.
  assert (D3 : ov_X3 s = scan_tree (ov_X2 s) TL mc1) by (unfold ov_X3; rewrite P2mcL; reflexivity).
  rewrite <- D3 in EX3. clear D3.
  set (s03 := set_Len (ov_X2 s) TL (mc1 + 1) 65535) in *.
  assert (LdlD : arr_len (tree_dl s03 TD) = 61) by (subst s03; rewrite tree_dl_set_Len_other, P2dlD by discriminate; exact LDL2).
  assert (HD15 : forall i, 0 <= i <= mc2 -> 0 <= Len s03 TD i <= 15).
  { intros i Hi. unfold Len. subst s03. rewrite tree_dl_set_Len_other, P2dlD by discriminate. pose proof (Len2 i ltac:(unfold D_CODES; lia)) as X. unfold MAX_BITS in X. lia. }
  assert (B3r : forall y, 0 <= y < 19 -> 0 <= arr_get b3 y <= 2 * (mc1 + 1)).
  { intros y Hy. rewrite Gb3, Bz by exact Hy. pose proof (TDcnt_nonneg (fun i => Len s03 TL i) mc1 y). pose proof (TDcnt_le (fun i => Len s03 TL i) mc1 y ltac:(lia)). lia. }
  destruct (scan_tree_cnt s03 b3 TD mc2 ltac:(discriminate) ltac:(lia) ltac:(rewrite LdlD; unfold D_CODES in Rmc2; lia) HD15 ltac:(lia)
              ltac:(intros y Hy; pose proof (B3r y Hy); lia) ltac:(intros y Hy; pose proof (B3r y Hy); unfold L_CODES in Rmc1; unfold D_CODES in Rmc2; lia))
    as (b4 & EX4 & Lb4 & Gb4 & EL4 & GL4).
  assert (P3mcD : ds_d_max_code (ov_X3 s) = mc2).
  { rewrite <- max_code_TD, EX3, max_code_sbf. subst s03. rewrite max_code_set_Len, max_code_TD. exact P2mcD. }
  rewrite <- EX3 in EX4.
  assert (D4 : ov_X4 s = scan_tree (ov_X3 s) TD mc2) by (unfold ov_X4; rewrite P3mcD; reflexivity).
  rewrite <- D4 in EX4. clear D4.
  set (s04 := set_Len s03 TD (mc2 + 1) 65535) in *.
  assert (P4dlL : forall i, Len (ov_X4 s) TL i = Len s03 TL i).
  { intros i. unfold Len. rewrite EX4, sbf_tree_dl. unfold s04. rewrite tree_dl_set_Len_other by discriminate. reflexivity. }
  assert (P4dlD : forall i, Len (ov_X4 s) TD i = Len s04 TD i) by (intros i; unfold Len; rewrite EX4, sbf_tree_dl; reflexivity).
  assert (P4dlB : tree_dl (ov_X4 s) TB = tree_dl s TB).
  { rewrite EX4, sbf_tree_dl. unfold s04, s03. rewrite !tree_dl_set_Len_other by discriminate. exact P2dlB. }
  assert (P4fcB : tree_fc (ov_X4 s) TB = b4) by (rewrite EX4, tree_fc_TB; apply sbf_get).
  assert (P4tl : tree_lens (ov_X4 s)).
  { rewrite EX4. apply tree_lens_sbf; [| rewrite Lb4, Lb3; exact Lb]. unfold s04, s03. apply tree_lens_set_Len, tree_lens_set_Len. exact P2tl. }
  assert (P4nt : nt_view (ov_X4 s) = nt_view s) by (rewrite EX4, nt_view_sbf; unfold s04, s03; rewrite !nt_view_set_Len; exact P2nt).
  assert (P4st : ds_strm (ov_X4 s) = ds_strm (ov_X0 s)) by (rewrite EX4, strm_sbf; unfold s04, s03; rewrite !strm_set_Len; exact P2st).
  assert (P4dp : ds_depth (ov_X4 s) = DP2) by (rewrite EX4, depth_sbf; unfold s04, s03; rewrite !depth_set_Len; exact P2dp).
  assert (P4ol : ds_opt_len (ov_X4 s) = ds_opt_len (ov_X2 s)) by (rewrite EX4, opt_len_sbf; unfold s04, s03; rewrite !opt_len_set_Len; reflexivity).
  assert (P4sl : ds_static_len (ov_X4 s) = ds_static_len (ov_X2 s)) by (rewrite EX4, static_len_sbf; unfold s04, s03; rewrite !static_len_set_Len; reflexivity).
  assert (P4mcL : ds_l_max_code (ov_X4 s) = mc1).
  { rewrite <- max_code_TL, EX4, max_code_sbf. unfold s04, s03. rewrite !max_code_set_Len, max_code_TL. exact P2mcL. }
  assert (P4mcD : ds_d_max_code (ov_X4 s) = mc2).
  { rewrite <- max_code_TD, EX4, max_code_sbf. unfold s04, s03. rewrite !max_code_set_Len, max_code_TD. exact P2mcD. }
  assert (T4dl : forall t i, 0 <= arr_get (tree_dl (ov_X4 s) t) i < 65536).
  { intros t i. rewrite EX4, sbf_tree_dl. unfold s04, s03. apply tree_dl_set_Len_typed. apply tree_dl_set_Len_typed.
    intros j. destruct t; [rewrite P2dlL; apply TDL1 | rewrite P2dlD; apply TDL2 | rewrite P2dlB; apply TDL]. }
  assert (HLs03 : forall j, 0 <= j <= mc1 -> 0 <= Len s03 TL j <= 15) by (intros j Hj; rewrite (EL3 j Hj); apply HL15; exact Hj).
  assert (HDs04 : forall j, 0 <= j <= mc2 -> 0 <= Len s04 TD j <= 15) by (intros j Hj; rewrite (EL4 j Hj); apply HD15; exact Hj).
  assert (TbB : forall i, 0 <= arr_get (ds_bl_tree_fc s) i < 65536) by (intros i; rewrite <- tree_fc_TB; apply TFC).
  assert (T4fcB : forall i, 0 <= arr_get b4 i < 65536).
  { intros i. rewrite (Gb4 i), (Gb3 i). destruct (Z_lt_le_dec i 0) as [Hi|Hi]; [| destruct (Z_lt_le_dec i 19) as [Hi'|Hi']].
    - rewrite (TDcnt_out (fun j => Len s03 TL j) mc1 i HLs03 ltac:(lia)), (TDcnt_out (fun j => Len s04 TD j) mc2 i HDs04 ltac:(lia)).
      rewrite P2fcB. pose proof (TbB i). lia.
    - rewrite Bz by lia. pose proof (TDcnt_nonneg (fun j => Len s03 TL j) mc1 i). pose proof (TDcnt_le (fun j => Len s03 TL j) mc1 i ltac:(lia)).
      pose proof (TDcnt_nonneg (fun j => Len s04 TD j) mc2 i). pose proof (TDcnt_le (fun j => Len s04 TD j) mc2 i ltac:(lia)). unfold L_CODES, D_CODES in Rmc1, Rmc2. lia.
    - rewrite (TDcnt_out (fun j => Len s03 TL j) mc1 i HLs03 ltac:(lia)), (TDcnt_out (fun j => Len s04 TD j) mc2 i HDs04 ltac:(lia)).
      rewrite P2fcB. pose proof (TbB i). lia. }
  assert (BP4 : bt_pre (ov_X4 s) TB).
  { constructor.
    - exact P4tl.
    - intros i. rewrite P4fcB. apply T4fcB.
    - intros i. apply T4dl.
    - intros i. rewrite P4dp. apply TDP2.
    - rewrite P4ol, EX2', bt_opt_len. apply wrap64_range.
    - rewrite P4sl, EX2', bt_static_len. apply wrap64_range. }
  destruct (build_tree_facts (ov_X4 s) TB BP4) as (FC5 & DL5 & HP5 & DP5 & BC5 & L5 & mc5 & Fl5 & SO5 & SS5 & EX5 & RL5 & Rmc5 & LF5 & ND5 & FF5 & LFC5 & LDL5 & LHP5 & LDP5 & LBC5 & TFC5 & TDL5 & TDP5 & RBC5 & Len5 & Use5 & Unu5 & ESO5 & ESS5 & RSO5 & RSS5).
  change (build_tree (ov_X4 s) TB) with (ov_X5 s) in EX5. rewrite if_stree_TB in EX5.
  cbn [sd_elems sd_max_length tsize] in RL5, Rmc5, FF5, LFC5, LDL5, Len5, Use5, Unu5, ESO5, ESS5, RSO5, RSS5.
  rewrite P4fcB in FF5, Use5, Unu5, ESO5, ESS5, RSO5, RSS5.
  pose proof (build_bl_tree_loop_range 17 (ov_X5 s) 18 ltac:(lia)) as Rmb. change (build_bl_tree_loop 17 (ov_X5 s) 18) with (ov_mb s) in Rmb.
  assert (EX6 : ov_X6 s = bt_upd (ov_X4 s) TB FC5 DL5 HP5 1 (574 - 2 * L5) DP5 BC5
                           (wrap64 (wrap64 (ds_opt_len (ov_X4 s) - Z.of_nat (length Fl5) + SO5) + 3 * (ov_mb s + 1) + 5 + 5 + 4)) (ds_static_len (ov_X4 s)) mc5).
  { unfold ov_X6, tfb_X6. change (tfb_mb (ov_X5 s)) with (ov_mb s). rewrite EX5, bt_set_opt_len, bt_opt_len. reflexivity. }
  assert (EL3' : forall i, i <> mc1 + 1 -> Len s03 TL i = Len (ov_X2 s) TL i).
  { intros i Hi. subst s03. rewrite Len_set_Len by (rewrite LdlL; unfold L_CODES in Rmc1; lia).
    replace (mc1 + 1 =? i) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
  assert (EL4' : forall i, i <> mc2 + 1 -> Len s04 TD i = Len (ov_X2 s) TD i).
  { intros i Hi. unfold s04. rewrite Len_set_Len by (rewrite LdlD; unfold D_CODES in Rmc2; lia).
    replace (mc2 + 1 =? i) with false by (symmetry; apply Z.eqb_neq; lia). subst s03. unfold Len. rewrite tree_dl_set_Len_other by discriminate. reflexivity. }
  assert (P4fcL : tree_fc (ov_X4 s) TL = FC1).
  { rewrite EX4, sbf_tree_fc by discriminate. unfold s04, s03. rewrite !tree_fc_set_Len. exact P2fcL. }
  assert (P4fcD : tree_fc (ov_X4 s) TD = FC2).
  { rewrite EX4, sbf_tree_fc by discriminate. unfold s04, s03. rewrite !tree_fc_set_Len. exact P2fcD. }
  assert (P6dlL : tree_dl (ov_X6 s) TL = tree_dl s03 TL).
  { rewrite EX6, bt_tree_dl_other, EX4, sbf_tree_dl by discriminate. unfold s04. rewrite tree_dl_set_Len_other by discriminate. reflexivity. }
  assert (P6dlD : tree_dl (ov_X6 s) TD = tree_dl s04 TD) by (rewrite EX6, bt_tree_dl_other, EX4, sbf_tree_dl by discriminate; reflexivity).
  assert (P6dlB : tree_dl (ov_X6 s) TB = DL5) by (rewrite EX6, bt_tree_dl; reflexivity).
  assert (P6fcL : tree_fc (ov_X6 s) TL = FC1) by (rewrite EX6, bt_tree_fc_other by discriminate; exact P4fcL).
  assert (P6fcD : tree_fc (ov_X6 s) TD = FC2) by (rewrite EX6, bt_tree_fc_other by discriminate; exact P4fcD).
  assert (P6fcB : tree_fc (ov_X6 s) TB = FC5) by (rewrite EX6, bt_tree_fc; reflexivity).
  assert (P6mcL : ds_l_max_code (ov_X6 s) = mc1) by (rewrite <- max_code_TL, EX6, max_code_bt_other, max_code_TL by discriminate; exact P4mcL).
  assert (P6mcD : ds_d_max_code (ov_X6 s) = mc2) by (rewrite <- max_code_TD, EX6, max_code_bt_other, max_code_TD by discriminate; exact P4mcD).
  assert (P6nt : nt_view (ov_X6 s) = nt_view s) by (rewrite EX6, nt_view_bt_upd; exact P4nt).
  assert (P6LD : forall i, Len (ov_X6 s) TL i = Len s03 TL i) by (intros i; unfold Len; rewrite P6dlL; reflexivity).
  assert (P6DD : forall i, Len (ov_X6 s) TD i = Len s04 TD i) by (intros i; unfold Len; rewrite P6dlD; reflexivity).
  assert (P6BD : forall x, Len (ov_X6 s) TB x = arr_get DL5 x) by (intros x; unfold Len; rewrite P6dlB; reflexivity).
  assert (XB : forall t c, 0 <= xbits t c <= 13).
  { intros t c. unfold xbits. destruct (sd_extra_base t <=? c); [|lia]. destruct t; cbn [sd_extra_bits];
      [pose proof (extra_lbits_bound (c - sd_extra_base TL)) | pose proof (extra_dbits_bound (c - sd_extra_base TD)) | pose proof (extra_blbits_bound (c - sd_extra_base TB))]; lia. }
  assert (F1 : Z.of_nat (length Fl1) <= fold_right (fun f acc => arr_get DL1 f + xbits TL f + acc) 0 Fl1).
  { apply (fold_ge_len Fl1 (fun f => arr_get DL1 f + xbits TL f)). intros f Hf. destruct (FF1 f Hf) as (A & B & C0).
    pose proof (Use1 f ltac:(lia) (or_intror Hf)). pose proof (XB TL f). lia. }
  assert (F2 : Z.of_nat (length Fl2) <= fold_right (fun f acc => arr_get DL2 f + xbits TD f + acc) 0 Fl2).
  { apply (fold_ge_len Fl2 (fun f => arr_get DL2 f + xbits TD f)). intros f Hf. destruct (FF2 f Hf) as (A & B & C0).
    pose proof (Use2 f ltac:(lia) (or_intror Hf)). pose proof (XB TD f). lia. }
  assert (F5 : Z.of_nat (length Fl5) <= fold_right (fun f acc => arr_get DL5 f + xbits TB f + acc) 0 Fl5).
  { apply (fold_ge_len Fl5 (fun f => arr_get DL5 f + xbits TB f)). intros f Hf. destruct (FF5 f Hf) as (A & B & C0).
    pose proof (Use5 f ltac:(lia) (or_intror Hf)). pose proof (XB TB f). lia. }
  assert (LF1' : Z.of_nat (length Fl1) <= 2) by lia. assert (LF2' : Z.of_nat (length Fl2) <= 2) by lia. assert (LF5' : Z.of_nat (length Fl5) <= 2) by lia.
  assert (FB1 : fold_right (fun f acc => arr_get DL1 f + xbits TL f + acc) 0 Fl1 <= 2 * 28).
  { rewrite (fold_split Fl1 (fun f => arr_get DL1 f) (xbits TL)).
    assert (G : forall l (g : Z -> Z) B, (forall f, In f l -> g f <= B) -> 0 <= B -> fold_right (fun f acc => g f + acc) 0 l <= Z.of_nat (length l) * B).
    { induction l as [|a l IH]; intros g B HBd HB0; cbn [fold_right length]; [lia|]. pose proof (HBd a (or_introl eq_refl)). specialize (IH g B ltac:(intros f Hf; apply HBd; right; exact Hf) HB0). lia. }
    pose proof (G Fl1 (fun f => arr_get DL1 f) 15 ltac:(intros f Hf; destruct (FF1 f Hf) as (A & B & C0); pose proof (Len1 f ltac:(lia)) as X; unfold MAX_BITS in X; lia) ltac:(lia)).
    pose proof (G Fl1 (xbits TL) 13 ltac:(intros f Hf; pose proof (XB TL f); lia) ltac:(lia)). lia. }
  assert (FB2 : fold_right (fun f acc => arr_get DL2 f + xbits TD f + acc) 0 Fl2 <= 2 * 28).
  { rewrite (fold_split Fl2 (fun f => arr_get DL2 f) (xbits TD)).
    assert (G : forall l (g : Z -> Z) B, (forall f, In f l -> g f <= B) -> 0 <= B -> fold_right (fun f acc => g f + acc) 0 l <= Z.of_nat (length l) * B).
    { induction l as [|a l IH]; intros g B HBd HB0; cbn [fold_right length]; [lia|]. pose proof (HBd a (or_introl eq_refl)). specialize (IH g B ltac:(intros f Hf; apply HBd; right; exact Hf) HB0). lia. }
    pose proof (G Fl2 (fun f => arr_get DL2 f) 15 ltac:(intros f Hf; destruct (FF2 f Hf) as (A & B & C0); pose proof (Len2 f ltac:(lia)) as X; unfold MAX_BITS in X; lia) ltac:(lia)).
    pose proof (G Fl2 (xbits TD) 13 ltac:(intros f Hf; pose proof (XB TD f); lia) ltac:(lia)). lia. }
  assert (FB5 : fold_right (fun f acc => arr_get DL5 f + xbits TB f + acc) 0 Fl5 <= 2 * 28).
  { rewrite (fold_split Fl5 (fun f => arr_get DL5 f) (xbits TB)).
    assert (G : forall l (g : Z -> Z) B, (forall f, In f l -> g f <= B) -> 0 <= B -> fold_right (fun f acc => g f + acc) 0 l <= Z.of_nat (length l) * B).
    { induction l as [|a l IH]; intros g B HBd HB0; cbn [fold_right length]; [lia|]. pose proof (HBd a (or_introl eq_refl)). specialize (IH g B ltac:(intros f Hf; apply HBd; right; exact Hf) HB0). lia. }
    pose proof (G Fl5 (fun f => arr_get DL5 f) 7 ltac:(intros f Hf; destruct (FF5 f Hf) as (A & B & C0); pose proof (Len5 f ltac:(lia)) as X; unfold MAX_BL_BITS in X; lia) ltac:(lia)).
    pose proof (G Fl5 (xbits TB) 13 ltac:(intros f Hf; pose proof (XB TB f); lia) ltac:(lia)). lia. }
  set (DATL := zsum (fun c => arr_get (ds_dyn_ltree_fc s) c * (arr_get DL1 c + xbits TL c)) 0 (Z.to_nat L_CODES)) in *.
  set (DATD := zsum (fun c => arr_get (ds_dyn_dtree_fc s) c * (arr_get DL2 c + xbits TD c)) 0 (Z.to_nat D_CODES)) in *.
  set (DATB := zsum (fun c => arr_get b4 c * (arr_get DL5 c + xbits TB c)) 0 (Z.to_nat BL_CODES)) in *.
  set (STL := zsum (fun c => arr_get (ds_dyn_ltree_fc s) c * (stree_Len TL c + xbits TL c)) 0 (Z.to_nat L_CODES)) in *.
  set (STD := zsum (fun c => arr_get (ds_dyn_dtree_fc s) c * (stree_Len TD c + xbits TD c)) 0 (Z.to_nat D_CODES)) in *.
  assert (OL1 : ds_opt_len (ov_X1 s) = SO1 - Z.of_nat (length Fl1)).
  { rewrite EX1, bt_opt_len. rewrite wrap64_id by lia. lia. }
  assert (SLv1 : ds_static_len (ov_X1 s) = STL).
  { rewrite EX1, bt_static_len, ESS1. rewrite (fold_split Fl1 (stree_Len TL) (xbits TL)).
    rewrite (fold_zero Fl1 (xbits TL)) by (intros f Hf; destruct (FF1 f Hf) as (A & _); apply xbits_small'; exact A).
    rewrite wrap64_id by lia. lia. }
  assert (OL2 : ds_opt_len (ov_X2 s) = SO1 - Z.of_nat (length Fl1) + (SO2 - Z.of_nat (length Fl2))).
  { rewrite EX2, bt_opt_len, OL1. rewrite wrap64_id by lia. lia. }
  assert (SLv2 : ds_static_len (ov_X2 s) = STL + STD).
  { rewrite EX2, bt_static_len, SLv1, ESS2. rewrite (fold_split Fl2 (stree_Len TD) (xbits TD)).
    rewrite (fold_zero Fl2 (xbits TD)) by (intros f Hf; destruct (FF2 f Hf) as (A & _); apply xbits_small'; exact A).
    rewrite wrap64_id by lia. lia. }
  assert (OL5 : ds_opt_len (ov_X5 s) = SO1 - Z.of_nat (length Fl1) + (SO2 - Z.of_nat (length Fl2)) + (SO5 - Z.of_nat (length Fl5))).
  { rewrite EX5, bt_opt_len, P4ol, OL2. rewrite wrap64_id by lia. lia. }
  assert (OL6 : ds_opt_len (ov_X6 s) = SO1 - Z.of_nat (length Fl1) + (SO2 - Z.of_nat (length Fl2)) + (SO5 - Z.of_nat (length Fl5)) + 3 * (ov_mb s + 1) + 14).
  { rewrite EX6, bt_opt_len, P4ol, OL2. rewrite (wrap64_id (SO1 - _ + _ - _ + _)) by lia. rewrite wrap64_id by lia. lia. }
  assert (SL6 : ds_static_len (ov_X6 s) = STL + STD) by (rewrite EX6, bt_static_len, P4sl; exact SLv2).
  assert (SL5 : ds_static_len (ov_X5 s) = STL + STD) by (rewrite EX5, bt_static_len, P4sl; exact SLv2).
  constructor.
  - exact P6nt.
  - rewrite EX6, strm_bt_upd. exact P4st.
  - exists dt. split; [exact EX0 | exact Rdt].
  - rewrite EX6. apply bt_tree_lens; try assumption.
  - intros t i. destruct t; [rewrite P6fcL; apply TFC1 | rewrite P6fcD; apply TFC2 | rewrite P6fcB; apply TFC5].
  - intros t i. destruct t; [rewrite P6dlL | rewrite P6dlD | rewrite P6dlB; apply TDL5].
    + subst s03. apply tree_dl_set_Len_typed. intros j. rewrite P2dlL. apply TDL1.
    + unfold s04, s03. apply tree_dl_set_Len_typed. apply tree_dl_set_Len_typed. intros j. rewrite P2dlD. apply TDL2.
  - intros i. rewrite EX6, bt_depth. apply TDP5.
  - intros i Hi. rewrite EX6, bt_bl_count. pose proof (RBC5 i Hi). lia.
  - rewrite P6mcL. unfold L_CODES. lia.
  - rewrite P6mcD. unfold D_CODES. lia.
  - intros i Hi. rewrite P6mcL in Hi. rewrite P6LD, EL3 by lia. apply HL15. lia.
  - intros i Hi. rewrite P6mcD in Hi. rewrite P6DD, EL4 by lia. apply HD15. lia.
  - intros i Hi Ni. rewrite P6mcL in Ni. rewrite P6LD, EL3' by lia. unfold Len. rewrite P2dlL. pose proof (Len1 i ltac:(unfold L_CODES in Hi; lia)) as X. unfold MAX_BITS in X. lia.
  - intros i Hi Ni. rewrite P6mcD in Ni. rewrite P6DD, EL4' by lia. unfold Len. rewrite P2dlD. pose proof (Len2 i ltac:(unfold D_CODES in Hi; lia)) as X. unfold MAX_BITS in X. lia.
  - intros x Hx. rewrite P6BD. pose proof (Len5 x Hx) as X. unfold MAX_BL_BITS in X. lia.
  - intros c Hc Hf. rewrite P6mcL. pose proof (Use1 c ltac:(unfold L_CODES in Hc; lia) (or_introl Hf)) as [A B].
    rewrite P6LD, EL3 by lia. unfold Len. rewrite P2dlL. pose proof (Len1 c ltac:(unfold L_CODES in Hc; lia)) as X. unfold MAX_BITS in X. lia.
  - intros d Hd Hf. rewrite P6mcD. pose proof (Use2 d ltac:(unfold D_CODES in Hd; lia) (or_introl Hf)) as [A B].
    rewrite P6DD, EL4 by lia. unfold Len. subst s03. rewrite tree_dl_set_Len_other, P2dlD by discriminate. pose proof (Len2 d ltac:(unfold D_CODES in Hd; lia)) as X. unfold MAX_BITS in X. lia.
  - exact Rmb.
  - intros x Hx. unfold ov_BC. rewrite <- tree_fc_TB, P4fcB, Gb4, Gb3, Bz by exact Hx. rewrite P6mcL, P6mcD.
    unfold Len. rewrite P6dlL, P6dlD. lia.
  - rewrite OL6. pose proof RSO1 as Q1. pose proof RSO2 as Q2. pose proof RSO5 as Q5. rewrite ESO1, ESO2, ESO5. clearbody DATL DATD DATB. lia.
  - unfold ov_BC. rewrite <- tree_fc_TB, P4fcB, OL6, ESO1, ESO2, ESO5. fold DATL DATD DATB.
    assert (EB : zsum (fun x => arr_get b4 x * (Len (ov_X6 s) TB x + arr_get extra_blbits_a x)) 0 19 = DATB).
    { subst DATB. apply zsum_ext. intros x Hx. rewrite P6BD. unfold xbits. cbn [sd_extra_base sd_extra_bits]. replace (0 <=? x) with true by (symmetry; apply Z.leb_le; lia). rewrite Z.sub_0_r. reflexivity. }
    assert (ELs : zsum (fun c => arr_get (ds_dyn_ltree_fc s) c * (Len (ov_X6 s) TL c + xbits TL c)) 0 (Z.to_nat L_CODES) = DATL).
    { subst DATL. apply zsum_ext. intros c Hc. rewrite P6LD.
      destruct (Z.eq_dec (arr_get (ds_dyn_ltree_fc s) c) 0) as [Z0|NZ]; [rewrite Z0; lia|].
      pose proof (Use1 c ltac:(unfold L_CODES in Hc; lia) (or_introl NZ)) as [A B].
      rewrite EL3 by lia. unfold Len. rewrite P2dlL. reflexivity. }
    assert (EDs : zsum (fun d => arr_get (ds_dyn_dtree_fc s) d * (Len (ov_X6 s) TD d + xbits TD d)) 0 (Z.to_nat D_CODES) = DATD).
    { subst DATD. apply zsum_ext. intros d Hd. rewrite P6DD.
      destruct (Z.eq_dec (arr_get (ds_dyn_dtree_fc s) d) 0) as [Z0|NZ]; [rewrite Z0; lia|].
      pose proof (Use2 d ltac:(unfold D_CODES in Hd; lia) (or_introl NZ)) as [A B].
      rewrite EL4 by lia. unfold Len. subst s03. rewrite tree_dl_set_Len_other, P2dlD by discriminate. reflexivity. }
    rewrite EB, ELs, EDs. lia.
  - rewrite SL6. reflexivity.
  - rewrite SL6. pose proof RSS1 as Q6. pose proof RSS2 as Q7. clearbody STL STD. lia.
  - exact (bt_safe_intro _ _ BP0).
  - exact (bt_safe_intro _ _ BP1).
  - rewrite P2mcL, P6mcL. reflexivity.
  - rewrite P2mcL. exact HL15.
  - intros i. rewrite P2dlL. apply TDL1.
  - intros i. rewrite P2fcB. apply TbB.
  - rewrite P3mcD, P6mcD. reflexivity.
  - intros i Hi. rewrite P3mcD in Hi. pose proof (HD15 i Hi) as X. rewrite Len_eq in X. rewrite Len_eq, EX3, sbf_tree_dl. exact X.
  - intros i. rewrite EX3, sbf_tree_dl. subst s03. apply tree_dl_set_Len_typed. intros j. rewrite P2dlD. apply TDL2.
  - intros i. rewrite EX3, sbf_get, Gb3. destruct (Z_lt_le_dec i 0) as [Hi|Hi]; [| destruct (Z_lt_le_dec i 19) as [Hi'|Hi']].
    + rewrite (TDcnt_out (fun j => Len s03 TL j) mc1 i HLs03 ltac:(lia)), P2fcB. pose proof (TbB i). lia.
    + rewrite Bz by lia. pose proof (TDcnt_nonneg (fun j => Len s03 TL j) mc1 i). pose proof (TDcnt_le (fun j => Len s03 TL j) mc1 i ltac:(lia)). unfold L_CODES in Rmc1. lia.
    + rewrite (TDcnt_out (fun j => Len s03 TL j) mc1 i HLs03 ltac:(lia)), P2fcB. pose proof (TbB i). lia.
  - exact (bt_safe_intro _ _ BP4).
  - intros i Hi. rewrite <- tree_dl_TB, EX5, bt_tree_dl. pose proof (Len5 i Hi) as X. unfold MAX_BL_BITS in X. lia.
  - intros i. rewrite <- tree_dl_TB, EX5, bt_tree_dl. apply TDL5.
  - rewrite OL5, SL5. pose proof RSO1 as Q1. pose proof RSO2 as Q2. pose proof RSO5 as Q5. pose proof RSS1 as Q6. pose proof RSS2 as Q7. rewrite ESO1, ESO2, ESO5. clearbody DATL DATD DATB STL STD. lia.
  - assert (V5 : nt_view (ov_X5 s) = nt_view s) by (rewrite EX5, nt_view_bt_upd; exact P4nt).
    pose proof (nt_view_facts _ _ V5) as V. destruct V as (_ & _ & _ & _ & _ & _ & _ & _ & V9 & _). exact V9.
  - split; [| split; [| split]].
    + rewrite <- !max_code_TL, EX5, EX6, !max_code_bt_other by discriminate. reflexivity.
    + rewrite <- !max_code_TD, EX5, EX6, !max_code_bt_other by discriminate. reflexivity.
    + rewrite OL6, OL5. lia.
    + rewrite SL6, SL5. reflexivity.
  - exact BP1.
  - exact BP4.
  - exact FC0L.
  - exact FC1D.
  - unfold ov_BC. rewrite tree_fc_TB. reflexivity.
  - intros i Ni. rewrite P6mcL in Ni. rewrite P6LD, EL3' by lia. unfold Len. rewrite P2dlL, EX1, bt_tree_dl. reflexivity.
  - intros i Ni. rewrite P6mcD in Ni. rewrite P6DD, EL4' by lia. reflexivity.
  - intros i. rewrite P6BD, EX5, bt_tree_dl. reflexivity.
  - rewrite P6mcL, P6LD. subst s03. rewrite Len_set_Len by (rewrite LdlL; unfold L_CODES in Rmc1; lia). rewrite Z.eqb_refl. reflexivity.
  - rewrite P6mcD, P6DD. unfold s04. rewrite Len_set_Len by (rewrite LdlD; unfold D_CODES in Rmc2; lia). rewrite Z.eqb_refl. reflexivity.
  - rewrite EX1, max_code_bt_upd. symmetry. exact P6mcL.
  - rewrite P6mcD, max_code_TD. exact P2mcD.
Qed.
End TreePhase.
