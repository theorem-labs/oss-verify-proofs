(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.E1 Require Import DSLayout.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import Prog ZIface DeflateState Trees TreeModel Deflate DeflInitLib.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.D6S Require Import DS6 TrInit6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition z0 : Z -> Z := fun _ => 0.

Ltac vnf := lazy -[Z.pow Z.sub Z.add Z.mul Z.div Z.shiftl Z.opp Z.eqb Z.ltb Z.leb init_u8 init_u16 init_u32 init_u64 swrap32 swrap64 wrap8 wrap16
         cfg_lazy cfg_good cfg_nice cfg_chain arr_u16_of arr_s32_of arr_u8_of blk_bytes blk_ush arr_fill arr_set arr_make arr_len arr_get
         cset_total_in cset_total_out cset_msg cset_data_type cset_adler z0 p_strm p_window p_prev p_head p_pending_buf].

Lemma arr_u16_of_z0 : forall o st n i, arr_get (arr_u16_of z0 o st n) i = 0.
Proof. intros. unfold arr_u16_of. rewrite arr_get_init. reflexivity. Qed.
Lemma arr_s32_of_z0 : forall o st n i, arr_get (arr_s32_of z0 o st n) i = 0.
Proof. intros. unfold arr_s32_of. rewrite arr_get_init. reflexivity. Qed.
Lemma arr_u8_of_z0 : forall o st n i, arr_get (arr_u8_of z0 o st n) i = 0.
Proof. intros. unfold arr_u8_of. rewrite arr_get_init. reflexivity. Qed.
Lemma blk_bytes_z0 : forall n i, arr_get (blk_bytes z0 n) i = 0.
Proof. intros. unfold blk_bytes. rewrite arr_get_init. reflexivity. Qed.
Lemma blk_ush_z0 : forall n i, arr_get (blk_ush z0 n) i = 0.
Proof. intros. unfold blk_ush. rewrite arr_get_init. reflexivity. Qed.

Section T.
Variables (b0 bw bp bh bb : blk) (cs : cstrm).

Definition sRK0 : deflate_state := DeflInitLib.sRK z0 z0 z0 z0 z0 b0 bw bp bh bb cs 1 15 8 6 0 8.
Definition sTI0 : deflate_state := DeflInitLib.sTI z0 z0 z0 z0 z0 b0 bw bp bh bb cs 1 15 8 6 0 8.
Definition sLM0 : deflate_state := DeflInitLib.sLM z0 z0 z0 z0 z0 b0 bw bp bh bb cs 1 15 8 6 0 8.

Lemma sTI0_eq : sTI0 = tr_init sRK0. Proof. reflexivity. Qed.

Lemma sRK0_dvals : forall (p : ds_ptrs) (S : Z),
  dvals6 sRK0 p S (0, 0, 0, 0, 0, 0) =
  [p_strm p; 42; p_pending_buf p; 65536; p_pending_buf p + 0; 0; 1; 0; 0; 8; -2; 32768; 15; 32767; p_window p; 0;
   p_prev p; p_head p; 0; 32768; 15; 32767; 5; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 6; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
   p_pending_buf p + 16384; 16384; 0; 49149; 0; 0; 0; 0; 0; 0; 0].
Proof. intros p S. vnf. reflexivity. Qed.

Lemma sLM0_vals : forall (p : ds_ptrs) (S : Z),
  ds6_vals sLM0 p S =
  [p_strm p; 42; p_pending_buf p; 65536; p_pending_buf p + 0; 0; 1; 0; 0; 8; -2; 32768; 15; 32767; p_window p; 65536;
   p_prev p; p_head p; 0; 32768; 15; 32767; 5; 0; 2; 0; 0; 0; 0; 0; 2; 128; 16; 6; 0; 8; 128;
   S + 212; 0; 168672; S + 2504; 0; 168704; S + 2748; 0; 168736; 0; 0;
   p_pending_buf p + 16384; 16384; 0; 49149; 0; 0; 0; 0; 0; 0; 0].
Proof. intros p S. vnf. reflexivity. Qed.

Lemma sRK0_arrs :
  ds_dyn_ltree_fc sRK0 = arr_u16_of z0 212 4 573 /\ ds_dyn_ltree_dl sRK0 = arr_u16_of z0 214 4 573
  /\ ds_dyn_dtree_fc sRK0 = arr_u16_of z0 2504 4 61 /\ ds_dyn_dtree_dl sRK0 = arr_u16_of z0 2506 4 61
  /\ ds_bl_tree_fc sRK0 = arr_u16_of z0 2748 4 39 /\ ds_bl_tree_dl sRK0 = arr_u16_of z0 2750 4 39
  /\ ds_bl_count sRK0 = arr_u16_of z0 2976 2 16 /\ ds_heap sRK0 = arr_s32_of z0 3008 4 573
  /\ ds_depth sRK0 = arr_u8_of z0 5308 1 573
  /\ ds_pending_buf sRK0 = blk_bytes z0 65536
  /\ ds_window sRK0 = blk_bytes z0 65536 /\ ds_prev sRK0 = blk_ush z0 32768 /\ ds_head sRK0 = blk_ush z0 32768.
Proof. vnf. repeat split; reflexivity. Qed.

Lemma tree_lens_sRK0 : tree_lens sRK0.
Proof. unfold tree_lens. vnf. repeat split; reflexivity. Qed.

Lemma sLM0_blocks :
  ds_pending_buf sLM0 = blk_bytes z0 65536
  /\ ds_window sLM0 = blk_bytes z0 65536 /\ ds_prev sLM0 = blk_ush z0 32768
  /\ ds_head sLM0 = arr_fill (arr_set (blk_ush z0 32768) 32767 0) 0 32767 0
  /\ ds_w_size sLM0 = 32768 /\ ds_hash_size sLM0 = 32768 /\ ds_lit_bufsize sLM0 = 16384.
Proof. vnf. repeat split; reflexivity. Qed.

Lemma sLM0_trees :
  ds_dyn_ltree_fc sLM0 = ds_dyn_ltree_fc sTI0 /\ ds_dyn_ltree_dl sLM0 = ds_dyn_ltree_dl sTI0
  /\ ds_dyn_dtree_fc sLM0 = ds_dyn_dtree_fc sTI0 /\ ds_dyn_dtree_dl sLM0 = ds_dyn_dtree_dl sTI0
  /\ ds_bl_tree_fc sLM0 = ds_bl_tree_fc sTI0 /\ ds_bl_tree_dl sLM0 = ds_bl_tree_dl sTI0
  /\ ds_bl_count sLM0 = ds_bl_count sTI0 /\ ds_heap sLM0 = ds_heap sTI0 /\ ds_depth sLM0 = ds_depth sTI0
  /\ ds_pending_buf sLM0 = ds_pending_buf sTI0.
Proof. vnf. repeat split; reflexivity. Qed.

Lemma tree_lens_sLM0 : tree_lens sLM0.
Proof. unfold tree_lens. vnf. repeat split; reflexivity. Qed.

Lemma sTI0_vals : forall (p : ds_ptrs) (S : Z),
  ds6_vals sTI0 p S =
  [p_strm p; 42; p_pending_buf p; 65536; p_pending_buf p + 0; 0; 1; 0; 0; 8; -2; 32768; 15; 32767; p_window p; 0;
   p_prev p; p_head p; 0; 32768; 15; 32767; 5; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 6; 0; 0; 0;
   S + 212; 0; 168672; S + 2504; 0; 168704; S + 2748; 0; 168736; 0; 0;
   p_pending_buf p + 16384; 16384; 0; 49149; 0; 0; 0; 0; 0; 0; 0].
Proof. intros p S. vnf. reflexivity. Qed.
Lemma sLM0_lens :
  arr_len (ds_window sLM0) = 65536 /\ arr_len (ds_prev sLM0) = 32768 /\ arr_len (ds_head sLM0) = 32768
  /\ arr_len (ds_pending_buf sLM0) = 65536.
Proof.
  pose proof sLM0_blocks as (E1 & E2 & E3 & E4 & _). rewrite E1, E2, E3, E4.
  unfold blk_bytes, blk_ush. rewrite arr_len_fill, arr_len_set, !arr_len_init. repeat split; reflexivity.
Qed.

Lemma sLM0_window_get : forall i, arr_get (ds_window sLM0) i = 0.
Proof. intros i. pose proof sLM0_blocks as (_ & E2 & _). rewrite E2. apply blk_bytes_z0. Qed.
Lemma sLM0_prev_get : forall i, arr_get (ds_prev sLM0) i = 0.
Proof. intros i. pose proof sLM0_blocks as (_ & _ & E3 & _). rewrite E3. apply blk_ush_z0. Qed.
Lemma sLM0_head_get : forall i, arr_get (ds_head sLM0) i = 0.
Proof.
  intros i. pose proof sLM0_blocks as (_ & _ & _ & E4 & _). rewrite E4.
  rewrite arr_get_fill. destruct (_ && _); [reflexivity|].
  rewrite arr_get_set. destruct (_ && _); [reflexivity|]. apply blk_ush_z0.
Qed.
End T.
