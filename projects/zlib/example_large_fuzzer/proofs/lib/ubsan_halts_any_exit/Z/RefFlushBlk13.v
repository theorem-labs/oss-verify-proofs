(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DSLayout.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TreeMem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TreesRod.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import BuildTreeRod.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import BuildTreeModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import GenBitlenModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import CompressModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ScanModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TrSmallModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require  GenCodesModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Trees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefBitsLib.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefBitsFwd.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefTreesApi.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefBuildTreeLib.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefBuildTree1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefBuildTree9.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefTrStored_run.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefScanTree_run.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefTrInit_run.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefSendTree1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefSendTree4.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefCompressBlk1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefFlushBlk1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefFlushBlk2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefFlushBlk3.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefFlushBlk4.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefFlushBlk5.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FlushBlockModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefFlushBlk6.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefFlushBlk7.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefFlushBlk8.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefFlushBlk9.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefFlushBlk10.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefFlushBlk11.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefFlushBlk12.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Walk.
Variable F : franges.
Variable S : Z.
Variable p : ds_ptrs.
Variable PBL : Z.
Variable ds : deflate_state.
Variable sp : Z.
Variable buf : option Z.
Variable bufp : Z.
Variable len : Z.
Variable last : Z.
Local Notation PB := (p_pending_buf p).
Local Notation SP := (sp - 80).

Local Ltac nf := cbn [RefBuildTree1.stF].

Local Ltac sideF := try solve [ intros; apply (RefBuildTree5.extra_view_bound' TL) ].

Local Ltac vcongr := first [ reflexivity | apply szwrap32_mod16 | rewrite szwrap32_mod16; reflexivity
                           | rewrite Z.mod_mod by lia; reflexivity
                           | rewrite Z.mod_mod by lia; apply szwrap32_mod16
                           | rewrite ?szwrap32_mod16, ?Z.mod_mod by lia; apply mod16_congr; lia ].
Local Ltac vwrap := first [ reflexivity | symmetry; apply wrap16_id; lia
                          | rewrite wrap16_mod'; reflexivity | rewrite wrap16_mod', szwrap32_mod16; reflexivity
                          | apply wrap16_id'; lia
                          | rewrite wrap16_mod', ?Z.mod_mod by lia; rewrite ?szwrap32_mod16; apply mod16_congr; lia ].
Local Ltac vrange := first [ lia | apply Z.mod_pos_bound; lia ].


Definition stat_ok (PBL' last' : Z) (X : deflate_state) : Prop :=
  sb_room PBL' X 3
  /\ compress_block_ok PBL' (send_bits X (2 + last') 3) static_ltree_fc static_ltree_dl static_dtree_fc static_dtree_dl
  /\ (0 <= ds_sym_next X /\ ds_sym_next X + 3 < 2 ^ 31) /\ 0 <= ds_lit_bufsize X < 2 ^ 32.

Definition sto_ok (PBL' : Z) (X : deflate_state) (buf' : option Z) (len' last' : Z) : Prop :=
  ds_pending (tr_stored_block X buf' len' last') <= PBL' /\ (len' <> 0 -> buf' <> None).

Definition post_ok (PBL' last' : Z) (Y : deflate_state) : Prop :=
  BINV PBL' Y /\ (last' <> 0 -> ds_pending (bi_windup (init_block Y)) <= PBL').

Definition hi_ok (PBL' : Z) (ds' : deflate_state) (buf' : option Z) (len' last' : Z) : Prop :=
  let X0 := tfb_X0 ds' in
  let X1 := build_tree X0 TL in
  let X2 := build_tree X1 TD in
  let mcl := ds_l_max_code X2 in
  let X3 := scan_tree X2 TL mcl in
  let mcd := ds_d_max_code X3 in
  let X4 := scan_tree X3 TD mcd in
  let X5 := build_tree X4 TB in
  let mb := tfb_mb X5 in
  let X6 := tfb_X6 X5 mb in
  bt_safe X0 TL /\ bt_safe X1 TD
  /\ (0 <= mcl /\ mcl + 1 < 573) /\ (forall i, 0 <= i <= mcl -> 0 <= Len X2 TL i <= 15)
  /\ (forall i, 0 <= i < 573 -> 0 <= arr_get (tree_dl X2 TL) i < 65536)
  /\ (forall i, 0 <= i < 39 -> 0 <= arr_get (ds_bl_tree_fc X2) i < 65536)
  /\ (0 <= mcd /\ mcd + 1 < 61) /\ (forall i, 0 <= i <= mcd -> 0 <= Len X3 TD i <= 15)
  /\ (forall i, 0 <= i < 61 -> 0 <= arr_get (tree_dl X3 TD) i < 65536)
  /\ (forall i, 0 <= i < 39 -> 0 <= arr_get (ds_bl_tree_fc X3) i < 65536)
  /\ bt_safe X4 TB
  /\ ((forall i, 0 <= i < 19 -> 0 <= arr_get (ds_bl_tree_dl X5) i < 16)
      /\ (forall i, 0 <= i < 39 -> 0 <= arr_get (ds_bl_tree_dl X5) i < 65536))
  /\ 0 <= ds_opt_len X5 < 2 ^ 63 /\ 0 <= ds_static_len X5 < 2 ^ 63 /\ 0 <= ds_strategy X5 <= 4
  /\ match tfb_branch X6 buf' len' with
     | 0 => stat_ok PBL' last' X6
     | 1 => RefFlushBlk12.dyn_ok PBL' last' X6 mb
     | _ => sto_ok PBL' X6 buf' len' last'
     end.

Definition lo_ok (PBL' : Z) (ds' : deflate_state) (buf' : option Z) (len' last' : Z) : Prop :=
  match buf' with None => stat_ok PBL' last' ds' | Some _ => sto_ok PBL' ds' buf' len' last' end.

Definition fb_safe (ds' : deflate_state) (buf' : option Z) (len' last' : Z) : Prop :=
  let PBL' := arr_len (ds_pending_buf ds') in
  0 <= ds_level ds' < 100 /\ - 2 ^ 31 <= cs_data_type (ds_strm ds') < 2 ^ 31 /\ 0 < PBL'
  /\ (forall i, 0 <= i < 573 -> 0 <= arr_get (ds_dyn_ltree_fc ds') i < 65536)
  /\ post_ok PBL' last' (tfb_pre ds' buf' len' last')
  /\ (if 0 <? ds_level ds' then hi_ok PBL' ds' buf' len' last' else lo_ok PBL' ds' buf' len' last').


Lemma ds_opt_len_set_opt_len : forall s v, ds_opt_len (set_opt_len s v) = v.
Proof. intros s v; destruct s; reflexivity. Qed.

Lemma tree_fc_TL : forall s, tree_fc s TL = ds_dyn_ltree_fc s. Proof. reflexivity. Qed.
Lemma tree_dl_TL : forall s, tree_dl s TL = ds_dyn_ltree_dl s. Proof. reflexivity. Qed.
Lemma tree_fc_TD : forall s, tree_fc s TD = ds_dyn_dtree_fc s. Proof. reflexivity. Qed.
Lemma tree_dl_TD : forall s, tree_dl s TD = ds_dyn_dtree_dl s. Proof. reflexivity. Qed.

Lemma tfb_emit_1 : forall X mb,
  0 <= mb <= 18 ->
  let X11 := sbs_run X (RefFlushBlk12.hd_calls last X mb) in
  let X13 := send_tree (send_tree X11 TL (ds_l_max_code X)) TD (ds_d_max_code X) in
  tfb_emit 1 X mb buf len last =
    compress_block X13 (ds_dyn_ltree_fc X13) (ds_dyn_ltree_dl X13) (ds_dyn_dtree_fc X13) (ds_dyn_dtree_dl X13).
Proof.
  intros X mb Hmb X11 X13. unfold tfb_emit. cbn [Z.eqb Pos.eqb]. change (Z.shiftl DYN_TREES 1) with 4.
  rewrite send_all_trees_eq by lia.
  destruct (trees8_facts X (send_bits X (4 + last) 3) (trees8_send_bits X (4 + last) 3)) as (_ & _ & _ & _ & _ & _ & -> & ->).
  replace (ds_l_max_code X + 1 - 1) with (ds_l_max_code X) by lia. replace (ds_d_max_code X + 1 - 1) with (ds_d_max_code X) by lia.
  assert (E11 : sbs_run (send_bits X (4 + last) 3) (sat_calls (send_bits X (4 + last) 3) (ds_l_max_code X + 1) (ds_d_max_code X + 1) (mb + 1)) = X11).
  { subst X11. unfold sat_calls, RefFlushBlk12.hd_calls. cbn [sbs_run app].
    replace (ds_l_max_code X + 1 - 257) with (ds_l_max_code X - 256) by lia.
    replace (ds_d_max_code X + 1 - 1) with (ds_d_max_code X) by lia.
    replace (mb + 1 - 4) with (mb - 3) by lia.
    rewrite (bl_calls_ext X (send_bits X (4 + last) 3)) by (intros; apply sb_Len). reflexivity. }
  rewrite E11. reflexivity.
Qed.

Lemma bits4_X6 : forall X0,
  bits4 (tfb_X6 (tfb_X5 X0) (tfb_mb (tfb_X5 X0))) = bits4 X0.
Proof.
  intros X0. unfold tfb_X6, tfb_X5. cbv zeta. rewrite bits4_set_opt_len.
  rewrite !(k_build_tree _ _ _ keeps_bits4), !(k_scan_tree _ _ _ keeps_bits4), !(k_build_tree _ _ _ keeps_bits4). reflexivity.
Qed.

Lemma bits4_X6' : bits4 (tfb_X6 (tfb_X5 (tfb_X0 ds)) (tfb_mb (tfb_X5 (tfb_X0 ds)))) = bits4 ds.
Proof.
  rewrite bits4_X6. unfold tfb_X0. destruct (_ && _); [apply bits4_set_strm | reflexivity].
Qed.

End Walk.
