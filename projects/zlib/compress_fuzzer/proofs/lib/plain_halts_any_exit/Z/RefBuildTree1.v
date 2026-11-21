(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DSLayout.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeMem.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesRod.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import BuildTreeRod.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import BuildTreeModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import Trees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefBitsLib.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefTreesApi.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefBuildTreeLib.
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
Variable (t : tree_id).
Local Notation PB := (p_pending_buf p).
Local Notation T := (S + toff t).
Local Notation E := (sd_elems t).
Local Notation SP := (sp - 192).
Local Notation U := (bt_upd ds t).
Let Htt : 212 <= toff t /\ toff t + 4 * tsize t <= 2904 /\ 1 <= tsize t <= 573 := toff_tsize t.

Lemma tsize_elems : tsize t = 2 * E + 1.
Proof. destruct t; reflexivity. Qed.
Lemma elems_range : 19 <= E <= 286.
Proof. destruct t; cbn; unfold L_CODES, D_CODES, BL_CODES, LITERALS, LENGTH_CODES; lia. Qed.
Lemma dsc_off_val : 2904 <= dsc_off t <= 2952.
Proof. destruct t; cbn; lia. Qed.
Lemma SDA_range : 192624 <= SDA t <= 192688.
Proof. destruct t; cbn; unfold A_static_l_desc, A_static_d_desc, A_static_bl_desc; lia. Qed.
Lemma STP_range : 0 <= STP t < 2 ^ 32.
Proof. destruct t; cbn; unfold A_static_ltree, A_static_dtree; lia. Qed.

Definition stree_dl : arr := match t with TL => static_ltree_dl | TD => static_dtree_dl | TB => arr_make 1 0 end.

Definition stF (FC DL HP DP BC : arr) (f : nat) (x : Z) : Z :=
  match f with
  | 0%nat => pb FC x | 1%nat => pb DL x | 2%nat => hv HP x | 3%nat => wb DP x | 4%nat => pb BC x
  | 5%nat => arr_get (sd_extra_bits t) x mod 2 ^ 32 | _ => pb stree_dl x
  end.

Definition FB : list (nat * Z) :=
  [(0%nat, 65536); (1%nat, 65536); (2%nat, 573); (3%nat, 256); (4%nat, 65536); (5%nat, 2 ^ 32); (6%nat, 65536)].

Definition VB : bounds :=
  [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 2 ^ 63); (35%nat, 300);
   (36%nat, 600); (37%nat, 600); (38%nat, 600); (39%nat, 600); (40%nat, 600); (41%nat, 600);
   (42%nat, 65536); (43%nat, 65536); (44%nat, 65536); (45%nat, 65536);
   (46%nat, 2 ^ 64); (47%nat, 2 ^ 64); (48%nat, 2 ^ 63); (49%nat, 2 ^ 63); (50%nat, 2 ^ 63); (51%nat, 3000)].

Local Ltac nf := cbn [stF].

Definition X0 : deflate_state :=
  U (tree_fc ds t) (tree_dl ds t) (ds_heap ds) 0 573 (ds_depth ds) (ds_bl_count ds) (ds_opt_len ds) (ds_static_len ds) (max_code ds t).

Section Loop1.

Variable FC : arr.
Variable BC : arr.
Variable HM : Z.
Variable OL : Z.
Variable SL : Z.
Variable MC : Z.
Local Notation V DL HP HL DP := (U FC DL HP HL HM DP BC OL SL MC).

Hypothesis RFC : forall i, 0 <= i < tsize t -> 0 <= arr_get FC i < 65536.

Definition L1 (X : deflate_state) (n mc : Z) : deflate_state * Z :=
  build_tree_loop1 (Z.to_nat (E - n)) X t E n mc.

Lemma L1_step : forall DL HP HL DP n mc, 0 <= n < E ->
  L1 (V DL HP HL DP) n mc =
    if negb (arr_get FC n =? 0)
    then L1 (V DL (arr_set HP (HL + 1) n) (HL + 1) (arr_set DP n (wrap8 0))) (n + 1) n
    else L1 (V (arr_set DL n (wrap16 0)) HP HL DP) (n + 1) mc.
Proof.
  intros DL HP HL DP n mc Hn. unfold L1.
  replace (Z.to_nat (E - n)) with (Datatypes.S (Z.to_nat (E - (n + 1)))) by lia.
  cbn [build_tree_loop1]. replace (n <? E) with true by (symmetry; apply Z.ltb_lt; lia).
  autorewrite with btupd. reflexivity.
Qed.

Lemma L1_end : forall X mc, L1 X E mc = (X, mc).
Proof. intros. unfold L1. replace (Z.to_nat (E - E)) with 0%nat by lia. reflexivity. Qed.
End Loop1.

End Walk.
