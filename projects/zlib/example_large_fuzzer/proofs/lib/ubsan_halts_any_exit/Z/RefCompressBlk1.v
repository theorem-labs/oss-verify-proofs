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
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TrSmallModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TreesRod.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import CompressModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Trees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefBitsLib.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefTreesApi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Ltac mlia := Z.to_euclidean_division_equations; lia.

Local Opaque length_code_a dist_code_a extra_lbits_a base_length_a extra_dbits_a base_dist_a
             static_ltree_fc static_ltree_dl static_dtree_fc static_dtree_dl bl_order_a extra_blbits_a.

Ltac tab_range :=
  lazymatch goal with
  | |- 0 <= wb _ _ < _ => apply wb_range
  | |- 0 <= pb _ _ < _ => apply pb_range
  | |- 0 <= arr_get length_code_a _ < _ => apply length_code_bound
  | |- 0 <= arr_get dist_code_a _ < _ => apply dist_code_bound
  | |- 0 <= arr_get extra_lbits_a _ < _ => apply extra_lbits_bound
  | |- 0 <= arr_get base_length_a _ < _ => apply base_length_bound
  | |- 0 <= arr_get extra_dbits_a _ < _ => apply extra_dbits_bound
  | |- 0 <= arr_get base_dist_a _ < _ => apply base_dist_bound
  end.


Definition sym_lens (s : deflate_state) (ldl ddl : arr) (sx : Z) : Prop :=
  let dist := sym_dist s sx in
  let lc := sym_lc s sx in
  if dist =? 0 then 0 <= arr_get ldl lc < 16
  else 0 <= arr_get ldl (arr_get length_code_a lc + LITERALS + 1) < 16
       /\ 0 <= arr_get ddl (d_code (dist - 1)) < 16.

Fixpoint cb_lens (fuel : nat) (s : deflate_state) (lfc ldl dfc ddl : arr) (sx : Z) : Prop :=
  match fuel with
  | O => True
  | S f =>
      sym_lens s ldl ddl sx
      /\ (let s' := sbs_run s (sym_calls s lfc ldl dfc ddl sx) in
          let sx' := sx + 1 + 1 + 1 in
          if sx' <? ds_sym_next s' then cb_lens f s' lfc ldl dfc ddl sx' else True)
  end.

Definition compress_lens_ok (s : deflate_state) (lfc ldl dfc ddl : arr) : Prop :=
  (ds_sym_next s <> 0 -> cb_lens (Z.to_nat (ds_sym_next s)) s lfc ldl dfc ddl 0)
  /\ 0 <= arr_get ldl END_BLOCK < 16.


Section Walk.
Variable F : franges.
Variable S : Z.
Variable p : ds_ptrs.
Variable PBL : Z.
Variable ds : deflate_state.
Variable sp : Z.
Variable LT : Z.
Variable DT : Z.
Variable lfc : arr.
Variable ldl : arr.
Variable dfc : arr.
Variable ddl : arr.
Local Notation PB := (p_pending_buf p).
Local Notation LB := (ds_lit_bufsize ds).
Local Notation sn := (ds_sym_next ds).
Hypothesis Hok : compress_block_ok PBL ds lfc ldl dfc ddl.
Hypothesis Hlfc : forall i, 0 <= i < 286 -> 0 <= arr_get lfc i < 65536.
Hypothesis Hdfc : forall i, 0 <= i < 30 -> 0 <= arr_get dfc i < 65536.
Hypothesis Hlens : compress_lens_ok ds lfc ldl dfc ddl.
Hypothesis HLT : 0 <= LT /\ LT + 1144 <= 2 ^ 63.
Hypothesis HDT : 0 <= DT /\ DT + 120 <= 2 ^ 63.
Hypothesis Hsn : 0 <= sn /\ sn + 3 < 2 ^ 31.
Hypothesis HLBr : 0 <= LB < 2 ^ 32.
Hypothesis HPBL : 0 < PBL.


Definition PURE (s : deflate_state) : Prop :=
  PBB s /\ BINV PBL s
  /\ (forall t, tree_fc s t = tree_fc ds t) /\ (forall t, tree_dl s t = tree_dl ds t)
  /\ ds_lit_bufsize s = LB /\ ds_sym_next s = sn /\ arr_len (ds_pending_buf s) = PBL.

Definition GI : franges := [(S, 5952); (PB, PBL)].

Lemma PURE_send : forall s v l, PURE s -> 0 <= l <= 16 -> sb_room PBL s l -> PURE (send_bits s v l).
Proof.
  intros s v l (P1 & P2 & P3 & P4 & P5 & P6 & P7) Hl Hr. unfold PURE.
  split.
  { unfold PBB in *. unfold send_bits, put_short, put_byte. destruct (Buf_size - l <? ds_bi_valid s); dsred; [|exact P1].
    rewrite !arr_len_set. intros i Hi. rewrite !arr_get_set.
    destruct (_ && _); [apply wrap8_range|]. destruct (_ && _); [apply wrap8_range|]. apply P1. exact Hi. }
  split; [apply send_bits_BINV; assumption|].
  split; [intros t; rewrite sb_tree_fc; apply P3|]. split; [intros t; rewrite sb_tree_dl; apply P4|].
  pose proof (sb_pbl s v l) as E. rewrite send_bits_shape in E |- *. cbn [upd4] in E |- *. dsred. rewrite E. tauto.
Qed.


Definition cbF (A : arr) (f : nat) (x : Z) : Z :=
  match f with
  | 0%nat => wb A x
  | 1%nat => pb lfc x | 2%nat => pb ldl x | 3%nat => pb dfc x | 4%nat => pb ddl x
  | 5%nat => arr_get length_code_a x | 6%nat => arr_get dist_code_a x
  | 7%nat => arr_get extra_lbits_a x | 8%nat => arr_get base_length_a x
  | 9%nat => arr_get extra_dbits_a x | _ => arr_get base_dist_a x
  end.

Definition VB : bounds :=
  [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 2 ^ 63); (35%nat, 2 ^ 40); (36%nat, 17);
   (37%nat, 2 ^ 63); (38%nat, 2 ^ 63); (39%nat, 256); (40%nat, 65536); (41%nat, 2 ^ 31);
   (42%nat, 2 ^ 31); (43%nat, 30); (44%nat, 2 ^ 63); (45%nat, 2 ^ 64); (46%nat, 65536)].

Local Ltac nf := cbn [cbF].

Local Ltac vcongr := first [ reflexivity | apply szwrap32_mod16 | rewrite szwrap32_mod16; reflexivity
                           | rewrite Z.mod_mod by lia; reflexivity
                           | rewrite Z.mod_mod, wrap32_mod, mod_pow2_mod_pow2 by lia; reflexivity ].
Local Ltac vwrap := first [ reflexivity | symmetry; apply wrap16_id; lia
                          | rewrite wrap16_mod'; reflexivity | rewrite wrap16_mod', szwrap32_mod16; reflexivity
                          | rewrite wrap16_mod', wrap32_mod, mod_pow2_mod_pow2 by lia; reflexivity ].
Local Ltac vrange := first [ lia | apply Z.mod_pos_bound; lia ].
Local Ltac pure_fin HP := first [exact HP | apply PURE_send; [exact HP | lia | unfold sb_room, Buf_size; intros; lia]].




Local Ltac frw H1 H2 := let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr; rewrite (H2 r Hr); exact (H1 r Hr).

End Walk.
