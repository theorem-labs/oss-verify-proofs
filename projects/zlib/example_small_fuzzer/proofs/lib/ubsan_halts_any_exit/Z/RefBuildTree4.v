(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefTreesApi.TreeMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TreesRod.

Module BuildTreeRod.

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TreesRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZSeqExecP.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZSeqExecP.BvAux.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition SDA (t : tree_id) : Z := match t with TL => A_static_l_desc | TD => A_static_d_desc | TB => A_static_bl_desc end.
Definition STP (t : tree_id) : Z := match t with TL => A_static_ltree | TD => A_static_dtree | TB => 0 end.
Definition EXP (t : tree_id) : Z := match t with TL => A_extra_lbits | TD => A_extra_dbits | TB => A_extra_blbits end.

Definition sdesc_w64 (j : Z) : Z :=
  match j with
  | 0 => A_static_ltree | 1 => A_extra_lbits | 2 => 257 + 286 * 2 ^ 32 | 3 => 15
  | 4 => A_static_dtree | 5 => A_extra_dbits | 6 => 0 + 30 * 2 ^ 32 | 7 => 15
  | 8 => 0 | 9 => A_extra_blbits | 10 => 0 + 19 * 2 ^ 32 | _ => 7
  end.

Lemma divmod8 : forall i k, 0 <= i -> 0 <= k < 8 -> (8 * i + k) mod 8 = k /\ (8 * i + k) / 8 = i.
Proof.
  intros i k Hi Hk. split.
  - rewrite Z.add_comm, Z.mul_comm, Z.mod_add, Z.mod_small; lia.
  - rewrite Z.add_comm, Z.mul_comm, Z.div_add, Z.div_small; lia.
Qed.

Section Rod.

Local Ltac ua := unfold TREES_ROD_LO, TREES_ROD_HI, A_static_l_desc, A_static_d_desc, A_static_bl_desc,
    A_length_code, A_extra_lbits, A_base_length, A_dist_code, A_extra_dbits, A_base_dist,
    A_static_dtree, A_static_ltree, A_bl_order, A_extra_blbits in *.

Definition sdesc_w32 (j : Z) : Z :=
  match j with
  | 0 => A_static_ltree | 2 => A_extra_lbits | 4 => 257 | 5 => 286 | 6 => 15
  | 8 => A_static_dtree | 10 => A_extra_dbits | 13 => 30 | 14 => 15
  | 18 => A_extra_blbits | 21 => 19 | 22 => 7
  | _ => 0
  end.

End Rod.
End BuildTreeRod.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.BuildTreeRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import BuildTreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import GenBitlenModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require  GenCodesModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefTreesApi.RefBitsLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefTreesApi.

Module RefBuildTreeLib.

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefTreesApi.TreeMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import MemFill.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import BuildTreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefTreesApi.RefBitsLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefTreesApi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Lemma dsc_off_range : forall t, 2904 <= dsc_off t <= 2952.
Proof. intros [| |]; cbn; lia. Qed.


Section RelT.
Variable F : franges.
Variable S : Z.
Variable p : ds_ptrs.
Variable PBL : Z.
Local Notation PB := (p_pending_buf p).

Variable s : deflate_state.
Variable t : tree_id.
Local Notation U FC DL HP HL' HM DP BC OL SL MC := (bt_upd s t FC DL HP HL' HM DP BC OL SL MC).

End RelT.


Inductive skind := KFc (i : Z) | KDl (i : Z) | KHeap (i : Z) | KDepth (i : Z) | KBlc (i : Z)
                 | KHl | KHm | KOpt | KStat | KOptW | KStatW | KMc | KOther.

Ltac st_eqT :=
  autorewrite with btupd;
  lazymatch goal with
  | |- bt_upd ?s ?t _ _ _ _ _ _ _ _ _ _ = bt_upd ?s ?t _ _ _ _ _ _ _ _ _ _ => apply bt_upd_congr
  end.
End RefBuildTreeLib.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.RefBuildTreeLib.

Module RefPqdown_run.

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefTreesApi.TreeMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Section Walk.
Variable S : Z.
Variable p : ds_ptrs.
Variable ds : deflate_state.
Variable t : tree_id.
Local Notation hl := (ds_heap_len ds).
Local Notation T := (S + toff t).
Local Notation TF := (tree_fc ds t).
Local Notation DP := (ds_depth ds).
Hypothesis HL : tree_lens ds.
Hypothesis Hhl : 1 <= hl <= 572.
Hypothesis Hpq : pq_ok (tsize t) ds.
Hypothesis Hfreq : forall i, 0 <= i < tsize t -> 0 <= arr_get TF i < 65536.
Hypothesis Hdep : forall i, 0 <= i < 573 -> 0 <= arr_get DP i < 256.

Definition LF : franges := [(S + 3008, 2292)].

Let Ht : 212 <= toff t /\ toff t + 4 * tsize t <= 2904 /\ 1 <= tsize t <= 573 := toff_tsize t.
Let HlenF : arr_len TF = tsize t := tree_lens_fc ds t HL.
Let HlenD : arr_len DP = 573 := proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HL))))))).
Let HlenH : arr_len (ds_heap ds) = 573 := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HL))))))).

Lemma tree_lens_sh : forall h, arr_len h = 573 -> tree_lens (set_heap ds h).
Proof.
  intros h Hh. pose proof HL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9). unfold tree_lens.
  cbn [set_heap ds_dyn_ltree_fc ds_dyn_ltree_dl ds_dyn_dtree_fc ds_dyn_dtree_dl ds_bl_tree_fc ds_bl_tree_dl ds_bl_count ds_heap ds_depth].
  repeat split; assumption.
Qed.


Definition pqF (h : arr) (f : nat) (x : Z) : Z :=
  match f with 0%nat => pb TF x | 1%nat => hv h x | _ => wb DP x end.
Definition VB : bounds :=
  [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 600); (35%nat, 573); (36%nat, 600); (37%nat, 600); (38%nat, 600)].

Definition sel (h : arr) (j : Z) : Z :=
  if (j <? hl) && smaller ds t (arr_get h (j + 1)) (arr_get h j) then j + 1 else j.

Local Ltac node h i V R PF PD :=
  assert (R : 0 <= arr_get h i < tsize t) by (auto with zarith || (match goal with Hr : forall n, 1 <= n <= hl -> _ |- _ => apply Hr; lia end));
  assert (V : hv h i = arr_get h i) by (apply hv_get; lia);
  assert (PF : pb TF (arr_get h i) = Freq ds t (arr_get h i)) by (unfold Freq; apply (pb_get TF); [intros q Hq; apply Hfreq; lia | lia]);
  assert (PD : wb DP (arr_get h i) = depth_get ds (arr_get h i)) by (unfold depth_get; apply (wb_get DP); [intros q Hq; apply Hdep; lia | lia]).

Local Ltac nf :=
  cbn [pqF];
  repeat match goal with H : hv ?hh ?e = arr_get ?hh ?e |- context [hv ?hh ?e] => rewrite !H end;
  repeat match goal with H : pb ?a ?e = _ |- context [pb ?a ?e] => rewrite !H end;
  repeat match goal with H : wb ?a ?e = _ |- context [wb ?a ?e] => rewrite !H end.

Local Ltac open_hregs H :=
  let H' := fresh "HR'" in pose proof H as H';
  destruct H' as (P10 & P11 & P13 & P5 & P15 & P6 & P28 & P7 & P30 & P1).


Local Ltac open_mregs H :=
  let H' := fresh "MR'" in pose proof H as H';
  destruct H' as ((P10 & P11 & P13 & P5 & P15 & P6 & P28 & P7 & P30 & P1) & P12 & P17 & P14).

Local Ltac vt := first [ reflexivity | nf; reflexivity | nf; assumption | nf; lia ].


Lemma sel_range : forall h j, 1 <= j <= hl -> j <= sel h j <= hl /\ sel h j <= j + 1.
Proof.
  intros h j Hj. unfold sel. destruct (Z.ltb_spec j hl); cbn [andb]; [destruct (smaller _ _ _ _)|]; lia.
Qed.

Lemma loop_S_sel : forall f h v k j, j <= hl ->
  pqdownheap_loop (Datatypes.S f) (set_heap ds h) t v k j =
    if smaller ds t v (arr_get h (sel h j)) then (set_heap ds h, k)
    else pqdownheap_loop f (set_heap ds (arr_set h k (arr_get h (sel h j)))) t v (sel h j) (2 * sel h j).
Proof.
  intros f h v k j Hj. rewrite pqdownheap_loop_S. rewrite sh_heap_len.
  replace (j <=? hl) with true by (symmetry; apply Z.leb_le; lia). cbv zeta.
  rewrite !sh_smaller, !sh_heap_get. unfold sel.
  rewrite Z.shiftl_mul_pow2 by lia. rewrite (Z.mul_comm _ (2 ^ 1)). reflexivity.
Qed.

End Walk.
End RefPqdown_run.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.RefPqdown_run.

Module RefGenCodes_run.

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefTreesApi.TreeMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require SendModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.SendModel.ScanModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import GenCodesModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Section Walk.
Variable S : Z.
Variable p : ds_ptrs.
Variable ds : deflate_state.
Variable t : tree_id.
Variable mc : Z.
Variable sp : Z.
Local Notation T := (S + toff t).
Local Notation BLC := (ds_bl_count ds).
Local Notation DL := (tree_dl ds t).
Hypothesis HL : tree_lens ds.
Hypothesis Hsp : 0 <= sp /\ sp + 80 <= 2 ^ 63.
Hypothesis Hmc : 0 <= mc < tsize t.
Hypothesis Hlen : forall i, 0 <= i <= mc -> 0 <= Len ds t i <= 15.
Hypothesis Hdl : forall i, 0 <= i < tsize t -> 0 <= arr_get DL i < 65536.
Hypothesis Hblc : forall i, 0 <= i < 16 -> 0 <= arr_get BLC i < 65536.

Definition LF : franges := [(sp + 48, 32); (S + toff t, 4 * tsize t)].

Let Ht : 212 <= toff t /\ toff t + 4 * tsize t <= 2904 /\ 1 <= tsize t <= 573 := toff_tsize t.
Let HlenD : arr_len DL = tsize t := tree_lens_dl ds t HL.

Lemma stf_lens' : forall a, arr_len a = tsize t -> tree_lens (set_tree_fc ds t a).
Proof. intros a Ha. apply stf_lens; [exact HL | exact Ha]. Qed.

Lemma wrap16_65536 : forall z, 0 <= wrap16 z < 65536.
Proof. intros z. pose proof (wrap16_range' z). change (2 ^ 16) with 65536 in H. exact H. Qed.


Definition gcF (nc : arr) (f : nat) (x : Z) : Z :=
  match f with 0%nat => pb BLC x | 1%nat => pb DL x | _ => pb nc x end.
Definition VB : bounds :=
  [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 600); (35%nat, 2 ^ 63); (36%nat, 600); (37%nat, 16);
   (38%nat, 65536); (39%nat, 65536)].

Local Ltac nf :=
  cbn [gcF];
  repeat match goal with H : pb ?a ?e = _ |- context [pb ?a ?e] => rewrite !H end.

Local Ltac open_cregs H :=
  let H' := fresh "CR'" in pose proof H as H'; destruct H' as (P21 & P2 & P11 & P16).

Local Ltac len_fact i V :=
  assert (V : pb DL i = Len ds t i) by (unfold Len; apply (pb_get DL); [intros q Hq; apply Hdl; rewrite HlenD in Hq; exact Hq | rewrite HlenD; lia]).


Local Ltac frc2 a b := let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr; rewrite (a r Hr); exact (b r Hr).
Local Ltac frc3 a b c := let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr; rewrite (a r Hr), (b r Hr); exact (c r Hr).
Local Ltac frc4 a b c d := let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr; rewrite (a r Hr), (b r Hr), (c r Hr); exact (d r Hr).

Lemma pb_blc : forall i, 0 <= i < 16 -> pb BLC i = arr_get BLC i.
Proof. intros i Hi. unfold pb. apply Z.mod_small. apply Hblc. exact Hi. Qed.

Local Ltac szw16 :=
  first [ reflexivity
        | rewrite <- (mod_pow2_mod_pow2 (szwrap 32 _) 32 16) by lia; rewrite szwrap_eqm by lia;
          rewrite (mod_pow2_mod_pow2 _ 32 16) by lia; reflexivity ].

End Walk.
End RefGenCodes_run.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.RefGenCodes_run.

Module RefBuildTree1.
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefTreesApi.TreeMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TreesRod.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.BuildTreeRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import BuildTreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefTreesApi.RefBitsLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.RefBuildTreeLib.
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
Lemma SDA_range : 192320 <= SDA t <= 192384.
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
End RefBuildTree1.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.

Module RefBuildTree2.
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefTreesApi.TreeMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TreesRod.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.BuildTreeRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import BuildTreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefTreesApi.RefBitsLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.RefBuildTreeLib.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.
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
Local Notation stree_dl := (RefBuildTree1.stree_dl t).
Local Notation stF := (RefBuildTree1.stF t).
Local Notation X0 := (RefBuildTree1.X0 ds t).
Local Notation L1 := (RefBuildTree1.L1 t).
Local Notation tsize_elems := (RefBuildTree1.tsize_elems t).
Local Notation elems_range := (RefBuildTree1.elems_range t).
Local Notation dsc_off_val := (RefBuildTree1.dsc_off_val t).
Local Notation SDA_range := (RefBuildTree1.SDA_range t).
Local Notation STP_range := (RefBuildTree1.STP_range t).

Local Ltac nf := cbn [RefBuildTree1.stF].


Lemma stree_has_STP : stree_has t = true <-> STP t <> 0.
Proof. destruct t; cbn; unfold A_static_ltree, A_static_dtree; split; intros; try congruence; lia. Qed.

Definition slen : Z := match t with TL => 288 | TD => 30 | TB => 1 end.

Lemma stree_Len_dl : forall n, stree_Len t n = arr_get stree_dl n.
Proof. intros n. unfold RefBuildTree1.stree_dl. destruct t; cbn [stree_Len]; rewrite ?arr_get_make; reflexivity. Qed.

Lemma stree_dl_bound : forall n, 0 <= n < slen -> 0 <= arr_get stree_dl n < 16.
Proof.
  intros n _. unfold RefBuildTree1.stree_dl. destruct t.
  - pose proof (static_ltree_dl_bound n). lia.
  - pose proof (static_dtree_dl_bound n). lia.
  - rewrite arr_get_make. lia.
Qed.

Lemma slen_ge : STP t <> 0 -> 3 <= slen.
Proof. unfold slen. destruct t; cbn; intros; lia. Qed.

Section PhaseC.
Variable DL : arr.
Variable HM : Z.
Variable BC : arr.
Variable MC : Z.
Local Notation W FC HP HL DP OL SL := (U FC DL HP HL HM DP BC OL SL MC).

Definition l2node (mc : Z) : Z * Z := if mc <? 2 then (mc + 1, mc + 1) else (0, mc).

Definition L2 (X : deflate_state) (mc : Z) : deflate_state * Z := build_tree_loop2 2 X t mc.

Lemma L2_out : forall f FC HP HL DP OL SL mc, 2 <= HL ->
  build_tree_loop2 f (W FC HP HL DP OL SL) t mc = (W FC HP HL DP OL SL, mc).
Proof.
  intros [|f] FC HP HL DP OL SL mc Hhl; [reflexivity|]. cbn [build_tree_loop2]. autorewrite with btupd.
  replace (HL <? 2) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

Lemma L2_step : forall f FC HP HL DP OL SL mc, HL < 2 ->
  build_tree_loop2 (Datatypes.S f) (W FC HP HL DP OL SL) t mc =
    (let '(node, mc') := l2node mc in
     build_tree_loop2 f
       (W (arr_set FC node (wrap16 1)) (arr_set HP (HL + 1) node) (HL + 1) (arr_set DP node (wrap8 0)) (wrap64 (OL - 1))
          (if stree_has t then wrap64 (SL - stree_Len t node) else SL)) t mc').
Proof.
  intros f FC HP HL DP OL SL mc Hhl. cbn [build_tree_loop2]. autorewrite with btupd.
  replace (HL <? 2) with true by (symmetry; apply Z.ltb_lt; lia). unfold l2node.
  destruct (mc <? 2); autorewrite with btupd; destruct (stree_has t); autorewrite with btupd; reflexivity.
Qed.

Lemma L2_ge2 : forall FC HP HL DP OL SL mc, 2 <= HL -> L2 (W FC HP HL DP OL SL) mc = (W FC HP HL DP OL SL, mc).
Proof. intros. unfold L2. apply L2_out. assumption. Qed.

Lemma L2_hl1 : forall FC HP DP OL SL mc,
  L2 (W FC HP 1 DP OL SL) mc =
    (let '(node, mc') := l2node mc in
     (W (arr_set FC node (wrap16 1)) (arr_set HP 2 node) 2 (arr_set DP node (wrap8 0)) (wrap64 (OL - 1))
        (if stree_has t then wrap64 (SL - stree_Len t node) else SL), mc')).
Proof.
  intros. unfold L2. rewrite L2_step by lia. unfold l2node.
  destruct (mc <? 2); (rewrite L2_out by lia); reflexivity.
Qed.

Lemma L2_hl0 : forall FC HP DP OL SL,
  L2 (W FC HP 0 DP OL SL) (-1) =
    (W (arr_set (arr_set FC 0 (wrap16 1)) 1 (wrap16 1)) (arr_set (arr_set HP 1 0) 2 1) 2
        (arr_set (arr_set DP 0 (wrap8 0)) 1 (wrap8 0)) (wrap64 (wrap64 (OL - 1) - 1))
        (if stree_has t then wrap64 ((if stree_has t then wrap64 (SL - stree_Len t 0) else SL) - stree_Len t 1)
         else (if stree_has t then wrap64 (SL - stree_Len t 0) else SL)), 1).
Proof.
  intros. unfold L2. rewrite L2_step by lia. unfold l2node. cbn [Z.ltb Z.compare Pos.compare].
  replace (-1 + 1) with 0 by reflexivity. replace (0 + 1) with 1 by reflexivity.
  rewrite L2_step by lia. unfold l2node. cbn [Z.ltb Z.compare Pos.compare].
  replace (1 + 1) with 2 by reflexivity. replace (0 + 1) with 1 by reflexivity.
  rewrite L2_out by lia. reflexivity.
Qed.

Lemma stree_pb : forall n, 0 <= n < slen -> pb stree_dl n = arr_get stree_dl n.
Proof. intros n Hn. unfold pb. apply Z.mod_small. pose proof (stree_dl_bound n Hn). lia. Qed.

Lemma STP_rod : STP t <> 0 -> 191072 <= STP t /\ STP t + 2 + 4 * slen <= 193788.
Proof. unfold slen. destruct t; cbn; unfold A_static_ltree, A_static_dtree; intros; lia. Qed.

Local Ltac ceq :=
  first [ reflexivity
        | rewrite ?arr_set_set_same; reflexivity
        | nf; rewrite ?stree_pb by lia; rewrite ?wrap64_sub_l; first [reflexivity | f_equal; lia] ].
End PhaseC.

End Walk.
End RefBuildTree2.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.RefBuildTree2.

Module RefBuildTree3.
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefTreesApi.TreeMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TreesRod.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.BuildTreeRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import BuildTreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import GenBitlenModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require  GenCodesModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefTreesApi.RefBitsLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.RefBuildTreeLib.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.RefPqdown_run.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.RefGenCodes_run.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.RefBuildTree1.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.RefBuildTree2.
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
Local Notation stree_dl := (RefBuildTree1.stree_dl t).
Local Notation stF := (RefBuildTree1.stF t).
Local Notation X0 := (RefBuildTree1.X0 ds t).
Local Notation L1 := (RefBuildTree1.L1 t).
Local Notation tsize_elems := (RefBuildTree1.tsize_elems t).
Local Notation elems_range := (RefBuildTree1.elems_range t).
Local Notation dsc_off_val := (RefBuildTree1.dsc_off_val t).
Local Notation SDA_range := (RefBuildTree1.SDA_range t).
Local Notation STP_range := (RefBuildTree1.STP_range t).
Local Notation L2 := (RefBuildTree2.L2 t).
Local Notation slen := (RefBuildTree2.slen t).

Local Ltac nf := cbn [RefBuildTree1.stF].



Definition pqF3 (FC HP DP : arr) (f : nat) (x : Z) : Z :=
  match f with 0%nat => pb FC x | 1%nat => hv HP x | _ => wb DP x end.

Definition VB3 : bounds :=
  [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 600); (35%nat, 573); (36%nat, 600); (37%nat, 600); (38%nat, 600);
   (39%nat, 600); (40%nat, 2 ^ 63); (41%nat, 600); (42%nat, 3000); (43%nat, 300)].

Section PhaseD.
Variable FC : arr.
Variable DL : arr.
Variable HL : Z.
Variable HM : Z.
Variable DP : arr.
Variable BC : arr.
Variable OL : Z.
Variable SL : Z.
Variable MC : Z.
Local Notation W h := (U FC DL h HL HM DP BC OL SL MC).

Hypothesis RFC : forall i, 0 <= i < tsize t -> 0 <= arr_get FC i < 65536.
Hypothesis RDP : forall i, 0 <= i < 573 -> 0 <= arr_get DP i < 256.
Hypothesis Hhl : 2 <= HL <= 572.
Hypothesis LFC : arr_len FC = tsize t.
Hypothesis LDP : arr_len DP = 573.

Definition smal (n m : Z) : bool :=
  (arr_get FC n <? arr_get FC m) || ((arr_get FC n =? arr_get FC m) && (arr_get DP n <=? arr_get DP m)).

Lemma smaller_W : forall h n m, smaller (W h) t n m = smal n m.
Proof. intros. unfold smaller, smal. autorewrite with btupd. reflexivity. Qed.

Definition sel3 (h : arr) (j : Z) : Z :=
  if (j <? HL) && smal (arr_get h (j + 1)) (arr_get h j) then j + 1 else j.

Lemma sel3_range : forall h j, 1 <= j <= HL -> j <= sel3 h j <= HL /\ sel3 h j <= j + 1.
Proof.
  intros h j Hj. unfold sel3. destruct (Z.ltb_spec j HL); cbn [andb]; [destruct (smal _ _)|]; lia.
Qed.

Definition PQ (h : arr) : Prop := forall i, 1 <= i <= HL -> 0 <= arr_get h i < tsize t.


Local Ltac node h i V R PF PD :=
  assert (R : 0 <= arr_get h i < tsize t) by (match goal with Hr : PQ h |- _ => apply Hr; lia end);
  assert (V : hv h i = arr_get h i) by (apply hv_get; lia);
  assert (PF : pb FC (arr_get h i) = arr_get FC (arr_get h i)) by (apply (pb_get FC); [intros q Hq; apply RFC; rewrite <- LFC; exact Hq | rewrite LFC; lia]);
  assert (PD : wb DP (arr_get h i) = arr_get DP (arr_get h i)) by (apply (wb_get DP); [intros q Hq; apply RDP; rewrite <- LDP; exact Hq | rewrite LDP; lia]).

Local Ltac nf3 :=
  cbn [pqF3];
  repeat match goal with H : hv ?hh ?e = arr_get ?hh ?e |- context [hv ?hh ?e] => rewrite !H end;
  repeat match goal with H : pb ?a ?e = _ |- context [pb ?a ?e] => rewrite !H end;
  repeat match goal with H : wb ?a ?e = _ |- context [wb ?a ?e] => rewrite !H end.

Local Ltac open_h3 H :=
  let H' := fresh "HR'" in pose proof H as H';
  destruct H' as ((P21 & P22 & P2 & P12 & P11 & P16 & P17 & P28 & P10 & P8) & P31 & P6 & P15 & P29 & P30).
Local Ltac open_m3 H :=
  let H' := fresh "MR'" in pose proof H as H';
  destruct H' as (((P21 & P22 & P2 & P12 & P11 & P16 & P17 & P28 & P10 & P8) & P31 & P6 & P15 & P29 & P30) & P13 & P5 & P14).


Lemma loop3_S_sel : forall f h v k j, j <= HL ->
  pqdownheap_loop (Datatypes.S f) (W h) t v k j =
    if smal v (arr_get h (sel3 h j)) then (W h, k)
    else pqdownheap_loop f (W (arr_set h k (arr_get h (sel3 h j)))) t v (sel3 h j) (sel3 h j * 2).
Proof.
  intros f h v k j Hj. rewrite pqdownheap_loop_S. autorewrite with btupd.
  replace (j <=? HL) with true by (symmetry; apply Z.leb_le; lia). cbv zeta.
  autorewrite with btupd. rewrite !smaller_W. unfold sel3.
  destruct ((j <? HL) && smal (arr_get h (j + 1)) (arr_get h j)).
  - destruct (smal v (arr_get h (j + 1))); [reflexivity|]. autorewrite with btupd.
    rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2. reflexivity.
  - destruct (smal v (arr_get h j)); [reflexivity|]. autorewrite with btupd.
    rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2. reflexivity.
Qed.

Definition L3 (h : arr) (n : Z) : deflate_state := build_tree_loop3 (Z.to_nat n) (W h) t n.


Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
End PhaseD.

End Walk.
End RefBuildTree3.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefBuildTree4.RefBuildTree3.
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
Local Notation stree_dl := (RefBuildTree1.stree_dl t).
Local Notation stF := (RefBuildTree1.stF t).
Local Notation X0 := (RefBuildTree1.X0 ds t).
Local Notation L1 := (RefBuildTree1.L1 t).
Local Notation tsize_elems := (RefBuildTree1.tsize_elems t).
Local Notation elems_range := (RefBuildTree1.elems_range t).
Local Notation dsc_off_val := (RefBuildTree1.dsc_off_val t).
Local Notation SDA_range := (RefBuildTree1.SDA_range t).
Local Notation STP_range := (RefBuildTree1.STP_range t).
Local Notation L2 := (RefBuildTree2.L2 t).
Local Notation slen := (RefBuildTree2.slen t).

Local Ltac nf := cbn [RefBuildTree1.stF].

Definition VB4 : bounds :=
  [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 2 ^ 63); (35%nat, 300); (36%nat, 600); (37%nat, 600);
   (38%nat, 600); (39%nat, 573); (40%nat, 573)].

Section PhaseE.
Variable BC : arr.
Variable OL : Z.
Variable SL : Z.
Variable MC : Z.
Local Notation W6 FC DL HP HL HM DP := (U FC DL HP HL HM DP BC OL SL MC).


Definition RNG (FC DP : arr) : Prop :=
  (forall i, 0 <= i < tsize t -> 0 <= arr_get FC i < 65536) /\ (forall i, 0 <= i < 573 -> 0 <= arr_get DP i < 256)
  /\ arr_len FC = tsize t /\ arr_len DP = 573.

Definition PQ4 (HP : arr) (HL : Z) : Prop := (forall i, 1 <= i <= HL -> 0 <= arr_get HP i < tsize t) /\ arr_len HP = 573.

Local Ltac nf3 :=
  cbn [pqF3];
  repeat match goal with H : hv ?hh ?e = arr_get ?hh ?e |- context [hv ?hh ?e] => rewrite !H end;
  repeat match goal with H : pb ?a ?e = _ |- context [pb ?a ?e] => rewrite !H end;
  repeat match goal with H : wb ?a ?e = _ |- context [wb ?a ?e] => rewrite !H end.

Local Ltac nodef FC DP x R PF PD :=
  assert (PF : pb FC x = arr_get FC x)
    by (apply (pb_get FC); [intros q Hq; match goal with Hr : RNG FC DP |- _ => apply (proj1 Hr); rewrite <- (proj1 (proj2 (proj2 Hr))); exact Hq end
                         | match goal with Hr : RNG FC DP |- _ => rewrite (proj1 (proj2 (proj2 Hr))); lia end]);
  assert (PD : wb DP x = arr_get DP x)
    by (apply (wb_get DP); [intros q Hq; match goal with Hr : RNG FC DP |- _ => apply (proj1 (proj2 Hr)); rewrite <- (proj2 (proj2 (proj2 Hr))); exact Hq end
                         | match goal with Hr : RNG FC DP |- _ => rewrite (proj2 (proj2 (proj2 Hr))); lia end]).


Lemma pq_flat : forall FC DL HP HL HM DP,
  pqdownheap (W6 FC DL HP HL HM DP) t 1 = W6 FC DL (ds_heap (pqdownheap (W6 FC DL HP HL HM DP) t 1)) HL HM DP.
Proof.
  intros. rewrite (pqdownheap_shape (W6 FC DL HP HL HM DP) t 1) at 1. rewrite bt_set_heap. reflexivity.
Qed.

Lemma pq_ok_flat : forall FC DL HP HL HM DP,
  PQ4 HP HL -> 1 <= HL <= 572 -> pq_ok (tsize t) (W6 FC DL HP HL HM DP).
Proof.
  intros FC DL HP HL HM DP [HPQ LHP] Hhl i Hi. unfold heap_get. rewrite bt_heap. rewrite bt_heap_len in Hi. apply HPQ. exact Hi.
Qed.

Lemma heap_get_def : forall s i, heap_get s i = arr_get (ds_heap s) i.
Proof. reflexivity. Qed.

Lemma PQ4_after : forall FC DL HP HL HM DP,
  PQ4 HP HL -> 1 <= HL <= 572 -> PQ4 (ds_heap (pqdownheap (W6 FC DL HP HL HM DP) t 1)) HL.
Proof.
  intros FC DL HP HL HM DP HPQ Hhl. pose proof HPQ as [HPQ1 LHP]. split.
  - intros i Hi. rewrite <- heap_get_def.
    pose proof (pq_ok_pqdownheap (tsize t) (W6 FC DL HP HL HM DP) t 1 (pq_ok_flat FC DL HP HL HM DP HPQ Hhl)) as Q.
    rewrite bt_heap_len, bt_heap, LHP in Q. apply (Q ltac:(lia) ltac:(lia) i).
    rewrite pqdownheap_heap_len, bt_heap_len. exact Hi.
  - rewrite pqdownheap_len, bt_heap. exact LHP.
Qed.

Definition dmax (DP : arr) (n m : Z) : Z := if arr_get DP m <=? arr_get DP n then arr_get DP n else arr_get DP m.

Section Trip.
Variable FC : arr.
Variable DL : arr.
Variable HP : arr.
Variable HL : Z.
Variable HM : Z.
Variable DP : arr.
Variable node : Z.
Let n := arr_get HP 1.
Let HP1 := arr_set HP 1 (arr_get HP HL).
Let HP2 := ds_heap (pqdownheap (W6 FC DL HP1 (HL - 1) HM DP) t 1).
Let m_ := arr_get HP2 1.
Let FC' := arr_set FC node (wrap16 (arr_get FC n + arr_get FC m_)).
Let DL' := arr_set (arr_set DL m_ (wrap16 node)) n (wrap16 node).
Let HP3 := arr_set (arr_set (arr_set HP2 (HM - 1) n) (HM - 2) m_) 1 node.
Let DP' := arr_set DP node (wrap8 (dmax DP n m_ + 1)).
Definition trip : deflate_state := pqdownheap (W6 FC' DL' HP3 (HL - 1) (HM - 2) DP') t 1.

Lemma trip_flat : trip = W6 FC' DL' (ds_heap trip) (HL - 1) (HM - 2) DP'.
Proof. unfold trip. apply pq_flat. Qed.

Lemma L4_step : forall f,
  build_tree_loop4 (Datatypes.S f) (W6 FC DL HP HL HM DP) t node =
    if 2 <=? HL - 1 then build_tree_loop4 f trip t (node + 1) else trip.
Proof.
  intros f. cbn [build_tree_loop4]. unfold SMALLEST. autorewrite with btupd.
  rewrite (pq_flat FC DL (arr_set HP 1 (arr_get HP HL)) (HL - 1) HM DP).
  fold HP1. fold HP2. autorewrite with btupd.
  unfold trip. subst n m_ FC' DL' HP3 DP'. fold HP1. fold HP2.
  rewrite pqdownheap_heap_len, bt_heap_len. unfold dmax.
  replace (HM - 1 - 1) with (HM - 2) by lia. reflexivity.
Qed.
End Trip.
End PhaseE.

End Walk.
