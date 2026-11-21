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
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require  GenCodesModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Trees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefBitsLib.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefTreesApi.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefBuildTreeLib.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefPqdown_run.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefGenCodes_run.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefBuildTree1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefBuildTree2.
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
