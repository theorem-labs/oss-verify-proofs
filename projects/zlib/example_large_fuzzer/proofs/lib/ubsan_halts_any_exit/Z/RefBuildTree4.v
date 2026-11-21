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
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefBuildTree3.
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
