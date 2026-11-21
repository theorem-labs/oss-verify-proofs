(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DSLayout.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import TreeMem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ScanModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import TrSmallModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import Trees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefBitsLib.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefBitsFwd.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefTreesApi.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefSendTree1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefSendTree2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefSendTree3.
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
Variable t : tree_id.
Variable mc : Z.
Local Notation PB := (p_pending_buf p).
Local Notation T := (S + toff t).
(* [comment removed for export] *)
Local Notation L i := (Len ds t i).
Local Notation BC c := (arr_get (ds_bl_tree_fc ds) c).
Local Notation BL c := (arr_get (ds_bl_tree_dl ds) c).
Let Htt : 212 <= toff t /\ toff t + 4 * tsize t <= 2904 /\ 1 <= tsize t <= 573 := toff_tsize t.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Local Notation PURE := (RefSendTree1.PURE PBL ds).
Local Notation GI := (RefSendTree1.GI S p PBL).
Local Notation stF := (RefSendTree1.stF ds t).
Local Notation cnts0 := (RefSendTree3.cnts0 ds t).

Local Ltac nf := cbn [RefSendTree1.stF].

(* [comment removed for export] *)
Local Ltac vcongr := first [ reflexivity | apply szwrap32_mod16 | rewrite szwrap32_mod16; reflexivity
                           | rewrite Z.mod_mod by lia; reflexivity
                           | rewrite Z.mod_mod by lia; apply szwrap32_mod16
                           | rewrite ?szwrap32_mod16, ?Z.mod_mod by lia; apply mod16_congr; lia ].
Local Ltac vwrap := first [ reflexivity | symmetry; apply wrap16_id; lia
                          | rewrite wrap16_mod'; reflexivity | rewrite wrap16_mod', szwrap32_mod16; reflexivity
                          | apply wrap16_id'; lia ].
Local Ltac vrange := first [ lia | apply Z.mod_pos_bound; lia ].
Local Ltac pure_fin HP := first [exact HP | apply PURE_send; [exact HP | lia | unfold sb_room, Buf_size; intros; lia]].

Local Ltac kregs_open K :=
  destruct K as (K10 & K15 & K30 & K29 & K5 & K6 & K8 & K7 & K31 & K9 & K2).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition SL (s : deflate_state) (n pl c k mx mn : Z) : deflate_state :=
  send_tree_loop (Z.to_nat (mc + 1 - n)) s t mc n pl c k mx mn.
Definition OK (s : deflate_state) (n pl c k mx mn : Z) : Prop :=
  send_tree_ok PBL (Z.to_nat (mc + 1 - n)) s t mc n pl c k mx mn.

(* [comment removed for export] *)
Definition cnts (pl c : Z) : Z * Z := if c =? 0 then (138, 3) else if c =? pl then (6, 3) else (7, 4).

Definition BND (pl c k mx mn : Z) : Prop :=
  (pl = -1 \/ 0 <= pl <= 15) /\ 0 <= c <= 15 /\ 0 <= k < mx /\ (mx, mn) = cnts pl c.

Local Ltac frc2 a b := let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr; rewrite (a r Hr); exact (b r Hr).

(* [comment removed for export] *)

Section Level.

(* [comment removed for export] *)
Local Ltac bnd :=
  unfold BND, cnts;
  repeat match goal with |- context [?x =? ?y] =>
    first [ rewrite (proj2 (Z.eqb_neq x y)) by lia | rewrite (proj2 (Z.eqb_eq x y)) by lia ] end;
  repeat split; try lia; try reflexivity.

(* [comment removed for export] *)
Local Ltac cnts_in H :=
  unfold cnts in H |- *;
  repeat match type of H with context [?x =? ?y] =>
    first [ replace (x =? y) with false in H |- * by (symmetry; apply Z.eqb_neq; lia)
          | replace (x =? y) with true in H |- * by (symmetry; apply Z.eqb_eq; lia) ] end;
  cbv beta iota in H; cbv beta iota.

Local Ltac frc3 a b c := let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr; rewrite (a r Hr), (b r Hr); exact (c r Hr).
End Level.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition send_tree_safe : Prop := OK ds 0 (-1) (L 0) 0 (fst cnts0) (snd cnts0).

End Walk.
