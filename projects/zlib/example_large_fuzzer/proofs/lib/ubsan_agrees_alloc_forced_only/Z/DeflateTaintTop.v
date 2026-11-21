(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import Trees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateBlk.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import Deflate.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateSafe.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateOverlay.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ModelRel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflateRel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeFB.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeI1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeI2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeI4.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeL0.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeL2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeL3.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeL4.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeL5.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefDeflSafeI6.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateTaintRel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateTaintBlk.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateTaintCall.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateTaintInit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateTaintCore.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope sm_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma zlength_zfirstn_le {A} n (l : list A) : 0 <= n -> 0 <= zlength (zfirstn n l) <= n.
Proof.
  intros Hn. unfold zfirstn, zlength. rewrite length_firstn.
  pose proof (Nat.le_min_l (Z.to_nat n) (length l)). lia.
Qed.

Lemma bytes_okP_zfirstn n l : bytes_okP l -> bytes_okP (zfirstn n l).
Proof.
  unfold bytes_okP, zfirstn. generalize (Z.to_nat n) as k. intros k H. revert k.
  induction H as [|x l Hx H IH]; intros [|k]; cbn; constructor; auto.
Qed.

Lemma bytes_okP_zskipn' n l : bytes_okP l -> bytes_okP (zskipn n l).
Proof.
  unfold bytes_okP, zskipn. generalize (Z.to_nat n) as k. intros k H. revert k.
  induction H as [|x l Hx H IH]; intros [|k]; cbn; [constructor|constructor|constructor; auto|apply IH].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section End_.
  Context {MM : MallocModel}.
End End_.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record C2I (dl : Z) (src : list Z) (x1 x2 : c2st) : Prop := {
  ci_s : DCALL (c2_s x1) (c2_s x2);
  ci_z : c2_z x2 = c2_z x1;
  ci_left : c2_left x2 = c2_left x1;
  ci_sl : c2_sourceLen x2 = c2_sourceLen x1;
  ci_pos : c2_in_pos x2 = c2_in_pos x1;
  ci_ain : c2_avail_in x2 = c2_avail_in x1;
  ci_aout : c2_avail_out x2 = c2_avail_out x1;
  ci_out : c2_out_rev x2 = c2_out_rev x1;
  ci_err : c2_err x2 = c2_err x1;
  ci_zok : zstrm_okP (c2_z x1);
  ci_aout0 : 0 <= c2_avail_out x1 <= C2_MAX;
  ci_left0 : 0 <= c2_left x1;
  ci_sum_out : zlength (c2_out_rev x1) + c2_avail_out x1 + c2_left x1 = dl;
  ci_pos0 : 0 <= c2_in_pos x1;
  ci_ain0 : 0 <= c2_avail_in x1 <= C2_MAX;
  ci_sl0 : 0 <= c2_sourceLen x1;
  ci_sum_in : c2_in_pos x1 + c2_avail_in x1 + c2_sourceLen x1 = zlength src;
  ci_tot : zs_total_out (c2_z x1) = wrap64 (zlength (c2_out_rev x1));
  ci_outb : Forall (fun b => 0 <= b < 256) (c2_out_rev x1) }.

(* [comment removed for export] *)
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require  DeflateCongr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
