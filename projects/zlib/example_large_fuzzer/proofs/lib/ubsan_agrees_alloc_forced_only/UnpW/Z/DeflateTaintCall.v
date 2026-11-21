(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import Trees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateBlk.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import Deflate.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateSafe.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import DeflateTaintTrees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateTaintRel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import DeflateTaintBits.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import DeflateTaintBlk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Definition DQ (s1 s2 : deflate_state) : Prop :=
  exists W C B bnd ms pm,
    REL W C B bnd ms pm s1 s2
    /\ (forall i, i < WHI s1 -> W i)
    /\ (ds_level s1 <> 0 -> bnd <= ds_strstart s1)
    /\ (forall i, ds_pending_out s1 <= i < ds_pending_out s1 + ds_pending s1 -> B i)
    /\ SYMB B s1
    /\ HWI s1.

(* [comment removed for export] *)
Definition DCALL (s1 s2 : deflate_state) : Prop :=
  DQ s1 s2 /\ INV s1 /\ INV s2 /\ dreach s1 /\ dreach s2.

(* [comment removed for export] *)
Definition DEFLATE_M_REL : Prop :=
  forall s1 s2 zc flush,
    DCALL s1 s2 -> dcall_wf zc -> (flush = Z_NO_FLUSH \/ flush = Z_FINISH) ->
    snd (deflate_m s1 zc flush) = snd (deflate_m s2 zc flush)
    /\ DCALL (fst (deflate_m s1 zc flush)) (fst (deflate_m s2 zc flush)).

Lemma DQ_clean s1 s2 : DQ s1 s2 -> clean s1 = clean s2.
Proof. intros (W & C & B & bnd & ms & pm & R & _). exact (r_clean _ _ _ _ _ _ _ _ R). Qed.

Lemma DREL_DQ s1 s2 : DREL s1 s2 -> DQ s1 s2.
Proof.
  intros (W & C & B & bnd & ms & pm & R & HW & Hb & HP & HS & HH). exists W, C, B, bnd, ms, pm.
  split; [exact R|]. split; [exact HW|]. split; [exact Hb|]. split; [|exact (conj HS HH)].
  destruct HP as [[P1 P2]|[P1 P2]]; [rewrite P1; intros i Hi; apply P2; lia|exact P2].
Qed.
Lemma DQ_DREL s1 s2 : DQ s1 s2 -> ds_pending s1 = 0 -> ds_pending_out s1 = 0 -> DREL s1 s2.
Proof.
  intros (W & C & B & bnd & ms & pm & R & HW & Hb & HP & HS & HH) Hp Hpo. exists W, C, B, bnd, ms, pm.
  split; [exact R|]. split; [exact HW|]. split; [exact Hb|]. split; [left; rewrite Hp, Hpo; split; [reflexivity|intros; lia]|exact (conj HS HH)].
Qed.
