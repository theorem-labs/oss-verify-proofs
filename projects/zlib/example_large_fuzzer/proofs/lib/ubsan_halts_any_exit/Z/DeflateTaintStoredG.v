(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FlushBlockModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TrSmallModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Trees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateBlk.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Deflate.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateSafe.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateOverlay.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflateRel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflFastM.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflFast1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeI1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeI2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeS.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflStored2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflStored4.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflStored5.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflStored6.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflStored7.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeI4.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeL0.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateTaintRel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateTaintRelG.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateTaintBitsG.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateTaintLzG.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateTaintBlkG.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateTaintTrees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateTaintStored.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Lemma CFGG_of_INV s : INVG s -> CFGG s.
Proof. intros I. exact (conj (ig_wbits s I) (conj (ig_hbits s I) (ig_strat s I))). Qed.
Lemma CFGG_SF a b : SF b = SF a -> CFGG a -> CFGG b.
Proof.
  intros E (C1 & C2 & C3). pose proof (SF_fields _ _ E) as ((_ & _ & _ & _ & _ & Esy) & _ & _ & _ & _ & (Ewb & Ehb & _)).
  unfold CFGG. rewrite Esy, Ewb, Ehb. exact (conj C1 (conj C2 C3)).
Qed.
Lemma CFGG_clean a b : clean a = clean b -> CFGG a -> CFGG b.
Proof.
  intros E (C1 & C2 & C3). unfold CFGG.
  rewrite <- (clean_eq_fieldT ds_w_bits a b E ltac:(reflexivity)), <- (clean_eq_fieldT ds_hash_bits a b E ltac:(reflexivity)),
    <- (clean_eq_fieldT ds_strategy a b E ltac:(reflexivity)).
  exact (conj C1 (conj C2 C3)).
Qed.

Theorem deflate_stored_relG c0 s1 s2 flush :
  C0OK' c0 -> SI c0 s1 s1 -> SI c0 s2 s2 -> FREL0 s1 s2 -> INVG s1 -> INVG s2 ->
  let r1 := deflate_stored s1 flush in let r2 := deflate_stored s2 flush in
  snd r1 = snd r2 /\ FREL0 (fst r1) (fst r2) /\ INVG (fst r1) /\ INVG (fst r2).
Proof.
  intros HC0 HS1 HS2 (W & C & B & bnd & ms & pm & R & HW & HP & HSY & HL) I1 I2.
  pose proof (deflate_stored_rel_core c0 s1 s2 flush HC0 C bnd ms pm W B R HW HS1 HS2) as XX. cbv zeta in XX.
  destruct XX as (E & (W' & B' & R' & HW' & P') & D1 & D2 & ESF & Hm).
  cbv zeta. split; [exact E|].
  assert (G1 : CFGG (fst (deflate_stored s1 flush))) by (apply (CFGG_SF s1); [exact ESF | apply CFGG_of_INV; exact I1]).
  split.
  - exists W', C, B', bnd, ms, pm. split; [exact R'|]. split; [exact HW'|]. split; [exact P'|]. split.
    + intros i Hi. exfalso. pose proof (proj1 (proj2 (proj2 (dx_st0 _ (proj2 (proj1 D1)) Hm)))) as Hsn. clear - Hi Hsn. lia.
    + apply dmode0_level. exact Hm.
  - split; [apply (INVG_of_DC c0); [exact D1 | exact G1]|].
    apply (INVG_of_DC c0); [exact D2 | apply (CFGG_clean (fst (deflate_stored s1 flush))); [exact (r_clean _ _ _ _ _ _ _ _ R') | exact G1]].
Qed.
