(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StreamSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreKit
     PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnLayoutS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmStatics PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnSpecsS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PMCK.
Import PMS.

Lemma writable_img M a n : wseg_ok RSEGS (Z_to_bv 64 a) (Z.to_nat n) = true -> 0 <= a -> 0 < n -> a + n <= 2 ^ 64 -> L5.writable RSEGS M a n.
Proof.
  intros W Ha Hn Han d k Hd Hk. destruct k as [|k]. reflexivity.
  eapply (store_ok_sub RSEGS M (Z_to_bv 64 a) _ (Z.to_nat n) (S k)).
  - rewrite L5.unsigned_lit by lia. rewrite Z2Nat.id by lia. lia.
  - apply store_ok_wseg. exact W.
  - rewrite !L5.unsigned_lit by lia. lia.
  - rewrite !L5.unsigned_lit by lia. rewrite Z2Nat.id by lia. lia.
Qed.

Lemma cs_in_KS (KS : list nat) : (forall k, In k PMK.cs_all -> existsb (Nat.eqb k) KS = true) -> forall k, In k PMK.cs_all -> In k KS.
Proof. intros H k Hk. apply L5K.In_of_mem. apply H. exact Hk. Qed.
Ltac cs_all_tac := apply cs_in_KS; intros k Hk; unfold PMK.cs_all in Hk; cbn in Hk; repeat (destruct Hk as [<-|Hk]; [vm_compute; reflexivity|]); destruct Hk.

(* [comment removed for export] *)
Lemma u32_of_u64 M a v : L5.u64_at RSEGS M a v -> L5.u32_at RSEGS M a v.
Proof.
  unfold L5.u64_at, L5.u32_at. intros H. rewrite (SeqExec.rdn_firstn RSEGS M 8%nat (Z_to_bv 64 a) _ 4%nat H) by lia. reflexivity.
Qed.

Section K.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Lemma lb_hi LB cr M VM : hi_heap HI LB cr M VM -> forall b, In b LB -> fst b + snd b <= hl_ceil L.
Proof. intros HH b Hb. pose proof (proj1 (hio_wf L SCFG HI HIok LB cr M _ HH) b Hb) as ((Q0 & Q1 & Q2 & Q3 & Q4) & _). exact Q4. Qed.
End K.
End PMCK.
