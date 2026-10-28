(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Image.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase AMalloc_iface AFake_iface ALayout AHeapP ARepExt AInstanceF AZ_kit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT}.
Lemma fake_heap_AI_of : forall FREE, fake_heap_law (AI_of FREE).
Proof.
  intros FREE L RNG st LB m AH. rewrite AI_of_E in AH. split.
  - pose proof AH as (ALO & _). pose proof (ao_fake L ALO) as OF. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OF.
    unfold ablk, KLS, AIMG_HI, FAKESZ. lia.
  - intros p A n Hin. unfold FAKESZ. exact (AHEAP_P_hb_fake _ _ _ _ _ _ _ _ _ AH Hin).
Qed.
End CANSEC1.
