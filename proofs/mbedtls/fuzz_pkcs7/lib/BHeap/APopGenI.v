(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModelX APop APopGen.
Import ListNotations.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Ltac2 gd_tbl_APopGenI () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.BHeap.AModel.AH"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_L"; "RocqVerifyHarness.AgentSubmission.BHeap.APopGen.null_reg"; "ARUN_1.icache"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_chunks"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_tq"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_gq"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_sec"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_dep"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_ia"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_fake"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_pa_committed"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_havol"; "RocqVerifyHarness.AgentSubmission.BHeap.APopGen.acct_set_exh"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_acct"].
   (* [comment removed for export] *)
Section ARUN_1. Context {hAR : arun}.

(* [comment removed for export] *)
#[using="Type"] Lemma cache_empty_noinit : forall h j, awf' h -> h_cinit h = false -> 0 <= j < kNumClasses -> pc_chunks (h_cache h j) = [].
Proof.
  intros h j AWF CI Hj. dpose AWF as (_ & WC & _). pose proof (WC j Hj) as X. cbn zeta in X. rewrite CI in X.
  ddestruct X as ([PM _] & _ & PCNT & _ & _). unfold pc_count in PCNT. rewrite PM in PCNT. cbn in PCNT.
  destruct (pc_chunks (h_cache h j)) as [|q l]; [reflexivity| exfalso; cbn [length] in PCNT; lia].
Qed.

(* [comment removed for export] *)
Definition icache (j : Z) : pcl := PC (max_count j) (class_size j) [].

Section NullInit.
  Variable h : ahst.
  Variables (c UU : Z) (xb : bool).
  Definition null_hI : ahst := ltac2:(CDefT.buildp (gd_tbl_APopGenI ()) "(0.(1.Vh,)(2.Vh,Vc,VUU,)$3.$4.(5.Vh,)(6.Vh,)(7.Vh,)(8.Vh,)(9.Vh,)(:.Vh,)(;.Vh,)(<.Vh,)(=.Vh,)(>.(?.Vh,)Vc,Vxb,))")
(* [comment removed for export] *).

  Hypothesis AWF : awf' h.
  Hypothesis CI : h_cinit h = false.
  Hypothesis GC : 1 <= c <= 30.
  Hypothesis HUU : UU = 0 \/ UU = kUserMapSize.
  Hypothesis MULIM : r_mapped_user (rN h c) + UU <= kUserLimit.
  Hypothesis MUAU : r_mapped_user (rN h c) + UU - r_alloc_user (rN h c) <= 2^19.
  (* [comment removed for export] *)
  Hypothesis XBN : xb = a_exh (h_acct h) c \/ xb = true.

  
  #[using="Type"] Lemma carved_nullI : forall j, carved null_hI j = carved h j.
  Proof. intros j. rewrite <- (carved_null h c UU xb j). reflexivity. Qed.

  #[using="hAR AWF CI"] Lemma owned_nullI : forall j, 0 <= j < kNumClasses -> owned null_hI j = owned h j.
  Proof.
    intros j Hj. rewrite <- (owned_null h c UU xb j). unfold owned, fa_set, cache_set, chunk_set, batch_set.
    cbn [h_reg h_cache h_chunks h_tq h_gq h_L null_hI null_h icache pc_chunks]. rewrite (cache_empty_noinit h j AWF CI Hj). reflexivity.
  Qed.

  #[using="AWF CI GC HUU MULIM MUAU XBN"] Theorem awf'_nullI : awf' null_hI.
  Proof.
    pose proof (awf'_null h c UU xb AWF GC HUU MULIM MUAU XBN) as AWN.
    dpose AWN as (WL & WC & WR & WK & WQ & WS & WD & WB & WBIG & WX & WG).
    split; [exact WL|].
    split. { intros c' Hc'. cbn zeta. cbn [h_cache h_cinit null_hI icache pc_max pc_csize pc_chunks]. unfold pc_count. cbn [pc_chunks length].
      pose proof (max_count_range' c') as MC.
      split; [intros _; split; reflexivity|]. split; [intros _; reflexivity|]. split; [cbn; clear - MC; lia|]. split; [cbn; clear; lia| constructor]. }
    split. { intros c' Hc'. pose proof (WR c' Hc') as X. cbn zeta in X |- *. change (h_reg null_hI c') with (h_reg (null_h h c UU xb) c').
      rewrite carved_nullI, (owned_nullI c' Hc'). rewrite carved_null, owned_null in X. exact X. }
    split. { ddestruct WK as (WKF & WKND & WKSEC). split; [| split; [exact WKND| exact WKSEC]].
      apply Forall_forall. intros k' Hk'. pose proof (proj1 (Forall_forall _ _) WKF k' Hk') as (W1 & W2 & W3 & W4).
      unfold wf_chunk'. rewrite carved_nullI. rewrite carved_null in W4. change (h_L null_hI) with (h_L h). change (h_sec null_hI) with (h_sec h).
      split; [exact W1|]. split; [exact W2|]. split; [exact W3|]. exact W4. }
    split. { ddestruct WQ as ((T1 & T2 & T3) & (G1 & G2 & G3) & ND & UQ).
      assert (FB : forall b, wf_batch (null_h h c UU xb) b -> wf_batch null_hI b).
      { (intros b dd_H; ddestruct dd_H as (B1 & B2 & B3 & B4)). unfold wf_batch. rewrite carved_nullI. rewrite ?carved_null in B4. change (h_L null_hI) with (h_L h). change (h_chunks null_hI) with (h_chunks h).
        split; [exact B1|]. split; [exact B2|]. split; [exact B3| exact B4]. }
      split; [split; [| split; [exact T2| exact T3]]| split; [split; [| split; [exact G2| exact G3]]| split; [exact ND| exact UQ]]];
        apply Forall_forall; intros b Hb; apply FB; [exact (proj1 (Forall_forall _ _) T1 b Hb)| exact (proj1 (Forall_forall _ _) G1 b Hb)]. }
    split; [exact WS|]. split; [exact WD|]. split; [exact WB|]. split; [exact WBIG|].
    split. { ddestruct WX as (X1 & X2 & X3 & X4 & X5 & X6 & X7). split; [| split; [exact X2| split; [intros E; discriminate E| split; [exact X4| split; [exact X5| split; [exact X6| exact X7]]]]]].
      intros c' Hc'. change (h_reg null_hI c') with (h_reg (null_h h c UU xb) c'). rewrite carved_nullI. rewrite <- (carved_null h c UU xb c'). exact (X1 c' Hc'). }
    exact WG.
  Qed.

    End NullInit.

End ARUN_1.
