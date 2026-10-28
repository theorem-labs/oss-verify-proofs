(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import FMapPositive.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import AsanAllocModel.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AllocWf.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma znth_zrepeat : forall {A} (x : A) n i, znth (zrepeat x n) i x = x.
Proof. intros A x n. induction n as [|n IH]; intros [|i]; cbn; auto. Qed.
Lemma length_zrepeat : forall {A} (x : A) n, length (zrepeat x n) = n.
Proof. intros A x n. induction n as [|n IH]; cbn; auto. Qed.

Section Init.
  Variables (rb sb pa : Z) (env : list Z) (ts : bool).
  #[local] Notation st := (init_state rb sb pa env ts).

  Lemma init_state_eq : init_state rb sb pa env ts = init_state_q rb sb pa env ts kQuarantineMaxSize kQuarantineMinSize kMaxCacheSize.
  Proof. reflexivity. Qed.

  Lemma get_region_init : forall c, get_region st c = region0.
  Proof. intros c. unfold get_region. cbn [as_regions init_state init_state_q]. apply znth_zrepeat. Qed.
  Lemma get_pc_init : forall c, get_pc st c = pclass0.
  Proof. intros c. unfold get_pc. cbn [as_cache init_state init_state_q]. apply znth_zrepeat. Qed.
  Lemma chunk_list_init : chunk_list st = [].
  Proof. reflexivity. Qed.
  Lemma carved_init : carved_addr_list st = [].
  Proof.
    unfold carved_addr_list. rewrite chunk_list_init. cbn [as_tq as_gq init_state init_state_q qc_list filter map app]. rewrite app_nil_r.
    generalize (map Z.of_nat (seq 0 32)) as l. intros l. induction l as [|c l IH]; [reflexivity|].
    cbn [flat_map]. rewrite get_region_init, get_pc_init. cbn [rg_free_array region0 pc_chunks pclass0 map app]. exact IH.
  Qed.

  Theorem WF_init : WF st.
  Proof.
    unfold WF. rewrite carved_init, chunk_list_init.
    cbn [as_sec as_n_reserved as_tq as_gq as_qmax as_qmin as_qcache as_regions as_cache as_chunks as_cache_inited init_state init_state_q
         qc_list qc_bytes qcache0 filter map app flat_map zlen length Z.of_nat].
    split.
    { intros c Hc. pose proof (class_size_table_facts c ltac:(unfold kNumClasses in Hc; lia)) as (CS & _).
      split.
      - constructor; rewrite get_region_init; cbn [rg_allocated_user rg_mapped_user rg_num_freed rg_free_array rg_mapped_free_array region0 zlen length Z.of_nat];
          unfold kUserMapSize, kFreeArrayOffset, kFreeArrayMapSize, kFreeArraySize;
          first [lia | reflexivity | (intros Hcs; apply Z.mod_0_l; exact Hcs) | (intros Hcs; cbn [Z.eqb]; lia) | (intros cp [])].
      - constructor; rewrite get_pc_init; cbn [pc_count pc_chunks pclass0 zlen length Z.of_nat as_cache_inited init_state init_state_q]; try reflexivity.
        intros cp []. }
    split; [constructor|].
    split; [intros ch []|].
    split; [intros ch ch' []|].
    split; [reflexivity|].
    split; [constructor|].
    split; [lia|]. split; [lia|].
    split; [split; [intros b []| reflexivity]|].
    split; [split; [intros b []| reflexivity]|].
    split; [unfold kMaxCacheSize; lia|]. split; [unfold kQuarantineMaxSize; lia|].
    split; [constructor|].
    split; [intros ch []|].
    split; [rewrite get_region_init; reflexivity|]. split; [rewrite get_region_init; reflexivity|].
    split; [rewrite get_pc_init; reflexivity|]. split; [rewrite get_pc_init; reflexivity|].
    split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    intros k x Hf. rewrite PositiveMap.gempty in Hf. discriminate Hf.
  Qed.
End Init.

(* [comment removed for export] *)
Corollary WF_init_q : forall rb sb pa env ts, WF (init_state_q rb sb pa env ts kQuarantineMaxSize kQuarantineMinSize kMaxCacheSize).
Proof. intros. rewrite <- init_state_eq. apply WF_init. Qed.
