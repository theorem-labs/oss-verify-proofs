(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool FMapPositive.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil BothAllocModel BothAllocCons.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BllocWf BllocKit BllocRep BW_MergeBatches BW_Recycle BG_RecycleModel2.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Definition csub (st st' : astate) : Prop := forall ch, In ch (chunk_list st') -> In ch (chunk_list st).
Lemma csub_refl : forall st, csub st st. Proof. intros st ch H. exact H. Qed.
Lemma csub_trans : forall a b c, csub a b -> csub b c -> csub a c.
Proof. intros a b c A B ch H. exact (A ch (B ch H)). Qed.
Lemma chunk_list_ext : forall a b, as_chunks a = as_chunks b -> chunk_list a = chunk_list b.
Proof. intros a b E. unfold chunk_list. rewrite E. reflexivity. Qed.
Lemma csub_ext : forall st st', as_chunks st' = as_chunks st -> csub st st'.
Proof. intros st st' E ch H. rewrite (chunk_list_ext st' st E) in H. exact H. Qed.
Lemma csub_remove : forall st u, csub st (set_chunks st (remove_chunk (as_chunks st) u)).
Proof. intros st u ch H. exact (proj1 (proj1 (chunk_list_remove_iff st u ch) H)). Qed.

Lemma cb_recycle_csub : forall st m st' ev, length (as_regions st) = 32%nat -> cb_recycle st m = Some (st', ev) -> csub st st'.
Proof.
  intros st m st' ev L H. unfold cb_recycle in H.
  destruct (find_chunk (as_chunks st) (m + kChunkHeaderSize)) as [ch|]; [| discriminate H].
  destruct (ch_state ch); [discriminate H|]. destruct (in_primary st m).
  - cbv zeta in H. destruct (class_of_addr st m =? 0); [discriminate H|].
    destruct (rg_mapped_user _ <? _); [discriminate H|]. destruct (negb _); [discriminate H|].
    destruct (poison_shadow st _ _ _) as [[st1 ev1]|] eqn:P; [| discriminate H].
    destruct (cache_dealloc _ _ _) as [[st3 ev3]|] eqn:CD; [| discriminate H]. injection H as <- _.
    pose proof (poison_shadow_core _ _ _ _ _ _ P) as C1.
    assert (CH1 : as_chunks st1 = as_chunks st) by (destruct C1 as (_ & _ & _ & _ & _ & _ & _ & E & _); exact E).
    assert (L2 : length (as_regions (set_chunks st1 (remove_chunk (as_chunks st1) (ch_user_beg ch)))) = 32%nat).
    { pose proof (qq_of_core _ _ C1) as (_ & _ & _ & E1). cbn [as_regions set_chunks]. rewrite E1. exact L. }
    assert (C0 : 0 <= class_of_addr st m) by (unfold class_of_addr; apply (proj2 (Z.land_nonneg _ _)); right; lia).
    destruct (cache_dealloc_frame _ _ _ _ _ L2 C0 CD) as (CH3 & _).
    eapply csub_trans; [apply (csub_ext st st1 CH1)|]. eapply csub_trans; [apply (csub_remove st1 (ch_user_beg ch))|]. exact (csub_ext _ _ CH3).
  - destruct (large_get_block_begin st m) as [p|]; [| discriminate H]. destruct (p =? 0); [discriminate H|].
    destruct (in_primary st p); [discriminate H|]. destruct (negb _); [discriminate H|].
    destruct (large_deallocate_core _ _ _ _ H) as [CV _].
    assert (CH3 : as_chunks st' = as_chunks (set_chunks st (remove_chunk (as_chunks st) (ch_user_beg ch)))).
    { unfold cview in CV. injection CV as _ _ _ E _ _. exact E. }
    eapply csub_trans; [apply (csub_remove st (ch_user_beg ch))|]. exact (csub_ext _ _ CH3).
Qed.

Lemma cb_recycle_list_csub : forall ms st racc st' racc', length (as_regions st) = 32%nat ->
  cb_recycle_list st ms racc = Some (st', racc') -> csub st st'.
Proof.
  induction ms as [|m ms IH]; intros st racc st' racc' L H; cbn [cb_recycle_list] in H.
  - injection H as <- _. apply csub_refl.
  - destruct (cb_recycle st m) as [[st1 ev1]|] eqn:R; [| discriminate H].
    pose proof (cb_recycle_qq _ _ _ _ L R) as (_ & _ & _ & L1). rewrite L in L1.
    eapply csub_trans; [exact (cb_recycle_csub _ _ _ _ L R)| exact (IH st1 _ _ _ L1 H)].
Qed.

Lemma do_recycle_csub : forall bs st racc st' racc', length (as_regions st) = 32%nat ->
  do_recycle st bs racc = Some (st', racc') -> csub st st'.
Proof.
  induction bs as [|b r IH]; intros st racc st' racc' L H; cbn [do_recycle] in H.
  - injection H as <- _. apply csub_refl.
  - destruct (cb_recycle_list st (qb_chunks b) racc) as [[st1 racc1]|] eqn:CL; [| discriminate H].
    pose proof (cb_recycle_list_qq _ _ _ _ _ L CL) as (_ & _ & _ & L1). rewrite L in L1.
    destruct (negb (in_primary st1 (qb_addr b))); [discriminate H|].
    destruct (cache_dealloc st1 _ _) as [[st2 ev2]|] eqn:CD; [| discriminate H].
    assert (C0 : 0 <= class_of_addr st1 (qb_addr b)) by (unfold class_of_addr; apply (proj2 (Z.land_nonneg _ _)); right; lia).
    pose proof (cache_dealloc_qq _ _ _ _ _ L1 C0 CD) as (_ & _ & _ & L2). rewrite L1 in L2.
    destruct (cache_dealloc_frame _ _ _ _ _ L1 C0 CD) as (CH2 & _).
    eapply csub_trans; [exact (cb_recycle_list_csub _ _ _ _ _ L CL)|]. eapply csub_trans; [exact (csub_ext _ _ CH2)| exact (IH st2 _ _ _ L2 H)].
Qed.

Lemma rsplit_le : forall g qmin l2 b2 ex rp, rsplit g qmin = Some (mkQC l2 b2, ex, rp) -> b2 <= qmin.
Proof.
  intros g qmin l2 b2 ex rp R. unfold rsplit in R.
  destruct (qc_bytes g <? zlen (qc_list g) * kBatchSize); [discriminate R|].
  destruct ((zlen (qc_list g) * kBatchSize <? qc_bytes g) && (qc_bytes g * 100 <? zlen (qc_list g) * kBatchSize * 200)).
  - destruct (merge_batches g) as [[[g' ex'] xb]|]; [| discriminate R].
    destruct (pop_while (S (length (qc_list g'))) (qc_list g') (qc_bytes g') qmin []) as [[[l2' b2'] rp']|] eqn:PW; [| discriminate R].
    injection R as _ <- _ _. pose proof (pop_while_shape _ _ _ _ _ _ _ _ PW) as (popped & _ & _ & _ & LE). exact LE.
  - destruct (pop_while (S (length (qc_list g))) (qc_list g) (qc_bytes g) qmin []) as [[[l2' b2'] rp']|] eqn:PW; [| discriminate R].
    injection R as _ <- _ _. pose proof (pop_while_shape _ _ _ _ _ _ _ _ PW) as (popped & _ & _ & _ & LE). exact LE.
Qed.

Theorem quarantine_recycle_final : forall st qmin stR evR, length (as_regions st) = 32%nat ->
  quarantine_recycle st qmin = Some (stR, evR) ->
  csub st stR /\ as_tq stR = as_tq st /\ qc_bytes (as_gq stR) <= qmin.
Proof.
  intros st qmin stR evR L H. rewrite quarantine_recycle_rsplit in H.
  destruct (rsplit (as_gq st) qmin) as [[[g2 ex] rp]|] eqn:RS; [| discriminate H].
  destruct (do_recycle (set_gq st g2) (ex ++ rev rp) []) as [[st2 racc]|] eqn:DR; [| discriminate H]. injection H as <- _.
  assert (L1 : length (as_regions (set_gq st g2)) = 32%nat) by exact L.
  pose proof (do_recycle_qq _ _ _ _ _ L1 DR) as (Q1 & Q2 & _).
  pose proof (do_recycle_csub _ _ _ _ _ L1 DR) as CS.
  split; [intros ch Hch; exact (CS ch Hch)|]. split; [rewrite Q1; reflexivity|].
  rewrite Q2. cbn [as_gq set_gq]. destruct g2 as [l2 b2]. cbn [qc_bytes]. exact (rsplit_le _ _ _ _ _ _ RS).
Qed.
