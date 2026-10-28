(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil BothAllocModel BothAllocCons.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BllocWf BllocKit BllocRep BW_MergeBatches BW_Recycle.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Lemma merge_batches_aux_total : forall fuel cur rest rdone rex xb,
  (length rest < fuel)%nat -> kBatchSize <= qb_size cur -> Forall (fun b => kBatchSize <= qb_size b) rest ->
  exists l' ex xb', merge_batches_aux fuel cur rest rdone rex xb = Some (l', ex, xb').
Proof.
  intros fuel. induction fuel as [|fuel IH]; intros cur rest rdone rex xb FU SC SR; [exfalso; lia|].
  cbn [merge_batches_aux]. destruct rest as [|nx rest'].
  - do 3 eexists. reflexivity.
  - apply Forall_cons_iff in SR. destruct SR as [SN SR']. cbn [length] in FU.
    destruct (qb_count cur + qb_count nx <=? kBatchCount).
    + replace (qb_size cur <? kBatchSize) with false by (symmetry; apply Z.ltb_ge; exact SC).
      apply IH; [lia| cbn [qb_size]; lia| exact SR'].
    + apply IH; [lia| exact SN| exact SR'].
Qed.

Lemma pop_while_total : forall fuel l bytes min_size acc,
  (length l < fuel)%nat -> 0 <= min_size -> bytes = bsum l -> Forall (fun b => kBatchSize <= qb_size b) l ->
  exists l2 b2 r, pop_while fuel l bytes min_size acc = Some (l2, b2, r).
Proof.
  intros fuel. induction fuel as [|fuel IH]; intros l bytes min_size acc FU MN BY SZ; [exfalso; lia|].
  rewrite pop_while_step. destruct (Z.leb_spec bytes min_size) as [LE|GT]; [do 3 eexists; reflexivity|].
  destruct l as [|b r].
  - exfalso. rewrite bsum_nil in BY. lia.
  - apply Forall_cons_iff in SZ. destruct SZ as [SB SR]. cbn [length] in FU. rewrite bsum_cons in BY.
    apply IH; [lia| exact MN| lia| exact SR].
Qed.

Definition qq (st st' : astate) : Prop :=
  as_tq st' = as_tq st /\ as_gq st' = as_gq st /\ as_space_beg st' = as_space_beg st /\ length (as_regions st') = length (as_regions st).
Lemma qq_refl : forall st, qq st st. Proof. intros; repeat split; reflexivity. Qed.
Lemma qq_trans : forall a b c, qq a b -> qq b c -> qq a c.
Proof. intros a b c (A1 & A2 & A3 & A4) (B1 & B2 & B3 & B4). unfold qq. rewrite B1, B2, B3, B4. repeat split; assumption. Qed.
Lemma qq_of_core : forall a b, same_core a b -> qq b a.
Proof. intros a b H. destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & _). unfold qq. rewrite H3. repeat split; assumption || reflexivity. Qed.

Lemma cache_dealloc_qq : forall st c p st' ev, length (as_regions st) = 32%nat -> 0 <= c ->
  cache_dealloc st c p = Some (st', ev) -> qq st st'.
Proof.
  intros st c p st' ev L C H. destruct (cache_dealloc_frame st c p st' ev L C H) as (_ & SB & LR & _ & TQ & GQ & _).
  unfold qq. rewrite L. repeat split; assumption.
Qed.

Lemma cb_recycle_qq : forall st m st' ev, length (as_regions st) = 32%nat -> cb_recycle st m = Some (st', ev) -> qq st st'.
Proof.
  intros st m st' ev L H. unfold cb_recycle in H.
  destruct (find_chunk (as_chunks st) (m + kChunkHeaderSize)) as [ch|]; [| discriminate H].
  destruct (ch_state ch); [discriminate H|]. destruct (in_primary st m).
  - cbv zeta in H. destruct (class_of_addr st m =? 0); [discriminate H|].
    destruct (rg_mapped_user _ <? _); [discriminate H|]. destruct (negb _); [discriminate H|].
    destruct (poison_shadow st _ _ _) as [[st1 ev1]|] eqn:P; [| discriminate H].
    destruct (cache_dealloc _ _ _) as [[st3 ev3]|] eqn:CD; [| discriminate H]. injection H as <- _.
    pose proof (qq_of_core _ _ (poison_shadow_core _ _ _ _ _ _ P)) as Q1.
    assert (Q2 : qq st1 (set_chunks st1 (remove_chunk (as_chunks st1) (ch_user_beg ch)))) by (repeat split; reflexivity).
    assert (L2 : length (as_regions (set_chunks st1 (remove_chunk (as_chunks st1) (ch_user_beg ch)))) = 32%nat).
    { destruct Q1 as (_ & _ & _ & E1). cbn [as_regions set_chunks]. rewrite E1. exact L. }
    assert (C0 : 0 <= class_of_addr st m) by (unfold class_of_addr; apply (proj2 (Z.land_nonneg _ _)); right; lia).
    pose proof (cache_dealloc_qq _ _ _ _ _ L2 C0 CD) as Q3.
    eapply qq_trans; [exact Q1| eapply qq_trans; [exact Q2| exact Q3]].
  - destruct (large_get_block_begin st m) as [p|]; [| discriminate H]. destruct (p =? 0); [discriminate H|].
    destruct (in_primary st p); [discriminate H|]. destruct (negb _); [discriminate H|].
    destruct (large_deallocate _ p) as [[st2 ev2]|] eqn:LD; [| discriminate H]. injection H as <- <-.
    destruct (large_deallocate_core _ _ _ _ LD) as [_ C]. apply qq_of_core in C.
    destruct C as (C1 & C2 & C3 & C4). cbn [as_tq as_gq as_space_beg as_regions set_sec set_chunks] in C1, C2, C3, C4.
    unfold qq. rewrite <- C1, <- C2, <- C3, <- C4. repeat split; reflexivity.
Qed.

Lemma cb_recycle_list_qq : forall ms st racc st' racc', length (as_regions st) = 32%nat ->
  cb_recycle_list st ms racc = Some (st', racc') -> qq st st'.
Proof.
  induction ms as [|m ms IH]; intros st racc st' racc' L H; cbn [cb_recycle_list] in H.
  - injection H as <- _. apply qq_refl.
  - destruct (cb_recycle st m) as [[st1 ev1]|] eqn:R; [| discriminate H].
    pose proof (cb_recycle_qq _ _ _ _ L R) as Q1. pose proof Q1 as (_ & _ & _ & L1). rewrite L in L1.
    eapply qq_trans; [exact Q1| exact (IH st1 _ _ _ L1 H)].
Qed.

Lemma do_recycle_qq : forall bs st racc st' racc', length (as_regions st) = 32%nat ->
  do_recycle st bs racc = Some (st', racc') -> qq st st'.
Proof.
  induction bs as [|b r IH]; intros st racc st' racc' L H; cbn [do_recycle] in H.
  - injection H as <- _. apply qq_refl.
  - destruct (cb_recycle_list st (qb_chunks b) racc) as [[st1 racc1]|] eqn:CL; [| discriminate H].
    pose proof (cb_recycle_list_qq _ _ _ _ _ L CL) as Q1. pose proof Q1 as (_ & _ & _ & L1). rewrite L in L1.
    destruct (negb (in_primary st1 (qb_addr b))); [discriminate H|].
    destruct (cache_dealloc st1 _ _) as [[st2 ev2]|] eqn:CD; [| discriminate H].
    assert (C0 : 0 <= class_of_addr st1 (qb_addr b)) by (unfold class_of_addr; apply (proj2 (Z.land_nonneg _ _)); right; lia).
    pose proof (cache_dealloc_qq _ _ _ _ _ L1 C0 CD) as Q2. pose proof Q2 as (_ & _ & _ & L2). rewrite L1 in L2.
    eapply qq_trans; [exact Q1| eapply qq_trans; [exact Q2| exact (IH st2 _ _ _ L2 H)]].
Qed.

Section HCW.
  Context {HCEIL : HeapCeil}.

  Theorem rsplit_total : forall l qbytes qmin,
    Forall bok l -> qbytes = bsum l -> 0 <= qmin ->
    exists l2 b2 ex rp, rsplit (mkQC l qbytes) qmin = Some (mkQC l2 b2, ex, rp).
  Proof.
    intros l qbytes qmin OKL QB QM.
    assert (SZ : Forall (fun b => kBatchSize <= qb_size b) l).
    { apply Forall_forall. intros b Hb. pose proof (proj1 (Forall_forall _ _) OKL b Hb) as (_ & _ & _ & _ & _ & K & _). exact K. }
    pose proof (bsum_len l OKL) as BL.
    unfold rsplit. cbn [qc_list qc_bytes].
    replace (qbytes <? zlen l * kBatchSize) with false by (symmetry; apply Z.ltb_ge; lia).
    destruct ((zlen l * kBatchSize <? qbytes) && (qbytes * 100 <? zlen l * kBatchSize * 200)).
    -
      destruct l as [|b r].
      + unfold merge_batches. cbn [qc_list qc_bytes length pop_while].
        replace (qbytes <=? qmin) with true by (symmetry; apply Z.leb_le; rewrite bsum_nil in QB; lia).
        do 4 eexists. reflexivity.
      + apply Forall_cons_iff in SZ. destruct SZ as [SB SR].
        destruct (merge_batches_aux_total (S (length r)) b r [] [] 0 ltac:(lia) SB SR) as (l' & ex & xb' & E).
        unfold merge_batches. cbn [qc_list qc_bytes]. rewrite E.
        pose proof (merge_batches_bsum (b :: r) qbytes l' (qbytes - xb') ex xb') as MB.
        unfold merge_batches in MB. cbn [qc_list qc_bytes] in MB. rewrite E in MB. specialize (MB eq_refl). destruct MB as (M1 & M2 & M3 & M4).
        assert (SZ' : Forall (fun b0 => kBatchSize <= qb_size b0) l').
        {
          clear - E SB SR.
          assert (G : forall fuel cur rest rdone rex xb l1 ex1 xb1,
                     kBatchSize <= qb_size cur -> Forall (fun b0 => kBatchSize <= qb_size b0) rest -> Forall (fun b0 => kBatchSize <= qb_size b0) rdone ->
                     merge_batches_aux fuel cur rest rdone rex xb = Some (l1, ex1, xb1) -> Forall (fun b0 => kBatchSize <= qb_size b0) l1).
          { intros fuel. induction fuel as [|fuel IH]; intros cur rest rdone rex xb l1 ex1 xb1 SC SRR SD H; [discriminate H|].
            cbn [merge_batches_aux] in H. destruct rest as [|nx rest'].
            - injection H as <- _ _. change (rev rdone ++ [cur]) with (rev (cur :: rdone)). apply Forall_rev. constructor; [exact SC| exact SD].
            - apply Forall_cons_iff in SRR. destruct SRR as [SN SRR'].
              destruct (qb_count cur + qb_count nx <=? kBatchCount).
              + destruct (qb_size cur <? kBatchSize); [discriminate H|].
                eapply (IH (mkQB (qb_addr cur) (qb_size cur + (qb_size nx - kBatchSize)) (qb_count cur + qb_count nx) (qb_chunks cur ++ qb_chunks nx)) rest' rdone _ _ l1 ex1 xb1);
                  [cbn [qb_size]; lia| exact SRR'| exact SD| exact H].
              + eapply (IH nx rest' (cur :: rdone) _ _ l1 ex1 xb1); [exact SN| exact SRR'| constructor; [exact SC| exact SD]| exact H]. }
          eapply (G (S (length r)) b r [] [] 0 l' ex xb'); [exact SB| exact SR| constructor| exact E]. }
        cbn [qc_list qc_bytes].
        destruct (pop_while_total (S (length l')) l' (qbytes - xb') qmin [] ltac:(lia) QM ltac:(lia) SZ') as (l2 & b2 & rp & P).
        rewrite P. do 4 eexists. reflexivity.
    -
      cbn [qc_list qc_bytes].
      destruct (pop_while_total (S (length l)) l qbytes qmin [] ltac:(lia) QM QB SZ) as (l2 & b2 & rp & P).
      rewrite P. do 4 eexists. reflexivity.
  Qed.
End HCW.
