(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FMapPositive.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import AsanAllocModel. From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both Require Import AsanAllocCons.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AllocWf AllocKit AG_MallocModel AG_WFHit CidBits AllocBudget.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sbpa (st st' : astate) : Prop := as_space_beg st' = as_space_beg st /\ as_ptr_array st' = as_ptr_array st.
Lemma sbpa_refl : forall st, sbpa st st. Proof. intros st. split; reflexivity. Qed.
Lemma sbpa_trans : forall a b c, sbpa a b -> sbpa b c -> sbpa a c.
Proof. intros a b c [A1 A2] [B1 B2]. split; congruence. Qed.
Lemma sbpa_of_core : forall a b, same_core a b -> sbpa b a.
Proof. intros a b C. destruct C as (S & P & _). split; [exact S| exact P]. Qed.
Lemma eci_sbpa : forall st, sbpa st (ensure_cache_inited st).
Proof. intros st. unfold sbpa, ensure_cache_inited. destruct (as_cache_inited st); split; reflexivity. Qed.

Lemma poison_shadow_sbpa : forall st a n v st' ev, poison_shadow st a n v = Some (st', ev) -> sbpa st st'.
Proof. intros st a n v st' ev H. exact (sbpa_of_core _ _ (poison_shadow_core _ _ _ _ _ _ H)). Qed.

Lemma populate_sbpa : forall st c req st' ev, length (as_regions st) = 32%nat -> 0 <= c < kNumClasses ->
  populate_free_array st c req = Some (st', ev) -> sbpa st st'.
Proof.
  intros st c req st' ev L Hc H. destruct (populate_free_array_core st c req st' ev L Hc H) as (mu' & mfa' & C & _). cbv zeta in C.
  exact (sbpa_of_core _ _ C).
Qed.

Lemma get_from_allocator_sbpa : forall st c n st' taken ev, length (as_regions st) = 32%nat -> 0 <= c < kNumClasses ->
  get_from_allocator st c n = Some (st', taken, ev) -> sbpa st st'.
Proof.
  intros st c n st' taken ev L Hc H. destruct (get_from_allocator_core st c n st' taken ev H) as (st1 & A & _ & ->).
  destruct A as [[-> _]|(_ & (ev1 & P & _))]; [split; reflexivity|].
  exact (populate_sbpa st c _ st1 ev1 L Hc P).
Qed.

Lemma cache_alloc_sbpa : forall st c st' a ev, length (as_regions st) = 32%nat -> 0 <= c ->
  cache_alloc st c = Some (st', a, ev) -> sbpa st st'.
Proof.
  intros st c st' a ev L C00 H. destruct (cache_alloc_core st c st' a ev H) as ((C0 & C1) & st1 & pc1 & cp & rest & A & _ & -> & _).
  destruct A as [(PZ & taken & ev' & G & _)|(PZ & -> & _)].
  - assert (Hc : 0 <= c < kNumClasses) by lia.
    pose proof (get_from_allocator_sbpa (ensure_cache_inited st) c _ st1 taken ev' ltac:(rewrite eci_regions; exact L) Hc G) as S1.
    exact (sbpa_trans _ _ _ (eci_sbpa st) S1).
  - split; reflexivity.
Qed.

Lemma cache_dealloc_sbpa : forall st c p st' ev, cache_dealloc st c p = Some (st', ev) -> sbpa st st'.
Proof.
  intros st c p st' ev H. unfold cache_dealloc in H.
  destruct ((c =? 0) || (kNumClasses <=? c)); [discriminate H|].
  set (st0 := ensure_cache_inited st) in H.
  assert (S0 : sbpa st st0) by (subst st0; apply eci_sbpa).
  clearbody st0.
  destruct (pc_count (get_pc st0 c) =? max_count c).
  - destruct (_ <? _); [discriminate H|].
    destruct (return_to_allocator (set_pc st0 c _) c _ _) as [[st1 ev1]|] eqn:RT; [| discriminate H]. injection H as <- _.
    unfold return_to_allocator in RT. destruct (ensure_free_array_space _ c _) as [[st2 ev2]|] eqn:EN; [| discriminate RT]. injection RT as <- _.
    destruct (ensure_free_array_space_core _ c _ st2 ev2 EN) as (mfa' & C2 & _). cbv zeta in C2.
    pose proof (sbpa_of_core _ _ C2) as S2. exact (sbpa_trans _ _ _ S0 S2).
  - injection H as <- _. exact S0.
Qed.

Lemma large_deallocate_sbpa : forall st p st' ev, large_deallocate st p = Some (st', ev) -> sbpa st st'.
Proof. intros st p st' ev H. destruct (large_deallocate_core st p st' ev H) as [_ C]. exact (sbpa_of_core _ _ C). Qed.

Lemma cb_recycle_sbpa : forall st m st' ev, cb_recycle st m = Some (st', ev) -> sbpa st st'.
Proof.
  intros st m st' ev H. unfold cb_recycle in H.
  destruct (find_chunk (as_chunks st) (m + kChunkHeaderSize)) as [ch|]; [| discriminate H].
  destruct (ch_state ch); [discriminate H|].
  destruct (in_primary st m).
  - destruct (class_of_addr st m =? 0); [discriminate H|]. destruct (_ <? _); [discriminate H|]. destruct (negb _); [discriminate H|].
    destruct (poison_shadow st _ _ _) as [[st1 ev1]|] eqn:PS; [| discriminate H].
    destruct (cache_dealloc _ _ _) as [[st3 ev3]|] eqn:CD; [| discriminate H]. injection H as <- _.
    exact (sbpa_trans _ _ _ (poison_shadow_sbpa _ _ _ _ _ _ PS) (cache_dealloc_sbpa _ _ _ _ _ CD)).
  - destruct (large_get_block_begin st m) as [p|]; [| discriminate H]. destruct (p =? 0); [discriminate H|].
    destruct (in_primary st p); [discriminate H|]. destruct (negb _); [discriminate H|].
    exact (large_deallocate_sbpa _ _ _ _ H).
Qed.

Lemma cb_recycle_list_sbpa : forall ms st racc st' racc', cb_recycle_list st ms racc = Some (st', racc') -> sbpa st st'.
Proof.
  induction ms as [|m ms IH]; intros st racc st' racc' H; cbn in H.
  - injection H as <- _. apply sbpa_refl.
  - destruct (cb_recycle st m) as [[st1 ev1]|] eqn:CB; [| discriminate H].
    exact (sbpa_trans _ _ _ (cb_recycle_sbpa _ _ _ _ CB) (IH _ _ _ _ H)).
Qed.

Lemma do_recycle_sbpa : forall bs st racc st' racc', do_recycle st bs racc = Some (st', racc') -> sbpa st st'.
Proof.
  induction bs as [|b bs IH]; intros st racc st' racc' H; cbn in H.
  - injection H as <- _. apply sbpa_refl.
  - destruct (cb_recycle_list st (qb_chunks b) racc) as [[st1 racc1]|] eqn:CL; [| discriminate H].
    destruct (negb _); [discriminate H|].
    destruct (cache_dealloc st1 _ _) as [[st2 ev2]|] eqn:CD; [| discriminate H].
    eapply sbpa_trans; [exact (cb_recycle_list_sbpa _ _ _ _ _ CL)|].
    eapply sbpa_trans; [exact (cache_dealloc_sbpa _ _ _ _ _ CD)| exact (IH _ _ _ _ H)].
Qed.

Lemma quarantine_recycle_sbpa : forall st ms st' ev, quarantine_recycle st ms = Some (st', ev) -> sbpa st st'.
Proof.
  intros st ms st' ev H. unfold quarantine_recycle in H.
  destruct (_ <? _); [discriminate H|].
  match type of H with (match ?mg with _ => _ end) = _ => destruct mg as [[g1 extracted]|]; [| discriminate H] end.
  destruct (pop_while _ _ _ _ _) as [[[l2 bytes2] rpopped]|]; [| discriminate H].
  destruct (do_recycle (set_gq st _) _ _) as [[st2 racc]|] eqn:DR; [| discriminate H]. injection H as <- _.
  exact (do_recycle_sbpa _ _ _ _ _ DR).
Qed.

Lemma quarantine_drain_sbpa : forall st st' ev, quarantine_drain st = Some (st', ev) -> sbpa st st'.
Proof.
  intros st st' ev H. unfold quarantine_drain in H.
  destruct (as_qmax st <? _).
  - exact (quarantine_recycle_sbpa _ _ _ _ H).
  - injection H as <- _. split; reflexivity.
Qed.

Lemma quarantine_enqueue_sbpa : forall st m size st' ev, length (as_regions st) = 32%nat ->
  quarantine_enqueue st m size = Some (st', ev) -> sbpa st st'.
Proof.
  intros st m size st' ev L H. unfold quarantine_enqueue in H.
  destruct (qc_list (as_tq st)) as [|b0 l0] eqn:TQ.
  - destruct (cache_alloc st kBatchClass) as [[[st1 b] ev1]|] eqn:CA; [| discriminate H].
    destruct (b =? 0); [discriminate H|]. injection H as <- _.
    exact (cache_alloc_sbpa st kBatchClass _ _ _ L ltac:(unfold kBatchClass; lia) CA).
  - destruct (kBatchCount <=? _).
    + destruct (cache_alloc st kBatchClass) as [[[st1 b] ev1]|] eqn:CA; [| discriminate H].
      destruct (b =? 0); [discriminate H|]. injection H as <- _.
      exact (cache_alloc_sbpa st kBatchClass _ _ _ L ltac:(unfold kBatchClass; lia) CA).
    + injection H as <- _. split; reflexivity.
Qed.

Lemma quarantine_put_sbpa : forall st ch st' ev, length (as_regions st) = 32%nat ->
  quarantine_put st ch = Some (st', ev) -> sbpa st st'.
Proof.
  intros st ch st' ev L H. unfold quarantine_put in H.
  destruct (_ || _); [discriminate H|].
  destruct (poison_shadow st _ _ _) as [[st1 ev1]|] eqn:PS; [| discriminate H].
  pose proof (poison_shadow_core _ _ _ _ _ _ PS) as C1.
  assert (L1 : length (as_regions st1) = 32%nat) by (rewrite (same_core_len_regions _ _ C1); exact L).
  destruct (quarantine_enqueue st1 _ _) as [[st2 ev2]|] eqn:EQ; [| discriminate H].
  pose proof (sbpa_trans _ _ _ (poison_shadow_sbpa _ _ _ _ _ _ PS) (quarantine_enqueue_sbpa _ _ _ _ _ L1 EQ)) as S2.
  destruct (_ <? _).
  - destruct (quarantine_drain st2) as [[st3 ev3]|] eqn:DR; [| discriminate H]. injection H as <- _.
    exact (sbpa_trans _ _ _ S2 (quarantine_drain_sbpa _ _ _ DR)).
  - injection H as <- _. exact S2.
Qed.

Theorem am_free_full_sbpa : forall st p st' ev, WF st -> am_free_full st p = Some (st', ev) ->
  as_space_beg st' = as_space_beg st /\ as_ptr_array st' = as_ptr_array st.
Proof.
  intros st p st' ev W H. pose proof (WF_lengths st W) as [LENR LENC].
  assert (K : forall st0 (ev0 : list effect), sbpa st st0 -> as_regions st0 = as_regions st ->
    (if p =? 0 then Some (st0, ev0) else
     match find_chunk (as_chunks st0) p with
     | None => None
     | Some ch => match ch_state ch with
                  | CQuarantine => None
                  | CAllocated =>
                      match quarantine_put (upd_chunk st0 (mkChunk (ch_alloc_beg ch) (ch_user_beg ch) (ch_used ch) (ch_rz ch) (ch_class ch) CQuarantine))
                              (mkChunk (ch_alloc_beg ch) (ch_user_beg ch) (ch_used ch) (ch_rz ch) (ch_class ch) CQuarantine) with
                      | None => None
                      | Some (st2, ev2) => Some (st2, ev0 ++ [EStore64 p 0xFFFFFFFF00000000; EStore64 p 0] ++ ev2)
                      end
                  end
     end) = Some (st', ev) -> sbpa st st').
  { intros st0 ev0 S0 R0 H0. destruct (Z.eqb_spec p 0) as [P0|P0].
    - injection H0 as <- _. exact S0.
    - destruct (find_chunk (as_chunks st0) p) as [ch|]; [| discriminate H0]. destruct (ch_state ch); [| discriminate H0].
      match type of H0 with (match quarantine_put ?a ?b with _ => _ end) = _ => destruct (quarantine_put a b) as [[st2 ev2]|] eqn:QP; [| discriminate H0] end.
      injection H0 as <- _.
      match type of QP with quarantine_put ?s1 ?c1 = _ =>
        pose proof (quarantine_put_sbpa s1 c1 _ _ ltac:(cbn; rewrite R0; exact LENR) QP) as S2 end.
      exact (sbpa_trans _ _ _ S0 S2). }
  unfold am_free_full in H.
  destruct (as_internal_init st); [exact (K st [] (sbpa_refl st) eq_refl H)| exact (K (set_internal_init st) [EInternalAllocInit] ltac:(split; reflexivity) eq_refl H)].
Qed.
