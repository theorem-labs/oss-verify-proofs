(* Theorem Labs, 2026-11: the allocator meter's room at the 16 GiB limit on the driver's own states (OSSV-265, the fuzz-input step). No released file is copied. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG03 YG0f YG09 YG0k.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YG0n_w YG08_w.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(** * [mroom] at [YG0n_w.ASAN_VM_LMIN] = 2^34 on small allocator states

    In [lib/BudgetWit/AW], [YG0n_w.ASAN_VM_LMIN] is the statement's limit
    (16 GiB), so [mroom s] says that the meter [ameter s] leaves [VM_HEAD]
    under 16 GiB.  The released [YG08.mroom_of_regime] proves [mroom] for every
    state of the allocator's regime at 2^39; at 2^34 that is false in general
    ([ameter] counts [EV_A] = 2^20 per event and [EV_MAX] = 11776 events are
    allowed).  [mroom_small] proves it for the states the driver of
    fuzz_identity reaches: at most 64 events, live blocks of at most 2^28
    bytes, a tight quarantine, and no free array mapped outside the batch
    class ([fa_clean]).  The free arrays are the one part of [prim_committed]
    that no event count bounds ([wr_fa_bound] allows [kFreeArrayMax] = 2^29 per
    class), so [fa_clean] is carried as an invariant: it holds at
    [init_state] and survives a secondary malloc ([malloc_sec_sameq]), a free
    of NULL and a free that does not recycle ([free_norecycle_effect]). *)

Definition fa_clean (S : astate) : Prop :=
  forall c, 1 <= c <= 31 -> c <> kBatchClass -> rg_mapped_fa (reg S c) = 0.

Lemma fa_clean_init : fa_clean init_state.
Proof.
  intros c Hc _. unfold reg, init_state, znth. cbn [st_regions]. rewrite nth_repeat. reflexivity.
Qed.

Lemma fa_clean_malloc_sec : forall n trc S evs r S',
  from_primary n = false -> apath (malloc n trc S) evs (r, S') -> fa_clean S -> fa_clean S'.
Proof.
  intros n trc S evs r S' Hp Hy HF.
  pose proof (apost_apath _ _ _ _ (malloc_sec_sameq n trc S Hp) Hy) as (A & _ & _ & _). cbn [snd] in A.
  intros c Hc Hb. unfold reg. rewrite A. exact (HF c Hc Hb).
Qed.

Lemma fa_clean_free_null : forall trc S evs S',
  apath (free PNull trc S) evs (tt, S') -> fa_clean S -> fa_clean S'.
Proof.
  intros trc S evs S' Hy HF.
  assert (X : apost (free PNull trc S) (fun r => SAMEQ S (snd r))).
  { unfold free. apply apost_bind. apply apost_tick. cbn [fst snd]. apply apost_bind. apply apost_get. cbn [fst snd].
    apply apost_bind.
    lazymatch goal with |- apost (?m ?sx) _ => assert (X : apost (m sx) (fun r => SAMEQ S (snd r))) end.
    { apply apost_if; intros _; [apply apost_ret | apply apost_modify]; cbn [snd]; sameq. }
    eapply apost_mono; [|exact X]. intros [[] s1] H1. apply apost_ret. exact H1. }
  pose proof (apost_apath _ _ _ _ X Hy) as (A & _ & _ & _). cbn [snd] in A.
  intros c Hc Hb. unfold reg. rewrite A. exact (HF c Hc Hb).
Qed.

Lemma fa_clean_free_norecycle : forall U p n trc S evs S',
  Wf U S -> In (p, n) (blocks S) -> quar_bytes S + req_size n + kBatchBytes <= kQuarantineMax ->
  apath (free p trc S) evs (tt, S') -> fa_clean S -> fa_clean S'.
Proof.
  intros U p n trc S evs S' W Hin Hq Hy HF.
  destruct (find_user_block U 0 0 0 S p n W Hin) as (k & Hf & Hk & _ & _ & Hr).
  assert (Hn : ck_n k = req_size n) by (unfold ck_n; rewrite Hr; reflexivity).
  assert (Hn0 : 0 <= ck_n k) by (rewrite Hn; unfold req_size; destruct (n =? 0) eqn:E; [lia|]; apply Z.eqb_neq in E;
    pose proof (proj1 (proj1 (Forall_forall _ _) (wf_chunks _ _ _ _ _ W) k Hk)); lia).
  rewrite <- Hn in Hq.
  pose proof (apost_apath _ _ _ _ (free_norecycle_effect p trc S k (wf_len_cache _ _ _ _ _ W) Hf Hn0 Hq) Hy) as [R _].
  cbn [snd] in R.
  intros c Hc Hb. destruct (R c Hc Hb) as [X1 _]. rewrite X1. exact (HF c Hc Hb).
Qed.

(** The primary commit of a state, with every free array but the batch
    class's unmapped. *)
Lemma fold_fa_le : forall (l : list region) (b : nat -> Z),
  (forall j, (j < length l)%nat -> 0 <= rg_mapped_fa (nth j l region0) <= b j) ->
  fold_right (fun r acc => rg_mapped_user r + rg_mapped_fa r + acc) 0 l
  <= fold_right (fun r acc => rg_mapped_user r + acc) 0 l + fold_right Z.add 0 (map b (seq 0 (length l))).
Proof.
  induction l as [|r t IH]; intros b Hb; cbn [fold_right length].
  - cbn. lia.
  - cbn [seq map fold_right]. rewrite <- seq_shift, map_map.
    pose proof (IH (fun j => b (S j)) (fun j Hj => Hb (S j) ltac:(cbn [length]; lia))) as IH'.
    pose proof (Hb 0%nat ltac:(cbn [length]; lia)) as H0. cbn [nth] in H0. lia.
Qed.

Lemma prim_committed_clean : forall U s, Wf U s -> fa_clean s ->
  prim_committed s <= kUserMapSize * st_nev s + kFreeArrayMax.
Proof.
  intros U s W HF.
  pose proof (wf_prim_ev _ _ _ _ _ W) as PU.
  set (b := fun j : nat => if Nat.eqb j 24 then kFreeArrayMax else 0).
  assert (SB : fold_right Z.add 0 (map b (seq 0 32)) = kFreeArrayMax) by reflexivity.
  assert (FA : forall j, (j < length (st_regions s))%nat -> 0 <= rg_mapped_fa (nth j (st_regions s) region0) <= b j).
  { intros j Hj. rewrite (wf_len_regions _ _ _ _ _ W) in Hj. destruct j as [|j].
    - pose proof (wf_reg0 _ _ _ _ _ W) as H0. unfold reg, znth in H0. change (Z.to_nat 0) with 0%nat in H0.
      rewrite H0. cbn. lia.
    - pose proof (wf_classes _ _ _ _ _ W (Z.of_nat (S j)) ltac:(lia)) as C. unfold wf_class, reg, znth in C.
      rewrite Nat2Z.id in C.
      pose proof (wr_fa _ _ _ _ _ _ C) as [F1 _]. pose proof (wr_fa_bound _ _ _ _ _ _ C) as F2.
      unfold b. destruct (Nat.eqb_spec (S j) 24) as [E|E]; [lia|].
      pose proof (HF (Z.of_nat (S j)) ltac:(lia) ltac:(unfold kBatchClass; lia)) as Z0.
      unfold reg, znth in Z0. rewrite Nat2Z.id in Z0. lia. }
  pose proof (fold_fa_le _ b FA) as G. rewrite (wf_len_regions _ _ _ _ _ W), SB in G.
  unfold prim_committed. unfold prim_user_mapped in PU. lia.
Qed.

Lemma bb_list : forall l,
  fold_right (fun k acc => if is_alloc k then ck_req k + acc else acc) 0 l
  = fold_right (fun b acc => snd b + acc) 0 (map (fun k => (ck_user k, ck_req k)) (List.filter is_alloc l)).
Proof.
  induction l as [|k t IH]; [reflexivity|].
  cbn [List.filter fold_right]. destruct (is_alloc k); [cbn [map fold_right snd]; rewrite IH; reflexivity | exact IH].
Qed.

Lemma blocks_bytes_blocks : forall s,
  blocks_bytes s = fold_right (fun b acc => snd b + acc) 0 (blocks s).
Proof. intros s. exact (bb_list (st_chunks s)). Qed.

(** The room, from the event count, the live bytes and [fa_clean]. *)
Theorem mroom_small : forall U S, Wf U S -> st_nev S <= 64 -> fa_clean S -> blocks_bytes S <= 2 ^ 28 -> qtight S ->
  mroom S.
Proof.
  intros U s W NEV HF BB (T1 & T2 & T3).
  pose proof (prim_committed_clean U s W HF) as PC.
  pose proof (sec_reserved_bound U s W) as SR.
  pose proof (wf_chunks _ _ _ _ _ W) as CK. pose proof (wf_chunks_ev _ _ _ _ _ W) as CE.
  pose proof (wf_secs_ev _ _ _ _ _ W) as SE. pose proof (wf_nev _ _ _ _ _ W) as NE.
  pose proof (wf_quarantine _ _ _ _ _ W) as Q.
  assert (R0 : Forall (fun k => 0 <= ck_req k) (st_chunks s)) by (eapply Forall_impl; [|exact CK]; intros k [Hk _]; lia).
  pose proof (sec_bytes_le _ R0) as B1. pose proof (alloc_n_le _ R0) as B2.
  change (sec_bytes (st_chunks s)) with (sec_live_bytes s) in B1. change (reqbytes (st_chunks s)) with (blocks_bytes s) in B2.
  change (quar_nl (st_chunks s)) with (quar_n s) in B1.
  assert (QN : queued_n s <= qc_bytes (st_qthread s) + qc_bytes (st_qglobal s)).
  { rewrite (wq_bytes_t _ Q), (wq_bytes_g _ Q), !sum_bytes_items. unfold queued_n, q_items, all_batches.
    rewrite flat_map_app, items_n_app. unfold kBatchBytes. lia. }
  pose proof (sec_hulls_count U 0 0 0 s W) as SH.
  assert (HM : HULL_MAX = 33564672) by reflexivity.
  assert (SH2 : HULL_MAX * Z.of_nat (length (st_secs s)) <= HULL_MAX * 64)
    by (apply Z.mul_le_mono_nonneg_l; lia).
  assert (PU2 : kUserMapSize * st_nev s <= kUserMapSize * 64)
    by (apply Z.mul_le_mono_nonneg_l; [unfold kUserMapSize; lia | lia]).
  assert (EA2 : EV_A * st_nev s <= EV_A * 64)
    by (apply Z.mul_le_mono_nonneg_l; [unfold EV_A; lia | lia]).
  assert (CH2 : 2 ^ 14 * Z.of_nat (length (st_chunks s)) <= 2 ^ 14 * 64)
    by (apply Z.mul_le_mono_nonneg_l; lia).
  unfold mroom, ameter, abudget, VM_HEAD, ASAN_VM_LMIN, E_BASE, A_BASE, EV_A in *.
  unfold kUserMapSize, kFreeArrayMax, kQuarantineMax, kQuarantineCacheMax in *. rewrite HM in *. lia.
Qed.

(** At [init_state], where the driver's first malloc is called. *)
Lemma mroom_init : forall U, Wf U init_state -> mroom init_state.
Proof.
  intros U W. apply (mroom_small U init_state W); [cbn; lia | exact fa_clean_init | cbn; lia | exact qtight_init].
Qed.

(** At a driver state holding one block of [cap] bytes. *)
Lemma mroom_drv : forall U S (pb : sptr) cap, Wf U S -> st_nev S <= 64 -> fa_clean S ->
  blocks S = [(pb, cap)] -> cap <= 2 ^ 28 -> qtight S -> mroom S.
Proof.
  intros U S pb cap W NEV HF HB Hc HT. apply (mroom_small U S W NEV HF); [|exact HT].
  rewrite blocks_bytes_blocks, HB. cbn [fold_right snd]. lia.
Qed.
