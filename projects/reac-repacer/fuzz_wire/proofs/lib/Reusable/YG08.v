(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YG08.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: EV_MAX raised to 11776, as in omx-clap-core/fuzz_manifest's copy of this file; new prim_committed_bound_nev bounds the primary commit by kUserMapSize * st_nev (wf_prim_ev), and vm_budget_slack's big regime uses it with st_nev <= EV_BIG instead of prim_committed_bound_any. *)
(* Modified by Theorem Labs, 2026-10: the empty-depot switch (DepotCfg.depot_has_trace) taken from proofs/libreac/fuzz_knock/lib/Reusable/YG08.v at 88154566652a, hunk by hunk (provenance evidence/depot: depot-classes.tsv, depot_apply.py): hunks 1 2 6 7 8 9 10 11 12; hunks 3 4 5 keep this file's text; hunk 9 (prim_committed_bound_any -> prim_committed_bound_nev) taken with this file's name restored. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_grant/lib/Reusable/YG08.v at 4f87de75d677 (donor image sha256 c2c7559b29bd), with its module paths changed. *)
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK04 YM05.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG0f YG0n DepotCfg.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YG09.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Definition SEC_LIVE_MAX : Z := 2 ^ 34 + 2 ^ 32.
Lemma sec_map_size_bound : forall n, 0 <= n -> sec_map_size n <= req_size n + 2 ^ 14.
Proof.
intros n Hn. unfold sec_map_size, needed_size.
pose proof (needed_primary_bounds n Hn) as (N1 & N2 & N3). pose proof (rz_size_bounds n) as [R1 R2]. pose proof (req_size_bounds n Hn) as (_ & Q1 & Q2 & Q3).
assert (RU : forall x, 0 <= x -> round_up x kPage < x + kPage).
{ intros x Hx. unfold round_up, kPage. pose proof (Z.mul_div_le (x + 4096 - 1) 4096 ltac:(lia)). lia. }
destruct (from_primary n); (eapply Z.le_trans; [apply Z.add_le_mono_r; apply Z.lt_le_incl; apply RU; lia | unfold kPage; lia]).
Qed.
Definition alloc_n (l : list chunk) : Z := fold_right (fun k acc => if is_alloc k then ck_n k + acc else acc) 0 l.
Definition sec_bytes (l : list chunk) : Z :=
fold_right (fun k acc => match ck_beg k with PSec _ _ => sec_map_size (ck_req k) + acc | _ => acc end) 0 l.
Lemma sec_bytes_le : forall l, Forall (fun k => 0 <= ck_req k) l ->
sec_bytes l <= alloc_n l + quar_nl l + 2 ^ 14 * Z.of_nat (length l).
Proof.
intros l H. induction H as [|k t Hk Ht IH]; [cbn; lia|].
unfold sec_bytes, alloc_n, quar_nl in *. cbn [fold_right length]. rewrite Nat2Z.inj_succ.
pose proof (sec_map_size_bound (ck_req k) Hk) as B. pose proof (req_size_bounds (ck_req k) Hk) as (_ & Q1 & _).
unfold ck_n in *. destruct (ck_beg k); destruct (is_alloc k); lia.
Qed.
Definition reqbytes (l : list chunk) : Z := fold_right (fun k acc => if is_alloc k then ck_req k + acc else acc) 0 l.
Lemma alloc_n_le : forall l, Forall (fun k => 0 <= ck_req k) l -> alloc_n l <= reqbytes l + Z.of_nat (length l).
Proof.
intros l H. induction H as [|k t Hk Ht IH]; [cbn; lia|].
unfold alloc_n, reqbytes in *. cbn [fold_right length]. rewrite Nat2Z.inj_succ.
pose proof (req_size_bounds (ck_req k) Hk) as (E & _ & _). unfold ck_n in *. destruct (is_alloc k); lia.
Qed.
Lemma sum_bytes_items : forall l, sum_bytes l = kBatchBytes * Z.of_nat (length l) + items_n (flat_map b_items l).
Proof.
induction l as [|b t IH]; [cbn; lia|]. unfold sum_bytes in *. cbn [fold_right length flat_map]. rewrite Nat2Z.inj_succ, items_n_app, IH.
unfold b_bytes, items_n. lia.
Qed.
Lemma prim_committed_bound_nev : forall U s, Wf U s -> prim_committed s <= kUserMapSize * st_nev s + 32 * kFreeArrayMax.
Proof.
intros U s W.
assert (PU : prim_user_mapped s <= kUserMapSize * st_nev s).
{ pose proof (wf_prim_ev _ _ _ _ _ W) as P. lia. }
assert (FA : forall j, (j < length (st_regions s))%nat -> 0 <= rg_mapped_fa (nth j (st_regions s) region0) <= kFreeArrayMax).
{ intros j Hj. rewrite (wf_len_regions _ _ _ _ _ W) in Hj. destruct j as [|j].
- pose proof (wf_reg0 _ _ _ _ _ W) as H0. unfold reg, znth in H0. change (Z.to_nat 0) with 0%nat in H0. rewrite H0. cbn. unfold kFreeArrayMax. lia.
- pose proof (wf_classes _ _ _ _ _ W (Z.of_nat (S j)) ltac:(lia)) as C. unfold wf_class, reg, znth in C. rewrite Nat2Z.id in C.
pose proof (wr_fa _ _ _ _ _ _ C) as [F1 _]. pose proof (wr_fa_bound _ _ _ _ _ _ C) as F2. lia. }
assert (G : forall l, (forall j, (j < length l)%nat -> 0 <= rg_mapped_fa (nth j l region0) <= kFreeArrayMax) ->
fold_right (fun r acc => rg_mapped_user r + rg_mapped_fa r + acc) 0 l
<= fold_right (fun r acc => rg_mapped_user r + acc) 0 l + kFreeArrayMax * Z.of_nat (length l)).
{ intros l Hl. induction l as [|r t IH]; [cbn; lia|]. cbn [fold_right length]. rewrite Nat2Z.inj_succ.
pose proof (Hl 0%nat ltac:(cbn; lia)) as H0. cbn in H0.
specialize (IH ltac:(intros j Hj; apply (Hl (S j)); cbn; lia)). lia. }
unfold prim_committed. pose proof (G _ FA) as GG. unfold prim_user_mapped in *.
rewrite (wf_len_regions _ _ _ _ _ W) in GG. change (Z.of_nat 32) with 32 in GG. unfold kFreeArrayMax in *. lia.
Qed.
Lemma prim_committed_bound : forall U s, Wf U s -> st_nev s <= EV_MAX -> prim_committed s <= kUserMapSize * EV_MAX + 32 * kFreeArrayMax.
Proof.
intros U s W NEx. pose proof (prim_committed_bound_nev U s W) as P. unfold kUserMapSize, EV_MAX in *. nia.
Qed.
Lemma prim_committed_bound_any : forall U s, Wf U s -> prim_committed s <= 32 * (kUserMapSize * EV_MAX) + 32 * kFreeArrayMax.
Proof.
intros U s W.
assert (B : forall j, (j < length (st_regions s))%nat ->
0 <= rg_mapped_user (nth j (st_regions s) region0) + rg_mapped_fa (nth j (st_regions s) region0) <= kUserMapSize * EV_MAX + kFreeArrayMax).
{ intros j Hj. rewrite (wf_len_regions _ _ _ _ _ W) in Hj. destruct j as [|j].
- pose proof (wf_reg0 _ _ _ _ _ W) as H0. unfold reg, znth in H0. change (Z.to_nat 0) with 0%nat in H0. rewrite H0. cbn. unfold kUserMapSize, EV_MAX, kFreeArrayMax. lia.
- pose proof (wf_classes _ _ _ _ _ W (Z.of_nat (S j)) ltac:(lia)) as C. unfold wf_class, reg, znth in C. rewrite Nat2Z.id in C.
pose proof (wr_fa _ _ _ _ _ _ C) as [F1 _]. pose proof (wr_fa_bound _ _ _ _ _ _ C) as F2. pose proof (wr_mapped_bound _ _ _ _ _ _ C) as M.
pose proof (wr_alloc _ _ _ _ _ _ C). lia. }
assert (G : forall l, (forall j, (j < length l)%nat -> 0 <= rg_mapped_user (nth j l region0) + rg_mapped_fa (nth j l region0) <= kUserMapSize * EV_MAX + kFreeArrayMax) ->
fold_right (fun r acc => rg_mapped_user r + rg_mapped_fa r + acc) 0 l <= (kUserMapSize * EV_MAX + kFreeArrayMax) * Z.of_nat (length l)).
{ intros l Hl. induction l as [|r t IH]; [cbn; lia|]. cbn [fold_right length]. rewrite Nat2Z.inj_succ.
pose proof (Hl 0%nat ltac:(cbn; lia)) as H0. cbn in H0. specialize (IH ltac:(intros j Hj; apply (Hl (S j)); cbn; lia)). lia. }
unfold prim_committed. pose proof (G _ B) as GG. rewrite (wf_len_regions _ _ _ _ _ W) in GG. change (Z.of_nat 32) with 32 in GG. lia.
Qed.
Theorem sec_live_bound : forall U s, Wf U s -> st_nev s <= EV_MAX -> qloose s -> sec_live_bytes s <= SEC_LIVE_MAX.
Proof.
intros U s W NEx (T1 & T2 & T3).
pose proof (wf_chunks _ _ _ _ _ W) as CK. pose proof (wf_chunks_ev _ _ _ _ _ W) as CE. pose proof (wf_nev _ _ _ _ _ W) as NE.
pose proof (wf_live _ _ _ _ _ W) as LV. pose proof (wf_quarantine _ _ _ _ _ W) as Q.
assert (R0 : Forall (fun k => 0 <= ck_req k) (st_chunks s)) by (eapply Forall_impl; [|exact CK]; intros k [Hk _]; lia).
pose proof (sec_bytes_le _ R0) as B1. pose proof (alloc_n_le _ R0) as B2.
change (sec_bytes (st_chunks s)) with (sec_live_bytes s) in B1. change (reqbytes (st_chunks s)) with (blocks_bytes s) in B2.
change (quar_nl (st_chunks s)) with (quar_n s) in B1.
assert (QN : queued_n s <= qc_bytes (st_qthread s) + qc_bytes (st_qglobal s)).
{ rewrite (wq_bytes_t _ Q), (wq_bytes_g _ Q), !sum_bytes_items. unfold queued_n, q_items, all_batches. rewrite flat_map_app, items_n_app.
unfold kBatchBytes. lia. }
unfold SEC_LIVE_MAX, LIVE_MAX, EV_MAX in *. lia.
Qed.
Lemma sec_bytes_le_sec : forall l, Forall (fun k => 0 <= ck_req k) l -> sec_bytes l <= alloc_n l + quar_nl l + 2 ^ 14 * nsec_l l.
Proof.
intros l H. induction H as [|k t Hk Ht IH]; [cbn; lia|].
unfold sec_bytes, alloc_n, quar_nl, nsec_l in *. cbn [fold_right].
pose proof (sec_map_size_bound (ck_req k) Hk) as B. pose proof (req_size_bounds (ck_req k) Hk) as (_ & Q1 & _).
unfold ck_n in *. destruct (ck_beg k); destruct (is_alloc k); lia.
Qed.
Theorem sec_live_bound_big : forall U s, Wf U s -> qloose s ->
Z.of_nat (length (st_chunks s)) <= 2 ^ 23 -> Z.of_nat (length (st_sec_arr s)) <= 2 ^ 14 ->
sec_live_bytes s <= SEC_LIVE_MAX.
Proof.
intros U s W (T1 & T2 & T3) HC HS.
pose proof (wf_chunks _ _ _ _ _ W) as CK. pose proof (wf_live _ _ _ _ _ W) as LV. pose proof (wf_quarantine _ _ _ _ _ W) as Q.
assert (R0 : Forall (fun k => 0 <= ck_req k) (st_chunks s)) by (eapply Forall_impl; [|exact CK]; intros k [Hk _]; lia).
pose proof (sec_bytes_le_sec _ R0) as B1. pose proof (alloc_n_le _ R0) as B2. pose proof (nsec_le_arr U 0 0 0 s W) as B3.
change (sec_bytes (st_chunks s)) with (sec_live_bytes s) in B1. change (reqbytes (st_chunks s)) with (blocks_bytes s) in B2.
change (quar_nl (st_chunks s)) with (quar_n s) in B1.
assert (QN : queued_n s <= qc_bytes (st_qthread s) + qc_bytes (st_qglobal s)).
{ rewrite (wq_bytes_t _ Q), (wq_bytes_g _ Q), !sum_bytes_items. unfold queued_n, q_items, all_batches. rewrite flat_map_app, items_n_app.
unfold kBatchBytes. lia. }
unfold SEC_LIVE_MAX, LIVE_MAX in *. lia.
Qed.
Lemma sec_reserved_bound : forall U s, Wf U s -> 0 <= 8 * st_sec_reserved s <= 2 ^ 17.
Proof.
intros U s W. pose proof (ws_reserved _ (wf_secondary _ _ _ _ _ W)) as R1. pose proof (ws_reserved_al _ (wf_secondary _ _ _ _ _ W)) as R2.
unfold kPtrArrayEntriesPerCommit in *. lia.
Qed.
Lemma sec_extents_sizes64P : forall U pp cc bb ly s, WfP U pp cc bb s -> Forall (fun e => 4096 <= snd e < 2 ^ 64) (sec_extents ly s).
Proof.
intros U pp cc bb ly s W. pose proof (wf_chunks _ _ _ _ _ W) as CK. unfold sec_extents. apply Forall_forall. intros e He.
apply in_flat_map in He as (k & Hk & He). pose proof (proj1 (Forall_forall _ _) CK k Hk) as [Hn _].
destruct (ck_beg k) as [|o|r o|c p]; try destruct He as [<-|[]]; try destruct He. cbn [snd].
pose proof (sec_map_size_bound (ck_req k) ltac:(lia)) as SB. pose proof (req_size_bounds (ck_req k) ltac:(lia)) as RB.
assert (LO : 4096 <= sec_map_size (ck_req k)).
{ unfold sec_map_size. pose proof (round_up_ge (needed_size (ck_req k)) kPage ltac:(unfold kPage; lia)) as [R _].
pose proof (needed_primary_bounds (ck_req k) ltac:(lia)) as (N1 & N2 & _). pose proof (rz_size_bounds (ck_req k)) as [RZ _].
assert (0 <= needed_size (ck_req k)) by (unfold needed_size; destruct (from_primary (ck_req k)); lia). unfold kPage in *. lia. }
unfold MALLOC_MAX in *. lia.
Qed.
Lemma sec_extents_sizes64 : forall U ly s, Wf U s -> Forall (fun e => 0 <= snd e < 2 ^ 64) (sec_extents ly s).
Proof. intros U ly s W. eapply Forall_impl; [|exact (sec_extents_sizes64P U 0 0 0 ly s W)]. cbn beta. intros e H. lia. Qed.
Lemma al_eager {rc : YM05.RunCeil}   : forall segs U ly s md, Wf U s -> ALedger segs ly s md ->
depot_pick (eager_used md <= E_BASE + prim_committed s + 8 * st_sec_reserved s + sec_live_bytes s)
(eager_used md <= E_BASE + prim_committed s + 8 * st_sec_reserved s + sec_live_bytes s + nb_eager ly).
Proof.
intros segs U ly s md W L. pose proof (al_eager_x _ _ _ _ L) as X.
pose proof (sec_extents_sizes_sum ly s (sec_extents_sizes64 U ly s W) (vm_noaccess (m_vmmaps md)) (m_vm_lazy md)) as Y. lia.
Qed.
Definition HULL_MAX : Z := SEC_LEN_MAX / 8 + 8192.
Lemma sec_hulls_count : forall U pp cc bb s, WfP U pp cc bb s -> 0 <= sec_hulls s <= HULL_MAX * Z.of_nat (length (st_secs s)).
Proof.
intros U pp cc bb s W. pose proof (ws_lens _ (wf_secondary _ _ _ _ _ W)) as L. unfold sec_hulls.
induction L as [|sm t Hsm Ht IH]; [cbn; lia|]. cbn [fold_right length]. rewrite Nat2Z.inj_succ.
assert (0 <= sm_len sm / 8 <= SEC_LEN_MAX / 8) by (split; [apply Z.div_pos; lia | apply Z.div_le_mono; lia]).
unfold HULL_MAX in *. lia.
Qed.
Definition VM_SLACK : Z := 2 ^ 36 + 2 ^ 31.
Theorem vm_budget_slack : forall U s, Wf U s -> aregime_mid s -> qloose s ->
depot_pick (E_BASE + prim_committed s + 8 * st_sec_reserved s + sec_live_bytes s + abudget s + VM_SLACK <= ASAN_VM_LIMIT)
(E_BASE + prim_committed s + 8 * st_sec_reserved s + sec_live_bytes s + abudget s + kNodesBlockSize + VM_SLACK <= ASAN_VM_LIMIT).
Proof.
intros U s W [NEx|(NEb & HH & HC)] QL; pose proof (wf_nev _ _ _ _ _ W) as NE; pose proof (sec_reserved_bound U s W) as SR.
- pose proof (sec_live_bound U s W NEx QL) as SL. pose proof (prim_committed_bound U s W NEx) as PC.
pose proof (sec_hulls_count U 0 0 0 s W) as SH. pose proof (wf_secs_ev _ _ _ _ _ W) as SE.
assert (SH2 : sec_hulls s <= HULL_MAX * EV_MAX) by (unfold HULL_MAX, SEC_LEN_MAX, EV_MAX in *; change ((2 ^ 28 + 2 ^ 14) / 8 + 8192) with 33564672 in *; nia).
unfold abudget, VM_SLACK, E_BASE, ASAN_VM_LIMIT, A_BASE, EV_A, SEC_LIVE_MAX, kUserMapSize, EV_MAX, kFreeArrayMax, HULL_MAX, SEC_LEN_MAX in *.
change ((2 ^ 28 + 2 ^ 14) / 8 + 8192) with 33564672 in *.
lazymatch eval cbv in depot_has_trace with true => idtac | false =>
pose proof (depot_abytes_bounds s); unfold kNodesBlockSize, kStoreBlockSize in * end. nia.
- assert (HS : Z.of_nat (length (st_sec_arr s)) <= 2 ^ 14).
{ pose proof (ws_reserved _ (wf_secondary _ _ _ _ _ W)) as R. unfold kPtrArrayEntriesPerCommit in R. lia. }
pose proof (sec_live_bound_big U s W QL HC HS) as SL. pose proof (prim_committed_bound_nev U s W) as PC.
unfold abudget, VM_SLACK, E_BASE, ASAN_VM_LIMIT, A_BASE, EV_A, SEC_LIVE_MAX, kUserMapSize, EV_MAX, kFreeArrayMax, EV_BIG, HPOT_MAX in *.
lazymatch eval cbv in depot_has_trace with true => idtac | false =>
pose proof (depot_abytes_bounds s); unfold kNodesBlockSize, kStoreBlockSize in * end. nia.
Qed.
Lemma meter_room {rc : YM05.RunCeil} : forall segs U ly s md (abytes k h : Z),
Wf U s -> ALedger segs ly s md -> abytes <= abudget s ->
ameter s + h <= ASAN_VM_LMIN -> 0 <= k ->
forall eager vmlim, eager <= eager_used md + k -> vmlim = vm_limit (m_vmmaps md) ->
eager + (abytes + k) + (h - 2 * k) <= vmlim.
Proof.
intros segs U ly s md abytes k h W L HA HM Hk eager vmlim HE ->.
pose proof (al_eager segs U ly s md W L) as AE. pose proof (al_limit _ _ _ _ L) as AL. unfold ameter in HM.
lazymatch eval cbv in depot_has_trace with true => idtac | false => pose proof (nb_eager_bounds ly) end. lia.
Qed.
Lemma mroom_slack {rc : YM05.RunCeil} : forall segs U ly s md0 md (a0 a k : Z),
Wf U s -> ALedger segs ly s md0 -> a0 <= abudget s -> mroom s ->
vm_limit (m_vmmaps md) = vm_limit (m_vmmaps md0) -> eager_used md <= eager_used md0 + k -> a <= a0 + k -> 0 <= k ->
eager_used md + a + (VM_HEAD - 2 * k) <= vm_limit (m_vmmaps md).
Proof.
intros segs U ly s md0 md a0 a k W L HA HM LIM EG AB Hk.
pose proof (al_eager segs U ly s md0 W L) as AE. pose proof (al_limit _ _ _ _ L) as AL. unfold mroom, ameter in HM.
lazymatch eval cbv in depot_has_trace with true => idtac | false => pose proof (nb_eager_bounds ly) end. lia.
Qed.
Lemma rroom_slack {rc : YM05.RunCeil} : forall segs U ly s md0 md (a0 a k : Z),
Wf U s -> ALedger segs ly s md0 -> a0 <= abudget s -> rroom s ->
vm_limit (m_vmmaps md) = vm_limit (m_vmmaps md0) -> eager_used md <= eager_used md0 + k -> a <= a0 + k -> 0 <= k ->
eager_used md + a + (RF_HEAD - 2 * k) <= vm_limit (m_vmmaps md).
Proof.
intros segs U ly s md0 md a0 a k W L HA HM LIM EG AB Hk.
pose proof (al_eager segs U ly s md0 W L) as AE. pose proof (al_limit _ _ _ _ L) as AL. unfold rroom, ameter in HM.
lazymatch eval cbv in depot_has_trace with true => idtac | false => pose proof (nb_eager_bounds ly) end. lia.
Qed.
Lemma ameter_small : forall U s, Wf U s -> aregime_mid s -> qloose s -> ameter s + VM_SLACK <= ASAN_VM_LIMIT.
Proof. intros U s W R Q. unfold ameter. pose proof (vm_budget_slack U s W R Q). lia. Qed.
Lemma mtr_ok_of_regime : forall U s m, Wf U s -> aregime_mid s -> qloose s -> 0 <= m <= 2 ^ 36 -> mtr_ok s m.
Proof. intros U s m W R Q Hm. pose proof (ameter_small U s W R Q) as A. unfold mtr_ok, VM_HEAD, ASAN_VM_LMIN. unfold VM_SLACK, ASAN_VM_LIMIT in A. lia. Qed.
Lemma mroom_of_regime : forall U s, Wf U s -> aregime_mid s -> qloose s -> mroom s.
Proof. intros U s W R Q. apply (mroom_of_mtr_ok s 0); [lia | apply (mtr_ok_of_regime U s 0 W R Q); lia]. Qed.
