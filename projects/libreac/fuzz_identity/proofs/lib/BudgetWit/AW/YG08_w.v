(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: made from projects/cgif/cgif_file_fuzzer/proofs/lib/YG08.v, with its module paths changed; 9 of its 195 lines of code are new or changed and 5 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: EV_MAX raised to 11776, as in omx-clap-core/fuzz_manifest's copy of this file; new prim_committed_bound_nev bounds the primary commit by kUserMapSize * st_nev (wf_prim_ev), and vm_budget_slack's big regime uses it with st_nev <= EV_BIG instead of prim_committed_bound_any. *)
(* Modified by Theorem Labs, 2026-11: made from Reusable/YG08.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
(* Theorem Labs, 2026-11: cut for the usage path at 16 GiB: the pruning removed declarations that this path does not use; some unused declarations can remain. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG0f.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YG0n_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG09.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
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
eager_used md <= E_BASE + prim_committed s + 8 * st_sec_reserved s + sec_live_bytes s.
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
Lemma mroom_slack {rc : YM05.RunCeil} : forall segs U ly s md0 md (a0 a k : Z),
Wf U s -> ALedger segs ly s md0 -> a0 <= abudget s -> mroom s ->
vm_limit (m_vmmaps md) = vm_limit (m_vmmaps md0) -> eager_used md <= eager_used md0 + k -> a <= a0 + k -> 0 <= k ->
eager_used md + a + (VM_HEAD - 2 * k) <= vm_limit (m_vmmaps md).
Proof.
intros segs U ly s md0 md a0 a k W L HA HM LIM EG AB Hk.
pose proof (al_eager segs U ly s md0 W L) as AE. pose proof (al_limit _ _ _ _ L) as AL. unfold mroom, ameter in HM. lia.
Qed.
Lemma rroom_slack {rc : YM05.RunCeil} : forall segs U ly s md0 md (a0 a k : Z),
Wf U s -> ALedger segs ly s md0 -> a0 <= abudget s -> rroom s ->
vm_limit (m_vmmaps md) = vm_limit (m_vmmaps md0) -> eager_used md <= eager_used md0 + k -> a <= a0 + k -> 0 <= k ->
eager_used md + a + (RF_HEAD - 2 * k) <= vm_limit (m_vmmaps md).
Proof.
intros segs U ly s md0 md a0 a k W L HA HM LIM EG AB Hk.
pose proof (al_eager segs U ly s md0 W L) as AE. pose proof (al_limit _ _ _ _ L) as AL. unfold rroom, ameter in HM. lia.
Qed.
(* Theorem Labs, 2026-11: the released mtr_ok_of_regime and mroom_of_regime are left out. With YG0n_w.ASAN_VM_LMIN
   = 2^34 they would claim room under 16 GiB for every state of the allocator's regime (up to EV_MAX events), which
   ameter does not give; BudgetWit/MroomB.v proves mroom on the driver's own small states instead. *)
