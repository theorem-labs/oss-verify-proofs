(* CARRIED from a working branch 3dd49fa29fa14b99e3c465cacbfe79a09756bb26,
   proofs/omx-clap-core/fuzz_preset/lib/Reusable/YGcfSecBound.v, sha256 0d584353e9a08b3333481cc1f9fa39ef8ad668c5d4474d3bfbf7227f1b18186e.
   DO NOT EDIT in this tree: change it on that branch and carry it again. The only change
   made here is the module prefix OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib -> OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib. *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset's event-free allocator instance (suffix cf), a STATE bound on the
   secondary count. st_sec_arr holds the live AND the quarantined secondaries (an entry leaves it only at the
   quarantine recycle), so a walk must not count it by steps: fuzz_reply makes about 1.59M secondary mallocs
   per call. The bound here reads the state only:
     (a) wf_sec_cf's wsc_arr_chunks and wsc_nodup (YG01cf.v): every entry r of st_sec_arr is a PSec r chunk of
         st_chunks, and the entries are distinct, so st_sec_arr is no longer than the PSec chunks;
     (b) a chunk is CAllocated or CQuarantined (cstate, YG00.v:135), and every quarantined chunk is a queued
         item (YGcfRoom.v's quar_in_q, from wf_quar and qtight);
     (c) a PSec chunk has from_primary (ck_req k) = false (chunk_ok_cf, YG01cf.v), so its request is at least
         64,513 (sec_req_min; exact: sec_req_min_exact), and ck_n = req_size = the request;
     (d) under qtight the queued items account at most kQuarantineMax + kQuarantineCacheMax bytes
         (YGcfRoom.v's quar_bytes_ok_cf).
   So at most QSEC_MAX = (2 ^ 28 + 2 ^ 20) / 64,513 = 4,177 secondaries are quarantined (QSEC_MAX_value).
   Nothing here is a function's proof (rule 24). No address. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
  YG00 YG0a YG01 YG03 YGcfNames YG00cf YG01cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YGcfRoom.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* The live secondaries: PSec chunks still allocated. *)
Definition live_sec_blocks (S : astate) : Z :=
  Z.of_nat (length (filter (fun k => match ck_beg k, ck_state k with PSec _ _, CAllocated => true | _, _ => false end)
    (st_chunks S))).

(* The most quarantined secondaries qtight leaves room for. *)
Definition QSEC_MAX : Z := (kQuarantineMax + kQuarantineCacheMax) / 64513.

Lemma QSEC_MAX_value : QSEC_MAX = 4177.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================ (c) a secondary request is at least 64,513 *)
Lemma sec_req_min : forall n, 0 <= n -> from_primary n = false -> 64513 <= n.
Proof.
  assert (H : zall (Z.to_nat (64512 - 0 + 1)) 0 from_primary = true) by (vm_compute; reflexivity).
  intros n Hn Hf. destruct (Z.le_gt_cases 64513 n) as [Hle|Hlt]; [exact Hle|].
  rewrite (zall_range 0 64512 _ H n ltac:(lia)) in Hf. discriminate Hf.
Qed.

(* 64,513 is the least secondary request: the bound of sec_req_min is exact. *)
Lemma sec_req_min_exact : from_primary 64512 = true /\ from_primary 64513 = false.
Proof. split; vm_compute; reflexivity. Qed.

(* ================================================================ the chunk classes counted *)
Definition is_sec (k : chunk) : bool := match ck_beg k with PSec _ _ => true | _ => false end.
Definition is_lsec (k : chunk) : bool :=
  match ck_beg k, ck_state k with PSec _ _, CAllocated => true | _, _ => false end.
Definition is_qsec (k : chunk) : bool :=
  match ck_beg k, ck_state k with PSec _ _, CQuarantined => true | _, _ => false end.
Definition sec_idx (k : chunk) : nat := match ck_beg k with PSec r _ => r | _ => O end.

(* (b) a PSec chunk is live or quarantined *)
Lemma len_sec_split : forall l,
  length (filter is_sec l) = (length (filter is_lsec l) + length (filter is_qsec l))%nat.
Proof.
  induction l as [|[b q st] t IH]; [reflexivity|].
  destruct b, st; cbn [filter is_sec is_lsec is_qsec ck_beg ck_state length]; lia.
Qed.

(* (a) st_sec_arr is no longer than the PSec chunks *)
Lemma sec_arr_le_sec_chunks {cp : CfParams} : forall s, wf_sec_cf s ->
  (length (st_sec_arr s) <= length (filter is_sec (st_chunks s)))%nat.
Proof.
  intros s H. rewrite <- (length_map sec_idx (filter is_sec (st_chunks s))).
  apply NoDup_incl_length; [exact (wsc_nodup _ H)|].
  intros r Hr. apply (wsc_arr_chunks _ H) in Hr as (k & Hk & Hb).
  apply in_map_iff. exists k. split.
  - unfold sec_idx. rewrite Hb. reflexivity.
  - apply filter_In. split; [exact Hk|]. unfold is_sec. rewrite Hb. reflexivity.
Qed.

Lemma items_n_ge_sec : forall l, Forall (fun x => 64513 <= ck_n x) l -> 64513 * Z.of_nat (length l) <= items_n l.
Proof.
  intros l H. induction H as [|k t Hk Ht IH]; [cbn; lia|].
  rewrite items_n_cons. cbn [length]. rewrite Nat2Z.inj_succ. lia.
Qed.

(* (c) + (d): the quarantined secondaries' bytes fit the quarantine *)
Lemma qsec_bytes {cp : CfParams} : forall U s, Wf_cf U s -> qtight s ->
  64513 * Z.of_nat (length (filter is_qsec (st_chunks s))) <= kQuarantineMax + kQuarantineCacheMax.
Proof.
  intros U s W T.
  pose proof (wfc_quarantine _ _ _ _ _ W) as Q. pose proof (wfc_chunks _ _ _ _ _ W) as HC.
  set (L := filter is_qsec (st_chunks s)).
  assert (HndL : NoDup L).
  { apply NoDup_filter. exact (NoDup_map_inv _ _ (wfc_chunks_nodup _ _ _ _ _ W)). }
  assert (HincL : incl L (q_items s)).
  { intros k Hk. unfold L in Hk. apply filter_In in Hk as [Hk Hq].
    apply (YGcfRoom.quar_in_q U s W T k Hk). revert Hq. unfold is_qsec.
    destruct (ck_beg k), (ck_state k); intros Hq; cbn in Hq; first [reflexivity | discriminate Hq]. }
  assert (HposQ : Forall (fun x => 0 <= ck_n x) (q_items s)).
  { apply Forall_forall. intros k Hk. pose proof (proj1 (Forall_forall _ _) (wq_items _ Q) k Hk) as [Hk1 _].
    pose proof (YGcfRoom.chunk_ok_cf_n s k (proj1 (Forall_forall _ _) HC k Hk1)). lia. }
  assert (HminL : Forall (fun x => 64513 <= ck_n x) L).
  { apply Forall_forall. intros k Hk. unfold L in Hk. apply filter_In in Hk as [Hk Hq].
    pose proof (proj1 (Forall_forall _ _) HC k Hk) as [Hr Hb]. unfold is_qsec in Hq.
    revert Hq Hb. destruct (ck_beg k); intros Hq Hb; cbn in Hq; try discriminate Hq.
    destruct Hb as [Hf _]. pose proof (sec_req_min (ck_req k) (proj1 Hr) Hf) as Hm.
    pose proof (req_size_bounds (ck_req k) (proj1 Hr)) as (_ & _ & Hs & _). unfold ck_n. lia. }
  pose proof (items_n_ge_sec L HminL) as Hge.
  pose proof (YGcfRoom.items_n_incl L (q_items s) HndL HincL HposQ) as Hle.
  pose proof (YGcfRoom.quar_bytes_ok_cf U s W T) as (_ & _ & _ & Hz).
  unfold YGcfRoom.room_of_cf in Hz. cbn [PresetRoom.rs_quar PresetRoom.rs_batches] in Hz.
  rewrite YGcfRoom.zsum_map_ck_n in Hz.
  unfold PresetRoom.QT, PresetRoom.Q_MAX, PresetRoom.Q_CACHE, PresetRoom.Q_BATCH_BYTES in Hz.
  unfold kQuarantineMax, kQuarantineCacheMax. lia.
Qed.

Section SECBOUND.
Context {cp : CfParams}.

(* THE STATE BOUND. st_sec_arr is at most the live secondaries plus QSEC_MAX = 4,177. *)
Theorem sec_arr_bound_cf : forall U pp cc bb S, WfP_cf U pp cc bb S -> qtight S ->
  Z.of_nat (length (st_sec_arr S)) <= live_sec_blocks S + QSEC_MAX.
Proof.
  intros U pp cc bb S W T.
  pose proof (wfc_slack _ _ _ _ _ W) as (H1 & H2 & H3).
  assert (W0 : Wf_cf U S) by exact (WfP_cf_weaken U pp cc bb 0 0 0 S W ltac:(lia) ltac:(lia) ltac:(lia)).
  pose proof (sec_arr_le_sec_chunks S (wfc_secondary _ _ _ _ _ W)) as A.
  rewrite len_sec_split in A.
  pose proof (qsec_bytes U S W0 T) as B.
  change (live_sec_blocks S) with (Z.of_nat (length (filter is_lsec (st_chunks S)))).
  rewrite QSEC_MAX_value. unfold kQuarantineMax, kQuarantineCacheMax in B. lia.
Qed.

(* The call premise ROOM_cf needs, from live secondaries alone. *)
Corollary ROOM_cf_count_of_live : forall U pp cc bb S, WfP_cf U pp cc bb S -> qtight S ->
  live_sec_blocks S + QSEC_MAX < cf_sec_live_max -> Z.of_nat (length (st_sec_arr S)) < cf_sec_live_max.
Proof. intros U pp cc bb S W T H. pose proof (sec_arr_bound_cf U pp cc bb S W T). lia. Qed.

End SECBOUND.
