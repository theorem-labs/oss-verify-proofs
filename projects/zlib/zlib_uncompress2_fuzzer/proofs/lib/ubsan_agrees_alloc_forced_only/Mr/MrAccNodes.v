(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs VmMapsDisjoint.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ITree Nodes Decode.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Mr Require Import MrNodes MrAccSpec MrAcc.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma u64z : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. exact VmMapsDisjoint.u64. Qed.

Lemma acc_mmap : forall addr len prot flags mo rsp mo' evs C U,
  nstep (NMmap addr len prot flags) mo rsp mo' evs ->
  0 <= len <= 2 ^ 30 - 4096 ->
  acc C U mo -> acc (C + 2) (U + len + 4096) mo'.
Proof.
  intros addr len prot flags mo rsp mo' evs C U H Hlen Hacc.
  apply nstep_mmap_iff in H as [[_ H] _].
  pose proof (MrAccSpec.accs_mmap _ _ _ _ _ _ _ _ _ _ C U H) as K.
  rewrite u64z in K by lia. replace (U + len + 4096) with (U + (len + 4096)) by lia.
  apply K; [lia|exact Hacc].
Qed.

Lemma acc_munmap : forall addr len mo rsp mo' evs C U,
  nstep (NMunmap addr len) mo rsp mo' evs -> acc C U mo -> acc (C + 2) U mo'.
Proof. intros addr len mo rsp mo' evs C U H Hacc. apply nstep_munmap_iff in H as [H _]. exact (MrAccSpec.accs_munmap _ _ _ _ _ _ C U H Hacc). Qed.

(* a SAFE munmap (nsafe: an exact entry or a free range) costs no entry. *)
Lemma acc_munmap_safe : forall addr len mo rsp mo' evs C U,
  nsafe (NMunmap addr len) mo ->
  nstep (NMunmap addr len) mo rsp mo' evs -> acc C U mo -> acc C U mo'.
Proof.
  intros addr len mo rsp mo' evs C U Hs H Hacc. apply nstep_munmap_iff in H as [H _].  (* FO's no-spurious conjunct *)
  exact (MrAccSpec.accs_munmap_safe _ _ _ _ _ _ C U Hs H Hacc).
Qed.

Lemma acc_mprotect : forall addr len prot mo rsp mo' evs C U,
  nstep (NMprotect addr len prot) mo rsp mo' evs -> acc C U mo -> acc C U mo'.
Proof. intros addr len prot mo rsp mo' evs C U H Hacc. apply nstep_mprotect_iff in H as [H _]. exact (MrAccSpec.accs_mprotect _ _ _ _ _ _ _ C U H Hacc). Qed.

Lemma acc_brk : forall req mo rsp mo' evs C U,
  nstep (NBrk req) mo rsp mo' evs ->
  0 <= req < 2 ^ 64 ->
  (req = 0 \/ bv_unsigned (vm_brk (m_vmmaps mo)) <= req) ->
  req - bv_unsigned (vm_brk (m_vmmaps mo)) <= 2 ^ 30 - 4096 ->
  acc C U mo ->
  acc (C + 1) (U + (Z.max 0 (req - bv_unsigned (vm_brk (m_vmmaps mo))) + 4096)) mo'.
Proof.
  intros req mo rsp mo' evs C U H Hr Hq Hsz Hacc. apply nstep_brk_iff in H as [H _].
  pose proof (MrAccSpec.accs_brk _ _ _ _ _ C U H) as K. rewrite u64z in K by lia.
  apply K; [exact Hq|exact Hsz|exact Hacc].
Qed.

Lemma lim_mm : forall n mo rsp mo' evs,
  MrNodes.mm_node n -> nstep n mo rsp mo' evs -> vm_limit (m_vmmaps mo') = vm_limit (m_vmmaps mo).
Proof.
  intros n mo rsp mo' evs Hn H. destruct n; try contradiction.
  - apply nstep_brk_iff in H as [H _]. exact (MrAccSpec.lim_brk _ _ _ _ _ H).
  - apply nstep_mmap_iff in H as [[_ H] _]. exact (MrAccSpec.lim_mmap _ _ _ _ _ _ _ _ _ _ H).
  - apply nstep_munmap_iff in H as [H _]. exact (MrAccSpec.lim_munmap _ _ _ _ _ _ H).
  - apply nstep_mprotect_iff in H as [H _]. exact (MrAccSpec.lim_mprotect _ _ _ _ _ _ _ H).
Qed.

Lemma brk0_query : forall mo rsp mo' evs r,
  nstep (NBrk 0) mo rsp mo' evs -> Decode.dec_brk0 rsp = Some r ->
  r = bv_unsigned (vm_brk (m_vmmaps mo)) /\ m_vmmaps mo' = m_vmmaps mo /\ m_vm_materialized mo' = m_vm_materialized mo
  /\ m_vm_lazy mo' = m_vm_lazy mo.
Proof.
  intros mo rsp mo' evs r H Hd. apply nstep_brk_iff in H as [H _].
  destruct (MrAccSpec.brk0_query_chk _ _ _ _ H) as (Hret & Hv & Hm & Hl).
  split; [|split; [exact Hv|split; [exact Hm|exact Hl]]].
  destruct rsp as [ret ws zs us cs ci]. unfold Decode.dec_brk0 in Hd. cbn [eff_ret] in Hret.
  destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate].
  injection Hd as <-. rewrite Hret. reflexivity.
Qed.

Lemma acc_brk0 : forall mo rsp mo' evs C U,
  nstep (NBrk 0) mo rsp mo' evs -> acc C U mo -> acc C U mo'.
Proof.
  intros mo rsp mo' evs C U H Hacc. apply nstep_brk_iff in H as [H _].
  destruct (MrAccSpec.brk0_query_chk _ _ _ _ H) as (_ & Hv & Hm & _).
  exact (acc_same_vm C U mo mo' Hv Hm Hacc).
Qed.
