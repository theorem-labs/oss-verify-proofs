(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.Lib Require Import PropExec MState ITree Nodes Decode.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.


Ltac dm mo := destruct mo as [? [? ? ?] ? ? ? ? ?].



Lemma live_bytes_app : forall l1 l2, live_bytes (l1 ++ l2) = live_bytes l1 + live_bytes l2.
Proof. induction l1 as [|[a n] l1 IH]; intros l2; cbn; [reflexivity| rewrite IH; lia]. Qed.

Lemma live_bytes_nonneg : forall l, 0 <= live_bytes l.
Proof. induction l as [|[a n] l IH]; cbn; [lia|]. pose proof (bv_unsigned_in_range 64 n). lia. Qed.

Lemma live_bytes_iv_subtract : forall a sz lo hi, lo <= hi ->
  live_bytes (iv_subtract a sz lo hi) <= bv_unsigned sz.
Proof.
  intros a sz lo hi Hlh. unfold iv_subtract.
  pose proof (bv_unsigned_in_range 64 a). pose proof (bv_unsigned_in_range 64 sz). unfold bv_modulus in *.
  destruct (Z.ltb_spec (bv_unsigned a) lo); destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)); cbn.
  - rewrite (unsigned_lit (Z.min (bv_unsigned sz) (lo - bv_unsigned a))) by lia.
    rewrite (unsigned_lit (bv_unsigned a + bv_unsigned sz - Z.max (bv_unsigned a) hi)) by lia. lia.
  - rewrite (unsigned_lit (Z.min (bv_unsigned sz) (lo - bv_unsigned a))) by lia. lia.
  - rewrite (unsigned_lit (bv_unsigned a + bv_unsigned sz - Z.max (bv_unsigned a) hi)) by lia. lia.
  - lia.
Qed.

Lemma live_bytes_maps_subtract : forall maps lo hi, lo <= hi ->
  live_bytes (maps_subtract maps lo hi) <= live_bytes maps.
Proof.
  induction maps as [|[a sz] maps IH]; intros lo hi Hlh; cbn; [lia|].
  rewrite live_bytes_app. pose proof (live_bytes_iv_subtract a sz lo hi Hlh). specialize (IH lo hi Hlh). lia.
Qed.

Lemma live_bytes_maps_subtract_all : forall cuts maps,
  live_bytes (maps_subtract_all maps cuts) <= live_bytes maps.
Proof.
  induction cuts as [|[a n] cuts IH]; intros maps; cbn; [lia|].
  etransitivity; [apply IH|]. apply live_bytes_maps_subtract. pose proof (bv_unsigned_in_range 64 n). lia.
Qed.

Lemma backing_le_live : forall mo, m_vm_lazy mo = [] -> m_vm_materialized mo = [] ->
  vm_backing_used mo <= vm_live_bytes (m_vmmaps mo).
Proof.
  intros mo Hl Hm. unfold vm_backing_used, vm_backed_maps, vm_live_bytes. rewrite Hl, Hm. cbn [maps_subtract_all length Z.of_nat].
  rewrite Z.mul_0_l, Z.add_0_r. apply live_bytes_maps_subtract_all.
Qed.












Lemma with_mmap_backing_plain : forall flags a n m, mmap_noreserve_b flags = false -> with_mmap_backing flags a n m = m.
Proof. intros flags a n m H. unfold with_mmap_backing. rewrite H. reflexivity. Qed.
Lemma with_mmap_replacement_plain : forall flags a n m, mmap_noreserve_b flags = false ->
  with_mmap_replacement flags a n m = vm_forget_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n) m.
Proof. intros flags a n m H. unfold with_mmap_replacement. rewrite with_mmap_backing_plain by exact H. reflexivity. Qed.
Lemma mmap_noreserve_backed_ok_plain : forall flags m nZ, mmap_noreserve_b flags = false ->
  mmap_noreserve_backed_ok flags m nZ = (vm_backing_used m + nZ <=? vm_limit (m_vmmaps m)).
Proof. intros flags m nZ H. unfold mmap_noreserve_backed_ok. rewrite H. reflexivity. Qed.

Lemma m_vmmaps_vm_forget_range : forall lo hi m, m_vmmaps (vm_forget_range lo hi m) = m_vmmaps m.
Proof. intros lo hi m; dm m; reflexivity. Qed.
Lemma m_vm_lazy_with_vmmaps : forall h m, m_vm_lazy (with_vmmaps h m) = m_vm_lazy m. Proof. intros h m; dm m; reflexivity. Qed.
Lemma m_vm_materialized_with_vmmaps : forall h m, m_vm_materialized (with_vmmaps h m) = m_vm_materialized m. Proof. intros h m; dm m; reflexivity. Qed.




