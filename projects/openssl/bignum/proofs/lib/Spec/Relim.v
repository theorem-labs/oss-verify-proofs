(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import PropExec MState ITree Nodes Decode.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition relim_h (L : Z) (h : VmMaps) : VmMaps :=
  mkVmMapsFull (vm_reserved h) (vm_maps h) (vm_noaccess h) (vm_start_brk h) (vm_brk h) L (vm_mmap_base h) (vm_init_sp h).
Definition relim (L : Z) (mo : Model) : Model := with_vmmaps (relim_h L (m_vmmaps mo)) mo.

Definition vm_clean (mo : Model) : Prop := m_vm_lazy mo = [] /\ m_vm_materialized mo = [].

Lemma minv_clean : forall mo, minv mo -> vm_clean mo.
Proof. intros mo H. split; [apply minv_lazy| apply minv_materialized]; exact H. Qed.

Lemma m_vmmaps_with_vmmaps : forall h mo, m_vmmaps (with_vmmaps h mo) = h. Proof. reflexivity. Qed.

Lemma live_bytes_app : forall l1 l2, live_bytes (l1 ++ l2) = live_bytes l1 + live_bytes l2.
Proof. induction l1 as [|[a n] l1 IH]; intros l2; cbn; [reflexivity| rewrite IH; lia]. Qed.

Lemma live_bytes_nonneg : forall l, 0 <= live_bytes l.
Proof. induction l as [|[a n] l IH]; cbn; [lia|]. pose proof (bv_unsigned_in_range 64 n). lia. Qed.

Lemma live_bytes_iv_subtract : forall a sz lo hi, lo <= hi -> live_bytes (iv_subtract a sz lo hi) <= bv_unsigned sz.
Proof.
  intros a sz lo hi Hlh. unfold iv_subtract.
  pose proof (bv_unsigned_in_range 64 a) as Ha. pose proof (bv_unsigned_in_range 64 sz) as Hs. unfold bv_modulus in *.
  destruct (Z.ltb_spec (bv_unsigned a) lo); destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)); cbn [app live_bytes];
    rewrite ?Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 64) with (2^64).
  - rewrite !Z.mod_small by lia. lia.
  - pose proof (Z.mod_le (Z.min (bv_unsigned sz) (lo - bv_unsigned a)) (2^64) ltac:(lia) ltac:(lia)). lia.
  - pose proof (Z.mod_le (bv_unsigned a + bv_unsigned sz - Z.max (bv_unsigned a) hi) (2^64) ltac:(lia) ltac:(lia)). lia.
  - lia.
Qed.

Lemma live_bytes_maps_subtract : forall maps lo hi, lo <= hi -> live_bytes (maps_subtract maps lo hi) <= live_bytes maps.
Proof.
  induction maps as [|[a sz] maps IH]; intros lo hi Hlh; cbn [maps_subtract live_bytes]; [lia|].
  rewrite live_bytes_app. pose proof (live_bytes_iv_subtract a sz lo hi Hlh). specialize (IH lo hi Hlh). lia.
Qed.

Lemma live_bytes_maps_subtract_all : forall cuts maps, live_bytes (maps_subtract_all maps cuts) <= live_bytes maps.
Proof.
  induction cuts as [|[a n] cuts IH]; intros maps; cbn [maps_subtract_all]; [lia|].
  etransitivity; [apply IH|]. apply live_bytes_maps_subtract. pose proof (bv_unsigned_in_range 64 n). lia.
Qed.

Lemma vm_backing_used_le_live' : forall mo, m_vm_materialized mo = [] ->
  vm_backing_used mo <= vm_live_bytes (m_vmmaps mo).
Proof.
  intros mo Hm. unfold vm_backing_used. rewrite Hm. cbn [length Z.of_nat]. rewrite Z.mul_0_l, Z.add_0_r.
  unfold vm_backed_maps, vm_live_bytes.
  etransitivity; [apply live_bytes_maps_subtract_all|]. apply live_bytes_maps_subtract_all.
Qed.

Lemma vm_backing_used_le_live : forall mo, vm_clean mo ->
  vm_backing_used mo <= vm_live_bytes (m_vmmaps mo).
Proof. intros mo [_ Hm]. apply vm_backing_used_le_live'. exact Hm. Qed.

Lemma vm_clean_with_vmmaps : forall h mo, vm_clean mo -> vm_clean (with_vmmaps h mo).
Proof. intros h mo [A B]. split; assumption. Qed.

Lemma page_round_up_Z_nonneg : forall x, 0 <= x -> 0 <= page_round_up_Z x.
Proof. intros x Hx. unfold page_round_up_Z. change page_size with 4096. apply Z.mul_nonneg_nonneg; [apply Z.div_pos; lia| lia]. Qed.

Lemma vm_clean_mprotect_model_next : forall m a n, vm_clean m -> vm_clean (mprotect_model_next m a n).
Proof. intros m a n Hc. unfold mprotect_model_next. apply vm_clean_with_vmmaps. exact Hc. Qed.

Fixpoint tlive {R} (B : Z) (t : itree node R) (mo : Model) : Prop :=
  match t with
  | Ret _ => True
  | Vis n k => forall rsp mo' evs, nstep n mo rsp mo' evs -> vm_live_bytes (m_vmmaps mo') <= B /\ tlive B (k rsp) mo'
  end.

Definition nstep_lim (B : Z) (n : node) (mo : Model) (rsp : resp) (mo' : Model) (evs : list event) : Prop :=
  nstep n mo rsp mo' evs /\ vm_live_bytes (m_vmmaps mo') <= B.

