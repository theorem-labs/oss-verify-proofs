(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import PropExec MState Exec NodesM.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require ShapeAlg.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache.

Section WithSegs.
Variable segs : list Segment.

Lemma msteps_C2S : forall ms ms', Exec.msteps segs ms ms' -> ShapeAlg.msteps segs ms ms'.
Proof.
  intros ms ms' H. induction H as [ms | ms ms1 ms2 [Hsvc Hstep] _ IH].
  - apply ShapeAlg.mst_refl.
  - eapply ShapeAlg.mst_step; [exact Hsvc | exact Hstep | exact IH].
Qed.

Lemma msteps_S2C : forall ms ms', ShapeAlg.msteps segs ms ms' -> Exec.msteps segs ms ms'.
Proof.
  intros ms ms' H. induction H as [ms | ms ms1 ms2 Hsvc Hstep _ IH].
  - apply msteps_refl.
  - eapply msteps_cons; [split; [exact Hsvc | exact Hstep] | exact IH].
Qed.

Lemma evt_realizes : forall (Q : machine_state -> Prop) ms mo (K : ShapeAlg.TSet),
  evt segs Q ms ->
  m_halted mo = None -> m_vm_lazy mo = [] ->
  (forall ms', Q ms' -> ShapeAlg.realizes segs (mkCfg ms' mo) K) ->
  ShapeAlg.realizes segs (mkCfg ms mo) K.
Proof.
  intros Q ms mo K (ms' & Hrun & HQ) Hh Hlz HK.
  eapply ShapeAlg.rz_msteps; [exact Hh | exact Hlz | apply msteps_C2S; exact Hrun | apply HK; exact HQ].
Qed.

End WithSegs.

Definition mo_ok (mo : Model) : Prop :=
  m_halted mo = None /\ m_vm_lazy mo = [] /\ m_vm_materialized mo = [].

Lemma mo_ok_halted mo : mo_ok mo -> m_halted mo = None.         Proof. intros (H & _ & _); exact H. Qed.
Lemma mo_ok_lazy mo : mo_ok mo -> m_vm_lazy mo = [].            Proof. intros (_ & H & _); exact H. Qed.
Lemma mo_ok_materialized mo : mo_ok mo -> m_vm_materialized mo = []. Proof. intros (_ & _ & H); exact H. Qed.
Lemma mo_ok_minv mo : mo_ok mo -> minv mo. Proof. exact (mo_ok_lazy mo). Qed.

Definition vm_agree : Model -> Model -> Prop := vm_only.

Lemma vm_agree_refl : forall mo, vm_agree mo mo.
Proof. exact vm_only_refl. Qed.
Lemma vm_agree_trans : forall a b c, vm_agree a b -> vm_agree b c -> vm_agree a c.
Proof. exact vm_only_trans. Qed.

Lemma vm_agree_mo_ok : forall mo mo', vm_agree mo mo' -> mo_ok mo -> mo_ok mo'.
Proof.
  intros mo mo' H (Hh & Hl & Hm). split; [| split].
  - destruct (vm_only_fields _ _ H) as (_ & _ & E & _). rewrite E. exact Hh.
  - exact (vm_only_lazy _ _ H Hl).
  - exact (vm_only_materialized _ _ H Hm).
Qed.

Lemma vm_agree_fds   : forall mo mo', vm_agree mo mo' -> m_fds mo' = m_fds mo.
Proof. intros mo mo' H. rewrite (vm_only_but_vm _ _ H). reflexivity. Qed.
Lemma vm_agree_pipes : forall mo mo', vm_agree mo mo' -> m_pipes mo' = m_pipes mo.
Proof. intros mo mo' H. rewrite (vm_only_but_vm _ _ H). reflexivity. Qed.
Lemma vm_agree_fs    : forall mo mo', vm_agree mo mo' -> m_fs mo' = m_fs mo.
Proof. intros mo mo' H. rewrite (vm_only_but_vm _ _ H). reflexivity. Qed.
Lemma vm_agree_halted : forall mo mo', vm_agree mo mo' -> m_halted mo' = m_halted mo.
Proof. intros mo mo' H. rewrite (vm_only_but_vm _ _ H). reflexivity. Qed.
Lemma vm_agree_tid   : forall mo mo', vm_agree mo mo' -> m_tid mo' = m_tid mo.
Proof. intros mo mo' H. rewrite (vm_only_but_vm _ _ H). reflexivity. Qed.
Lemma vm_agree_stdin : forall mo mo', vm_agree mo mo' -> m_stdin mo' = m_stdin mo.
Proof. intros mo mo' H. rewrite (vm_only_but_vm _ _ H). reflexivity. Qed.
Lemma vm_agree_fd    : forall mo mo', vm_agree mo mo' -> m_fd mo' = m_fd mo.
Proof. intros mo mo' H. rewrite (vm_only_but_vm _ _ H). reflexivity. Qed.
Lemma vm_agree_io    : forall mo mo', vm_agree mo mo' -> m_io mo' = m_io mo.
Proof. intros mo mo' H. rewrite (vm_only_but_vm _ _ H). reflexivity. Qed.
Lemma vm_agree_fsys  : forall mo mo', vm_agree mo mo' -> m_fsys mo' = m_fsys mo.
Proof. intros mo mo' H. rewrite (vm_only_but_vm _ _ H). reflexivity. Qed.
Lemma vm_agree_proc  : forall mo mo', vm_agree mo mo' -> m_proc mo' = m_proc mo.
Proof. intros mo mo' H. rewrite (vm_only_but_vm _ _ H). reflexivity. Qed.
Lemma vm_agree_lim   : forall mo mo', vm_agree mo mo' -> m_lim mo' = m_lim mo.
Proof. intros mo mo' H. rewrite (vm_only_but_vm _ _ H). reflexivity. Qed.
Lemma vm_agree_time  : forall mo mo', vm_agree mo mo' -> m_time mo' = m_time mo.
Proof. intros mo mo' H. rewrite (vm_only_but_vm _ _ H). reflexivity. Qed.
Lemma vm_agree_resv  : forall mo mo', vm_agree mo mo' -> vm_reserved (m_vmmaps mo') = vm_reserved (m_vmmaps mo).
Proof. intros mo mo' H. destruct (vm_only_consts _ _ H) as (E & _). exact E. Qed.
Lemma vm_agree_start : forall mo mo', vm_agree mo mo' -> vm_start_brk (m_vmmaps mo') = vm_start_brk (m_vmmaps mo).
Proof. intros mo mo' H. destruct (vm_only_consts _ _ H) as (_ & E & _). exact E. Qed.
Lemma vm_agree_limit : forall mo mo', vm_agree mo mo' -> vm_limit (m_vmmaps mo') = vm_limit (m_vmmaps mo).
Proof. intros mo mo' H. destruct (vm_only_consts _ _ H) as (_ & _ & E & _). exact E. Qed.
Lemma vm_agree_mbase : forall mo mo', vm_agree mo mo' -> vm_mmap_base (m_vmmaps mo') = vm_mmap_base (m_vmmaps mo).
Proof. intros mo mo' H. destruct (vm_only_consts _ _ H) as (_ & _ & _ & E & _). exact E. Qed.
Lemma vm_agree_init_sp : forall mo mo', vm_agree mo mo' -> vm_init_sp (m_vmmaps mo') = vm_init_sp (m_vmmaps mo).
Proof. exact vm_only_init_sp. Qed.
Lemma vm_agree_alloc_top : forall mo mo', vm_agree mo mo' -> alloc_top (m_vmmaps mo') = alloc_top (m_vmmaps mo).
Proof. exact vm_only_alloc_top. Qed.
