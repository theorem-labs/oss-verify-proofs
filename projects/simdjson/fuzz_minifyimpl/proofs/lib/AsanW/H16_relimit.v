(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import PropExec MState.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import AcctCore ModelX.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AS Require Import MainExport MainFactsAsan MainEntry.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition relimit_maps (L : Z) (h : VmMaps) : VmMaps :=
  mkVmMapsFull (vm_reserved h) (vm_maps h) (vm_noaccess h) (vm_start_brk h) (vm_brk h) L (vm_mmap_base h) (vm_init_sp h).
Definition relimit (L : Z) (mo : Model) : Model := with_vmmaps (relimit_maps L (m_vmmaps mo)) mo.

Lemma m_vmmaps_relimit : forall L mo, m_vmmaps (relimit L mo) = relimit_maps L (m_vmmaps mo).
Proof. intros. unfold relimit. apply m_vmmaps_with_vmmaps. Qed.
Lemma m_vm_lazy_relimit : forall L mo, m_vm_lazy (relimit L mo) = m_vm_lazy mo. Proof. reflexivity. Qed.
Lemma m_vm_materialized_relimit : forall L mo, m_vm_materialized (relimit L mo) = m_vm_materialized mo. Proof. reflexivity. Qed.
Lemma m_fds_relimit : forall L mo, m_fds (relimit L mo) = m_fds mo. Proof. reflexivity. Qed.
Lemma m_fs_relimit : forall L mo, m_fs (relimit L mo) = m_fs mo. Proof. reflexivity. Qed.
Lemma m_halted_relimit : forall L mo, m_halted (relimit L mo) = m_halted mo. Proof. reflexivity. Qed.
Lemma m_tid_relimit : forall L mo, m_tid (relimit L mo) = m_tid mo. Proof. reflexivity. Qed.
Lemma vm_limit_relimit : forall L mo, vm_limit (m_vmmaps (relimit L mo)) = L. Proof. intros. rewrite m_vmmaps_relimit. reflexivity. Qed.
Lemma nonlazy_bytes_relimit : forall L mo, nonlazy_bytes (relimit L mo) = nonlazy_bytes mo.
Proof. intros. unfold nonlazy_bytes. rewrite m_vmmaps_relimit, m_vm_lazy_relimit. reflexivity. Qed.
Lemma MX_relimit : forall L mo mat, MX (relimit L mo) mat = relimit L (MX mo mat). Proof. reflexivity. Qed.
Lemma strip_relimit_vm : forall L mo, m_vmmaps (strip (relimit L mo)) = relimit_maps L (m_vmmaps mo). Proof. intros. apply m_vmmaps_relimit. Qed.

Lemma amodelL_relimit : forall L L' V sp fs mo, amodelL L V sp fs mo -> L <= L' -> amodelL L' V sp fs (relimit L' mo).
Proof.
  intros L L' V sp fs mo HM HLE.
  destruct HM as [Hh Hfds Hfs Hres Hlim Hbrk Hsbrk Htop Husp Hmaps Hkinds Hsep Hbnd Hlzb Hnawf Hnasub Hnapos Htot Hnl Hab Hbud Halw Hnd Hmat].
  constructor; rewrite ?m_vmmaps_relimit, ?m_vm_lazy_relimit, ?m_vm_materialized_relimit, ?nonlazy_bytes_relimit; cbn [relimit_maps vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit vm_mmap_base vm_init_sp];
    try assumption; try reflexivity.     (* [comment removed for export] *)
  lia.   (* [comment removed for export] *)
Qed.
