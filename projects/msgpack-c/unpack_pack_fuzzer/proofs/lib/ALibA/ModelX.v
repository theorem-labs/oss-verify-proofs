(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import AcctCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Definition strip (m : Model) : Model := with_tid (Z_to_bv 64 1) (with_vm_backing [] [] m).

Definition MX (m : Model) (mat : list word) : Model := with_vm_backing (m_vm_lazy m) mat m.

Lemma same_but_mat_MX : forall m mat, same_but_mat m (MX m mat).
Proof. intros m mat. reflexivity. Qed.

Lemma same_but_mat_MX_eq : forall m m', same_but_mat m m' -> m' = MX m (m_vm_materialized m').
Proof. intros m m' H. exact H. Qed.

Lemma MX_mat : forall m, MX m (m_vm_materialized m) = m.
Proof. intros [fd [mp lz mt] io fs pr lm tm]. reflexivity. Qed.

Lemma MX_MX : forall m a b, MX (MX m a) b = MX m b.
Proof. intros. reflexivity. Qed.

Lemma m_vm_materialized_MX : forall m mat, m_vm_materialized (MX m mat) = mat.
Proof. reflexivity. Qed.
Lemma m_vm_lazy_MX : forall m mat, m_vm_lazy (MX m mat) = m_vm_lazy m.
Proof. reflexivity. Qed.
Lemma m_vmmaps_MX : forall m mat, m_vmmaps (MX m mat) = m_vmmaps m.
Proof. reflexivity. Qed.
Lemma m_fds_MX : forall m mat, m_fds (MX m mat) = m_fds m. Proof. reflexivity. Qed.
Lemma m_fs_MX : forall m mat, m_fs (MX m mat) = m_fs m. Proof. reflexivity. Qed.
Lemma m_tid_MX : forall m mat, m_tid (MX m mat) = m_tid m. Proof. reflexivity. Qed.
Lemma m_halted_MX : forall m mat, m_halted (MX m mat) = m_halted m. Proof. reflexivity. Qed.
Lemma m_stdin_MX : forall m mat, m_stdin (MX m mat) = m_stdin m. Proof. reflexivity. Qed.
Lemma nonlazy_bytes_MX : forall m mat, nonlazy_bytes (MX m mat) = nonlazy_bytes m. Proof. reflexivity. Qed.
Lemma strip_MX : forall m mat, strip (MX m mat) = strip m. Proof. reflexivity. Qed.

Lemma vm_backing_used_MX : forall m mat,
  vm_backing_used (MX m mat) = nonlazy_bytes m + Z.of_nat (length mat) * page_size.
Proof. reflexivity. Qed.

Lemma with_fds_MX : forall x m mat, with_fds x (MX m mat) = MX (with_fds x m) mat. Proof. reflexivity. Qed.
Lemma with_tid_MX : forall x m mat, with_tid x (MX m mat) = MX (with_tid x m) mat. Proof. reflexivity. Qed.
Lemma with_halted_MX : forall x m mat, with_halted x (MX m mat) = MX (with_halted x m) mat. Proof. reflexivity. Qed.
Lemma with_stdin_MX : forall x m mat, with_stdin x (MX m mat) = MX (with_stdin x m) mat. Proof. reflexivity. Qed.
Lemma with_vmmaps_MX : forall h m mat, with_vmmaps h (MX m mat) = MX (with_vmmaps h m) mat. Proof. reflexivity. Qed.
Lemma vm_add_lazy_MX : forall a n m mat, vm_add_lazy a n (MX m mat) = MX (vm_add_lazy a n m) mat. Proof. reflexivity. Qed.
Lemma vm_forget_range_MX : forall lo hi m mat,
  vm_forget_range lo hi (MX m mat) = MX (vm_forget_range lo hi m) (List.filter (page_outside_range lo hi) mat).
Proof. reflexivity. Qed.

Lemma strip_with_fds : forall x m, strip (with_fds x m) = with_fds x (strip m). Proof. reflexivity. Qed.
Lemma strip_with_tid : forall x m, strip (with_tid x m) = strip m. Proof. reflexivity. Qed.
Lemma strip_with_halted : forall x m, strip (with_halted x m) = with_halted x (strip m). Proof. reflexivity. Qed.
Lemma m_fds_strip : forall m, m_fds (strip m) = m_fds m. Proof. reflexivity. Qed.
Lemma m_fs_strip : forall m, m_fs (strip m) = m_fs m. Proof. reflexivity. Qed.
Lemma m_tid_strip : forall m, m_tid (strip m) = Some (Z_to_bv 64 1). Proof. reflexivity. Qed.
Lemma m_halted_strip : forall m, m_halted (strip m) = m_halted m. Proof. reflexivity. Qed.

