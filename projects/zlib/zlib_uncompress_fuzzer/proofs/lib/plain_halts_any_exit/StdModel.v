(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit Require Import ModelAmb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition fds_std : list (word * FdEntry) :=
  [(Z_to_bv 64 0, FdChannel (Z_to_bv 64 0)); (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1));
   (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2))].

Record std_model (VM : VmMaps) (model : Model) : Prop := STD_MODEL {
  stdm_fds  : m_fds model = fds_std;
  stdm_vm   : m_vmmaps model = VM;
  stdm_halt : m_halted model = None;
  stdm_lazy : m_vm_lazy model = [];
  stdm_mat  : m_vm_materialized model = []
}.

Lemma std_model_mk : forall VM stdin0 fs0 tid rlim,
  std_model VM (mkModelA fds_std VM stdin0 fs0 None tid rlim).
Proof. intros. constructor; reflexivity. Qed.
