(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the run's vDSO pair; the launch's input, mmap base and entry draw). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.pupnp.FuzzHttp.images Require Plain.
Import ListNotations.
Open Scope Z_scope.

Definition segsP0 : list Segment := Plain.M.loaded_segments.
Definition imgP0 : Image := mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs.

(* LPS 727298f3: the plain run's start model ([Run.init_config]) carries the entry's vDSO draw. *)
Definition moP0 (brk mb sp : word) (inp : ProcInput) (rnd : EntryDraw) : Model :=
  with_vdso (Vdso.vdso_run_init (ed_vdso rnd)) (init_model (segments_reserved segsP0) brk mb sp source_alloc_limit inp).

(* [with_vdso] rebuilds only the vDSO run field: the accessors the shape proofs read are init_model's. *)
Lemma m_tid_moP0 : forall brk mb sp inp rnd,
  m_tid (moP0 brk mb sp inp rnd) = m_tid (init_model (segments_reserved segsP0) brk mb sp source_alloc_limit inp).
Proof. reflexivity. Qed.
Lemma m_halted_moP0 : forall brk mb sp inp rnd,
  m_halted (moP0 brk mb sp inp rnd) = m_halted (init_model (segments_reserved segsP0) brk mb sp source_alloc_limit inp).
Proof. reflexivity. Qed.
Lemma m_fds_moP0 : forall brk mb sp inp rnd,
  m_fds (moP0 brk mb sp inp rnd) = m_fds (init_model (segments_reserved segsP0) brk mb sp source_alloc_limit inp).
Proof. reflexivity. Qed.
Lemma m_fs_moP0 : forall brk mb sp inp rnd,
  m_fs (moP0 brk mb sp inp rnd) = m_fs (init_model (segments_reserved segsP0) brk mb sp source_alloc_limit inp).
Proof. reflexivity. Qed.
