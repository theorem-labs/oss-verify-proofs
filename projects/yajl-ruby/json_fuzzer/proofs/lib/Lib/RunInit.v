(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (ms0 from the launch's entry block, mo0 with the vDSO draw, the run over run_segments, the channel-reader premise of mo0_minv, valid_entry_launch, and the old stack-span and run_of_tree lemmas dropped). *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Vdso Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState Frame Exec ITree RunCeiling Nodes RegsEquiv FP InitMem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition prog_tree (R : Type) : Type := ProcInput -> ExecEntry -> itree node R.

(* [comment removed for export] *)
Definition ms0 (segs : list Segment) (pc : N) (ph : PhdrInfo)
    (en : ExecEntry) (inp : ProcInput) : machine_state :=
  init_ms segs pc ph (en_sp en) (en_mmap_base en) (en_draw en) inp.

Lemma ms0_eq : forall segs pc ph en inp,
  ms0 segs pc ph en inp =
  MS (mkR_init (en_sp en)) bvmap_empty (Z_to_bv 64 (Z.of_N pc)) (Z_to_bv 32 0) None
     (wrap_mem inp (en_mmap_base en) ph (Z_to_bv 64 (Z.of_N pc)) (en_sp en) (en_draw en)) (seg_rom segs).
Proof. reflexivity. Qed.

(* LPS 08b1429: the initial model carries the launch's vDSO draw. *)
Definition mo0 (segs : list Segment) (lim : Z) (en : ExecEntry) (inp : ProcInput) : Model :=
  with_vdso (Vdso.vdso_run_init (ed_vdso (en_draw en)))
    (init_model (segments_reserved segs) (en_brk en) (en_mmap_base en) (en_sp en) lim inp).

Lemma init_config_eq : forall segs pc ph lim en inp,
  init_config segs pc ph (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en) lim inp
  = mkCfg (init_machine_state segs pc ph (en_sp en) (en_mmap_base en) (en_draw en) inp) (mo0 segs lim en inp).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma mo0_not_halted : forall segs lim en inp, m_halted (mo0 segs lim en inp) = None.
Proof. reflexivity. Qed.

Lemma mo0_vmmaps : forall segs lim en inp,
  m_vmmaps (mo0 segs lim en inp)
  = m_vmmaps (init_model (segments_reserved segs) (en_brk en) (en_mmap_base en) (en_sp en) lim inp).
Proof. reflexivity. Qed.

Lemma mo0_alloc_top : forall segs lim en inp,
  alloc_top (m_vmmaps (mo0 segs lim en inp)) = (bv_unsigned (en_sp en) - stack_max_size)%Z.
Proof. reflexivity. Qed.

Lemma mo0_fds : forall segs lim en inp,
  m_fds (mo0 segs lim en inp) =
  [ (Z_to_bv 64 0, FdChannel (Z_to_bv 64 0)); (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1)); (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2)) ].
Proof. reflexivity. Qed.

Lemma mo0_fs : forall segs lim en inp, m_fs (mo0 segs lim en inp) = in_fs inp.
Proof. reflexivity. Qed.

Lemma mo0_tid : forall segs lim en inp, m_tid (mo0 segs lim en inp) = None.
Proof. reflexivity. Qed.

Lemma mo0_killed : forall segs lim en inp, m_killed (mo0 segs lim en inp) = None.
Proof. reflexivity. Qed.

Lemma mo0_lazy : forall segs lim en inp, m_vm_lazy (mo0 segs lim en inp) = [].
Proof. reflexivity. Qed.

Lemma mo0_backing_used : forall segs lim en inp, vm_backing_used (mo0 segs lim en inp) = 0%Z.
Proof.
  intros. unfold mo0.
  first [ reflexivity
        | exact (vm_backing_used_init_model (segments_reserved segs) (en_brk en) (en_mmap_base en) (en_sp en) lim inp) ].
Qed.

Lemma ms0_svc : forall segs pc ph en inp, ms_svc_pending (ms0 segs pc ph en inp) = None.
Proof. reflexivity. Qed.

Remark frm0_init : frm0 (Z_to_bv 32 0).
Proof. reflexivity. Qed.

Lemma ms0_frm0 : forall segs pc ph en inp, frm0 (ms_fcsr (ms0 segs pc ph en inp)).
Proof. intros. exact frm0_init. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma valid_entry_unpack : forall segs pc ph en inp,
  valid_entry (mkImage segs pc ph) en inp -> valid_input inp ->
  valid_sp (en_sp en) /\ valid_brk segs (en_brk en) /\ valid_mmap_base (en_mmap_base en)
  /\ entry_stack_fits (en_sp en) (in_argv inp) (in_envp inp).
Proof.
  intros segs pc ph [sp brk mb d] inp H HI.
  pose proof (valid_input_va_size _ HI) as Hv.
  unfold valid_entry in H. rewrite Hv in H. destruct H as (A & B & C & D & _).
  exact (conj A (conj B (conj C D))).
Qed.

(* LPS 08b1429: the launch half of valid_entry (stack top, sp and mmap base for the input's strings). *)
Lemma valid_entry_launch : forall segs pc ph en inp,
  valid_entry (mkImage segs pc ph) en inp -> valid_input inp ->
  entry_launch_ok_va Sv48 en inp.
Proof.
  intros segs pc ph [sp brk mb d] inp H HI.
  pose proof (valid_input_va_size _ HI) as Hv.
  unfold valid_entry in H. rewrite Hv in H. destruct H as (_ & _ & _ & _ & E). exact E.
Qed.

Lemma valid_input_unpack : forall inp,
  valid_input inp -> valid_argv (in_argv inp) /\ valid_envp (in_envp inp) /\ valid_fs (in_fs inp) /\ valid_creds inp.
Proof. intros inp (A & B & C & _ & _ & D & _). exact (conj A (conj B (conj C D))). Qed.

Lemma valid_input_hwcap : forall inp, valid_input inp -> valid_hwcap (in_hwcap inp).
Proof. intros inp (_ & _ & _ & _ & _ & _ & _ & _ & G & _). exact G. Qed.

Lemma valid_input_not_abort : forall inp, valid_input inp -> in_abort_terminal inp = false.
Proof. intros inp (_ & _ & _ & _ & _ & _ & _ & _ & _ & G & _). exact G. Qed.



(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma run_eq : forall segs pc ph lim en inp,
  run (mkImage segs pc ph) lim en inp =
  let vsegs := run_segments segs inp (en_sp en) (en_mmap_base en) in
  let c0 := mkCfg (init_machine_state vsegs pc ph (en_sp en) (en_mmap_base en) (en_draw en) inp) (mo0 vsegs lim en inp) in
  {| bh_traces := obs_trace vsegs c0;
     bh_errors := reaches_error vsegs c0;
     bh_all_errors := all_traces_error vsegs c0;
     bh_unmodeled := reaches_unmodeled vsegs c0 |}.
Proof. intros segs pc ph lim [sp brk mb rnd] inp. reflexivity. Qed.

(* [comment removed for export] *)
Lemma run_scfg_eq : forall cfg segs pc ph lim en inp,
  run_scfg cfg (mkImage segs pc ph) lim en inp =
  let vsegs := run_segments segs inp (en_sp en) (en_mmap_base en) in
  let c0 := mkCfg (init_machine_state vsegs pc ph (en_sp en) (en_mmap_base en) (en_draw en) inp) (mo0 vsegs lim en inp) in
  {| bh_traces := obs_trace_cfg vsegs cfg c0;
     bh_errors := reaches_error_cfg vsegs cfg c0;
     bh_all_errors := all_traces_error_cfg vsegs cfg c0;
     bh_unmodeled := reaches_unmodeled_cfg vsegs cfg c0 |}.
Proof. intros cfg segs pc ph lim [sp brk mb rnd] inp. reflexivity. Qed.

Lemma init_config_ms0 : forall segs pc ph lim en inp,
  init_config segs pc ph (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en) lim inp
  = mkCfg (init_machine_state segs pc ph (en_sp en) (en_mmap_base en) (en_draw en) inp) (mo0 segs lim en inp)
  /\ ms_eqv (init_machine_state segs pc ph (en_sp en) (en_mmap_base en) (en_draw en) inp) (ms0 segs pc ph en inp).
Proof. intros. split; [reflexivity | apply init_machine_state_eqv]. Qed.

(* [comment removed for export] *)
Definition tree_traces {R : Type} (t : itree node R) (mo : Model) : list event -> Prop :=
  fun tr => exists full, ttrace nstep nexit t mo full /\ is_prefix tr full.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section RC__.
Context {RC__ : RunCeiling}.

Lemma mo0_minv : forall segs lim en inp,
  bv_unsigned (en_sp en) = rc_sp -> valid_sp (en_sp en) -> in_channel_reader inp = true -> minv (mo0 segs lim en inp).
Proof.
  intros segs lim en inp Hrc (L & H & _) Hch. apply minv_init; [exact Hrc| rewrite <- Hrc; split; assumption | exact Hch].
Qed.

Lemma mo0_minv_entry : forall segs pc ph lim en inp,
  bv_unsigned (en_sp en) = rc_sp -> valid_entry (mkImage segs pc ph) en inp -> valid_input inp -> minv (mo0 segs lim en inp).
Proof.
  intros segs pc ph lim en inp Hrc HE HI. destruct (valid_entry_unpack _ _ _ _ _ HE HI) as (V & _).
  apply mo0_minv; [exact Hrc | exact V | exact (valid_input_channel_reader _ HI)].
Qed.

End RC__.
