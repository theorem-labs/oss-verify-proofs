(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
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
  init_ms segs pc ph (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en).

Lemma ms0_eq : forall segs pc ph en inp,
  ms0 segs pc ph en inp =
  MS (mkR_init (en_sp en)) bvmap_empty (Z_to_bv 64 (Z.of_N pc)) (Z_to_bv 32 0) None
     (wrap_mem ph (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en)) (seg_rom segs).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition mo0 (segs : list Segment) (lim : Z) (en : ExecEntry) (inp : ProcInput) : Model :=
  init_model (segments_reserved segs) (en_brk en) (en_mmap_base en) (en_sp en) lim inp.

Lemma init_config_eq : forall segs pc ph lim en inp,
  init_config segs pc ph (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en) lim inp
  = mkCfg (init_machine_state segs pc ph (en_sp en) (en_draw en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) (mo0 segs lim en inp).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma mo0_not_halted : forall segs lim en inp, m_halted (mo0 segs lim en inp) = None.
Proof. reflexivity. Qed.

Lemma mo0_vmmaps : forall segs lim en inp,
  m_vmmaps (mo0 segs lim en inp) = mkVmMapsFull (segments_reserved segs) [] [] (en_brk en) (en_brk en) lim (en_mmap_base en) (en_sp en).
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
Proof. intros. apply vm_backing_used_init_model. Qed.

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
  rewrite (valid_entry_sv48 _ _ _ Hv) in H. exact H.
Qed.

Lemma valid_input_unpack : forall inp,
  valid_input inp -> valid_argv (in_argv inp) /\ valid_envp (in_envp inp) /\ valid_fs (in_fs inp) /\ valid_creds inp.
Proof. intros inp (A & B & C & _ & D & _). exact (conj A (conj B (conj C D))). Qed.

Lemma valid_input_hwcap : forall inp, valid_input inp -> valid_hwcap (in_hwcap inp).
Proof. intros inp (_ & _ & _ & _ & _ & _ & _ & G & _). exact G. Qed.

Lemma valid_input_not_abort : forall inp, valid_input inp -> in_abort_terminal inp = false.
Proof. intros inp (_ & _ & _ & _ & _ & _ & _ & _ & G & _). exact G. Qed.

(* [comment removed for export] *)
Lemma build_stack_bytes_le_span : forall ph sp argv envp uid hw rnd,
  (Z.of_nat (length (build_stack_bytes ph sp argv envp uid hw rnd)) <= entry_stack_span argv envp)%Z.
Proof. exact build_stack_bytes_within_span. Qed.

Lemma entry_facts : forall segs pc ph en inp,
  valid_entry (mkImage segs pc ph) en inp -> valid_input inp ->
  let sp := en_sp en in
  let img := build_stack_bytes ph sp (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en) in
  (stack_max_size <= bv_unsigned sp)%Z
  /\ (sp_window_lo <= bv_unsigned sp)%Z
  /\ (bv_unsigned sp + Z.of_nat (length img) <= sp_window_hi)%Z
  /\ (bv_unsigned sp + Z.of_nat (length img) <= 2^64)%Z
  /\ (bv_unsigned sp mod 16 = 0)%Z
  /\ (Z.of_nat (length img) <= entry_stack_span_max)%Z.
Proof.
  intros segs pc ph en inp HE HI. cbv zeta.
  destruct (valid_entry_unpack _ _ _ _ _ HE HI) as ((L & H & M) & _ & _ & F).
  destruct (valid_input_unpack _ HI) as (VA & VE & _ & _).
  pose proof (build_stack_bytes_le_span ph (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en)).
  pose proof (entry_stack_span_bound (in_argv inp) (in_envp inp) VA VE).
  unfold entry_stack_fits, sp_window_lo, sp_window_hi, stack_max_size in *. lia.
Qed.

(* [comment removed for export] *)
Lemma entry_image_facts : forall segs pc ph en inp,
  valid_entry (mkImage segs pc ph) en inp -> valid_input inp ->
  let sp := en_sp en in
  let img := build_stack_bytes ph sp (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en) in
  let eimg := entry_stack_image ph sp (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en) in
  (length img <= length eimg)%nat
  /\ (bv_unsigned sp + Z.of_nat (length eimg) = entry_page_top sp img)%Z
  /\ (bv_unsigned sp + Z.of_nat (length eimg) <= sp_window_hi)%Z
  /\ (bv_unsigned sp + Z.of_nat (length eimg) <= 2^64)%Z
  /\ ((bv_unsigned sp + Z.of_nat (length eimg)) mod 4096 = 0)%Z.
Proof.
  intros segs pc ph en inp HE HI. cbv zeta.
  destruct (valid_entry_unpack _ _ _ _ _ HE HI) as (_ & _ & _ & F).
  pose proof (entry_image_length_ge ph (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en)) as LG.
  pose proof (entry_stack_image_top ph (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en)) as TOP.
  pose proof (entry_page_top_within_window ph (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en) F) as W.
  assert (PG : (entry_page_top (en_sp en) (build_stack_bytes ph (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en)) mod 4096 = 0)%Z).
  { unfold entry_page_top, page_round_up_Z, page_size. Z.div_mod_to_equations. lia. }
  unfold sp_window_hi in *. repeat split; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma run_eq : forall segs pc ph lim en inp,
  run (mkImage segs pc ph) lim en inp =
  let c0 := mkCfg (init_machine_state segs pc ph (en_sp en) (en_draw en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) (mo0 segs lim en inp) in
  {| bh_traces := obs_trace segs c0;
     bh_errors := reaches_error segs c0;
     bh_all_errors := all_traces_error segs c0;
     bh_unmodeled := reaches_unmodeled segs c0 |}.
Proof. intros segs pc ph lim [sp brk mb rnd] inp. reflexivity. Qed.

(* [comment removed for export] *)
Lemma run_scfg_eq : forall cfg segs pc ph lim en inp,
  run_scfg cfg (mkImage segs pc ph) lim en inp =
  let c0 := mkCfg (init_machine_state segs pc ph (en_sp en) (en_draw en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) (mo0 segs lim en inp) in
  {| bh_traces := obs_trace_cfg segs cfg c0;
     bh_errors := reaches_error_cfg segs cfg c0;
     bh_all_errors := all_traces_error_cfg segs cfg c0;
     bh_unmodeled := reaches_unmodeled_cfg segs cfg c0 |}.
Proof. intros cfg segs pc ph lim [sp brk mb rnd] inp. reflexivity. Qed.

Lemma init_config_ms0 : forall segs pc ph lim en inp,
  init_config segs pc ph (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en) lim inp
  = mkCfg (init_machine_state segs pc ph (en_sp en) (en_draw en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) (mo0 segs lim en inp)
  /\ ms_eqv (init_machine_state segs pc ph (en_sp en) (en_draw en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) (ms0 segs pc ph en inp).
Proof. intros. split; [reflexivity | apply init_machine_state_eqv]. Qed.

(* [comment removed for export] *)
Lemma run_fields_ms0 : forall segs pc ph lim en inp,
  let b := run (mkImage segs pc ph) lim en inp in
  let c0 := mkCfg (ms0 segs pc ph en inp) (mo0 segs lim en inp) in
  (forall tr, bh_traces b tr <-> obs_trace segs c0 tr)
  /\ (bh_errors b <-> reaches_error segs c0)
  /\ (bh_all_errors b <-> all_traces_error segs c0)
  /\ (bh_unmodeled b <-> reaches_unmodeled segs c0).
Proof.
  intros segs pc ph lim en inp. rewrite run_eq. cbv zeta. cbn [bh_traces bh_errors bh_all_errors bh_unmodeled].
  exact (init_behaviour_eqv segs pc ph (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en) (mo0 segs lim en inp)).
Qed.

(* [comment removed for export] *)
Definition tree_traces {R : Type} (t : itree node R) (mo : Model) : list event -> Prop :=
  fun tr => exists full, ttrace nstep nexit t mo full /\ is_prefix tr full.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section RC__.
Context {RC__ : RunCeiling}.

Lemma mo0_minv : forall segs lim en inp,
  bv_unsigned (en_sp en) = rc_sp -> valid_sp (en_sp en) -> minv (mo0 segs lim en inp).
Proof.
  intros segs lim en inp Hrc (L & H & _). apply minv_init; [exact Hrc|]. rewrite <- Hrc. split; assumption.
Qed.

Lemma mo0_minv_entry : forall segs pc ph lim en inp,
  bv_unsigned (en_sp en) = rc_sp -> valid_entry (mkImage segs pc ph) en inp -> valid_input inp -> minv (mo0 segs lim en inp).
Proof.
  intros segs pc ph lim en inp Hrc HE HI. destruct (valid_entry_unpack _ _ _ _ _ HE HI) as (V & _). apply mo0_minv; assumption.
Qed.

(* [comment removed for export] *)
Lemma run_of_tree : forall {R : Type} segs pc ph lim (t : itree node R) (Q : R -> machine_state -> Prop) en inp,
  bv_unsigned (en_sp en) = rc_sp -> valid_sp (en_sp en) ->
  impl segs (at_node segs) t Q (ms0 segs pc ph en inp) ->
  leaves_unreachable_m nstep t (mo0 segs lim en inp) ->
  tsafe nstep nsafe t (mo0 segs lim en inp) ->
  (forall tr, bh_traces (run (mkImage segs pc ph) lim en inp) tr <-> tree_traces t (mo0 segs lim en inp) tr)
  /\ ~ bh_errors (run (mkImage segs pc ph) lim en inp)
  /\ ~ bh_unmodeled (run (mkImage segs pc ph) lim en inp).
Proof.
  intros R segs pc ph lim t Q en inp Hrc Hv Himpl Hleaves Hsafe.
  destruct (run_fields_ms0 segs pc ph lim en inp) as (Htr & Herr & _ & Hunm).
  pose proof (nodes_sound segs) as NS. pose proof (mo0_minv segs lim en inp Hrc Hv) as MI.
  split; [| split].
  - intros tr. rewrite (Htr tr). unfold tree_traces.
    apply (impl_run_traces2 node segs (at_node segs) nstep nexit minv nsafe NS t _ _ _
             Himpl Hleaves (mo0_not_halted _ _ _ _) MI Hsafe (ms0_svc _ _ _ _ _)).
  - rewrite Herr.
    apply (impl_run_safe2 node segs (at_node segs) nstep nexit minv nsafe NS t _ _ _
             Himpl Hleaves (mo0_not_halted _ _ _ _) MI Hsafe (ms0_svc _ _ _ _ _)).
  - rewrite Hunm.
    apply (impl_run_modeled2 node segs (at_node segs) nstep nexit minv nsafe NS t _ _ _
             Himpl Hleaves (mo0_not_halted _ _ _ _) MI Hsafe (ms0_svc _ _ _ _ _)).
Qed.

(* [comment removed for export] *)
Lemma run_progress_of_tree : forall {R : Type} segs pc ph lim (t : itree node R) (Q : R -> machine_state -> Prop) en inp tr ms' mo',
  bv_unsigned (en_sp en) = rc_sp -> valid_sp (en_sp en) ->
  impl segs (at_node segs) t Q (ms0 segs pc ph en inp) ->
  leaves_unreachable_m nstep t (mo0 segs lim en inp) ->
  tsafe nstep nsafe t (mo0 segs lim en inp) ->
  star segs (mkCfg (ms0 segs pc ph en inp) (mo0 segs lim en inp)) tr (mkCfg ms' mo') -> m_halted mo' = None ->
  exists evs c'', sstep segs (mkCfg ms' mo') evs (SNext c'').
Proof.
  intros R segs pc ph lim t Q en inp tr ms' mo' Hrc Hv Himpl Hleaves Hsafe Hstar Hh.
  pose proof (mo0_minv segs lim en inp Hrc Hv) as MI.
  eapply (impl_run_progress2 node segs (at_node segs) nstep nexit minv nsafe (nodes_sound segs) t Q);
    eauto using mo0_not_halted.
Qed.
End RC__.
