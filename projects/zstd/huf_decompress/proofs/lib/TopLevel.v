(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (14 recorded proofs replaced by written proofs (ms0_eq, init_config_eq, mo0_not_halted and 11 more); ms0_eq, init_config_eq, mo0_minv and 3 more restated for the revision's model; adds mo0_vsegs, minv_with_vdso, vsegs_tail_high and 1 more; ms0, mo0 redefined for the revision's model; defines vsegs; imports; valid_input_either_va_size and valid_input_either_launch take their conjunct by shape). *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run Vdso.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Frame Exec Cfg ITree Nodes RegsEquiv FP InitMem RunSegs.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition prog_tree (R : Type) : Type := ProcInput -> ExecEntry -> itree node R.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ms0 (segs : list Segment) (pc : N) (ph : PhdrInfo)
    (en : ExecEntry) (inp : ProcInput) : machine_state :=
  init_ms segs pc ph (en_sp en) (en_mmap_base en) (en_draw en) inp.

(* LPS 727298f3 runs a binary over [run_segments segs inp sp mbase], the image's segments
   followed by the vDSO pair, and starts it from [with_vdso (vdso_run_init ...) (init_model ...)]. *)
Definition vsegs (segs : list Segment) (en : ExecEntry) (inp : ProcInput) : list Segment :=
  run_segments segs inp (en_sp en) (en_mmap_base en).

Lemma ms0_eq : forall segs pc ph en inp,
  ms0 segs pc ph en inp =
  MS (mkR_init (en_sp en)) bvmap_empty (Z_to_bv 64 (Z.of_N pc)) (Z_to_bv 32 0) None
     (wrap_mem inp (en_mmap_base en) ph (Z_to_bv 64 (Z.of_N pc)) (en_sp en) (en_draw en)) (seg_rom segs).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition mo0 (segs : list Segment) (lim : Z) (en : ExecEntry) (inp : ProcInput) : Model :=
  with_vdso (vdso_run_init (ed_vdso (en_draw en)))
    (init_model (segments_reserved segs) (en_brk en) (en_mmap_base en) (en_sp en) lim inp).

Lemma mo0_vsegs : forall segs lim en inp,
  with_vdso (vdso_run_init (ed_vdso (en_draw en)))
    (init_model (segments_reserved (vsegs segs en inp)) (en_brk en) (en_mmap_base en) (en_sp en) lim inp)
  = mo0 segs lim en inp.
Proof. intros. unfold vsegs, run_segments, mo0. rewrite segments_reserved_vdso_app. reflexivity. Qed.

Lemma init_config_eq : forall segs pc ph lim en inp,
  init_config segs pc ph (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en) lim inp
  = mkCfg (init_machine_state segs pc ph (en_sp en) (en_mmap_base en) (en_draw en) inp) (mo0 segs lim en inp).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma mo0_not_halted : forall segs lim en inp, m_halted (mo0 segs lim en inp) = None.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma minv_with_vdso : forall v mo, minv mo -> minv (with_vdso v mo).
Proof. intros v mo H. exact H. Qed.

Lemma mo0_minv : forall segs pc ph lim en inp,
  valid_entry (mkImage segs pc ph) en inp -> in_va_size inp = Sv48 -> in_channel_reader inp = true ->
  minv (mo0 segs lim en inp).
Proof.
  intros segs pc ph lim [sp brk mb dr] inp Hve Hsv48 Hrdr.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hve. destruct Hve as (Vsp & _ & _ & _).
  unfold mo0. apply minv_with_vdso. apply minv_init; [|exact Hrdr].
  destruct Vsp as (L & H & _). cbn [en_sp].
lia.
Qed.

(* [comment removed for export] *)
Lemma valid_input_either_va_size : forall inp, valid_input_either inp -> in_va_size inp = Sv48.
Proof. intros inp H. red in H. repeat match goal with H : _ /\ _ |- _ => destruct H end. assumption. Qed.   (* [comment removed for export] *)

Lemma valid_input_either_launch : forall inp, valid_input_either inp -> valid_launch inp.
Proof. intros inp H. red in H. repeat match goal with H : _ /\ _ |- _ => destruct H end. assumption. Qed.

Lemma valid_entry_either : forall segs pc ph sp brk mb dr inp, valid_input_either inp ->
  valid_entry (mkImage segs pc ph) (mkEntry sp brk mb dr) inp <->
  (valid_sp sp /\ valid_brk segs brk /\ valid_mmap_base mb /\ entry_stack_fits sp (in_argv inp) (in_envp inp)
   /\ entry_launch_ok_va Sv48 (mkEntry sp brk mb dr) inp).
Proof. intros. apply valid_entry_sv48. apply valid_input_either_va_size. assumption. Qed.

(* [comment removed for export] *)
Lemma mo0_vm_init_sp : forall segs lim en inp, vm_init_sp (m_vmmaps (mo0 segs lim en inp)) = en_sp en.
Proof. reflexivity. Qed.
Lemma mo0_alloc_top : forall segs lim en inp, alloc_top (m_vmmaps (mo0 segs lim en inp)) = entry_atop en.
Proof. reflexivity. Qed.

Lemma ms0_svc : forall segs pc ph en inp, ms_svc_pending (ms0 segs pc ph en inp) = None.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Remark frm0_init : frm0 (Z_to_bv 32 0).
Proof. reflexivity. Qed.

Lemma ms0_frm0 : forall segs pc ph en inp, frm0 (ms_fcsr (ms0 segs pc ph en inp)).
Proof. intros. exact frm0_init. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition tree_ok {R : Type} (segs : list Segment) (pc : N) (ph : PhdrInfo) (lim : Z)
    (t : prog_tree R) (Q : R -> machine_state -> Prop) : Prop :=
  forall en inp, valid_entry (mkImage segs pc ph) en inp -> valid_input_either inp ->
    impl segs (at_node segs) (t inp en) Q (ms0 segs pc ph en inp)
    /\ leaves_unreachable_m nstep (t inp en) (mo0 segs lim en inp)
    /\ tsafe nstep nsafe (t inp en) (mo0 segs lim en inp).

(* [comment removed for export] *)
Definition tree_traces {R : Type} (t : itree node R) (mo : Model) : list event -> Prop :=
  fun tr => exists full, ttrace nstep nexit t mo full /\ is_prefix tr full.

(* [comment removed for export] *)
Definition trees_equiv {RS RT : Type} (segsS : list Segment) (pcS : N) (phS : PhdrInfo)
    (segsT : list Segment) (pcT : N) (phT : PhdrInfo) (tS : prog_tree RS) (tT : prog_tree RT) : Prop :=
  forall enS enT inp,
    valid_entry (mkImage segsS pcS phS) enS inp ->
    valid_entry (mkImage segsT pcT phT) enT inp ->
    valid_input_either inp ->
    trace_equiv (tree_traces (tS inp enS) (mo0 segsS source_alloc_limit enS inp))
                (tree_traces (tT inp enT) (mo0 segsT target_alloc_limit enT inp)).

(* [comment removed for export] *)
Lemma trees_equiv_of_ttrace : forall {RS RT : Type} (tS : itree node RS) (tT : itree node RT) moS moT,
  (forall tr, ttrace nstep nexit tS moS tr <-> ttrace nstep nexit tT moT tr) ->
  trace_equiv (tree_traces tS moS) (tree_traces tT moT).
Proof.
  intros RS RT tS tT moS moT H tr. unfold tree_traces.
  split; intros (full & Hf & Hp); exists full; split; auto; apply H; exact Hf.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma in_map_WriteEv_no_kill : forall fd l sig fs, ~ In (KillEv sig fs) (map (WriteEv fd) l).
Proof.
  intros fd l sig fs Hin. apply in_map_iff in Hin as (x & Hx & _). discriminate Hx.
Qed.

Lemma nstep_no_kill : forall n mo eff mo' evs,
  nstep n mo eff mo' evs -> forall sig fs, ~ In (KillEv sig fs) evs.
Proof.
  intros n mo eff mo' evs Hst sig fs.
  destruct n; cbn [nstep] in Hst.
  - (* [comment removed for export] *) destruct Hst as (k & _ & _ & _ & ->). apply in_map_WriteEv_no_kill.
  - (* [comment removed for export] *) destruct Hst as (_ & Hst).
    destruct (Z.of_nat (length (concat bufs)) =? 0).
    + destruct Hst as (_ & ->). intros [].
    + destruct Hst as (k & _ & _ & ->). apply in_map_WriteEv_no_kill.
  - destruct Hst as (-> & _); intros [].
  - destruct Hst as (-> & _); intros [].
  - destruct Hst as (-> & _); intros [].
  - destruct Hst as (-> & _); intros [].
  - destruct Hst as (-> & _); intros [].
  - destruct Hst as [].
  - destruct Hst as (-> & _); intros [].
  - destruct Hst as (-> & _); intros [].
  - destruct Hst as (-> & _); intros [].
  - destruct Hst as (-> & _); intros [].
  - destruct Hst as (-> & _); intros [].
Qed.

Lemma ttrace_no_kill : forall {R : Type} (t : itree node R) mo tr,
  ttrace nstep nexit t mo tr -> forall sig fs, ~ In (KillEv sig fs) tr.
Proof.
  intros R t. induction t as [r | n k IH]; intros mo tr Htr sig fs.
  - cbn in Htr. subst tr. intros [].
  - cbn [ttrace] in Htr. destruct Htr as [(code & mo' & _ & ->) | (rsp & mo' & evs & tr' & Hst & Htr' & ->)].
    + intros [H | []]. discriminate H.
    + intros Hin. apply in_app_or in Hin as [Hin | Hin].
      * exact (nstep_no_kill _ _ _ _ _ Hst sig fs Hin).
      * exact (IH rsp mo' tr' Htr' sig fs Hin).
Qed.

Lemma tree_traces_no_kill : forall {R : Type} (t : itree node R) mo tr,
  tree_traces t mo tr -> forall sig fs, ~ In (KillEv sig fs) tr.
Proof.
  intros R t mo tr (full & Hf & Hp) sig fs Hin.
  exact (ttrace_no_kill t mo full Hf sig fs (in_is_prefix _ _ _ Hp Hin)).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma run_eq : forall segs pc ph lim en inp,
  run_scfg ACFG (mkImage segs pc ph) lim en inp =
  let c0 := mkCfg (init_machine_state (vsegs segs en inp) pc ph (en_sp en) (en_mmap_base en) (en_draw en) inp) (mo0 segs lim en inp) in
  {| bh_traces := obs_trace_cfg (vsegs segs en inp) ACFG c0;
     bh_errors := reaches_error_cfg (vsegs segs en inp) ACFG c0;
     bh_all_errors := all_traces_error_cfg (vsegs segs en inp) ACFG c0;
     bh_unmodeled := reaches_unmodeled_cfg (vsegs segs en inp) ACFG c0 |}.
Proof. intros segs pc ph lim [sp brk mb dr] inp. cbv zeta. rewrite <- mo0_vsegs. reflexivity. Qed.

(* The vDSO pair lies above every image this tree verifies. *)
Lemma vsegs_tail_high : forall segs pc ph en inp,
  valid_entry (mkImage segs pc ph) en inp -> in_va_size inp = Sv48 ->
  (segs_top segs <= 0x10000000)%Z ->
  forall s, In s (vdso_segments (in_kernel inp) (en_sp en) (en_mmap_base en)) ->
    (segs_top segs + 8 <= Z.of_N (seg_base s))%Z.
Proof.
  intros segs pc ph [sp brk mb dr] inp Hve Hsv48 Htop s Hs.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hve. destruct Hve as (Vsp & _ & Vmb & _ & _).
  exact (vdso_segments_high (in_kernel inp) sp mb (segs_top segs + 8) Vsp Vmb ltac:(lia) s Hs).
Qed.

(* The run's initial machine state is the proof's, with the run's read-only backing. *)
Lemma init_ms_vsegs : forall segs pc ph en inp,
  init_ms (vsegs segs en inp) pc ph (en_sp en) (en_mmap_base en) (en_draw en) inp
  = with_rom (ms0 segs pc ph en inp) (seg_rom (vsegs segs en inp)).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma run_of_tree : forall {R : Type} segs pc ph lim (t : itree node R) (Q : R -> machine_state -> Prop) en inp,
  valid_entry (mkImage segs pc ph) en inp ->
  in_va_size inp = Sv48 ->
  in_channel_reader inp = true ->
  (segs_top segs <= 0x10000000)%Z ->
  impl segs (at_node segs) t Q (ms0 segs pc ph en inp) ->
  leaves_unreachable_m nstep t (mo0 segs lim en inp) ->
  tsafe nstep nsafe t (mo0 segs lim en inp) ->
  trace_equiv (bh_traces (run_scfg ACFG (mkImage segs pc ph) lim en inp)) (tree_traces t (mo0 segs lim en inp))
  /\ ~ bh_errors (run_scfg ACFG (mkImage segs pc ph) lim en inp)
  /\ ~ bh_unmodeled (run_scfg ACFG (mkImage segs pc ph) lim en inp)
  /\ ~ dies_by_signal (run_scfg ACFG (mkImage segs pc ph) lim en inp).
Proof.
  intros R segs pc ph lim t Q en inp Hve Hsv48 Hrdr Htop Himpl0 Hleaves Hsafe.
  pose proof (mo0_minv segs pc ph lim en inp Hve Hsv48 Hrdr) as Hminv.
  pose proof (impl_lift segs (vdso_segments (in_kernel inp) (en_sp en) (en_mmap_base en))
                (vsegs_tail_high segs pc ph en inp Hve Hsv48 Htop) t Q _ Himpl0) as Himpl.
  change (segs ++ vdso_segments (in_kernel inp) (en_sp en) (en_mmap_base en)) with (vsegs segs en inp) in Himpl.
  rewrite <- init_ms_vsegs in Himpl.
  set (V := vsegs segs en inp) in *.
  rewrite run_eq. cbn [bh_traces bh_errors bh_unmodeled]. fold V.
  destruct (init_behaviour_eqv_scfg ACFG V pc ph (en_sp en) (en_mmap_base en) (en_draw en) inp (mo0 segs lim en inp))
    as (Htr & Herr & _ & Hunm).
  pose proof (nodes_sound V) as NS.
  assert (Hsvc : ms_svc_pending (init_ms V pc ph (en_sp en) (en_mmap_base en) (en_draw en) inp) = None) by reflexivity.
  assert (HTR : trace_equiv (obs_trace_cfg V ACFG (mkCfg (init_machine_state V pc ph (en_sp en) (en_mmap_base en) (en_draw en) inp) (mo0 segs lim en inp)))
                            (tree_traces t (mo0 segs lim en inp))).
  { intros tr. rewrite (Htr tr). unfold tree_traces.
    apply (impl_run_traces2 node V (at_node V) nstep nexit minv nsafe NS t _ _ _
             Himpl Hleaves (mo0_not_halted _ _ _ _) Hminv Hsafe Hsvc). }
  split; [exact HTR| split; [| split]].
  - rewrite Herr.
    apply (impl_run_safe2 node V (at_node V) nstep nexit minv nsafe NS t _ _ _
             Himpl Hleaves (mo0_not_halted _ _ _ _) Hminv Hsafe Hsvc).
  - rewrite Hunm.
    apply (impl_run_modeled2 node V (at_node V) nstep nexit minv nsafe NS t _ _ _
             Himpl Hleaves (mo0_not_halted _ _ _ _) Hminv Hsafe Hsvc).
  - (* [comment removed for export] *)
    intros (tr & sig & fs & Hb & Hin). cbn [bh_traces] in Hb.
    apply (proj1 (HTR tr)) in Hb. exact (tree_traces_no_kill t _ tr Hb sig fs Hin).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma trace_equiv_sym : forall T1 T2, trace_equiv T1 T2 -> trace_equiv T2 T1.
Proof. intros T1 T2 H tr. symmetry. apply H. Qed.

Lemma trace_equiv_trans : forall T1 T2 T3, trace_equiv T1 T2 -> trace_equiv T2 T3 -> trace_equiv T1 T3.
Proof. intros T1 T2 T3 H1 H2 tr. rewrite (H1 tr). apply H2. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From OSSVerify.zstd.huf_decompress.images Require Import Plain.

Module SrcImg := Plain.M.

(* [comment removed for export] *)
(* [comment removed for export] *)
