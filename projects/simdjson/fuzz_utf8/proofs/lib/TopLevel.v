(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: changed init_config_eq, mo0, mo0_minv and 6 more; added NX, at_node_lift, bytes_at_app_tail and 36 more; removed run_eq; taken in part from projects/simdjson/fuzz_minifyimpl/proofs/lib/TopLevel.v, line 73. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Vdso Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem DecodeC.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib Require Import Cfg.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib Require Import PropExec MState Mem Frame Exec ITree Nodes RegsEquiv FP InitMem.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition prog_tree (R : Type) : Type := ProcInput -> ExecEntry -> itree node R.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* LPS 75d69e00: [RegsEquiv.init_ms] takes the mmap base, the entry draw and the whole input, as
   [Run.init_machine_state] does (fuzz_dump's TopLevel is the template). *)
Definition ms0 (segs : list Segment) (pc : N) (ph : PhdrInfo)
    (en : ExecEntry) (inp : ProcInput) : machine_state :=
  init_ms segs pc ph (en_sp en) (en_mmap_base en) (en_draw en) inp.

Lemma ms0_eq : forall segs pc ph en inp,
  ms0 segs pc ph en inp =
  MS (mkR_init (en_sp en)) bvmap_empty (Z_to_bv 64 (Z.of_N pc)) (Z_to_bv 32 0) None
     (wrap_mem inp (en_mmap_base en) ph (Z_to_bv 64 (Z.of_N pc)) (en_sp en) (en_draw en)) (seg_rom segs).
Proof. reflexivity. Qed.

(* The run's initial model, as [Run.init_config] builds it: the ledger and the launch, with the
   entry's vDSO draw installed. *)
Definition mo0 (segs : list Segment) (lim : Z) (en : ExecEntry) (inp : ProcInput) : Model :=
  with_vdso (vdso_run_init (ed_vdso (en_draw en)))
    (init_model (segments_reserved segs) (en_brk en) (en_mmap_base en) (en_sp en) lim inp).

Lemma init_config_eq : forall segs pc ph lim en inp,
  init_config segs pc ph (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en) lim inp
  = mkCfg (init_machine_state segs pc ph (en_sp en) (en_mmap_base en) (en_draw en) inp) (mo0 segs lim en inp).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma mo0_not_halted : forall segs lim en inp, m_halted (mo0 segs lim en inp) = None.
Proof. reflexivity. Qed.

(* [State.with_vdso] rebuilds the VM record from [m]'s own maps, lazy and materialized lists, and
   keeps the fd table, file system and process, so every conjunct of [minv] is [m]'s. *)
Lemma minv_with_vdso : forall v m, minv m -> minv (with_vdso v m).
Proof. intros v m H. unfold minv in *. exact H. Qed.

(* [comment removed for export] *)
Lemma mo0_minv : forall segs pc ph lim en inp,
  valid_entry (mkImage segs pc ph) en inp -> in_va_size inp = Sv48 -> in_channel_reader inp = true ->
  minv (mo0 segs lim en inp).
Proof.
  intros segs pc ph lim [sp brk mb dr] inp Hve Hsv48 Hrd.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hve. destruct Hve as (Vsp & _ & _ & _).
  apply minv_with_vdso. apply minv_init; [| exact Hrd].
  destruct Vsp as (L & H & _). cbn [en_sp]. lia.
Qed.

(* [comment removed for export] *)
(* BY NAME, not by index.  [in_va_size] moved to [valid_input_either]'s TENTH conjunct at
   75d69e00 and the old eight-underscore pattern silently took [valid_hwcap] instead -- it
   named a different clause rather than failing, which is the hazard the model warns about
   beside its own accessors.  So nothing here counts conjuncts: the model's
   [valid_input_either_splits] (Run.v:4721) turns the predicate into the two pinned launches,
   and each arm has its own accessor, [valid_input_va_size] (:5126) and
   [valid_input_abort_va_size] (:5282).  Cited by rev:
     git -C ~/src/lps-revision show 75d69e00:theories/LinuxProcessSem/Run.v
   A later conjunct cannot break this proof, because no part of it mentions a position. *)
Lemma valid_input_either_va_size : forall inp, valid_input_either inp -> in_va_size inp = Sv48.
Proof.
  intros inp H. destruct (valid_input_either_splits inp H) as [Hv | Ha].
  - exact (valid_input_va_size inp Hv).
  - exact (valid_input_abort_va_size inp Ha).
Qed.

(* The same answer for a conjunct the model gives no [_either] accessor for -- argv, envp,
   creds, hwcap.  Split the predicate to full depth and let [assumption] match the TYPE, which
   is what the model's own accessors do inside.  [valid_creds] is unfolded because its two ids
   sit behind a Definition.  Never a positional index: the model's note beside its accessors
   says a caller reaching in by position will "name a DIFFERENT clause rather than fail". *)
Ltac vie_pick H :=
  red in H; unfold valid_creds in H;
  repeat match goal with Hx : _ /\ _ |- _ => destruct Hx end;
  assumption.

Lemma valid_input_either_launch : forall inp, valid_input_either inp -> valid_launch inp.
Proof.
  intros inp H. red in H.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  assumption.
Qed.

Lemma valid_entry_either : forall segs pc ph sp brk mb dr inp, valid_input_either inp ->
  valid_entry (mkImage segs pc ph) (mkEntry sp brk mb dr) inp <->
  (valid_sp sp /\ valid_brk segs brk /\ valid_mmap_base mb /\ entry_stack_fits sp (in_argv inp) (in_envp inp)
   /\ entry_launch_ok_va Sv48 (mkEntry sp brk mb dr) inp).   (* LPS 75d69e00: [valid_entry_sv48]'s fifth conjunct *)
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
  - (* [comment removed for export] *) destruct Hst as (-> & _); intros [].
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

(* ------------------------------------------------------------------------- *)
(* The run's segment list.  [Run.run_scfg] reads every step against           *)
(* [run_segments segs inp sp mbase] = [segs ++ vdso_segments ...], and its      *)
(* initial state's ROM is that list's; the tree proofs run over [segs].  The   *)
(* vDSO pair is never executable, so a step that succeeds over [segs]          *)
(* succeeds over [segs ++ tail] with the same result, and the ROM field,       *)
(* which no step reads, is carried along.  Ported from fuzz_dump's TopLevel    *)
(* (farm-compiled there in fuzz_dump-20261104t184617z-3914d1); at_node_lift    *)
(* follows this tree's [at_node], and impl_lift this tree's two-constructor     *)
(* [itree].                                                                    *)
(* ------------------------------------------------------------------------- *)

Lemma fs_app_some : forall segs tail a n s,
  find_segment segs a n = Some s -> find_segment (segs ++ tail) a n = Some s.
Proof.
  induction segs as [|s0 r IH]; intros tail a n s; [intro H; discriminate H|].
  cbn [find_segment app].
  match goal with |- context [if ?c then _ else _] => destruct c end; [auto| apply IH].
Qed.

Lemma fs_app_none : forall segs tail a n,
  find_segment segs a n = None -> find_segment (segs ++ tail) a n = find_segment tail a n.
Proof.
  induction segs as [|s0 r IH]; intros tail a n; [intros _; reflexivity|].
  cbn [find_segment app].
  match goal with |- context [if ?c then _ else _] => destruct c end; [intro H; discriminate H| apply IH].
Qed.

Lemma fs_in : forall l a n s, find_segment l a n = Some s -> In s l.
Proof.
  induction l as [|s0 r IH]; intros a n s; [intro H; discriminate H|].
  cbn [find_segment].
  match goal with |- context [if ?c then _ else _] => destruct c end.
  - intro H. injection H as <-. left. reflexivity.
  - intro H. right. exact (IH _ _ _ H).
Qed.

Lemma mr_app : forall segs tail a n x,
  memory_read segs a n = Some x -> memory_read (segs ++ tail) a n = Some x.
Proof.
  intros segs tail a n x. unfold memory_read.
  destruct (find_segment segs (bv_unsigned a) (Z.of_N n)) as [s|] eqn:E; [|intro H; discriminate H].
  rewrite (fs_app_some segs tail _ _ _ E). auto.
Qed.

Lemma ov_read_app : forall segs tail n m a bs,
  ov_read_bytes segs m a n = Some bs -> ov_read_bytes (segs ++ tail) m a n = Some bs.
Proof.
  intros segs tail n. induction n as [|n IH]; intros m a bs; cbn [ov_read_bytes]; [auto|].
  destruct (m a) as [b|].
  - destruct (ov_read_bytes segs m (a + 1) n) as [rest|] eqn:E1; [|intro H; discriminate H].
    rewrite (IH _ _ _ E1). auto.
  - destruct (memory_read segs a 1) as [[|b l]|] eqn:Emr; [intro H; discriminate H| |intro H; discriminate H].
    rewrite (mr_app segs tail _ _ _ Emr).
    destruct (ov_read_bytes segs m (a + 1) n) as [rest|] eqn:E1; [|intro H; discriminate H].
    rewrite (IH _ _ _ E1). auto.
Qed.

Lemma wview_app : forall segs tail m a b,
  wview segs m a = Some b -> wview (segs ++ tail) m a = Some b.
Proof.
  intros segs tail m a b. unfold wview. destruct (m a); [auto|].
  destruct (find_segment segs (bv_unsigned a) 1) as [s|] eqn:E; [|intro H; discriminate H].
  rewrite (fs_app_some segs tail _ _ _ E). auto.
Qed.

Lemma store_ok_app : forall segs tail m n a,
  store_ok segs m a n = true -> store_ok (segs ++ tail) m a n = true.
Proof.
  intros segs tail m n. induction n as [|n IH]; intros a; cbn [store_ok]; [auto|].
  destruct (wview segs m a) as [b|] eqn:E; [|intro H; discriminate H].
  rewrite (wview_app segs tail m a b E). apply IH.
Qed.

Lemma interp_app : forall segs tail t m r,
  interp_eff_accesses segs t m = MachineOk r -> interp_eff_accesses (segs ++ tail) t m = MachineOk r.
Proof.
  intros segs tail t. induction t as [c|c|c|c|c|c|n a k IH|n a v k IH]; intros m r; cbn [interp_eff_accesses];
    try (intro H; discriminate H); try (intro H; exact H).
  - destruct (ov_read_bytes segs m a (width_bytes n)) as [bs|] eqn:E.
    + rewrite (ov_read_app segs tail _ _ _ _ E).
      lazymatch goal with |- context [interp_eff_accesses segs ?t0 ?m0] =>
        destruct (interp_eff_accesses segs t0 m0) as [rep| |] eqn:E2 end;
        [|intro H; discriminate H|intro H; discriminate H].
      rewrite (IH _ _ _ E2). auto.
    + destruct (range_meets_vvar segs a (width_bytes n)); intro H; discriminate H.
  - destruct (store_ok segs m a (width_bytes n)) eqn:E; [|intro H; discriminate H].
    rewrite (store_ok_app segs tail _ _ _ E).
    lazymatch goal with |- context [interp_eff_accesses segs ?t0 ?m0] =>
      destruct (interp_eff_accesses segs t0 m0) as [rep| |] eqn:E2 end;
      [|intro H; discriminate H|intro H; discriminate H].
    rewrite (IH _ _ E2). auto.
Qed.

Lemma decode_app : forall segs tail st w r,
  decode_exec_accesses segs st w = MachineOk r -> decode_exec_accesses (segs ++ tail) st w = MachineOk r.
Proof.
  intros segs tail st w r. unfold decode_exec_accesses.
  destruct (is_ecall w); [auto|].
  destruct (decode_any w) as [[i isz]|]; [|auto].
  lazymatch goal with |- context [interp_eff_accesses segs ?t0 ?m0] =>
    destruct (interp_eff_accesses segs t0 m0) as [rep| |] eqn:E end;
    [|intro H; discriminate H|intro H; discriminate H].
  rewrite (interp_app segs tail _ _ _ E). auto.
Qed.

Lemma fetch_failure_not_ok : forall segs m a st, fetch_failure segs m a <> MachineOk st.
Proof.
  intros segs m a st. unfold fetch_failure. cbv zeta.
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; discriminate.
Qed.

Section NonExecTail.
  Variables (segs tail : list Segment).
  Hypothesis NX : Forall (fun s => seg_executable s = false) tail.

  Lemma code_read_app : forall a n, code_read (segs ++ tail) a n = code_read segs a n.
  Proof.
    intros a n. unfold code_read.
    destruct (find_segment segs (bv_unsigned a) (Z.of_N n)) as [s|] eqn:E.
    - rewrite (fs_app_some segs tail _ _ _ E). reflexivity.
    - rewrite (fs_app_none segs tail _ _ E).
      destruct (find_segment tail (bv_unsigned a) (Z.of_N n)) as [s|] eqn:E2; [|reflexivity].
      apply fs_in in E2. rewrite Forall_forall in NX. rewrite (NX s E2). reflexivity.
  Qed.

  Lemma code_read_ov_app : forall m a n, code_read_ov (segs ++ tail) m a n = code_read_ov segs m a n.
  Proof.
    intros m a n. unfold code_read_ov.
    destruct (find_segment segs (bv_unsigned a) (Z.of_N n)) as [s|] eqn:E.
    - rewrite (fs_app_some segs tail _ _ _ E). reflexivity.
    - rewrite (fs_app_none segs tail _ _ E).
      destruct (find_segment tail (bv_unsigned a) (Z.of_N n)) as [s|] eqn:E2; [|reflexivity].
      apply fs_in in E2. rewrite Forall_forall in NX. rewrite (NX s E2). reflexivity.
  Qed.

  Lemma fetch_word_app : forall a, fetch_word (segs ++ tail) a = fetch_word segs a.
  Proof. intros a. unfold fetch_word. rewrite code_read_app. reflexivity. Qed.

  Lemma fetch_word_ov_app : forall m a, fetch_word_ov (segs ++ tail) m a = fetch_word_ov segs m a.
  Proof. intros m a. unfold fetch_word_ov. rewrite code_read_ov_app. reflexivity. Qed.

  Lemma fetch_half_any_app : forall m a, fetch_half_any (segs ++ tail) m a = fetch_half_any segs m a.
  Proof. intros m a. unfold fetch_half_any, fetch_half, fetch_half_ov. rewrite code_read_app, code_read_ov_app. reflexivity. Qed.

  Lemma fetch_tail_any_app : forall m a, fetch_tail_any (segs ++ tail) m a = fetch_tail_any segs m a.
  Proof. intros m a. unfold fetch_tail_any. rewrite !fetch_half_any_app. reflexivity. Qed.

  Lemma step_app : forall st st',
    RiscvSemantics.step segs st = MachineOk st' -> RiscvSemantics.step (segs ++ tail) st = MachineOk st'.
  Proof.
    intros st st'. unfold RiscvSemantics.step, step_accesses.
    rewrite fetch_word_app, fetch_word_ov_app, fetch_tail_any_app.
    destruct (fetch_word segs (ms_pc st)) as [w|].
    { destruct (decode_exec_accesses segs st w) as [rep| |] eqn:E; cbn [drop_access_report]; intro H; try discriminate H.
      rewrite (decode_app segs tail _ _ _ E). exact H. }
    destruct (fetch_word_ov segs (ms_mem st) (ms_pc st)) as [w|].
    { destruct (decode_exec_accesses segs st w) as [rep| |] eqn:E; cbn [drop_access_report]; intro H; try discriminate H.
      rewrite (decode_app segs tail _ _ _ E). exact H. }
    destruct (fetch_tail_any segs (ms_mem st) (ms_pc st)) as [w|].
    { destruct (decode_exec_accesses segs st w) as [rep| |] eqn:E; cbn [drop_access_report]; intro H; try discriminate H.
      rewrite (decode_app segs tail _ _ _ E). exact H. }
    destruct (fetch_failure segs (ms_mem st) (ms_pc st)) eqn:FF; cbn [drop_access_report]; intro H; try discriminate H.
    exfalso. exact (fetch_failure_not_ok _ _ _ _ FF).
  Qed.
End NonExecTail.

(* A machine state with its ROM replaced. *)
Definition set_rom (r : word -> option byte) (ms : machine_state) : machine_state :=
  {| ms_regs := ms_regs ms; ms_fregs := ms_fregs ms; ms_pc_val := ms_pc_val ms;
     ms_svc_pending := ms_svc_pending ms; ms_resv := ms_resv ms; ms_fcsr := ms_fcsr ms;
     ms_mem := ms_mem ms; ms_rom := r |}.

Lemma dec_set_rom : forall sg r st w st',
  drop_access_report (decode_exec_accesses sg st w) = MachineOk st' ->
  drop_access_report (decode_exec_accesses sg (set_rom r st) w) = MachineOk (set_rom r st').
Proof.
  intros sg r st w st'. unfold decode_exec_accesses.
  cbn [set_rom ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem ms_rom ms_svc_pending].
  destruct (is_ecall w).
  - cbn [drop_access_report access_value]. intro H. injection H as <-. reflexivity.
  - destruct (decode_any w) as [[i isz]|]; [|destruct (is_defined_illegal w); cbn [drop_access_report]; intro H; discriminate H].
    lazymatch goal with |- context [interp_eff_accesses sg ?t0 ?m0] =>
      destruct (interp_eff_accesses sg t0 m0) as [rep| |] end;
      [| cbn [drop_access_report]; intro H; discriminate H | cbn [drop_access_report]; intro H; discriminate H].
    destruct (@access_value _ rep) as [c m']. cbn [drop_access_report access_value].
    intro H. injection H as <-. reflexivity.
Qed.

Lemma step_set_rom : forall sg r st st',
  RiscvSemantics.step sg st = MachineOk st' -> RiscvSemantics.step sg (set_rom r st) = MachineOk (set_rom r st').
Proof.
  intros sg r st st'. unfold RiscvSemantics.step, step_accesses.
  change (ms_pc (set_rom r st)) with (ms_pc st). change (ms_mem (set_rom r st)) with (ms_mem st).
  destruct (fetch_word sg (ms_pc st)) as [w|]; [apply dec_set_rom|].
  destruct (fetch_word_ov sg (ms_mem st) (ms_pc st)) as [w|]; [apply dec_set_rom|].
  destruct (fetch_tail_any sg (ms_mem st) (ms_pc st)) as [w|]; [apply dec_set_rom|].
  destruct (fetch_failure sg (ms_mem st) (ms_pc st)) eqn:FF; cbn [drop_access_report]; intro H; try discriminate H.
  exfalso. exact (fetch_failure_not_ok _ _ _ _ FF).
Qed.

Lemma mstep_lift : forall segs tail r ms ms',
  Forall (fun s => seg_executable s = false) tail ->
  mstep segs ms ms' -> mstep (segs ++ tail) (set_rom r ms) (set_rom r ms').
Proof.
  intros segs tail r ms ms' NX [Hs H]. split; [exact Hs|].
  apply step_set_rom. exact (step_app segs tail NX _ _ H).
Qed.

Lemma evt_lift : forall segs tail r (P : machine_state -> Prop) ms,
  Forall (fun s => seg_executable s = false) tail ->
  evt segs P ms -> evt (segs ++ tail) (fun ms' => exists msp, ms' = set_rom r msp /\ P msp) (set_rom r ms).
Proof.
  intros segs tail r P ms NX (ms1 & Hm & HP). exists (set_rom r ms1). split; [|exists ms1; split; [reflexivity| exact HP]].
  clear HP. induction Hm as [ms0|ms0 ms2 ms3 H1 H2 IH].
  - apply msteps_refl.
  - eapply msteps_cons; [exact (mstep_lift segs tail r _ _ NX H1)| exact IH].
Qed.

Lemma mrd_app : forall segs tail m a b, mrd segs m a = Some b -> mrd (segs ++ tail) m a = Some b.
Proof.
  intros segs tail m a b. unfold mrd, seg_rom. destruct (m a); [auto|].
  destruct (memory_read segs a 1) as [[|b0 l]|] eqn:E; [intro H; discriminate H| |intro H; discriminate H].
  rewrite (mr_app segs tail _ _ _ E). auto.
Qed.

Lemma bytes_at_app_tail : forall segs tail m a bs, bytes_at segs m a bs -> bytes_at (segs ++ tail) m a bs.
Proof.
  intros segs tail m a bs (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|].
  intros i Hi. specialize (H3 i Hi). destruct (nth_error bs i) as [b|] eqn:E.
  - apply mrd_app. exact H3.
  - apply nth_error_None in E. lia.
Qed.

Lemma wr_at_app_tail : forall segs tail m a n, wr_at segs m a n -> wr_at (segs ++ tail) m a n.
Proof.
  intros segs tail m a n (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|].
  intros i Hi Hw. apply (H3 i Hi).
  destruct (wview segs m (wa (a + i))) as [b|] eqn:E; [|reflexivity].
  rewrite (wview_app segs tail _ _ _ E) in Hw. discriminate Hw.
Qed.

(* This tree's [at_node]: NWrite, NWritev and NOpen carry [ms_rom ms = seg_rom segs] and a
   [bytes_at], NRead a [wr_at]; the other nine constructors read neither the ROM nor [segs]. *)
Lemma at_node_lift : forall segs tail n ms,
  at_node segs n ms -> at_node (segs ++ tail) n (set_rom (seg_rom (segs ++ tail)) ms).
Proof.
  intros segs tail n ms H. destruct n; cbn [at_node] in H |- *; try exact H.
  - (* NWrite *)
    destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & _ & H8).
    split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|]. split; [exact H6|].
    split; [reflexivity|]. apply bytes_at_app_tail. exact H8.
  - (* NWritev *)
    destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & _ & iovs & H9 & H10).
    split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|]. split; [exact H6|].
    split; [exact H7|]. split; [reflexivity|]. exists iovs. split; [apply bytes_at_app_tail; exact H9|].
    clear -H10. induction H10 as [|iov bs l1 l2 HP HF IH]; constructor; [|exact IH].
    destruct HP as (A & B & C). split; [exact A|]. split; [exact B|]. apply bytes_at_app_tail. exact C.
  - (* NOpen *)
    destruct H as (H1 & H2 & H3 & H4 & H5 & _ & H7 & H8).
    split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
    split; [reflexivity|]. split; [apply bytes_at_app_tail; exact H7| exact H8].
  - (* NRead *)
    destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
    split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|]. split; [exact H6|].
    split; [exact H7|]. apply wr_at_app_tail. exact H8.
Qed.

Lemma nret_set_rom : forall r ms rsp, nret (set_rom r ms) rsp = set_rom r (nret ms rsp).
Proof. reflexivity. Qed.

Lemma impl_lift : forall segs tail {R} (t : itree node R) (Q : R -> machine_state -> Prop) ms,
  Forall (fun s => seg_executable s = false) tail ->
  impl segs (at_node segs) t Q ms ->
  impl (segs ++ tail) (at_node (segs ++ tail)) t
       (fun r ms' => exists msp, ms' = set_rom (seg_rom (segs ++ tail)) msp /\ Q r msp)
       (set_rom (seg_rom (segs ++ tail)) ms).
Proof.
  intros segs tail R t. induction t as [r|n k IH]; intros Q ms NX H; cbn [impl] in H |- *.
  - exact (evt_lift segs tail _ _ ms NX H).
  - eapply evt_mono; [exact (evt_lift segs tail (seg_rom (segs ++ tail)) _ ms NX H)|].
    intros ms' (msp & -> & Hat & Hk). split; [apply at_node_lift; exact Hat|].
    intros rsp. rewrite nret_set_rom. apply IH; [exact NX| apply Hk].
Qed.

(* The vDSO pair is read-only ("r--") and is no reservation of the binary. *)
Local Transparent vdso_segments.

Lemma vdso_nonexec : forall kb (sp mbase : word),
  Forall (fun s => seg_executable s = false) (vdso_segments kb sp mbase).
Proof.
  intros kb sp mbase. unfold vdso_segments. cbv zeta.
  match goal with |- context [if ?c then _ else _] => destruct c end; repeat constructor.
Qed.

Lemma run_segments_reserved : forall segs inp (sp mbase : word),
  segments_reserved (run_segments segs inp sp mbase) = segments_reserved segs.
Proof.
  intros segs inp sp mbase. unfold segments_reserved, run_segments.
  (* LPS 75d69e00: [Run.segments_reserved] filters with STDPP's [filter] (a [Decision]-indexed
     predicate), not [List.filter], so Stdlib's [filter_app] does not match the subterm. *)
  rewrite list_basics.list.filter_app.
  assert (E : filter (fun s => negb (seg_kernel_map s)) (vdso_segments (in_kernel inp) sp mbase) = []).
  { unfold vdso_segments. cbv zeta. match goal with |- context [if ?c then _ else _] => destruct c end; reflexivity. }
  rewrite E, app_nil_r. reflexivity.
Qed.

Global Opaque vdso_segments.

Lemma set_rom_ms0 : forall segs tail pc ph en inp,
  set_rom (seg_rom (segs ++ tail)) (ms0 segs pc ph en inp)
  = init_ms (segs ++ tail) pc ph (en_sp en) (en_mmap_base en) (en_draw en) inp.
Proof. reflexivity. Qed.

(* [run_scfg] over [run_segments segs ...], with the ledger of [segs] (the vDSO pair reserves nothing). *)
Lemma run_scfg_eq : forall cfg segs pc ph lim en inp,
  run_scfg cfg (mkImage segs pc ph) lim en inp =
  let vsegs := segs ++ vdso_segments (in_kernel inp) (en_sp en) (en_mmap_base en) in
  let c0 := mkCfg (init_machine_state vsegs pc ph (en_sp en) (en_mmap_base en) (en_draw en) inp) (mo0 segs lim en inp) in
  {| bh_traces := obs_trace_cfg vsegs cfg c0;
     bh_errors := reaches_error_cfg vsegs cfg c0;
     bh_all_errors := all_traces_error_cfg vsegs cfg c0;
     bh_unmodeled := reaches_unmodeled_cfg vsegs cfg c0 |}.
Proof.
  intros cfg segs pc ph lim [sp brk mb rnd] inp. cbn [run_scfg en_sp en_mmap_base en_draw en_brk].
  unfold mo0. cbn [en_sp en_mmap_base en_draw en_brk].
  rewrite <- (run_segments_reserved segs inp sp mb). reflexivity.
Qed.

(* [comment removed for export] *)
(* LPS 08b1429: [Run.valid_input_either] pins [in_channel_reader inp = true]. *)
Lemma vie_reader : forall inp, valid_input_either inp -> in_channel_reader inp = true.
Proof.
  intros inp H. red in H.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  assumption.
Qed.

Lemma run_of_tree : forall {R : Type} segs pc ph lim (t : itree node R) (Q : R -> machine_state -> Prop) en inp,
  valid_entry (mkImage segs pc ph) en inp ->
  in_va_size inp = Sv48 ->
  in_channel_reader inp = true ->
  impl segs (at_node segs) t Q (ms0 segs pc ph en inp) ->
  leaves_unreachable_m nstep t (mo0 segs lim en inp) ->
  tsafe nstep nsafe t (mo0 segs lim en inp) ->
  trace_equiv (bh_traces (run_scfg ACFG (mkImage segs pc ph) lim en inp)) (tree_traces t (mo0 segs lim en inp))
  /\ ~ bh_errors (run_scfg ACFG (mkImage segs pc ph) lim en inp)
  /\ ~ bh_unmodeled (run_scfg ACFG (mkImage segs pc ph) lim en inp)
  /\ ~ dies_by_signal (run_scfg ACFG (mkImage segs pc ph) lim en inp).
Proof.
  intros R segs pc ph lim t Q en inp Hve Hsv48 Hrd Himpl Hleaves Hsafe.
  assert (Hminv : minvR (mo0 segs lim en inp))
    by (split; [exact (mo0_minv segs pc ph lim en inp Hve Hsv48 Hrd) | exact Hrd]).
  rewrite run_scfg_eq. cbv zeta. cbn [bh_traces bh_errors bh_unmodeled].
  set (V := vdso_segments (in_kernel inp) (en_sp en) (en_mmap_base en)).
  destruct (init_behaviour_scfg_eqv ACFG (segs ++ V) pc ph (en_sp en) (en_mmap_base en) (en_draw en) inp (mo0 segs lim en inp))
    as (Htr & Herr & Hunm).
  (* the tree proofs run over [segs]; lift them to the run's [segs ++ V] *)
  pose proof (impl_lift segs V t Q (ms0 segs pc ph en inp) (vdso_nonexec _ _ _) Himpl) as Himpl'.
  rewrite set_rom_ms0 in Himpl'.
  pose proof (nodes_sound (segs ++ V)) as NS.
  assert (SVC : ms_svc_pending (init_ms (segs ++ V) pc ph (en_sp en) (en_mmap_base en) (en_draw en) inp) = None)
    by reflexivity.
  assert (HTR : trace_equiv (obs_trace_cfg (segs ++ V) ACFG
                               (mkCfg (init_machine_state (segs ++ V) pc ph (en_sp en) (en_mmap_base en) (en_draw en) inp)
                                      (mo0 segs lim en inp)))
                            (tree_traces t (mo0 segs lim en inp))).
  { intros tr. rewrite (Htr tr). unfold tree_traces.
    apply (impl_run_traces2 node (segs ++ V) ACFG (at_node (segs ++ V)) nstep nexit minvR nsafe NS t _ _ _
             Himpl' Hleaves (mo0_not_halted _ _ _ _) Hminv Hsafe SVC). }
  split; [exact HTR| split; [| split]].
  - rewrite Herr.
    apply (impl_run_safe2 node (segs ++ V) ACFG (at_node (segs ++ V)) nstep nexit minvR nsafe NS t _ _ _
             Himpl' Hleaves (mo0_not_halted _ _ _ _) Hminv Hsafe SVC).
  - rewrite Hunm.
    apply (impl_run_modeled2 node (segs ++ V) ACFG (at_node (segs ++ V)) nstep nexit minvR nsafe NS t _ _ _
             Himpl' Hleaves (mo0_not_halted _ _ _ _) Hminv Hsafe SVC).
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
Theorem runs_of_trees_gen :
  forall {RS RT : Type}
         (segsS : list Segment) (pcS : N) (phS : PhdrInfo)
         (segsT : list Segment) (pcT : N) (phT : PhdrInfo)
         (tS : prog_tree RS) (tT : prog_tree RT)
         (QS : RS -> machine_state -> Prop) (QT : RT -> machine_state -> Prop),
    tree_ok segsS pcS phS source_alloc_limit tS QS ->
    tree_ok segsT pcT phT target_alloc_limit tT QT ->
    trees_equiv segsS pcS phS segsT pcT phT tS tT ->
    forall enS enT inp,
      valid_entry (mkImage segsS pcS phS) enS inp ->
      valid_entry (mkImage segsT pcT phT) enT inp ->
      valid_input_either inp ->
      let bS := run_scfg ACFG (mkImage segsS pcS phS) source_alloc_limit enS inp in
      let bT := run_scfg ACFG (mkImage segsT pcT phT) target_alloc_limit enT inp in
      (~ bh_errors bS /\ ~ bh_unmodeled bS /\ ~ dies_by_signal bS)
      /\ (~ bh_errors bT /\ ~ bh_unmodeled bT /\ ~ dies_by_signal bT)
      /\ trace_equiv (bh_traces bS) (bh_traces bT).
Proof.
  intros RS RT segsS pcS phS segsT pcT phT tS tT QS QT HS HT HEQ enS enT inp HvS HvT Hvi.
  pose proof (valid_input_either_va_size inp Hvi) as Hsv48.
  destruct (HS enS inp HvS Hvi) as (HimplS & HleavesS & HsafeS).
  destruct (HT enT inp HvT Hvi) as (HimplT & HleavesT & HsafeT).
  destruct (run_of_tree segsS pcS phS source_alloc_limit (tS inp enS) QS enS inp HvS Hsv48 (vie_reader _ Hvi) HimplS HleavesS HsafeS)
    as (HtrS & HerrS & HmodS & HkS).
  destruct (run_of_tree segsT pcT phT target_alloc_limit (tT inp enT) QT enT inp HvT Hsv48 (vie_reader _ Hvi) HimplT HleavesT HsafeT)
    as (HtrT & HerrT & HmodT & HkT).
  cbv zeta. split; [| split]; [split; [| split]; assumption| split; [| split]; assumption|].
  eapply trace_equiv_trans; [exact HtrS|].
  eapply trace_equiv_trans; [exact (HEQ enS enT inp HvS HvT Hvi)|].
  apply trace_equiv_sym. exact HtrT.
Qed.

Theorem strong_universal_from_trees_gen :
  forall {RS RT : Type}
         (segsS : list Segment) (pcS : N) (phS : PhdrInfo)
         (segsT : list Segment) (pcT : N) (phT : PhdrInfo)
         (tS : prog_tree RS) (tT : prog_tree RT)
         (QS : RS -> machine_state -> Prop) (QT : RT -> machine_state -> Prop),
    tree_ok segsS pcS phS source_alloc_limit tS QS ->
    tree_ok segsT pcT phT target_alloc_limit tT QT ->
    trees_equiv segsS pcS phS segsT pcT phT tS tT ->
    strong_universal_T_scfg ACFG (mkImage segsS pcS phS) (mkImage segsT pcT phT).
Proof.
  intros RS RT segsS pcS phS segsT pcT phT tS tT QS QT HS HT HEQ enS enT inp HvS HvT Hvi.
  destruct (runs_of_trees_gen segsS pcS phS segsT pcT phT tS tT QS QT HS HT HEQ enS enT inp HvS HvT
              (valid_input_either_of_valid_input _ Hvi)) as ((_ & HmodS & _) & (HerrT & _ & _) & Htr).
  split.
  - (* [comment removed for export] *) exact HmodS.
  - (* [comment removed for export] *) right. split; [exact Htr| exact HerrT].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Theorem strong_universal_error_free_from_trees_gen :
  forall {RS RT : Type}
         (segsS : list Segment) (pcS : N) (phS : PhdrInfo)
         (segsT : list Segment) (pcT : N) (phT : PhdrInfo)
         (tS : prog_tree RS) (tT : prog_tree RT)
         (QS : RS -> machine_state -> Prop) (QT : RT -> machine_state -> Prop),
    tree_ok segsS pcS phS source_alloc_limit tS QS ->
    tree_ok segsT pcT phT target_alloc_limit tT QT ->
    trees_equiv segsS pcS phS segsT pcT phT tS tT ->
    strong_universal_error_free_T_scfg ACFG (mkImage segsS pcS phS) (mkImage segsT pcT phT).
Proof.
  intros RS RT segsS pcS phS segsT pcT phT tS tT QS QT HS HT HEQ enS enT inp HvS HvT Hvi.
  destruct (runs_of_trees_gen segsS pcS phS segsT pcT phT tS tT QS QT HS HT HEQ enS enT inp HvS HvT
              (valid_input_either_of_valid_input _ Hvi)) as ((HerrS & _ & _) & (HerrT & _ & _) & Htr).
  split; [exact HerrS|]. split; [exact HerrT| exact Htr].
Qed.

(* [comment removed for export] *)
Theorem strong_universal_error_free_budgets_abort_from_trees_gen :
  forall {RS RT : Type}
         (segsS : list Segment) (pcS : N) (phS : PhdrInfo)
         (segsT : list Segment) (pcT : N) (phT : PhdrInfo)
         (tS : prog_tree RS) (tT : prog_tree RT)
         (QS : RS -> machine_state -> Prop) (QT : RT -> machine_state -> Prop),
    tree_ok segsS pcS phS source_alloc_limit tS QS ->
    tree_ok segsT pcT phT target_alloc_limit tT QT ->
    trees_equiv segsS pcS phS segsT pcT phT tS tT ->
    strong_universal_error_free_T_scfg_budgets_abort ACFG ShippedBudgets.lim_source ShippedBudgets.lim_target
      (mkImage segsS pcS phS) (mkImage segsT pcT phT).
Proof.
  intros RS RT segsS pcS phS segsT pcT phT tS tT QS QT HS HT HEQ.
  cbv delta [ShippedBudgets.lim_source ShippedBudgets.lim_target].
  intros enS enT inp HvS HvT Hvi _.
  destruct (runs_of_trees_gen segsS pcS phS segsT pcT phT tS tT QS QT HS HT HEQ enS enT inp HvS HvT
              (valid_input_either_of_valid_input_abort _ Hvi)) as ((HerrS & _ & HkS) & (HerrT & _ & HkT) & Htr).
  split; [split; [exact HerrS| exact HkS]|]. split; [split; [exact HerrT| exact HkT]| exact Htr].
Qed.

(* [comment removed for export] *)
