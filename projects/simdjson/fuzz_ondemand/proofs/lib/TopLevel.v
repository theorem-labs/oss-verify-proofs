(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the run is read over the binary's segments plus the vDSO segments, the initial model carries the vDSO draw, and the input's channel-reader fact feeds the node invariant minvR. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Vdso Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem DecodeC.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import PropExec MState Mem Frame Exec ITree Nodes RegsEquiv FP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Definition prog_tree (R : Type) : Type := ProcInput -> ExecEntry -> itree node R.

Definition ms0 (segs : list Segment) (pc : N) (ph : PhdrInfo)
    (en : ExecEntry) (inp : ProcInput) : machine_state :=
  init_ms segs pc ph (en_sp en) (en_mmap_base en) (en_draw en) inp.

Lemma ms0_eq : forall segs pc ph en inp,
  ms0 segs pc ph en inp =
  MS (mkR_init (en_sp en)) bvmap_empty (Z_to_bv 64 (Z.of_N pc)) (Z_to_bv 32 0) None
     (wrap_mem inp (en_mmap_base en) ph (Z_to_bv 64 (Z.of_N pc)) (en_sp en) (en_draw en)) (seg_rom segs).
Proof. reflexivity. Qed.

(* The run's initial model, as [Run.init_config] builds it: the ledger and
   the launch, with the entry's vDSO draw installed. *)
Definition mo0 (segs : list Segment) (lim : Z) (en : ExecEntry) (inp : ProcInput) : Model :=
  with_vdso (vdso_run_init (ed_vdso (en_draw en)))
    (init_model (segments_reserved segs) (en_brk en) (en_mmap_base en) (en_sp en) lim inp).

Lemma init_config_eq : forall segs pc ph lim en inp,
  init_config segs pc ph (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en) lim inp
  = mkCfg (init_machine_state segs pc ph (en_sp en) (en_mmap_base en) (en_draw en) inp) (mo0 segs lim en inp).
Proof. reflexivity. Qed.

Lemma mo0_fds : forall segs lim en inp,
  m_fds (mo0 segs lim en inp) = m_fds (init_model (segments_reserved segs) (en_brk en) (en_mmap_base en) (en_sp en) lim inp).
Proof. reflexivity. Qed.

Lemma mo0_fs : forall segs lim en inp,
  m_fs (mo0 segs lim en inp) = m_fs (init_model (segments_reserved segs) (en_brk en) (en_mmap_base en) (en_sp en) lim inp).
Proof. reflexivity. Qed.

(* [with_vdso] rebuilds the VM subsystem only; [minv] reads the fd table,
   the file system and the process. *)
Lemma minv_with_vdso : forall v m, minv m -> minv (with_vdso v m).
Proof. intros v m H. unfold minv in *. exact H. Qed.

Lemma mo0_alloc_top : forall segs lim en inp,
  alloc_top (m_vmmaps (mo0 segs lim en inp)) = (bv_unsigned (en_sp en) - stack_max_size)%Z.
Proof. reflexivity. Qed.

Lemma mo0_alloc_top_ceiling : forall segs pc ph lim en inp,
  in_va_size inp = Sv48 ->
  valid_entry (mkImage segs pc ph) en inp ->
  alloc_top (m_vmmaps (mo0 segs lim en inp)) = @alloc_ceiling (ceiling_of_sp (bv_unsigned (en_sp en))).
Proof.
  intros segs pc ph lim en inp Hsv48 Hve. rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hve.
  destruct en as [sp brk mb rnd]. destruct Hve as (Hsp & _ & _ & _). destruct Hsp as (H1 & H2 & H3).
  rewrite mo0_alloc_top. cbn [en_sp]. unfold sp_window_lo, sp_window_hi, stack_max_size in *.
  rewrite ceiling_of_sp_eq; [reflexivity| lia | exact H3].
Qed.

Lemma vie_va_size : forall inp, valid_input_either inp -> in_va_size inp = Sv48.
Proof.
  intros inp H. red in H.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  assumption.
Qed.

Lemma vie_launch : forall inp, valid_input_either inp -> valid_launch inp.
Proof.
  intros inp H. red in H.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  assumption.
Qed.

Lemma mo0_not_halted : forall segs lim en inp, m_halted (mo0 segs lim en inp) = None.
Proof. reflexivity. Qed.

Lemma mo0_minv : forall segs lim en inp, minv (mo0 segs lim en inp).
Proof. intros. apply minv_with_vdso, minv_init. Qed.

(* LPS 08b1429: [Run.valid_input_either] pins [in_channel_reader inp = true]. *)
Lemma vie_reader : forall inp, valid_input_either inp -> in_channel_reader inp = true.
Proof.
  intros inp H. red in H.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  assumption.
Qed.

Lemma mo0_minvR : forall segs lim en inp, in_channel_reader inp = true -> minvR (mo0 segs lim en inp).
Proof. intros segs lim en inp Hr. unfold minvR. split; [apply mo0_minv| exact Hr]. Qed.

Lemma ms0_svc : forall segs pc ph en inp, ms_svc_pending (ms0 segs pc ph en inp) = None.
Proof. reflexivity. Qed.

Remark frm0_init : frm0 (Z_to_bv 32 0).
Proof. reflexivity. Qed.

Lemma ms0_frm0 : forall segs pc ph en inp, frm0 (ms_fcsr (ms0 segs pc ph en inp)).
Proof. intros. exact frm0_init. Qed.

Definition tree_ok {R : Type} (segs : list Segment) (pc : N) (ph : PhdrInfo) (lim : Z)
    (t : prog_tree R) (Q : R -> machine_state -> Prop) : Prop :=
  forall en inp, valid_entry (mkImage segs pc ph) en inp -> valid_input_either inp ->
    impl segs (at_node segs) (t inp en) Q (ms0 segs pc ph en inp)
    /\ leaves_unreachable_m nstep (t inp en) (mo0 segs lim en inp)
    /\ tsafe nstep nsafeU (t inp en) (mo0 segs lim en inp).

Definition tree_traces {R : Type} (t : itree node R) (mo : Model) : list event -> Prop :=
  fun tr => exists full, ttrace nstep nexit t mo full /\ is_prefix tr full.

Definition trees_equiv {RS RT : Type} (segsS : list Segment) (pcS : N) (phS : PhdrInfo)
    (segsT : list Segment) (pcT : N) (phT : PhdrInfo) (tS : prog_tree RS) (tT : prog_tree RT) : Prop :=
  forall enS enT inp,
    valid_entry (mkImage segsS pcS phS) enS inp ->
    valid_entry (mkImage segsT pcT phT) enT inp ->
    valid_input_either inp ->
    forall tS' tT', resolves tS' (tS inp enS) -> resolves tT' (tT inp enT) ->
    trace_equiv (tree_traces tS' (mo0 segsS source_alloc_limit enS inp))
                (tree_traces tT' (mo0 segsT target_alloc_limit enT inp)).

Lemma trees_equiv_of_ttrace : forall {RS RT : Type} (tS : itree node RS) (tT : itree node RT) moS moT,
  (forall tr, ttrace nstep nexit tS moS tr <-> ttrace nstep nexit tT moT tr) ->
  trace_equiv (tree_traces tS moS) (tree_traces tT moT).
Proof.
  intros RS RT tS tT moS moT H tr. unfold tree_traces.
  split; intros (full & Hf & Hp); exists full; split; auto; apply H; exact Hf.
Qed.

(* ------------------------------------------------------------------------- *)
(* The run's segment list.  [Run.run_scfg] reads every step against           *)
(* [run_segments segs inp sp mbase] = [segs ++ vdso_segments ...], and its      *)
(* initial state's ROM is that list's; the tree proofs run over [segs].  The   *)
(* vDSO pair is never executable, so a step that succeeds over [segs]          *)
(* succeeds over [segs ++ tail] with the same result, and the ROM field,       *)
(* which no step reads, is carried along.                                      *)
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

Lemma at_node_lift : forall segs tail n ms,
  at_node segs n ms -> at_node (segs ++ tail) n (set_rom (seg_rom (segs ++ tail)) ms).
Proof.
  intros segs tail n ms H. destruct n; cbn [at_node] in H |- *.
  - destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & _ & H8 & iovs & H9 & H10).
    split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|]. split; [exact H6|].
    split; [reflexivity|]. split; [exact H8|]. exists iovs. split; [apply bytes_at_app_tail; exact H9|].
    clear -H10. induction H10 as [|iov bs l1 l2 HP HF IH]; constructor; [|exact IH].
    destruct HP as (A & B & C). split; [exact A|]. split; [exact B|]. apply bytes_at_app_tail. exact C.
  - destruct H as (H1 & H2 & H3 & H4 & _ & H6 & H7).
    split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [reflexivity|].
    split; [apply bytes_at_app_tail; exact H6| exact H7].
  - destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
    split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|]. split; [exact H6|].
    split; [exact H7|]. apply wr_at_app_tail. exact H8.
  - exact H.
  - exact H.
  - exact H.
  - exact H.
  - exact H.
  - exact H.
  - exact H.
  - exact H.
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
  intros segs tail R t. induction t as [r|n k IH|kc IHc]; intros Q ms NX H; cbn [impl] in H |- *.
  - exact (evt_lift segs tail _ _ ms NX H).
  - eapply evt_mono; [exact (evt_lift segs tail (seg_rom (segs ++ tail)) _ ms NX H)|].
    intros ms' (msp & -> & Hat & Hk). split; [apply at_node_lift; exact Hat|].
    intros rsp. rewrite nret_set_rom. apply IH; [exact NX| apply Hk].
  - destruct H as [z H]. exists z. apply IHc; assumption.
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
     predicate), not [List.filter], so Stdlib's [filter_app] does not match the subterm.
     Sibling of fuzz_utf8/proofs/lib/TopLevel.v:508, fix confirmed by
     a build; this lemma is byte-identical across the seven trees
     (sha256 4a8c908a0656232d of its text). *)
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

Lemma run_of_tree : forall {R : Type} segs pc ph lim (t : itree node R) (Q : R -> machine_state -> Prop) en inp,
  impl segs (at_node segs) t Q (ms0 segs pc ph en inp) ->
  leaves_unreachable_m nstep t (mo0 segs lim en inp) ->
  tsafe nstep nsafeU t (mo0 segs lim en inp) ->
  in_channel_reader inp = true ->
  exists t', resolves t' t
  /\ trace_equiv (bh_traces (run_scfg ACFG (mkImage segs pc ph) lim en inp)) (tree_traces t' (mo0 segs lim en inp))
  /\ ~ bh_errors (run_scfg ACFG (mkImage segs pc ph) lim en inp)
  /\ ~ bh_unmodeled (run_scfg ACFG (mkImage segs pc ph) lim en inp).
Proof.
  intros R segs pc ph lim t Q en inp Himpl Hleaves Hsafe Hrd.
  rewrite run_scfg_eq. cbv zeta. cbn [bh_traces bh_errors bh_unmodeled].
  set (V := vdso_segments (in_kernel inp) (en_sp en) (en_mmap_base en)).
  destruct (init_behaviour_scfg_eqv ACFG (segs ++ V) pc ph (en_sp en) (en_mmap_base en) (en_draw en) inp (mo0 segs lim en inp))
    as (Htr & Herr & _ & Hunm).
  pose proof (impl_lift segs V t Q (ms0 segs pc ph en inp) (vdso_nonexec _ _ _) Himpl) as Himpl'.
  rewrite set_rom_ms0 in Himpl'.
  pose proof (nodes_sound (segs ++ V)) as NS.
  assert (SVC : ms_svc_pending (init_ms (segs ++ V) pc ph (en_sp en) (en_mmap_base en) (en_draw en) inp) = None) by reflexivity.
  destruct (impl_run_traces3 node (segs ++ V) ACFG (at_node (segs ++ V)) nstep nexit minvR nsafeU NS t _ _ _
              Himpl' Hleaves (mo0_not_halted _ _ _ _) (mo0_minvR _ _ _ _ Hrd) Hsafe SVC) as (t' & Hres & Htr').
  exists t'. split; [exact Hres|].
  split; [| split].
  - intros tr. rewrite (Htr tr). unfold tree_traces. exact (Htr' tr).
  - rewrite Herr.
    apply (impl_run_safe2 node (segs ++ V) ACFG (at_node (segs ++ V)) nstep nexit minvR nsafeU NS t _ _ _
             Himpl' Hleaves (mo0_not_halted _ _ _ _) (mo0_minvR _ _ _ _ Hrd) Hsafe SVC).
  - rewrite Hunm.
    apply (impl_run_modeled2 node (segs ++ V) ACFG (at_node (segs ++ V)) nstep nexit minvR nsafeU NS t _ _ _
             Himpl' Hleaves (mo0_not_halted _ _ _ _) (mo0_minvR _ _ _ _ Hrd) Hsafe SVC).
Qed.

Lemma trace_equiv_sym : forall T1 T2, trace_equiv T1 T2 -> trace_equiv T2 T1.
Proof. intros T1 T2 H tr. symmetry. apply H. Qed.

Lemma trace_equiv_trans : forall T1 T2 T3, trace_equiv T1 T2 -> trace_equiv T2 T3 -> trace_equiv T1 T3.
Proof. intros T1 T2 T3 H1 H2 tr. rewrite (H1 tr). apply H2. Qed.

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
  intros RS RT segsS pcS phS segsT pcT phT tS tT QS QT HS HT HEQ enS enT inp HvS HvT Hvi. apply valid_input_either_of_valid_input in Hvi.
  destruct (HS enS inp HvS Hvi) as (HimplS & HleavesS & HsafeS).
  destruct (HT enT inp HvT Hvi) as (HimplT & HleavesT & HsafeT).
  destruct (run_of_tree segsS pcS phS source_alloc_limit (tS inp enS) QS enS inp HimplS HleavesS HsafeS (vie_reader _ Hvi))
    as (tS' & HrS & HtrS & _ & HmodS).
  destruct (run_of_tree segsT pcT phT target_alloc_limit (tT inp enT) QT enT inp HimplT HleavesT HsafeT (vie_reader _ Hvi))
    as (tT' & HrT & HtrT & HerrT & _).
  split.
  -   exact HmodS.
  -
    right. split; [| exact HerrT].
    eapply trace_equiv_trans; [exact HtrS|].
    eapply trace_equiv_trans; [exact (HEQ enS enT inp HvS HvT Hvi tS' tT' HrS HrT)|].
    apply trace_equiv_sym. exact HtrT.
Qed.

Theorem error_free_from_trees_gen :
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
  intros RS RT segsS pcS phS segsT pcT phT tS tT QS QT HS HT HEQ enS enT inp HvS HvT Hvi. apply valid_input_either_of_valid_input in Hvi.
  destruct (HS enS inp HvS Hvi) as (HimplS & HleavesS & HsafeS).
  destruct (HT enT inp HvT Hvi) as (HimplT & HleavesT & HsafeT).
  destruct (run_of_tree segsS pcS phS source_alloc_limit (tS inp enS) QS enS inp HimplS HleavesS HsafeS (vie_reader _ Hvi))
    as (tS' & HrS & HtrS & HerrS & _).
  destruct (run_of_tree segsT pcT phT target_alloc_limit (tT inp enT) QT enT inp HimplT HleavesT HsafeT (vie_reader _ Hvi))
    as (tT' & HrT & HtrT & HerrT & _).
  split; [exact HerrS|]. split; [exact HerrT|].
  eapply trace_equiv_trans; [exact HtrS|].
  eapply trace_equiv_trans; [exact (HEQ enS enT inp HvS HvT Hvi tS' tT' HrS HrT)|].
  apply trace_equiv_sym. exact HtrT.
Qed.

Theorem error_free_scfg_from_trees_gen :
  forall {RS RT : Type}
         (segsS : list Segment) (pcS : N) (phS : PhdrInfo)
         (segsT : list Segment) (pcT : N) (phT : PhdrInfo)
         (tS : prog_tree RS) (tT : prog_tree RT)
         (QS : RS -> machine_state -> Prop) (QT : RT -> machine_state -> Prop),
    tree_ok segsS pcS phS source_alloc_limit tS QS ->
    tree_ok segsT pcT phT target_alloc_limit tT QT ->
    trees_equiv segsS pcS phS segsT pcT phT tS tT ->
    strong_universal_error_free_T_scfg ACFG
      (mkImage segsS pcS phS) (mkImage segsT pcT phT).
Proof.
  intros. eapply error_free_from_trees_gen; eassumption.
Qed.

Theorem strong_universal_scfg_from_trees_gen :
  forall {RS RT : Type}
         (segsS : list Segment) (pcS : N) (phS : PhdrInfo)
         (segsT : list Segment) (pcT : N) (phT : PhdrInfo)
         (tS : prog_tree RS) (tT : prog_tree RT)
         (QS : RS -> machine_state -> Prop) (QT : RT -> machine_state -> Prop),
    tree_ok segsS pcS phS source_alloc_limit tS QS ->
    tree_ok segsT pcT phT target_alloc_limit tT QT ->
    trees_equiv segsS pcS phS segsT pcT phT tS tT ->
    strong_universal_T_scfg ACFG
      (mkImage segsS pcS phS) (mkImage segsT pcT phT).
Proof.
  intros. eapply strong_universal_from_trees_gen; eassumption.
Qed.

From OSSVerify.simdjson.fuzz_ondemand.images Require Import Plain.
From OSSVerify.simdjson.fuzz_ondemand.images Require Import Ubsan.
Module SrcP := Plain.

Theorem strong_universal_from_trees :
  forall (tS tT : prog_tree (Exc.exc unit)) (postS postT : unit -> machine_state -> Prop),
  tree_ok SrcP.M.loaded_segments SrcP.M.init_pc SrcP.M.phdrs
          source_alloc_limit tS (epost postS) ->
  tree_ok Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs
          target_alloc_limit tT (epost postT) ->
  trees_equiv SrcP.M.loaded_segments SrcP.M.init_pc SrcP.M.phdrs
              Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs
              tS tT ->
  strong_universal_T_scfg ACFG
    (mkImage SrcP.M.loaded_segments SrcP.M.init_pc SrcP.M.phdrs)
    (mkImage Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs).
Proof. intros tS tT postS postT. apply strong_universal_from_trees_gen. Qed.

Theorem error_free_from_trees :
  forall (tS tT : prog_tree (Exc.exc unit)) (postS postT : unit -> machine_state -> Prop),
  tree_ok SrcP.M.loaded_segments SrcP.M.init_pc SrcP.M.phdrs
          source_alloc_limit tS (epost postS) ->
  tree_ok Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs
          target_alloc_limit tT (epost postT) ->
  trees_equiv SrcP.M.loaded_segments SrcP.M.init_pc SrcP.M.phdrs
              Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs
              tS tT ->
  strong_universal_error_free_T_scfg ACFG
    (mkImage SrcP.M.loaded_segments SrcP.M.init_pc SrcP.M.phdrs)
    (mkImage Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs).
Proof. intros tS tT postS postT. apply error_free_from_trees_gen. Qed.

Theorem error_free_scfg_from_trees :
  forall (tS tT : prog_tree (Exc.exc unit)) (postS postT : unit -> machine_state -> Prop),
  tree_ok SrcP.M.loaded_segments SrcP.M.init_pc SrcP.M.phdrs
          source_alloc_limit tS (epost postS) ->
  tree_ok Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs
          target_alloc_limit tT (epost postT) ->
  trees_equiv SrcP.M.loaded_segments SrcP.M.init_pc SrcP.M.phdrs
              Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs
              tS tT ->
  strong_universal_error_free_T_scfg ACFG
    (mkImage SrcP.M.loaded_segments SrcP.M.init_pc SrcP.M.phdrs)
    (mkImage Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs).
Proof. intros tS tT postS postT. apply error_free_scfg_from_trees_gen. Qed.

