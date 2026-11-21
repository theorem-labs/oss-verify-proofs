(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(** * Common.ExitSim — reusable trace-semantics infrastructure for
      "exit-only" binaries (no observable I/O before the terminating
      exit/exit_group syscall), built on the star-based LinuxProcessSem.Run
      semantics.

    TRUST BOUNDARY: this file is part of the shared proof library, not
    the trusted specification.  It is image-INDEPENDENT: every lemma is generic over the
    loaded segments [segs] and the exit code [code], so it is shared by all
    exit-only proofs.

    Exit codes and syscall numbers are [word = bv 64], memory bytes are
    [byte = bv 8], and the exit-number dispatch tests are [Z.eqb] over
    [bv_unsigned] (mirroring the Specs.v dispatcher).  [N.land code 255]
    is [bv_and code (Z_to_bv 64 255)].  Stack-offset bookkeeping in the
    overlay lemmas is characterized in [Z] over unsigned values, so no
    no-wrap side conditions are needed.

    STRUCTURE.  An exit-only binary runs a finite, deterministic straight
    line of machine instructions and then executes [exit]/[exit_group].  We
    capture that straight line with an inductive [to_exit segs code ms]
    ("[ms] deterministically reaches an exit ecall carrying code [code]"),
    prove it holds by a [vm_compute]-checkable Fixpoint [sim_c], read it
    as the omni judgment [to_exit_exec] ([OmniRun.exec] with the exact
    trace and exit code as postcondition), and from that one judgment
    derive:

    - [obs_trace] of the run is exactly the prefixes of
      [[ExitEv (bv_and code (Z_to_bv 64 255)) (in_fs inp)]]  (exit_obs_iff), and
    - the run can NEVER take the explicit error transition
      ([~ reaches_error]; exit_no_error_run).

    The two facts combine into the [Equivalence.equiv] the [Equivalence]
    functor grades (exit_strong_equiv): two exit-only binaries that reach
    the same exit code are observably equivalent (neither errors). *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Vdso Run OmniRun.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit Require Import SimInv.

Import ListNotations.
Open Scope bv_scope.

(* ========================================================================= *)
(* Exit-syscall spec facts, derived directly from the relational spec.       *)
(*                                                                           *)
(* For a SyscallInput whose number is 93 (exit) or 94 (exit_group) the       *)
(* dispatcher routes to [exit_spec], which has EXACTLY ONE outcome shape:    *)
(* halt the model at [bv_and a0 255], no writes, no events.  We read those   *)
(* facts below keep this proof infrastructure independent of the executable  *)
(* checker representation.                                                   *)
(* ========================================================================= *)

Definition is_exit_no (no : word) : Prop :=
  bv_unsigned no = 93%Z \/ bv_unsigned no = 94%Z.

Lemma syscall_spec_exit : forall i m o,
  is_exit_no (in_sysno i) ->
  syscall_spec i m o <-> exit_spec (in_arg i 0) i m o.
Proof.
  intros i m o [E|E]; unfold syscall_spec, dispatch; rewrite E; reflexivity.
Qed.

(** The unique admissible exit outcome exists. *)
Lemma exit_dispatch_ok : forall i m,
  is_exit_no (in_sysno i) ->
  syscall_spec i m
    (Ok (mkEffect (Z_to_bv 64 0) [] [])
        (with_halted (bv_and (in_arg i 0) (Z_to_bv 64 255)) m) []).
Proof.
  intros i m Hno. apply (proj2 (syscall_spec_exit i m _ Hno)).
  unfold exit_spec, set_halted, ret_only, modify, bind, pure. cbn.
  eexists tt, (with_halted (bv_and (in_arg i 0) (Z_to_bv 64 255)) m),
    [], []. repeat split; reflexivity.
Qed.

(** Every admissible exit outcome IS that unique one. *)
Lemma exit_dispatch_ok_inv : forall i m eff m' evs,
  is_exit_no (in_sysno i) ->
  syscall_spec i m (Ok eff m' evs) ->
  eff = mkEffect (Z_to_bv 64 0) [] [] /\
  m' = with_halted (bv_and (in_arg i 0) (Z_to_bv 64 255)) m /\ evs = [].
Proof.
  intros i m eff m' evs Hno Hspec.
  apply (proj1 (syscall_spec_exit i m _ Hno)) in Hspec.
  unfold exit_spec, set_halted, ret_only, modify, bind, pure in Hspec. cbn in Hspec.
  sys_destruct. rewrite app_nil_l in *. repeat split; congruence.
Qed.

(** Exit never takes the error transition. *)
Lemma exit_dispatch_no_unmodeled : forall i m,
  is_exit_no (in_sysno i) -> ~ syscall_spec i m Unmodeled.
Proof.
  intros i m Hno Hspec.
  apply (proj1 (syscall_spec_exit i m _ Hno)) in Hspec.
  unfold exit_spec, set_halted, ret_only, modify, bind, pure in Hspec. cbn in Hspec.
  sys_destruct.
Qed.

(** [in_arg (sys_input segs ms x8) 0] is [ms_gpr ms 0] (a0). *)
Lemma in_arg0_sys_input : forall segs ms x8,
  in_arg (sys_input segs ms x8) 0 = ms_gpr ms 0.
Proof. reflexivity. Qed.

(** [in_sysno (sys_input segs ms x8) = x8]. *)
Lemma in_sysno_sys_input : forall segs ms x8,
  in_sysno (sys_input segs ms x8) = x8.
Proof. reflexivity. Qed.

Section WithSegs.
Variable segs : list Segment.
Variable code : word.

(* ========================================================================= *)
(* to_exit: the deterministic straight line to the exit ecall.               *)
(* ========================================================================= *)

Inductive to_exit : machine_state -> Prop :=
| te_here : forall ms x8,
    ms_svc_pending ms = Some x8 ->
    is_exit_no x8 ->
    ms_gpr ms 0 = code ->
    to_exit ms
| te_step : forall ms ms',
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    to_exit ms' ->
    to_exit ms.

(* ========================================================================= *)
(* sim_c: a fuel-bounded executable witness for [to_exit], closed by         *)
(* vm_compute for a concrete straight-line binary.                           *)
(* ========================================================================= *)

Fixpoint sim_c (fuel : nat) (ms : machine_state) : bool :=
  match fuel with
  | O => false
  | S fuel' =>
    match ms_svc_pending ms with
    | Some x8 => ((bv_unsigned x8 =? 93)%Z || (bv_unsigned x8 =? 94)%Z)
                 && bv_eqb (ms_gpr ms 0) code
    | None =>
      match RiscvSemantics.step segs ms with
      | MachineOk ms' => sim_c fuel' ms'
      | MachineFault | MachineUnmodeled => false
      end
    end
  end.

Lemma sim_c_to_exit : forall fuel ms, sim_c fuel ms = true -> to_exit ms.
Proof.
  induction fuel as [|fuel IH]; intros ms H; [discriminate|].
  cbn in H. destruct (ms_svc_pending ms) as [x8|] eqn:Hsvc.
  - apply andb_true_iff in H as [Hx8 Hgpr].
    apply bv_eqb_eq in Hgpr.
    eapply te_here; eauto.
    apply orb_true_iff in Hx8. destruct Hx8 as [H|H]; apply Z.eqb_eq in H;
      [left|right]; exact H.
  - destruct (RiscvSemantics.step segs ms) as [ms'| |] eqn:Hstep;
      [|discriminate|discriminate].
    eapply te_step; eauto.
Qed.

(* ========================================================================= *)
(* Propositional-execution bridges into [sim_c].                             *)
(*                                                                           *)
(* When the source reads argv memory we cannot [vm_compute] [sim_c]       *)
(* (argv is symbolic).  Instead we chain the per-instruction [step_*]        *)
(* lemmas from [Common.PropExec] one [sim_c] step at a time via [sim_step],  *)
(* and close at the terminating ecall via [sim_ecall_exit].                  *)
(* ========================================================================= *)

(** One executable step: an ordinary (non-syscall) instruction. *)
Lemma sim_step : forall fuel ms ms',
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  sim_c fuel ms' = true ->
  sim_c (S fuel) ms = true.
Proof.
  intros fuel ms ms' Hsvc Hstep Hrec.
  cbn [sim_c]. rewrite Hsvc. cbv beta iota. rewrite Hstep. exact Hrec.
Qed.

(** A configuration whose pending syscall is exit/exit_group with a0 = code
    passes [sim_c] immediately.  Scrutinee stays a variable so [cbn] does not
    over-reduce the register lookups. *)
Lemma sim_c_exit_now : forall fuel ms x8,
  ms_svc_pending ms = Some x8 ->
  ((bv_unsigned x8 =? 93)%Z || (bv_unsigned x8 =? 94)%Z) = true ->
  bv_eqb (ms_gpr ms 0) code = true ->
  sim_c (S fuel) ms = true.
Proof.
  intros fuel ms x8 Hsvc Hx8 Hcode.
  cbn [sim_c]. rewrite Hsvc. cbv beta iota. rewrite Hx8. cbn [andb]. exact Hcode.
Qed.

(** Closing the run: at [ms] (svc not pending), the next instruction is the
    [ecall] (0x73); a7 selects exit/exit_group and a0 carries [code]. *)
Lemma sim_ecall_exit : forall fuel ms,
  ms_svc_pending ms = None ->
  fetch_word segs (ms_pc ms) = Some 0x73 ->
  ((bv_unsigned (ms_reg ms 17) =? 93)%Z || (bv_unsigned (ms_reg ms 17) =? 94)%Z) = true ->
  bv_eqb (ms_gpr ms 0) code = true ->
  sim_c (S (S fuel)) ms = true.
Proof.
  intros fuel ms Hsvc Hfetch Hcheck Hcode.
  set (ms1 := {| ms_regs := ms_regs ms; ms_fregs := ms_fregs ms; ms_pc_val := ms_pc_val ms;
                 ms_svc_pending := Some (ms_reg ms 17); ms_resv := ms_resv ms; ms_fcsr := ms_fcsr ms;
                 ms_mem := ms_mem ms; ms_rom := ms_rom ms |}).
  apply (sim_step (S fuel) ms ms1 Hsvc).
  - change (drop_access_report (step_accesses segs ms) = MachineOk ms1).
    unfold step_accesses. rewrite Hfetch. unfold ms1. reflexivity.
  - apply (sim_c_exit_now fuel ms1 (ms_reg ms 17)).
    + subst ms1. reflexivity.
    + exact Hcheck.
    + exact Hcode.
Qed.

(* ========================================================================= *)
(* One-step inversions of [sstep] on the two kinds of on-path configs.       *)
(* ========================================================================= *)

(** From a non-syscall state that steps to [ms'], the ONLY transition is the
    deterministic instruction step; no events, no error. *)
Lemma sstep_instr_inv : forall ms model ms' evs st,
  m_vm_lazy model = [] ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  sstep segs (mkCfg ms model) evs st ->
  evs = [] /\ st = SNext (mkCfg ms' model).
Proof.
  intros ms model ms' evs st Hlazy Hsvc Hstep Hss.
  inversion Hss; subst.
  - (* sstep_instr *)
    match goal with H : mi_account_step segs ms model = MachineOk _ |- _ =>
      rewrite (mi_account_step_no_lazy segs ms model Hlazy) in H;
      rewrite Hstep in H; inversion H; subst end.
    split; reflexivity.
  - (* sstep_instr_fault *)
    match goal with H : mi_account_step segs ms model = MachineFault |- _ =>
      rewrite (mi_account_step_no_lazy segs ms model Hlazy) in H;
      rewrite Hstep in H; discriminate end.
  - (* sstep_instr_unmodeled *)
    match goal with H : mi_account_step segs ms model = MachineUnmodeled |- _ =>
      rewrite (mi_account_step_no_lazy segs ms model Hlazy) in H;
      rewrite Hstep in H; discriminate end.
  - (* sstep_vdso_call: its first premise is the same [MachineUnmodeled] *)
    match goal with H : mi_account_step segs ms model = MachineUnmodeled |- _ =>
      rewrite (mi_account_step_no_lazy segs ms model Hlazy) in H;
      rewrite Hstep in H; discriminate end.
  - (* sstep_vdso_materialization_fault *)
    match goal with H : mi_account_step segs ms model = MachineUnmodeled |- _ =>
      rewrite (mi_account_step_no_lazy segs ms model Hlazy) in H;
      rewrite Hstep in H; discriminate end.
  - (* sstep_vdso_unmodeled *)
    match goal with H : mi_account_step segs ms model = MachineUnmodeled |- _ =>
      rewrite (mi_account_step_no_lazy segs ms model Hlazy) in H;
      rewrite Hstep in H; discriminate end.
  - (* sstep_syscall *) congruence.
  - (* sstep_syscall_materialization_fault *) congruence.
  - (* sstep_exit *) congruence.
  - (* sstep_killed *) congruence.
  - (* sstep_syscall_unmodeled *) congruence.
Qed.

(** From an exit ecall config, the ONLY transition is [sstep_exit]: it emits
    the single [ExitEv] and halts the model. *)
Lemma sstep_exit_inv : forall ms model x8 evs st,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  is_exit_no x8 ->
  sstep segs (mkCfg ms model) evs st ->
  evs = [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)] /\
  st = SNext (mkCfg ms (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model)).
Proof.
  intros ms model x8 evs st Hh Hsvc Hx8 Hss.
  inversion Hss; subst; try congruence.
  - (* sstep_syscall : model' halted, contradiction with m_halted model' = None *)
    (* the accessors do not reduce through a setter on their own,
       so normalise the hypotheses before matching on their shape *)
    autorewrite with model in *.
    exfalso.
    match goal with
    | H3 : syscall_spec (sys_input segs ms ?x) model (Ok _ ?model' _),
      H2 : ms_svc_pending ms = Some ?x,
      H6 : m_halted ?model' = None |- _ =>
      assert (Hxe : is_exit_no (in_sysno (sys_input segs ms x)))
        by (rewrite in_sysno_sys_input; replace x with x8 by congruence; exact Hx8);
      apply (exit_dispatch_ok_inv _ _ _ _ _ Hxe) in H3;
      destruct H3 as (_ & Hm & _); rewrite Hm in H6;
      autorewrite with model in H6; discriminate
    end.
  - (* sstep_syscall_materialization_fault: same pre-materialization model *)
    autorewrite with model in *.
    exfalso.
    match goal with
    | H3 : syscall_spec (sys_input segs ms ?x) model (Ok _ ?model' _),
      H2 : ms_svc_pending ms = Some ?x,
      H6 : m_halted ?model' = None |- _ =>
      assert (Hxe : is_exit_no (in_sysno (sys_input segs ms x)))
        by (rewrite in_sysno_sys_input; replace x with x8 by congruence; exact Hx8);
      apply (exit_dispatch_ok_inv _ _ _ _ _ Hxe) in H3;
      destruct H3 as (_ & Hm & _); rewrite Hm in H6;
      autorewrite with model in H6; discriminate
    end.
  - (* sstep_exit *)
    autorewrite with model in *.
    match goal with
    | H3 : syscall_spec (sys_input segs ms ?x) model (Ok _ ?model' ?evs0),
      H2 : ms_svc_pending ms = Some ?x,
      H6 : m_halted ?model' = Some ?code |- _ =>
      assert (Hxe : is_exit_no (in_sysno (sys_input segs ms x)))
        by (rewrite in_sysno_sys_input; replace x with x8 by congruence; exact Hx8);
      apply (exit_dispatch_ok_inv _ _ _ _ _ Hxe) in H3;
      destruct H3 as (Heff & Hm & Hevs);
      rewrite in_arg0_sys_input in Hm;
      subst evs0 model';
      assert (Hcode : code = bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
        by (autorewrite with model in H6; congruence);
      subst code
    end.
    cbn. split; reflexivity.
  - (* sstep_killed: the exit arm's post-model is [State.with_halted]'s,
       whose [State.m_killed] is [None] by construction *)
    exfalso.
    match goal with
    | H3 : syscall_spec (sys_input segs ms ?x) model (Ok _ ?model' _),
      H2 : ms_svc_pending ms = Some ?x,
      H6 : m_killed ?model' = Some _ |- _ =>
      assert (Hxe : is_exit_no (in_sysno (sys_input segs ms x)))
        by (rewrite in_sysno_sys_input; replace x with x8 by congruence; exact Hx8);
      apply (exit_dispatch_ok_inv _ _ _ _ _ Hxe) in H3;
      destruct H3 as (_ & Hm & _); rewrite Hm in H6;
      autorewrite with model in H6; discriminate
    end.
  - (* sstep_syscall_unmodeled *)
    exfalso.
    match goal with
    | H3 : syscall_spec (sys_input segs ms ?x) model Unmodeled,
      H2 : ms_svc_pending ms = Some ?x |- _ =>
      eapply exit_dispatch_no_unmodeled; [| exact H3];
      rewrite in_sysno_sys_input; replace x with x8 by congruence; exact Hx8
    end.
Qed.

(** A run cannot leave a halted config. *)
Lemma star_halted_nil : forall c tr c',
  m_halted (cfg_model c) <> None -> star segs c tr c' -> tr = [] /\ c' = c.
Proof.
  intros c tr c' Hh Hstar. inversion Hstar as [|c1 evs c2 tr2 c3 Hss Hstar2]; subst.
  - split; reflexivity.
  - exfalso. destruct c as [ms model]. cbn in Hh.
    inversion Hss; subst; cbn in Hh; congruence.
Qed.

(* ========================================================================= *)
(* The omni reading: one induction over [to_exit] gives the exact trace,     *)
(* termination and error-freedom at once.                                    *)
(* ========================================================================= *)

Definition exit_post (fs : Fs.Fs) : post :=
  fun tr o => tr = [ExitEv (bv_and code (Z_to_bv 64 255)) fs]
              /\ exits_with (bv_and code (Z_to_bv 64 255)) tr o.

Lemma to_exit_exec : forall ms model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  to_exit ms ->
  OmniRun.exec segs (mkCfg ms model) (exit_post (m_fs model)).
Proof.
  intros ms model Hh Hlazy Hte.
  induction Hte as [ms x8 Hsvc Hx8 Hgpr | ms ms' Hsvc Hstep Hte IH].
  - (* te_here: the one transition is the exit, into the halted configuration *)
    apply (exec_step_only segs _ _
             [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)]
             (mkCfg ms (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model))).
    + replace [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)]
        with ([] ++ [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
                       (m_fs (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model))])
        by (cbn; reflexivity).
      apply (sstep_exit segs ms model x8 (mkEffect (Z_to_bv 64 0) [] [])
               (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model) []
               (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))).
      * exact Hh.
      * exact Hsvc.
      * apply (exit_dispatch_ok (sys_input segs ms x8) model).
        rewrite in_sysno_sys_input. exact Hx8.
      * cbn. reflexivity.
      * apply m_killed_with_halted.
    + intros evs st Hss. exact (sstep_exit_inv ms model x8 evs st Hh Hsvc Hx8 Hss).
    + apply exec_halt.
      * cbn. rewrite m_halted_with_halted. discriminate.
      * unfold exit_post. cbn beta. rewrite app_nil_r, Hgpr. split; [reflexivity |].
        cbn [exits_with cfg_model]. split;
          [ rewrite m_halted_with_halted; reflexivity
          | apply m_killed_with_halted ].
  - (* te_step: one silent instruction *)
    apply (exec_step_only segs _ _ [] (mkCfg ms' model)).
    + apply (sstep_instr segs ms model ms' model); [exact Hh | exact Hsvc |].
      rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
    + intros evs st Hss. exact (sstep_instr_inv ms model ms' evs st Hlazy Hsvc Hstep Hss).
    + eapply exec_conseq; [exact IH |]. intros tr o H. cbn [app]. exact H.
Qed.

(* ========================================================================= *)
(* Trace characterization of an exit-only run — corollaries of [to_exit_exec]. *)
(* ========================================================================= *)

Lemma to_exit_star_only : forall ms model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  to_exit ms ->
  forall tr c, star segs (mkCfg ms model) tr c ->
    tr = [] \/ tr = [ExitEv (bv_and code (Z_to_bv 64 255)) (m_fs model)].
Proof.
  intros ms model Hh Hlazy Hte tr c Hstar.
  destruct (exec_realizes _ _ _ (exec_star _ _ _ _ _ (to_exit_exec ms model Hh Hlazy Hte) Hstar))
    as (tr' & o & _ & HQ).
  unfold exit_post in HQ. cbn beta in HQ. destruct HQ as (Heq & _).
  destruct (app_eq_unit _ _ Heq) as [(-> & _) | (-> & _)]; [left | right]; reflexivity.
Qed.

Lemma to_exit_star_admits : forall ms model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  to_exit ms ->
  exists c, star segs (mkCfg ms model)
              [ExitEv (bv_and code (Z_to_bv 64 255)) (m_fs model)] c.
Proof.
  intros ms model Hh Hlazy Hte.
  destruct (exec_realizes _ _ _ (to_exit_exec ms model Hh Hlazy Hte))
    as (tr & [c' | c'] & Hm & Heq & Hx); [| destruct Hx].
  subst tr. destruct (mexec_halt_star _ _ _ _ Hm c' eq_refl) as (Hstar & _).
  exists c'. exact Hstar.
Qed.

(* ========================================================================= *)
(* No-error characterization: no reachable config takes the error step.      *)
(* ========================================================================= *)

(** On-path invariant: a reachable config is either still on the straight
    line (model not halted, [to_exit] holds) or already halted. *)
Definition on_path (c : config) : Prop :=
  (m_halted (cfg_model c) = None /\ m_vm_lazy (cfg_model c) = [] /\
   to_exit (cfg_ms c))
  \/ m_halted (cfg_model c) <> None.

Lemma on_path_step : forall c evs c',
  on_path c -> sstep segs c evs (SNext c') -> on_path c'.
Proof.
  intros [ms model] evs [ms' model'] Hop Hss.
  unfold on_path in *; cbn in Hop |- *.
  destruct Hop as [[Hh [Hlazy Hte]] | Hh].
  - destruct Hte as [ms0 x8 Hsvc Hx8 Hgpr | ms0 ms0' Hsvc Hstep Hte].
    + (* te_here *)
      destruct (sstep_exit_inv ms0 model x8 evs (SNext (mkCfg ms' model'))
                  Hh Hsvc Hx8 Hss) as [_ Hc'].
      inversion Hc'; subst. right. cbn. discriminate.
    + (* te_step *)
      destruct (sstep_instr_inv ms0 model ms0' evs (SNext (mkCfg ms' model'))
                  Hlazy Hsvc Hstep Hss) as [_ Hc'].
      inversion Hc'; subst. left. repeat split; assumption.
  - (* already halted: no sstep possible *)
    exfalso. inversion Hss; subst; cbn in Hh; congruence.
Qed.

Lemma on_path_no_error : forall c evs, on_path c -> ~ sstep segs c evs SError.
Proof.
  intros [ms model] evs Hop Hss.
  unfold on_path in *; cbn in Hop.
  destruct Hop as [[Hh [Hlazy Hte]] | Hh].
  - destruct Hte as [ms0 x8 Hsvc Hx8 Hgpr | ms0 ms0' Hsvc Hstep Hte].
    + destruct (sstep_exit_inv ms0 model x8 evs SError Hh Hsvc Hx8 Hss) as [_ Hc'].
      discriminate.
    + destruct (sstep_instr_inv ms0 model ms0' evs SError Hlazy Hsvc Hstep Hss) as [_ Hc'].
      discriminate.
  - inversion Hss; subst; cbn in Hh; congruence.
Qed.

Lemma star_on_path : forall c tr c',
  on_path c -> star segs c tr c' -> on_path c'.
Proof. exact (star_inv segs on_path on_path_step). Qed.

Lemma to_exit_no_error : forall ms model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  to_exit ms ->
  ~ reaches_error segs (mkCfg ms model).
Proof.
  intros ms model Hh Hlazy Hte. apply exec_no_error.
  eapply exec_conseq; [exact (to_exit_exec ms model Hh Hlazy Hte) |].
  intros tr o (_ & Hx). exact (exits_with_never_errors _ _ _ Hx).
Qed.

End WithSegs.

(* ========================================================================= *)
(* Overlay + enumerate: closing [sim_c] for binaries that read only argc.     *)
(*                                                                           *)
(* The source binary reads argc (the first 8 stack bytes) and branches on *)
(* it.  To let [vm_compute] close [sim_c] for ALL argv, we replace the        *)
(* symbolic stack memory by an "overlay": the first 8 bytes are the concrete  *)
(* little-endian encoding of [argc], every other address defers to an         *)
(* unevaluated base function.  Enumerating argc over its valid range          *)
(* (0..1024, from [valid_argv]) then discharges every case by computation,    *)
(* because the binary only ever reads those 8 concrete bytes.  All lemmas are *)
(* image-INDEPENDENT (generic over segs/init_pc/init_sp/argv/envp).   *)
(*                                                                           *)
(* The address tests are [Z.eqb] over unsigned values:                        *)
(* [bv_unsigned sp + k] cannot wrap in [Z], so the overlay equals the real    *)
(* initial memory for EVERY [sp], including the (unreachable) top-of-address- *)
(* space corner where [sp + k] would wrap under [bv] addition.               *)
(* ========================================================================= *)

Definition overlay_argc_bytes (sp : word) (argc : nat)
    (base_mem : word -> option byte) : word -> option byte :=
  let bytes := word_le8 (nat_to_word argc) in
  fun addr =>
    if (bv_unsigned addr =? bv_unsigned sp)%Z then nth_error bytes 0
    else if (bv_unsigned addr =? bv_unsigned sp + 1)%Z then nth_error bytes 1
    else if (bv_unsigned addr =? bv_unsigned sp + 2)%Z then nth_error bytes 2
    else if (bv_unsigned addr =? bv_unsigned sp + 3)%Z then nth_error bytes 3
    else if (bv_unsigned addr =? bv_unsigned sp + 4)%Z then nth_error bytes 4
    else if (bv_unsigned addr =? bv_unsigned sp + 5)%Z then nth_error bytes 5
    else if (bv_unsigned addr =? bv_unsigned sp + 6)%Z then nth_error bytes 6
    else if (bv_unsigned addr =? bv_unsigned sp + 7)%Z then nth_error bytes 7
    else base_mem addr.

Lemma stm_at (sp : word) (bytes : list byte) (addr : word) (i : nat) :
  (i < length bytes)%nat ->
  bv_unsigned addr = (bv_unsigned sp + Z.of_nat i)%Z ->
  stack_to_mem sp bytes addr = nth_error bytes i.
Proof.
  intros Hi Haddr. unfold stack_to_mem. rewrite Haddr. cbv beta zeta.
  destruct (Z.leb (bv_unsigned sp) (bv_unsigned sp + Z.of_nat i)) eqn:E1.
  2: { apply Z.leb_gt in E1; lia. }
  replace (bv_unsigned sp + Z.of_nat i - bv_unsigned sp)%Z with (Z.of_nat i) by lia.
  destruct (Z.ltb (Z.of_nat i) (Z.of_nat (length bytes))) eqn:E2.
  - rewrite Nat2Z.id. reflexivity.
  - apply Z.ltb_ge in E2. lia.
Qed.

Lemma word_le8_length : forall v, length (word_le8 v) = 8%nat.
Proof. intro v. reflexivity. Qed.

(** The block still OPENS with argc: [create_elf_tables]
    (fs/binfmt_elf.c, Linux v6.18.46, commit ) writes it at
    the entry stack pointer, below the pointer arrays.  What the new
    layout moved is everything above the auxv, not this word.  The
    image IS the block now, so there is no page tail to see past. *)
Lemma build_stack_starts_with_argc :
  forall inp mbase ph entry (sp : word) draw,
  exists rest,
    entry_stack_image inp mbase ph entry sp draw =
    word_le8 (nat_to_word (length (in_argv inp))) ++ rest.
Proof.
  intros inp mbase ph entry sp draw.
  unfold entry_stack_image, build_stack_bytes, len_word, nat_to_word.
  cbv zeta.
  destruct (string_addrs _ (in_argv inp)) as [? ?].
  destruct (string_addrs _ (in_envp inp)) as [? ?].
  eexists. exact (eq_sym (app_assoc _ _ _)).
Qed.

Lemma build_stack_min_length : forall inp mbase ph entry (sp : word) draw,
  (8 <= length (entry_stack_image inp mbase ph entry sp draw))%nat.
Proof.
  intros inp mbase ph entry sp draw.
  destruct (build_stack_starts_with_argc inp mbase ph entry sp draw)
    as [rest Hr].
  rewrite Hr, length_app, word_le8_length. lia.
Qed.

(** The [i]-th byte of the initial stack memory (i < 8) is the [i]-th byte of
    the little-endian argc.  Goes through this repo's zero-fallback wrapper.
    The address is characterized by its unsigned value (no wrap in [Z]). *)
Lemma init_first8 :
  forall segs init_pc ph init_sp mbase init_rnd inp addr i, (i < 8)%nat ->
  bv_unsigned addr = (bv_unsigned init_sp + Z.of_nat i)%Z ->
  ms_mem (init_machine_state segs init_pc ph init_sp mbase init_rnd inp) addr =
  nth_error (word_le8 (nat_to_word (length (in_argv inp)))) i.
Proof.
  intros segs init_pc ph init_sp mbase init_rnd inp addr i Hi Haddr.
  assert (Hstk : stack_to_mem init_sp
                   (entry_stack_image inp mbase ph
                      (Z_to_bv 64 (Z.of_N init_pc)) init_sp init_rnd) addr
                 = nth_error (word_le8 (nat_to_word (length (in_argv inp)))) i).
  { rewrite (stm_at init_sp _ addr i);
      [ | pose proof (build_stack_min_length inp mbase ph
                        (Z_to_bv 64 (Z.of_N init_pc)) init_sp init_rnd); lia
        | exact Haddr ].
    destruct (build_stack_starts_with_argc inp mbase ph
                (Z_to_bv 64 (Z.of_N init_pc)) init_sp init_rnd) as [rest Hr].
    rewrite Hr. apply nth_error_app1. rewrite word_le8_length. lia. }
  change (ms_mem (init_machine_state segs init_pc ph init_sp mbase init_rnd inp)
            addr)
    with (match stack_to_mem init_sp
                  (entry_stack_image inp mbase ph
                     (Z_to_bv 64 (Z.of_N init_pc)) init_sp init_rnd) addr with
          | Some b => Some b
          | None =>
              if andb (Z.leb (stack_window_lo (in_kernel inp) mbase init_rnd)
                             (bv_unsigned addr))
                      (Z.ltb (bv_unsigned addr) (bv_unsigned init_sp))
              then Some (Z_to_bv 8 0) else None
          end).
  rewrite Hstk.
  destruct (nth_error (word_le8 (nat_to_word (length (in_argv inp)))) i) eqn:E;
    [reflexivity|].
  apply nth_error_None in E. rewrite word_le8_length in E. lia.
Qed.

Lemma actual_mem_is_overlay :
  forall segs init_pc ph init_sp mbase init_rnd inp,
  ms_mem (init_machine_state segs init_pc ph init_sp mbase init_rnd inp) =
  overlay_argc_bytes init_sp (length (in_argv inp))
    (ms_mem (init_machine_state segs init_pc ph init_sp mbase init_rnd inp)).
Proof.
  intros segs init_pc ph init_sp mbase init_rnd inp.
  apply functional_extensionality. intro addr.
  unfold overlay_argc_bytes.
  destruct ((bv_unsigned addr =? bv_unsigned init_sp)%Z) eqn:E0;
    [ apply Z.eqb_eq in E0;
      apply (init_first8 segs init_pc ph init_sp mbase init_rnd inp addr 0); lia | ].
  destruct ((bv_unsigned addr =? bv_unsigned init_sp + 1)%Z) eqn:E1;
    [ apply Z.eqb_eq in E1;
      apply (init_first8 segs init_pc ph init_sp mbase init_rnd inp addr 1); lia | ].
  destruct ((bv_unsigned addr =? bv_unsigned init_sp + 2)%Z) eqn:E2;
    [ apply Z.eqb_eq in E2;
      apply (init_first8 segs init_pc ph init_sp mbase init_rnd inp addr 2); lia | ].
  destruct ((bv_unsigned addr =? bv_unsigned init_sp + 3)%Z) eqn:E3;
    [ apply Z.eqb_eq in E3;
      apply (init_first8 segs init_pc ph init_sp mbase init_rnd inp addr 3); lia | ].
  destruct ((bv_unsigned addr =? bv_unsigned init_sp + 4)%Z) eqn:E4;
    [ apply Z.eqb_eq in E4;
      apply (init_first8 segs init_pc ph init_sp mbase init_rnd inp addr 4); lia | ].
  destruct ((bv_unsigned addr =? bv_unsigned init_sp + 5)%Z) eqn:E5;
    [ apply Z.eqb_eq in E5;
      apply (init_first8 segs init_pc ph init_sp mbase init_rnd inp addr 5); lia | ].
  destruct ((bv_unsigned addr =? bv_unsigned init_sp + 6)%Z) eqn:E6;
    [ apply Z.eqb_eq in E6;
      apply (init_first8 segs init_pc ph init_sp mbase init_rnd inp addr 6); lia | ].
  destruct ((bv_unsigned addr =? bv_unsigned init_sp + 7)%Z) eqn:E7;
    [ apply Z.eqb_eq in E7;
      apply (init_first8 segs init_pc ph init_sp mbase init_rnd inp addr 7); lia | ].
  reflexivity.
Qed.

Lemma machine_state_eta : forall ms : machine_state,
  ms = {| ms_regs := ms_regs ms; ms_fregs := ms_fregs ms; ms_pc_val := ms_pc_val ms;
          ms_svc_pending := ms_svc_pending ms; ms_resv := ms_resv ms; ms_fcsr := ms_fcsr ms;
          ms_mem := ms_mem ms; ms_rom := ms_rom ms |}.
Proof. intros []; reflexivity. Qed.

(** The "enumeration state": structural fields from the initial state
    (none of them reads argv), [ms_mem] replaced by an overlay with a
    FREE [argc]/base.  It takes the launch's own [inp] and mmap base
    rather than building a [State.ProcInput] of its own: the entry
    image is a function of the whole input now, so there is no
    argv-free instance of it to name. *)
Definition enum_state (segs : list Segment) (init_pc : N) (ph : PhdrInfo)
    (init_sp mbase : word) (init_rnd : EntryDraw) (inp : ProcInput)
    (argc : nat) (base : word -> option byte) : machine_state :=
  {| ms_regs       := ms_regs (init_machine_state segs init_pc ph init_sp mbase init_rnd inp);
     ms_fregs      := ms_fregs (init_machine_state segs init_pc ph init_sp mbase init_rnd inp);
     ms_pc_val     := ms_pc_val (init_machine_state segs init_pc ph init_sp mbase init_rnd inp);
     ms_svc_pending := ms_svc_pending (init_machine_state segs init_pc ph init_sp mbase init_rnd inp);
     ms_resv       := ms_resv (init_machine_state segs init_pc ph init_sp mbase init_rnd inp);
     ms_fcsr       := ms_fcsr (init_machine_state segs init_pc ph init_sp mbase init_rnd inp);
     ms_mem        := overlay_argc_bytes init_sp argc base;
     ms_rom        := ms_rom (init_machine_state segs init_pc ph init_sp mbase init_rnd inp) |}.

(** Bridge: the real initial state equals the enumeration state at
    [argc := length argv] and [base := its own memory]. *)
Lemma init_eq_enum_state :
  forall segs init_pc ph init_sp mbase init_rnd inp,
  init_machine_state segs init_pc ph init_sp mbase init_rnd inp =
  enum_state segs init_pc ph init_sp mbase init_rnd inp
    (length (in_argv inp))
    (ms_mem (init_machine_state segs init_pc ph init_sp mbase init_rnd inp)).
Proof.
  intros segs init_pc ph init_sp mbase init_rnd inp. unfold enum_state.
  rewrite (machine_state_eta
             (init_machine_state segs init_pc ph init_sp mbase init_rnd inp)) at 1.
  f_equal; try reflexivity. apply actual_mem_is_overlay.
Qed.

(* ========================================================================= *)
(* Run-level packaging: the two facts, and the equivalence glue.              *)
(* ========================================================================= *)

(** The run-level omni judgment of an exit-only binary. *)
Lemma exit_omni_run : forall segs pc ph sp brk0 mb rnd lim code inp F,
  sim_c (run_segments segs inp sp mb) code F (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp) = true ->
  omni_run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp
    (exit_post code (in_fs inp)).
Proof.
  intros segs pc ph sp brk0 mb rnd lim code inp F Hsim.
  cbn [omni_run]. unfold init_config.
  exact (to_exit_exec (run_segments segs inp sp mb) code
           (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp)
           (with_vdso (vdso_run_init (ed_vdso rnd))
              (init_model (segments_reserved (run_segments segs inp sp mb)) brk0 mb sp lim inp))
           eq_refl eq_refl (sim_c_to_exit (run_segments segs inp sp mb) code F _ Hsim)).
Qed.

Lemma exit_obs_iff : forall segs pc ph sp brk0 mb rnd lim code inp F,
  sim_c (run_segments segs inp sp mb) code F (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp) = true ->
  forall tr, obs_trace (run_segments segs inp sp mb) (init_config (run_segments segs inp sp mb) pc ph sp brk0 mb rnd lim inp) tr
             <-> is_prefix tr [ExitEv (bv_and code (Z_to_bv 64 255)) (in_fs inp)].
Proof.
  intros segs pc ph sp brk0 mb rnd lim code inp F Hsim tr.
  apply exec_obs_iff.
  eapply exec_conseq; [exact (exit_omni_run segs pc ph sp brk0 mb rnd lim code inp F Hsim) |].
  intros tr' o (Heq & Hx). split; [exact Heq | exact (exits_with_never_errors _ _ _ Hx)].
Qed.

Lemma exit_no_error_run : forall segs pc ph sp brk0 mb rnd lim code inp F,
  sim_c (run_segments segs inp sp mb) code F (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp) = true ->
  ~ reaches_error (run_segments segs inp sp mb) (init_config (run_segments segs inp sp mb) pc ph sp brk0 mb rnd lim inp).
Proof.
  intros segs pc ph sp brk0 mb rnd lim code inp F Hsim. apply exec_no_error.
  eapply exec_conseq; [exact (exit_omni_run segs pc ph sp brk0 mb rnd lim code inp F Hsim) |].
  intros tr o (_ & Hx). exact (exits_with_never_errors _ _ _ Hx).
Qed.

(** The code half of [exit_post], consumed and pinned: the run satisfies
    [MustExit.must_exit_with] at the masked code, and at no other. *)
Lemma exit_must_exit_with : forall segs pc ph sp brk0 mb rnd lim code inp F,
  sim_c (run_segments segs inp sp mb) code F (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp) = true ->
  must_exit_with (bv_and code (Z_to_bv 64 255)) (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp.
Proof.
  intros segs pc ph sp brk0 mb rnd lim code inp F Hsim. apply must_exit_with_iff.
  eapply exec_conseq; [exact (exit_omni_run segs pc ph sp brk0 mb rnd lim code inp F Hsim) |].
  intros tr o (_ & Hx). exact Hx.
Qed.

Lemma exit_omni_run_code_unique : forall segs pc ph sp brk0 mb rnd lim code inp F code',
  sim_c (run_segments segs inp sp mb) code F (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp) = true ->
  omni_run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp (exits_with code') ->
  code' = bv_and code (Z_to_bv 64 255).
Proof.
  intros segs pc ph sp brk0 mb rnd lim code inp F code' Hsim Hex.
  pose proof (exit_omni_run segs pc ph sp brk0 mb rnd lim code inp F Hsim) as Hrun.
  cbn [omni_run] in Hrun, Hex.
  destruct (exec_realizes _ _ _ Hrun) as (tr & [c' | c'] & Hm & _ & Hx); [| destruct Hx].
  pose proof (exec_sound _ _ _ Hex _ _ Hm) as Hx'.
  cbn [exits_with] in Hx, Hx'. destruct Hx as (Hx & _). destruct Hx' as (Hx' & _).
  rewrite Hx in Hx'. injection Hx' as Hx'. symmetry. exact Hx'.
Qed.

(** The omni equivalence for two exit-only binaries reaching the same
    exit code, at the two role budgets.  Trace agreement is the two
    [exit_obs_iff] instances under [OmniEquivalence.trace_equiv_iff_omni]
    (both runs have the same exact trace); the source's coverage and the
    target's error-freedom are [exit_omni_run] weakened. *)
Lemma exit_omni_strong_equiv :
  forall source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd code inp FR FA,
  sim_c (run_segments source_segs inp rsp rmb) code FR
    (init_machine_state (run_segments source_segs inp rsp rmb) rpc rph rsp rmb rrnd inp) = true ->
  sim_c (run_segments target_segs inp asp amb) code FA
    (init_machine_state (run_segments target_segs inp asp amb) apc aph asp amb arnd inp) = true ->
  omni_strong_equiv (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
                    (mkEntry rsp rbrk rmb rrnd) (mkEntry asp abrk amb arnd) inp.
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd code inp FR FA
    Hsource Htarget.
  split.
  { cbn [image_run_segments img_segments en_sp en_mmap_base].
    eapply coexec_conseq;
      [apply exec_coexec;
       exact (exit_omni_run source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit code inp FR Hsource) |].
    intros tr o (_ & Hx).
    exact (never_errors_covered _ _ _ (exits_with_never_errors _ _ _ Hx)). }
  right. split.
  - apply trace_equiv_iff_omni. intro tr. cbn.
    rewrite (exit_obs_iff source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit code inp FR Hsource tr).
    rewrite (exit_obs_iff target_segs apc aph asp abrk amb arnd target_alloc_limit code inp FA Htarget tr).
    reflexivity.
  - apply bh_errors_iff. cbn.
    apply (exit_no_error_run target_segs apc aph asp abrk amb arnd target_alloc_limit code inp FA Htarget).
Qed.

(** The [Equivalence]-level equivalence for two exit-only binaries reaching
    the same exit code. *)
Lemma exit_strong_equiv :
  forall source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim code inp FR FA,
  sim_c (run_segments source_segs inp rsp rmb) code FR
    (init_machine_state (run_segments source_segs inp rsp rmb) rpc rph rsp rmb rrnd inp) = true ->
  sim_c (run_segments target_segs inp asp amb) code FA
    (init_machine_state (run_segments target_segs inp asp amb) apc aph asp amb arnd inp) = true ->
  Equivalence.modeled (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ Equivalence.equiv (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
                       (run (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp).
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim code inp FR FA
    Hsource Htarget.
  split.
  { apply no_error_run_modeled.
    apply (exit_no_error_run source_segs rpc rph rsp rbrk rmb rrnd rlim code inp FR Hsource). }
  right. split.
  - intro tr. cbn.
    rewrite (exit_obs_iff source_segs rpc rph rsp rbrk rmb rrnd rlim code inp FR Hsource tr).
    rewrite (exit_obs_iff target_segs apc aph asp abrk amb arnd alim code inp FA Htarget tr).
    reflexivity.
  - cbn. apply (exit_no_error_run target_segs apc aph asp abrk amb arnd alim code inp FA Htarget).
Qed.
