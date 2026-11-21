(* AS/DivergeSim := 's own theories/Common/DivergeSim.v IN PLACE (md5 ), Common requires -> AS/; the old text is kept aside *)
(** * Common.DivergeSim — reusable trace-semantics infrastructure for a
      SILENTLY DIVERGING branch: execution reaches a machine state from
      which it loops forever without issuing another effectful step.

    TRUST BOUNDARY: image-INDEPENDENT proof library (like Common.ExitSim).
    Generic over the loaded segments [segs].

    WHY THIS EXISTS.  The sealed ASan runtime answers an internal
    allocation failure with a tight infinite loop that makes NO further
    syscalls (typically a single self-jump, [j .] = [jal x0, 0], or an
    equivalent closed loop over a few PCs).  An equivalence proof over
    the spec's failure-anytime mmap nondeterminism must show, at each
    refusal case-split, that the diverging resolution contributes no new
    complete trace and only already-covered prefixes: from the loop
    state, [Run.star] can emit nothing further, so [Run.obs_trace] gains
    only prefixes of the events already emitted (which the prefix
    closure of [bh_traces] contributes anyway), the branch can never
    take the explicit error transition (nothing lands in [bh_errors]),
    and — because the loop is an infinite non-erroring execution — the
    branch also REFUTES [bh_all_errors], so the source-vacuity escape of
    [Equivalence.equiv] cannot fire through it.

    NO COINDUCTION IS NEEDED.  [bh_traces] holds only FINITE prefixes of
    finite [star] derivations, [bh_errors] is a finite reach, and
    [bh_all_errors] is inductive (accessibility), so "loops forever" is
    consumed purely inductively: a set of configurations closed under
    the one deterministic silent step absorbs every finite derivation
    that enters it.  Consequently every lemma here is [Qed] with no
    axioms beyond the baseline.

    STRUCTURE (three layers, from general to executable):

    - [silent_loop P]: a SET of configurations, each un-halted, with no
      pending syscall, whose accounted instruction step ([Run.
      mi_account_step]) succeeds and stays in the set.  This is the
      finite-cycle predicate in its most general, model-threading form
      ([silent_loop_cycle] shows the literal finite-set instance is
      definitional).  Core results: a [star] from a [silent_loop] state
      emits [] ([silent_loop_star]); no error transition is reachable
      ([silent_loop_no_error]); the observation set is exactly {[]}
      ([silent_loop_obs_iff]); and [all_traces_error] is refuted
      ([silent_loop_not_all_errors]).
    - [to_spin ms model]: "this machine state deterministically runs a
      straight line of silent instruction steps into a one-step
      FIXPOINT" — the reach-style predicate an example proof
      establishes at the post-refusal state, mirroring [ExitSim.to_exit]
      (which reaches an exit ecall where this reaches a self-jump).
      The base case is an accounted-step fixpoint; smart constructors
      cover the two ways proofs actually meet it: an instruction with
      an EMPTY access report ([ts_spin_no_access] — any model, lazy
      mappings included, so post-mmap ASan states are covered) and the
      no-lazy raw-step idiom the existing sim files use
      ([ts_spin_no_lazy]/[ts_step_no_lazy] compose with the
      [PropExec.step_*] lemmas over [mkst]).
    - [spin_c]: a fuel-bounded executable witness for [to_spin], closed
      by [vm_compute] on a concrete machine state ([spin_c_to_spin];
      tactic [prove_to_spin]), keyed on recognizing the literal
      self-jump instruction [is_self_jump] (a decoded [Jal rd imm] with
      [rd = x0] and [bv_signed imm = 0] — both the 4-byte [j .] and the
      compressed [c.j .] expand to exactly that).  Use it only when the
      state is concrete enough for the boolean to collapse; symbolic
      proofs chain [ts_step_no_access]/[ts_step_no_lazy] instead.

    HOW A SIM PROOF INVOKES IT.  At an mmap-refusal case-split the
    derivation stands at the post-refusal configuration [mkCfg ms model]
    with some emitted prefix [P] behind it.  Establish
    [to_spin ms model] (by [prove_to_spin], or by chaining
    [ts_step_no_lazy] over [PropExec] step lemmas into
    [ts_spin_of_step_j]); then

    - in the FORWARD direction of a [*_obs_iff] proof, the tail [star]
      of the refusal branch collapses by [spin_star_nil] (so the branch
      trace is [P ++ [] = P], a prefix of the already-covered complete
      trace);
    - in a [*_no_error] proof, the refusal branch's error reach is
      refuted by [spin_no_error_run] (and, at the split configuration
      itself, [spin_no_sstep_error]);
    - the BACKWARD direction needs nothing new: prefixes of [P] are
      already contributed by the derivation that reaches the split
      ([obs_trace_of_star]).

    [spin_branch_toy_*] at the bottom work a complete two-branch toy
    obligation in exactly this shape, and the [SelfJumpImage] section
    checks the executable layer end-to-end on a concrete image whose
    single instruction is the literal [j .] encoding 0x0000006f. *)

From Stdlib Require Import ZArith NArith List Lia Bool String PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Vdso Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.AS Require Import PropExec.
Import ListNotations.
Open Scope bv_scope.
(** The [StepTac.vm_refl_bv] idiom, redeclared locally (this file sits
    BELOW [StepTac] in the layering): close a decidable goal by a
    VM-checked [bool_decide] cast — plain [vm_compute; reflexivity]
    gets stuck on the opaque [Z_to_bv] wf proofs. *)
Local Ltac div_vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Section WithFP1.
Context {fx : FPState}.

(* ================================================================= *)
(* Prefix-order helpers                                              *)
(* ================================================================= *)

Lemma is_prefix_nil_inv {A} : forall (tr : list A),
  is_prefix tr [] -> tr = [].
Proof. destruct tr; [reflexivity | contradiction]. Qed.

Lemma is_prefix_app_mono {A} : forall (e a b : list A),
  is_prefix a b -> is_prefix (e ++ a) (e ++ b).
Proof. induction e; cbn; auto. Qed.

(* ================================================================= *)
(* Accounted-step plumbing (segment-generic, outside the section     *)
(* only because nothing here mentions [segs])                        *)
(* ================================================================= *)

(** An instruction that touches no memory materializes nothing: the
    accounting layer is the identity on the model, WHATEVER the lazy
    ledger holds.  This is [State.materialize_model_accesses_no_lazy]'s
    dual, and it is what frees the loop lemmas from any [m_vm_lazy]
    hypothesis — the ASan spin runs long after MAP_NORESERVE mappings
    have populated the lazy ledger. *)
Lemma materialize_model_accesses_nil : forall m,
  materialize_model_accesses m [] = Some m.
Proof.
  intros [fd [maps lazy materialized] io fs proc lim].
  unfold materialize_model_accesses; cbn.
  unfold materialize_accesses, newly_materialized_pages; cbn.
  reflexivity.
Qed.

(** Read an accounted step off a raw access report. *)
Lemma mi_account_step_of_accesses : forall segs ms model ms' ranges,
  RiscvSemantics.step_accesses segs ms = MachineOk (@mkAccessReport machine_state ms' ranges) ->
  mi_account_step segs ms model =
    match materialize_model_accesses model ranges with
    | Some model' => MachineOk (ms', model')
    | None => MachineFault
    end.
Proof.
  intros segs ms model ms' ranges Hstep.
  unfold mi_account_step. rewrite Hstep. reflexivity.
Qed.

(** An access-free instruction steps the machine and leaves the model
    alone — no lazy hypothesis. *)
Lemma mi_account_step_no_access : forall segs ms model ms',
  RiscvSemantics.step_accesses segs ms = MachineOk (@mkAccessReport machine_state ms' []) ->
  mi_account_step segs ms model = MachineOk (ms', model).
Proof.
  intros segs ms model ms' Hstep.
  rewrite (mi_account_step_of_accesses segs ms model ms' [] Hstep).
  rewrite materialize_model_accesses_nil. reflexivity.
Qed.

(** An accounted instruction step preserves haltedness (it can only
    charge lazy pages; [m_proc] is framed). *)
Lemma mi_account_step_halted : forall segs ms model ms' model',
  mi_account_step segs ms model = MachineOk (ms', model') ->
  m_halted model' = m_halted model.
Proof.
  intros segs ms model ms' model' Hacc.
  destruct (mi_account_step_model_frame segs ms model ms' model' Hacc)
    as (_ & _ & _ & _ & _ & Hproc & _).
  unfold m_halted. rewrite Hproc. reflexivity.
Qed.

(* ================================================================= *)
(* The self-jump instruction: the accounted one-step fixpoint         *)
(* ================================================================= *)

(** [v_addi a 0 = a]. *)
Lemma v_addi_0 : forall a : word, v_addi a 0 = a.
Proof.
  intro a. unfold v_addi. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned.
Qed.

(** A decoded [Jal x0 imm] with [bv_signed imm = 0] — the expansion of
    both [j .] (4 bytes, 0x0000006f) and [c.j .] (2 bytes) — is a
    one-step fixpoint of the machine semantics WITH AN EMPTY ACCESS
    REPORT, for an ARBITRARY machine state with no pending syscall (no
    [mkst] shape required: the spin state inherits whatever registers,
    reservation and fcsr the crashing runtime left behind). *)
Lemma self_jump_step_accesses : forall segs ms w (rd : reg) (imm : bv 21) sz,
  ms_svc_pending ms = None ->
  fetch_word segs (ms_pc ms) = Some w ->
  is_ecall w = false ->
  decode_any w = Some (Jal rd imm, sz) ->
  is_x0 rd = true ->
  bv_signed imm = 0%Z ->
  RiscvSemantics.step_accesses segs ms = MachineOk (@mkAccessReport machine_state ms []).
Proof.
  intros segs ms w rd imm sz Hsvc Hfetch Hecall Hdecode Hx0 Himm.
  unfold RiscvSemantics.step_accesses.
  rewrite Hfetch.
  unfold RiscvSemantics.decode_exec_accesses.
  rewrite Hecall. cbv beta iota.
  rewrite Hdecode. cbv beta iota.
  cbv beta iota zeta delta
    [RiscvSemantics.interp_eff_accesses Sem.exec
     Sem.rget Sem.rset Sem.with_regs Sem.with_pc
     Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv].
  rewrite Hx0. cbv beta iota.
  rewrite b_addsext, Himm, v_addi_0.
  destruct ms; cbn in Hsvc; subst; reflexivity.
Qed.

(** The same, packaged at the accounted level: the self-jump is a
    fixpoint of [mi_account_step] with the model UNCHANGED — again with
    no hypothesis on the lazy ledger. *)
Lemma self_jump_account_fix : forall segs ms model w (rd : reg) (imm : bv 21) sz,
  ms_svc_pending ms = None ->
  fetch_word segs (ms_pc ms) = Some w ->
  is_ecall w = false ->
  decode_any w = Some (Jal rd imm, sz) ->
  is_x0 rd = true ->
  bv_signed imm = 0%Z ->
  mi_account_step segs ms model = MachineOk (ms, model).
Proof.
  intros. eapply mi_account_step_no_access.
  eapply self_jump_step_accesses; eassumption.
Qed.

(** The [PropExec.mkst] spelling, for symbolic straight-line proofs in
    the existing sim idiom. *)
Lemma step_j_self : forall segs regs pc mem rom w (rd : reg) (imm : bv 21) sz,
  fetch_word segs pc = Some w ->
  is_ecall w = false ->
  decode_any w = Some (Jal rd imm, sz) ->
  is_x0 rd = true ->
  bv_signed imm = 0%Z ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs pc mem rom).
Proof.
  intros segs regs pc mem rom w rd imm sz Hf He Hd Hx0 Hi.
  unfold RiscvSemantics.step.
  rewrite (self_jump_step_accesses segs (mkst regs pc mem rom) w rd imm sz
             eq_refl Hf He Hd Hx0 Hi).
  reflexivity.
Qed.

Section WithSegs.
Variable segs : list Segment.

(* ================================================================= *)
(* silent_loop: a step-closed set of effect-free configurations       *)
(* ================================================================= *)

(** [P] is a set of configurations, each of which is un-halted, has no
    pending syscall, and whose accounted instruction step succeeds and
    lands back in [P].  Execution entering [P] therefore runs forever,
    emits no event, and never reaches the error transition.  This is
    the "closed loop over a few PCs" predicate in its most general
    form: the loop body may even keep materializing fresh lazy pages
    forever, as long as every accounted step succeeds. *)
Definition silent_loop (P : config -> Prop) : Prop :=
  forall c, P c ->
    m_halted (cfg_model c) = None /\
    ms_svc_pending (cfg_ms c) = None /\
    exists ms' model',
      mi_account_step segs (cfg_ms c) (cfg_model c) = MachineOk (ms', model') /\
      P (mkCfg ms' model').

(** The finite-cycle instance is DEFINITIONAL: a concrete list of
    configurations, each stepping to a member, is a [silent_loop]. *)
Lemma silent_loop_cycle : forall (cs : list config),
  (forall c, In c cs ->
     m_halted (cfg_model c) = None /\
     ms_svc_pending (cfg_ms c) = None /\
     exists ms' model',
       mi_account_step segs (cfg_ms c) (cfg_model c) = MachineOk (ms', model') /\
       In (mkCfg ms' model') cs) ->
  silent_loop (fun c => In c cs).
Proof. intros cs H c. exact (H c). Qed.

(** From a [silent_loop] configuration the ONLY transition is the
    silent instruction step, and it stays in the loop. *)
Lemma silent_loop_sstep : forall P c evs to,
  silent_loop P -> P c -> sstep segs c evs to ->
  evs = [] /\ exists c', to = SNext c' /\ P c'.
Proof.
  intros P c evs to Hloop HP Hstep.
  destruct (Hloop c HP) as (Hh & Hsvc & ms' & model' & Hacc & HP').
  destruct c as [ms model]; cbn in Hh, Hsvc, Hacc.
  inversion Hstep; subst; try congruence.
  (* only [sstep_instr] survives: deterministic, matches Hacc *)
  repeat match goal with
  | H : mi_account_step ?s ?a ?b = MachineOk ?x,
    H' : mi_account_step ?s ?a ?b = MachineOk ?y |- _ =>
      rewrite H in H'; injection H'; intros; subst; clear H
  end.
  eauto 7.
Qed.

(** One-level case analysis on a [star] derivation (a plain [destruct]
    packaged so case-split proofs need no [inversion] bookkeeping). *)
Lemma star_case : forall c tr c', star segs c tr c' ->
  (tr = [] /\ c' = c) \/
  exists evs c2 tr2,
    sstep segs c evs (SNext c2) /\ star segs c2 tr2 c' /\ tr = evs ++ tr2.
Proof.
  intros c tr c' H;
    destruct H as [c | c1 evs c2 tr2 c3 Hstep Htail];
    [left; auto | right; exists evs, c2, tr2; auto].
Qed.

(** A finite run from inside the loop emits nothing and stays inside. *)
Lemma silent_loop_star : forall P, silent_loop P ->
  forall c tr c', star segs c tr c' -> P c -> tr = [] /\ P c'.
Proof.
  intros P Hloop c tr c' Hstar.
  induction Hstar as [c | c evs c2 tr c3 Hstep Hstar IH]; intros HP.
  - auto.
  - destruct (silent_loop_sstep P c evs _ Hloop HP Hstep)
      as (-> & c2' & Heq & HP2).
    injection Heq as <-.
    destruct (IH HP2) as (-> & HP3). auto.
Qed.

Lemma silent_loop_star_nil : forall P c tr c',
  silent_loop P -> P c -> star segs c tr c' -> tr = [].
Proof.
  intros P c tr c' Hloop HP Hstar.
  exact (proj1 (silent_loop_star P Hloop c tr c' Hstar HP)).
Qed.

(** No error transition is reachable from inside the loop: nothing this
    branch does can land in [bh_errors]. *)
Lemma silent_loop_no_error : forall P c,
  silent_loop P -> P c -> ~ reaches_error segs c.
Proof.
  intros P c Hloop HP (tr & c2 & evs & Hstar & Herr).
  destruct (silent_loop_star P Hloop c tr c2 Hstar HP) as (_ & HP2).
  destruct (silent_loop_sstep P c2 evs _ Hloop HP2 Herr)
    as (_ & c' & Heq & _).
  discriminate Heq.
Qed.

(** ...and a fortiori nothing unmodeled is reachable. *)
Lemma silent_loop_no_unmodeled : forall P c,
  silent_loop P -> P c -> ~ reaches_unmodeled segs c.
Proof.
  intros P c Hloop HP.
  exact (no_error_no_unmodeled segs c (silent_loop_no_error P c Hloop HP)).
Qed.

(** The loop's observation set is exactly {[]}: the branch contributes
    only prefixes of whatever was emitted BEFORE it was entered. *)
Lemma silent_loop_obs_iff : forall P c,
  silent_loop P -> P c -> forall tr, obs_trace segs c tr <-> tr = [].
Proof.
  intros P c Hloop HP tr. split.
  - intros (tr' & c2 & Hstar & Hpre).
    rewrite (silent_loop_star_nil P c tr' c2 Hloop HP Hstar) in Hpre.
    exact (is_prefix_nil_inv tr Hpre).
  - intros ->. apply obs_trace_nil.
Qed.

(** The loop is an infinite NON-erroring execution, so it refutes
    [all_traces_error]: a source binary whose refusal branch spins can
    never take [Equivalence.equiv]'s vacuity escape through that
    branch. *)
Lemma silent_loop_not_all_errors : forall P c,
  silent_loop P -> P c -> ~ all_traces_error segs c.
Proof.
  intros P c Hloop HP Hall. revert HP.
  induction Hall as [c Hprog Hnext IH]; intros HP.
  destruct (Hloop c HP) as (Hh & Hsvc & ms' & model' & Hacc & HP').
  destruct c as [ms model]; cbn in Hh, Hsvc, Hacc.
  apply (IH [] (mkCfg ms' model')); [|exact HP'].
  apply sstep_instr; assumption.
Qed.

(* ================================================================= *)
(* to_spin: a deterministic straight line into a one-step fixpoint    *)
(* ================================================================= *)

(** "[ms] (running against [model]) silently reaches a one-step
    fixpoint": finitely many successful accounted instruction steps, no
    pending syscall anywhere, ending at a state whose accounted step is
    the identity.  The reach-style mirror of [ExitSim.to_exit], with
    the model THREADED because the accounting layer may charge lazy
    pages on the way in. *)
Inductive to_spin : machine_state -> Model -> Prop :=
| ts_spin : forall ms model,
    ms_svc_pending ms = None ->
    mi_account_step segs ms model = MachineOk (ms, model) ->
    to_spin ms model
| ts_step : forall ms model ms' model',
    ms_svc_pending ms = None ->
    mi_account_step segs ms model = MachineOk (ms', model') ->
    to_spin ms' model' ->
    to_spin ms model.

(** Smart constructors, in decreasing order of generality. *)

Lemma ts_spin_no_access : forall ms model,
  ms_svc_pending ms = None ->
  RiscvSemantics.step_accesses segs ms = MachineOk (@mkAccessReport machine_state ms []) ->
  to_spin ms model.
Proof.
  intros ms model Hsvc Hstep.
  apply ts_spin; [exact Hsvc | exact (mi_account_step_no_access segs ms model ms Hstep)].
Qed.

Lemma ts_step_no_access : forall ms model ms',
  ms_svc_pending ms = None ->
  RiscvSemantics.step_accesses segs ms = MachineOk (@mkAccessReport machine_state ms' []) ->
  to_spin ms' model ->
  to_spin ms model.
Proof.
  intros ms model ms' Hsvc Hstep Hspin.
  exact (ts_step ms model ms' model Hsvc
           (mi_account_step_no_access segs ms model ms' Hstep) Hspin).
Qed.

(** The raw-step spellings the existing sim files produce
    ([PropExec.step_*] lemmas over [mkst] state raw
    [RiscvSemantics.step] equalities); they need the usual no-lazy
    hypothesis those files already thread. *)

Lemma ts_spin_no_lazy : forall ms model,
  ms_svc_pending ms = None ->
  m_vm_lazy model = [] ->
  RiscvSemantics.step segs ms = MachineOk ms ->
  to_spin ms model.
Proof.
  intros ms model Hsvc Hlazy Hstep.
  apply ts_spin; [exact Hsvc|].
  rewrite (mi_account_step_no_lazy segs ms model Hlazy).
  rewrite Hstep. reflexivity.
Qed.

Lemma ts_step_no_lazy : forall ms model ms',
  ms_svc_pending ms = None ->
  m_vm_lazy model = [] ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  to_spin ms' model ->
  to_spin ms model.
Proof.
  intros ms model ms' Hsvc Hlazy Hstep Hspin.
  apply (ts_step ms model ms' model); [exact Hsvc| |exact Hspin].
  rewrite (mi_account_step_no_lazy segs ms model Hlazy).
  rewrite Hstep. reflexivity.
Qed.

(** Entering the spin on the literal self-jump instruction. *)
Lemma ts_spin_of_step_j : forall ms model w (rd : reg) (imm : bv 21) sz,
  ms_svc_pending ms = None ->
  fetch_word segs (ms_pc ms) = Some w ->
  is_ecall w = false ->
  decode_any w = Some (Jal rd imm, sz) ->
  is_x0 rd = true ->
  bv_signed imm = 0%Z ->
  to_spin ms model.
Proof.
  intros. eapply ts_spin_no_access; [assumption|].
  eapply self_jump_step_accesses; eassumption.
Qed.

(** The set a [to_spin] derivation stays inside. *)
Definition spinning (c : config) : Prop :=
  to_spin (cfg_ms c) (cfg_model c) /\ m_halted (cfg_model c) = None.

Lemma spinning_silent_loop : silent_loop spinning.
Proof.
  intros [ms model] [Hspin Hh]; cbn in Hspin, Hh; cbn.
  revert Hh.
  destruct Hspin as [ms model Hsvc Hfix | ms model ms' model' Hsvc Hacc Hspin'];
    intros Hh.
  - refine (conj Hh (conj Hsvc _)).
    exists ms, model. split; [exact Hfix|].
    split; cbn; [apply ts_spin; assumption | exact Hh].
  - refine (conj Hh (conj Hsvc _)).
    exists ms', model'. split; [exact Hacc|].
    split; cbn; [exact Hspin'|].
    rewrite (mi_account_step_halted segs ms model ms' model' Hacc). exact Hh.
Qed.

(* ================================================================= *)
(* The proof-facing trio at a spin state                              *)
(* ================================================================= *)

(** In the FORWARD direction of a [*_obs_iff] proof: once the refusal
    branch's derivation stands at [mkCfg ms model] with [to_spin], its
    tail [star] collapses to []. *)
Theorem spin_star_nil : forall ms model tr c',
  to_spin ms model -> m_halted model = None ->
  star segs (mkCfg ms model) tr c' -> tr = [].
Proof.
  intros ms model tr c' Hspin Hh Hstar.
  exact (silent_loop_star_nil spinning (mkCfg ms model) tr c'
           spinning_silent_loop (conj Hspin Hh) Hstar).
Qed.

(** The branch's own observation set is exactly {[]}. *)
Theorem spin_obs_iff : forall ms model,
  to_spin ms model -> m_halted model = None ->
  forall tr, obs_trace segs (mkCfg ms model) tr <-> tr = [].
Proof.
  intros ms model Hspin Hh.
  exact (silent_loop_obs_iff spinning (mkCfg ms model)
           spinning_silent_loop (conj Hspin Hh)).
Qed.

(** In a [*_no_error] proof: the refusal branch never errors. *)
Theorem spin_no_error_run : forall ms model,
  to_spin ms model -> m_halted model = None ->
  ~ reaches_error segs (mkCfg ms model).
Proof.
  intros ms model Hspin Hh.
  exact (silent_loop_no_error spinning (mkCfg ms model)
           spinning_silent_loop (conj Hspin Hh)).
Qed.

(** At the split configuration itself: no single erroring step. *)
Theorem spin_no_sstep_error : forall ms model,
  to_spin ms model -> m_halted model = None ->
  forall evs, ~ sstep segs (mkCfg ms model) evs SError.
Proof.
  intros ms model Hspin Hh evs Herr.
  destruct (silent_loop_sstep spinning (mkCfg ms model) evs SError
              spinning_silent_loop (conj Hspin Hh) Herr)
    as (_ & c' & Heq & _).
  discriminate Heq.
Qed.

Theorem spin_no_unmodeled : forall ms model,
  to_spin ms model -> m_halted model = None ->
  ~ reaches_unmodeled segs (mkCfg ms model).
Proof.
  intros ms model Hspin Hh.
  exact (silent_loop_no_unmodeled spinning (mkCfg ms model)
           spinning_silent_loop (conj Hspin Hh)).
Qed.

(** The spin refutes the vacuity escape. *)
Theorem spin_not_all_errors : forall ms model,
  to_spin ms model -> m_halted model = None ->
  ~ all_traces_error segs (mkCfg ms model).
Proof.
  intros ms model Hspin Hh.
  exact (silent_loop_not_all_errors spinning (mkCfg ms model)
           spinning_silent_loop (conj Hspin Hh)).
Qed.

(* ================================================================= *)
(* Shape: a run that reaches a spin with prefix P                    *)
(* contributes exactly the prefixes of P                              *)
(* ================================================================= *)

(** Prefixes of any reached derivation are observable — the generic
    containment direction (nothing spin-specific; stated here because
    the spin glue consumes it together with [spin_star_nil]). *)
Lemma obs_trace_of_star : forall c0 evs c tr,
  star segs c0 evs c -> is_prefix tr evs -> obs_trace segs c0 tr.
Proof. intros c0 evs c tr Hstar Hpre. exists evs, c. auto. Qed.

(** If a run reaches [mkCfg ms model] having emitted [P], and the state
    spins, then (i) every prefix of [P] is observable from [c0], and
    (ii) every continuation THROUGH the spin state adds nothing: the
    branch contributes exactly the prefixes of [P] to [bh_traces].  In
    particular, if [P] is already a prefix of a complete trace the
    other resolution produces, the trace-set equality obligation is
    unaffected by this branch. *)
Theorem spin_reach_obs : forall c0 P ms model,
  star segs c0 P (mkCfg ms model) ->
  to_spin ms model -> m_halted model = None ->
  (forall tr, is_prefix tr P -> obs_trace segs c0 tr) /\
  (forall tr c', star segs (mkCfg ms model) tr c' -> P ++ tr = P).
Proof.
  intros c0 P ms model Hstar Hspin Hh. split.
  - intros tr Hpre. exact (obs_trace_of_star c0 P _ tr Hstar Hpre).
  - intros tr c' Htail.
    rewrite (spin_star_nil ms model tr c' Hspin Hh Htail).
    apply app_nil_r.
Qed.

(* ================================================================= *)
(* Executable witness                                                *)
(* ================================================================= *)

(** Recognize the literal self-jump: no pending syscall, and the
    fetched word decodes to [Jal x0 imm] with [bv_signed imm = 0]
    (both [j .] and [c.j .]).  The immutable-code fast path
    ([fetch_word]) is deliberately the only one tried: the ASan spin
    sits in the binary's r-x text segment.  A self-jump in a w+x
    segment must go through [ts_spin_no_lazy] by hand. *)
Definition is_self_jump (ms : machine_state) : bool :=
  match ms_svc_pending ms with
  | Some _ => false
  | None =>
    match fetch_word segs (ms_pc ms) with
    | Some w =>
      if is_ecall w then false else
      match decode_any w with
      | Some (Jal rd imm, _) => is_x0 rd && (bv_signed imm =? 0)%Z
      | _ => false
      end
    | None => false
    end
  end.

Lemma is_self_jump_to_spin : forall ms model,
  is_self_jump ms = true -> to_spin ms model.
Proof.
  intros ms model H. unfold is_self_jump in H.
  destruct (ms_svc_pending ms) eqn:Hsvc; [discriminate|].
  destruct (fetch_word segs (ms_pc ms)) as [w|] eqn:Hfetch; [|discriminate].
  destruct (is_ecall w) eqn:Hecall; [discriminate|].
  destruct (decode_any w) as [[i sz]|] eqn:Hdecode; [|discriminate].
  destruct i; try discriminate.
  apply andb_prop in H as [Hx0 Himm].
  apply Z.eqb_eq in Himm.
  eapply ts_spin_of_step_j; eassumption.
Qed.

(** Fuel-bounded executable straight-line-to-spin check, closed by
    [vm_compute] on a concrete state (mirroring [ExitSim.sim_c]).
    NOTE: [vm_compute] normalizes the whole term, so only use this when
    [ms]/[model] are concrete enough for the boolean to collapse —
    in particular never with an infinite [InputStream] buried in a
    concrete model.  Symbolic proofs chain the [ts_*] constructors. *)
Fixpoint spin_c (fuel : nat) (ms : machine_state) (model : Model) : bool :=
  match fuel with
  | O => false
  | S fuel' =>
    if is_self_jump ms then true
    else
      match ms_svc_pending ms with
      | Some _ => false
      | None =>
        match mi_account_step segs ms model with
        | MachineOk (ms', model') => spin_c fuel' ms' model'
        | _ => false
        end
      end
  end.

Lemma spin_c_to_spin : forall fuel ms model,
  spin_c fuel ms model = true -> to_spin ms model.
Proof.
  induction fuel as [|fuel IH]; intros ms model H; cbn in H;
    [discriminate|].
  destruct (is_self_jump ms) eqn:Hj;
    [exact (is_self_jump_to_spin ms model Hj)|].
  destruct (ms_svc_pending ms) eqn:Hsvc; [discriminate|].
  destruct (mi_account_step segs ms model) as [[ms' model']| |] eqn:Hacc;
    try discriminate.
  exact (ts_step ms model ms' model' Hsvc Hacc (IH ms' model' H)).
Qed.

End WithSegs.

(** Close a [to_spin ?segs ?ms ?model] goal by execution, [fuel] steps
    deep.  Only for concrete states — see the [spin_c] note. *)
End WithFP1.
Ltac prove_to_spin fuel :=
  apply (spin_c_to_spin _ fuel);
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.
Section WithFP2.
Context {fx : FPState}.


(* ================================================================= *)
(* Worked example 1: a toy two-branch obligation, in the shape of an  *)
(* mmap-refusal case-split                                            *)
(* ================================================================= *)

(** The toy: a configuration [c0] (think: the mmap ecall) with exactly
    two resolutions — a GRANT step emitting [evs_g] into a branch whose
    observations are the prefixes of [T] and which never errors, and a
    silent REFUSAL step into a spin.  Conclusion: the refusal branch
    changes NOTHING — the observation set from [c0] is exactly the
    prefixes of [evs_g ++ T], and no error is reachable.  A real
    [MmapSim]-style proof runs the same three moves at its refusal arm:
    [spin_star_nil] on the tail star, [spin_no_sstep_error] /
    [spin_no_error_run] on the error reach, and the shared prefix is
    covered by the grant branch's prefix closure. *)
Section TwoBranchToy.
Variable segs : list Segment.
Variable c0 : config.
Variable evs_g : list event.
Variable c_g c_r : config.
Variable T : list event.
Variable P : config -> Prop.

Hypothesis Hsplit : forall evs to, sstep segs c0 evs to ->
  (evs = evs_g /\ to = SNext c_g) \/ (evs = [] /\ to = SNext c_r).
Hypothesis Hstep_g : sstep segs c0 evs_g (SNext c_g).
Hypothesis Hg_obs : forall tr, obs_trace segs c_g tr <-> is_prefix tr T.
Hypothesis Hg_noerr : ~ reaches_error segs c_g.
Hypothesis Hloop : silent_loop segs P.
Hypothesis HP_r : P c_r.

Theorem spin_branch_toy_obs_iff : forall tr,
  obs_trace segs c0 tr <-> is_prefix tr (evs_g ++ T).
Proof.
  intro tr. split.
  - intros (tr' & cend & Hstar & Hpre).
    destruct (star_case segs c0 tr' cend Hstar)
      as [[-> _] | (evs & c2 & tr2 & Hstep & Htail & ->)].
    + apply is_prefix_nil_inv in Hpre. subst tr. apply is_prefix_nil.
    + destruct (Hsplit evs _ Hstep) as [[-> Heq] | [-> Heq]];
        injection Heq as ->.
      * (* grant branch: the tail is one of its observations *)
        assert (Hobs2 : obs_trace segs c_g tr2)
          by (exists tr2, cend; split; [exact Htail | apply is_prefix_refl]).
        apply Hg_obs in Hobs2.
        eapply is_prefix_trans; [exact Hpre|].
        apply is_prefix_app_mono. exact Hobs2.
      * (* refusal branch: the tail collapses *)
        rewrite (silent_loop_star_nil segs P c_r tr2 cend Hloop HP_r Htail)
          in Hpre.
        apply is_prefix_nil_inv in Hpre. subst tr. apply is_prefix_nil.
  - intro Hpre.
    destruct (proj2 (Hg_obs T) (is_prefix_refl T))
      as (tr'' & cend & Hstar & HpreT).
    exists (evs_g ++ tr''), cend. split.
    + exact (star_step segs c0 evs_g c_g tr'' cend Hstep_g Hstar).
    + eapply is_prefix_trans; [exact Hpre|].
      apply is_prefix_app_mono. exact HpreT.
Qed.

Theorem spin_branch_toy_no_error : ~ reaches_error segs c0.
Proof.
  intros (tr & cerr & evs & Hstar & Herr).
  destruct (star_case segs c0 tr cerr Hstar)
    as [[_ ->] | (evs1 & c2 & tr2 & Hstep & Htail & _)].
  - destruct (Hsplit evs SError Herr) as [[_ Heq] | [_ Heq]]; discriminate.
  - destruct (Hsplit evs1 _ Hstep) as [[_ Heq] | [_ Heq]];
      injection Heq as ->.
    + apply Hg_noerr. exists tr2, cerr, evs. auto.
    + apply (silent_loop_no_error segs P c_r Hloop HP_r).
      exists tr2, cerr, evs. auto.
Qed.

End TwoBranchToy.

(* ================================================================= *)
(* Worked example 2: the literal [j .] binary, end to end             *)
(* ================================================================= *)

(** A concrete image whose single instruction is the 4-byte [j .]
    encoding 0x0000006f (bytes 6f 00 00 00) in an r-x segment, entered
    at its base: the run emits nothing, never errors, and cannot take
    the vacuity escape — for EVERY entry, limit and input.  This pins
    the whole executable layer (fetch, decode, the x0/imm=0 test, the
    empty access report) against the real encoding. *)
End WithFP2.
Module SelfJumpImage.

Definition spin_seg : Segment := {|
  seg_base := 0x10000;
  seg_size := 4;
  seg_perms := "r-x"%string;
  seg_bytes := ["6f000000"%pstring];
  seg_kind  := SegLoader
|}.
Definition spin_segs : list Segment := [spin_seg].
Definition spin_img : Image :=
  mkImage spin_segs 0x10000 (mkPhdrInfo 0x10040 56 6).

Example j_dot_decodes :
  decode_any (Z_to_bv 32 0x6f) = Some (Jal 0 (Z_to_bv 21 0), 4%Z).
Proof. div_vm_refl. Qed.

(** Over the RUN's segment list: this image's own segment and the vDSO
    pair [Run.run_segments] appends, with the pair an abstract tail so
    that no computation here normalises the measured image.  The
    spinning instruction is in the image's own segment, which comes
    first, so the pair changes nothing. *)
Lemma spin_img_to_spin : forall vt sp brk0 mbase (rnd : EntryDraw) lim inp,
  to_spin (spin_segs ++ vt)
    (init_machine_state (spin_segs ++ vt) 0x10000 (mkPhdrInfo 0x10040 56 6)
       sp mbase rnd inp)
    (with_vdso (vdso_run_init (ed_vdso rnd))
       (init_model (segments_reserved (spin_segs ++ vt)) brk0 mbase sp lim inp)).
Proof.
  intros vt sp brk0 mbase rnd lim inp.
  eapply ts_spin_of_step_j with (w := Z_to_bv 32 0x6f).
  - reflexivity.
  - div_vm_refl.
  - div_vm_refl.
  - apply j_dot_decodes.
  - div_vm_refl.
  - div_vm_refl.
Qed.

Example spin_img_obs_iff : forall lim en inp tr,
  bh_traces (run spin_img lim en inp) tr <-> tr = [].
Proof.
  intros lim [sp brk0 mbase rnd] inp tr.
  cbn [run bh_traces spin_img]. unfold init_config.
  apply spin_obs_iff.
  - apply spin_img_to_spin.
  - reflexivity.
Qed.

Example spin_img_no_error : forall lim en inp,
  ~ bh_errors (run spin_img lim en inp).
Proof.
  intros lim [sp brk0 mbase rnd] inp.
  cbn [run bh_errors spin_img]. unfold init_config.
  apply spin_no_error_run.
  - apply spin_img_to_spin.
  - reflexivity.
Qed.

Example spin_img_not_all_errors : forall lim en inp,
  ~ bh_all_errors (run spin_img lim en inp).
Proof.
  intros lim [sp brk0 mbase rnd] inp.
  cbn [run bh_all_errors spin_img]. unfold init_config.
  apply spin_not_all_errors.
  - apply spin_img_to_spin.
  - reflexivity.
Qed.

(** The executable path closes the same goal by computation when the
    inputs are concrete.

    [spin_exec_input] is the same [State.ProcInput] both sides take, so
    the entry image and the model agree on argv, envp, the credentials
    and the kernel build.

    THE DRAW'S [ed_top] IS ONE PAGE ABOVE [sp], and it has to be.  The
    block now runs from [sp] all the way to [ed_top], so the image is
    [ed_top - sp] bytes and [vm_compute] builds every one of them; the
    top of the Sv48 user stack would be a list of 2^47 bytes and the
    checker is killed building it (measured).  This fixture's [sp] is
    65536, far below any Linux stack, so it is not a launch
    [Run.entry_launch_ok_va] admits and no lemma here asks it to be:
    the goal is that a self-jump spins, which reads no stack byte.  One
    page is what the model mapped here before the block grew, so the
    computation costs what it always did. *)
Definition spin_exec_input : ProcInput :=
  mkProcInput [[]] [] [] IEof (Z_to_bv 64 1000) (Z_to_bv 64 1002) []
    net_silent default_nofile (Z_to_bv 64 0) hwcap_rv64gc false Sv48.

Example spin_img_to_spin_by_execution :
  to_spin spin_segs
    (init_machine_state spin_segs 0x10000 (mkPhdrInfo 0x10040 56 6)
       (Z_to_bv 64 65536) (Z_to_bv 64 0x7fff7f800000)
       (mkDraw (Z_to_bv 128 0) (Z_to_bv 64 69632) vdso_keeps_all)
       spin_exec_input)
    (init_model (segments_reserved spin_segs) (Z_to_bv 64 1048576)
       (Z_to_bv 64 0x7fff7f800000) (Z_to_bv 64 65536) 0x40000000%Z
       spin_exec_input).
Proof. prove_to_spin 1%nat. Qed.

End SelfJumpImage.
