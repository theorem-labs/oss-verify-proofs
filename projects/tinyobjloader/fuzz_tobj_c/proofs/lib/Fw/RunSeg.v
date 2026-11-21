(* SPDX-License-Identifier: MIT *)
(* Theorem Labs, 2026-11 (LPS 75d69e00): the binary's own segments, lifted to the run's.

   WHAT THIS FILE IS FOR.  At 75d69e00 [Run.run_scfg] reads a binary against
   [run_segments segs inp sp mb] = [segs ++ vdso_segments (in_kernel inp) sp mb], from
   [init_config (run_segments ..) ..].  The tree's own statements -- [Fw/Safety.v]'s [SOUND],
   [COMPLETE] and [Refusable.reaches_error_a] -- are over the BINARY's segments [segs] and
   [init_config segs ..], and they must stay there: [Fw3/SymStep.v:1397-1398] guards [sym_load]
   on [segs_novvar segs], which is false of the run's list because the pair carries the vvar
   page.  So the lift happens HERE, once, between [Fw/Safety.v] and the published statement,
   and nothing below [Fw/] changes.

   THE TWO DIFFERENCES, AND WHAT EACH COSTS.
   (1) THE SEGMENT LIST gains the vDSO pair.  The pair is neither executable nor writable, so
       no instruction fetch and no writable view changes (Part 2).  Going BACK from the run's
       list to the binary's needs to know the instruction does not fault over [segs]
       ([mi_ok_of_noerr]) -- which [~ reaches_error_a segs c0] gives at every reachable
       configuration, so it costs no new premise.
   (2) THE READ-ONLY BACKING grows: [init_machine_state]'s [ms_rom] reads
       [memory_read mi_loaded_segments], and the pair adds the vDSO text's bytes
       ([rom_ext_run_segments]).  [segments_reserved] drops the pair, so the model part is
       unchanged and the two start configurations differ in [ms_rom] ALONE
       ([init_config_run_segments]).  No machine step reads [ms_rom]; only a system call does,
       through [Run.sys_input]'s [in_mem] := [ms_read_byte].  Transferring a step therefore
       costs [RomBase.sys_rob] at the configuration (Part 1), and that IS a new premise:
       [rob_reach], below.  It is the one thing this layer cannot discharge from what
       [Fw/Safety.v] already proves.

   PROVENANCE.  Part 1 (minus the walk-relation lemmas), Part 2 (minus the walk-relation
   lemmas) and Part 3 are ported STATEMENT AND PROOF from
   the donor:
     projects/openssl/bignum/proofs/lib/VCommon/Cfg/RomStable.v:36-104,110-132,137-223,238-247
       (Part 1), :267-290,292-514 (Part 2), :529-615 (Part 3)
   whose text for those spans is identical to
     projects/libreac/fuzz_ctrl/proofs/lib/Reusable/RomStableK.v:56-166,170-223,251-321 (Part 1),
     :325-348,350-557 (Part 2), :696-782 (Part 3),
   the named donor.  The two lemmas specific to this tree,
   [rom_ext_run_segments] and [init_config_run_segments], are RomStableK.v:763-769 and
   :772-778 -- STATEMENT AND PROOF -- with [rom_ext], [seg_rom1] and [cwrom] defined tree-side
   ([Fw/RomBase.v], [Fw/RunSeg.v]); none of those four names exists in the model at 75d69e00.
   [vdso_segments_nx] and [vdso_segments_nw] are RomStableK.v:699-706 and :708-715, STATEMENT
   AND PROOF; they are facts about model definitions alone and LPS is to carry them, at which
   point the copies here go.

   WHAT IS WRITTEN FRESH, because every donor states its transfer over a walk relation
   ([YK15.realizes], [ShapeAlgCfg.realizes_cfg]) and THIS TREE HAS NONE -- it proves
   [SOUND]/[COMPLETE] over [Fw/Safety.v] instead: the [star_cfg], [obs_trace_cfg] and
   [reaches_error_cfg] transfers ([star_wrom_fwd], [star_wrom_back], [obs_trace_wrom_iff],
   [reaches_error_wrom_back], [star_app_fwd], [star_app_back], [obs_trace_app_iff],
   [reaches_error_app_back]) and the two theorems at the end.

   The donor's proofs carry over unchanged; their check here is this unit's own build. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase MemImageType RiscvSemantics StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import DecodeC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Refusable RomBase.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(** [vdso_image segs = None] for a concrete binary segment list: none of its segments is the
    vDSO text; by lazy conversion, which reads only the segments' kinds.
    (RomStableK.v:40-41, statement and proof.) *)
Ltac vdso_none :=
  first [ reflexivity | unfold vdso_image, vdso_text_seg; vm_compute; reflexivity ].

(* ------------------------------------------------------------------------------------------
   Part 0: the shape of a [star_cfg], written fresh (the donors never need it: a walk
   relation carries its own induction principle).
   ------------------------------------------------------------------------------------------ *)

Lemma sstep_cfg_halted_none : forall sg cfg c e st,
  sstep_cfg sg cfg c e st -> m_halted (cfg_model c) = None.
Proof.
  intros sg cfg [ms model] e st H. cbn [cfg_model]. inversion H; subst; assumption.
Qed.

Lemma star_cfg_cat : forall sg cfg c1 tr1 c2 tr2 c3,
  star_cfg sg cfg c1 tr1 c2 -> star_cfg sg cfg c2 tr2 c3 ->
  star_cfg sg cfg c1 (tr1 ++ tr2) c3.
Proof.
  intros sg cfg c1 tr1 c2 tr2 c3 H1. induction H1 as [c | c1 evs ca tr cb Hs Hst IH]; intros H2.
  - exact H2.
  - rewrite <- app_assoc. eapply star_cfg_step; [exact Hs | apply IH; exact H2].
Qed.

Lemma star_cfg_one : forall sg cfg c evs c',
  sstep_cfg sg cfg c evs (SNext c') -> star_cfg sg cfg c evs c'.
Proof.
  intros sg cfg c evs c' H. rewrite <- (app_nil_r evs).
  eapply star_cfg_step; [exact H | apply star_cfg_refl].
Qed.

Lemma star_cfg_snoc : forall sg cfg c1 tr c2 evs c3,
  star_cfg sg cfg c1 tr c2 -> sstep_cfg sg cfg c2 evs (SNext c3) ->
  star_cfg sg cfg c1 (tr ++ evs) c3.
Proof.
  intros sg cfg c1 tr c2 evs c3 H1 H2.
  eapply star_cfg_cat; [exact H1 | apply star_cfg_one; exact H2].
Qed.

(* ------------------------------------------------------------------------------------------
   Part 1: a change of the read-only backing
   ------------------------------------------------------------------------------------------ *)

Definition rep_wrom (x : machine_result (access_report machine_state)) (r : word -> option byte)
    : machine_result (access_report machine_state) :=
  match x with
  | MachineOk rep => MachineOk (@mkAccessReport machine_state (wrom (@access_value _ rep) r) (@accessed_ranges _ rep))
  | MachineFault => MachineFault
  | MachineUnmodeled => MachineUnmodeled
  end.

Section Seg.
Variable segs : list Segment.

Lemma decode_exec_accesses_wrom : forall st w r,
  decode_exec_accesses segs (wrom st r) w = rep_wrom (decode_exec_accesses segs st w) r.
Proof.
  intros st w r. unfold decode_exec_accesses.
  destruct (is_ecall w); [reflexivity|].
  destruct (decode_any w) as [[i isz]|]; [| destruct (is_defined_illegal w); reflexivity].
  assert (E1 : ms_regs (wrom st r) = ms_regs st) by reflexivity.
  assert (E2 : ms_fregs (wrom st r) = ms_fregs st) by reflexivity.
  assert (E3 : ms_pc_val (wrom st r) = ms_pc_val st) by reflexivity.
  assert (E4 : ms_fcsr (wrom st r) = ms_fcsr st) by reflexivity.
  assert (E5 : ms_resv (wrom st r) = ms_resv st) by reflexivity.
  assert (E6 : ms_mem (wrom st r) = ms_mem st) by reflexivity.
  rewrite ?E1, ?E2, ?E3, ?E4, ?E5, ?E6.
  destruct (interp_eff_accesses segs _ (ms_mem st)) as [rep| |]; [|reflexivity|reflexivity].
  destruct rep as [[c m'] acc]. reflexivity.
Qed.

Lemma step_accesses_wrom : forall st r,
  step_accesses segs (wrom st r) = rep_wrom (step_accesses segs st) r.
Proof.
  intros st r. unfold step_accesses.
  assert (Ep : ms_pc (wrom st r) = ms_pc st) by reflexivity.
  assert (Em : ms_mem (wrom st r) = ms_mem st) by reflexivity.
  rewrite ?Ep, ?Em.
  destruct (fetch_word segs (ms_pc st)) as [w|]; [apply decode_exec_accesses_wrom|].
  destruct (fetch_word_ov segs (ms_mem st) (ms_pc st)) as [w|]; [apply decode_exec_accesses_wrom|].
  destruct (fetch_tail_any segs (ms_mem st) (ms_pc st)) as [w|]; [apply decode_exec_accesses_wrom|].
  destruct (fetch_failure segs (ms_mem st) (ms_pc st)) eqn:Ef; [|reflexivity|reflexivity].
  exfalso. revert Ef. unfold fetch_failure. cbv zeta.
  repeat match goal with |- context [if ?b then _ else _] => destruct b end;
    intro Ef; discriminate Ef.
Qed.

Lemma mi_account_step_wrom : forall ms model r,
  mi_account_step segs (wrom ms r) model
  = match mi_account_step segs ms model with
    | MachineOk (ms', m') => MachineOk (wrom ms' r, m')
    | MachineFault => MachineFault
    | MachineUnmodeled => MachineUnmodeled
    end.
Proof.
  intros ms model r. unfold mi_account_step. rewrite step_accesses_wrom.
  destruct (step_accesses segs ms) as [rep| |]; cbn [rep_wrom access_value accessed_ranges];
    [|reflexivity|reflexivity].
  destruct (materialize_model_accesses model (@accessed_ranges _ rep)); reflexivity.
Qed.

Lemma mi_account_step_rom : forall ms model ms' m',
  mi_account_step segs ms model = MachineOk (ms', m') -> ms_rom ms' = ms_rom ms.
Proof.
  intros ms model ms' m' H.
  pose proof (mi_account_step_wrom ms model (ms_rom ms)) as E.
  rewrite wrom_eta, H in E. injection E as E. rewrite E. reflexivity.
Qed.

Lemma apply_effect_wrom : forall ms eff r,
  advance_past_svc (apply_effect (wrom ms r) eff) = wrom (advance_past_svc (apply_effect ms eff)) r.
Proof. reflexivity. Qed.

Variable cfg : SpuriousCfg.

(** The refusal filter reads the syscall number and the specification, not [in_mem]'s bytes. *)
Lemma spurious_wrom : forall ms r x8 m eff,
  (forall o, syscall_spec (sys_input segs (wrom ms r) x8) m o <-> syscall_spec (sys_input segs ms x8) m o) ->
  spurious_refusal_cfg cfg (sys_input segs (wrom ms r) x8) m eff
  <-> spurious_refusal_cfg cfg (sys_input segs ms x8) m eff.
Proof.
  intros ms r x8 m eff Hs. unfold spurious_refusal_cfg.
  change (injected_family_off cfg (sys_input segs (wrom ms r) x8)) with (injected_family_off cfg (sys_input segs ms x8)).
  change (refusal_b (sys_input segs (wrom ms r) x8)) with (refusal_b (sys_input segs ms x8)).
  split; intros (H1 & H2 & eff' & m' & evs' & H3 & H4); (split; [exact H1|]); (split; [exact H2|]);
    exists eff', m', evs'; (split; [apply Hs; exact H3 | exact H4]).
Qed.

Lemma nspur_to_wrom : forall ms r x8 m eff,
  (forall o, syscall_spec (sys_input segs (wrom ms r) x8) m o <-> syscall_spec (sys_input segs ms x8) m o) ->
  ~ spurious_refusal_cfg cfg (sys_input segs ms x8) m eff ->
  ~ spurious_refusal_cfg cfg (sys_input segs (wrom ms r) x8) m eff.
Proof. intros ms r x8 m eff Hs Hn Hp. apply Hn. apply (spurious_wrom ms r x8 m eff Hs). exact Hp. Qed.

Lemma nspur_of_wrom : forall ms r x8 m eff,
  (forall o, syscall_spec (sys_input segs (wrom ms r) x8) m o <-> syscall_spec (sys_input segs ms x8) m o) ->
  ~ spurious_refusal_cfg cfg (sys_input segs (wrom ms r) x8) m eff ->
  ~ spurious_refusal_cfg cfg (sys_input segs ms x8) m eff.
Proof. intros ms r x8 m eff Hs Hn Hp. apply Hn. apply (spurious_wrom ms r x8 m eff Hs). exact Hp. Qed.

(** THE NEW PREMISE, and the only one this file adds: at every configuration the binary can
    reach over its OWN segments AND FROM WHICH IT CAN STILL STEP, the system call's
    specification does not change when the read-only backing grows.
    [RomBase.sys_rob_instr] discharges it at an instruction configuration and
    [RomBase.sys_rob_memfree] at a system call whose specification does not read [in_mem];
    the donors get it from their walk relation's node, which this tree has not got.

    THE [m_halted] SIDE CONDITION IS NOT DECORATION.  Every constructor of [Run.sstep_cfg]
    (rocq-linux-process-semantics@75d69e00:theories/LinuxProcessSem/Run.v:2221-2313) asks
    [m_halted model = None], so every use below has it in hand from the step it is
    transferring.  Asking for it here is what keeps the obligation dischargeable at the
    producer end: this tree's [SymExit.ok_halted] (decoded) supplies only [m_halted md =
    Some code] and [tcons], from which [sys_rob] does NOT follow, and a halted
    configuration takes no step for the lift to transfer. *)
Definition rob_from (c0 : config) : Prop :=
  forall tr c, star_cfg segs cfg c0 tr c -> m_halted (cfg_model c) = None -> sys_rob segs c.

Lemma rob_from_here : forall c,
  rob_from c -> m_halted (cfg_model c) = None -> sys_rob segs c.
Proof. intros c H Hh. apply (H [] c); [apply star_cfg_refl | exact Hh]. Qed.

Lemma rob_from_star : forall c tr c', rob_from c -> star_cfg segs cfg c tr c' -> rob_from c'.
Proof.
  intros c tr c' H Hst tr2 d Hst2 Hh. apply (H (tr ++ tr2) d); [|exact Hh].
  eapply star_cfg_cat; [exact Hst | exact Hst2].
Qed.

Lemma rob_from_step : forall c evs c',
  rob_from c -> sstep_cfg segs cfg c evs (SNext c') -> rob_from c'.
Proof.
  intros c evs c' H Hs. eapply rob_from_star; [exact H | apply star_cfg_one; exact Hs].
Qed.

Hypothesis Hvi : vdso_image segs = None.

Lemma vdso_entry_fn_none_seg : forall pc, vdso_entry_fn segs pc = None.
Proof. intros pc. unfold vdso_entry_fn. rewrite Hvi. reflexivity. Qed.

Lemma sstep_cfg_next_rom : forall c e c',
  sstep_cfg segs cfg c e (SNext c') -> ms_rom (cfg_ms c') = ms_rom (cfg_ms c).
Proof.
  intros c e c' H. inversion H; subst; cbn [cfg_ms]; try reflexivity.
  all: first [ eapply mi_account_step_rom; eassumption
             | exfalso; rewrite vdso_entry_fn_none_seg in *; discriminate ].
Qed.

Lemma star_cfg_rom : forall c tr c',
  star_cfg segs cfg c tr c' -> ms_rom (cfg_ms c') = ms_rom (cfg_ms c).
Proof.
  intros c tr c' H. induction H as [c | c1 evs c2 tr c3 Hs Hst IH]; [reflexivity|].
  rewrite IH. exact (sstep_cfg_next_rom c1 evs c2 Hs).
Qed.

(** Forward: a step from [c] is a step from [c] with a larger backing. *)
Lemma sstep_wrom_fwd : forall c e c' r,
  sys_rob segs c -> rom_ext (ms_rom (cfg_ms c)) r ->
  sstep_cfg segs cfg c e (SNext c') -> sstep_cfg segs cfg (cwrom c r) e (SNext (cwrom c' r)).
Proof.
  intros [ms model] e c' r Hrob Hr H. unfold cwrom. cbn [cfg_ms cfg_model] in *.
  inversion H; subst; cbn [cfg_ms cfg_model].
  - apply sstep_cfg_instr; [assumption | assumption |].
    rewrite mi_account_step_wrom.
    match goal with Hm : mi_account_step _ _ _ = MachineOk _ |- _ => rewrite Hm end. reflexivity.
  - exfalso. rewrite vdso_entry_fn_none_seg in *. discriminate.
  - rewrite <- apply_effect_wrom.
    assert (Hs : forall o, syscall_spec (sys_input segs (wrom ms r) x8) model o <-> syscall_spec (sys_input segs ms x8) model o)
      by (intros o; exact (Hrob r x8 Hr ltac:(assumption) o)).
    eapply sstep_cfg_syscall; [eassumption | eassumption | apply Hs; eassumption
                               | apply (nspur_to_wrom _ _ _ _ _ Hs); assumption | eassumption | eassumption].
  - assert (Hs : forall o, syscall_spec (sys_input segs (wrom ms r) x8) model o <-> syscall_spec (sys_input segs ms x8) model o)
      by (intros o; exact (Hrob r x8 Hr ltac:(assumption) o)).
    eapply sstep_cfg_exit; [eassumption | eassumption | apply Hs; eassumption | eassumption | eassumption].
  - assert (Hs : forall o, syscall_spec (sys_input segs (wrom ms r) x8) model o <-> syscall_spec (sys_input segs ms x8) model o)
      by (intros o; exact (Hrob r x8 Hr ltac:(assumption) o)).
    eapply sstep_cfg_killed; [eassumption | eassumption | apply Hs; eassumption | eassumption].
Qed.

(** Backward: every step from the larger backing is one from [c], mapped. *)
Lemma sstep_wrom_back : forall c e st r,
  sys_rob segs c -> rom_ext (ms_rom (cfg_ms c)) r ->
  sstep_cfg segs cfg (cwrom c r) e st ->
  exists st0, sstep_cfg segs cfg c e st0
         /\ st = match st0 with SNext c0 => SNext (cwrom c0 r) | SError => SError end.
Proof.
  intros [ms model] e st r Hrob Hr H. unfold cwrom in H. cbn [cfg_ms cfg_model] in *.
  assert (Hs : forall x8, ms_svc_pending ms = Some x8 ->
            forall o, syscall_spec (sys_input segs (wrom ms r) x8) model o <-> syscall_spec (sys_input segs ms x8) model o)
    by (intros x8 Hx o; exact (Hrob r x8 Hr Hx o)).
  remember (wrom ms r) as ms2 eqn:E2.
  inversion H; subst.
  - match goal with Hm : mi_account_step _ (wrom ms r) _ = MachineOk (?a, ?b) |- _ =>
      rewrite mi_account_step_wrom in Hm;
      destruct (mi_account_step segs ms model) as [[ms1 m1]| |] eqn:Em; try discriminate Hm;
      injection Hm as <- <- end.
    exists (SNext (mkCfg ms1 m1)). split; [apply sstep_cfg_instr; assumption | reflexivity].
  - match goal with Hm : mi_account_step _ (wrom ms r) _ = MachineFault |- _ =>
      rewrite mi_account_step_wrom in Hm;
      destruct (mi_account_step segs ms model) as [[ms1 m1]| |] eqn:Em; try discriminate Hm end.
    exists SError. split; [apply sstep_cfg_instr_fault; assumption | reflexivity].
  - match goal with Hm : mi_account_step _ (wrom ms r) _ = MachineUnmodeled |- _ =>
      rewrite mi_account_step_wrom in Hm;
      destruct (mi_account_step segs ms model) as [[ms1 m1]| |] eqn:Em; try discriminate Hm end.
    exists SError. split; [apply sstep_cfg_instr_unmodeled; assumption | reflexivity].
  - exfalso. rewrite vdso_entry_fn_none_seg in *. discriminate.
  - exfalso. rewrite vdso_entry_fn_none_seg in *. discriminate.
  - exfalso. rewrite vdso_entry_fn_none_seg in *. discriminate.
  - exists (SNext (mkCfg (advance_past_svc (apply_effect ms eff)) model'')).
    split; [| reflexivity].
    pose proof (Hs x8 ltac:(assumption)) as Hx.
    eapply sstep_cfg_syscall; [eassumption | eassumption | apply Hx; eassumption
                               | apply (nspur_of_wrom _ _ _ _ _ Hx); assumption | eassumption | eassumption].
  - exists SError. split; [| reflexivity].
    pose proof (Hs x8 ltac:(assumption)) as Hx.
    eapply sstep_cfg_syscall_materialization_fault; [eassumption | eassumption | apply Hx; eassumption
                               | apply (nspur_of_wrom _ _ _ _ _ Hx); assumption | eassumption | eassumption].
  - exists (SNext (mkCfg ms model')). split; [| reflexivity].
    pose proof (Hs x8 ltac:(assumption)) as Hx.
    eapply sstep_cfg_exit; [eassumption | eassumption | apply Hx; eassumption | eassumption | eassumption].
  - exists (SNext (mkCfg ms model')). split; [| reflexivity].
    pose proof (Hs x8 ltac:(assumption)) as Hx.
    eapply sstep_cfg_killed; [eassumption | eassumption | apply Hx; eassumption | eassumption].
  - exists SError. split; [| reflexivity].
    pose proof (Hs x8 ltac:(assumption)) as Hx.
    eapply sstep_cfg_syscall_unmodeled; [eassumption | eassumption | apply Hx; eassumption].
Qed.

(** The node at the larger backing is robust too: the larger backing's own extensions are the
    original's. *)
Lemma sys_rob_wrom : forall c r, sys_rob segs c -> rom_ext (ms_rom (cfg_ms c)) r -> sys_rob segs (cwrom c r).
Proof.
  intros [ms m] r Hrob Hr r2 x8 Hr2 Hs o. unfold cwrom in *. cbn [cfg_ms cfg_model] in *.
  change (wrom (wrom ms r) r2) with (wrom ms r2).
  change (ms_svc_pending (wrom ms r)) with (ms_svc_pending ms) in Hs.
  change (ms_rom (wrom ms r)) with r in Hr2.
  cbn [cfg_ms cfg_model] in Hrob.
  rewrite (Hrob r2 x8 (rom_ext_trans _ _ _ Hr Hr2) Hs o).
  symmetry. exact (Hrob r x8 Hr Hs o).
Qed.

(** FRESH, because the donors state this over a walk relation this tree has not got. *)
Lemma star_wrom_fwd : forall c tr c' r,
  rob_from c -> rom_ext (ms_rom (cfg_ms c)) r ->
  star_cfg segs cfg c tr c' -> star_cfg segs cfg (cwrom c r) tr (cwrom c' r).
Proof.
  intros c tr c' r Hrob Hr H. revert Hrob Hr.
  induction H as [c | c1 evs c2 tr c3 Hs Hst IH]; intros Hrob Hr.
  - apply star_cfg_refl.
  - eapply star_cfg_step.
    + exact (sstep_wrom_fwd c1 evs c2 r
               (rob_from_here c1 Hrob (sstep_cfg_halted_none _ _ _ _ _ Hs)) Hr Hs).
    + apply IH; [exact (rob_from_step c1 evs c2 Hrob Hs)|].
      rewrite (sstep_cfg_next_rom c1 evs c2 Hs). exact Hr.
Qed.

Lemma star_wrom_back : forall r cv tr d,
  star_cfg segs cfg cv tr d ->
  forall c, cv = cwrom c r -> rob_from c -> rom_ext (ms_rom (cfg_ms c)) r ->
  exists c', d = cwrom c' r /\ star_cfg segs cfg c tr c'.
Proof.
  intros r cv tr d H. induction H as [cv | c1 evs c2 tr c3 Hs Hst IH];
    intros c Hc Hrob Hr; subst.
  - exists c. split; [reflexivity | apply star_cfg_refl].
  - destruct (sstep_wrom_back c evs (SNext c2) r
                (rob_from_here c Hrob (sstep_cfg_halted_none _ _ _ _ _ Hs)) Hr Hs)
      as (st0 & H0 & Heq).
    destruct st0 as [c1'|]; [|discriminate Heq].
    injection Heq as Heq2.
    assert (Hr' : rom_ext (ms_rom (cfg_ms c1')) r)
      by (rewrite (sstep_cfg_next_rom c evs c1' H0); exact Hr).
    destruct (IH c1' Heq2 (rob_from_step c evs c1' Hrob H0) Hr') as (c3' & -> & Hst').
    exists c3'. split; [reflexivity|]. eapply star_cfg_step; [exact H0 | exact Hst'].
Qed.

Lemma reaches_error_wrom_back : forall c r,
  rob_from c -> rom_ext (ms_rom (cfg_ms c)) r ->
  reaches_error_cfg segs cfg (cwrom c r) -> reaches_error_cfg segs cfg c.
Proof.
  intros c r Hrob Hr (tr & d & evs & Hst & He).
  destruct (star_wrom_back r (cwrom c r) tr d Hst c eq_refl Hrob Hr) as (c' & -> & Hst').
  assert (Hr' : rom_ext (ms_rom (cfg_ms c')) r)
    by (rewrite (star_cfg_rom c tr c' Hst'); exact Hr).
  destruct (sstep_wrom_back c' evs SError r
              (rob_from_here c' (rob_from_star c tr c' Hrob Hst')
                 (sstep_cfg_halted_none _ _ _ _ _ He)) Hr' He) as (st0 & H0 & Heq).
  destruct st0 as [c2|]; [discriminate Heq|].
  exists tr, c', evs. split; [exact Hst' | exact H0].
Qed.

Lemma obs_trace_wrom_iff : forall c r tr,
  rob_from c -> rom_ext (ms_rom (cfg_ms c)) r ->
  (obs_trace_cfg segs cfg (cwrom c r) tr <-> obs_trace_cfg segs cfg c tr).
Proof.
  intros c r tr Hrob Hr. split.
  - intros (tr' & d & Hst & Hp).
    destruct (star_wrom_back r (cwrom c r) tr' d Hst c eq_refl Hrob Hr) as (c' & -> & Hst').
    exists tr', c'. split; [exact Hst' | exact Hp].
  - intros (tr' & c' & Hst & Hp).
    exists tr', (cwrom c' r). split; [| exact Hp].
    exact (star_wrom_fwd c tr' c' r Hrob Hr Hst).
Qed.

End Seg.

(* ------------------------------------------------------------------------------------------
   Part 2: the run's segment list
   ------------------------------------------------------------------------------------------ *)

Lemma find_segment_app : forall segs tail addr n,
  find_segment (segs ++ tail) addr n
  = match find_segment segs addr n with
    | Some s => Some s
    | None => find_segment tail addr n
    end.
Proof.
  induction segs as [|seg rest IH]; intros tail addr n; [reflexivity|].
  cbn [find_segment app].
  destruct (Z.leb (Z.of_N (seg_base seg)) addr
            && Z.leb (addr + n) (Z.of_N (seg_base seg) + Z.of_N (seg_size seg)))%bool;
    [reflexivity | apply IH].
Qed.

Lemma find_segment_in : forall segs addr n s,
  find_segment segs addr n = Some s -> In s segs.
Proof.
  induction segs as [|seg rest IH]; intros addr n s H; [discriminate H|].
  cbn [find_segment] in H.
  destruct (Z.leb (Z.of_N (seg_base seg)) addr
            && Z.leb (addr + n) (Z.of_N (seg_base seg) + Z.of_N (seg_size seg)))%bool.
  - injection H as <-. left. reflexivity.
  - right. exact (IH _ _ _ H).
Qed.

Section AppTail.
  Variables segs tail : list Segment.
  Hypothesis Hnx : forall s, In s tail -> seg_executable s = false.
  Hypothesis Hnw : forall s, In s tail -> seg_writable s = false.

  Lemma code_read_app_nx : forall a n,
    code_read (segs ++ tail) a n = code_read segs a n.
  Proof.
    intros a n. unfold code_read. rewrite find_segment_app.
    destruct (find_segment segs (bv_unsigned a) (Z.of_N n)) as [s|]; [reflexivity|].
    destruct (find_segment tail (bv_unsigned a) (Z.of_N n)) as [s|] eqn:E; [|reflexivity].
    rewrite (Hnx s (find_segment_in _ _ _ _ E)). reflexivity.
  Qed.

  Lemma code_read_ov_app_nx : forall m a n,
    code_read_ov (segs ++ tail) m a n = code_read_ov segs m a n.
  Proof.
    intros m a n. unfold code_read_ov. rewrite find_segment_app.
    destruct (find_segment segs (bv_unsigned a) (Z.of_N n)) as [s|]; [reflexivity|].
    destruct (find_segment tail (bv_unsigned a) (Z.of_N n)) as [s|] eqn:E; [|reflexivity].
    rewrite (Hnx s (find_segment_in _ _ _ _ E)). reflexivity.
  Qed.

  Lemma fetch_word_app_nx : forall a,
    fetch_word (segs ++ tail) a = fetch_word segs a.
  Proof. intros a. unfold fetch_word. rewrite code_read_app_nx. reflexivity. Qed.

  Lemma fetch_word_ov_app_nx : forall m a,
    fetch_word_ov (segs ++ tail) m a = fetch_word_ov segs m a.
  Proof. intros m a. unfold fetch_word_ov. rewrite code_read_ov_app_nx. reflexivity. Qed.

  Lemma fetch_half_any_app_nx : forall m a,
    fetch_half_any (segs ++ tail) m a = fetch_half_any segs m a.
  Proof.
    intros m a. unfold fetch_half_any, fetch_half, fetch_half_ov.
    rewrite code_read_app_nx, code_read_ov_app_nx. reflexivity.
  Qed.

  Lemma fetch_tail_any_app_nx : forall m a,
    fetch_tail_any (segs ++ tail) m a = fetch_tail_any segs m a.
  Proof.
    intros m a. unfold fetch_tail_any. rewrite !fetch_half_any_app_nx. reflexivity.
  Qed.

  Lemma memory_read_app_nx : forall a n bs,
    memory_read segs a n = Some bs -> memory_read (segs ++ tail) a n = Some bs.
  Proof.
    intros a n bs. unfold memory_read. rewrite find_segment_app.
    destruct (find_segment segs (bv_unsigned a) (Z.of_N n)) as [s|];
      [intro H; exact H | intro H; discriminate H].
  Qed.

  Lemma ov_read_bytes_app_nx : forall n m a bs,
    ov_read_bytes segs m a n = Some bs -> ov_read_bytes (segs ++ tail) m a n = Some bs.
  Proof.
    induction n as [|n IH]; intros m a bs; cbn [ov_read_bytes]; [intro H; exact H|].
    destruct (m a) as [b|].
    - destruct (ov_read_bytes segs m (a + 1) n) as [rest|] eqn:E; [|intro H; discriminate H].
      rewrite (IH _ _ _ E). intro H; exact H.
    - destruct (memory_read segs a 1) as [[|b rest0]|] eqn:Em;
        [intro H; discriminate H | | intro H; discriminate H].
      rewrite (memory_read_app_nx _ _ _ Em).
      destruct (ov_read_bytes segs m (a + 1) n) as [rest|] eqn:E; [|intro H; discriminate H].
      rewrite (IH _ _ _ E). intro H; exact H.
  Qed.

  Lemma wview_app_nw : forall m a, wview (segs ++ tail) m a = wview segs m a.
  Proof.
    intros m a. unfold wview. destruct (m a) as [b|]; [reflexivity|].
    rewrite find_segment_app.
    destruct (find_segment segs (bv_unsigned a) 1) as [s|]; [reflexivity|].
    destruct (find_segment tail (bv_unsigned a) 1) as [s|] eqn:E; [|reflexivity].
    rewrite (Hnw s (find_segment_in _ _ _ _ E)). reflexivity.
  Qed.

  Lemma store_ok_app_nw : forall n m a,
    store_ok (segs ++ tail) m a n = store_ok segs m a n.
  Proof.
    induction n as [|n IH]; intros m a; cbn [store_ok]; [reflexivity|].
    rewrite wview_app_nw. destruct (wview segs m a); [apply IH | reflexivity].
  Qed.

  Lemma interp_eff_accesses_app_nx : forall t m r,
    interp_eff_accesses segs t m = MachineOk r ->
    interp_eff_accesses (segs ++ tail) t m = MachineOk r.
  Proof.
    induction t as [c|c|c|c|c|c|n a k IH|n a v k IH]; intros m r;
      cbn [interp_eff_accesses]; try (intro H; exact H).
    - destruct (ov_read_bytes segs m a (width_bytes n)) as [bs|] eqn:E.
      + rewrite (ov_read_bytes_app_nx _ _ _ _ E).
        match goal with
        | |- context [interp_eff_accesses segs ?t' ?m'] =>
            destruct (interp_eff_accesses segs t' m') as [rep| |] eqn:E2;
              [| intro H; discriminate H | intro H; discriminate H]
        end.
        rewrite (IH _ _ _ E2). intro H; exact H.
      + destruct (range_meets_vvar segs a (width_bytes n)); intro H; discriminate H.
    - rewrite store_ok_app_nw.
      destruct (store_ok segs m a (width_bytes n)) eqn:E; [|intro H; discriminate H].
      match goal with
      | |- context [interp_eff_accesses segs k ?m'] =>
          destruct (interp_eff_accesses segs k m') as [rep| |] eqn:E2;
            [| intro H; discriminate H | intro H; discriminate H]
      end.
      rewrite (IH _ _ E2). intro H; exact H.
  Qed.

  Lemma decode_exec_accesses_app_nx : forall st w rep,
    decode_exec_accesses segs st w = MachineOk rep ->
    decode_exec_accesses (segs ++ tail) st w = MachineOk rep.
  Proof.
    intros st w rep. unfold decode_exec_accesses.
    destruct (is_ecall w); [intro H; exact H|].
    destruct (decode_any w) as [[i isz]|]; [|intro H; exact H].
    match goal with
    | |- context [interp_eff_accesses segs ?t ?m] =>
        destruct (interp_eff_accesses segs t m) as [r| |] eqn:E;
          [rewrite (interp_eff_accesses_app_nx _ _ _ E); intro H; exact H
          | intro H; discriminate H | intro H; discriminate H]
    end.
  Qed.

  Lemma step_accesses_app_nx : forall st rep,
    step_accesses segs st = MachineOk rep ->
    step_accesses (segs ++ tail) st = MachineOk rep.
  Proof.
    intros st rep. unfold step_accesses.
    rewrite fetch_word_app_nx, fetch_word_ov_app_nx, fetch_tail_any_app_nx.
    destruct (fetch_word segs (ms_pc st)) as [w|]; [apply decode_exec_accesses_app_nx|].
    destruct (fetch_word_ov segs (ms_mem st) (ms_pc st)) as [w|];
      [apply decode_exec_accesses_app_nx|].
    destruct (fetch_tail_any segs (ms_mem st) (ms_pc st)) as [w|];
      [apply decode_exec_accesses_app_nx|].
    destruct (fetch_failure segs (ms_mem st) (ms_pc st)) eqn:Ef;
      [| intro H; discriminate H | intro H; discriminate H].
    exfalso. revert Ef. unfold fetch_failure. cbv zeta.
    repeat match goal with |- context [if ?b then _ else _] => destruct b end;
      intro Ef; discriminate Ef.
  Qed.

  Lemma mi_account_step_app_nx : forall ms model r,
    mi_account_step segs ms model = MachineOk r ->
    mi_account_step (segs ++ tail) ms model = MachineOk r.
  Proof.
    intros ms model r. unfold mi_account_step.
    destruct (step_accesses segs ms) as [rep| |] eqn:E;
      [rewrite (step_accesses_app_nx _ _ E); intro H; exact H
      | intro H; discriminate H | intro H; discriminate H].
  Qed.

  Lemma sys_input_app_nw : forall ms x8,
    sys_input (segs ++ tail) ms x8 = sys_input segs ms x8.
  Proof.
    intros ms x8. unfold sys_input. f_equal.
    apply functional_extensionality. intro a. unfold ms_writable_byte. apply wview_app_nw.
  Qed.

  Hypothesis Hvi : vdso_image segs = None.

  Lemma vdso_entry_fn_none : forall pc, vdso_entry_fn segs pc = None.
  Proof. intros pc. unfold vdso_entry_fn. rewrite Hvi. reflexivity. Qed.

  Variable cfg : SpuriousCfg.

  Lemma sstep_cfg_app_next : forall c e c',
    sstep_cfg segs cfg c e (SNext c') -> sstep_cfg (segs ++ tail) cfg c e (SNext c').
  Proof.
    intros c e c' H. inversion H; subst.
    - eapply sstep_cfg_instr; [assumption | assumption |].
      apply mi_account_step_app_nx. assumption.
    - exfalso. rewrite vdso_entry_fn_none in *. discriminate.
    - eapply sstep_cfg_syscall; rewrite ?sys_input_app_nw; eassumption.
    - eapply sstep_cfg_exit; rewrite ?sys_input_app_nw; eassumption.
    - eapply sstep_cfg_killed; rewrite ?sys_input_app_nw; eassumption.
  Qed.

  Lemma sstep_cfg_app_back : forall ms model e st,
    (ms_svc_pending ms = None -> exists r, mi_account_step segs ms model = MachineOk r) ->
    sstep_cfg (segs ++ tail) cfg (mkCfg ms model) e st ->
    sstep_cfg segs cfg (mkCfg ms model) e st.
  Proof.
    intros ms model e st Hok H. inversion H; subst.
    - destruct (Hok ltac:(assumption)) as (r & Hr).
      pose proof (mi_account_step_app_nx _ _ _ Hr) as Hr'.
      match goal with Hb : mi_account_step (_ ++ _) _ _ = MachineOk _ |- _ =>
        rewrite Hr' in Hb; injection Hb as Hb'; subst r end.
      eapply sstep_cfg_instr; eassumption.
    - exfalso. destruct (Hok ltac:(assumption)) as (r & Hr).
      pose proof (mi_account_step_app_nx _ _ _ Hr) as Hr'. congruence.
    - exfalso. destruct (Hok ltac:(assumption)) as (r & Hr).
      pose proof (mi_account_step_app_nx _ _ _ Hr) as Hr'. congruence.
    - exfalso. destruct (Hok ltac:(assumption)) as (r & Hr).
      pose proof (mi_account_step_app_nx _ _ _ Hr) as Hr'. congruence.
    - exfalso. destruct (Hok ltac:(assumption)) as (r & Hr).
      pose proof (mi_account_step_app_nx _ _ _ Hr) as Hr'. congruence.
    - exfalso. destruct (Hok ltac:(assumption)) as (r & Hr).
      pose proof (mi_account_step_app_nx _ _ _ Hr) as Hr'. congruence.
    - rewrite sys_input_app_nw in *. eapply sstep_cfg_syscall; eassumption.
    - rewrite sys_input_app_nw in *. eapply sstep_cfg_syscall_materialization_fault; eassumption.
    - rewrite sys_input_app_nw in *. eapply sstep_cfg_exit; eassumption.
    - rewrite sys_input_app_nw in *. eapply sstep_cfg_killed; eassumption.
    - rewrite sys_input_app_nw in *. eapply sstep_cfg_syscall_unmodeled; eassumption.
  Qed.

  (* the input is the same over both lists ([sys_input_app_nw]), so robustness carries over *)
  Lemma sys_rob_app_tail : forall c, sys_rob segs c -> sys_rob (segs ++ tail) c.
  Proof.
    intros c H r x8 Hr Hs o. rewrite !sys_input_app_nw. exact (H r x8 Hr Hs o).
  Qed.

  (** FRESH.  The donors get [Hok] from a walk's node; this tree gets it from the
      error-freedom it already proves: an instruction that faults or is unmodeled at a
      reachable configuration IS an [SError] step over [segs]. *)
  Lemma mi_ok_of_noerr : forall c0 tr ms model,
    ~ reaches_error_cfg segs cfg c0 ->
    star_cfg segs cfg c0 tr (mkCfg ms model) ->
    m_halted model = None -> ms_svc_pending ms = None ->
    exists p, mi_account_step segs ms model = MachineOk p.
  Proof.
    intros c0 tr ms model Hne Hst Hh Hsvc.
    destruct (mi_account_step segs ms model) as [p| |] eqn:E.
    - exists p. reflexivity.
    - exfalso. apply Hne. exists tr, (mkCfg ms model), [].
      split; [exact Hst | apply sstep_cfg_instr_fault; assumption].
    - exfalso. apply Hne. exists tr, (mkCfg ms model), [].
      split; [exact Hst|].
      apply sstep_cfg_instr_unmodeled;
        [assumption | assumption | assumption | apply vdso_entry_fn_none].
  Qed.

  Lemma star_app_fwd : forall c tr c',
    star_cfg segs cfg c tr c' -> star_cfg (segs ++ tail) cfg c tr c'.
  Proof.
    intros c tr c' H. induction H as [c | c1 evs c2 tr c3 Hs Hst IH]; [apply star_cfg_refl|].
    eapply star_cfg_step; [apply sstep_cfg_app_next; exact Hs | exact IH].
  Qed.

  Lemma star_app_back_aux : forall c1 tr c2,
    star_cfg (segs ++ tail) cfg c1 tr c2 ->
    forall c0 tr0, ~ reaches_error_cfg segs cfg c0 -> star_cfg segs cfg c0 tr0 c1 ->
    star_cfg segs cfg c1 tr c2.
  Proof.
    intros c1 tr c2 H. induction H as [c | ca evs cb tr cc Hs Hst IH]; intros c0 tr0 Hne H0.
    - apply star_cfg_refl.
    - assert (Hs' : sstep_cfg segs cfg ca evs (SNext cb)).
      { destruct ca as [ms model].
        apply (sstep_cfg_app_back ms model evs (SNext cb)); [|exact Hs].
        intros Hsvc.
        exact (mi_ok_of_noerr c0 tr0 ms model Hne H0
                 (sstep_cfg_halted_none _ _ _ _ _ Hs) Hsvc). }
      eapply star_cfg_step; [exact Hs'|].
      apply (IH c0 (tr0 ++ evs)); [exact Hne|].
      eapply star_cfg_snoc; [exact H0 | exact Hs'].
  Qed.

  Lemma star_app_back : forall c0 tr c,
    ~ reaches_error_cfg segs cfg c0 ->
    star_cfg (segs ++ tail) cfg c0 tr c -> star_cfg segs cfg c0 tr c.
  Proof.
    intros c0 tr c Hne H.
    exact (star_app_back_aux c0 tr c H c0 [] Hne (star_cfg_refl segs cfg c0)).
  Qed.

  Lemma reaches_error_app_back : forall c0,
    ~ reaches_error_cfg segs cfg c0 -> ~ reaches_error_cfg (segs ++ tail) cfg c0.
  Proof.
    intros c0 Hne (tr & c & evs & Hst & He).
    pose proof (star_app_back c0 tr c Hne Hst) as Hst'.
    destruct c as [ms model].
    apply Hne. exists tr, (mkCfg ms model), evs. split; [exact Hst'|].
    apply (sstep_cfg_app_back ms model evs SError); [|exact He].
    intros Hsvc.
    exact (mi_ok_of_noerr c0 tr ms model Hne Hst'
             (sstep_cfg_halted_none _ _ _ _ _ He) Hsvc).
  Qed.

  Lemma obs_trace_app_iff : forall c0 tr,
    ~ reaches_error_cfg segs cfg c0 ->
    (obs_trace_cfg (segs ++ tail) cfg c0 tr <-> obs_trace_cfg segs cfg c0 tr).
  Proof.
    intros c0 tr Hne. split.
    - intros (tr' & c & Hst & Hp). exists tr', c.
      split; [exact (star_app_back c0 tr' c Hne Hst) | exact Hp].
    - intros (tr' & c & Hst & Hp). exists tr', c.
      split; [exact (star_app_fwd c0 tr' c Hst) | exact Hp].
  Qed.

End AppTail.

(* ------------------------------------------------------------------------------------------
   Part 3: the run's own start
   ------------------------------------------------------------------------------------------ *)

Section VdsoPair.
  Local Transparent vdso_segments.

  Lemma vdso_segments_nx : forall kb (sp mbase : word) s,
    In s (vdso_segments kb sp mbase) -> seg_executable s = false.
  Proof.
    intros kb sp mbase s H. unfold vdso_segments in H. cbv zeta in H.
    match type of H with In _ (if ?b then _ else _) => destruct b end;
      [destruct H|].
    destruct H as [<-|[<-|[]]]; reflexivity.
  Qed.

  Lemma vdso_segments_nw : forall kb (sp mbase : word) s,
    In s (vdso_segments kb sp mbase) -> seg_writable s = false.
  Proof.
    intros kb sp mbase s H. unfold vdso_segments in H. cbv zeta in H.
    match type of H with In _ (if ?b then _ else _) => destruct b end;
      [destruct H|].
    destruct H as [<-|[<-|[]]]; reflexivity.
  Qed.

  Lemma segments_reserved_vdso : forall kb (sp mbase : word),
    segments_reserved (vdso_segments kb sp mbase) = [].
  Proof.
    intros kb sp mbase. unfold vdso_segments. cbv zeta.
    match goal with |- segments_reserved (if ?b then _ else _) = _ => destruct b end;
      reflexivity.
  Qed.
End VdsoPair.

(* [segments_reserved]'s [filter] is stdpp's (through BvBase): by induction and conversion. *)
Lemma segments_reserved_app : forall a b,
  segments_reserved (a ++ b) = segments_reserved a ++ segments_reserved b.
Proof.
  intros a b. unfold segments_reserved.
  induction a as [|s a IH]; [reflexivity|].
  cbn [app]. destruct s as [sb ssz sp sby sk]. destruct sk;
    match goal with
    | |- context [?s0 :: a ++ b] =>
        first [ exact IH | exact (f_equal (cons (segment_reservation s0)) IH) ]
    end.
Qed.

Lemma segments_reserved_run_segments : forall segs inp (sp mb : word),
  segments_reserved (run_segments segs inp sp mb) = segments_reserved segs.
Proof.
  intros segs inp sp mb. unfold run_segments.
  rewrite segments_reserved_app, segments_reserved_vdso, app_nil_r. reflexivity.
Qed.

(** THE FIRST OF THE TWO LEMMAS THIS TREE OWNS.  [seg_rom1], [rom_ext] and [cwrom] are
    tree-side ([Fw/RomBase.v]); none of the three is in the model at 75d69e00.
    RomStableK.v:760-769, statement and proof. *)
Definition seg_rom1 (segs : list Segment) : word -> option byte :=
  fun addr => match memory_read segs addr 1 with Some (b :: _) => Some b | _ => None end.

Lemma rom_ext_run_segments : forall segs inp (sp mb : word),
  rom_ext (seg_rom1 segs) (seg_rom1 (run_segments segs inp sp mb)).
Proof.
  intros segs inp sp mb a b. unfold seg_rom1, run_segments.
  destruct (memory_read segs a 1) as [bs|] eqn:E; [|intro H; discriminate H].
  rewrite (memory_read_app_nx segs _ _ _ _ E). intro H; exact H.
Qed.

(** THE SECOND.  The run's start configuration is the binary's with the run's backing:
    [segments_reserved] drops the pair, so the model part is untouched and [ms_rom] is the
    only field that moves.  RomStableK.v:772-778, statement and proof. *)
Lemma init_config_run_segments : forall segs inp (sp mb : word) pc ph brk rnd lim,
  init_config (run_segments segs inp sp mb) pc ph sp brk mb rnd lim inp
  = cwrom (init_config segs pc ph sp brk mb rnd lim inp) (seg_rom1 (run_segments segs inp sp mb)).
Proof.
  intros segs inp sp mb pc ph brk rnd lim. unfold init_config, cwrom.
  cbn [cfg_ms cfg_model]. rewrite segments_reserved_run_segments. reflexivity.
Qed.

Lemma init_config_rom : forall segs inp (sp : word) mb pc ph brk rnd lim,
  ms_rom (cfg_ms (init_config segs pc ph sp brk mb rnd lim inp)) = seg_rom1 segs.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------------------------------
   Part 4: the run's own statement, composed.  FRESH: the donors compose into [run_init] over
   a walk relation; these two compose into the observations [Run.run_scfg] actually reports.
   ------------------------------------------------------------------------------------------ *)

(** An error the RUN can reach is one the binary can reach over its own segments. *)
Theorem reaches_error_run_init :
  forall cfg segs inp (sp brk mb : word) pc ph rnd lim,
  vdso_image segs = None ->
  rob_from segs cfg (init_config segs pc ph sp brk mb rnd lim inp) ->
  ~ reaches_error_cfg segs cfg (init_config segs pc ph sp brk mb rnd lim inp) ->
  ~ reaches_error_cfg (run_segments segs inp sp mb) cfg
      (init_config (run_segments segs inp sp mb) pc ph sp brk mb rnd lim inp).
Proof.
  intros cfg segs inp sp brk mb pc ph rnd lim Hvi Hrob Hne.
  assert (Hne2 : ~ reaches_error_cfg segs cfg
                   (cwrom (init_config segs pc ph sp brk mb rnd lim inp)
                          (seg_rom1 (run_segments segs inp sp mb)))).
  { intros Hc. apply Hne.
    apply reaches_error_wrom_back with (r := seg_rom1 (run_segments segs inp sp mb));
      try exact Hvi; try exact Hrob; try exact Hc.
    rewrite init_config_rom. apply rom_ext_run_segments. }
  rewrite init_config_run_segments. unfold run_segments at 1.
  apply reaches_error_app_back; try exact Hvi; try exact Hne2;
    intros s Hs; first [ exact (vdso_segments_nx _ _ _ s Hs)
                       | exact (vdso_segments_nw _ _ _ s Hs) ].
Qed.

(** The RUN's traces are the binary's over its own segments. *)
Theorem obs_trace_run_init :
  forall cfg segs inp (sp brk mb : word) pc ph rnd lim tr,
  vdso_image segs = None ->
  rob_from segs cfg (init_config segs pc ph sp brk mb rnd lim inp) ->
  ~ reaches_error_cfg segs cfg (init_config segs pc ph sp brk mb rnd lim inp) ->
  (obs_trace_cfg (run_segments segs inp sp mb) cfg
     (init_config (run_segments segs inp sp mb) pc ph sp brk mb rnd lim inp) tr
   <-> obs_trace_cfg segs cfg (init_config segs pc ph sp brk mb rnd lim inp) tr).
Proof.
  intros cfg segs inp sp brk mb pc ph rnd lim tr Hvi Hrob Hne.
  assert (Hr : rom_ext (ms_rom (cfg_ms (init_config segs pc ph sp brk mb rnd lim inp)))
                       (seg_rom1 (run_segments segs inp sp mb)))
    by (rewrite init_config_rom; apply rom_ext_run_segments).
  assert (Hne2 : ~ reaches_error_cfg segs cfg
                   (cwrom (init_config segs pc ph sp brk mb rnd lim inp)
                          (seg_rom1 (run_segments segs inp sp mb)))).
  { intros Hc. apply Hne.
    apply reaches_error_wrom_back with (r := seg_rom1 (run_segments segs inp sp mb));
      try exact Hvi; try exact Hrob; try exact Hc; try exact Hr. }
  assert (Hiff1 : obs_trace_cfg (segs ++ vdso_segments (in_kernel inp) sp mb) cfg
                    (cwrom (init_config segs pc ph sp brk mb rnd lim inp)
                           (seg_rom1 (run_segments segs inp sp mb))) tr
                  <-> obs_trace_cfg segs cfg
                    (cwrom (init_config segs pc ph sp brk mb rnd lim inp)
                           (seg_rom1 (run_segments segs inp sp mb))) tr).
  { apply obs_trace_app_iff; try exact Hvi; try exact Hne2;
      intros s Hs; first [ exact (vdso_segments_nx _ _ _ s Hs)
                         | exact (vdso_segments_nw _ _ _ s Hs) ]. }
  assert (Hiff2 : obs_trace_cfg segs cfg
                    (cwrom (init_config segs pc ph sp brk mb rnd lim inp)
                           (seg_rom1 (run_segments segs inp sp mb))) tr
                  <-> obs_trace_cfg segs cfg (init_config segs pc ph sp brk mb rnd lim inp) tr).
  { apply obs_trace_wrom_iff; try exact Hvi; try exact Hrob; try exact Hr. }
  rewrite init_config_run_segments. unfold run_segments at 1.
  split; intro H.
  - exact (proj1 Hiff2 (proj1 Hiff1 H)).
  - exact (proj2 Hiff1 (proj2 Hiff2 H)).
Qed.

(* ------------------------------------------------------------------------------------------
   Part 5: the same two, at the tree's own configuration [Refusable.ACFG] and under the
   tree's own names.
   ------------------------------------------------------------------------------------------ *)

(** The new premise, at [ACFG]: every configuration the binary reaches over its OWN segments,
    and from which it can still step, is robust against the read-only backing growing. *)
Definition rob_reach (segs : list Segment) (c0 : config) : Prop := rob_from segs ACFG c0.

(** WHAT A PRODUCER ACTUALLY HAS TO SHOW, after the two obligations this layer discharges for
    it.  An instruction configuration is robust for nothing ([RomBase.sys_rob_instr]), and a
    HALTED one is never asked, so only the reachable SYSTEM-CALL configurations with
    [m_halted = None] are at issue; of those, [RomBase.sys_rob_memfree] closes every number
    whose specification does not read [in_mem] (57, 63, 93, 94, 96, 172-178, 214, 215, 222,
    226, 233 -- [RomBase.memfree_lit]).

    The three premises below are exactly the ones this tree's own encoded obligation
    [SymCall.ok_pframe] already carries, bar the syscall number: decoded under [-vok] it is
    [forall tr ms md x8, K tr md -> ms_svc_pending ms = Some x8 ->
     SysStep.only_ok (sys_input segs ms x8) md -> ok (tr, mkCfg ms md)], and [x8] is
    universally quantified there with nothing to pin it, which is why a producer has to reach
    the per-call rules rather than strengthen [ok]. *)
Lemma rob_reach_of_calls : forall segs c0,
  (forall tr ms md x8, star_a segs c0 tr (mkCfg ms md) ->
     m_halted md = None -> ms_svc_pending ms = Some x8 -> sys_rob segs (mkCfg ms md)) ->
  rob_reach segs c0.
Proof.
  intros segs c0 H. unfold rob_reach, rob_from. intros tr c Hst Hh.
  destruct c as [ms md]. cbn [cfg_model] in Hh.
  destruct (ms_svc_pending ms) as [x8|] eqn:E.
  - exact (H tr ms md x8 Hst Hh E).
  - apply sys_rob_instr. cbn [cfg_ms]. exact E.
Qed.

Theorem reaches_error_a_run_init :
  forall segs inp (sp brk mb : word) pc ph rnd lim,
  vdso_image segs = None ->
  rob_reach segs (init_config segs pc ph sp brk mb rnd lim inp) ->
  ~ reaches_error_a segs (init_config segs pc ph sp brk mb rnd lim inp) ->
  ~ reaches_error_a (run_segments segs inp sp mb)
      (init_config (run_segments segs inp sp mb) pc ph sp brk mb rnd lim inp).
Proof.
  intros segs inp sp brk mb pc ph rnd lim Hvi Hrob Hne.
  unfold reaches_error_a in *. unfold rob_reach in Hrob.
  apply reaches_error_run_init; assumption.
Qed.

Theorem obs_trace_a_run_init :
  forall segs inp (sp brk mb : word) pc ph rnd lim tr,
  vdso_image segs = None ->
  rob_reach segs (init_config segs pc ph sp brk mb rnd lim inp) ->
  ~ reaches_error_a segs (init_config segs pc ph sp brk mb rnd lim inp) ->
  (obs_trace_a (run_segments segs inp sp mb)
     (init_config (run_segments segs inp sp mb) pc ph sp brk mb rnd lim inp) tr
   <-> obs_trace_a segs (init_config segs pc ph sp brk mb rnd lim inp) tr).
Proof.
  intros segs inp sp brk mb pc ph rnd lim tr Hvi Hrob Hne.
  unfold obs_trace_a, reaches_error_a in *. unfold rob_reach in Hrob.
  apply obs_trace_run_init; assumption.
Qed.
