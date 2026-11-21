(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (munmap's injected -ENOMEM, a spurious refusal under the forced-only allocation configuration; each node of a walk asks that its system call answers the same over a larger read-only backing (RomBase.sys_rob), so a walk over the image's own segments lifts to the run's segment list). *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import Scfg HSimInv HExitSim HCatSim HMmapSim HShapeAlg HNodes AllocNodes HDivergeSim LazyFrame HSymTac.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Common.Cfg Require RomBase.
Import ListNotations.
Open Scope bv_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section WithSegs.
Variable segs : list Segment.
Context {SC : StepCfg}.

Inductive srealizes : config -> TSet -> Prop :=
| srz_node : forall c (I : Type) (evs : I -> list event) (nx : I -> config)
                    (T : I -> TSet) (i0 : I),
    node_ok segs c I evs nx ->
    RomBase.sys_rob segs c ->   (* LPS 08b1429: as [HShapeAlg.rz_node] *)
    (forall i, srealizes (nx i) (T i)) ->
    srealizes c (t_alt (fun i => t_emit (evs i) (T i)))
| srz_halt : forall c,
    m_halted (cfg_model c) <> None ->
    srealizes c t_nil
| srz_conseq : forall c T T',
    srealizes c T -> t_eq T T' -> srealizes c T'.

Lemma srealizes_of_realizes : forall c T,
  realizes segs c T -> srealizes c T.
Proof.
  intros c T H;
    induction H as [c I evs nx T i0 Hnode Hrob Hcont IH | c Hh | c T T' H IH Heq].
  - exact (srz_node c I evs nx T i0 Hnode Hrob IH).
  - exact (srz_halt c Hh).
  - exact (srz_conseq c T T' IH Heq).
Qed.

Lemma srealizes_nonempty : forall c T, srealizes c T -> T [].
Proof.
  intros c T H;
    induction H as [c I evs nx T i0 Hnode Hrob Hcont IH | c Hh | c T T' H IH Heq].
  - exists i0. left. apply is_prefix_nil.
  - reflexivity.
  - apply Heq. exact IH.
Qed.

Definition srz_path (c : config) : Prop := exists T, srealizes c T.

Lemma srz_silent1 : forall c c' T,
  node_ok segs c unit (fun _ => []) (fun _ => c') ->
  RomBase.sys_rob segs c ->
  srealizes c' T ->
  srealizes c T.
Proof.
  intros c c' T Hnode Hrob Hc.
  apply (srz_conseq c (t_alt (fun _ : unit => t_emit [] T))).
  - apply (srz_node c unit (fun _ => []) (fun _ => c') (fun _ => T) tt Hnode Hrob).
    intros []; exact Hc.
  - eapply t_eq_trans;
      [ apply (t_alt_unit (fun _ : unit => t_emit [] T))
      | apply t_emit_nil_eq; eapply srealizes_nonempty; exact Hc ].
Qed.

Lemma srz_step : forall ms model ms' T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  srealizes (mkCfg ms' model) T ->
  srealizes (mkCfg ms model) T.
Proof.
  intros ms model ms' T Hh Hlazy Hsvc Hstep Hc.
  eapply srz_silent1; [apply node_instr; eassumption | apply RomBase.sys_rob_instr; exact Hsvc | exact Hc].
Qed.

Lemma srz_msteps : forall ms ms' model T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  msteps segs ms ms' ->
  srealizes (mkCfg ms' model) T ->
  srealizes (mkCfg ms model) T.
Proof.
  intros ms ms' model T Hh Hlazy Hms;
    induction Hms as [ms | ms ms1 ms2 Hsvc Hstep Hms IH];
    intro Hc; [exact Hc|].
  eapply srz_step; [exact Hh | exact Hlazy | exact Hsvc | exact Hstep
                   | apply IH; exact Hc].
Qed.

Lemma srz_exit : forall ms model x8,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  is_exit_no x8 ->
  srealizes (mkCfg ms model)
            (t_exit (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)).
Proof.
  intros ms model x8 Hh Hsvc Hx8.
  apply srealizes_of_realizes. apply (rz_exit segs ms model x8); assumption.
Qed.

Lemma node_munmap {AF : AllocForced SC} : forall ms model x8,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 215%Z ->
  munmap_args_ok ms model ->
  node_ok segs (mkCfg ms model) unit (fun _ => [])
    (fun _ => mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
                    (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1))
                                  model)).
Proof.
  intros ms model x8 Hh Hlazy Hsvc Hno Hargs.
  assert (Hno' : bv_unsigned (in_sysno (sys_input segs ms x8)) = 215%Z)
    by (rewrite in_sysno_sys_input; exact Hno).
  assert (Hns0 : ~ spurious_refusal_cfg the_scfg (sys_input segs ms x8) model (munmap_eff ms)).
  { apply Run.spurious_refusal_not_refusal. unfold munmap_eff. cbn [eff_ret].
    exact (zero_not_refusal_munmap _ model Hno'). }
  split.
  - intros []. apply (sstep_cfg_syscall segs the_scfg ms model x8 (munmap_eff ms)
                        (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)
                        (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) []).
    + exact Hh.
    + exact Hsvc.
    + apply munmap_ok; assumption.
    + exact Hns0.
    + rewrite munmap_model_halted; exact Hh.
    + apply materialize_model_accesses_no_lazy.
      exact (munmap_model_no_lazy _ _ _ Hlazy).
  - intros e st Hss.
    destruct (sstep_cfg_svc_inv segs ms model x8 e st Hsvc Hss)
      as [(eff & model' & evs & Hc & Hcase) | (Hc & _ & _)];
      [| exfalso; exact (munmap_no_unmodeled segs ms x8 model Hno Hargs Hc)].
    destruct (munmap_ok_inv segs ms x8 model eff model' evs Hno Hargs Hc) as (Hevs & Hd).
    subst evs.
    destruct Hd as [(e0 & HIn & -> & ->) | (-> & ->)].
    + (* the refusal: spurious under [AllocForced], so no [sstep_cfg] takes it *)
      exfalso.
      assert (Hsp : spurious_refusal_cfg the_scfg (sys_input segs ms x8) model
                      (mkEffect (errno_ret e0) [] [])).
      { apply (alloc_refusal_spurious (sys_input segs ms x8) model _ (munmap_eff ms)
                 (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) []).
        - exact (family_off_munmap_true _ Hno').
        - cbn [eff_ret]. exact (errno_is_refusal_munmap _ model e0 Hno' HIn).
        - apply munmap_ok; assumption.
        - unfold munmap_eff. cbn [eff_ret]. exact (zero_not_refusal_munmap _ model Hno'). }
      destruct Hcase as [(m'' & _ & _ & Hns & _ & _)
                        | [(_ & _ & Hns & _ & _)
                        | [(code & Hhc & _) | (sig & Hk & _)]]].
      * exact (Hns Hsp).
      * exact (Hns Hsp).
      * rewrite Hh in Hhc. discriminate.
      * rewrite (m_killed_of_m_halted_none _ Hh) in Hk. discriminate.
    + destruct Hcase as [(m'' & _ & He & _ & Hmat & Hst)
                        | [(_ & _ & _ & Hmat & _)
                        | [(code & Hhc & _) | (sig & Hk & _)]]].
      * rewrite (materialize_model_accesses_no_lazy _ _
                   (munmap_model_no_lazy _ _ _ Hlazy)) in Hmat.
        injection Hmat as <-. exists tt. split; [exact He | exact Hst].
      * rewrite (materialize_model_accesses_no_lazy _ _
                   (munmap_model_no_lazy _ _ _ Hlazy)) in Hmat. discriminate.
      * rewrite munmap_model_halted, Hh in Hhc. discriminate.
      * rewrite (m_killed_of_m_halted_none _
                   (eq_trans (munmap_model_halted _ _ _) Hh)) in Hk. discriminate.
Qed.

End WithSegs.

Ltac chain_mst_sp :=
  first [ (eapply srz_msteps; [ sym_halted | sym_no_lazy | | ])
        | chain_mst ].

