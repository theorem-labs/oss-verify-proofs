(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from Common/StoreOk.v's ShapeAlg.realizes and Common/AsanAcctShape.v's ShapeRel.shape_rel: the same carrier with a no-allocation-call check at each node, and the proof that a configuration it holds at never reaches a budget-refused configuration. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (rzb_not_refused covers the model's vDSO arm of budget_refused_at; RomBase.sys_rob as the third part of node_ok, proved at the exit node). *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
Require Stdlib.NArith.NArith Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Require LinuxProcessSemantics.EquivalenceDefinition.Equivalence LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CfgStep OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RomBase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(** * [rzb]: [ShapeAlg.realizes] with a no-allocation-call check at each node

    The released walks of this harness are stated over [ShapeAlg.realizes]
    ([Common/StoreOk.v]), whose node rule [node_ok] lists the steps of
    [Run.sstep_cfg] at [CfgStep.kit_cfg], a filtered step.  The budget premise
    [~ run_scfg_budget_refused cfg img lim en inp] reads a run.  A [realizes]
    derivation cannot carry it: a node may be a brk, mmap, mremap or mprotect
    call the budget refuses, and at such a node the filter drops steps the
    unfiltered [Run.sstep] still takes.

    [rzb] is [realizes] with one more premise at each node, [grant_ok]: the
    configuration has no pending system call, or the pending call is not one
    of 214, 216, 222, 226 ([CfgStep.not_alloc_pending]).  At such a node the
    filtered and the unfiltered steps agree ([CfgStep.sstep_cfg_of_sstep_on]),
    the grant clause of [Run.budget_refused_at] cannot fire
    ([Run.alloc_budget_refused_b_outside]), and its two first-touch clauses are
    premises of an error step ([Run.budget_fault_instr_sstep_error],
    [Run.budget_fault_syscall_sstep_error]) that [node_ok] excludes.  So a
    configuration that [rzb] holds at reaches no budget-refused configuration,
    through the unfiltered step ([rzb_never_refused]), and so through the step
    of any spurious-failure configuration ([rzb_never_refused_cfg]).

    [ShapeRelB.shape_rel] is [ShapeRel.shape_rel] ([Common/AsanAcctShape.v])
    with the same extra premise on [sr_node], and [sr_embed] taking [rzb] in
    place of [realizes]; [ShapeRelB.SR_rzb] is its instance at [rzb].  The
    released walks quantify over a [shape_rel]; the files of this directory
    restate the ones on the usage path over [ShapeRelB.shape_rel]. *)

Module RzbAlg.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim.SimInv OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CfgStep.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope bv_scope.

Section WithSegs.
Variable segs : list Segment.

(** No allocation call is pending at the configuration. *)
Definition grant_ok (c : config) : Prop := not_alloc_pending (cfg_ms c).

Inductive rzb : config -> TSet -> Prop :=
| rzb_node : forall c (I : Type) (evs : I -> list event) (nx : I -> config)
                    (T : I -> TSet) (i0 : I),
    node_ok segs c I evs nx -> grant_ok c ->
    (forall i, rzb (nx i) (T i)) ->
    rzb c (t_alt (fun i => t_emit (evs i) (T i)))
| rzb_halt : forall c,
    m_halted (cfg_model c) <> None ->
    rzb c t_nil
| rzb_conseq : forall c T T',
    rzb c T -> t_eq T T' -> rzb c T'.

(** Forgetting the check gives the released carrier. *)
Lemma rzb_realizes : forall c T, rzb c T -> realizes segs c T.
Proof.
  intros c T H; induction H as [c I evs nx T i0 Hn Hg Hc IH | c Hh | c T T' H IH Heq].
  - exact (rz_node segs c I evs nx T i0 Hn IH).
  - exact (rz_halt segs c Hh).
  - exact (rz_conseq segs c T T' IH Heq).
Qed.

Lemma rzb_nonempty : forall c T, rzb c T -> T [].
Proof. intros c T H. exact (realizes_nonempty segs c T (rzb_realizes c T H)). Qed.

(** Both carriers give the exact trace set, so they agree on it. *)
Lemma rzb_det : forall c T T', rzb c T -> realizes segs c T' -> t_eq T T'.
Proof.
  intros c T T' H1 H2 tr.
  pose proof (realizes_obs_iff segs c T (rzb_realizes c T H1) tr) as X1.
  pose proof (realizes_obs_iff segs c T' H2 tr) as X2. tauto.
Qed.

Lemma grant_pending_on : forall c, grant_ok c -> pending_on segs kit_cfg c.
Proof. intros [ms model] H. exact (kit_pending_on_not_alloc segs ms model H). Qed.

Lemma grant_not_mark : forall c x8, grant_ok c -> ms_svc_pending (cfg_ms c) = Some x8 ->
  ~ In (bv_unsigned x8) alloc_mark_sysnos.
Proof.
  intros c x8 H Hx Hin. apply alloc_no_b_true_iff in Hin. rewrite (H x8 Hx) in Hin. discriminate Hin.
Qed.

(** At a checked node no unfiltered step is an error. *)
Lemma node_no_error : forall c (I : Type) evs nx e,
  node_ok segs c I evs nx -> grant_ok c -> ~ sstep segs c e SError.
Proof.
  intros c I evs nx e Hn Hg Hs.
  pose proof (sstep_cfg_of_sstep_on segs kit_cfg c e SError (grant_pending_on c Hg) Hs) as Hc.
  destruct (proj1 (proj2 Hn) e SError Hc) as (i & _ & E). discriminate E.
Qed.

(** An unfiltered step from a configuration [rzb] holds at reaches one it holds at. *)
Lemma rzb_step_inv : forall c T, rzb c T ->
  forall e c', sstep segs c e (SNext c') -> exists T', rzb c' T'.
Proof.
  intros c T H; induction H as [c I evs nx T i0 Hn Hg Hc IH | c Hh | c T T' H IH Heq];
    intros e c' Hs.
  - pose proof (sstep_cfg_of_sstep_on segs kit_cfg c e (SNext c') (grant_pending_on c Hg) Hs) as Hcs.
    destruct (proj1 (proj2 Hn) e (SNext c') Hcs) as (i & _ & E). injection E as E.
    exists (T i). rewrite E. exact (Hc i).
  - exfalso. apply Hh. exact (sstep_halted_none segs c e (SNext c') Hs).
  - exact (IH e c' Hs).
Qed.

(** A configuration [rzb] holds at is not budget-refused. *)
Lemma rzb_not_refused : forall c T, rzb c T -> ~ budget_refused_at segs c.
Proof.
  intros c T H; induction H as [c I evs nx T i0 Hn Hg Hc IH | c Hh | c T T' H IH Heq];
    intros Hb.
  - destruct c as [ms model].
    destruct Hb as (Hh & [(Hnone & [(report & Hst & Hmat)
                                   | (Hacct & fn & n & eff & model' & evs' &
                                      Hfn & Hsys & Hspec & Hef & Hh' & Hmat)])
                         | (x8 & Hx & [Hgr | (eff & model' & evs' & Hsp & Hh' & Hmat)])]);
      cbn [cfg_ms cfg_model] in *.
    + exact (node_no_error _ I evs nx [] Hn Hg
               (budget_fault_instr_sstep_error segs ms model report Hh Hnone Hst Hmat)).
    + exact (node_no_error _ I evs nx [] Hn Hg
               (budget_fault_vdso_sstep_error segs ms model fn n eff model' evs'
                  Hh Hnone Hacct Hfn Hsys Hspec Hef Hh' Hmat)).
    + pose proof (alloc_budget_refused_b_outside (sys_input segs ms x8) model
                    (grant_not_mark (mkCfg ms model) x8 Hg Hx)) as Hf.
      rewrite Hf in Hgr. discriminate Hgr.
    + exact (node_no_error _ I evs nx [] Hn Hg
               (budget_fault_syscall_sstep_error segs ms model x8 eff model' evs' Hh Hx Hsp Hh' Hmat)).
  - apply Hh. exact (proj1 Hb).
  - exact (IH Hb).
Qed.

(** The run from a configuration [rzb] holds at never reaches a
    budget-refused configuration, through the unfiltered step. *)
Theorem rzb_never_refused : forall c T, rzb c T -> ~ reaches_budget_refused segs c.
Proof.
  intros c T H.
  apply (never_budget_refused_ind segs (fun c => exists T, rzb c T)).
  - cbv beta. exists T. exact H.
  - intros c1 e c2 (T1 & H1) Hs. exact (rzb_step_inv c1 T1 H1 e c2 Hs).
  - intros c1 (T1 & H1). exact (rzb_not_refused c1 T1 H1).
Qed.

(** ... and so through the step of every spurious-failure configuration. *)
Theorem rzb_never_refused_cfg : forall cfg c T, rzb c T -> ~ reaches_budget_refused_cfg segs cfg c.
Proof.
  intros cfg c T H Hr. exact (rzb_never_refused c T H (reaches_budget_refused_cfg_sub segs cfg c Hr)).
Qed.

(** Introducing the check. *)
Lemma grant_ok_no_svc : forall ms model, ms_svc_pending ms = None -> grant_ok (mkCfg ms model).
Proof. intros ms model H. exact (not_alloc_pending_none ms H). Qed.

Lemma grant_ok_sysno : forall ms model x8 n,
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = n -> alloc_no_b n = false ->
  grant_ok (mkCfg ms model).
Proof. intros ms model x8 n Hs Hn Hb. exact (not_alloc_pending_sysno ms x8 n Hs Hn Hb). Qed.

(** The released derived rules, restated. *)
Lemma rzb_silent1 : forall c c' T,
  node_ok segs c unit (fun _ => []) (fun _ => c') -> grant_ok c ->
  rzb c' T -> rzb c T.
Proof.
  intros c c' T Hnode Hg Hc.
  apply (rzb_conseq c (t_alt (fun _ : unit => t_emit [] T))).
  - apply (rzb_node c unit (fun _ => []) (fun _ => c') (fun _ => T) tt Hnode Hg).
    intros []; exact Hc.
  - eapply t_eq_trans;
      [ apply (t_alt_unit (fun _ : unit => t_emit [] T))
      | apply t_emit_nil_eq; eapply rzb_nonempty; exact Hc ].
Qed.

Lemma rzb_emit1 : forall c c' e T,
  node_ok segs c unit (fun _ => e) (fun _ => c') -> grant_ok c ->
  rzb c' T -> rzb c (t_emit e T).
Proof.
  intros c c' e T Hnode Hg Hc.
  apply (rzb_conseq c (t_alt (fun _ : unit => t_emit e T))).
  - apply (rzb_node c unit (fun _ => e) (fun _ => c') (fun _ => T) tt Hnode Hg).
    intros []; exact Hc.
  - apply t_alt_unit.
Qed.

Lemma rzb_step : forall ms model ms' T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  rzb (mkCfg ms' model) T ->
  rzb (mkCfg ms model) T.
Proof.
  intros ms model ms' T Hh Hlazy Hsvc Hstep Hc.
  apply (rzb_silent1 (mkCfg ms model) (mkCfg ms' model) T).
  - exact (node_instr segs ms model ms' Hh Hlazy Hsvc Hstep).
  - exact (grant_ok_no_svc ms model Hsvc).
  - exact Hc.
Qed.

Lemma rzb_msteps : forall ms ms' model T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  msteps segs ms ms' ->
  rzb (mkCfg ms' model) T ->
  rzb (mkCfg ms model) T.
Proof.
  intros ms ms' model T Hh Hlazy Hms;
    induction Hms as [ms | ms ms1 ms2 Hsvc Hstep Hms IH];
    intro Hc; [exact Hc|].
  eapply rzb_step; [exact Hh | exact Hlazy | exact Hsvc | exact Hstep
                   | apply IH; exact Hc].
Qed.

Lemma rzb_exit : forall ms model x8,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  is_exit_no x8 ->
  rzb (mkCfg ms model)
      (t_exit (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)).
Proof.
  intros ms model x8 Hh Hsvc Hx8.
  set (code := bv_and (ms_gpr ms 0) (Z_to_bv 64 255)).
  unfold t_exit.
  apply (rzb_emit1 (mkCfg ms model) (mkCfg ms (with_halted code model))).
  - apply node_ok_of_u;
      [destruct Hx8 as [Hx8' | Hx8'];
       apply (kit_pending_on_sysno segs ms model x8 _ Hsvc Hx8'); reflexivity
      | exact (RomBase.sys_rob_exit segs ms model x8 Hsvc Hx8) |].
    split.
    + intros []. cbn.
      replace [ExitEv code (m_fs model)]
        with ([] ++ [ExitEv code (m_fs (with_halted code model))]) by reflexivity.
      apply (sstep_exit segs ms model x8 (mkEffect (Z_to_bv 64 0) [] [])
               (with_halted code model) [] code);
        [exact Hh | exact Hsvc
         | apply (exit_dispatch_ok (sys_input segs ms x8) model);
           rewrite in_sysno_sys_input; exact Hx8
         | reflexivity
         | apply m_killed_with_halted ].
    + intros e st Hss.
      destruct (sstep_exit_inv segs ms model x8 e st Hh Hsvc Hx8 Hss) as [-> ->].
      exists tt. split; reflexivity.
  - destruct Hx8 as [Hx8' | Hx8'];
      exact (grant_ok_sysno ms model x8 _ Hsvc Hx8' eq_refl).
  - apply rzb_halt. cbn. discriminate.
Qed.

End WithSegs.
End RzbAlg.

Module ShapeRelB.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim.SimInv OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CfgStep.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Import RzbAlg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope bv_scope.

Section WithSegs.
Variable segs : list Segment.

Record shape_rel := SR {
  sr_rel :> config -> TSet -> Prop;
  sr_node : forall c (I : Type) (evs : I -> list event) (nx : I -> config) (T : I -> TSet) (i0 : I),
      node_ok segs c I evs nx -> grant_ok c -> (forall i, sr_rel (nx i) (T i)) ->
      sr_rel c (t_alt (fun i => t_emit (evs i) (T i)));
  sr_halt : forall c, m_halted (cfg_model c) <> None -> sr_rel c t_nil;
  sr_conseq : forall c T T', sr_rel c T -> t_eq T T' -> sr_rel c T';
  sr_nonempty : forall c T, sr_rel c T -> T [];
  sr_embed : forall c T, rzb segs c T -> sr_rel c T
}.

Definition SR_rzb : shape_rel :=
  SR (rzb segs) (rzb_node segs) (rzb_halt segs) (rzb_conseq segs) (rzb_nonempty segs) (fun c T H => H).

(** The trace set a configuration admits, and exactness, as [AsIface3.MhKInst]. *)
Definition sr_exactness (R : shape_rel) : Prop :=
  forall c T, R c T -> t_eq (obs_trace_cfg segs kit_cfg c) T.

Lemma exact_rzb : sr_exactness SR_rzb.
Proof. intros c T H tr. exact (realizes_obs_iff segs c T (rzb_realizes segs c T H) tr). Qed.

Lemma SR_det_of_exact : forall (R : shape_rel), sr_exactness R ->
  forall c T T', sr_rel R c T -> realizes segs c T' -> t_eq T T'.
Proof.
  intros R SRX c T T' H1 H2 tr.
  pose proof (SRX c T H1 tr) as X1. pose proof (realizes_obs_iff segs c T' H2 tr) as X2. tauto.
Qed.

Variable R : shape_rel.

Lemma sr_silent_node : forall c (I : Type) (i0 : I) (nx : I -> config) T,
  node_ok segs c I (fun _ => []) nx -> grant_ok c ->
  (forall i, R (nx i) T) -> R c T.
Proof.
  intros c I i0 nx T Hnode Hg Hc.
  apply (sr_conseq R c (t_alt (fun _ : I => t_emit [] T))).
  - apply (sr_node R c I (fun _ => []) nx (fun _ => T) i0 Hnode Hg Hc).
  - assert (HT : T []) by (eapply (sr_nonempty R); exact (Hc i0)).
    intros tr. split.
    + intros [i Hi]. exact (proj1 (t_emit_nil_eq T HT tr) Hi).
    + intros Htr. exists i0. exact (proj2 (t_emit_nil_eq T HT tr) Htr).
Qed.

Lemma sr_silent1 : forall c c' T,
  node_ok segs c unit (fun _ => []) (fun _ => c') -> grant_ok c -> R c' T -> R c T.
Proof.
  intros c c' T Hnode Hg Hc. apply (sr_silent_node c unit tt (fun _ => c') T Hnode Hg).
  intros []; exact Hc.
Qed.

Lemma sr_step : forall ms model ms' T,
  m_halted model = None -> m_vm_lazy model = [] -> ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  R (mkCfg ms' model) T -> R (mkCfg ms model) T.
Proof.
  intros ms model ms' T Hh Hlazy Hsvc Hstep Hc.
  apply (sr_silent1 (mkCfg ms model) (mkCfg ms' model) T).
  - exact (node_instr segs ms model ms' Hh Hlazy Hsvc Hstep).
  - exact (grant_ok_no_svc ms model Hsvc).
  - exact Hc.
Qed.

Lemma sr_msteps : forall ms ms' model T,
  m_halted model = None -> m_vm_lazy model = [] -> msteps segs ms ms' ->
  R (mkCfg ms' model) T -> R (mkCfg ms model) T.
Proof.
  intros ms ms' model T Hh Hlazy Hms;
    induction Hms as [ms | ms ms1 ms2 Hsvc Hstep Hms IH]; intro Hc; [exact Hc|].
  eapply sr_step; [exact Hh | exact Hlazy | exact Hsvc | exact Hstep | apply IH; exact Hc].
Qed.

Lemma sr_exit : forall ms model x8,
  m_halted model = None -> ms_svc_pending ms = Some x8 -> is_exit_no x8 ->
  R (mkCfg ms model) (t_exit (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)).
Proof. intros. apply (sr_embed R). eapply rzb_exit; eassumption. Qed.

Lemma sr_of_realizes : forall c T, rzb segs c T -> R c T.
Proof. exact (sr_embed R). Qed.

End WithSegs.
End ShapeRelB.
