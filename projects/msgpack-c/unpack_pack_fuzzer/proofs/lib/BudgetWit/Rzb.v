(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from Common/ShapeAlg.v and Common/ShapeAcc.v: the relation realizes with a budget check at each node (rzb), its soundness for the budget premise, and the node lemmas restated over rzb. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (node_not_refused closes the vDSO clause of budget_refused_at; rzb_node takes RomBase.sys_rob after node_ok, so rzb_silent1 and rzb_emit1 take it too, and rzb_step, rzb_astep and rzb_exit prove it; imports RomBase). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Scfg Require Import Fcfg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg ShapeAcc.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS Require Import RomBase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(** * [rzb]: [ShapeAlg.realizes] with a budget check at each node

    [ShapeAlg.realizes segs c T] ties a trace set to the one-step families of
    the configurations a run reaches, for the filtered step [sstep_cfg segs
    fcfg].  It has no cut, but a derivation records nothing about the
    configurations it passes, so no [realizes] proof says that a run is never
    refused by the budget.  [rzb] has the same three constructors, and its node
    constructor asks, besides [node_ok] and [RomBase.sys_rob] (the node's system
    call reads no byte a larger read-only backing adds, so that
    [BudgetWit.RzbRom.rzb_run_init] lifts a walk to the run's segment list), for
    [budget_ok segs c]:
    - [grant_ok]: if a syscall is pending at [c], the budget mark
      [Run.alloc_budget_refused_b] answers [false] on it;
    - [Fcfg.step_nonspur]: no step of the unfiltered relation [sstep] from [c]
      is a spurious refusal of [fcfg], so every [sstep] step from [c] is an
      [sstep_cfg segs fcfg] step ([Fcfg.sstep_fcfg_of_sstep]).

    [rzb_never_refused]: no configuration the unfiltered run reaches is
    budget-refused.  The first-touch clauses of [Run.budget_refused_at] are
    premises of an [SError] step ([Run.budget_fault_instr_sstep_error],
    [Run.budget_fault_syscall_sstep_error]); the second half of
    [budget_ok] makes that step a filtered one, which the completeness half of
    [node_ok] excludes.  The grant clause is the negation of [grant_ok].

    Both halves hold at an instruction ([budget_ok_instr]) and at a syscall
    whose number is none of 214, 216, 222 and 226, the RISC-V Linux numbers of
    brk, mremap, mmap and mprotect ([Run.alloc_mark_sysnos];
    [budget_ok_nonalloc], [budget_ok_num], [budget_ok_exit]).

    The rest of the file is ShapeAlg's and ShapeAcc's lemmas that build a
    [realizes] node, restated over [rzb] with their proofs: [rz_] is written
    [rzb_].  A lemma that takes a [node_ok] also takes [sys_rob] and [budget_ok]
    for the same configuration; a lemma whose node is an instruction or an exit
    derives both. *)

Section g.
Variable segs : list Segment.

(** If a syscall is pending at [c], the budget does not refuse it as a grant. *)
Definition grant_ok (c : config) : Prop :=
  forall x8, ms_svc_pending (cfg_ms c) = Some x8 ->
    alloc_budget_refused_b (sys_input segs (cfg_ms c) x8) (cfg_model c) = false.

Definition budget_ok (c : config) : Prop := grant_ok c /\ step_nonspur segs c.

Lemma budget_ok_instr : forall ms model,
  ms_svc_pending ms = None -> budget_ok (mkCfg ms model).
Proof.
  intros ms model Hsvc. split.
  - intros x8 Hx. cbn [cfg_ms] in Hx. rewrite Hsvc in Hx. discriminate Hx.
  - apply step_nonspur_instr. exact Hsvc.
Qed.

Lemma budget_ok_nonalloc : forall ms model x8,
  ms_svc_pending ms = Some x8 -> ~ In (bv_unsigned x8) alloc_mark_sysnos ->
  budget_ok (mkCfg ms model).
Proof.
  intros ms model x8 Hsvc Hn. split.
  - intros y Hy. cbn [cfg_ms cfg_model] in *. rewrite Hsvc in Hy. injection Hy as <-.
    apply alloc_budget_refused_b_outside. rewrite in_sysno_sys_input. exact Hn.
  - exact (step_nonspur_nonalloc segs ms model x8 Hsvc Hn).
Qed.

(** The form a certificate gives: the number as a literal, checked by
    [existsb]. *)
Lemma budget_ok_num : forall ms model x8 n,
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = n ->
  existsb (Z.eqb n) alloc_mark_sysnos = false ->
  budget_ok (mkCfg ms model).
Proof.
  intros ms model x8 n Hsvc Hx Hb. apply (budget_ok_nonalloc ms model x8 Hsvc).
  rewrite Hx. intros Hin.
  assert (Ht : existsb (Z.eqb n) alloc_mark_sysnos = true).
  { apply existsb_exists. exists n. split; [exact Hin | apply Z.eqb_refl]. }
  congruence.
Qed.

(** The exit (93 or 94) is off the four allocation numbers. *)
Lemma budget_ok_exit : forall ms model x8,
  ms_svc_pending ms = Some x8 -> is_exit_no x8 -> budget_ok (mkCfg ms model).
Proof.
  intros ms model x8 Hsvc Hx. exact (budget_ok_nonalloc ms model x8 Hsvc (exit_nonalloc x8 Hx)).
Qed.
End g.

Section d.
Variable segs : list Segment.

Inductive rzb : config -> TSet -> Prop :=
| rzb_node : forall c (I : Type) (evs : I -> list event) (nx : I -> config)
                    (T : I -> TSet) (i0 : I),
    node_ok segs c I evs nx ->
    (* LPS 727298f3: the node's system call reads no byte the run's backing adds
       ([RomBase.sys_rob]; [RzbRom.rzb_run_init] lifts a walk to the run's start) *)
    sys_rob segs c ->
    budget_ok segs c ->
    (forall i, rzb (nx i) (T i)) ->
    rzb c (t_alt (fun i => t_emit (evs i) (T i)))
| rzb_halt : forall c,
    m_halted (cfg_model c) <> None ->
    rzb c t_nil
| rzb_conseq : forall c T T',
    rzb c T -> t_eq T T' -> rzb c T'.
End d.

(** ** Soundness for the budget premise *)
Section s.
Variable segs : list Segment.

Lemma rzb_sstep_lift : forall c e st,
  budget_ok segs c -> sstep segs c e st -> sstep_cfg segs fcfg c e st.
Proof. intros c e st [_ Hn] H. exact (sstep_fcfg_of_sstep segs c e st Hn H). Qed.

Lemma star_cases : forall c tr c', star segs c tr c' ->
  c' = c \/ exists e c2 tr2, sstep segs c e (SNext c2) /\ star segs c2 tr2 c'.
Proof.
  intros c tr c' H. destruct H as [c0 | c1 e c2 tr2 c3 Hss Hstar].
  - left. reflexivity.
  - right. exists e, c2, tr2. split; [exact Hss | exact Hstar].
Qed.

(** A node with the budget check is not budget-refused. *)
Lemma node_not_refused : forall c I evs nx,
  node_ok segs c I evs nx -> budget_ok segs c -> ~ budget_refused_at segs c.
Proof.
  intros [ms model] I evs nx [_ Hc] Hb [Hh Hr].
  assert (Herr : ~ sstep segs (mkCfg ms model) [] SError).
  { intros Hs.
    destruct (Hc [] SError (rzb_sstep_lift _ [] SError Hb Hs)) as (i & _ & Hbad).
    discriminate Hbad. }
  cbn [cfg_ms cfg_model] in Hh, Hr.
  (* [Run.budget_refused_at]'s no-syscall half is a disjunction now: the
     first-touch instruction fault and the vDSO materialization fault.  Both
     are premises of an [SError] step, so both close the same way. *)
  destruct Hr as [(Hsvc & [ (report & Hstep & Hmat)
                          | (Hacct & fn & n & eff & model' & evs' &
                             Hfn & Hsys & Hspec & Hef & Hh' & Hmat) ])
                 | (x8 & Hx8 & [Hgr | (eff & model' & evs' & Hspec & Hh' & Hmat)])].
  - exact (Herr (budget_fault_instr_sstep_error segs ms model report Hh Hsvc Hstep Hmat)).
  - exact (Herr (budget_fault_vdso_sstep_error segs ms model fn n eff model' evs'
                   Hh Hsvc Hacct Hfn Hsys Hspec Hef Hh' Hmat)).
  - destruct Hb as [Hg _]. pose proof (Hg x8 Hx8) as Hg'. cbn [cfg_ms cfg_model] in Hg'. congruence.
  - exact (Herr (budget_fault_syscall_sstep_error segs ms model x8 eff model' evs' Hh Hx8 Hspec Hh' Hmat)).
Qed.

Lemma rzb_star_not_refused : forall c T, rzb segs c T ->
  forall tr c', star segs c tr c' -> ~ budget_refused_at segs c'.
Proof.
  intros c T H;
  induction H as [c I evs nx T i0 Hnode Hrob Hb Hcont IH | c Hh | c T T' H IH Heq];
  intros tr c' Hstar.
  - destruct (star_cases _ _ _ Hstar) as [-> | (e & c2 & tr2 & Hss & Hstar2)].
    + exact (node_not_refused c I evs nx Hnode Hb).
    + destruct (proj2 Hnode e (SNext c2) (rzb_sstep_lift c e (SNext c2) Hb Hss))
        as (i & _ & Heq2).
      injection Heq2 as ->. exact (IH i tr2 c' Hstar2).
  - destruct (star_cases _ _ _ Hstar) as [-> | (e & c2 & tr2 & Hss & Hstar2)].
    + intros [Hn _]. exact (Hh Hn).
    + exfalso. exact (Hh (sstep_halted_none segs c e _ Hss)).
  - exact (IH tr c' Hstar).
Qed.

(** No configuration the unfiltered run reaches from an [rzb] configuration is
    budget-refused. *)
Theorem rzb_never_refused : forall c T, rzb segs c T -> ~ reaches_budget_refused segs c.
Proof.
  intros c T H (tr & c' & Hstar & Hb). exact (rzb_star_not_refused c T H tr c' Hstar Hb).
Qed.

(** ...and so under every spurious-failure configuration
    ([Run.reaches_budget_refused_cfg_sub]). *)
Theorem rzb_never_refused_cfg : forall cfg c T, rzb segs c T ->
  ~ reaches_budget_refused_cfg segs cfg c.
Proof.
  intros cfg c T H Hr. exact (rzb_never_refused c T H (reaches_budget_refused_cfg_sub segs cfg c Hr)).
Qed.
End s.

(** ** ShapeAlg's and ShapeAcc's node lemmas over [rzb] *)
Section WithSegs.
Variable segs : list Segment.

Lemma rzb_nonempty : forall c T, rzb segs c T -> T [].
Proof.
  intros c T H; induction H as [c I evs nx T i0 Hnode Hrob Hb Hcont IH | c Hh | c T T' H IH Heq].
  - exists i0. left. apply is_prefix_nil.
  - reflexivity.
  - apply Heq. exact IH.
Qed.

Lemma rzb_silent1 : forall c c' T,
  node_ok segs c unit (fun _ => []) (fun _ => c') -> sys_rob segs c ->
  budget_ok segs c ->
  rzb segs c' T ->
  rzb segs c T.
Proof.
  intros c c' T Hnode Hrob Hb Hc.
  apply (rzb_conseq segs c (t_alt (fun _ : unit => t_emit [] T))).
  - apply (rzb_node segs c unit (fun _ => []) (fun _ => c') (fun _ => T) tt Hnode Hrob Hb).
    intros []; exact Hc.
  - eapply t_eq_trans;
      [ apply (t_alt_unit (fun _ : unit => t_emit [] T))
      | apply t_emit_nil_eq; eapply rzb_nonempty; exact Hc ].
Qed.

Lemma rzb_emit1 : forall c c' e T,
  node_ok segs c unit (fun _ => e) (fun _ => c') -> sys_rob segs c ->
  budget_ok segs c ->
  rzb segs c' T ->
  rzb segs c (t_emit e T).
Proof.
  intros c c' e T Hnode Hrob Hb Hc.
  apply (rzb_conseq segs c (t_alt (fun _ : unit => t_emit e T))).
  - apply (rzb_node segs c unit (fun _ => e) (fun _ => c') (fun _ => T) tt Hnode Hrob Hb).
    intros []; exact Hc.
  - apply t_alt_unit.
Qed.

Lemma rzb_step : forall ms model ms' T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  rzb segs (mkCfg ms' model) T ->
  rzb segs (mkCfg ms model) T.
Proof.
  intros ms model ms' T Hh Hlazy Hsvc Hstep Hc.
  eapply rzb_silent1; [apply node_instr; eassumption | apply sys_rob_instr; exact Hsvc
                      | apply budget_ok_instr; exact Hsvc | exact Hc].
Qed.

Lemma rzb_msteps : forall ms ms' model T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  msteps segs ms ms' ->
  rzb segs (mkCfg ms' model) T ->
  rzb segs (mkCfg ms model) T.
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
  rzb segs (mkCfg ms model)
      (t_exit (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)).
Proof.
  intros ms model x8 Hh Hsvc Hx8.
  set (code := bv_and (ms_gpr ms 0) (Z_to_bv 64 255)).
  unfold t_exit.
  eapply (rzb_emit1 (mkCfg ms model) (mkCfg ms (with_halted code model))).
  - apply two_sided_lift; [apply (step_nonspur_nonalloc segs ms model x8 Hsvc), exit_nonalloc, Hx8 |]. split.
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
  - exact (sys_rob_exit segs ms model x8 Hsvc Hx8).
  - exact (budget_ok_exit segs ms model x8 Hsvc Hx8).
  - apply rzb_halt. cbn. discriminate.
Qed.

(** ShapeAcc's accounting steps. *)
Lemma rzb_astep : forall ms model ms' model' T,
  m_halted model = None -> ms_svc_pending ms = None ->
  mi_account_step segs ms model = MachineOk (ms', model') ->
  rzb segs (mkCfg ms' model') T -> rzb segs (mkCfg ms model) T.
Proof.
  intros ms model ms' model' T Hh Hsvc Hstep Hc.
  eapply rzb_silent1; [apply node_ainstr; eassumption | apply sys_rob_instr; exact Hsvc
                      | apply budget_ok_instr; exact Hsvc | exact Hc].
Qed.

Lemma rzb_asteps : forall ms model ms' model' T,
  m_halted model = None -> asteps segs ms model ms' model' ->
  rzb segs (mkCfg ms' model') T -> rzb segs (mkCfg ms model) T.
Proof.
  intros ms model ms' model' T Hh H. revert Hh.
  induction H as [ms mo | ms mo ms1 mo1 ms2 mo2 Hsvc Hstep Hms IH]; intros Hh Hc; [exact Hc|].
  eapply rzb_astep; [exact Hh | exact Hsvc | exact Hstep |].
  apply IH; [|exact Hc]. rewrite (account_step_halted segs _ _ _ _ Hstep). exact Hh.
Qed.

End WithSegs.
