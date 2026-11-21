(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from QRjH.v: the relation realizes with a budget check at each node, its soundness for the budget premise, and the node lemmas of QRjH that the usage path uses, restated over it. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (RomBase.sys_rob at each node of realizes, as QRjH.rz_node has it, through rz_silent1, rz_emit1 and the instruction and exit nodes; the vDSO layer: budget_ok_lift over the vDSO step cases of sstep, and the vDSO materialization fault of budget_refused_at as an SError step; the header note brought up to date). *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qpox QsV0 QsRG Qn1e QiVh QEVk QSjk QRjH QBxa.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Cfg Require RomBase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import Qpox QsV0 QsRG Qn1e.Mq1 QiVh QEVk QSjk.Mq1 QRjH.
Import ListNotations.
Open Scope bv_scope.

(** * [realizes] with a budget check at each node

    [QRjH.realizes segs c T] ties a trace set to the one-step families of the
    configurations the run reaches under the filter [alloc_only_cfg false]
    ([QRjH.node_ok]).  A derivation records nothing about the configurations
    it passes, so no [QRjH.realizes] proof says that a run is never refused by
    the budget.

    This file defines a relation of the same name, [realizes], whose node
    constructor [rz_node] asks, besides [node_ok] and [RomBase.sys_rob] (as
    [QRjH.rz_node] does since LPS 727298f3, so that [BudgetWit.QRjHBRom]
    lifts a walk to the run's segment list), for [budget_ok c]: if a
    syscall is pending at [c], its number is none of brk, munmap, mremap,
    mmap and mprotect (214, 215, 216, 222, 226; [Run.alloc_mark_sysnos]).  It keeps
    [rz_halt] and [rz_conseq].  It leaves out [QRjH.rz_loop] and its mutual
    [lbody]: no declaration on the usage path builds a loop node, so the
    copied walk never needs them.  The usage-path files of this directory
    import this module after [QRjH], so their [realizes], [rz_node],
    [rz_conseq], [rz_step], [rz_msteps] and the rest name the declarations
    below.

    From [budget_ok], every unfiltered step from the node is a filtered step
    ([budget_ok_lift]), so the completeness half of [node_ok] covers the
    unfiltered run; the grant clause of [Run.budget_refused_at] is false
    ([Run.alloc_budget_refused_b_outside]); its three first-touch clauses
    (instruction, vDSO call, syscall) are unfiltered [SError] steps
    ([Run.budget_fault_instr_sstep_error], [Run.budget_fault_vdso_sstep_error],
    [Run.budget_fault_syscall_sstep_error]), which node completeness excludes.
    [rz_never_refused] is [~ Run.reaches_budget_refused]; [rz_never_refused_cfg]
    gives every spurious-failure configuration through
    [Run.reaches_budget_refused_cfg_sub]. *)


(** If a syscall is pending at [c], it is not an allocation call. *)
Definition budget_ok (c : config) : Prop :=
  forall x8, ms_svc_pending (cfg_ms c) = Some x8 -> ~ In (bv_unsigned x8) alloc_mark_sysnos.

Lemma budget_ok_instr : forall ms model,
  ms_svc_pending ms = None -> budget_ok (mkCfg ms model).
Proof. intros ms model H x8 Hx. cbn [cfg_ms] in Hx. rewrite H in Hx. discriminate Hx. Qed.

Lemma nalloc_lit : forall (x8 : word) (n : Z),
  bv_unsigned x8 = n -> existsb (Z.eqb n) alloc_mark_sysnos = false ->
  ~ In (bv_unsigned x8) alloc_mark_sysnos.
Proof.
  intros x8 n Hx Hb Hin. rewrite Hx in Hin.
  assert (Ht : existsb (Z.eqb n) alloc_mark_sysnos = true).
  { apply existsb_exists. exists n. split; [exact Hin | apply Z.eqb_refl]. }
  congruence.
Qed.

Lemma budget_ok_nalloc : forall ms model x8,
  ms_svc_pending ms = Some x8 -> ~ In (bv_unsigned x8) alloc_mark_sysnos ->
  budget_ok (mkCfg ms model).
Proof.
  intros ms model x8 Hsvc Hn y Hy. cbn [cfg_ms] in Hy. rewrite Hsvc in Hy.
  injection Hy as <-. exact Hn.
Qed.

Lemma budget_ok_num : forall ms model x8 (n : Z),
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = n ->
  existsb (Z.eqb n) alloc_mark_sysnos = false ->
  budget_ok (mkCfg ms model).
Proof.
  intros ms model x8 n Hsvc Hx Hb y Hy. cbn [cfg_ms] in Hy. rewrite Hsvc in Hy.
  injection Hy as <-. exact (nalloc_lit x8 n Hx Hb).
Qed.

(** exit (93) and exit_group (94) are not allocation calls. *)
Lemma budget_ok_exit : forall ms model x8,
  ms_svc_pending ms = Some x8 -> is_exit_no x8 -> budget_ok (mkCfg ms model).
Proof.
  intros ms model x8 Hsvc [Hx | Hx].
  - exact (budget_ok_num ms model x8 93 Hsvc Hx eq_refl).
  - exact (budget_ok_num ms model x8 94 Hsvc Hx eq_refl).
Qed.

Section WithSegs.
Variable segs : list Segment.
Local Notation node_ok := (QRjH.node_ok segs).
(** Every unfiltered step from a configuration with the budget check is a
    step of the run filtered by [alloc_only_cfg false]. *)
Definition step_nonspur (c : config) : Prop :=
  forall x8 eff m' evs, ms_svc_pending (cfg_ms c) = Some x8 ->
    syscall_spec (sys_input segs (cfg_ms c) x8) (cfg_model c) (Ok eff m' evs) ->
    ~ spurious_refusal_cfg (alloc_only_cfg false) (sys_input segs (cfg_ms c) x8) (cfg_model c) eff.

Lemma budget_ok_step_nonspur : forall c, budget_ok c -> step_nonspur c.
Proof.
  intros c Hb x8 eff m' evs Hx _.
  apply QBxa.Mq4.not_spurious_sysno. exact (Hb x8 Hx).
Qed.

(* LPS 727298f3: [sstep] has the three vDSO arms; [sstep_cfg]'s carry no filter premise *)
Lemma budget_ok_lift : forall c e st,
  budget_ok c -> sstep segs c e st -> sstep_cfg segs (alloc_only_cfg false) c e st.
Proof.
  intros c e st Hb H. pose proof (budget_ok_step_nonspur c Hb) as Hn. revert Hn.
  unfold step_nonspur.
  destruct H; cbn [cfg_ms cfg_model]; intros Hn;
    [ eapply sstep_cfg_instr | eapply sstep_cfg_instr_fault | eapply sstep_cfg_instr_unmodeled
    | eapply sstep_cfg_vdso_call | eapply sstep_cfg_vdso_materialization_fault
    | eapply sstep_cfg_vdso_unmodeled
    | eapply sstep_cfg_syscall | eapply sstep_cfg_syscall_materialization_fault
    | eapply sstep_cfg_exit | eapply sstep_cfg_killed | eapply sstep_cfg_syscall_unmodeled ];
    eauto.
Qed.

Inductive realizes : config -> TSet -> Prop :=
| rz_node : forall c (I : Type) (evs : I -> list event) (nx : I -> config)
                   (T : I -> TSet) (i0 : I),
    node_ok c I evs nx ->
    (* LPS 727298f3: the node's system call reads no byte a larger read-only backing adds
       ([RomBase.sys_rob]; [QRjHBRom.rz_run_init] lifts a walk to the run's start) *)
    RomBase.sys_rob segs c ->
    budget_ok c ->
    (forall i, realizes (nx i) (T i)) ->
    realizes c (t_alt (fun i => t_emit (evs i) (T i)))
| rz_halt : forall c,
    m_halted (cfg_model c) <> None ->
    realizes c t_nil
| rz_conseq : forall c T T',
    realizes c T -> t_eq T T' -> realizes c T'.

(** ** Soundness for the budget premise *)

Lemma sstep_running_b : forall c e st, sstep segs c e st -> m_halted (cfg_model c) = None.
Proof. intros c e st H. destruct H; cbn [cfg_model]; assumption. Qed.

Lemma star_cases_b : forall c tr c', star segs c tr c' ->
  c' = c \/ exists e c2 tr2, sstep segs c e (SNext c2) /\ star segs c2 tr2 c'.
Proof.
  intros c tr c' H. destruct H as [c0 | c1 e c2 tr2 c3 Hss Hstar].
  - left. reflexivity.
  - right. exists e, c2, tr2. split; [exact Hss | exact Hstar].
Qed.

(** A node with the budget check is not budget-refused. *)
Lemma node_not_refused : forall c I evs nx,
  node_ok c I evs nx -> budget_ok c -> ~ budget_refused_at segs c.
Proof.
  intros [ms model] I evs nx [_ Hc] Hb [Hh Hr].
  assert (Herr : ~ sstep segs (mkCfg ms model) [] SError).
  { intros Hs.
    destruct (Hc [] SError (budget_ok_lift _ [] SError Hb Hs)) as (i & _ & Hbad).
    discriminate Hbad. }
  cbn [cfg_ms cfg_model] in Hh, Hr.
  (* [Run.budget_refused_at]'s no-syscall half is a disjunction: the first-touch instruction fault and the
     vDSO materialization fault.  Both are premises of an [SError] step, so both close the same way. *)
  destruct Hr as [(Hsvc & [ (report & Hstep & Hmat)
                          | (Hacct & fn & n & eff & model' & evs' &
                             Hfn & Hsys & Hspec & Hef & Hh' & Hmat) ])
                 | (x8 & Hx8 & [Hgr | (eff & model' & evs' & Hspec & Hh' & Hmat)])].
  - exact (Herr (budget_fault_instr_sstep_error segs ms model report Hh Hsvc Hstep Hmat)).
  - exact (Herr (budget_fault_vdso_sstep_error segs ms model fn n eff model' evs'
                   Hh Hsvc Hacct Hfn Hsys Hspec Hef Hh' Hmat)).
  - rewrite (alloc_budget_refused_b_outside (sys_input segs ms x8) model (Hb x8 Hx8)) in Hgr.
    discriminate Hgr.
  - exact (Herr (budget_fault_syscall_sstep_error segs ms model x8 eff model' evs' Hh Hx8 Hspec Hh' Hmat)).
Qed.

Lemma rz_star_not_refused : forall c T, realizes c T ->
  forall tr c', star segs c tr c' -> ~ budget_refused_at segs c'.
Proof.
  intros c T H;
  induction H as [c I evs nx T i0 Hnode Hrob Hb Hcont IH | c Hh | c T T' H IH Heq];
  intros tr c' Hstar.
  - destruct (star_cases_b _ _ _ Hstar) as [-> | (e & c2 & tr2 & Hss & Hstar2)].
    + exact (node_not_refused c I evs nx Hnode Hb).
    + destruct (proj2 Hnode e (SNext c2) (budget_ok_lift c e (SNext c2) Hb Hss))
        as (i & _ & Heq2).
      injection Heq2 as ->. exact (IH i tr2 c' Hstar2).
  - destruct (star_cases_b _ _ _ Hstar) as [-> | (e & c2 & tr2 & Hss & Hstar2)].
    + intros [Hn _]. exact (Hh Hn).
    + exfalso. exact (Hh (sstep_running_b c e _ Hss)).
  - exact (IH tr c' Hstar).
Qed.

(** No configuration the unfiltered run reaches from a [realizes]
    configuration is budget-refused. *)
Theorem rz_never_refused : forall c T, realizes c T -> ~ reaches_budget_refused segs c.
Proof.
  intros c T H (tr & c' & Hstar & Hb). exact (rz_star_not_refused c T H tr c' Hstar Hb).
Qed.

(** ... and so under every spurious-failure configuration. *)
Theorem rz_never_refused_cfg : forall cfg c T, realizes c T ->
  ~ reaches_budget_refused_cfg segs cfg c.
Proof.
  intros cfg c T H Hr. exact (rz_never_refused c T H (reaches_budget_refused_cfg_sub segs cfg c Hr)).
Qed.

(** ** QRjH's node lemmas on the usage path, over [realizes] *)

#[using="Type"] Lemma realizes_nonempty : forall c T, realizes c T -> T [].
Proof.
intros c T H; induction H as [c I evs nx T i0 Hnode Hrob Hb Hcont IH | c Hh | c T T' H IH Heq].
- exists i0. left. apply is_prefix_nil.
- reflexivity.
- apply Heq. exact IH.
Qed.

#[using="Type"] Lemma rz_silent1 : forall c c' T,
node_ok c unit (fun _ => []) (fun _ => c') ->
RomBase.sys_rob segs c ->
budget_ok c ->
realizes c' T ->
realizes c T.
Proof.
intros c c' T Hnode Hrob Hb Hc.
apply (rz_conseq c (t_alt (fun _ : unit => t_emit [] T))).
- apply (rz_node c unit (fun _ => []) (fun _ => c') (fun _ => T) tt Hnode Hrob Hb).
intros []; exact Hc.
- eapply t_eq_trans;
[ apply (t_alt_unit (fun _ : unit => t_emit [] T))
| apply t_emit_nil_eq; eapply realizes_nonempty; exact Hc ].
Qed.

#[using="Type"] Lemma rz_emit1 : forall c c' e T,
node_ok c unit (fun _ => e) (fun _ => c') ->
RomBase.sys_rob segs c ->
budget_ok c ->
realizes c' T ->
realizes c (t_emit e T).
Proof.
intros c c' e T Hnode Hrob Hb Hc.
apply (rz_conseq c (t_alt (fun _ : unit => t_emit e T))).
- apply (rz_node c unit (fun _ => e) (fun _ => c') (fun _ => T) tt Hnode Hrob Hb).
intros []; exact Hc.
- apply t_alt_unit.
Qed.

#[using="Type"] Lemma rz_step : forall ms model ms' T,
m_halted model = None ->
m_vm_lazy model = [] ->
ms_svc_pending ms = None ->
RiscvSemantics.step segs ms = MachineOk ms' ->
realizes (mkCfg ms' model) T ->
realizes (mkCfg ms model) T.
Proof.
intros ms model ms' T Hh Hlazy Hsvc Hstep Hc.
eapply rz_silent1; [apply node_instr; eassumption | exact (RomBase.sys_rob_instr segs (mkCfg ms model) Hsvc)
                   | apply budget_ok_instr; exact Hsvc | exact Hc].
Qed.

#[using="Type"] Lemma rz_msteps : forall ms ms' model T,
m_halted model = None ->
m_vm_lazy model = [] ->
msteps segs ms ms' ->
realizes (mkCfg ms' model) T ->
realizes (mkCfg ms model) T.
Proof.
intros ms ms' model T Hh Hlazy Hms;
induction Hms as [ms | ms ms1 ms2 Hsvc Hstep Hms IH];
intro Hc; [exact Hc|].
eapply rz_step; [exact Hh | exact Hlazy | exact Hsvc | exact Hstep
| apply IH; exact Hc].
Qed.

#[using="Type"] Lemma rz_exit : forall ms model x8,
m_halted model = None ->
ms_svc_pending ms = Some x8 ->
is_exit_no x8 ->
realizes (mkCfg ms model)
(t_exit (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)).
Proof.
intros ms model x8 Hh Hsvc Hx8.
set (code := bv_and (ms_gpr ms 0) (Z_to_bv 64 255)).
unfold t_exit.
eapply (rz_emit1 (mkCfg ms model) (mkCfg ms (with_halted code model))).
- split.
+ intros []. cbn.
replace [ExitEv code (m_fs model)]
with ([] ++ [ExitEv code (m_fs (with_halted code model))]) by reflexivity.
apply (sstep_cfg_exit segs (alloc_only_cfg false) ms model x8 (mkEffect (Z_to_bv 64 0) [] [])
(with_halted code model) [] code);
[exact Hh | exact Hsvc
| apply (exit_dispatch_ok (sys_input segs ms x8) model);
rewrite in_sysno_sys_input; exact Hx8
| reflexivity
| apply m_killed_with_halted ].
+ intros e st Hss.
destruct (sstep_exit_inv segs ms model x8 e st Hh Hsvc Hx8 (sstep_cfg_sub segs _ _ _ _ Hss)) as [-> ->].
exists tt. split; reflexivity.
- exact (RomBase.sys_rob_exit segs ms model x8 Hsvc Hx8).
- exact (budget_ok_exit ms model x8 Hsvc Hx8).
- apply rz_halt. cbn. discriminate.
Qed.

End WithSegs.
