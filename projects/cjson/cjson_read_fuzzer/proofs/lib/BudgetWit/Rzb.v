(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from ShapeAlg.v: the relation realizes with a no-allocation-call check at each node (rzb), its soundness for the budget premise, and ShapeAlg's node lemmas that the usage path uses, restated over rzb. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: node_not_refused also excludes the vDSO materialization clause of Run.budget_refused_at, an SError step by budget_fault_vdso_sstep_error; rzb_node takes RomBase.sys_rob after node_ok, so rzb_silent1 and rzb_emit1 take it and rzb_step and rzb_exit prove it, as ShapeAlg's rz_node does. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require ExitSim.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ExitSim.SimInv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ExitSim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require WallSim.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.WallSim.CatSim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import MmapSim AllocSim WallSim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Cfg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import RomBase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.

(** * [rzb]: [ShapeAlg.realizes] with a no-allocation-call check at each node

    [ShapeAlg.realizes segs c T] ties a trace set to the one-step families of
    the configurations a run reaches.  It has three constructors, [rz_node],
    [rz_halt] and [rz_conseq]; there is no cut.  It still says nothing about
    the budget: a derivation records no fact about the system calls it passes,
    so no [realizes] proof says that a run is never refused by the budget.

    [rzb] has the same three constructors, and its node constructor asks,
    besides [node_ok], for [grant_ok c]: if a syscall is pending at [c], its
    number is none of the four allocation numbers 214, 216, 222 and 226 (brk,
    mremap, mmap, mprotect; [Run.alloc_mark_sysnos]).

    In this tree [node_ok] is stated over [sstep_cfg segs ACFG], the run that
    may refuse an allocation call spuriously ([Cfg.ACFG]), not over the
    unfiltered [sstep]; the two differ in general.  At a configuration where
    no allocation call is pending they coincide: an instruction step and an
    exit step have no refusal premise, and a syscall step off the allocation
    numbers is never a spurious refusal under [ACFG] ([Cfg.acfg_nonspurious]),
    so every [sstep] from there is an [sstep_cfg segs ACFG] step
    ([sstep_acfg_of_grant], from [Cfg.sstep_cfg_of_sstep]).  That is why
    [grant_ok] asks for a non-allocation number rather than only for the budget
    mark's answer: it makes the completeness half of [node_ok] cover every
    unfiltered step, and it gives the budget mark's answer as well
    ([grant_ok_budget], [Run.alloc_budget_refused_b_outside]).

    [rzb_never_refused]: no configuration the unfiltered run reaches from an
    [rzb] configuration is budget-refused.  The three fault clauses of
    [Run.budget_refused_at] are premises of an [SError] step
    ([Run.budget_fault_instr_sstep_error], [Run.budget_fault_vdso_sstep_error],
    [Run.budget_fault_syscall_sstep_error]),
    which the completeness half of [node_ok] excludes; the grant clause is
    excluded by [grant_ok_budget].  [rzb_never_refused_cfg] gives the same for
    every spurious-failure configuration ([Run.reaches_budget_refused_cfg_sub]).

    The rest of the file is ShapeAlg's lemmas that build a [realizes] node and
    that the usage path uses, restated over [rzb] with ShapeAlg's proofs.  Each
    lemma that takes a [node_ok] also takes [grant_ok] for the same
    configuration. *)

(** If a syscall is pending at [c], it is not an allocation call. *)
Definition grant_ok (c : config) : Prop :=
  forall x8, ms_svc_pending (cfg_ms c) = Some x8 -> ~ In (bv_unsigned x8) alloc_mark_sysnos.

Lemma grant_ok_instr : forall ms model,
  ms_svc_pending ms = None -> grant_ok (mkCfg ms model).
Proof.
  intros ms model Hsvc x8 Hx. cbn [cfg_ms] in Hx. rewrite Hsvc in Hx. discriminate Hx.
Qed.

Lemma grant_ok_nonalloc : forall ms model x8,
  ms_svc_pending ms = Some x8 -> ~ In (bv_unsigned x8) alloc_mark_sysnos ->
  grant_ok (mkCfg ms model).
Proof.
  intros ms model x8 Hsvc Hnin y Hy. cbn [cfg_ms] in Hy.
  rewrite Hsvc in Hy. injection Hy as <-. exact Hnin.
Qed.

(** The form [Cfg.nsp_no] has: the number as a literal, checked by [alloc_no_b]. *)
Lemma grant_ok_no : forall ms (model : Model) (x8 : word) (n : Z),
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = n -> alloc_no_b n = false ->
  grant_ok (mkCfg ms model).
Proof.
  intros ms model x8 n Hsvc Hx Hb. subst n.
  exact (grant_ok_nonalloc ms model x8 Hsvc (alloc_no_b_false _ Hb)).
Qed.

(** The exit (93 or 94) is off the four allocation numbers. *)
Lemma grant_ok_exit : forall ms model x8,
  ms_svc_pending ms = Some x8 -> is_exit_no x8 -> grant_ok (mkCfg ms model).
Proof.
  intros ms model x8 Hsvc [E|E]; (eapply grant_ok_no; [exact Hsvc | exact E | reflexivity]).
Qed.

Section g.
Variable segs : list Segment.

(** ... so the budget does not refuse it as a grant. *)
Lemma grant_ok_budget : forall c x8,
  grant_ok c -> ms_svc_pending (cfg_ms c) = Some x8 ->
  alloc_budget_refused_b (sys_input segs (cfg_ms c) x8) (cfg_model c) = false.
Proof.
  intros c x8 Hg Hx.
  exact (alloc_budget_refused_b_outside (sys_input segs (cfg_ms c) x8) (cfg_model c) (Hg x8 Hx)).
Qed.

(** Where no allocation call is pending, every step is an [ACFG] step. *)
Lemma sstep_acfg_of_grant : forall c e st,
  grant_ok c -> sstep segs c e st -> sstep_cfg segs ACFG c e st.
Proof.
  intros [ms mo] e st Hg H. apply sstep_cfg_of_sstep; [exact H|].
  intros x8 eff m' evs' Hx _ _. apply acfg_nonspurious. exact (Hg x8 Hx).
Qed.
End g.

Section d.
Variable segs : list Segment.
Inductive rzb : config -> TSet -> Prop :=
| rzb_node : forall c (I : Type) (evs : I -> list event) (nx : I -> config)
                    (T : I -> TSet) (i0 : I),
    node_ok segs c I evs nx ->
    (* the node's system call reads no byte a larger read-only backing adds (RomBase.sys_rob), so
       RzbRom.rzb_run_init lifts a walk to the run's segment list *)
    sys_rob segs c ->
    grant_ok c ->
    (forall i, rzb (nx i) (T i)) ->
    rzb c (t_alt (fun i => t_emit (evs i) (T i)))
| rzb_halt : forall c,
    m_halted (cfg_model c) <> None ->
    rzb c t_nil
| rzb_conseq : forall c T T',
    rzb c T -> t_eq T T' -> rzb c T'.
End d.

(** ** Soundness *)
Section s.
Variable segs : list Segment.

Lemma sstep_running : forall c e st, sstep segs c e st -> m_halted (cfg_model c) = None.
Proof. intros c e st H. destruct H; cbn [cfg_model]; assumption. Qed.

Lemma star_cases : forall c tr c', star segs c tr c' ->
  c' = c \/ exists e c2 tr2, sstep segs c e (SNext c2) /\ star segs c2 tr2 c'.
Proof.
  intros c tr c' H. destruct H as [c0 | c1 e c2 tr2 c3 Hss Hstar].
  - left. reflexivity.
  - right. exists e, c2, tr2. split; [exact Hss | exact Hstar].
Qed.

(** A node with the grant check is not budget-refused. *)
Lemma node_not_refused : forall c I evs nx,
  node_ok segs c I evs nx -> grant_ok c -> ~ budget_refused_at segs c.
Proof.
  intros [ms model] I evs nx [_ Hc] Hg [Hh Hb].
  assert (Herr : ~ sstep segs (mkCfg ms model) [] SError).
  { intros Hs.
    destruct (Hc [] SError (sstep_acfg_of_grant segs _ [] SError Hg Hs)) as (i & _ & Hbad).
    discriminate Hbad. }
  cbn [cfg_ms cfg_model] in Hh, Hb.
  destruct Hb as [(Hsvc & [(report & Hstep & Hmat)
                          | (Hun & fn & n & eff & model' & evs' & Hfn & Hn & Hspec & Hne & Hh' & Hmat)])
                 | (x8 & Hx8 & [Hgr | (eff & model' & evs' & Hspec & Hh' & Hmat)])].
  - exact (Herr (budget_fault_instr_sstep_error segs ms model report Hh Hsvc Hstep Hmat)).
  - exact (Herr (budget_fault_vdso_sstep_error segs ms model fn n eff model' evs'
                   Hh Hsvc Hun Hfn Hn Hspec Hne Hh' Hmat)).
  - pose proof (grant_ok_budget segs (mkCfg ms model) x8 Hg Hx8) as Hg'.
    cbn [cfg_ms cfg_model] in Hg'. congruence.
  - exact (Herr (budget_fault_syscall_sstep_error segs ms model x8 eff model' evs' Hh Hx8 Hspec Hh' Hmat)).
Qed.

Lemma rzb_star_not_refused : forall c T, rzb segs c T ->
  forall tr c', star segs c tr c' -> ~ budget_refused_at segs c'.
Proof.
  intros c T H;
  induction H as [c I evs nx T i0 Hnode Hrob Hg Hcont IH | c Hh | c T T' H IH Heq];
  intros tr c' Hstar.
  - destruct (star_cases _ _ _ Hstar) as [-> | (e & c2 & tr2 & Hss & Hstar2)].
    + exact (node_not_refused c I evs nx Hnode Hg).
    + destruct (proj2 Hnode e (SNext c2) (sstep_acfg_of_grant segs c e (SNext c2) Hg Hss))
        as (i & _ & Heq2).
      injection Heq2 as ->. exact (IH i tr2 c' Hstar2).
  - destruct (star_cases _ _ _ Hstar) as [-> | (e & c2 & tr2 & Hss & Hstar2)].
    + intros [Hn _]. exact (Hh Hn).
    + exfalso. exact (Hh (sstep_running c e _ Hss)).
  - exact (IH tr c' Hstar).
Qed.

(** No configuration the run reaches from an [rzb] configuration is
    budget-refused. *)
Theorem rzb_never_refused : forall c T, rzb segs c T ->
  ~ reaches_budget_refused segs c.
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

(** ** ShapeAlg's node lemmas over [rzb] *)
Section WithSegs.
Variable segs : list Segment.

Lemma rzb_nonempty : forall c T, rzb segs c T -> T [].
Proof.
  intros c T H; induction H as [c I evs nx T i0 Hnode Hrob Hg Hcont IH | c Hh | c T T' H IH Heq].
  - exists i0. left. apply is_prefix_nil.
  - reflexivity.
  - apply Heq. exact IH.
Qed.

Lemma rzb_silent1 : forall c c' T,
  node_ok segs c unit (fun _ => []) (fun _ => c') -> sys_rob segs c ->
  grant_ok c ->
  rzb segs c' T ->
  rzb segs c T.
Proof.
  intros c c' T Hnode Hrob Hg Hc.
  apply (rzb_conseq segs c (t_alt (fun _ : unit => t_emit [] T))).
  - apply (rzb_node segs c unit (fun _ => []) (fun _ => c') (fun _ => T) tt Hnode Hrob Hg).
    intros []; exact Hc.
  - eapply t_eq_trans;
      [ apply (t_alt_unit (fun _ : unit => t_emit [] T))
      | apply t_emit_nil_eq; eapply rzb_nonempty; exact Hc ].
Qed.

Lemma rzb_emit1 : forall c c' e T,
  node_ok segs c unit (fun _ => e) (fun _ => c') -> sys_rob segs c ->
  grant_ok c ->
  rzb segs c' T ->
  rzb segs c (t_emit e T).
Proof.
  intros c c' e T Hnode Hrob Hg Hc.
  apply (rzb_conseq segs c (t_alt (fun _ : unit => t_emit e T))).
  - apply (rzb_node segs c unit (fun _ => e) (fun _ => c') (fun _ => T) tt Hnode Hrob Hg).
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
                      | apply grant_ok_instr; exact Hsvc | exact Hc].
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
  - split.
    + intros []. cbn.
      replace [ExitEv code (m_fs model)]
        with ([] ++ [ExitEv code (m_fs (with_halted code model))]) by reflexivity.
      apply (sstep_cfg_exit segs ACFG ms model x8 (mkEffect (Z_to_bv 64 0) [] [])
               (with_halted code model) [] code);
        [exact Hh | exact Hsvc
         | apply (exit_dispatch_ok (sys_input segs ms x8) model);
           rewrite in_sysno_sys_input; exact Hx8
         | reflexivity
         | apply m_killed_with_halted ].
    + intros e st Hss. apply sstep_cfg_sub in Hss.
      destruct (sstep_exit_inv segs ms model x8 e st Hh Hsvc Hx8 Hss) as [-> ->].
      exists tt. split; reflexivity.
  - destruct Hx8 as [Hx8' | Hx8'];
      (eapply sys_rob_memfree; [exact Hsvc | rewrite Hx8'; first [exact memfree_93 | exact memfree_94]]).
  - exact (grant_ok_exit ms model x8 Hsvc Hx8).
  - apply rzb_halt. cbn. discriminate.
Qed.

End WithSegs.
