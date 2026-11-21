(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from Lib/Shape.v's realizes and the lemmas about it that the usage path uses, with a no-allocation-call check at each node; adds the theorem that turns the carrier into the budget premise. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the three-part node_ok of Lib/Shape.v and the vDSO clause of the budget refusal). *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Common Require Import SimInv ExitSim.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Shape.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.

(** * The released carrier with a no-allocation-call check at each node

    [Shape.realizes] records, at each node, every step the configuration can
    take ([Shape.node_ok]).  That is enough to exclude the two first-touch
    clauses of [Run.budget_refused_at] (each is the premise of an error step,
    which a node does not admit), but not the grant clause: a pending brk,
    mremap, mmap or mprotect that the budget declines is answered with a
    refusal, an ordinary step.  So [realizes] alone cannot carry the budget
    premise.

    [realizes] below is [Shape.realizes] with one more premise at each node,
    [grant_free c]: if [c] has a pending system call, it is not one the budget
    declines.  Every other constructor is unchanged.  Its name is the released
    one, so that a released proof, copied into a module that imports this one
    after [Shape], is the same proof over this carrier.

    [realizes_not_refused] is the reason for the carrier: from a configuration
    it realizes, no configuration the run reaches is budget-refused. *)

Lemma t_alt_unit_b : forall (f : unit -> TSet), t_eq (t_alt f) (f tt).
Proof.
  intros f tr. split; [intros [[] Hf]; exact Hf | intro Hf; exists tt; exact Hf].
Qed.

Section WithSegs.
Variable segs : list Segment.

(** The pending system call, if any, is not one the budget declines. *)
Definition grant_free (c : config) : Prop :=
  forall x8, ms_svc_pending (cfg_ms c) = Some x8 ->
    alloc_budget_refused_b (sys_input segs (cfg_ms c) x8) (cfg_model c) = false.

Inductive realizes : config -> TSet -> Prop :=
| rz_node : forall c (I : Type) (evs : I -> list event) (nx : I -> config)
                   (T : I -> TSet) (i0 : I),
    Shape.node_ok segs c I evs nx ->
    grant_free c ->
    (forall i, realizes (nx i) (T i)) ->
    realizes c (t_alt (fun i => t_emit (evs i) (T i)))
| rz_halt : forall c,
    Shape.halted_ok c ->
    realizes c t_nil
| rz_conseq : forall c T T',
    realizes c T -> t_eq T T' -> realizes c T'.

(** An instruction configuration has no pending system call. *)
Lemma grant_free_instr : forall ms model,
  ms_svc_pending ms = None -> grant_free (mkCfg ms model).
Proof. intros ms model Hs y Hy. cbn [cfg_ms] in Hy. congruence. Qed.

(** A pending system call whose number is off [Run.alloc_mark_sysnos]. *)
Lemma grant_free_no : forall ms model x8,
  ms_svc_pending ms = Some x8 -> ~ In (bv_unsigned x8) alloc_mark_sysnos ->
  grant_free (mkCfg ms model).
Proof.
  intros ms model x8 Hs Hn y Hy. cbn [cfg_ms cfg_model] in Hy |- *.
  rewrite Hs in Hy. injection Hy as <-.
  apply alloc_budget_refused_b_outside. exact Hn.
Qed.

Lemma sstep_halted_none_b : forall c e st,
  sstep segs c e st -> m_halted (cfg_model c) = None.
Proof. intros c e st H; inversion H; subst; cbn; assumption. Qed.

Lemma realizes_nonempty : forall c T, realizes c T -> T [].
Proof.
  intros c T H; induction H as [c I evs nx T i0 Hnode Hg Hcont IH | c Hh | c T T' H IH Heq].
  - exists i0. left. apply is_prefix_nil.
  - reflexivity.
  - apply Heq. exact IH.
Qed.

Lemma realizes_step : forall c T e c',
  realizes c T -> sstep segs c e (SNext c') -> exists T', realizes c' T'.
Proof.
  intros c T e c' H; revert e c';
  induction H as [c I evs nx T i0 Hnode Hg Hcont IH | c Hh | c T T' H IH Heq];
    intros e c' Hss.
  - destruct Hnode as (_ & Hsound & _).
    destruct (Hsound e (SNext c') Hss) as (i & _ & Heq2).
    inversion Heq2; subst c'. exists (T i). apply Hcont.
  - exfalso. destruct Hh as [[a Ha] _].
    rewrite (sstep_halted_none_b c e (SNext c') Hss) in Ha. discriminate Ha.
  - eapply IH; exact Hss.
Qed.

(** A realized configuration is not budget-refused: the instruction, vDSO
    and effect clauses are premises of an error step, which [Shape.node_ok]
    excludes; the grant clause is what [grant_free] excludes; a halted
    configuration is not refused. *)
Lemma realizes_not_refused_at : forall c T, realizes c T -> ~ budget_refused_at segs c.
Proof.
  intros c T H; induction H as [c I evs nx T i0 Hnode Hg Hcont IH | c Hh | c T T' H IH Heq].
  - destruct c as [ms model]. destruct Hnode as (_ & Hsound & _).
    intros (Hn & [(Hsvc & [(report & Hstep & Hmat)
                          | (Hacct & fn & n & eff & model' & evs' &
                             Hfn & Hsys & Hspec & Hef & Hh' & Hmat)])
                 | (x8 & Hx8 & [Hb | (eff & model' & evs' & Hspec & Hh' & Hmat)])]);
      cbn [cfg_ms cfg_model] in *.
    + destruct (Hsound [] SError
                  (budget_fault_instr_sstep_error segs ms model report Hn Hsvc Hstep Hmat))
        as (i & _ & Habs).
      discriminate Habs.
    + destruct (Hsound [] SError
                  (budget_fault_vdso_sstep_error segs ms model fn n eff model' evs'
                     Hn Hsvc Hacct Hfn Hsys Hspec Hef Hh' Hmat))
        as (i & _ & Habs).
      discriminate Habs.
    + pose proof (Hg x8 Hx8) as Hf. cbn [cfg_ms cfg_model] in Hf. congruence.
    + destruct (Hsound [] SError
                  (budget_fault_syscall_sstep_error segs ms model x8 eff model' evs'
                     Hn Hx8 Hspec Hh' Hmat))
        as (i & _ & Habs).
      discriminate Habs.
  - intros (Hn & _). destruct Hh as [[a Ha] _]. rewrite Ha in Hn. discriminate Hn.
  - exact IH.
Qed.

(** From a configuration this carrier realizes, the run reaches no
    budget-refused configuration. *)
Theorem realizes_not_refused : forall c T, realizes c T -> ~ reaches_budget_refused segs c.
Proof.
  intros c T H.
  apply (never_budget_refused_ind segs (fun c => exists T, realizes c T) c).
  - exists T. exact H.
  - intros c1 evs c2 (T1 & H1) Hss. exact (realizes_step c1 T1 evs c2 H1 Hss).
  - intros c1 (T1 & H1). exact (realizes_not_refused_at c1 T1 H1).
Qed.

(** The node rules the usage path uses, as [Shape] states them, with the
    node's [grant_free] premise. *)
Lemma rz_silent1 : forall c c' T,
  Shape.node_ok segs c unit (fun _ => []) (fun _ => c') ->
  grant_free c ->
  realizes c' T ->
  realizes c T.
Proof.
  intros c c' T Hnode Hg Hc.
  apply (rz_conseq c (t_alt (fun _ : unit => t_emit [] T))).
  - apply (rz_node c unit (fun _ => []) (fun _ => c') (fun _ => T) tt Hnode Hg).
    intros []; exact Hc.
  - eapply t_eq_trans;
      [ apply (t_alt_unit_b (fun _ : unit => t_emit [] T))
      | apply t_emit_nil_eq; eapply realizes_nonempty; exact Hc ].
Qed.

Lemma rz_emit1 : forall c c' e T,
  Shape.node_ok segs c unit (fun _ => e) (fun _ => c') ->
  grant_free c ->
  realizes c' T ->
  realizes c (t_emit e T).
Proof.
  intros c c' e T Hnode Hg Hc.
  apply (rz_conseq c (t_alt (fun _ : unit => t_emit e T))).
  - apply (rz_node c unit (fun _ => e) (fun _ => c') (fun _ => T) tt Hnode Hg).
    intros []; exact Hc.
  - apply t_alt_unit_b.
Qed.

(** An instruction step: the released statement, no new premise. *)
Lemma rz_step : forall ms model ms' T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  realizes (mkCfg ms' model) T ->
  realizes (mkCfg ms model) T.
Proof.
  intros ms model ms' T Hh Hlazy Hsvc Hstep Hc.
  eapply rz_silent1;
    [ apply (node_instr segs); eassumption
    | apply grant_free_instr; exact Hsvc
    | exact Hc ].
Qed.

Lemma rz_msteps : forall ms ms' model T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  Shape.msteps segs ms ms' ->
  realizes (mkCfg ms' model) T ->
  realizes (mkCfg ms model) T.
Proof.
  intros ms ms' model T Hh Hlazy Hms;
    induction Hms as [ms | ms ms1 ms2 Hsvc Hstep Hms IH];
    intro Hc; [exact Hc|].
  eapply rz_step; [exact Hh | exact Hlazy | exact Hsvc | exact Hstep
                  | apply IH; exact Hc].
Qed.

End WithSegs.

(** The number checks the system-call nodes discharge [grant_free] with. *)
Lemma not_alloc_lit : forall (x8 : word) (n : Z), bv_unsigned x8 = n ->
  existsb (Z.eqb n) alloc_mark_sysnos = false ->
  ~ In (bv_unsigned x8) alloc_mark_sysnos.
Proof.
  intros x8 n Hn Hb Hin. rewrite Hn in Hin.
  apply Bool.not_true_iff_false in Hb. apply Hb.
  apply existsb_exists. exists n. split; [exact Hin | apply Z.eqb_refl].
Qed.

Lemma not_alloc_exit : forall x8, is_exit_no x8 -> ~ In (bv_unsigned x8) alloc_mark_sysnos.
Proof. intros x8 [E|E]; apply (not_alloc_lit x8 _ E); reflexivity. Qed.
