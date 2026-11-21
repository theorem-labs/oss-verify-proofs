(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from YK15.v: the relation realizes with a budget check at each node (rzb), its soundness for the budget premise, and YK15's node lemmas restated over rzb; alloc_no_b and alloc_no_b_false as cgif_file_fuzzer's proofs/lib/R/Cfg.v states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (node_ok's third part, sys_rob, at the nodes, with sys_rob_exit at the exit node; the new vDSO-entry arm of budget_refused_at in node_not_refused; rzb walks lifted to the run's segment list, run_segments, and its start configuration by rzb_wrom, rzb_app_tail, rzb_run_segments and rzb_run_init; RomBase and RomStable imports). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK16 YK0o YK0j YK0v YK02 YK03 YK1i YK15 RomBase.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require RomStable.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Open Scope bv_scope.

(** * [rzb]: [YK15.realizes] with a budget check at each node

    [YK15.realizes segs c T] ties a trace set to the one-step families of the
    configurations a run reaches.  In this tree it has three constructors,
    [rz_node], [rz_halt] and [rz_conseq]: there is no cut, so a [realizes] proof
    never stops at a budget-refused configuration.  Its [node_ok] lists the steps
    of the unfiltered [sstep segs] (no spurious-failure configuration is fixed),
    so its completeness half already covers every step of the unfiltered run.  It
    still says nothing about the budget: a derivation records no fact about the
    grant check of the syscalls it passes.

    [rzb] has the same three constructors, and its node constructor asks, besides
    [node_ok], for [budget_ok segs c]: if a syscall is pending at [c], the budget
    mark [Run.alloc_budget_refused_b] answers [false] on it.

    [rzb_never_refused] reads an [rzb] derivation: no configuration the unfiltered
    run reaches is budget-refused.  The two first-touch clauses of
    [Run.budget_refused_at] are premises of an [SError] step
    ([Run.budget_fault_instr_sstep_error], [Run.budget_fault_syscall_sstep_error]),
    which the completeness half of [node_ok] excludes; the grant clause is the
    negation of [budget_ok].  Every filtered run is an unfiltered run
    ([Run.reaches_budget_refused_cfg_sub]), so the fact holds under every
    spurious-failure configuration ([rzb_never_refused_cfg]).

    The rest of the file is YK15's lemmas that build a [realizes] node, restated
    over [rzb] with YK15's proofs: [rz_] is written [rzb_], and each lemma that
    takes a [node_ok] also takes [budget_ok] for the same configuration.  214,
    216, 222 and 226 are the RISC-V Linux numbers of brk, mremap, mmap and
    mprotect ([Run.alloc_mark_sysnos]). *)

(** Whether [n] is one of the four allocation numbers, by computation. *)
Definition alloc_no_b (n : Z) : bool :=
  match List.find (Z.eqb n) alloc_mark_sysnos with Some _ => true | None => false end.
Lemma alloc_no_b_false : forall n, alloc_no_b n = false -> ~ In n alloc_mark_sysnos.
Proof.
  intros n H Hin. unfold alloc_no_b in H.
  destruct (List.find (Z.eqb n) alloc_mark_sysnos) eqn:E; [discriminate H|].
  pose proof (List.find_none _ _ E n Hin) as Hn. rewrite Z.eqb_refl in Hn. discriminate Hn.
Qed.

Section g.
Variable segs : list Segment.

(** If a syscall is pending at [c], the budget does not refuse it as a grant. *)
Definition budget_ok (c : config) : Prop :=
  forall x8, ms_svc_pending (cfg_ms c) = Some x8 ->
    alloc_budget_refused_b (sys_input segs (cfg_ms c) x8) (cfg_model c) = false.

Lemma budget_ok_instr : forall ms model,
  ms_svc_pending ms = None -> budget_ok (mkCfg ms model).
Proof.
  intros ms model Hsvc x8 Hx. cbn [cfg_ms] in Hx. rewrite Hsvc in Hx. discriminate Hx.
Qed.

Lemma budget_ok_nonalloc : forall ms model x8,
  ms_svc_pending ms = Some x8 -> ~ In (bv_unsigned x8) alloc_mark_sysnos ->
  budget_ok (mkCfg ms model).
Proof.
  intros ms model x8 Hsvc Hnin y Hy. cbn [cfg_ms cfg_model] in *.
  rewrite Hsvc in Hy. injection Hy as <-.
  apply alloc_budget_refused_b_outside. exact Hnin.
Qed.

(** The number as a literal, checked by [alloc_no_b]. *)
Lemma budget_ok_no : forall ms (model : Model) (x8 : word) (n : Z),
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = n -> alloc_no_b n = false ->
  budget_ok (mkCfg ms model).
Proof.
  intros ms model x8 n Hsvc Hx Hb. subst n.
  exact (budget_ok_nonalloc ms model x8 Hsvc (alloc_no_b_false _ Hb)).
Qed.

(** The exit (93 or 94) is off the four allocation numbers. *)
Lemma budget_ok_exit : forall ms model x8,
  ms_svc_pending ms = Some x8 -> is_exit_no x8 -> budget_ok (mkCfg ms model).
Proof.
  intros ms model x8 Hsvc [E|E]; (eapply budget_ok_no; [exact Hsvc | exact E | reflexivity]).
Qed.
End g.

Section d.
Variable segs : list Segment.
Inductive rzb : config -> TSet -> Prop :=
| rzb_node : forall c (I : Type) (evs : I -> list event) (nx : I -> config)
(T : I -> TSet) (i0 : I),
node_ok segs c I evs nx ->
budget_ok segs c ->
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

(** A node with the budget check is not budget-refused. *)
Lemma node_not_refused : forall c I evs nx,
  node_ok segs c I evs nx -> budget_ok segs c -> ~ budget_refused_at segs c.
Proof.
  intros [ms model] I evs nx [_ [Hc _]] Hg [Hh Hb].
  assert (Herr : ~ sstep segs (mkCfg ms model) [] SError).
  { intros Hs.
    destruct (Hc [] SError Hs) as (i & _ & Hbad).
    discriminate Hbad. }
  cbn [cfg_ms cfg_model] in Hh, Hb.
  (* LPS 727298f3: an instruction configuration is also budget-refused at a vDSO entry whose
     system call cannot materialize its accesses (Run.budget_refused_at's second arm). *)
  destruct Hb as [(Hsvc & [(report & Hstep & Hmat)
                           | (Hun & fn & n & eff & model' & evs' & Hfn & Hn & Hspec & Hret & Hh' & Hmat)])
                 | (x8 & Hx8 & [Hgr | (eff & model' & evs' & Hspec & Hh' & Hmat)])].
  - exact (Herr (budget_fault_instr_sstep_error segs ms model report Hh Hsvc Hstep Hmat)).
  - exact (Herr (budget_fault_vdso_sstep_error segs ms model fn n eff model' evs' Hh Hsvc Hun Hfn Hn Hspec Hret Hh' Hmat)).
  - pose proof (Hg x8 Hx8) as Hg'. cbn [cfg_ms cfg_model] in Hg'. congruence.
  - exact (Herr (budget_fault_syscall_sstep_error segs ms model x8 eff model' evs' Hh Hx8 Hspec Hh' Hmat)).
Qed.

Lemma rzb_star_not_refused : forall c T, rzb segs c T ->
  forall tr c', star segs c tr c' -> ~ budget_refused_at segs c'.
Proof.
  intros c T H;
  induction H as [c I evs nx T i0 Hnode Hg Hcont IH | c Hh | c T T' H IH Heq];
  intros tr c' Hstar.
  - destruct (star_cases _ _ _ Hstar) as [-> | (e & c2 & tr2 & Hss & Hstar2)].
    + exact (node_not_refused c I evs nx Hnode Hg).
    + destruct (proj1 (proj2 Hnode) e (SNext c2) Hss) as (i & _ & Heq2).
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

(** ** YK15's node lemmas over [rzb] *)
Section d2.
Variable segs : list Segment.
Local Notation rzb := (rzb segs).
Local Notation rzb_node := (rzb_node segs).
Local Notation rzb_halt := (rzb_halt segs).
Local Notation rzb_conseq := (rzb_conseq segs).
Lemma rzb_nonempty : forall c T, rzb c T -> T [].
Proof.
intros c T H; induction H as [c I evs nx T i0 Hnode Hg Hcont IH | c Hh | c T T' H IH Heq].
- exists i0. left. apply is_prefix_nil.
- reflexivity.
- apply Heq. exact IH.
Qed.
Lemma rzb_emit_nil : forall c T, rzb c T -> rzb c (t_emit [] T).
Proof.
intros c T H. eapply rzb_conseq; [exact H|]. apply t_eq_sym. apply t_emit_nil_eq.
eapply rzb_nonempty. exact H.
Qed.
Lemma rzb_silent1 : forall c c' T,
node_ok segs c unit (fun _ => []) (fun _ => c') ->
budget_ok segs c ->
rzb c' T ->
rzb c T.
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
node_ok segs c unit (fun _ => e) (fun _ => c') ->
budget_ok segs c ->
rzb c' T ->
rzb c (t_emit e T).
Proof.
intros c c' e T Hnode Hg Hc.
apply (rzb_conseq c (t_alt (fun _ : unit => t_emit e T))).
- apply (rzb_node c unit (fun _ => e) (fun _ => c') (fun _ => T) tt Hnode Hg).
intros []; exact Hc.
- apply t_alt_unit.
Qed.
Lemma rzb_silent_allI : forall c (I : Type) (nx : I -> config) (i0 : I) T,
node_ok segs c I (fun _ => []) nx ->
budget_ok segs c ->
(forall i, rzb (nx i) T) ->
rzb c T.
Proof.
intros c I nx i0 T Hnode Hg Hc.
assert (HT0 : T []) by (eapply rzb_nonempty; apply (Hc i0)).
apply (rzb_conseq c (t_alt (fun _ : I => t_emit [] T))).
- apply (rzb_node c I (fun _ => []) nx (fun _ => T) i0 Hnode Hg). exact Hc.
- intro tr. split.
+ intros [i Hi]. exact (proj1 (t_emit_nil_eq T HT0 tr) Hi).
+ intro HT. exists i0. exact (proj2 (t_emit_nil_eq T HT0 tr) HT).
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
eapply rzb_silent1; [apply node_instr; eassumption | apply budget_ok_instr; exact Hsvc | exact Hc].
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
eapply (rzb_emit1 (mkCfg ms model) (mkCfg ms (with_halted code model))).
- split; [| split; [| exact (RomBase.sys_rob_exit segs ms model x8 Hsvc Hx8)]].
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
- exact (budget_ok_exit segs ms model x8 Hsvc Hx8).
- apply rzb_halt. cbn. discriminate.
Qed.
End d2.

(** ** The walk over the binary's own segments, lifted to the run

    LPS 727298f3: [Run.run_budget_refused] and [Run.run_scfg_budget_refused] read the
    run against [run_segments segs inp sp mbase] -- the binary's segments with the
    run's vDSO appended -- and from the start configuration over that list.  A walk
    is built over the binary's own segments, so it is lifted, exactly as
    [RomStable.run_init] lifts a [YK15.realizes] walk; every node-level step is
    RomStable's own.  [budget_ok] reads only the system-call number and arguments
    ([Run.alloc_budget_refused_b]), which neither a larger read-only backing nor
    appended segments change. *)
Lemma budget_ok_cwrom : forall segs c r, budget_ok segs c -> budget_ok segs (cwrom c r).
Proof. intros segs [ms model] r H x8 Hx. exact (H x8 Hx). Qed.

Lemma budget_ok_app_tail : forall segs tail c, budget_ok segs c -> budget_ok (segs ++ tail) c.
Proof. intros segs tail [ms model] H x8 Hx. exact (H x8 Hx). Qed.

Section RzbWrom.
  Variable segs : list Segment.
  Hypothesis Hvi : vdso_image segs = None.

  Theorem rzb_wrom : forall c T, rzb segs c T ->
    forall r, rom_ext (ms_rom (cfg_ms c)) r -> rzb segs (cwrom c r) T.
  Proof.
    intros c T H;
    induction H as [c I evs nx T i0 Hn Hb Hc IH | c Hh | c T T' H IH Heq];
    intros r Hr.
    - apply (rzb_node segs (cwrom c r) I evs (fun i => cwrom (nx i) r) T i0).
      + eapply RomStable.node_wrom; eassumption.
      + apply budget_ok_cwrom; exact Hb.
      + intros i. apply IH.
        match goal with |- rom_ext ?x _ => replace x with (ms_rom (cfg_ms c)) end;
          [exact Hr|].
        symmetry. eapply RomStable.node_rom; eassumption.
    - apply rzb_halt. exact Hh.
    - eapply rzb_conseq; [apply IH; exact Hr | exact Heq].
  Qed.
End RzbWrom.

Section RzbAppTail.
  Variables segs tail : list Segment.
  Hypothesis Hnx : forall s, In s tail -> seg_executable s = false.
  Hypothesis Hnw : forall s, In s tail -> seg_writable s = false.
  Hypothesis Hvi : vdso_image segs = None.

  Theorem rzb_app_tail : forall c T, rzb segs c T -> rzb (segs ++ tail) c T.
  Proof.
    intros c T H;
    induction H as [c I evs nx T i0 Hn Hb Hc IH | c Hh | c T T' H IH Heq].
    - apply (rzb_node (segs ++ tail) c I evs nx T i0).
      + eapply RomStable.node_ok_app_tail; eassumption.
      + apply budget_ok_app_tail; exact Hb.
      + exact IH.
    - apply rzb_halt. exact Hh.
    - eapply rzb_conseq; [exact IH | exact Heq].
  Qed.
End RzbAppTail.

Theorem rzb_run_segments : forall segs inp (sp mb : word) c T,
  vdso_image segs = None ->
  rzb segs c T -> rzb (run_segments segs inp sp mb) c T.
Proof.
  intros segs inp sp mb c T Hvi H. unfold run_segments.
  apply (rzb_app_tail segs _
           (fun s Hs => RomStable.vdso_segments_nx _ _ _ s Hs)
           (fun s Hs => RomStable.vdso_segments_nw _ _ _ s Hs) Hvi).
  exact H.
Qed.

(** A walk over the binary's own segments, from the binary's start, is a walk of the
    run's start over the run's segment list. *)
Theorem rzb_run_init : forall segs inp (sp mb : word) pc ph brk rnd lim T,
  vdso_image segs = None ->
  rzb segs (init_config segs pc ph sp brk mb rnd lim inp) T ->
  rzb (run_segments segs inp sp mb)
    (init_config (run_segments segs inp sp mb) pc ph sp brk mb rnd lim inp) T.
Proof.
  intros segs inp sp mb pc ph brk rnd lim T Hvi H.
  rewrite RomStable.init_config_run_segments.
  apply rzb_run_segments; [exact Hvi|].
  apply (rzb_wrom segs Hvi); [exact H|].
  rewrite RomStable.init_config_rom. apply RomStable.rom_ext_run_segments.
Qed.
