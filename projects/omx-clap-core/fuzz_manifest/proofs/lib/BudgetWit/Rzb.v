(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YK15.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from Reusable/YK15.v: the relation realizes without its cut and with a no-allocation-call check at each node (rzb), its soundness for the budget premise, and YK15's node lemmas restated over rzb. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the revision's munmap (errno arm, cut, allocation mark); the vDSO pair and its reserved region; mremap's new answers; mprotect's vDSO gate; the node obligation sys_rob and the new system calls; the budget obligation at the changed nodes). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK16 YK0n YK0i YK0v YK02 YK1i YK15.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable.R Require Import Cfg.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import RomBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require RomStableK.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Open Scope bv_scope.

(** * [rzb]: [YK15.realizes] without the cut, with a grant check at each node

    [YK15.realizes segs c T] ties a trace set to the one-step families of the
    configurations a run reaches.  Its constructor [rz_cut] lets a derivation
    stop at any configuration where the budget refuses memory, and a derivation
    records nothing about the configurations it passes, so no [realizes] proof
    says that a run is never refused.  [rzb] has the same constructors less
    [rz_cut], and its two node constructors ask, besides [node_ok], for
    [grant_ok c]: if a syscall is pending at [c], its number is none of the
    allocation numbers of [Run.alloc_mark_sysnos] (brk 214, munmap 215 from
    LPS 727298f3 on, mremap 216, mmap 222, mprotect 226).

    In this tree [node_ok] is stated over [sstep_cfg segs ACFG], the run that
    never refuses an allocation call spuriously ([Cfg.ACFG]), not over the
    unfiltered [sstep]; there is no lemma that the two coincide, and they do
    not in general: [sstep] also takes the spurious refusals of an allocation
    call.  At a configuration where no allocation call is pending they do
    coincide: an instruction step and an exit step have no refusal premise, and
    a syscall step off the allocation numbers is never a spurious refusal under
    [ACFG] ([Cfg.acfg_nonspurious]), so every [sstep] from there is an
    [sstep_cfg segs ACFG] step ([sstep_acfg_of_grant]; the converse is
    [Run.sstep_cfg_sub]).  That is why [grant_ok] asks for a non-allocation
    number rather than only for the budget mark's answer: it makes the
    completeness half of [node_ok] cover every unfiltered step, and it gives
    the budget mark's answer as well ([grant_ok_budget],
    [Run.alloc_budget_refused_b_outside]).

    [rzb_never_refused]: no configuration the unfiltered run reaches from an
    [rzb] configuration is budget-refused.  The two first-touch clauses of
    [Run.budget_refused_at] are premises of an [SError] step
    ([Run.budget_fault_instr_sstep_error], [Run.budget_fault_syscall_sstep_error]),
    which the completeness half of [node_ok] excludes; the grant clause is
    excluded by [grant_ok_budget].  [rzb_never_refused_cfg] gives the same for
    every spurious-failure configuration ([Run.reaches_budget_refused_cfg_sub]).

    The rest of the file is YK15's lemmas that build a [realizes] node and that
    the usage path uses, restated over [rzb] with YK15's proofs: [rz_] is
    written [rzb_].  Each lemma that takes a [node_ok] also takes [grant_ok] for
    the same configuration. *)


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

(** The form [Cfg.transparent_nonalloc_no] has: the number as a literal, checked by
    [alloc_no_b]. *)
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
  intros c e st Hg H. destruct H as
    [ms model ms' model' Hh Hs Hst
    | ms model Hh Hs Hst
    | ms model Hh Hs Hst Hv
    | ms model fn n eff model' model'' evs Hh Hs Hst Hv Hn Hspec Hret Hh' Hmat
    | ms model fn n eff model' evs Hh Hs Hst Hv Hn Hspec Hret Hh' Hmat
    | ms model fn Hh Hs Hst Hv Hu
    | ms model x8 eff model' model'' evs Hh Hs Hspec Hh' Hmat
    | ms model x8 eff model' evs Hh Hs Hspec Hh' Hmat
    | ms model x8 eff model' evs code Hh Hs Hspec Hh' Hk
    | ms model x8 eff model' evs sig Hh Hs Hspec Hk
    | ms model x8 Hh Hs Hspec ].
  - exact (sstep_cfg_instr segs ACFG ms model ms' model' Hh Hs Hst).
  - exact (sstep_cfg_instr_fault segs ACFG ms model Hh Hs Hst).
  - exact (sstep_cfg_instr_unmodeled segs ACFG ms model Hh Hs Hst Hv).
  (* 727298f3: the three vDSO arms, which [sstep_cfg] mirrors with no filter premise *)
  - exact (sstep_cfg_vdso_call segs ACFG ms model fn n eff model' model'' evs Hh Hs Hst Hv Hn Hspec Hret Hh' Hmat).
  - exact (sstep_cfg_vdso_materialization_fault segs ACFG ms model fn n eff model' evs Hh Hs Hst Hv Hn Hspec Hret Hh' Hmat).
  - exact (sstep_cfg_vdso_unmodeled segs ACFG ms model fn Hh Hs Hst Hv Hu).
  - exact (sstep_cfg_syscall segs ACFG ms model x8 eff model' model'' evs Hh Hs Hspec
      (acfg_nonspurious (sys_input segs ms x8) model eff (Hg x8 Hs)) Hh' Hmat).
  - exact (sstep_cfg_syscall_materialization_fault segs ACFG ms model x8 eff model' evs Hh Hs Hspec
      (acfg_nonspurious (sys_input segs ms x8) model eff (Hg x8 Hs)) Hh' Hmat).
  - exact (sstep_cfg_exit segs ACFG ms model x8 eff model' evs code Hh Hs Hspec Hh' Hk).
  - exact (sstep_cfg_killed segs ACFG ms model x8 eff model' evs sig Hh Hs Hspec Hk).
  - exact (sstep_cfg_syscall_unmodeled segs ACFG ms model x8 Hh Hs Hspec).
Qed.
End g.

Section d.
Variable segs : list Segment.
Inductive rzb : config -> TSet -> Prop :=
| rzb_node : forall c (I : Type) (evs : I -> list event) (nx : I -> config)
(T : I -> TSet) (i0 : I),
node_ok segs c I evs nx ->
grant_ok c ->
(forall i, rzb (nx i) (T i)) ->
rzb c (t_alt (fun i => t_emit (evs i) (T i)))
| rzb_halt : forall c,
m_halted (cfg_model c) <> None ->
rzb c t_nil
| rzb_conseq : forall c T T',
rzb c T -> t_eq T T' -> rzb c T'
| rzb_silent : forall c (I : Type) (nx : I -> config) (T : I -> TSet) (i0 : I),
node_ok segs c I (fun _ => []) nx -> grant_ok c ->
(forall i, rzb (nx i) (T i)) -> rzb c (t_alt T).
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
  intros [ms model] I evs nx [_ [Hc _]] Hg [Hh Hb].
  assert (Herr : ~ sstep segs (mkCfg ms model) [] SError).
  { intros Hs.
    destruct (Hc [] SError (sstep_acfg_of_grant segs _ [] SError Hg Hs)) as (i & _ & Hbad).
    discriminate Hbad. }
  cbn [cfg_ms cfg_model] in Hh, Hb.
  (* 727298f3: the no-syscall branch of [Run.budget_refused_at] also holds a faulting vDSO call. *)
  destruct Hb as [(Hsvc & [(report & Hstep & Hmat)
                          | (Hun & fn & n & eff & model' & evs' & Hfn & Hn & Hspec & Hef & Hh' & Hmat)])
                 | (x8 & Hx8 & [Hgr | (eff & model' & evs' & Hspec & Hh' & Hmat)])].
  - exact (Herr (budget_fault_instr_sstep_error segs ms model report Hh Hsvc Hstep Hmat)).
  - exact (Herr (budget_fault_vdso_sstep_error segs ms model fn n eff model' evs' Hh Hsvc Hun Hfn Hn Hspec Hef Hh' Hmat)).
  - pose proof (grant_ok_budget segs (mkCfg ms model) x8 Hg Hx8) as Hg'.
    cbn [cfg_ms cfg_model] in Hg'. congruence.
  - exact (Herr (budget_fault_syscall_sstep_error segs ms model x8 eff model' evs' Hh Hx8 Hspec Hh' Hmat)).
Qed.

Lemma rzb_star_not_refused : forall c T, rzb segs c T ->
  forall tr c', star segs c tr c' -> ~ budget_refused_at segs c'.
Proof.
  intros c T H;
  induction H as [c I evs nx T i0 Hnode Hg Hcont IH | c Hh | c T T' H IH Heq | c I nx T i0 Hnode Hg Hcont IH];
  intros tr c' Hstar.
  - destruct (star_cases _ _ _ Hstar) as [-> | (e & c2 & tr2 & Hss & Hstar2)].
    + exact (node_not_refused c I evs nx Hnode Hg).
    + destruct (proj1 (proj2 Hnode) e (SNext c2) (sstep_acfg_of_grant segs c e (SNext c2) Hg Hss))
        as (i & _ & Heq2).
      injection Heq2 as ->. exact (IH i tr2 c' Hstar2).
  - destruct (star_cases _ _ _ Hstar) as [-> | (e & c2 & tr2 & Hss & Hstar2)].
    + intros [Hn _]. exact (Hh Hn).
    + exfalso. exact (Hh (sstep_running c e _ Hss)).
  - exact (IH tr c' Hstar).
  - destruct (star_cases _ _ _ Hstar) as [-> | (e & c2 & tr2 & Hss & Hstar2)].
    + exact (node_not_refused c I (fun _ => []) nx Hnode Hg).
    + destruct (proj1 (proj2 Hnode) e (SNext c2) (sstep_acfg_of_grant segs c e (SNext c2) Hg Hss))
        as (i & _ & Heq2).
      injection Heq2 as ->. exact (IH i tr2 c' Hstar2).
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
Local Notation rzb_silent := (rzb_silent segs).
Lemma rzb_emit_nil : forall c T, rzb c T -> rzb c (t_emit [] T).
Proof using.
intros c T H;
induction H as [c I evs nx T i0 Hnode Hg Hcont IH | c Hh | c T T' H IH Heq | c I nx T i0 Hnode Hg Hcont IH].
- eapply rzb_conseq; [exact (rzb_node c I evs nx T i0 Hnode Hg Hcont)|].
apply t_eq_sym. apply t_emit_nil_eq. exists i0. left. apply is_prefix_nil.
- eapply rzb_conseq; [exact (rzb_halt c Hh)|].
apply t_eq_sym. apply t_emit_nil_eq. reflexivity.
- eapply rzb_conseq; [exact IH|].
intro tr. unfold t_emit. split; intros [Hp | (tr' & -> & HT)];
[ left; exact Hp | right; exists tr'; split; [reflexivity | apply Heq; exact HT]
| left; exact Hp | right; exists tr'; split; [reflexivity | apply Heq; exact HT] ].
- eapply rzb_conseq; [exact (rzb_silent c I nx (fun i => t_emit [] (T i)) i0 Hnode Hg IH)|].
intro tr. unfold t_alt, t_emit. split.
+ intros [i [Hp | (tr' & -> & HT)]];
[ left; exact Hp | right; exists tr'; split; [reflexivity | exists i; exact HT] ].
+ intros [Hp | (tr' & -> & (i & HT))];
[ exists i0; left; exact Hp | exists i; right; exists tr'; split; [reflexivity | exact HT] ].
Qed.
Lemma rzb_silent1 : forall c c' T,
node_ok segs c unit (fun _ => []) (fun _ => c') ->
grant_ok c ->
rzb c' T ->
rzb c T.
Proof using.
intros c c' T Hnode Hg Hc.
apply (rzb_conseq c (t_alt (fun _ : unit => T))).
- apply (rzb_silent c unit (fun _ => c') (fun _ => T) tt Hnode Hg).
intros []; exact Hc.
- apply (t_alt_unit (fun _ : unit => T)).
Qed.
Lemma rzb_emit1 : forall c c' e T,
node_ok segs c unit (fun _ => e) (fun _ => c') ->
grant_ok c ->
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
grant_ok c ->
(forall i, rzb (nx i) T) ->
rzb c T.
Proof using.
intros c I nx i0 T Hnode Hg Hc.
apply (rzb_conseq c (t_alt (fun _ : I => T))).
- exact (rzb_silent c I nx (fun _ => T) i0 Hnode Hg Hc).
- intro tr. split.
+ intros [i Hi]. exact Hi.
+ intro HT. exists i0. exact HT.
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
eapply rzb_silent1; [apply node_instr; eassumption | apply grant_ok_instr; exact Hsvc | exact Hc].
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
- apply (node_ok_of_pnode segs); [eapply (transparent_exit segs); eassumption | exact (sys_rob_exit segs ms model x8 Hsvc Hx8) |]. split.
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
- exact (grant_ok_exit ms model x8 Hsvc Hx8).
- apply rzb_halt. cbn. discriminate.
Qed.
End d2.

(** ** The walk lifted to the run's segment list

    At LPS 727298f3 [Run.run_scfg_budget_refused] reads the run against
    [run_segments segs inp sp mbase] -- the binary's segments with the run's
    vDSO pair appended -- from the start configuration over that list.  A walk
    is built over the binary's own segments, so it is lifted as
    [RomStableK.run_init] lifts a [YK15.realizes] walk: every node's [node_ok]
    is RomStableK's, and [grant_ok] reads [ms_svc_pending] alone, which a
    change of the read-only backing or of the segment list leaves as it is. *)
Lemma grant_ok_cwrom : forall c r, grant_ok c -> grant_ok (cwrom c r).
Proof. intros [ms model] r H. exact H. Qed.

Section RzbWrom.
Variable segs : list Segment.
Hypothesis Hvi : vdso_image segs = None.
Theorem rzb_wrom : forall c T, rzb segs c T ->
  forall r, rom_ext (ms_rom (cfg_ms c)) r -> rzb segs (cwrom c r) T.
Proof.
  intros c T H;
  induction H as [c I evs nx T i0 Hn Hg Hc IH | c Hh | c T T' H IH Heq | c I nx T i0 Hn Hg Hc IH];
  intros r Hr.
  - apply (rzb_node segs (cwrom c r) I evs (fun i => cwrom (nx i) r) T i0).
    + eapply RomStableK.node_wrom; eauto.
    + apply grant_ok_cwrom. exact Hg.
    + intros i. apply IH. erewrite RomStableK.node_rom; eauto.
  - apply rzb_halt. exact Hh.
  - eapply rzb_conseq; [apply IH; exact Hr | exact Heq].
  - apply (rzb_silent segs (cwrom c r) I (fun i => cwrom (nx i) r) T i0).
    + eapply RomStableK.node_wrom; eauto.
    + apply grant_ok_cwrom. exact Hg.
    + intros i. apply IH. erewrite RomStableK.node_rom; eauto.
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
  induction H as [c I evs nx T i0 Hn Hg Hc IH | c Hh | c T T' H IH Heq | c I nx T i0 Hn Hg Hc IH].
  - apply (rzb_node (segs ++ tail) c I evs nx T i0); [| exact Hg | exact IH].
    eapply RomStableK.node_ok_app_tail; eauto.
  - apply rzb_halt. exact Hh.
  - eapply rzb_conseq; [exact IH | exact Heq].
  - apply (rzb_silent (segs ++ tail) c I nx T i0); [| exact Hg | exact IH].
    eapply RomStableK.node_ok_app_tail; eauto.
Qed.
End RzbAppTail.

(** A walk over the binary's own segments, from the binary's start, is a walk
    of the run's start over the run's segment list. *)
Theorem rzb_run_init : forall segs inp (sp mb : word) pc ph brk rnd lim T,
  vdso_image segs = None ->
  rzb segs (init_config segs pc ph sp brk mb rnd lim inp) T ->
  rzb (run_segments segs inp sp mb)
    (init_config (run_segments segs inp sp mb) pc ph sp brk mb rnd lim inp) T.
Proof.
  intros segs inp sp mb pc ph brk rnd lim T Hvi H.
  rewrite RomStableK.init_config_run_segments. unfold run_segments at 1.
  apply rzb_app_tail;
    [ intros s Hs; exact (RomStableK.vdso_segments_nx _ _ _ s Hs)
    | intros s Hs; exact (RomStableK.vdso_segments_nw _ _ _ s Hs)
    | exact Hvi |].
  apply (rzb_wrom segs Hvi); [exact H|].
  rewrite RomStableK.init_config_rom. apply RomStableK.rom_ext_run_segments.
Qed.
