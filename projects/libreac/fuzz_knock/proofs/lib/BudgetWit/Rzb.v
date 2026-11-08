(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YK15.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from Reusable/YK15.v: the relation realizes without its cut and with a grant check at each node (rzb), its soundness for the budget premise, and YK15's node lemmas restated over rzb. *)
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YK16 YK0n YK0i YK0v YK02 YK1i YK15.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable.R Require Import Cfg.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Open Scope bv_scope.

(** * [rzb]: [YK15.realizes] without the cut, with a grant check at each node

    [YK15.realizes segs c T] ties a trace set to the one-step families of the
    configurations a run reaches.  Its constructor [rz_cut] lets an [AcfgMode]
    derivation stop at any configuration where the budget refuses memory, and a
    derivation records nothing about the configurations it passes, so no
    [realizes] proof says that a run is never refused.  [rzb] has the same
    constructors less [rz_cut], and its two node constructors ask, besides
    [node_ok], for [grant_ok segs c]: if a syscall is pending at [c], the budget
    mark [Run.alloc_budget_refused_b] answers [false] on it.

    [rzb_never_refused] reads a [MayFail] derivation, where [sstep_cfg] is
    [sstep] ([Run.sstep_cfg_may_fail]): no configuration the unfiltered run
    reaches is budget-refused.  The two first-touch clauses of
    [Run.budget_refused_at] are premises of an [SError] step
    ([Run.budget_fault_instr_sstep_error], [Run.budget_fault_syscall_sstep_error]),
    which the completeness half of [node_ok] excludes; the grant clause is the
    negation of [grant_ok].

    The rest of the file is YK15's lemmas that build a [realizes] node, restated
    over [rzb] with YK15's proofs: [rz_] is written [rzb_].  Each lemma that takes
    a [node_ok] also takes [grant_ok] for the same configuration.  214, 216, 222
    and 226 are the RISC-V Linux numbers of brk, mremap, mmap and mprotect
    ([Run.alloc_mark_sysnos]). *)

Section g.
Variable segs : list Segment.

(** If a syscall is pending at [c], the budget does not refuse it as a grant. *)
Definition grant_ok (c : config) : Prop :=
  forall x8, ms_svc_pending (cfg_ms c) = Some x8 ->
    alloc_budget_refused_b (sys_input segs (cfg_ms c) x8) (cfg_model c) = false.

Lemma grant_ok_instr : forall ms model,
  ms_svc_pending ms = None -> grant_ok (mkCfg ms model).
Proof.
  intros ms model Hsvc x8 Hx. cbn [cfg_ms] in Hx. rewrite Hsvc in Hx. discriminate Hx.
Qed.

Lemma grant_ok_nonalloc : forall ms model x8,
  ms_svc_pending ms = Some x8 -> ~ In (bv_unsigned x8) alloc_mark_sysnos ->
  grant_ok (mkCfg ms model).
Proof.
  intros ms model x8 Hsvc Hnin y Hy. cbn [cfg_ms cfg_model] in *.
  rewrite Hsvc in Hy. injection Hy as <-.
  apply alloc_budget_refused_b_outside. exact Hnin.
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
End g.

Section d.
Variable segs : list Segment.
Context {AM : AllocMode}.
Inductive rzb : config -> TSet -> Prop :=
| rzb_node : forall c (I : Type) (evs : I -> list event) (nx : I -> config)
(T : I -> TSet) (i0 : I),
@node_ok segs AM c I evs nx ->
grant_ok segs c ->
(forall i, rzb (nx i) (T i)) ->
rzb c (t_alt (fun i => t_emit (evs i) (T i)))
| rzb_halt : forall c,
m_halted (cfg_model c) <> None ->
rzb c t_nil
| rzb_conseq_m : forall c T T',
rzb c T -> (if @amf AM then (forall tr, T tr -> T' tr) else t_eq T T') -> rzb c T'
| rzb_silent : forall c (I : Type) (nx : I -> config) (T : I -> TSet) (i0 : I),
@node_ok segs AM c I (fun _ => []) nx -> grant_ok segs c ->
(forall i, rzb (nx i) (T i)) -> rzb c (t_alt T).
End d.

(** ** Soundness at [MayFail] *)
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

(** A [MayFail] node with the grant check is not budget-refused. *)
Lemma node_not_refused : forall c I evs nx,
  @node_ok segs MayFail c I evs nx -> grant_ok segs c -> ~ budget_refused_at segs c.
Proof.
  intros [ms model] I evs nx [_ Hc] Hg [Hh Hb].
  assert (Herr : ~ sstep segs (mkCfg ms model) [] SError).
  { intros Hs.
    destruct (Hc [] SError (proj1 (sstep_cfg_may_fail segs _ [] SError) Hs)) as (i & _ & Hbad).
    discriminate Hbad. }
  cbn [cfg_ms cfg_model] in Hh, Hb.
  destruct Hb as [(Hsvc & report & Hstep & Hmat)
                 | (x8 & Hx8 & [Hgr | (eff & model' & evs' & Hspec & Hh' & Hmat)])].
  - exact (Herr (budget_fault_instr_sstep_error segs ms model report Hh Hsvc Hstep Hmat)).
  - pose proof (Hg x8 Hx8) as Hg'. cbn [cfg_ms cfg_model] in Hg'. congruence.
  - exact (Herr (budget_fault_syscall_sstep_error segs ms model x8 eff model' evs' Hh Hx8 Hspec Hh' Hmat)).
Qed.

Lemma rzb_star_not_refused : forall c T, @rzb segs MayFail c T ->
  forall tr c', star segs c tr c' -> ~ budget_refused_at segs c'.
Proof.
  intros c T H;
  induction H as [c I evs nx T i0 Hnode Hg Hcont IH | c Hh | c T T' H IH Heq | c I nx T i0 Hnode Hg Hcont IH];
  intros tr c' Hstar.
  - destruct (star_cases _ _ _ Hstar) as [-> | (e & c2 & tr2 & Hss & Hstar2)].
    + exact (node_not_refused c I evs nx Hnode Hg).
    + destruct (proj2 Hnode e (SNext c2) (proj1 (sstep_cfg_may_fail segs c e (SNext c2)) Hss))
        as (i & _ & Heq2).
      injection Heq2 as ->. exact (IH i tr2 c' Hstar2).
  - destruct (star_cases _ _ _ Hstar) as [-> | (e & c2 & tr2 & Hss & Hstar2)].
    + intros [Hn _]. exact (Hh Hn).
    + exfalso. exact (Hh (sstep_running c e _ Hss)).
  - exact (IH tr c' Hstar).
  - destruct (star_cases _ _ _ Hstar) as [-> | (e & c2 & tr2 & Hss & Hstar2)].
    + exact (node_not_refused c I (fun _ => []) nx Hnode Hg).
    + destruct (proj2 Hnode e (SNext c2) (proj1 (sstep_cfg_may_fail segs c e (SNext c2)) Hss))
        as (i & _ & Heq2).
      injection Heq2 as ->. exact (IH i tr2 c' Hstar2).
Qed.

(** No configuration the run reaches from a [MayFail] [rzb] configuration is
    budget-refused. *)
Theorem rzb_never_refused : forall c T, @rzb segs MayFail c T ->
  ~ reaches_budget_refused segs c.
Proof.
  intros c T H (tr & c' & Hstar & Hb). exact (rzb_star_not_refused c T H tr c' Hstar Hb).
Qed.

(** ...and so under every spurious-failure configuration
    ([Run.reaches_budget_refused_cfg_sub]). *)
Theorem rzb_never_refused_cfg : forall cfg c T, @rzb segs MayFail c T ->
  ~ reaches_budget_refused_cfg segs cfg c.
Proof.
  intros cfg c T H Hr. exact (rzb_never_refused c T H (reaches_budget_refused_cfg_sub segs cfg c Hr)).
Qed.
End s.

(** ** YK15's node lemmas over [rzb] *)
Section d2.
Variable segs : list Segment.
Context {AM : AllocMode}.
Local Notation node_ok := (@node_ok segs AM).
Local Notation rzb := (@rzb segs AM).
Local Notation rzb_node := (@rzb_node segs AM).
Local Notation rzb_halt := (@rzb_halt segs AM).
Local Notation rzb_conseq_m := (@rzb_conseq_m segs AM).
Local Notation rzb_silent := (@rzb_silent segs AM).
Local Notation node_ok_of_pnode := (@node_ok_of_pnode segs AM).
Local Notation transparent_exit := (@transparent_exit segs AM).
Lemma rzb_conseq : forall c T T', rzb c T -> t_eq T T' -> rzb c T'.
Proof using.
intros c T T' H Heq. apply (rzb_conseq_m c T T' H).
destruct (@amf AM); [intros tr HT; apply Heq; exact HT | exact Heq].
Qed.
Lemma rzb_weak : forall c T T', @amf AM = true -> rzb c T -> (forall tr, T tr -> T' tr) -> rzb c T'.
Proof using.
intros c T T' Hm H Hs. apply (rzb_conseq_m c T T' H). rewrite Hm. exact Hs.
Qed.
Lemma rzb_emit_nil : forall c T, rzb c T -> rzb c (t_emit [] T).
Proof using.
intros c T H;
induction H as [c I evs nx T i0 Hnode Hg Hcont IH | c Hh | c T T' H IH Heq | c I nx T i0 Hnode Hg Hcont IH].
- eapply rzb_conseq; [exact (rzb_node c I evs nx T i0 Hnode Hg Hcont)|].
apply t_eq_sym. apply t_emit_nil_eq. exists i0. left. apply is_prefix_nil.
- eapply rzb_conseq; [exact (rzb_halt c Hh)|].
apply t_eq_sym. apply t_emit_nil_eq. reflexivity.
- apply (rzb_conseq_m c (t_emit [] T) (t_emit [] T') IH). revert Heq. destruct (@amf AM); intros Heq.
+ intro tr. unfold t_emit. intros [Hp | (tr' & -> & HT)];
[ left; exact Hp | right; exists tr'; split; [reflexivity | apply Heq; exact HT] ].
+ intro tr. unfold t_emit. split; intros [Hp | (tr' & -> & HT)];
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
node_ok c unit (fun _ => []) (fun _ => c') ->
grant_ok segs c ->
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
node_ok c unit (fun _ => e) (fun _ => c') ->
grant_ok segs c ->
rzb c' T ->
rzb c (t_emit e T).
Proof.
intros c c' e T Hnode Hg Hc.
apply (rzb_conseq c (t_alt (fun _ : unit => t_emit e T))).
- apply (rzb_node c unit (fun _ => e) (fun _ => c') (fun _ => T) tt Hnode Hg).
intros []; exact Hc.
- apply t_alt_unit.
Qed.
Lemma rzb_alt2 : forall c (IA IB : Type) (nx : IA + IB -> config) (A B : TSet)
(a0 : IA) (b0 : IB),
node_ok c (IA + IB) (fun _ => []) nx ->
grant_ok segs c ->
(forall i, rzb (nx (inl i)) A) ->
(forall i, rzb (nx (inr i)) B) ->
rzb c (t_alt2 A B).
Proof using.
intros c IA IB nx A B a0 b0 Hnode Hg HA HB.
apply (rzb_conseq c
(t_alt (fun i : IA + IB => match i with inl _ => A | inr _ => B end))).
- apply (rzb_silent c (IA + IB) nx
(fun i => match i with inl _ => A | inr _ => B end) (inl a0) Hnode Hg).
intros [i|i]; [apply HA | apply HB].
- intro tr. unfold t_alt2. split.
+ intros [[i|i] Hi]; [left; exact Hi | right; exact Hi].
+ intros [H | H]; [exists (inl a0); exact H | exists (inr b0); exact H].
Qed.
Lemma rzb_silent_allI : forall c (I : Type) (nx : I -> config) (i0 : I) T,
node_ok c I (fun _ => []) nx ->
grant_ok segs c ->
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
- apply node_ok_of_pnode; [eapply transparent_exit; eassumption|]. split.
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
- exact (grant_ok_exit segs ms model x8 Hsvc Hx8).
- apply rzb_halt. cbn. discriminate.
Qed.
End d2.
