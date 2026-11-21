(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YK18.v, with its module paths changed; srealizes_of_realizes removed and the exit case of srz_exit re-proved directly (srz_emit1 over sstep_exit), because this unit's realizes (YK15.v) has a cut at a budget refusal (a Theorem Labs lane's adaptation, a working branch). *)
(* Modified by Theorem Labs, 2026-11: made from Reusable/YK18.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW): srealizes keeps its name and its constructors, and its node constructor also asks for the budget mark's answer and the effect clause at the node (bnode_ok); the node lemmas that build a node take or derive that obligation, and the soundness for the budget premise is added at the end. *)
(* Theorem Labs, 2026-11: cut to the declarations the usage path at 16 GiB uses. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3, with libreac/fuzz_boxreg's port of its copy of this file (changed err_filtered_of_effects, srz_exit, node_munmap, node_not_refused, srealizes_star_not_refused, srealizes_never_refused_forced; added srz_silent_all, srealizes_realizes, srealizes_cut_free, srealizes_never_refused_run). *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require BudgetPremise.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YK16 YK0n YK0i YK0v YK15 YK0j YK0t YK1g.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.R Require Import Cfg.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.BudgetWit Require Rzb.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import RomBase.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require RomStableK.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Open Scope bv_scope.

(** * [srealizes] with the budget obligation at each node

    This twin of [Reusable/YK18.v] keeps the name [srealizes], so the walk
    files of [lib/BudgetWit/AW] are the released walk files with their imports
    renamed.  Its node constructor [srz_node] also asks, at the node [c], for
    [bnode_ok c]:

    - [budget_ok c]: if a system call is pending, the budget mark
      [Run.alloc_budget_refused_b] answers [false] for it at [c]'s model;
    - [err_filtered c]: every unfiltered error step from [c] is an [ACFG] step.

    With [node_ok]'s completeness half, the second clause excludes the two
    first-touch clauses of [Run.budget_refused_at], and the first excludes the
    grant clause ([srealizes_never_refused_cfg] at the end).  Both are read at
    the limit of the node's model, so an [srealizes] walk from
    [init_config ... lim inp] ties off the budget premise at [lim].

    Discharge: [bnode_of_grant] where no allocation call is pending (an
    instruction, or a system call off brk, mremap, mmap and mprotect);
    [bnode_of_grant_outcome] at an allocation call one of whose admitted
    outcomes is not a refusal, with the effect clause. *)

Section b.
Variable segs : list Segment.

Definition budget_ok (c : config) : Prop :=
  forall x8, ms_svc_pending (cfg_ms c) = Some x8 ->
    alloc_budget_refused_b (sys_input segs (cfg_ms c) x8) (cfg_model c) = false.

Definition err_filtered (c : config) : Prop :=
  forall e, sstep segs c e SError -> sstep_cfg segs ACFG c e SError.

Definition bnode_ok (c : config) : Prop := budget_ok c /\ err_filtered c.

Lemma bnode_of_grant : forall c, Rzb.grant_ok c -> bnode_ok c.
Proof.
  intros c Hg. split.
  - intros x8 Hx. exact (Rzb.grant_ok_budget segs c x8 Hg Hx).
  - intros e Hs. exact (Rzb.sstep_acfg_of_grant segs c e SError Hg Hs).
Qed.

Lemma bnode_none : forall ms model, ms_svc_pending ms = None -> bnode_ok (mkCfg ms model).
Proof. intros ms model Hsvc. apply bnode_of_grant. exact (Rzb.grant_ok_instr ms model Hsvc). Qed.

Lemma bnode_no : forall ms model x8 n, ms_svc_pending ms = Some x8 -> bv_unsigned x8 = n -> alloc_no_b n = false ->
  bnode_ok (mkCfg ms model).
Proof. intros ms model x8 n Hsvc Hn Ha. apply bnode_of_grant. exact (Rzb.grant_ok_no ms model x8 n Hsvc Hn Ha). Qed.

Lemma bnode_exit : forall ms model x8, ms_svc_pending ms = Some x8 -> is_exit_no x8 -> bnode_ok (mkCfg ms model).
Proof. intros ms model x8 Hsvc Hx. apply bnode_of_grant. exact (Rzb.grant_ok_exit ms model x8 Hsvc Hx). Qed.

(** Where the mark fires, every admitted outcome of brk, mmap and mprotect is a
    refusal (LPS [Checks.BudgetPremise]). *)
Lemma mark_false_of_grant_outcome : forall i m eff m' evs,
  In (bv_unsigned (in_sysno i)) [214; 222; 226]%Z ->
  syscall_spec i m (Ok eff m' evs) -> refusal_b i m (eff_ret eff) = false ->
  alloc_budget_refused_b i m = false.
Proof.
  intros i m eff m' evs Hno Hspec Hnr.
  destruct (alloc_budget_refused_b i m) eqn:Hm; [exfalso | reflexivity].
  destruct Hno as [E | [E | [E | []]]].
  - rewrite (BudgetPremise.brk_budget_refused_is_refusal i m eff m' evs (eq_sym E) Hm Hspec) in Hnr.
    discriminate Hnr.
  - rewrite (BudgetPremise.mmap_budget_refused_is_refusal i m eff m' evs (eq_sym E) Hm Hspec) in Hnr.
    discriminate Hnr.
  - rewrite (BudgetPremise.mprotect_budget_refused_is_refusal i m eff m' evs (eq_sym E) Hm Hspec) in Hnr.
    discriminate Hnr.
Qed.

Lemma err_filtered_of_effects : forall ms model,
  (forall x8 eff model' evs,
     ms_svc_pending ms = Some x8 ->
     syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
     m_halted model' = None ->
     materialize_model_accesses model' (syscall_effect_accesses eff) = None ->
     ~ spurious_refusal_cfg ACFG (sys_input segs ms x8) model eff) ->
  err_filtered (mkCfg ms model).
Proof.
  intros ms model Heff e Hs.
  inversion Hs; subst;
  first
    [ eapply sstep_cfg_instr_fault; eassumption
    | eapply sstep_cfg_instr_unmodeled; eassumption
    | eapply sstep_cfg_syscall_unmodeled; eassumption
    (* 727298f3: a vDSO call's two error arms, which [sstep_cfg] mirrors with no filter *)
    | eapply sstep_cfg_vdso_materialization_fault; eassumption
    | eapply sstep_cfg_vdso_unmodeled; eassumption
    | eapply sstep_cfg_syscall_materialization_fault;
        [ eassumption | eassumption | eassumption | eapply Heff; eassumption | eassumption | eassumption ] ].
Qed.

Lemma bnode_of_grant_outcome : forall ms model x8 eff model' evs,
  ms_svc_pending ms = Some x8 ->
  In (bv_unsigned x8) [214; 222; 226]%Z ->
  syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
  refusal_b (sys_input segs ms x8) model (eff_ret eff) = false ->
  (forall eff1 model1 evs1,
     syscall_spec (sys_input segs ms x8) model (Ok eff1 model1 evs1) ->
     m_halted model1 = None ->
     materialize_model_accesses model1 (syscall_effect_accesses eff1) = None ->
     ~ spurious_refusal_cfg ACFG (sys_input segs ms x8) model eff1) ->
  bnode_ok (mkCfg ms model).
Proof.
  intros ms model x8 eff model' evs Hsvc Hno Hspec Hnr Heff. split.
  - intros y8 Hy. cbn [cfg_ms cfg_model] in Hy |- *. rewrite Hsvc in Hy. injection Hy as <-.
    exact (mark_false_of_grant_outcome (sys_input segs ms x8) model eff model' evs Hno Hspec Hnr).
  - apply err_filtered_of_effects. intros y8 eff1 model1 evs1 Hy Hs1 Hh1 Hm1.
    rewrite Hsvc in Hy. injection Hy as <-. exact (Heff eff1 model1 evs1 Hs1 Hh1 Hm1).
Qed.

Inductive srealizes : config -> TSet -> Prop :=
| srz_node : forall c (I : Type) (evs : I -> list event) (nx : I -> config)
(T : I -> TSet) (i0 : I),
node_ok segs c I evs nx ->
bnode_ok c ->
(forall i, srealizes (nx i) (T i)) ->
srealizes c (t_alt (fun i => t_emit (evs i) (T i)))
| srz_halt : forall c,
m_halted (cfg_model c) <> None ->
srealizes c t_nil
| srz_spin : forall c,
False /\ to_spin segs (cfg_ms c) (cfg_model c) ->
m_halted (cfg_model c) = None ->
srealizes c t_nil
| srz_conseq : forall c T T',
srealizes c T -> t_eq T T' -> srealizes c T'.
Lemma srealizes_nonempty : forall c T, srealizes c T -> T [].
Proof.
intros c T H;
induction H as [c I evs nx T i0 Hnode Hb Hcont IH | c Hh
| c Hspin Hh | c T T' H IH Heq].
- exists i0. left. apply is_prefix_nil.
- reflexivity.
- reflexivity.
- apply Heq. exact IH.
Qed.
Lemma srz_silent1 : forall c c' T,
node_ok segs c unit (fun _ => []) (fun _ => c') ->
bnode_ok c ->
srealizes c' T ->
srealizes c T.
Proof.
intros c c' T Hnode Hb Hc.
apply (srz_conseq c (t_alt (fun _ : unit => t_emit [] T))).
- apply (srz_node c unit (fun _ => []) (fun _ => c') (fun _ => T) tt Hnode Hb).
intros []; exact Hc.
- eapply t_eq_trans;
[ apply (t_alt_unit (fun _ : unit => t_emit [] T))
| apply t_emit_nil_eq; eapply srealizes_nonempty; exact Hc ].
Qed.
Lemma srz_emit1 : forall c c' e T,
node_ok segs c unit (fun _ => e) (fun _ => c') ->
bnode_ok c ->
srealizes c' T ->
srealizes c (t_emit e T).
Proof.
intros c c' e T Hnode Hb Hc.
apply (srz_conseq c (t_alt (fun _ : unit => t_emit e T))).
- apply (srz_node c unit (fun _ => e) (fun _ => c') (fun _ => T) tt Hnode Hb).
intros []; exact Hc.
- apply t_alt_unit.
Qed.
Lemma srz_exit : forall ms model x8,
m_halted model = None ->
ms_svc_pending ms = Some x8 ->
is_exit_no x8 ->
srealizes (mkCfg ms model)
(t_exit (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)).
Proof.
intros ms model x8 Hh Hsvc Hx8.
set (code := bv_and (ms_gpr ms 0) (Z_to_bv 64 255)).
unfold t_exit.
eapply (srz_emit1 (mkCfg ms model) (mkCfg ms (with_halted code model))).
- apply node_ok_of_pnode; [eapply transparent_exit; eassumption | exact (sys_rob_exit segs ms model x8 Hsvc Hx8) |]. split.
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
- exact (bnode_exit ms model x8 Hsvc Hx8).
- apply srz_halt. cbn. discriminate.
Qed.
(* this twin's node constructor also asks for [bnode_ok] at the node *)
Lemma srz_silent_all : forall c (I : Type) (nx : I -> config) (T : TSet) (i0 : I),
  node_ok segs c I (fun _ => []) nx ->
  bnode_ok c ->
  (forall i, srealizes (nx i) T) ->
  srealizes c T.
Proof.
  intros c I nx T i0 Hnode Hb HT.
  assert (HT0 : T []) by (eapply srealizes_nonempty; apply (HT i0)).
  apply (srz_conseq c (t_alt (fun _ : I => t_emit [] T))).
  - apply (srz_node c I (fun _ => []) nx (fun _ => T) i0 Hnode Hb).
    intros i; exact (HT i).
  - intro tr. split.
    + intros [i Hi]. exact (proj1 (t_emit_nil_eq T HT0 tr) Hi).
    + intro H. exists i0. exact (proj2 (t_emit_nil_eq T HT0 tr) H).
Qed.
Lemma node_munmap : forall ms model x8,
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
(* LPS 727298f3: 215 joined alloc_mark_sysnos, so [transparent_nonalloc_no] no longer applies here.
   Under ACFG the ENOMEM answer is a spurious refusal, which is exactly [YK15.node_munmap_cfg]. *)
assert (mat : materialize_model_accesses
  (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)
  (syscall_effect_accesses (munmap_eff ms))
  = Some (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)).
{ apply materialize_model_accesses_no_lazy. exact (munmap_model_no_lazy _ _ _ Hlazy). }
exact (node_munmap_cfg segs ms model x8 _ Hh Hsvc Hno Hargs mat).
Qed.
(** A node with [bnode_ok] is not budget-refused. *)
Lemma node_not_refused : forall c I evs nx,
  node_ok segs c I evs nx -> bnode_ok c -> ~ budget_refused_at segs c.
Proof.
  intros [ms model] I evs nx [_ [Hc _]] [Hb He] [Hh Hr].
  assert (Herr : forall e, ~ sstep segs (mkCfg ms model) e SError).
  { intros e Hs. destruct (Hc e SError (He e Hs)) as (i & _ & Hbad). discriminate Hbad. }
  cbn [cfg_ms cfg_model] in Hh, Hr.
  (* 727298f3: the no-syscall branch of [Run.budget_refused_at] also holds a faulting vDSO
     call (as BudgetWit/Rzb.v). *)
  destruct Hr as [(Hsvc & [(report & Hstep & Hmat)
                          | (Hun & fn & n & eff & model' & evs' & Hfn & Hn & Hspec & Hef & Hh' & Hmat)])
                 | (x8 & Hx8 & [Hgr | (eff & model' & evs' & Hspec & Hh' & Hmat)])].
  - exact (Herr [] (budget_fault_instr_sstep_error segs ms model report Hh Hsvc Hstep Hmat)).
  - exact (Herr [] (budget_fault_vdso_sstep_error segs ms model fn n eff model' evs' Hh Hsvc Hun Hfn Hn Hspec Hef Hh' Hmat)).
  - pose proof (Hb x8 Hx8) as Hf. cbn [cfg_ms cfg_model] in Hf. congruence.
  - exact (Herr [] (budget_fault_syscall_sstep_error segs ms model x8 eff model' evs' Hh Hx8 Hspec Hh' Hmat)).
Qed.

Lemma srealizes_star_not_refused : forall c T, srealizes c T ->
  forall tr c', star_cfg segs ACFG c tr c' -> ~ budget_refused_at segs c'.
Proof.
  intros c T H;
  induction H as [c I evs nx T i0 Hnode Hb Hcont IH | c Hh | c Hspin Hh | c T T' H IH Heq];
  intros tr c' Hstar.
  - inversion Hstar; subst.
    + eapply node_not_refused; eassumption.
    + match goal with
      | Hss : sstep_cfg _ _ _ _ (SNext ?c2), Hst : star_cfg _ _ ?c2 _ _ |- _ =>
          destruct (proj1 (proj2 Hnode) _ _ Hss) as (i & _ & Heq2);
          injection Heq2 as ->; exact (IH i _ _ Hst)
      end.
  - inversion Hstar; subst.
    + intros [Hn _]. exact (Hh Hn).
    + exfalso.
      match goal with Hss : sstep_cfg _ _ _ _ (SNext _) |- _ => inversion Hss; subst end;
      cbn [cfg_model] in Hh; congruence.
  - destruct Hspin as [[] _].
  - exact (IH tr c' Hstar).
Qed.

Lemma star_cfg_up_acfg : forall cfg c tr c', cfg_le cfg ACFG ->
  star_cfg segs cfg c tr c' -> star_cfg segs ACFG c tr c'.
Proof.
  intros cfg c tr c' Hle H. induction H as [c0 | c1 evs c2 tr0 c3 Hss Hst IH].
  - apply star_cfg_refl.
  - eapply star_cfg_step; [exact (sstep_cfg_mono segs cfg ACFG _ _ _ Hle Hss) | exact IH].
Qed.

(** No configuration that a run from an [srealizes] configuration reaches,
    under a configuration below [ACFG], is budget-refused. *)
Theorem srealizes_never_refused_cfg : forall cfg c T, cfg_le cfg ACFG -> srealizes c T ->
  ~ reaches_budget_refused_cfg segs cfg c.
Proof.
  intros cfg c T Hle H (tr & c' & Hst & Hb).
  exact (srealizes_star_not_refused c T H tr c' (star_cfg_up_acfg cfg c tr c' Hle Hst) Hb).
Qed.

Corollary srealizes_never_refused_forced : forall c T, srealizes c T ->
  ~ reaches_budget_refused_cfg segs forced_only_cfg c.
Proof. intros c T H. exact (srealizes_never_refused_cfg forced_only_cfg c T (forced_only_cfg_least ACFG) H). Qed.
End b.

(** ** The walk lifted to the run's segment list

    At LPS 727298f3 [Run.run_scfg_budget_refused] reads the run against
    [run_segments segs inp sp mbase], from the start configuration over that
    list, while an [srealizes] walk is over the binary's own segments.  An
    [srealizes] walk is a [YK15.realizes] walk with no cut
    ([srealizes_realizes]) that is cut-free ([srealizes_star_not_refused]), so
    [RomStableK.cut_free_run_init] lifts its cut-freeness to the run. *)
Section lift.
Variable segs : list Segment.
Lemma srealizes_realizes : forall c T, srealizes segs c T -> YK15.realizes segs c T.
Proof.
  intros c T H;
  induction H as [c I evs nx T i0 Hnode Hb Hcont IH | c Hh | c Hspin Hh | c T T' H IH Heq].
  - exact (YK15.rz_node segs c I evs nx T i0 Hnode IH).
  - exact (YK15.rz_halt segs c Hh).
  - destruct Hspin as [[] _].
  - exact (YK15.rz_conseq segs c T T' IH Heq).
Qed.
Lemma srealizes_cut_free : forall c T, srealizes segs c T -> YK15.cut_free segs c.
Proof. intros c T H. exact (srealizes_star_not_refused segs c T H). Qed.
End lift.

(** No configuration of the run from [init_config] over the run's segment
    list is budget-refused, under any configuration below [ACFG]. *)
Theorem srealizes_never_refused_run : forall cfg segs pc ph (sp brk mb : word) rnd lim inp T,
  vdso_image segs = None -> cfg_le cfg ACFG ->
  srealizes segs (init_config segs pc ph sp brk mb rnd lim inp) T ->
  ~ run_scfg_budget_refused cfg (mkImage segs pc ph) lim (mkEntry sp brk mb rnd) inp.
Proof.
  intros cfg segs pc ph sp brk mb rnd lim inp T Hvi Hle H (tr & c' & Hst & Hb).
  exact (RomStableK.cut_free_run_init segs inp sp mb pc ph brk rnd lim T Hvi
           (srealizes_realizes segs _ T H) (srealizes_cut_free segs _ T H) tr c'
           (star_cfg_up_acfg _ cfg _ tr c' Hle Hst) Hb).
Qed.
