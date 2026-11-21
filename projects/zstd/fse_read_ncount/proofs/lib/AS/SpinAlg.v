(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (adds srz_silent_all: a node whose answers are all silent srealizes T when every successor does; node_munmap re-proved through munmap_node_cfg, as munmap (215) is now an injected syscall; srz_node takes RomBase.sys_rob, so srz_silent1 and srz_silent_all take it too and the inductions over srealizes and realizes name it; imports RomBase). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Cfg.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AS Require Import
SimInv ExitSim CatSim MmapSim ShapeAlg DivergeSim.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AS Require Import RomBase.
Import ListNotations.
Open Scope bv_scope.
Section WithSegs.
Variable segs : list Segment.
Inductive srealizes : config -> TSet -> Prop :=
| srz_node : forall c (I : Type) (evs : I -> list event) (nx : I -> config)
(T : I -> TSet) (i0 : I),
node_ok segs c I evs nx ->
    sys_rob segs c ->   (* LPS 727298f3: see [ShapeAlg.rz_node] *)
(forall i, srealizes (nx i) (T i)) ->
srealizes c (t_alt (fun i => t_emit (evs i) (T i)))
| srz_halt : forall c,
m_halted (cfg_model c) <> None ->
srealizes c t_nil
| srz_conseq : forall c T T',
srealizes c T -> t_eq T T' -> srealizes c T'.
#[using="Type"] Lemma srealizes_of_realizes : forall c T,
realizes segs c T -> srealizes c T.
Proof.
intros c T H;
    induction H as [c I evs nx T i0 Hnode Hrob Hcont IH | c Hh | c T T' H IH Heq].
  - exact (srz_node c I evs nx T i0 Hnode Hrob IH).
- exact (srz_halt c Hh).
- exact (srz_conseq c T T' IH Heq).
Qed.
#[using="Type"] Lemma realizes_of_srealizes : forall c T,
srealizes c T -> realizes segs c T.
Proof.
intros c T H;
    induction H as [c I evs nx T i0 Hnode Hrob Hcont IH | c Hh | c T T' H IH Heq].
  - exact (rz_node segs c I evs nx T i0 Hnode Hrob IH).
- exact (rz_halt segs c Hh).
- exact (rz_conseq segs c T T' IH Heq).
Qed.
#[using="Type"] Lemma srealizes_nonempty : forall c T, srealizes c T -> T [].
Proof.
intros c T H;
    induction H as [c I evs nx T i0 Hnode Hrob Hcont IH | c Hh
| c T T' H IH Heq].
- exists i0. left. apply is_prefix_nil.
- reflexivity.
- apply Heq. exact IH.
Qed.
#[using="Type"] Lemma srealizes_pclosed : forall c T, srealizes c T ->
forall tr tr', T tr -> is_prefix tr' tr -> T tr'.
Proof.
intros c T H;
    induction H as [c I evs nx T i0 Hnode Hrob Hcont IH | c Hh
| c T T' H IH Heq];
intros tr tr' HT Hp.
- destruct HT as [i [Hpre | (tr0 & -> & HT0)]]; exists i.
+ left. eapply is_prefix_trans; eauto.
+ apply is_prefix_app_split in Hp as [Hp | (tr0' & -> & Hp)].
* left. exact Hp.
* right. exists tr0'. split; [reflexivity | eapply IH; eauto].
- unfold t_nil in *. subst tr. apply is_prefix_nil_r in Hp. exact Hp.
- apply Heq. eapply IH; [apply Heq; exact HT | exact Hp].
Qed.
#[using="Type"] Lemma srealizes_star_only : forall c T, srealizes c T ->
forall tr c', star_cfg segs ACFG c tr c' -> T tr.
Proof.
intros c T H;
    induction H as [c I evs nx T i0 Hnode Hrob Hcont IH | c Hh
| c T T' H IH Heq];
intros tr c' Hstar.
- inversion Hstar as [|c1 e c2 tr2 c3 Hss Hstar2]; subst.
+ exists i0. left. apply is_prefix_nil.
+ destruct Hnode as [_ Hsound].
destruct (Hsound e (SNext c2) Hss) as (i & -> & Heq2).
inversion Heq2; subst c2.
exists i. right. exists tr2.
split; [reflexivity | eapply IH; exact Hstar2].
- destruct (star_cfg_halted_nil segs ACFG c tr c' Hh Hstar) as [-> _]. reflexivity.
- apply Heq. eapply IH; exact Hstar.
Qed.
#[using="Type"] Lemma srealizes_admits : forall c T, srealizes c T ->
forall tr, T tr -> obs_trace_cfg segs ACFG c tr.
Proof.
intros c T H;
    induction H as [c I evs nx T i0 Hnode Hrob Hcont IH | c Hh
| c T T' H IH Heq];
intros tr HT.
- destruct Hnode as [Hcomp _].
destruct HT as [i [Hpre | (tr0 & -> & HT0)]].
+ exists (evs i), (nx i). split; [apply star_cfg_one; apply Hcomp | exact Hpre].
+ destruct (IH i tr0 HT0) as (tr'' & c'' & Hstar & Hp).
exists (evs i ++ tr''), c''.
split; [eapply star_cfg_step; [apply Hcomp | exact Hstar]
| apply is_prefix_app_mono; exact Hp].
- unfold t_nil in HT; subst tr. apply obs_trace_cfg_nil.
- apply IH. apply Heq. exact HT.
Qed.
#[using="Type"] Theorem srealizes_obs_iff : forall c T, srealizes c T ->
forall tr, obs_trace_cfg segs ACFG c tr <-> T tr.
Proof.
intros c T H tr. split.
- intros (tr' & c' & Hstar & Hp).
eapply srealizes_pclosed;
[exact H | eapply srealizes_star_only; eauto | exact Hp].
- apply srealizes_admits; exact H.
Qed.
#[using="Type"] Lemma srealizes_step : forall c T e c',
srealizes c T -> sstep_cfg segs ACFG c e (SNext c') -> exists T', srealizes c' T'.
Proof.
intros c T e c' H; revert e c';
    induction H as [c I evs nx T i0 Hnode Hrob Hcont IH | c Hh
| c T T' H IH Heq];
intros e c' Hss.
- destruct Hnode as [_ Hsound].
destruct (Hsound e (SNext c') Hss) as (i & _ & Heq2).
inversion Heq2; subst c'. exists (T i). apply Hcont.
- exfalso. apply Hh. eapply sstep_cfg_halted_none; exact Hss.
- eapply IH; exact Hss.
Qed.
#[using="Type"] Lemma srealizes_no_sserror : forall c T e,
srealizes c T -> ~ sstep_cfg segs ACFG c e SError.
Proof.
intros c T e H; revert e;
    induction H as [c I evs nx T i0 Hnode Hrob Hcont IH | c Hh
| c T T' H IH Heq];
intros e Hss.
- destruct Hnode as [_ Hsound].
destruct (Hsound e SError Hss) as (i & _ & Hbad). discriminate.
- apply Hh. eapply sstep_cfg_halted_none; exact Hss.
- eapply IH; exact Hss.
Qed.
Definition srz_path (c : config) : Prop := exists T, srealizes c T.
#[using="Type"] Lemma srz_path_star : forall c tr c',
star_cfg segs ACFG c tr c' -> srz_path c -> srz_path c'.
Proof.
intros c tr c' Hstar. induction Hstar as [c | c1 evs c2 tr c3 Hss Hstar IH]; intros Hp; [exact Hp|].
apply IH. destruct Hp as [T HT]. exact (srealizes_step c1 T evs c2 HT Hss).
Qed.
#[using="Type"] Theorem srealizes_no_error : forall c T,
srealizes c T -> ~ reaches_error_cfg segs ACFG c.
Proof.
intros c T H (tr & c' & evs & Hstar & Herr).
destruct (srz_path_star c tr c' Hstar (ex_intro _ T H)) as [T' HT'].
exact (srealizes_no_sserror c' T' evs HT' Herr).
Qed.
#[using="Type"] Lemma srz_silent1 : forall c c' T,
  node_ok segs c unit (fun _ => []) (fun _ => c') -> sys_rob segs c ->
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
#[using="Type"] Lemma srz_exit : forall ms model x8,
m_halted model = None ->
ms_svc_pending ms = Some x8 ->
is_exit_no x8 ->
srealizes (mkCfg ms model)
(t_exit (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)).
Proof.
intros ms model x8 Hh Hsvc Hx8.
apply srealizes_of_realizes. apply (rz_exit segs ms model x8); assumption.
Qed.
Lemma srz_silent_all : forall c (I : Type) (nx : I -> config) (T : TSet) (i0 : I),
  node_ok segs c I (fun _ => []) nx -> sys_rob segs c ->
  (forall i, srealizes (nx i) T) ->
  srealizes c T.
Proof.
  intros c I nx T i0 Hnode Hrob HT.
  assert (HT0 : T []) by (eapply srealizes_nonempty; apply (HT i0)).
  apply (srz_conseq c (t_alt (fun _ : I => t_emit [] T))).
  - apply (srz_node c I (fun _ => []) nx (fun _ => T) i0 Hnode Hrob).
    intros i; exact (HT i).
  - intro tr. split.
    + intros [i Hi]. exact (proj1 (t_emit_nil_eq T HT0 tr) Hi).
    + intro H. exists i0. exact (proj2 (t_emit_nil_eq T HT0 tr) H).
Qed.

#[using="Type"] Lemma node_munmap : forall ms model x8,
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
(* 215 (munmap) joined Run.injected_table at #38, so [alloc_no_b 215] is now TRUE and the
   old route through [transparent_nonalloc_no ... ; reflexivity] cannot close: the goal
   [alloc_no_b 215 = false] is FALSE at this model, not merely unproved.  The right route
   is the one this unit's own AS/MmapSim.v:296 already takes -- [munmap_node_cfg] discharges
   [injected_family_off ACFG (sys_input segs ms x8) = true] at :320 and goes through
   [node_chk_grant_cfg], i.e. the family-OFF side.  zstd/simple_decompress's AS/SpinAlg.v:393
   states this proof verbatim and compiled there.  AS/MmapSim.v builds in this unit on the
   same test. *)
intros ms model x8 Hh Hlazy Hsvc Hno Hargs.
exact (munmap_node_cfg segs ms model x8 Hh Hlazy Hsvc Hno Hargs).
Qed.
End WithSegs.
