(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by gabelogan195, 2026-11: the spinning leaf srz_cfg_spin removed from srealizes_cfg, with the lemma srz_cfg_spinning and the spinning case of each lemma that inducts on srealizes_cfg, so that a derivation of srealizes_cfg is a well-founded tree of steps ending in halted configurations. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import
  SimInv ExitSim CatSim MmapSim ShapeAlg DivergeSim LazyFrame SpinAlg.
Unset Nia Cache.  (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache.

(* [comment removed for export] *)
Definition CFG : SpuriousCfg := mkSpuriousCfg false true true true true true.

(* [comment removed for export] *)
Lemma gpr0_adv_apply : forall ms eff, ms_gpr (advance_past_svc (apply_effect ms eff)) 0 = eff_ret eff.
Proof.
  intros ms eff. unfold ms_gpr, advance_past_svc, apply_effect, set_reg. cbn [ms_regs].
  match goal with |- context [if ?b then _ else _] => replace b with false by reflexivity end.
  cbn [ms_regs]. unfold reg_get.
  match goal with |- context [bvmap_get ?k (bvmap_set ?k' _ _)] => replace k with k' by (apply bv_eq; reflexivity) end.
  rewrite bvmap_get_set_same. reflexivity.
Qed.

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)

Definition node_ok_cfg (c : config) (I : Type)
    (evs : I -> list event) (nx : I -> config) : Prop :=
  (forall i, sstep_cfg segs CFG c (evs i) (SNext (nx i)))
  /\ (forall e st, sstep_cfg segs CFG c e st -> exists i, e = evs i /\ st = SNext (nx i)).

Inductive srealizes_cfg : config -> TSet -> Prop :=
| srz_cfg_node : forall c (I : Type) (evs : I -> list event) (nx : I -> config)
                        (T : I -> TSet) (i0 : I),
    node_ok_cfg c I evs nx ->
    (forall i, srealizes_cfg (nx i) (T i)) ->
    srealizes_cfg c (t_alt (fun i => t_emit (evs i) (T i)))
| srz_cfg_halt : forall c,
    m_halted (cfg_model c) <> None ->
    srealizes_cfg c t_nil
| srz_cfg_conseq : forall c T T',
    srealizes_cfg c T -> t_eq T T' -> srealizes_cfg c T'.

(* [comment removed for export] *)

Lemma srealizes_cfg_nonempty : forall c T, srealizes_cfg c T -> T [].
Proof.
  intros c T H;
    induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq].
  - exists i0. left. apply is_prefix_nil.
  - reflexivity.
  - apply Heq. exact IH.
Qed.

Lemma srealizes_cfg_pclosed : forall c T, srealizes_cfg c T ->
  forall tr tr', T tr -> is_prefix tr' tr -> T tr'.
Proof.
  intros c T H;
    induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq];
    intros tr tr' HT Hp.
  - destruct HT as [i [Hpre | (tr0 & -> & HT0)]]; exists i.
    + left. eapply is_prefix_trans; eauto.
    + apply is_prefix_app_split in Hp as [Hp | (tr0' & -> & Hp)].
      * left. exact Hp.
      * right. exists tr0'. split; [reflexivity | eapply IH; eauto].
  - unfold t_nil in *. subst tr. apply is_prefix_nil_r in Hp. exact Hp.
  - apply Heq. eapply IH; [apply Heq; exact HT | exact Hp].
Qed.

(* [comment removed for export] *)

Lemma sstep_cfg_halted_none : forall c e st,
  sstep_cfg segs CFG c e st -> m_halted (cfg_model c) = None.
Proof. intros c e st H; inversion H; subst; cbn; assumption. Qed.

Lemma star_cfg_halted_nil : forall c tr c',
  m_halted (cfg_model c) <> None -> star_cfg segs CFG c tr c' -> tr = [].
Proof.
  intros c tr c' Hh H. destruct H as [c | c1 evs c2 tr c3 Hss _]; [reflexivity|].
  exfalso. apply Hh. exact (sstep_cfg_halted_none _ _ _ Hss).
Qed.

Lemma obs_trace_cfg_nil : forall c, obs_trace_cfg segs CFG c [].
Proof. intros c. exists [], c. split; [apply star_cfg_refl | apply is_prefix_nil]. Qed.

Lemma star_cfg_one : forall c evs c', sstep_cfg segs CFG c evs (SNext c') -> star_cfg segs CFG c evs c'.
Proof.
  intros c evs c' H. rewrite <- (app_nil_r evs).
  econstructor; [exact H | apply star_cfg_refl].
Qed.

Lemma star_cfg_inv (Inv : config -> Prop)
  (Hstep : forall c evs c', Inv c -> sstep_cfg segs CFG c evs (SNext c') -> Inv c') :
  forall c tr c', Inv c -> star_cfg segs CFG c tr c' -> Inv c'.
Proof.
  intros c tr c' HInv Hstar. induction Hstar; [exact HInv|].
  apply IHHstar. eapply Hstep; eauto.
Qed.

(* [comment removed for export] *)
Lemma spin_star_cfg_nil : forall ms model tr c',
  to_spin segs ms model -> m_halted model = None ->
  star_cfg segs CFG (mkCfg ms model) tr c' -> tr = [].
Proof.
  intros ms model tr c' Hspin Hh Hstar.
  exact (spin_star_nil segs ms model tr c' Hspin Hh (star_cfg_sub segs CFG _ _ _ Hstar)).
Qed.

(* [comment removed for export] *)

Lemma srealizes_cfg_star_only : forall c T, srealizes_cfg c T ->
  forall tr c', star_cfg segs CFG c tr c' -> T tr.
Proof.
  intros c T H;
    induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq];
    intros tr c' Hstar.
  - inversion Hstar as [|c1 e c2 tr2 c3 Hss Hstar2]; subst.
    + exists i0. left. apply is_prefix_nil.
    + destruct Hnode as [_ Hsound].
      destruct (Hsound e (SNext c2) Hss) as (i & -> & Heq2).
      inversion Heq2; subst c2.
      exists i. right. exists tr2. split; [reflexivity | eapply IH; exact Hstar2].
  - rewrite (star_cfg_halted_nil c tr c' Hh Hstar). reflexivity.
  - apply Heq. eapply IH; exact Hstar.
Qed.

Lemma srealizes_cfg_admits : forall c T, srealizes_cfg c T ->
  forall tr, T tr -> obs_trace_cfg segs CFG c tr.
Proof.
  intros c T H;
    induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq];
    intros tr HT.
  - destruct Hnode as [Hcomp _].
    destruct HT as [i [Hpre | (tr0 & -> & HT0)]].
    + exists (evs i), (nx i). split; [apply star_cfg_one; apply Hcomp | exact Hpre].
    + destruct (IH i tr0 HT0) as (tr'' & c'' & Hstar & Hp).
      exists (evs i ++ tr''), c''.
      split; [eapply star_cfg_step; [apply Hcomp | exact Hstar] | apply is_prefix_app_mono; exact Hp].
  - unfold t_nil in HT; subst tr. apply obs_trace_cfg_nil.
  - apply IH. apply Heq. exact HT.
Qed.

(* [comment removed for export] *)
Theorem srealizes_cfg_obs_iff : forall c T, srealizes_cfg c T ->
  forall tr, obs_trace_cfg segs CFG c tr <-> T tr.
Proof.
  intros c T H tr. split.
  - intros (tr' & c' & Hstar & Hp).
    eapply srealizes_cfg_pclosed; [exact H | eapply srealizes_cfg_star_only; eauto | exact Hp].
  - apply srealizes_cfg_admits; exact H.
Qed.

Lemma srealizes_cfg_step : forall c T e c',
  srealizes_cfg c T -> sstep_cfg segs CFG c e (SNext c') -> exists T', srealizes_cfg c' T'.
Proof.
  intros c T e c' H; revert e c';
    induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq];
    intros e c' Hss.
  - destruct Hnode as [_ Hsound].
    destruct (Hsound e (SNext c') Hss) as (i & _ & Heq2).
    inversion Heq2; subst c'. exists (T i). apply Hcont.
  - exfalso. apply Hh. eapply sstep_cfg_halted_none; exact Hss.
  - eapply IH; exact Hss.
Qed.

Lemma srealizes_cfg_no_sserror : forall c T e,
  srealizes_cfg c T -> ~ sstep_cfg segs CFG c e SError.
Proof.
  intros c T e H; revert e;
    induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq];
    intros e Hss.
  - destruct Hnode as [_ Hsound].
    destruct (Hsound e SError Hss) as (i & _ & Hbad). discriminate.
  - apply Hh. eapply sstep_cfg_halted_none; exact Hss.
  - eapply IH; exact Hss.
Qed.

Definition srz_cfg_path (c : config) : Prop := exists T, srealizes_cfg c T.

(* [comment removed for export] *)
Theorem srealizes_cfg_no_error : forall c T,
  srealizes_cfg c T -> ~ reaches_error_cfg segs CFG c.
Proof.
  intros c T H (tr & c' & evs & Hstar & Hss).
  destruct (star_cfg_inv srz_cfg_path
              ltac:(intros c1 e c2 (T1 & H1) Hs; eapply srealizes_cfg_step; eauto)
              c tr c' (ex_intro _ T H) Hstar) as (T' & H').
  exact (srealizes_cfg_no_sserror c' T' evs H' Hss).
Qed.

Corollary srealizes_cfg_no_unmodeled : forall c T,
  srealizes_cfg c T -> ~ reaches_unmodeled_cfg segs CFG c.
Proof.
  intros c T H Hun. apply (srealizes_cfg_no_error c T H).
  exact (reaches_unmodeled_cfg_reaches_error_cfg segs CFG c Hun).
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition nonalloc (c : config) : Prop :=
  forall x8, ms_svc_pending (cfg_ms c) = Some x8 ->
    injected_family_off CFG (sys_input segs (cfg_ms c) x8) = false.

Lemma nonalloc_instr : forall ms model, ms_svc_pending ms = None -> nonalloc (mkCfg ms model).
Proof. intros ms model H x8 H'. cbn [cfg_ms] in H'. congruence. Qed.

(* [comment removed for export] *)
Definition alloc_no (no : Z) : bool :=
  match injected_arm no with
  | Some a => negb (family_may_fail CFG (ia_family a))
  | None => false
  end.

Lemma injected_family_off_alloc_no : forall ms x8,
  injected_family_off CFG (sys_input segs ms x8) = alloc_no (bv_unsigned x8).
Proof. reflexivity. Qed.

Lemma nonalloc_no : forall ms model x8,
  ms_svc_pending ms = Some x8 -> alloc_no (bv_unsigned x8) = false -> nonalloc (mkCfg ms model).
Proof.
  intros ms model x8 H Hno y H'. cbn [cfg_ms] in *. rewrite H in H'. injection H' as <-.
  rewrite injected_family_off_alloc_no. exact Hno.
Qed.

(* [comment removed for export] *)
Lemma sstep_cfg_of_nonalloc : forall c e st,
  nonalloc c -> sstep segs c e st -> sstep_cfg segs CFG c e st.
Proof.
  intros c e st Hna H. destruct H as
    [ms model ms' model' Hh Hsvc Hacc
    | ms model Hh Hsvc Hacc
    | ms model Hh Hsvc Hacc
    | ms model x8 eff model' model'' evs Hh Hsvc Hspec Hh' Hmat
    | ms model x8 eff model' evs Hh Hsvc Hspec Hh' Hmat
    | ms model x8 eff model' evs code Hh Hsvc Hspec Hh' Hk
    | ms model x8 eff model' evs sig Hh Hsvc Hspec Hk
    | ms model x8 Hh Hsvc Hspec].
  - eapply sstep_cfg_instr; eassumption.
  - eapply sstep_cfg_instr_fault; eassumption.
  - eapply sstep_cfg_instr_unmodeled; eassumption.
  - eapply sstep_cfg_syscall; try eassumption.
    intros (Hoff & _ & _). specialize (Hna x8 Hsvc). cbn [cfg_ms] in Hna. rewrite Hna in Hoff. discriminate.
  - eapply sstep_cfg_syscall_materialization_fault; try eassumption.
    intros (Hoff & _ & _). specialize (Hna x8 Hsvc). cbn [cfg_ms] in Hna. rewrite Hna in Hoff. discriminate.
  - eapply sstep_cfg_exit; eassumption.
  - eapply sstep_cfg_killed; eassumption.
  - eapply sstep_cfg_syscall_unmodeled; eassumption.
Qed.

Lemma node_ok_cfg_of_nonalloc : forall c I evs nx,
  nonalloc c -> node_ok segs c I evs nx -> node_ok_cfg c I evs nx.
Proof.
  intros c I evs nx Hna [Hc Hs]. split.
  - intros i. apply sstep_cfg_of_nonalloc; [exact Hna | apply Hc].
  - intros e st H. apply Hs. exact (sstep_cfg_sub segs CFG c e st H).
Qed.

(* [comment removed for export] *)
Definition forced_refusals (c : config) : Prop :=
  forall x8, ms_svc_pending (cfg_ms c) = Some x8 ->
    forall eff m' evs, syscall_spec (sys_input segs (cfg_ms c) x8) (cfg_model c) (Ok eff m' evs) ->
      refusal_b (sys_input segs (cfg_ms c) x8) (cfg_model c) (eff_ret eff) = true.

Lemma sstep_cfg_of_forced : forall c e st,
  forced_refusals c -> sstep segs c e st -> sstep_cfg segs CFG c e st.
Proof.
  intros c e st Hfo H. destruct H as
    [ms model ms' model' Hh Hsvc Hacc
    | ms model Hh Hsvc Hacc
    | ms model Hh Hsvc Hacc
    | ms model x8 eff model' model'' evs Hh Hsvc Hspec Hh' Hmat
    | ms model x8 eff model' evs Hh Hsvc Hspec Hh' Hmat
    | ms model x8 eff model' evs code Hh Hsvc Hspec Hh' Hk
    | ms model x8 eff model' evs sig Hh Hsvc Hspec Hk
    | ms model x8 Hh Hsvc Hspec].
  - eapply sstep_cfg_instr; eassumption.
  - eapply sstep_cfg_instr_fault; eassumption.
  - eapply sstep_cfg_instr_unmodeled; eassumption.
  - eapply sstep_cfg_syscall; try eassumption.
    intros (_ & _ & (eff' & m2 & evs2 & Hs2 & Hr2)).
    pose proof (Hfo x8 Hsvc eff' m2 evs2 Hs2) as Hr. cbn [cfg_ms cfg_model] in Hr. congruence.
  - eapply sstep_cfg_syscall_materialization_fault; try eassumption.
    intros (_ & _ & (eff' & m2 & evs2 & Hs2 & Hr2)).
    pose proof (Hfo x8 Hsvc eff' m2 evs2 Hs2) as Hr. cbn [cfg_ms cfg_model] in Hr. congruence.
  - eapply sstep_cfg_exit; eassumption.
  - eapply sstep_cfg_killed; eassumption.
  - eapply sstep_cfg_syscall_unmodeled; eassumption.
Qed.

Lemma node_ok_cfg_of_forced : forall c I evs nx,
  forced_refusals c -> node_ok segs c I evs nx -> node_ok_cfg c I evs nx.
Proof.
  intros c I evs nx Hfo [Hc Hs]. split.
  - intros i. apply sstep_cfg_of_forced; [exact Hfo | apply Hc].
  - intros e st H. apply Hs. exact (sstep_cfg_sub segs CFG c e st H).
Qed.

(* [comment removed for export] *)
Lemma sstep_of_outcome : forall ms model x8 eff m' evs,
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  syscall_spec (sys_input segs ms x8) model (Ok eff m' evs) ->
  (exists m'', m_halted m' = None /\
     materialize_model_accesses m' (syscall_effect_accesses eff) = Some m'' /\
     sstep segs (mkCfg ms model) evs (SNext (mkCfg (advance_past_svc (apply_effect ms eff)) m'')))
  \/ sstep segs (mkCfg ms model) [] SError
  \/ (exists e', sstep segs (mkCfg ms model) e' (SNext (mkCfg ms m'))).
Proof.
  intros ms model x8 eff m' evs Hh Hsvc Hspec.
  destruct (m_halted m') as [code |] eqn:Hh'.
  - right. right. destruct (m_killed m') as [sig |] eqn:Hk'.
    + eexists. eapply sstep_killed; eassumption.
    + eexists. eapply sstep_exit; eassumption.
  - destruct (materialize_model_accesses m' (syscall_effect_accesses eff)) as [m'' |] eqn:Hmat.
    + left. exists m''. split; [reflexivity | split; [reflexivity |]].
      eapply sstep_syscall; eassumption.
    + right. left. eapply sstep_syscall_materialization_fault; eassumption.
Qed.

(* [comment removed for export] *)
Lemma sstep_svc_next_inv : forall ms model x8 e c',
  ms_svc_pending ms = Some x8 -> ms_svc_pending (cfg_ms c') = None ->
  sstep segs (mkCfg ms model) e (SNext c') ->
  exists eff m' m'', syscall_spec (sys_input segs ms x8) model (Ok eff m' e) /\ m_halted m' = None /\
    materialize_model_accesses m' (syscall_effect_accesses eff) = Some m'' /\
    c' = mkCfg (advance_past_svc (apply_effect ms eff)) m''.
Proof.
  intros ms model x8 e c' Hsvc Hsvc' H. inversion H; subst; try congruence.
  - match goal with H : ms_svc_pending ms = Some ?y |- _ => rewrite Hsvc in H; inversion H; subst end.
    eexists _, _, _. split; [eassumption | split; [eassumption | split; [eassumption | reflexivity]]].
  - exfalso. cbn [cfg_ms] in Hsvc'. congruence.
  - exfalso. cbn [cfg_ms] in Hsvc'. congruence.
Qed.

Lemma snext_gpr0 : forall c1 c2, SNext c1 = SNext c2 -> ms_gpr (cfg_ms c1) 0 = ms_gpr (cfg_ms c2) 0.
Proof. intros c1 c2 H. injection H as ->. reflexivity. Qed.

Lemma snext_svc : forall c1 c2, SNext c1 = SNext c2 -> ms_svc_pending (cfg_ms c1) = ms_svc_pending (cfg_ms c2).
Proof. intros c1 c2 H. injection H as ->. reflexivity. Qed.

(* [comment removed for export] *)
Lemma node_ok_cfg_unit : forall c e0 c',
  node_ok segs c unit (fun _ => e0) (fun _ => c') -> node_ok_cfg c unit (fun _ => e0) (fun _ => c').
Proof.
  intros c e0 c' [Hc Hs]. split; [| intros e st H; apply Hs; exact (sstep_cfg_sub segs CFG c e st H)].
  intros []. pose proof (Hc tt) as H. cbv beta in H.
  destruct c as [ms model].
  inversion H as
    [ms1 model1 ms' model' Hh Hsvc Hacc
    | ms1 model1 Hh Hsvc Hacc
    | ms1 model1 Hh Hsvc Hacc
    | ms1 model1 x8 eff model' model'' evs Hh Hsvc Hspec Hh' Hmat
    | ms1 model1 x8 eff model' evs Hh Hsvc Hspec Hh' Hmat
    | ms1 model1 x8 eff model' evs code Hh Hsvc Hspec Hh' Hk
    | ms1 model1 x8 eff model' evs sig Hh Hsvc Hspec Hk
    | ms1 model1 x8 Hh Hsvc Hspec]; subst.
  - eapply sstep_cfg_instr; eassumption.
  - eapply sstep_cfg_syscall; try eassumption.
    intros (_ & Hr & (eff' & m2 & evs2 & Hs2 & Hr2)).
    destruct (sstep_of_outcome ms model x8 eff' m2 evs2 Hh Hsvc Hs2)
      as [(m3 & _ & _ & H3) | [H3 | (e3 & H3)]].
    + destruct (Hs _ _ H3) as (_ & _ & E3). apply snext_gpr0 in E3. cbn [cfg_ms] in E3.
      rewrite !gpr0_adv_apply in E3. rewrite E3, Hr in Hr2. discriminate Hr2.
    + destruct (Hs _ _ H3) as (_ & _ & E3). discriminate.
    + destruct (Hs _ _ H3) as (_ & _ & E3). apply snext_svc in E3. cbn [cfg_ms advance_past_svc ms_svc_pending] in E3.
      congruence.
  - eapply sstep_cfg_exit; eassumption.
  - eapply sstep_cfg_killed; eassumption.
Qed.

(* [comment removed for export] *)
Lemma node_ok_cfg_keep : forall ms model x8 (I J : Type) (evs : I -> list event) (nx : I -> config)
    (f : J -> I) (j0 : J),
  ms_svc_pending ms = Some x8 ->
  injected_family_off CFG (sys_input segs ms x8) = true ->
  node_ok segs (mkCfg ms model) I evs nx ->
  (forall i, ms_svc_pending (cfg_ms (nx i)) = None) ->
  (forall j, refusal_b (sys_input segs ms x8) model (ms_gpr (cfg_ms (nx (f j))) 0) = false) ->
  (forall i, refusal_b (sys_input segs ms x8) model (ms_gpr (cfg_ms (nx i)) 0) = false -> exists j, f j = i) ->
  node_ok_cfg (mkCfg ms model) J (fun j => evs (f j)) (fun j => nx (f j)).
Proof.
  intros ms model x8 I J evs nx f j0 Hsvc Hoff [Hc Hs] Hsvc' Hkeep Hall.
  (* [comment removed for export] *)
  destruct (sstep_svc_next_inv ms model x8 _ _ Hsvc (Hsvc' (f j0)) (Hc (f j0)))
    as (eff0 & m0 & m0' & Hspec0 & _ & _ & E0).
  assert (Hnr0 : refusal_b (sys_input segs ms x8) model (eff_ret eff0) = false).
  { rewrite <- (gpr0_adv_apply ms eff0). specialize (Hkeep j0). rewrite E0 in Hkeep. exact Hkeep. }
  split.
  - intros j. destruct (sstep_svc_next_inv ms model x8 _ _ Hsvc (Hsvc' (f j)) (Hc (f j)))
      as (eff & m' & m'' & Hspec & Hh' & Hmat & E).
    pose proof (Hkeep j) as Hk. rewrite E in Hk. cbn [cfg_ms] in Hk. rewrite gpr0_adv_apply in Hk.
    rewrite E. apply (sstep_cfg_syscall segs CFG ms model x8 eff m' m''); try assumption.
    + exact (sstep_halted_none segs _ _ _ (Hc (f j))).
    + apply spurious_refusal_not_refusal. exact Hk.
  - intros e st H. destruct (Hs e st (sstep_cfg_sub segs CFG _ e st H)) as (i & -> & ->).
    destruct (refusal_b (sys_input segs ms x8) model (ms_gpr (cfg_ms (nx i)) 0)) eqn:Hr.
    + exfalso.
      inversion H as
        [ms1 model1 ms' model' Hh Hsv Hacc
        | ms1 model1 Hh Hsv Hacc
        | ms1 model1 Hh Hsv Hacc
        | ms1 model1 y8 eff model' model'' evs1 Hh Hsv Hspec Hns Hh' Hmat
        | ms1 model1 y8 eff model' evs1 Hh Hsv Hspec Hns Hh' Hmat
        | ms1 model1 y8 eff model' evs1 code Hh Hsv Hspec Hh' Hk
        | ms1 model1 y8 eff model' evs1 sig Hh Hsv Hspec Hk
        | ms1 model1 y8 Hh Hsv Hspec]; subst; try congruence.
      * rewrite Hsvc in Hsv. injection Hsv as <-.
        match goal with E : _ = nx i |- _ => rewrite <- E in Hr end.
        cbn [cfg_ms] in Hr. rewrite gpr0_adv_apply in Hr.
        apply Hns. split; [exact Hoff | split; [exact Hr |]].
        exists eff0, m0, (evs (f j0)). split; [exact Hspec0 | exact Hnr0].
      * pose proof (Hsvc' i) as Hp.
        match goal with E : _ = nx i |- _ => rewrite <- E in Hp end.
        cbn [cfg_ms] in Hp. congruence.
      * pose proof (Hsvc' i) as Hp.
        match goal with E : _ = nx i |- _ => rewrite <- E in Hp end.
        cbn [cfg_ms] in Hp. congruence.
    + destruct (Hall i Hr) as (j & <-). exists j. split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma node_ok_cfg_nonref : forall ms model x8 (I : Type) (evs : I -> list event) (nx : I -> config) (i0 : I),
  ms_svc_pending ms = Some x8 ->
  node_ok segs (mkCfg ms model) I evs nx ->
  (forall i, ms_svc_pending (cfg_ms (nx i)) = None) ->
  (forall i, refusal_b (sys_input segs ms x8) model (ms_gpr (cfg_ms (nx i)) 0) = false) ->
  node_ok_cfg (mkCfg ms model) I evs nx.
Proof.
  intros ms model x8 I evs nx i0 Hsvc Hnode Hsvc' Hnr.
  destruct (injected_family_off CFG (sys_input segs ms x8)) eqn:Hoff.
  - exact (node_ok_cfg_keep ms model x8 I I evs nx (fun i => i) i0 Hsvc Hoff Hnode Hsvc' Hnr
             (fun i _ => ex_intro _ i eq_refl)).
  - apply node_ok_cfg_of_nonalloc; [| exact Hnode].
    intros y Hy. cbn [cfg_ms] in Hy. rewrite Hsvc in Hy. injection Hy as <-. exact Hoff.
Qed.

(* [comment removed for export] *)
Lemma node_ok_cfg_uniform : forall ms model (I : Type) (evs : I -> list event) (nx : I -> config),
  node_ok segs (mkCfg ms model) I evs nx ->
  (forall i, ms_svc_pending (cfg_ms (nx i)) = None) ->
  (forall i j, ms_gpr (cfg_ms (nx i)) 0 = ms_gpr (cfg_ms (nx j)) 0) ->
  node_ok_cfg (mkCfg ms model) I evs nx.
Proof.
  intros ms model I evs nx [Hc Hs] Hsvc' Hsame.
  split; [| intros e st H; apply Hs; exact (sstep_cfg_sub segs CFG _ e st H)].
  intros i. pose proof (Hc i) as H.
  inversion H as
    [ms1 model1 ms' model' Hh Hsvc Hacc
    | ms1 model1 Hh Hsvc Hacc
    | ms1 model1 Hh Hsvc Hacc
    | ms1 model1 x8 eff model' model'' evs1 Hh Hsvc Hspec Hh' Hmat
    | ms1 model1 x8 eff model' evs1 Hh Hsvc Hspec Hh' Hmat
    | ms1 model1 x8 eff model' evs1 code Hh Hsvc Hspec Hh' Hk
    | ms1 model1 x8 eff model' evs1 sig Hh Hsvc Hspec Hk
    | ms1 model1 x8 Hh Hsvc Hspec]; subst.
  - try (match goal with E : _ = nx i |- _ => rewrite <- E end).
    eapply sstep_cfg_instr; eassumption.
  - match goal with E : _ = nx i |- _ => rename E into Ei end.
    try rewrite <- Ei. try (match goal with E : _ = evs i |- _ => rewrite <- E end).
    eapply sstep_cfg_syscall; try eassumption.
    intros (_ & Hr & (eff' & m2 & evs2 & Hs2 & Hr2)).
    destruct (sstep_of_outcome ms model x8 eff' m2 evs2 Hh Hsvc Hs2)
      as [(m3 & _ & _ & H3) | [H3 | (e3 & H3)]].
    + destruct (Hs _ _ H3) as (j & _ & E3). apply snext_gpr0 in E3. cbn [cfg_ms] in E3.
      rewrite gpr0_adv_apply, (Hsame j i), <- Ei in E3. cbn [cfg_ms] in E3. rewrite gpr0_adv_apply in E3.
      rewrite E3, Hr in Hr2. discriminate Hr2.
    + destruct (Hs _ _ H3) as (j & _ & E3). discriminate.
    + destruct (Hs _ _ H3) as (j & _ & E3). apply snext_svc in E3. cbn [cfg_ms] in E3.
      rewrite (Hsvc' j) in E3. congruence.
  - match goal with E : _ = nx i |- _ => rename E into Ei end.
    pose proof (Hsvc' i) as Hp. rewrite <- Ei in Hp. cbn [cfg_ms] in Hp. congruence.
  - match goal with E : _ = nx i |- _ => rename E into Ei end.
    pose proof (Hsvc' i) as Hp. rewrite <- Ei in Hp. cbn [cfg_ms] in Hp. congruence.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma srz_cfg_silent1 : forall c c' T,
  node_ok segs c unit (fun _ => []) (fun _ => c') ->
  srealizes_cfg c' T ->
  srealizes_cfg c T.
Proof.
  intros c c' T Hnode Hc.
  apply (srz_cfg_conseq c (t_alt (fun _ : unit => t_emit [] T))).
  - apply (srz_cfg_node c unit (fun _ => []) (fun _ => c') (fun _ => T) tt (node_ok_cfg_unit c [] c' Hnode)).
    intros []; exact Hc.
  - eapply t_eq_trans;
      [ apply (t_alt_unit (fun _ : unit => t_emit [] T))
      | apply t_emit_nil_eq; eapply srealizes_cfg_nonempty; exact Hc ].
Qed.

(* [comment removed for export] *)
Lemma srz_cfg_emit1 : forall c c' e T,
  node_ok segs c unit (fun _ => e) (fun _ => c') ->
  srealizes_cfg c' T ->
  srealizes_cfg c (t_emit e T).
Proof.
  intros c c' e T Hnode Hc.
  apply (srz_cfg_conseq c (t_alt (fun _ : unit => t_emit e T))).
  - apply (srz_cfg_node c unit (fun _ => e) (fun _ => c') (fun _ => T) tt (node_ok_cfg_unit c e c' Hnode)).
    intros []; exact Hc.
  - apply t_alt_unit.
Qed.

(* [comment removed for export] *)
Lemma srz_cfg_node_na : forall c (I : Type) (evs : I -> list event) (nx : I -> config) (T : I -> TSet) (i0 : I),
  nonalloc c ->
  node_ok segs c I evs nx ->
  (forall i, srealizes_cfg (nx i) (T i)) ->
  srealizes_cfg c (t_alt (fun i => t_emit (evs i) (T i))).
Proof.
  intros c I evs nx T i0 Hna Hnode Hc.
  exact (srz_cfg_node c I evs nx T i0 (node_ok_cfg_of_nonalloc c I evs nx Hna Hnode) Hc).
Qed.

(* [comment removed for export] *)
Lemma srz_cfg_cases : forall c (I : Type) (nx : I -> config) (T : I -> TSet) (i0 : I),
  node_ok_cfg c I (fun _ => []) nx ->
  (forall i, srealizes_cfg (nx i) (T i)) ->
  srealizes_cfg c (t_alt T).
Proof.
  intros c I nx T i0 Hnode Hc.
  apply (srz_cfg_conseq c (t_alt (fun i => t_emit [] (T i)))).
  - apply (srz_cfg_node c I (fun _ => []) nx T i0 Hnode Hc).
  - intros tr. split.
    + intros [i Hi]. exists i.
      exact (proj1 (t_emit_nil_eq (T i) (srealizes_cfg_nonempty _ _ (Hc i)) tr) Hi).
    + intros [i Hi]. exists i.
      exact (proj2 (t_emit_nil_eq (T i) (srealizes_cfg_nonempty _ _ (Hc i)) tr) Hi).
Qed.

(* [comment removed for export] *)
Lemma srz_cfg_same : forall c (I : Type) (nx : I -> config) (T : TSet) (i0 : I),
  node_ok_cfg c I (fun _ => []) nx ->
  (forall i, srealizes_cfg (nx i) T) ->
  srealizes_cfg c T.
Proof.
  intros c I nx T i0 Hnode Hc.
  apply (srz_cfg_conseq c (t_alt (fun _ : I => T))).
  - exact (srz_cfg_cases c I nx (fun _ => T) i0 Hnode Hc).
  - intros tr. split; [intros [_ H]; exact H | intros H; exists i0; exact H].
Qed.

(* [comment removed for export] *)
Lemma srz_cfg_alt2 : forall c (IA IB : Type) (nx : IA + IB -> config) (A B : TSet) (a0 : IA) (b0 : IB),
  node_ok_cfg c (IA + IB) (fun _ => []) nx ->
  (forall i, srealizes_cfg (nx (inl i)) A) ->
  (forall i, srealizes_cfg (nx (inr i)) B) ->
  srealizes_cfg c (t_alt2 A B).
Proof.
  intros c IA IB nx A B a0 b0 Hnode HA HB.
  assert (HA0 : A []) by (eapply srealizes_cfg_nonempty; apply (HA a0)).
  assert (HB0 : B []) by (eapply srealizes_cfg_nonempty; apply (HB b0)).
  apply (srz_cfg_conseq c
    (t_alt (fun i : IA + IB => t_emit [] (match i with inl _ => A | inr _ => B end)))).
  - apply (srz_cfg_node c (IA + IB) (fun _ => []) nx
             (fun i => match i with inl _ => A | inr _ => B end) (inl a0) Hnode).
    intros [i|i]; [apply HA | apply HB].
  - intro tr. unfold t_alt2. split.
    + intros [[i|i] Hi];
        [ left; exact (proj1 (t_emit_nil_eq A HA0 tr) Hi)
        | right; exact (proj1 (t_emit_nil_eq B HB0 tr) Hi) ].
    + intros [H | H];
        [ exists (inl a0); exact (proj2 (t_emit_nil_eq A HA0 tr) H)
        | exists (inr b0); exact (proj2 (t_emit_nil_eq B HB0 tr) H) ].
Qed.

(* [comment removed for export] *)
Lemma srz_cfg_alt2_drop : forall ms model x8 (IA IB : Type) (nx : IA + IB -> config) (B : TSet) (b0 : IB),
  ms_svc_pending ms = Some x8 ->
  injected_family_off CFG (sys_input segs ms x8) = true ->
  node_ok segs (mkCfg ms model) (IA + IB) (fun _ => []) nx ->
  (forall i, ms_svc_pending (cfg_ms (nx i)) = None) ->
  (forall a, refusal_b (sys_input segs ms x8) model (ms_gpr (cfg_ms (nx (inl a))) 0) = true) ->
  (forall b, refusal_b (sys_input segs ms x8) model (ms_gpr (cfg_ms (nx (inr b))) 0) = false) ->
  (forall b, srealizes_cfg (nx (inr b)) B) ->
  srealizes_cfg (mkCfg ms model) B.
Proof.
  intros ms model x8 IA IB nx B b0 Hsvc Hoff Hnode Hsvc' Hrefa Hrefb HB.
  apply (srz_cfg_same (mkCfg ms model) IB (fun b => nx (inr b)) B b0); [| exact HB].
  apply (node_ok_cfg_keep ms model x8 (IA + IB) IB (fun _ => []) nx inr b0 Hsvc Hoff Hnode Hsvc' Hrefb).
  intros [a | b] Hr; [rewrite Hrefa in Hr; discriminate Hr | exists b; reflexivity].
Qed.

(* [comment removed for export] *)
Lemma srz_cfg_silent_nonref : forall ms model x8 (I : Type) (nx : I -> config) (B : TSet) (i0 : I),
  ms_svc_pending ms = Some x8 ->
  injected_family_off CFG (sys_input segs ms x8) = true ->
  node_ok segs (mkCfg ms model) I (fun _ => []) nx ->
  (forall i, ms_svc_pending (cfg_ms (nx i)) = None) ->
  refusal_b (sys_input segs ms x8) model (ms_gpr (cfg_ms (nx i0)) 0) = false ->
  (forall i, refusal_b (sys_input segs ms x8) model (ms_gpr (cfg_ms (nx i)) 0) = false -> srealizes_cfg (nx i) B) ->
  srealizes_cfg (mkCfg ms model) B.
Proof.
  intros ms model x8 I nx B i0 Hsvc Hoff Hnode Hsvc' Hr0 HB.
  set (J := {i : I | refusal_b (sys_input segs ms x8) model (ms_gpr (cfg_ms (nx i)) 0) = false}).
  apply (srz_cfg_same (mkCfg ms model) J (fun j => nx (proj1_sig j)) B (exist _ i0 Hr0)).
  - apply (node_ok_cfg_keep ms model x8 I J (fun _ => []) nx (@proj1_sig _ _) (exist _ i0 Hr0) Hsvc Hoff Hnode Hsvc').
    + intros [i Hi]. exact Hi.
    + intros i Hi. exists (exist _ i Hi). reflexivity.
  - intros [i Hi]. exact (HB i Hi).
Qed.

(* [comment removed for export] *)
Lemma alloc_no_214 : alloc_no 214 = true. Proof. reflexivity. Qed.
Lemma alloc_no_216 : alloc_no 216 = true. Proof. reflexivity. Qed.
Lemma alloc_no_222 : alloc_no 222 = true. Proof. reflexivity. Qed.
Lemma alloc_no_226 : alloc_no 226 = true. Proof. reflexivity. Qed.

Lemma injected_family_off_no : forall ms x8 no,
  bv_unsigned x8 = no -> alloc_no no = true -> injected_family_off CFG (sys_input segs ms x8) = true.
Proof. intros ms x8 no Hno H. rewrite injected_family_off_alloc_no, Hno. exact H. Qed.

Lemma refusal_b_mmap : forall ms x8 m ret,
  bv_unsigned x8 = 222%Z -> refusal_b (sys_input segs ms x8) m ret = bv_eqb ret (errno_ret ENOMEM).
Proof.
  intros ms x8 m ret Hno. unfold refusal_b. cbn [in_sysno sys_input]. rewrite Hno. cbn.
  unfold ret_in_errnos. cbn [existsb mmap_errnos]. apply orb_false_r.
Qed.

Lemma refusal_b_mprotect : forall ms x8 m ret,
  bv_unsigned x8 = 226%Z -> refusal_b (sys_input segs ms x8) m ret = bv_eqb ret (errno_ret ENOMEM).
Proof.
  intros ms x8 m ret Hno. unfold refusal_b. cbn [in_sysno sys_input]. rewrite Hno. cbn.
  unfold ret_in_errnos. cbn [existsb mprotect_errnos]. apply orb_false_r.
Qed.

Lemma refusal_b_brk : forall ms x8 m ret,
  bv_unsigned x8 = 214%Z -> refusal_b (sys_input segs ms x8) m ret = brk_refusal_b m (ms_gpr ms 0) ret.
Proof.
  intros ms x8 m ret Hno. unfold refusal_b. cbn [in_sysno sys_input]. rewrite Hno. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma errno_ret_unsigned' : forall e, (1 <= e <= 4095)%Z -> bv_unsigned (errno_ret e) = (2 ^ 64 - e)%Z.
Proof.
  intros e He. unfold errno_ret.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (Z.of_N 64) with 64%Z.
  replace (- e)%Z with (2 ^ 64 - e + (-1) * 2 ^ 64)%Z by lia.
  rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

Lemma bv_eqb_errno_small : forall (ret : word) e,
  (1 <= e <= 4095)%Z -> (bv_unsigned ret < 2 ^ 64 - 4095)%Z -> bv_eqb ret (errno_ret e) = false.
Proof.
  intros ret e He Hr. destruct (bv_eqb ret (errno_ret e)) eqn:E; [| reflexivity].
  apply bv_eqb_eq in E. apply (f_equal bv_unsigned) in E.
  rewrite errno_ret_unsigned' in E by lia. lia.
Qed.

Lemma bv_eqb_errno_refl : forall e, bv_eqb (errno_ret e) (errno_ret e) = true.
Proof. intros e. apply bv_eqb_eq. reflexivity. Qed.

(* [comment removed for export] *)
Lemma srz_cfg_step : forall ms model ms' T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  srealizes_cfg (mkCfg ms' model) T ->
  srealizes_cfg (mkCfg ms model) T.
Proof.
  intros ms model ms' T Hh Hlazy Hsvc Hstep Hc.
  eapply srz_cfg_silent1; [apply node_instr; eassumption | exact Hc].
Qed.

Lemma srz_cfg_msteps : forall ms ms' model T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  msteps segs ms ms' ->
  srealizes_cfg (mkCfg ms' model) T ->
  srealizes_cfg (mkCfg ms model) T.
Proof.
  intros ms ms' model T Hh Hlazy Hms;
    induction Hms as [ms | ms ms1 ms2 Hsvc Hstep Hms IH];
    intro Hc; [exact Hc|].
  eapply srz_cfg_step; [exact Hh | exact Hlazy | exact Hsvc | exact Hstep | apply IH; exact Hc].
Qed.

Lemma srz_cfg_step_disjoint : forall ms model ms' ranges T,
  m_halted model = None ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step_accesses segs ms
    = MachineOk (@mkAccessReport machine_state ms' ranges) ->
  accesses_outside_lazy ranges (m_vm_lazy model) ->
  srealizes_cfg (mkCfg ms' model) T ->
  srealizes_cfg (mkCfg ms model) T.
Proof.
  intros ms model ms' ranges T Hh Hsvc Hstep Hout Hc.
  eapply srz_cfg_silent1; [eapply node_instr_disjoint; eassumption | exact Hc].
Qed.

(* [comment removed for export] *)
Lemma srz_cfg_exit : forall ms model x8,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  is_exit_no x8 ->
  srealizes_cfg (mkCfg ms model)
            (t_exit (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)).
Proof.
  intros ms model x8 Hh Hsvc Hx8.
  set (code := bv_and (ms_gpr ms 0) (Z_to_bv 64 255)).
  unfold t_exit.
  eapply (srz_cfg_emit1 (mkCfg ms model) (mkCfg ms (with_halted code model))).
  - split.
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
  - apply srz_cfg_halt. cbn. discriminate.
Qed.

End WithSegs.
