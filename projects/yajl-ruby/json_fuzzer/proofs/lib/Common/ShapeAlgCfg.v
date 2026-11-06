(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import LiaTuning.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import SimInv ExitSim CatSim MmapSim.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Export ShapeAlg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma injected_family_off_no_arm : forall cfg i,
  injected_arm (bv_unsigned (in_sysno i)) = None ->
  injected_family_off cfg i = false.
Proof. intros cfg i H. unfold injected_family_off. rewrite H. reflexivity. Qed.

Lemma not_spurious_no_arm : forall cfg i m eff,
  injected_arm (bv_unsigned (in_sysno i)) = None ->
  ~ spurious_refusal_cfg cfg i m eff.
Proof.
  intros cfg i m eff H. apply spurious_refusal_family_on.
  apply injected_family_off_no_arm. exact H.
Qed.

(* [comment removed for export] *)
Lemma spurious_refusal_ret : forall cfg i m eff eff',
  eff_ret eff = eff_ret eff' ->
  spurious_refusal_cfg cfg i m eff <-> spurious_refusal_cfg cfg i m eff'.
Proof.
  intros cfg i m eff eff' E. unfold spurious_refusal_cfg. rewrite E. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma apply_effect_regs : forall ms eff,
  ms_regs (apply_effect ms eff) = bvmap_set (Z_to_bv 5 10) (eff_ret eff) (ms_regs ms).
Proof. intros ms eff. reflexivity. Qed.

Lemma advance_apply_effect_ret : forall ms eff eff',
  advance_past_svc (apply_effect ms eff) = advance_past_svc (apply_effect ms eff') ->
  eff_ret eff = eff_ret eff'.
Proof.
  intros ms eff eff' E.
  assert (R : ms_regs (advance_past_svc (apply_effect ms eff))
              = ms_regs (advance_past_svc (apply_effect ms eff'))) by (rewrite E; reflexivity).
  cbn [advance_past_svc ms_regs] in R. rewrite !apply_effect_regs in R.
  assert (G : bvmap_get (Z_to_bv 5 10) (bvmap_set (Z_to_bv 5 10) (eff_ret eff) (ms_regs ms))
              = bvmap_get (Z_to_bv 5 10) (bvmap_set (Z_to_bv 5 10) (eff_ret eff') (ms_regs ms)))
    by (rewrite R; reflexivity).
  rewrite !bvmap_get_set_same in G. congruence.
Qed.

Lemma advance_past_svc_svc : forall ms, ms_svc_pending (advance_past_svc ms) = None.
Proof. reflexivity. Qed.

Section StepLift.
Variable cfg : SpuriousCfg.
Variable segs : list Segment.

(* [comment removed for export] *)
Lemma sstep_cfg_of_sstep : forall ms mo evs X,
  sstep segs (mkCfg ms mo) evs X ->
  (forall x8 eff m' evs', ms_svc_pending ms = Some x8 ->
     syscall_spec (sys_input segs ms x8) mo (Ok eff m' evs') -> m_halted m' = None ->
     ~ spurious_refusal_cfg cfg (sys_input segs ms x8) mo eff) ->
  sstep_cfg segs cfg (mkCfg ms mo) evs X.
Proof.
  intros ms mo evs X Hss Hns.
  inversion Hss; subst;
    [ eapply sstep_cfg_instr | eapply sstep_cfg_instr_fault | eapply sstep_cfg_instr_unmodeled
    | eapply sstep_cfg_syscall | eapply sstep_cfg_syscall_materialization_fault
    | eapply sstep_cfg_exit | eapply sstep_cfg_killed | eapply sstep_cfg_syscall_unmodeled ];
    eauto.
Qed.

Lemma sstep_cfg_of_sstep_instr : forall ms mo evs X,
  ms_svc_pending ms = None ->
  sstep segs (mkCfg ms mo) evs X -> sstep_cfg segs cfg (mkCfg ms mo) evs X.
Proof.
  intros ms mo evs X Hsvc Hss. apply sstep_cfg_of_sstep; [exact Hss|].
  intros x8 eff m' evs' H. rewrite Hsvc in H. discriminate H.
Qed.

Lemma sstep_cfg_of_sstep_no_arm : forall ms mo x8 evs X,
  ms_svc_pending ms = Some x8 ->
  injected_arm (bv_unsigned x8) = None ->
  sstep segs (mkCfg ms mo) evs X -> sstep_cfg segs cfg (mkCfg ms mo) evs X.
Proof.
  intros ms mo x8 evs X Hsvc Harm Hss. apply sstep_cfg_of_sstep; [exact Hss|].
  intros x8' eff m' evs' H _ _. rewrite Hsvc in H. injection H as <-.
  apply not_spurious_no_arm. rewrite in_sysno_sys_input. exact Harm.
Qed.

(* [comment removed for export] *)
Lemma sstep_cfg_of_sstep_inplace : forall ms mo evs mo',
  ms_svc_pending ms <> None ->
  sstep segs (mkCfg ms mo) evs (SNext (mkCfg ms mo')) ->
  sstep_cfg segs cfg (mkCfg ms mo) evs (SNext (mkCfg ms mo')).
Proof.
  intros ms mo evs mo' Hsvc Hss.
  inversion Hss; subst.
  - exfalso. apply Hsvc. assumption.
  - exfalso.
    match goal with
    | [ H : advance_past_svc (apply_effect ms ?e) = ms |- _ ] =>
        apply Hsvc; rewrite <- H; apply advance_past_svc_svc
    end.
  - eapply sstep_cfg_exit; eauto.
  - eapply sstep_cfg_killed; eauto.
Qed.

(* [comment removed for export] *)
Lemma sstep_cfg_of_sstep_syscall : forall ms mo x8 evs ms' mo',
  ms_svc_pending ms = Some x8 ->
  ms_svc_pending ms' = None ->
  sstep segs (mkCfg ms mo) evs (SNext (mkCfg ms' mo')) ->
  (forall eff m1 evs1, syscall_spec (sys_input segs ms x8) mo (Ok eff m1 evs1) ->
     advance_past_svc (apply_effect ms eff) = ms' ->
     ~ spurious_refusal_cfg cfg (sys_input segs ms x8) mo eff) ->
  sstep_cfg segs cfg (mkCfg ms mo) evs (SNext (mkCfg ms' mo')).
Proof.
  intros ms mo x8 evs ms' mo' Hsvc Hsvc' Hss Hns.
  inversion Hss; subst.
  - exfalso. congruence.
  - match goal with
    | [ H : ms_svc_pending ms = Some ?x |- _ ] =>
        assert (x = x8) by congruence; subst x
    end.
    eapply sstep_cfg_syscall; eauto.
  - exfalso. congruence.
  - exfalso. congruence.
Qed.

End StepLift.

(* [comment removed for export] *)

Section WithCfg.
Variable cfg : SpuriousCfg.
Variable segs : list Segment.

Local Abbreviation sstepC := (sstep_cfg segs cfg).
Local Abbreviation starC := (star_cfg segs cfg).

(* [comment removed for export] *)
Definition node_ok_cfg (c : config) (I : Type)
    (evs : I -> list event) (nx : I -> config) : Prop :=
  (forall i, sstepC c (evs i) (SNext (nx i)))
  /\ (forall e st, sstepC c e st -> exists i, e = evs i /\ st = SNext (nx i)).

(* [comment removed for export] *)
Lemma node_ok_cfg_lift : forall c I evs nx,
  node_ok segs c I evs nx ->
  (forall i, sstepC c (evs i) (SNext (nx i))) ->
  node_ok_cfg c I evs nx.
Proof.
  intros c I evs nx [_ Hsound] Hcomp. split; [exact Hcomp|].
  intros e st Hss. apply Hsound. eapply sstep_cfg_sub. exact Hss.
Qed.

(* [comment removed for export] *)
Inductive realizes_cfg : config -> TSet -> Prop :=
| rz_node_cfg : forall c (I : Type) (evs : I -> list event) (nx : I -> config)
                   (T : I -> TSet) (i0 : I),
    node_ok_cfg c I evs nx ->
    (forall i, realizes_cfg (nx i) (T i)) ->
    realizes_cfg c (t_alt (fun i => t_emit (evs i) (T i)))
| rz_halt_cfg : forall c,
    m_halted (cfg_model c) <> None ->
    realizes_cfg c t_nil
| rz_conseq_cfg : forall c T T',
    realizes_cfg c T -> t_eq T T' -> realizes_cfg c T'.

(* [comment removed for export] *)

Lemma realizes_cfg_nonempty : forall c T, realizes_cfg c T -> T [].
Proof.
  intros c T H; induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq].
  - exists i0. left. apply is_prefix_nil.
  - reflexivity.
  - apply Heq. exact IH.
Qed.

Lemma realizes_cfg_pclosed : forall c T, realizes_cfg c T ->
  forall tr tr', T tr -> is_prefix tr' tr -> T tr'.
Proof.
  intros c T H; induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq];
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
  sstepC c e st -> m_halted (cfg_model c) = None.
Proof. intros c e st H; inversion H; subst; cbn; assumption. Qed.

Lemma star_cfg_halted_nil : forall c tr c',
  m_halted (cfg_model c) <> None -> starC c tr c' -> tr = [] /\ c' = c.
Proof.
  intros c tr c' Hh Hstar. inversion Hstar as [|c1 evs c2 tr2 c3 Hss Hstar2]; subst.
  - split; reflexivity.
  - exfalso. apply Hh. eapply sstep_cfg_halted_none. exact Hss.
Qed.

Lemma star_cfg_one : forall c evs c',
  sstepC c evs (SNext c') -> starC c evs c'.
Proof.
  intros c evs c' H. rewrite <- (app_nil_r evs).
  econstructor; eauto using star_cfg_refl.
Qed.

Lemma star_cfg_trans : forall c1 t1 c2 t2 c3,
  starC c1 t1 c2 -> starC c2 t2 c3 -> starC c1 (t1 ++ t2) c3.
Proof.
  intros c1 t1 c2 t2 c3 H1; revert t2 c3.
  induction H1; intros t2 c3' H2; cbn; [assumption|].
  rewrite <- app_assoc. econstructor; eauto.
Qed.

Lemma realizes_cfg_star_only : forall c T, realizes_cfg c T ->
  forall tr c', starC c tr c' -> T tr.
Proof.
  intros c T H; induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq];
    intros tr c' Hstar.
  - inversion Hstar as [|c1 e c2 tr2 c3 Hss Hstar2]; subst.
    + exists i0. left. apply is_prefix_nil.
    + destruct Hnode as [_ Hsound].
      destruct (Hsound e (SNext c2) Hss) as (i & -> & Heq2).
      inversion Heq2; subst c2.
      exists i. right. exists tr2. split; [reflexivity | eapply IH; exact Hstar2].
  - destruct (star_cfg_halted_nil c tr c' Hh Hstar) as [-> _]. reflexivity.
  - apply Heq. eapply IH; exact Hstar.
Qed.

(* [comment removed for export] *)

Lemma obs_trace_cfg_nil : forall c0, obs_trace_cfg segs cfg c0 [].
Proof.
  intros c0. exists [], c0. split; [apply star_cfg_refl | apply is_prefix_nil].
Qed.

Lemma realizes_cfg_admits : forall c T, realizes_cfg c T ->
  forall tr, T tr -> obs_trace_cfg segs cfg c tr.
Proof.
  intros c T H; induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq];
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
Theorem realizes_cfg_obs_iff : forall c T, realizes_cfg c T ->
  forall tr, obs_trace_cfg segs cfg c tr <-> T tr.
Proof.
  intros c T H tr. split.
  - intros (tr' & c' & Hstar & Hp).
    eapply realizes_cfg_pclosed; [exact H | eapply realizes_cfg_star_only; eauto | exact Hp].
  - apply realizes_cfg_admits; exact H.
Qed.

(* [comment removed for export] *)

Lemma realizes_cfg_step : forall c T e c',
  realizes_cfg c T -> sstepC c e (SNext c') -> exists T', realizes_cfg c' T'.
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

Lemma realizes_cfg_star : forall c T tr c',
  realizes_cfg c T -> starC c tr c' -> exists T', realizes_cfg c' T'.
Proof.
  intros c T tr c' H Hstar. revert T H.
  induction Hstar as [c | c1 evs c2 tr c3 Hss Hstar IH]; intros T H.
  - exists T. exact H.
  - destruct (realizes_cfg_step c1 T evs c2 H Hss) as [T2 H2]. exact (IH T2 H2).
Qed.

Lemma realizes_cfg_no_sserror : forall c T e,
  realizes_cfg c T -> ~ sstepC c e SError.
Proof.
  intros c T e H; revert e;
  induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq];
    intros e Hss.
  - destruct Hnode as [_ Hsound].
    destruct (Hsound e SError Hss) as (i & _ & Hbad). discriminate.
  - apply Hh. eapply sstep_cfg_halted_none; exact Hss.
  - eapply IH; exact Hss.
Qed.

Theorem realizes_cfg_no_error : forall c T,
  realizes_cfg c T -> ~ reaches_error_cfg segs cfg c.
Proof.
  intros c T H (tr & c' & evs & Hstar & Herr).
  destruct (realizes_cfg_star c T tr c' H Hstar) as [T' H'].
  exact (realizes_cfg_no_sserror c' T' evs H' Herr).
Qed.

(* [comment removed for export] *)
Lemma realizes_cfg_progress : forall c T,
  realizes_cfg c T -> m_halted (cfg_model c) = None ->
  exists e c', sstepC c e (SNext c').
Proof.
  intros c T H; induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq];
    intros Hnone.
  - destruct Hnode as [Hcomp _]. exists (evs i0), (nx i0). apply Hcomp.
  - exfalso. exact (Hh Hnone).
  - exact (IH Hnone).
Qed.

Definition rz_path_cfg (c : config) : Prop := exists T, realizes_cfg c T.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition behaves_cfg (c : config) (T : TSet) : Prop :=
  (forall tr, obs_trace_cfg segs cfg c tr <-> T tr)
  /\ ~ reaches_error_cfg segs cfg c.

Theorem realizes_cfg_behaves : forall c T,
  realizes_cfg c T -> behaves_cfg c T.
Proof.
  intros c T H. split; [apply realizes_cfg_obs_iff; exact H | eapply realizes_cfg_no_error; exact H].
Qed.

Lemma behaves_cfg_conseq : forall c T T',
  behaves_cfg c T -> t_eq T T' -> behaves_cfg c T'.
Proof.
  intros c T T' [Htr Herr] Heq. split; [| exact Herr].
  intros tr. rewrite (Htr tr). apply Heq.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rz_silent1_cfg : forall c c' T,
  node_ok_cfg c unit (fun _ => []) (fun _ => c') ->
  realizes_cfg c' T ->
  realizes_cfg c T.
Proof.
  intros c c' T Hnode Hc.
  apply (rz_conseq_cfg c (t_alt (fun _ : unit => t_emit [] T))).
  - apply (rz_node_cfg c unit (fun _ => []) (fun _ => c') (fun _ => T) tt Hnode).
    intros []; exact Hc.
  - eapply t_eq_trans;
      [ apply (t_alt_unit (fun _ : unit => t_emit [] T))
      | apply t_emit_nil_eq; eapply realizes_cfg_nonempty; exact Hc ].
Qed.

(* [comment removed for export] *)
Lemma rz_emit1_cfg : forall c c' e T,
  node_ok_cfg c unit (fun _ => e) (fun _ => c') ->
  realizes_cfg c' T ->
  realizes_cfg c (t_emit e T).
Proof.
  intros c c' e T Hnode Hc.
  apply (rz_conseq_cfg c (t_alt (fun _ : unit => t_emit e T))).
  - apply (rz_node_cfg c unit (fun _ => e) (fun _ => c') (fun _ => T) tt Hnode).
    intros []; exact Hc.
  - apply t_alt_unit.
Qed.

(* [comment removed for export] *)
Lemma rz_alt2_cfg : forall c (IA IB : Type) (nx : IA + IB -> config) (A B : TSet)
                       (a0 : IA) (b0 : IB),
  node_ok_cfg c (IA + IB) (fun _ => []) nx ->
  (forall i, realizes_cfg (nx (inl i)) A) ->
  (forall i, realizes_cfg (nx (inr i)) B) ->
  realizes_cfg c (t_alt2 A B).
Proof.
  intros c IA IB nx A B a0 b0 Hnode HA HB.
  assert (HA0 : A []) by (eapply realizes_cfg_nonempty; apply (HA a0)).
  assert (HB0 : B []) by (eapply realizes_cfg_nonempty; apply (HB b0)).
  apply (rz_conseq_cfg c
    (t_alt (fun i : IA + IB =>
              t_emit [] (match i with inl _ => A | inr _ => B end)))).
  - apply (rz_node_cfg c (IA + IB) (fun _ => []) nx
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
Lemma rz_silent_cfg : forall c (I : Type) (nx : I -> config) (T : TSet) (i0 : I),
  node_ok_cfg c I (fun _ => []) nx ->
  (forall i, realizes_cfg (nx i) T) ->
  realizes_cfg c T.
Proof.
  intros c I nx T i0 Hnode Hc.
  assert (HT0 : T []) by (eapply realizes_cfg_nonempty; apply (Hc i0)).
  apply (rz_conseq_cfg c (t_alt (fun i : I => t_emit [] T))).
  - apply (rz_node_cfg c I (fun _ => []) nx (fun _ => T) i0 Hnode). exact Hc.
  - intro tr. split.
    + intros [i Hi]. exact (proj1 (t_emit_nil_eq T HT0 tr) Hi).
    + intros H. exists i0. exact (proj2 (t_emit_nil_eq T HT0 tr) H).
Qed.

(* [comment removed for export] *)

Lemma node_instr_cfg : forall ms model ms',
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  node_ok_cfg (mkCfg ms model) unit (fun _ => []) (fun _ => mkCfg ms' model).
Proof.
  intros ms model ms' Hh Hlazy Hsvc Hstep.
  apply node_ok_cfg_lift; [apply node_instr; assumption|].
  intros []. apply sstep_cfg_of_sstep_instr; [exact Hsvc|].
  exact (proj1 (node_instr segs ms model ms' Hh Hlazy Hsvc Hstep) tt).
Qed.

Lemma rz_step_cfg : forall ms model ms' T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  realizes_cfg (mkCfg ms' model) T ->
  realizes_cfg (mkCfg ms model) T.
Proof.
  intros ms model ms' T Hh Hlazy Hsvc Hstep Hc.
  eapply rz_silent1_cfg; [apply node_instr_cfg; eassumption | exact Hc].
Qed.

Lemma rz_msteps_cfg : forall ms ms' model T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  msteps segs ms ms' ->
  realizes_cfg (mkCfg ms' model) T ->
  realizes_cfg (mkCfg ms model) T.
Proof.
  intros ms ms' model T Hh Hlazy Hms;
    induction Hms as [ms | ms ms1 ms2 Hsvc Hstep Hms IH];
    intro Hc; [exact Hc|].
  eapply rz_step_cfg; [exact Hh | exact Hlazy | exact Hsvc | exact Hstep
                      | apply IH; exact Hc].
Qed.

(* [comment removed for export] *)
Lemma injected_arm_64 : injected_arm 64 = None.
Proof. reflexivity. Qed.
Lemma injected_arm_93 : injected_arm 93 = None.
Proof. reflexivity. Qed.
Lemma injected_arm_94 : injected_arm 94 = None.
Proof. reflexivity. Qed.
Lemma injected_arm_215 : injected_arm 215 = None.
Proof. reflexivity. Qed.

Lemma node_write1_cfg : forall ms model x8 buf,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fd1chan model ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = Z_to_bv 64 1 ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  buf_modeled buf ->
  (1 <= length buf)%nat ->
  node_ok_cfg (mkCfg ms model) (wr_index buf)
          (fun i => map (WriteEv (Z_to_bv 64 1)) (firstn (proj1_sig i) buf))
          (fun i => mkCfg (advance_past_svc
                             (set_gpr0 ms (len_word (firstn (proj1_sig i) buf))))
                          model).
Proof.
  intros ms model x8 buf Hh Hlazy Hfd Hsvc Hno Hg Hr Hbm Hnb.
  pose proof (node_write1 segs ms model x8 buf Hh Hlazy Hfd Hsvc Hno Hg Hr Hbm Hnb) as N.
  apply node_ok_cfg_lift; [exact N|].
  intros i. apply (sstep_cfg_of_sstep_no_arm cfg segs ms model x8); [exact Hsvc | | exact (proj1 N i)].
  rewrite Hno. apply injected_arm_64.
Qed.

Lemma rz_write1_cfg : forall ms model x8 buf T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fd1chan model ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = Z_to_bv 64 1 ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  buf_modeled buf ->
  (1 <= length buf)%nat ->
  (forall n, (1 <= n)%nat -> (n <= length buf)%nat ->
     realizes_cfg (mkCfg (advance_past_svc (set_gpr0 ms (len_word (firstn n buf)))) model) T) ->
  realizes_cfg (mkCfg ms model) (t_write_ch (Z_to_bv 64 1) buf T).
Proof.
  intros ms model x8 buf T Hh Hlazy Hfd Hsvc Hno Hg Hr Hbm Hnb Hc.
  unfold t_write_ch.
  apply (rz_node_cfg (mkCfg ms model) (wr_index buf)
           (fun i => map (WriteEv (Z_to_bv 64 1)) (firstn (proj1_sig i) buf))
           (fun i => mkCfg (advance_past_svc
                              (set_gpr0 ms (len_word (firstn (proj1_sig i) buf))))
                           model)
           (fun _ => T) (wr_full buf Hnb)).
  - apply (node_write1_cfg ms model x8 buf); assumption.
  - intros [n [Hn1 Hn2]]. cbn [proj1_sig]. apply Hc; assumption.
Qed.

(* [comment removed for export] *)
Lemma is_exit_no_arm : forall x8, is_exit_no x8 -> injected_arm (bv_unsigned x8) = None.
Proof. intros x8 [E|E]; rewrite E; reflexivity. Qed.

Lemma rz_exit_cfg : forall ms model x8,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  is_exit_no x8 ->
  realizes_cfg (mkCfg ms model)
           (t_exit (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)).
Proof.
  intros ms model x8 Hh Hsvc Hx8.
  set (code := bv_and (ms_gpr ms 0) (Z_to_bv 64 255)).
  unfold t_exit.
  eapply (rz_emit1_cfg (mkCfg ms model) (mkCfg ms (with_halted code model))).
  - split.
    + intros []. cbn.
      replace [ExitEv code (m_fs model)]
        with ([] ++ [ExitEv code (m_fs (with_halted code model))]) by reflexivity.
      apply (sstep_cfg_exit segs cfg ms model x8 (mkEffect (Z_to_bv 64 0) [] [])
               (with_halted code model) [] code);
        [exact Hh | exact Hsvc
         | apply (exit_dispatch_ok (sys_input segs ms x8) model);
           rewrite in_sysno_sys_input; exact Hx8
         | reflexivity
         | apply m_killed_with_halted ].
    + intros e st Hss. apply sstep_cfg_sub in Hss.
      destruct (sstep_exit_inv segs ms model x8 e st Hh Hsvc Hx8 Hss) as [-> ->].
      exists tt. split; reflexivity.
  - apply rz_halt_cfg. cbn. discriminate.
Qed.

(* [comment removed for export] *)
Lemma rz_munmap_cfg : forall ms model x8 T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 215%Z ->
  munmap_args_ok ms model ->
  realizes_cfg (mkCfg (advance_past_svc (apply_effect ms (munmap_eff ms)))
                  (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)) T ->
  realizes_cfg (mkCfg ms model) T.
Proof.
  intros ms model x8 T Hh Hlazy Hsvc Hno Hargs Hc.
  eapply rz_silent1_cfg; [| exact Hc]. split.
  - intros []. apply (sstep_cfg_of_sstep_no_arm cfg segs ms model x8); [exact Hsvc | rewrite Hno; apply injected_arm_215 |].
    apply (sstep_syscall segs ms model x8 (munmap_eff ms)
                        (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model)
                        (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) []).
    + exact Hh.
    + exact Hsvc.
    + apply munmap_ok; assumption.
    + rewrite munmap_model_halted; exact Hh.
    + apply materialize_model_accesses_no_lazy.
      exact (munmap_model_no_lazy _ _ _ Hlazy).
  - intros e st Hss. apply sstep_cfg_sub in Hss.
    destruct (sstep_munmap_inv segs ms model x8 e st Hh Hlazy Hsvc Hno Hargs Hss)
      as [-> ->].
    exists tt. split; reflexivity.
Qed.

End WithCfg.

Arguments node_ok_cfg cfg segs c I evs nx : clear implicits.

(* [comment removed for export] *)

Section RunLevel.
Variable cfg : SpuriousCfg.

(* [comment removed for export] *)
Lemma run_scfg_eq : forall segs pc ph lim sp brk0 mb dr inp,
  run_scfg cfg (mkImage segs pc ph) lim (mkEntry sp brk0 mb dr) inp =
  let c0 := init_config segs pc ph sp brk0 mb dr lim inp in
  {| bh_traces := obs_trace_cfg segs cfg c0;
     bh_errors := reaches_error_cfg segs cfg c0;
     bh_all_errors := all_traces_error_cfg segs cfg c0;
     bh_unmodeled := reaches_unmodeled_cfg segs cfg c0 |}.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma run_scfg_of_behaves : forall segs pc ph lim sp brk0 mb dr inp T,
  behaves_cfg cfg segs (init_config segs pc ph sp brk0 mb dr lim inp) T ->
  error_free (run_scfg cfg (mkImage segs pc ph) lim (mkEntry sp brk0 mb dr) inp)
  /\ (forall tr, bh_traces (run_scfg cfg (mkImage segs pc ph) lim (mkEntry sp brk0 mb dr) inp) tr <-> T tr).
Proof.
  intros segs pc ph lim sp brk0 mb dr inp T [Htr Herr].
  rewrite run_scfg_eq. cbv zeta. cbn [bh_traces bh_errors]. split; [exact Herr | exact Htr].
Qed.

(* [comment removed for export] *)
Lemma run_scfg_modeled_of_behaves : forall segs pc ph lim sp brk0 mb dr inp T,
  behaves_cfg cfg segs (init_config segs pc ph sp brk0 mb dr lim inp) T ->
  Equivalence.modeled (run_scfg cfg (mkImage segs pc ph) lim (mkEntry sp brk0 mb dr) inp).
Proof.
  intros segs pc ph lim sp brk0 mb dr inp T [_ Herr].
  rewrite run_scfg_eq. cbv zeta. unfold Equivalence.modeled. cbn [bh_unmodeled].
  intros Hun. apply Herr. apply reaches_unmodeled_cfg_reaches_error_cfg. exact Hun.
Qed.

(* [comment removed for export] *)
Theorem shape_strong_equiv_error_free_cfg :
  forall segsS pcS phS spS brkS mbS drS (limS : Z)
         segsT pcT phT spT brkT mbT drT (limT : Z)
         (T : TSet) (inp : ProcInput),
  behaves_cfg cfg segsS (init_config segsS pcS phS spS brkS mbS drS limS inp) T ->
  behaves_cfg cfg segsT (init_config segsT pcT phT spT brkT mbT drT limT inp) T ->
  error_free (run_scfg cfg (mkImage segsS pcS phS) limS (mkEntry spS brkS mbS drS) inp)
  /\ error_free (run_scfg cfg (mkImage segsT pcT phT) limT (mkEntry spT brkT mbT drT) inp)
  /\ trace_equiv (bh_traces (run_scfg cfg (mkImage segsS pcS phS) limS (mkEntry spS brkS mbS drS) inp))
                 (bh_traces (run_scfg cfg (mkImage segsT pcT phT) limT (mkEntry spT brkT mbT drT) inp)).
Proof.
  intros until inp. intros HS HT.
  destruct (run_scfg_of_behaves _ _ _ _ _ _ _ _ _ _ HS) as [HeS HtS].
  destruct (run_scfg_of_behaves _ _ _ _ _ _ _ _ _ _ HT) as [HeT HtT].
  split; [exact HeS|]. split; [exact HeT|].
  intros tr. rewrite (HtS tr), (HtT tr). reflexivity.
Qed.

(* [comment removed for export] *)
Theorem shape_strong_equiv_cfg :
  forall segsS pcS phS spS brkS mbS drS (limS : Z)
         segsT pcT phT spT brkT mbT drT (limT : Z)
         (T : TSet) (inp : ProcInput),
  behaves_cfg cfg segsS (init_config segsS pcS phS spS brkS mbS drS limS inp) T ->
  behaves_cfg cfg segsT (init_config segsT pcT phT spT brkT mbT drT limT inp) T ->
  Equivalence.modeled (run_scfg cfg (mkImage segsS pcS phS) limS (mkEntry spS brkS mbS drS) inp)
  /\ Equivalence.equiv (run_scfg cfg (mkImage segsS pcS phS) limS (mkEntry spS brkS mbS drS) inp)
                       (run_scfg cfg (mkImage segsT pcT phT) limT (mkEntry spT brkT mbT drT) inp).
Proof.
  intros until inp. intros HS HT.
  split; [eapply run_scfg_modeled_of_behaves; exact HS|].
  destruct (shape_strong_equiv_error_free_cfg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS HT) as (_ & HeT & Htr).
  right. split; [exact Htr | exact HeT].
Qed.

End RunLevel.
