(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition base_cfg : SpuriousCfg := mkSpuriousCfg false true true true true true.

Lemma base_cfg_alloc_only : base_cfg = alloc_only_cfg false.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition alloc_only_off (cfg : SpuriousCfg) : Prop :=
  sc_alloc cfg = false /\ sc_fs cfg = true /\ sc_fd cfg = true /\
  sc_net cfg = true /\ sc_cred cfg = true /\ sc_intr cfg = true.

Lemma base_cfg_alloc_only_off : alloc_only_off base_cfg.
Proof. repeat split. Qed.

Lemma alloc_only_cfg_false_off : alloc_only_off (alloc_only_cfg false).
Proof. repeat split. Qed.

(* [comment removed for export] *)
Definition alloc_no_b (n : Z) : bool :=
  Z.eqb n 214 || Z.eqb n 216 || Z.eqb n 222 || Z.eqb n 226.

Lemma alloc_no_b_true_iff : forall n,
  alloc_no_b n = true <-> In n alloc_mark_sysnos.
Proof.
  intros n. unfold alloc_no_b, alloc_mark_sysnos. cbn [In].
  rewrite !orb_true_iff, !Z.eqb_eq. intuition congruence.
Qed.

(* [comment removed for export] *)
Definition family_off_no (cfg : SpuriousCfg) (n : Z) : bool :=
  match injected_arm n with
  | Some a => negb (family_may_fail cfg (ia_family a))
  | None => false
  end.

Lemma injected_family_off_no : forall cfg i,
  injected_family_off cfg i = family_off_no cfg (bv_unsigned (in_sysno i)).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma family_off_no_alloc_only : forall cfg n,
  alloc_only_off cfg -> family_off_no cfg n = alloc_no_b n.
Proof.
  intros cfg n (Ha & Hfs & Hfd & Hnet & Hcred & Hintr).
  unfold family_off_no, injected_arm, alloc_no_b.
  cbn [injected_table lookup_injected ia_no].
  repeat match goal with
  | |- context [Z.eqb ?k n] =>
      destruct (Z.eqb_spec k n) as [<- | ?];
      [ cbn [ia_family family_may_fail]; rewrite ?Ha, ?Hfs, ?Hfd, ?Hnet, ?Hcred, ?Hintr;
        reflexivity | ]
  end.
  symmetry. rewrite !orb_false_iff, !Z.eqb_neq. repeat split; congruence.
Qed.

Lemma injected_family_off_alloc_only : forall cfg i,
  alloc_only_off cfg ->
  injected_family_off cfg i = alloc_no_b (bv_unsigned (in_sysno i)).
Proof.
  intros cfg i H. rewrite injected_family_off_no. apply family_off_no_alloc_only, H.
Qed.

Lemma injected_family_off_alloc_only_iff : forall cfg i,
  alloc_only_off cfg ->
  (injected_family_off cfg i = true <-> In (bv_unsigned (in_sysno i)) alloc_mark_sysnos).
Proof.
  intros cfg i H. rewrite (injected_family_off_alloc_only cfg i H).
  apply alloc_no_b_true_iff.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma arg_reg_0_eq : Z_to_bv 5 (10 + Z.of_nat 0) = (10 : bv 5).
Proof. apply bv_eq. reflexivity. Qed.

Lemma gpr0_after_effect : forall ms eff,
  ms_gpr (advance_past_svc (apply_effect ms eff)) 0 = eff_ret eff.
Proof.
  intros ms eff.
  unfold ms_gpr, advance_past_svc, apply_effect, set_reg, Sem.reg_get.
  cbn [ms_regs].
  change (bv_eqb (10 : bv 5) 0) with false. cbn [ms_regs].
  rewrite arg_reg_0_eq, Prelude.bvmap_get_set_same. reflexivity.
Qed.

Lemma gpr0_after_set_gpr0 : forall ms r,
  ms_gpr (advance_past_svc (set_gpr0 ms r)) 0 = r.
Proof.
  intros ms r.
  unfold ms_gpr, advance_past_svc, set_gpr0, set_reg, Sem.reg_get.
  cbn [ms_regs].
  change (bv_eqb (10 : bv 5) 0) with false. cbn [ms_regs].
  rewrite arg_reg_0_eq, Prelude.bvmap_get_set_same. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma materialize_halted : forall m acc m',
  materialize_model_accesses m acc = Some m' -> m_halted m' = m_halted m.
Proof.
  intros m acc m' H.
  destruct (materialize_model_accesses_frame m acc m' H) as (_ & _ & _ & _ & _ & Hp & _).
  unfold m_halted. rewrite Hp. reflexivity.
Qed.

Lemma killed_halted : forall m sig, m_killed m = Some sig -> m_halted m <> None.
Proof.
  intros m sig Hk Hh. rewrite (m_killed_of_m_halted_none m Hh) in Hk. discriminate Hk.
Qed.

Section WithSegs.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition pending_off (c : config) : Prop :=
  exists x8, ms_svc_pending (cfg_ms c) = Some x8 /\
             injected_family_off cfg (sys_input segs (cfg_ms c) x8) = true.

(* [comment removed for export] *)
Definition pending_on (c : config) : Prop :=
  forall x8, ms_svc_pending (cfg_ms c) = Some x8 ->
             injected_family_off cfg (sys_input segs (cfg_ms c) x8) = false.

Lemma pending_on_not_off : forall c, pending_on c -> ~ pending_off c.
Proof. intros c Hon (x8 & Hsvc & Hoff). rewrite (Hon x8 Hsvc) in Hoff. discriminate. Qed.

Lemma pending_on_or_off : forall c, pending_on c \/ pending_off c.
Proof.
  intros c. destruct (ms_svc_pending (cfg_ms c)) as [x8 |] eqn:Hsvc.
  - destruct (injected_family_off cfg (sys_input segs (cfg_ms c) x8)) eqn:Hoff.
    + right. exists x8. split; [exact Hsvc | exact Hoff].
    + left. intros y8 Hy. rewrite Hsvc in Hy. injection Hy as <-. exact Hoff.
  - left. intros y8 Hy. rewrite Hsvc in Hy. discriminate Hy.
Qed.

Lemma pending_on_no_svc : forall c, ms_svc_pending (cfg_ms c) = None -> pending_on c.
Proof. intros c H x8 Hx. rewrite H in Hx. discriminate Hx. Qed.

(* [comment removed for export] *)
Lemma pending_on_sysno : forall ms model x8 n,
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = n ->
  family_off_no cfg n = false ->
  pending_on (mkCfg ms model).
Proof.
  intros ms model x8 n Hsvc Hn Hoff y8 Hy. cbn [cfg_ms] in *.
  rewrite Hsvc in Hy. injection Hy as <-.
  rewrite injected_family_off_no. cbn [sys_input in_sysno]. rewrite Hn. exact Hoff.
Qed.

Lemma pending_off_sysno : forall ms model x8 n,
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = n ->
  family_off_no cfg n = true ->
  pending_off (mkCfg ms model).
Proof.
  intros ms model x8 n Hsvc Hn Hoff. exists x8. cbn [cfg_ms]. split; [exact Hsvc |].
  rewrite injected_family_off_no. cbn [sys_input in_sysno]. rewrite Hn. exact Hoff.
Qed.

(* [comment removed for export] *)
Definition child_refusal_b (c c' : config) : bool :=
  match ms_svc_pending (cfg_ms c) with
  | Some x8 =>
      match m_halted (cfg_model c') with
      | None => refusal_b (sys_input segs (cfg_ms c) x8) (cfg_model c)
                          (ms_gpr (cfg_ms c') 0)
      | Some _ => false
      end
  | None => false
  end.

(* [comment removed for export] *)
Definition nonrefusal_outcome (c : config) : Prop :=
  exists x8 eff' m' evs',
    ms_svc_pending (cfg_ms c) = Some x8 /\
    syscall_spec (sys_input segs (cfg_ms c) x8) (cfg_model c) (Ok eff' m' evs') /\
    refusal_b (sys_input segs (cfg_ms c) x8) (cfg_model c) (eff_ret eff') = false.

(* [comment removed for export] *)
Definition spurious_child (c c' : config) : Prop :=
  pending_off c /\ child_refusal_b c c' = true /\ nonrefusal_outcome c.

Lemma spurious_child_not_on : forall c c', pending_on c -> ~ spurious_child c c'.
Proof. intros c c' Hon (Hoff & _). exact (pending_on_not_off c Hon Hoff). Qed.

Lemma spurious_child_not_refusal : forall c c',
  child_refusal_b c c' = false -> ~ spurious_child c c'.
Proof. intros c c' H (_ & Hr & _). congruence. Qed.

(* [comment removed for export] *)
Lemma child_refusal_b_syscall : forall ms model x8 eff model'',
  ms_svc_pending ms = Some x8 ->
  m_halted model'' = None ->
  child_refusal_b (mkCfg ms model)
                  (mkCfg (advance_past_svc (apply_effect ms eff)) model'')
  = refusal_b (sys_input segs ms x8) model (eff_ret eff).
Proof.
  intros ms model x8 eff model'' Hsvc Hh. unfold child_refusal_b.
  cbn [cfg_ms cfg_model]. rewrite Hsvc, Hh, gpr0_after_effect. reflexivity.
Qed.

Lemma child_refusal_b_halted : forall c c',
  m_halted (cfg_model c') <> None -> child_refusal_b c c' = false.
Proof.
  intros c c' Hh. unfold child_refusal_b.
  destruct (ms_svc_pending (cfg_ms c)); [| reflexivity].
  destruct (m_halted (cfg_model c')); [reflexivity | contradiction].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Theorem sstep_cfg_next_iff : forall c e c',
  sstep_cfg segs cfg c e (SNext c') <->
  sstep segs c e (SNext c') /\ ~ spurious_child c c'.
Proof.
  intros c e c'. split.
  - intros H. split; [exact (sstep_cfg_sub segs cfg _ _ _ H) |].
    inversion H; subst.
    + (* [comment removed for export] *)
      intros ((x8 & Hsvc & _) & _). cbn [cfg_ms] in Hsvc. congruence.
    + (* [comment removed for export] *)
      intros ((y8 & Hy & Hoff) & Hr & Hex). cbn [cfg_ms] in Hy.
      match goal with Hs : ms_svc_pending ms = Some ?x |- _ =>
        rewrite Hs in Hy; injection Hy as <- end.
      match goal with
      | Hmat : materialize_model_accesses ?m' _ = Some ?m'', Hh' : m_halted ?m' = None |- _ =>
          pose proof (eq_trans (materialize_halted _ _ _ Hmat) Hh') as Hh''
      end.
      match goal with Hs : ms_svc_pending ms = Some ?x |- _ =>
        rewrite (child_refusal_b_syscall ms model x eff _ Hs Hh'') in Hr end.
      match goal with Hns : ~ spurious_refusal_cfg _ _ _ _ |- _ => apply Hns end.
      split; [exact Hoff | split; [exact Hr |]].
      destruct Hex as (z8 & eff' & m' & evs' & Hz & Hspec & Hnr). cbn [cfg_ms cfg_model] in *.
      match goal with Hs : ms_svc_pending ms = Some ?x |- _ =>
        rewrite Hs in Hz; injection Hz as <- end.
      exists eff', m', evs'. split; assumption.
    + (* [comment removed for export] *)
      apply spurious_child_not_refusal, child_refusal_b_halted. cbn [cfg_model]. congruence.
    + (* [comment removed for export] *)
      apply spurious_child_not_refusal, child_refusal_b_halted. cbn [cfg_model].
      eapply killed_halted; eassumption.
  - intros [H Hns]. inversion H; subst.
    + apply sstep_cfg_instr; assumption.
    + eapply sstep_cfg_syscall; try eassumption.
      intros (Hoff & Hr & (eff' & m' & evs' & Hspec & Hnr)). apply Hns.
      match goal with
      | Hmat : materialize_model_accesses ?m' _ = Some ?m'', Hh' : m_halted ?m' = None |- _ =>
          pose proof (eq_trans (materialize_halted _ _ _ Hmat) Hh') as Hh''
      end.
      split; [| split].
      * exists x8. cbn [cfg_ms]. split; assumption.
      * rewrite (child_refusal_b_syscall ms model x8 eff _ ltac:(assumption) Hh''). exact Hr.
      * exists x8, eff', m', evs'. cbn [cfg_ms cfg_model]. repeat split; assumption.
    + eapply sstep_cfg_exit; eassumption.
    + eapply sstep_cfg_killed; eassumption.
Qed.

(* [comment removed for export] *)
Theorem sstep_cfg_of_sstep_on : forall c e st,
  pending_on c -> sstep segs c e st -> sstep_cfg segs cfg c e st.
Proof.
  intros c e st Hon H. destruct H.
  - apply sstep_cfg_instr; assumption.
  - apply sstep_cfg_instr_fault; assumption.
  - apply sstep_cfg_instr_unmodeled; assumption.
  - eapply sstep_cfg_syscall; try eassumption.
    apply spurious_refusal_family_on. apply (Hon x8). assumption.
  - eapply sstep_cfg_syscall_materialization_fault; try eassumption.
    apply spurious_refusal_family_on. apply (Hon x8). assumption.
  - eapply sstep_cfg_exit; eassumption.
  - eapply sstep_cfg_killed; eassumption.
  - eapply sstep_cfg_syscall_unmodeled; eassumption.
Qed.

Corollary sstep_cfg_iff_on : forall c e st,
  pending_on c -> (sstep_cfg segs cfg c e st <-> sstep segs c e st).
Proof.
  intros c e st Hon. split; [apply sstep_cfg_sub | apply sstep_cfg_of_sstep_on; exact Hon].
Qed.

(* [comment removed for export] *)
Corollary sstep_cfg_iff_instr : forall c e st,
  ms_svc_pending (cfg_ms c) = None ->
  (sstep_cfg segs cfg c e st <-> sstep segs c e st).
Proof. intros c e st H. apply sstep_cfg_iff_on, pending_on_no_svc, H. Qed.

(* [comment removed for export] *)
Corollary sstep_cfg_of_sstep_nonrefusal : forall c e c',
  sstep segs c e (SNext c') -> child_refusal_b c c' = false ->
  sstep_cfg segs cfg c e (SNext c').
Proof.
  intros c e c' H Hr. apply sstep_cfg_next_iff. split; [exact H |].
  apply spurious_child_not_refusal, Hr.
Qed.

(* [comment removed for export] *)
Lemma halted_pending_on_irrelevant : forall c e st,
  sstep segs c e st -> m_halted (cfg_model c) = None.
Proof. intros c e st H; inversion H; subst; cbn; assumption. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition node_ok_u (c : config) (I : Type)
    (evs : I -> list event) (nx : I -> config) : Prop :=
  (forall i, sstep segs c (evs i) (SNext (nx i)))
  /\ (forall e st, sstep segs c e st -> exists i, e = evs i /\ st = SNext (nx i)).

(* [comment removed for export] *)
Definition node_ok_c (c : config) (I : Type)
    (evs : I -> list event) (nx : I -> config) : Prop :=
  (forall i, sstep_cfg segs cfg c (evs i) (SNext (nx i)))
  /\ (forall e st, sstep_cfg segs cfg c e st -> exists i, e = evs i /\ st = SNext (nx i)).

(* [comment removed for export] *)
Lemma node_ok_c_reindex : forall c (I J : Type) evs nx (f : J -> I),
  node_ok_c c I evs nx ->
  (forall i, exists j, evs (f j) = evs i /\ nx (f j) = nx i) ->
  node_ok_c c J (fun j => evs (f j)) (fun j => nx (f j)).
Proof.
  intros c I J evs nx f [Hc Hs] Hsurj. split.
  - intros j. apply Hc.
  - intros e st H. destruct (Hs e st H) as (i & -> & ->).
    destruct (Hsurj i) as (j & He & Hn). exists j. rewrite He, Hn. split; reflexivity.
Qed.

Lemma node_ok_c_ext : forall c (I : Type) evs nx evs' nx',
  node_ok_c c I evs nx ->
  (forall i, evs' i = evs i) -> (forall i, nx' i = nx i) ->
  node_ok_c c I evs' nx'.
Proof.
  intros c I evs nx evs' nx' [Hc Hs] He Hn. split.
  - intros i. rewrite He, Hn. apply Hc.
  - intros e st H. destruct (Hs e st H) as (i & -> & ->). exists i.
    rewrite He, Hn. split; reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Theorem node_transfer_gen : forall c (I J : Type) evs nx (f : J -> I),
  node_ok_u c I evs nx ->
  (forall j, ~ spurious_child c (nx (f j))) ->
  (forall i, ~ spurious_child c (nx i) -> exists j, evs (f j) = evs i /\ nx (f j) = nx i) ->
  node_ok_c c J (fun j => evs (f j)) (fun j => nx (f j)).
Proof.
  intros c I J evs nx f [Hc Hs] Hkeep Hsurj. split.
  - intros j. apply sstep_cfg_next_iff. split; [apply Hc | apply Hkeep].
  - intros e st H.
    destruct (Hs e st (sstep_cfg_sub segs cfg _ _ _ H)) as (i & -> & ->).
    apply sstep_cfg_next_iff in H. destruct H as [_ Hns].
    destruct (Hsurj i Hns) as (j & He & Hn). exists j. rewrite He, Hn. split; reflexivity.
Qed.

(* [comment removed for export] *)
Theorem node_transfer_on : forall c (I : Type) evs nx,
  pending_on c -> node_ok_u c I evs nx -> node_ok_c c I evs nx.
Proof.
  intros c I evs nx Hon [Hc Hs]. split.
  - intros i. apply sstep_cfg_of_sstep_on; [exact Hon | apply Hc].
  - intros e st H. exact (Hs e st (sstep_cfg_sub segs cfg _ _ _ H)).
Qed.

(* [comment removed for export] *)
Lemma nonrefusal_outcome_of_child : forall c e c',
  sstep segs c e (SNext c') ->
  pending_off c ->
  m_halted (cfg_model c') = None ->
  child_refusal_b c c' = false ->
  nonrefusal_outcome c.
Proof.
  intros c e c' H (y8 & Hy & _) Hh' Hr. inversion H; subst; cbn [cfg_ms cfg_model] in *.
  - congruence.
  - match goal with
    | Hmat : materialize_model_accesses ?m' _ = Some ?m'', Hhm : m_halted ?m' = None |- _ =>
        pose proof (eq_trans (materialize_halted _ _ _ Hmat) Hhm) as Hh''
    end.
    rewrite (child_refusal_b_syscall ms model x8 eff _ ltac:(assumption) Hh'') in Hr.
    exists x8, eff, model', e. cbn [cfg_ms cfg_model]. repeat split; assumption.
  - congruence.
  - exfalso. eapply killed_halted; eassumption.
Qed.

(* [comment removed for export] *)
Lemma nonrefusal_child_of_outcome : forall c (I : Type) evs nx,
  node_ok_u c I evs nx ->
  m_halted (cfg_model c) = None ->
  (forall i, m_halted (cfg_model (nx i)) = None) ->
  nonrefusal_outcome c ->
  exists i, child_refusal_b c (nx i) = false.
Proof.
  intros [ms model] I evs nx [Hc Hs] Hh Hunh (x8 & eff' & m' & evs' & Hsvc & Hspec & Hnr).
  cbn [cfg_ms cfg_model] in *.
  destruct (m_killed m') as [sig |] eqn:Hk.
  { (* [comment removed for export] *)
    exfalso.
    destruct (Hs _ _ (sstep_killed segs ms model x8 eff' m' evs' sig Hh Hsvc Hspec Hk))
      as (i & _ & Hi).
    injection Hi as Hi. pose proof (Hunh i) as Hu. rewrite <- Hi in Hu. cbn [cfg_model] in Hu.
    exact (killed_halted m' sig Hk Hu). }
  destruct (m_halted m') as [code |] eqn:Hh'.
  { (* [comment removed for export] *)
    exfalso.
    destruct (Hs _ _ (sstep_exit segs ms model x8 eff' m' evs' code Hh Hsvc Hspec Hh' Hk))
      as (i & _ & Hi).
    injection Hi as Hi. pose proof (Hunh i) as Hu. rewrite <- Hi in Hu. cbn [cfg_model] in Hu.
    congruence. }
  destruct (materialize_model_accesses m' (syscall_effect_accesses eff')) as [m'' |] eqn:Hmat.
  - destruct (Hs _ _ (sstep_syscall segs ms model x8 eff' m' m'' evs' Hh Hsvc Hspec Hh' Hmat))
      as (i & _ & Hi).
    injection Hi as Hi. exists i. rewrite <- Hi.
    rewrite (child_refusal_b_syscall ms model x8 eff' m'' Hsvc
               (eq_trans (materialize_halted _ _ _ Hmat) Hh')).
    exact Hnr.
  - exfalso.
    destruct (Hs _ _ (sstep_syscall_materialization_fault segs ms model x8 eff' m' evs'
                        Hh Hsvc Hspec Hh' Hmat)) as (i & _ & Hi).
    discriminate Hi.
Qed.

(* [comment removed for export] *)
Theorem node_transfer_sub : forall c (I J : Type) evs nx (f : J -> I) (j0 : J),
  node_ok_u c I evs nx ->
  pending_off c ->
  (forall j, child_refusal_b c (nx (f j)) = false) ->
  m_halted (cfg_model (nx (f j0))) = None ->
  (forall i, child_refusal_b c (nx i) = false ->
     exists j, evs (f j) = evs i /\ nx (f j) = nx i) ->
  node_ok_c c J (fun j => evs (f j)) (fun j => nx (f j)).
Proof.
  intros c I J evs nx f j0 Hnode Hoff Hkeep Hh0 Hsurj.
  apply (node_transfer_gen c I J evs nx f Hnode).
  - intros j. apply spurious_child_not_refusal, Hkeep.
  - intros i Hns. apply Hsurj.
    destruct (child_refusal_b c (nx i)) eqn:Hr; [| reflexivity].
    exfalso. apply Hns. split; [exact Hoff | split; [exact Hr |]].
    exact (nonrefusal_outcome_of_child c (evs (f j0)) (nx (f j0))
             (proj1 Hnode (f j0)) Hoff Hh0 (Hkeep j0)).
Qed.

(* [comment removed for export] *)
Theorem node_transfer_sig : forall c (I : Type) evs nx (i0 : I),
  node_ok_u c I evs nx ->
  pending_off c ->
  child_refusal_b c (nx i0) = false ->
  m_halted (cfg_model (nx i0)) = None ->
  node_ok_c c {i : I | child_refusal_b c (nx i) = false}
            (fun j => evs (proj1_sig j)) (fun j => nx (proj1_sig j)).
Proof.
  intros c I evs nx i0 Hnode Hoff Hr0 Hh0.
  apply (node_transfer_sub c I {i : I | child_refusal_b c (nx i) = false} evs nx
           (@proj1_sig _ _) (exist _ i0 Hr0) Hnode Hoff).
  - intros [i Hi]. exact Hi.
  - exact Hh0.
  - intros i Hi. exists (exist _ i Hi). split; reflexivity.
Qed.

(* [comment removed for export] *)
Theorem node_transfer_sum_r : forall c (IA IB : Type) evs nx (b0 : IB),
  node_ok_u c (IA + IB) evs nx ->
  pending_off c ->
  (forall a, child_refusal_b c (nx (inl a)) = true) ->
  (forall b, child_refusal_b c (nx (inr b)) = false) ->
  m_halted (cfg_model (nx (inr b0))) = None ->
  node_ok_c c IB (fun b => evs (inr b)) (fun b => nx (inr b)).
Proof.
  intros c IA IB evs nx b0 Hnode Hoff HA HB Hh0.
  apply (node_transfer_sub c (IA + IB) IB evs nx inr b0 Hnode Hoff HB Hh0).
  intros [a | b] Hi.
  - rewrite HA in Hi. discriminate Hi.
  - exists b. split; reflexivity.
Qed.

Theorem node_transfer_sum_l : forall c (IA IB : Type) evs nx (a0 : IA),
  node_ok_u c (IA + IB) evs nx ->
  pending_off c ->
  (forall a, child_refusal_b c (nx (inl a)) = false) ->
  (forall b, child_refusal_b c (nx (inr b)) = true) ->
  m_halted (cfg_model (nx (inl a0))) = None ->
  node_ok_c c IA (fun a => evs (inl a)) (fun a => nx (inl a)).
Proof.
  intros c IA IB evs nx a0 Hnode Hoff HA HB Hh0.
  apply (node_transfer_sub c (IA + IB) IA evs nx inl a0 Hnode Hoff HA Hh0).
  intros [a | b] Hi.
  - exists a. split; reflexivity.
  - rewrite HB in Hi. discriminate Hi.
Qed.

(* [comment removed for export] *)
Theorem node_transfer_all_refusals : forall c (I : Type) evs nx,
  node_ok_u c I evs nx ->
  (forall i, m_halted (cfg_model (nx i)) = None) ->
  (forall i, child_refusal_b c (nx i) = true) ->
  node_ok_c c I evs nx.
Proof.
  intros c I evs nx Hnode Hunh Hall.
  apply (node_ok_c_ext c I (fun i => evs ((fun x => x) i)) (fun i => nx ((fun x => x) i)));
    [| reflexivity | reflexivity].
  apply (node_transfer_gen c I I evs nx (fun x => x) Hnode).
  - intros i (_ & _ & Hex).
    pose proof (halted_pending_on_irrelevant _ _ _ (proj1 Hnode i)) as Hh.
    destruct (nonrefusal_child_of_outcome c I evs nx Hnode Hh Hunh Hex) as (j & Hj).
    rewrite Hall in Hj. discriminate Hj.
  - intros i _. exists i. split; reflexivity.
Qed.

(* [comment removed for export] *)
Theorem node_transfer_no_refusals : forall c (I : Type) evs nx,
  node_ok_u c I evs nx ->
  (forall i, child_refusal_b c (nx i) = false) ->
  node_ok_c c I evs nx.
Proof.
  intros c I evs nx Hnode Hnr.
  apply (node_ok_c_ext c I (fun i => evs ((fun x => x) i)) (fun i => nx ((fun x => x) i)));
    [| reflexivity | reflexivity].
  apply (node_transfer_gen c I I evs nx (fun x => x) Hnode).
  - intros i. apply spurious_child_not_refusal, Hnr.
  - intros i _. exists i. split; reflexivity.
Qed.

(* [comment removed for export] *)
Theorem node_transfer_exact : forall c (I : Type) evs nx,
  node_ok_u c I evs nx ->
  pending_off c ->
  (forall i, m_halted (cfg_model (nx i)) = None) ->
  node_ok_c c {i : I | child_refusal_b c (nx i) = false
                       \/ (forall j, child_refusal_b c (nx j) = true)}
            (fun k => evs (proj1_sig k)) (fun k => nx (proj1_sig k)).
Proof.
  intros c I evs nx Hnode Hoff Hunh.
  apply (node_transfer_gen c I _ evs nx (@proj1_sig _ _) Hnode).
  - intros [i [Hi | Hall]]; cbn [proj1_sig].
    + apply spurious_child_not_refusal, Hi.
    + intros (_ & _ & Hex).
      pose proof (halted_pending_on_irrelevant _ _ _ (proj1 Hnode i)) as Hh.
      destruct (nonrefusal_child_of_outcome c I evs nx Hnode Hh Hunh Hex) as (j & Hj).
      rewrite Hall in Hj. discriminate Hj.
  - intros i Hns.
    assert (Hi : child_refusal_b c (nx i) = false
                 \/ (forall j, child_refusal_b c (nx j) = true)).
    { destruct (child_refusal_b c (nx i)) eqn:Hr; [right | left; reflexivity].
      intros j. destruct (child_refusal_b c (nx j)) eqn:Hj; [reflexivity |].
      exfalso. apply Hns. split; [exact Hoff | split; [exact Hr |]].
      exact (nonrefusal_outcome_of_child c (evs j) (nx j) (proj1 Hnode j) Hoff (Hunh j) Hj). }
    exists (exist _ i Hi). split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma refusal_child_not_cfg_step : forall c e c' e0 c0,
  pending_off c ->
  child_refusal_b c c' = true ->
  sstep segs c e0 (SNext c0) ->
  m_halted (cfg_model c0) = None ->
  child_refusal_b c c0 = false ->
  ~ sstep_cfg segs cfg c e (SNext c').
Proof.
  intros c e c' e0 c0 Hoff Hr H0 Hh0 Hr0 H.
  apply sstep_cfg_next_iff in H. destruct H as [_ Hns]. apply Hns.
  split; [exact Hoff | split; [exact Hr |]].
  exact (nonrefusal_outcome_of_child c e0 c0 H0 Hoff Hh0 Hr0).
Qed.

End WithSegs.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma pending_on_alloc_only : forall segs cfg ms model x8,
  alloc_only_off cfg ->
  ms_svc_pending ms = Some x8 ->
  alloc_no_b (bv_unsigned x8) = false ->
  pending_on segs cfg (mkCfg ms model).
Proof.
  intros segs cfg ms model x8 Hcfg Hsvc Hno.
  apply (pending_on_sysno segs cfg ms model x8 (bv_unsigned x8) Hsvc eq_refl).
  rewrite (family_off_no_alloc_only cfg _ Hcfg). exact Hno.
Qed.

Lemma pending_off_alloc_only : forall segs cfg ms model x8,
  alloc_only_off cfg ->
  ms_svc_pending ms = Some x8 ->
  alloc_no_b (bv_unsigned x8) = true ->
  pending_off segs cfg (mkCfg ms model).
Proof.
  intros segs cfg ms model x8 Hcfg Hsvc Hno.
  apply (pending_off_sysno segs cfg ms model x8 (bv_unsigned x8) Hsvc eq_refl).
  rewrite (family_off_no_alloc_only cfg _ Hcfg). exact Hno.
Qed.

(* [comment removed for export] *)

Lemma refusal_b_mmap : forall i m r,
  bv_unsigned (in_sysno i) = 222%Z -> refusal_b i m r = ret_in_errnos mmap_errnos r.
Proof. intros i m r H. unfold refusal_b. rewrite H. reflexivity. Qed.

Lemma refusal_b_mprotect : forall i m r,
  bv_unsigned (in_sysno i) = 226%Z -> refusal_b i m r = ret_in_errnos mprotect_errnos r.
Proof. intros i m r H. unfold refusal_b. rewrite H. reflexivity. Qed.

Lemma refusal_b_mremap : forall i m r,
  bv_unsigned (in_sysno i) = 216%Z -> refusal_b i m r = ret_in_errnos mremap_errnos r.
Proof. intros i m r H. unfold refusal_b. rewrite H. reflexivity. Qed.

Lemma refusal_b_brk : forall i m r,
  bv_unsigned (in_sysno i) = 214%Z -> refusal_b i m r = brk_refusal_b m (in_arg i 0) r.
Proof. intros i m r H. unfold refusal_b. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
Lemma ret_in_errnos_errno : forall es e, In e es -> ret_in_errnos es (errno_ret e) = true.
Proof.
  intros es e He. unfold ret_in_errnos. apply existsb_exists. exists e.
  split; [exact He | apply bv_eqb_eq; reflexivity].
Qed.

(* [comment removed for export] *)
Lemma errno_ret_unsigned_window : forall e,
  (1 <= e <= 4095)%Z -> bv_unsigned (errno_ret e) = (2 ^ 64 - e)%Z.
Proof.
  intros e He. unfold errno_ret. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64)%Z with (2 ^ 64)%Z.
  rewrite <- (Z.mod_add (- e) 1 (2 ^ 64)) by lia.
  rewrite Z.mod_small; lia.
Qed.

Lemma ret_in_errnos_below : forall es r,
  Forall (fun e => (1 <= e <= 4095)%Z) es ->
  (bv_unsigned r <= 2 ^ 64 - 4096)%Z ->
  ret_in_errnos es r = false.
Proof.
  intros es r Hes Hr. unfold ret_in_errnos.
  apply Bool.not_true_is_false. intros Hex. apply existsb_exists in Hex as (e & He & Heq).
  apply bv_eqb_eq in Heq. subst r.
  pose proof (proj1 (Forall_forall _ _) Hes e He) as Hrange. cbv beta in Hrange.
  rewrite (errno_ret_unsigned_window e Hrange) in Hr. lia.
Qed.

Lemma enomem_window : Forall (fun e => (1 <= e <= 4095)%Z) [ENOMEM].
Proof. constructor; [unfold ENOMEM; lia | constructor]. Qed.

Lemma refusal_b_mmap_errno : forall i m e,
  bv_unsigned (in_sysno i) = 222%Z -> In e mmap_errnos -> refusal_b i m (errno_ret e) = true.
Proof. intros i m e H He. rewrite (refusal_b_mmap i m _ H). apply ret_in_errnos_errno, He. Qed.

Lemma refusal_b_mmap_below : forall i m r,
  bv_unsigned (in_sysno i) = 222%Z -> (bv_unsigned r <= 2 ^ 64 - 4096)%Z ->
  refusal_b i m r = false.
Proof.
  intros i m r H Hr. rewrite (refusal_b_mmap i m _ H).
  apply ret_in_errnos_below; [exact enomem_window | exact Hr].
Qed.

Lemma refusal_b_mprotect_errno : forall i m e,
  bv_unsigned (in_sysno i) = 226%Z -> In e mprotect_errnos -> refusal_b i m (errno_ret e) = true.
Proof. intros i m e H He. rewrite (refusal_b_mprotect i m _ H). apply ret_in_errnos_errno, He. Qed.

Lemma refusal_b_mprotect_below : forall i m r,
  bv_unsigned (in_sysno i) = 226%Z -> (bv_unsigned r <= 2 ^ 64 - 4096)%Z ->
  refusal_b i m r = false.
Proof.
  intros i m r H Hr. rewrite (refusal_b_mprotect i m _ H).
  apply ret_in_errnos_below; [exact enomem_window | exact Hr].
Qed.

Lemma refusal_b_mremap_errno : forall i m e,
  bv_unsigned (in_sysno i) = 216%Z -> In e mremap_errnos -> refusal_b i m (errno_ret e) = true.
Proof. intros i m e H He. rewrite (refusal_b_mremap i m _ H). apply ret_in_errnos_errno, He. Qed.

Lemma refusal_b_mremap_below : forall i m r,
  bv_unsigned (in_sysno i) = 216%Z -> (bv_unsigned r <= 2 ^ 64 - 4096)%Z ->
  refusal_b i m r = false.
Proof.
  intros i m r H Hr. rewrite (refusal_b_mremap i m _ H).
  apply ret_in_errnos_below; [exact enomem_window | exact Hr].
Qed.

(* [comment removed for export] *)
Lemma child_refusal_b_set_gpr0 : forall segs ms model x8 r model',
  ms_svc_pending ms = Some x8 ->
  m_halted model' = None ->
  child_refusal_b segs (mkCfg ms model) (mkCfg (advance_past_svc (set_gpr0 ms r)) model')
  = refusal_b (sys_input segs ms x8) model r.
Proof.
  intros segs ms model x8 r model' Hsvc Hh. unfold child_refusal_b.
  cbn [cfg_ms cfg_model]. rewrite Hsvc, Hh, gpr0_after_set_gpr0. reflexivity.
Qed.

Lemma in_sysno_sys_input_eq : forall segs ms x8, in_sysno (sys_input segs ms x8) = x8.
Proof. reflexivity. Qed.

Lemma in_arg0_sys_input : forall segs ms x8, in_arg (sys_input segs ms x8) 0 = ms_gpr ms 0.
Proof. reflexivity. Qed.

(* [comment removed for export] *)

Definition kit_cfg : SpuriousCfg := base_cfg.

Lemma kit_cfg_alloc_only : alloc_only_off kit_cfg.
Proof. exact base_cfg_alloc_only_off. Qed.

Lemma kit_cfg_eq : kit_cfg = mkSpuriousCfg false true true true true true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma kit_pending_on_sysno : forall segs ms model x8 n,
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = n ->
  alloc_no_b n = false ->
  pending_on segs kit_cfg (mkCfg ms model).
Proof.
  intros segs ms model x8 n Hsvc Hn Hno.
  apply (pending_on_alloc_only segs kit_cfg ms model x8 kit_cfg_alloc_only Hsvc).
  rewrite Hn. exact Hno.
Qed.

Lemma kit_pending_off_sysno : forall segs ms model x8 n,
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = n ->
  alloc_no_b n = true ->
  pending_off segs kit_cfg (mkCfg ms model).
Proof.
  intros segs ms model x8 n Hsvc Hn Hno.
  apply (pending_off_alloc_only segs kit_cfg ms model x8 kit_cfg_alloc_only Hsvc).
  rewrite Hn. exact Hno.
Qed.

(* [comment removed for export] *)
Definition not_alloc_pending (ms : machine_state) : Prop :=
  forall x8, ms_svc_pending ms = Some x8 -> alloc_no_b (bv_unsigned x8) = false.

Lemma kit_pending_on_not_alloc : forall segs ms model,
  not_alloc_pending ms -> pending_on segs kit_cfg (mkCfg ms model).
Proof.
  intros segs ms model H x8 Hsvc. cbn [cfg_ms] in *.
  rewrite (injected_family_off_alloc_only kit_cfg _ kit_cfg_alloc_only).
  cbn [sys_input in_sysno]. exact (H x8 Hsvc).
Qed.

Lemma not_alloc_pending_none : forall ms, ms_svc_pending ms = None -> not_alloc_pending ms.
Proof. intros ms H x8 Hx. rewrite H in Hx. discriminate Hx. Qed.

Lemma not_alloc_pending_sysno : forall ms x8 n,
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = n -> alloc_no_b n = false ->
  not_alloc_pending ms.
Proof.
  intros ms x8 n Hsvc Hn Hno y8 Hy. rewrite Hsvc in Hy. injection Hy as <-.
  rewrite Hn. exact Hno.
Qed.

(* [comment removed for export] *)
Ltac kit_pending_on :=
  first
    [ apply pending_on_no_svc; cbn [cfg_ms]; first [assumption | reflexivity]
    | eapply kit_pending_on_sysno;
        [ first [eassumption | reflexivity]
        | first [eassumption | reflexivity]
        | first [reflexivity | assumption] ]
    | apply kit_pending_on_not_alloc; assumption ].

(* [comment removed for export] *)
Ltac kit_not_alloc :=
  solve
    [ reflexivity
    | match goal with
      | H : ?x = Z_to_bv 64 _ |- alloc_no_b (bv_unsigned ?x) = false => rewrite H; reflexivity
      | H : bv_unsigned ?x = _ |- alloc_no_b (bv_unsigned ?x) = false => rewrite H; reflexivity
      end
    | assumption ].
