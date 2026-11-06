From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Import ListNotations.

Definition fcfg : SpuriousCfg := alloc_only_cfg false.

Lemma fcfg_family_on : forall i,
  ~ In (bv_unsigned (in_sysno i)) alloc_mark_sysnos -> injected_family_off fcfg i = false.
Proof.
  intros i Hn. unfold injected_family_off.
  destruct (injected_arm (bv_unsigned (in_sysno i))) as [a|] eqn:E; [|reflexivity].
  destruct (ia_family a) eqn:F; try reflexivity.
  exfalso. exact (Hn (alloc_family_dispatched _ _ E F)).
Qed.

Lemma fcfg_family_off : forall i,
  In (bv_unsigned (in_sysno i)) alloc_mark_sysnos -> injected_family_off fcfg i = true.
Proof.
  intros i H. unfold injected_family_off.
  destruct H as [E|[E|[E|[E|[]]]]]; rewrite <- E; reflexivity.
Qed.

Lemma fcfg_nonalloc_nonspur : forall i m eff,
  ~ In (bv_unsigned (in_sysno i)) alloc_mark_sysnos -> ~ spurious_refusal_cfg fcfg i m eff.
Proof. intros i m eff Hn. apply spurious_refusal_family_on, fcfg_family_on, Hn. Qed.

Lemma fcfg_nonref_nonspur : forall i m eff,
  refusal_b i m (eff_ret eff) = false -> ~ spurious_refusal_cfg fcfg i m eff.
Proof. intros i m eff H. apply spurious_refusal_not_refusal. exact H. Qed.

Lemma fcfg_forced_nonspur : forall i m eff,
  (forall eff' m' evs', syscall_spec i m (Ok eff' m' evs') -> refusal_b i m (eff_ret eff') = true) ->
  ~ spurious_refusal_cfg fcfg i m eff.
Proof.
  intros i m eff H (_ & _ & (eff' & m' & evs' & Hs & Hr)).
  rewrite (H _ _ _ Hs) in Hr. discriminate Hr.
Qed.

Lemma fcfg_nonspur_refusal_forced : forall i m eff,
  In (bv_unsigned (in_sysno i)) alloc_mark_sysnos ->
  refusal_b i m (eff_ret eff) = true ->
  ~ spurious_refusal_cfg fcfg i m eff ->
  forall eff' m' evs', syscall_spec i m (Ok eff' m' evs') -> refusal_b i m (eff_ret eff') = true.
Proof.
  intros i m eff Ha Hr Hns eff' m' evs' Hs.
  destruct (refusal_b i m (eff_ret eff')) eqn:E; [reflexivity|].
  exfalso. apply Hns. split; [exact (fcfg_family_off i Ha)|]. split; [exact Hr|].
  exists eff', m', evs'. split; [exact Hs | exact E].
Qed.

Lemma fcfg_refusal_nonspur_iff : forall i m eff,
  In (bv_unsigned (in_sysno i)) alloc_mark_sysnos ->
  refusal_b i m (eff_ret eff) = true ->
  (~ spurious_refusal_cfg fcfg i m eff <->
   forall eff' m' evs', syscall_spec i m (Ok eff' m' evs') -> refusal_b i m (eff_ret eff') = true).
Proof.
  intros i m eff Ha Hr. split.
  - exact (fcfg_nonspur_refusal_forced i m eff Ha Hr).
  - apply fcfg_forced_nonspur.
Qed.

Section Steps.
Variable segs : list Segment.

Definition step_nonspur (c : config) : Prop :=
  forall x8 eff m' evs, ms_svc_pending (cfg_ms c) = Some x8 ->
    syscall_spec (sys_input segs (cfg_ms c) x8) (cfg_model c) (Ok eff m' evs) ->
    ~ spurious_refusal_cfg fcfg (sys_input segs (cfg_ms c) x8) (cfg_model c) eff.

Lemma step_nonspur_instr : forall ms m, ms_svc_pending ms = None -> step_nonspur (mkCfg ms m).
Proof. intros ms m H x8 eff m' evs Hp. cbn [cfg_ms] in Hp. congruence. Qed.

Lemma step_nonspur_nonalloc : forall ms m x8, ms_svc_pending ms = Some x8 ->
  ~ In (bv_unsigned x8) alloc_mark_sysnos -> step_nonspur (mkCfg ms m).
Proof.
  intros ms m x8 Hp Hn y8 eff m' evs Hp' _. cbn [cfg_ms cfg_model] in *.
  rewrite Hp in Hp'. injection Hp' as <-.
  apply fcfg_nonalloc_nonspur. exact Hn.
Qed.

Lemma sstep_fcfg_of_sstep : forall c e st,
  step_nonspur c -> sstep segs c e st -> sstep_cfg segs fcfg c e st.
Proof.
  intros c e st Hn H. revert Hn. unfold step_nonspur.
  destruct H; cbn [cfg_ms cfg_model]; intros Hn;
    [ eapply sstep_cfg_instr | eapply sstep_cfg_instr_fault | eapply sstep_cfg_instr_unmodeled
    | eapply sstep_cfg_syscall | eapply sstep_cfg_syscall_materialization_fault
    | eapply sstep_cfg_exit | eapply sstep_cfg_killed | eapply sstep_cfg_syscall_unmodeled ];
    eauto.
Qed.

Lemma sstep_fcfg_iff : forall c e st,
  step_nonspur c -> (sstep segs c e st <-> sstep_cfg segs fcfg c e st).
Proof.
  intros c e st Hn. split; [apply sstep_fcfg_of_sstep, Hn | apply sstep_cfg_sub].
Qed.

Definition two_sided (c : config) (I : Type) (evs : I -> list event) (nx : I -> config) : Prop :=
  (forall i, sstep segs c (evs i) (SNext (nx i)))
  /\ (forall e st, sstep segs c e st -> exists i, e = evs i /\ st = SNext (nx i)).

Definition two_sided_fcfg (c : config) (I : Type) (evs : I -> list event) (nx : I -> config) : Prop :=
  (forall i, sstep_cfg segs fcfg c (evs i) (SNext (nx i)))
  /\ (forall e st, sstep_cfg segs fcfg c e st -> exists i, e = evs i /\ st = SNext (nx i)).

Lemma two_sided_lift : forall c I evs nx,
  step_nonspur c -> two_sided c I evs nx -> two_sided_fcfg c I evs nx.
Proof.
  intros c I evs nx Hn [Hs Hc]. split.
  - intros i. apply sstep_fcfg_of_sstep; [exact Hn | apply Hs].
  - intros e st H. apply Hc, (sstep_cfg_sub segs fcfg), H.
Qed.

Lemma two_sided_lift_branches : forall c I evs nx,
  (forall i, sstep_cfg segs fcfg c (evs i) (SNext (nx i))) ->
  (forall e st, sstep segs c e st -> exists i, e = evs i /\ st = SNext (nx i)) ->
  two_sided_fcfg c I evs nx.
Proof.
  intros c I evs nx Hs Hc. split; [exact Hs|].
  intros e st H. apply Hc, (sstep_cfg_sub segs fcfg), H.
Qed.

End Steps.

Lemma nonalloc_lit : forall K, (0 <= K < 2^64)%Z ->
  existsb (Z.eqb K) alloc_mark_sysnos = false ->
  ~ In (bv_unsigned (Z_to_bv 64 K)) alloc_mark_sysnos.
Proof.
  intros K HK Hb Hin.
  rewrite Z_to_bv_unsigned, bv_wrap_small in Hin by (unfold bv_modulus; exact HK).
  assert (Ht : existsb (Z.eqb K) alloc_mark_sysnos = true).
  { apply existsb_exists. exists K. split; [exact Hin | apply Z.eqb_refl]. }
  congruence.
Qed.
