From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require RoomShapesDraft AgreeLim.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable.R Require Import Cfg.
Import ListNotations.

Ltac sys_outcome_cases H :=
  unfold err_ret, ret_only, errno_from, bind, pure, choose, alt, get_model, modify, unmodeled in H;
  cbv beta iota zeta in H;
  repeat match goal with
  | H0 : _ /\ _ |- _ => destruct H0
  | H0 : exists _, _ |- _ => destruct H0
  | H0 : _ \/ _ |- _ => destruct H0
  | H0 : Ok _ _ _ = Ok _ _ _ |- _ => injection H0; clear H0; intros; subst
  | H0 : Ok _ _ _ = Unmodeled |- _ => discriminate H0
  | H0 : Unmodeled = Ok _ _ _ |- _ => discriminate H0
  | H0 : context [if ?b then _ else _] |- _ => destruct b; cbv beta iota in H0
  end.

Ltac proc_kept FR :=
  unfold with_mmap_replacement, with_mmap_destroyed, with_mmap_backing, with_brk_next, mremap_model_next;
  cbv beta zeta;
  repeat match goal with |- context [if ?b then _ else _] => destruct b end;
  rewrite ?FR; reflexivity.

Section Uniform.
Variable segs : list Segment.

Lemma placement_events_eq : forall c x8 len e1 c1 e2 c2,
  RoomShapesDraft.placement_at segs c x8 len ->
  sstep_cfg segs ACFG c e1 (SNext c1) -> sstep_cfg segs ACFG c e2 (SNext c2) -> e1 = e2.
Proof.
  assert (FR : forall l m0, m_proc (forget_vm_ranges l m0) = m_proc m0).
  { induction l as [|[a n] l IH]; intros m0; [reflexivity|]. cbn [forget_vm_ranges]. rewrite IH. reflexivity. }
  assert (Q : forall i m len eff m' evs, RoomShapesDraft.placement_len i m = Some len ->
      syscall_spec i m (Ok eff m' evs) -> evs = [] /\ m_proc m' = m_proc m).
  { intros i m len eff m' evs Hl Hs.
    unfold RoomShapesDraft.placement_len in Hl. cbv zeta in Hl. revert Hl Hs.
    destruct (Z.eqb_spec (bv_unsigned (in_sysno i)) 222) as [E|_].
    - intros _ Hs.
      assert (Hm : mmap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5)
          i m (Ok eff m' evs)).
      { revert Hs. unfold syscall_spec, dispatch. cbv beta. rewrite E. intro H. exact H. }
      clear Hs. unfold mmap_spec in Hm. sys_outcome_cases Hm; (split; [reflexivity | proc_kept FR]).
    - destruct (Z.eqb_spec (bv_unsigned (in_sysno i)) 216) as [E|_].
      + intros _ Hs.
        assert (Hm : mremap_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i m (Ok eff m' evs)).
        { revert Hs. unfold syscall_spec, dispatch. cbv beta. rewrite E. intro H. exact H. }
        clear Hs. unfold mremap_spec in Hm. sys_outcome_cases Hm; (split; [reflexivity | proc_kept FR]).
      + destruct (Z.eqb_spec (bv_unsigned (in_sysno i)) 214) as [E|_]; [| intros Hl; discriminate Hl].
        intros _ Hs.
        assert (Hm : brk_spec (in_arg i 0) i m (Ok eff m' evs)).
        { revert Hs. unfold syscall_spec, dispatch. cbv beta. rewrite E. intro H. exact H. }
        clear Hs. unfold brk_spec in Hm. sys_outcome_cases Hm; (split; [reflexivity | proc_kept FR]). }
  assert (S : forall ms md x8 len e c', m_halted md = None -> ms_svc_pending ms = Some x8 ->
      RoomShapesDraft.placement_len (sys_input segs ms x8) md = Some len ->
      sstep_cfg segs ACFG (mkCfg ms md) e (SNext c') -> e = []).
  { intros ms md x8 len e c' Hh Hsvc Hl Hs.
    inversion Hs; subst; rewrite Hsvc in *;
      repeat match goal with
      | Hp : Some _ = Some _ |- _ => injection Hp; clear Hp; intros; subst
      | Hp : Some _ = None |- _ => discriminate Hp
      end.
    - match goal with HS : syscall_spec _ _ (Ok _ _ _) |- _ => exact (proj1 (Q _ _ _ _ _ _ Hl HS)) end.
    - exfalso.
      match goal with HS : syscall_spec _ _ (Ok _ ?md' _), HH : m_halted ?md' = Some _ |- _ =>
        destruct (Q _ _ _ _ _ _ Hl HS) as [_ EP]; unfold m_halted in HH, Hh; rewrite EP in HH; congruence end.
    - exfalso.
      match goal with HS : syscall_spec _ _ (Ok _ ?md' _), HK : m_killed ?md' = Some _ |- _ =>
        destruct (Q _ _ _ _ _ _ Hl HS) as [_ EP]; pose proof (m_killed_of_m_halted_none _ Hh) as K;
        unfold m_killed in HK, K; rewrite EP in HK; congruence end. }
  intros [ms md] x8 len e1 c1 e2 c2 (Hh & Hsvc & Hl) H1 H2.
  cbn [cfg_ms cfg_model] in Hh, Hsvc, Hl.
  rewrite (S ms md x8 len e1 c1 Hh Hsvc Hl H1), (S ms md x8 len e2 c2 Hh Hsvc Hl H2). reflexivity.
Qed.

Definition place_uniform (c : config) : Prop :=
  forall x8 len, RoomShapesDraft.placement_at segs c x8 len ->
  forall e1 c1 e2 c2, sstep_cfg segs ACFG c e1 (SNext c1) -> sstep_cfg segs ACFG c e2 (SNext c2) ->
    e1 = e2 /\ (forall tr, obs_trace_cfg segs ACFG c1 tr <-> obs_trace_cfg segs ACFG c2 tr).

Definition canon_fit_at (c : config) : Prop :=
  forall p s st, RoomShapesDraft.policy_ok p ->
  (page_round_down_Z (alloc_top (m_vmmaps (cfg_model c))) <= st)%Z ->
  (vm_limit (m_vmmaps (cfg_model c)) <= AgreeLim.LIM_AG)%Z ->
  forall x8 len, RoomShapesDraft.placement_at segs c x8 len ->
  (exists evs c', sstep_cfg segs ACFG c evs (SNext c')) ->
  RoomShapesDraft.canon_can_step p s st segs ACFG c.

Definition uniform (c : config) : Prop :=
  forall tr c', star_cfg segs ACFG c tr c' -> place_uniform c' /\ canon_fit_at c'.

Lemma uniform_here : forall c, uniform c -> place_uniform c.
Proof. intros c H. exact (proj1 (H [] c (star_cfg_refl segs ACFG c))). Qed.

Lemma uniform_fit_here : forall c, uniform c -> canon_fit_at c.
Proof. intros c H. exact (proj2 (H [] c (star_cfg_refl segs ACFG c))). Qed.

Lemma uniform_place : forall c tr c', uniform c -> star_cfg segs ACFG c tr c' -> place_uniform c'.
Proof. intros c tr c' H Hs. exact (proj1 (H tr c' Hs)). Qed.

Lemma uniform_fit : forall c tr c', uniform c -> star_cfg segs ACFG c tr c' -> canon_fit_at c'.
Proof. intros c tr c' H Hs. exact (proj2 (H tr c' Hs)). Qed.

Lemma uniform_step : forall c e c', uniform c -> sstep_cfg segs ACFG c e (SNext c') -> uniform c'.
Proof.
  intros c e c' H Hs tr c'' Hstar. apply (H (e ++ tr) c''). eapply star_cfg_step; [exact Hs | exact Hstar].
Qed.

Lemma uniform_intro : forall c, place_uniform c -> canon_fit_at c ->
  (forall e c', sstep_cfg segs ACFG c e (SNext c') -> uniform c') -> uniform c.
Proof.
  intros c Hp Hf Hs tr c' Hstar.
  inversion Hstar as [c0 | c1 evs c2 tr' c3 Hst Hstar']; subst; [exact (conj Hp Hf) | exact (Hs evs c2 Hst tr' c' Hstar')].
Qed.

Lemma uniform_placement : forall c, place_uniform c -> canon_fit_at c ->
  (forall e c', sstep_cfg segs ACFG c e (SNext c') -> uniform c') -> uniform c.
Proof. exact uniform_intro. Qed.

Lemma place_uniform_nonplacement : forall c,
  (forall x8 len, ~ RoomShapesDraft.placement_at segs c x8 len) -> place_uniform c.
Proof. intros c Hn x8 len Hp. exfalso. exact (Hn x8 len Hp). Qed.

Lemma canon_fit_at_nonplacement : forall c,
  (forall x8 len, ~ RoomShapesDraft.placement_at segs c x8 len) -> canon_fit_at c.
Proof. intros c Hn p s st _ _ _ x8 len Hp. exfalso. exact (Hn x8 len Hp). Qed.

Lemma uniform_nonplacement : forall c,
  (forall x8 len, ~ RoomShapesDraft.placement_at segs c x8 len) ->
  (forall e c', sstep_cfg segs ACFG c e (SNext c') -> uniform c') -> uniform c.
Proof.
  intros c Hn Hs. exact (uniform_intro c (place_uniform_nonplacement c Hn) (canon_fit_at_nonplacement c Hn) Hs).
Qed.

Lemma instr_not_placement : forall ms md x8 len,
  ms_svc_pending ms = None -> ~ RoomShapesDraft.placement_at segs (mkCfg ms md) x8 len.
Proof. intros ms md x8 len Hn (_ & Hs & _). cbn [cfg_ms] in Hs. congruence. Qed.

Lemma halted_not_placement : forall c x8 len,
  m_halted (cfg_model c) <> None -> ~ RoomShapesDraft.placement_at segs c x8 len.
Proof. intros c x8 len Hh (Hn & _). exact (Hh Hn). Qed.

Lemma nonalloc_not_placement : forall ms md x8 y8 len,
  ms_svc_pending ms = Some x8 -> alloc_no_b (bv_unsigned x8) = false ->
  ~ RoomShapesDraft.placement_at segs (mkCfg ms md) y8 len.
Proof.
  intros ms md x8 y8 len Hsvc Hno (_ & Hs & Hl). cbn [cfg_ms cfg_model] in Hs, Hl.
  rewrite Hsvc in Hs. injection Hs as <-.
  unfold RoomShapesDraft.placement_len in Hl. cbv zeta in Hl.
  change (in_sysno (sys_input segs ms x8)) with x8 in Hl. revert Hl.
  destruct (Z.eqb_spec (bv_unsigned x8) 222) as [E|_]; [rewrite E in Hno; vm_compute in Hno; discriminate Hno|].
  destruct (Z.eqb_spec (bv_unsigned x8) 216) as [E|_]; [rewrite E in Hno; vm_compute in Hno; discriminate Hno|].
  destruct (Z.eqb_spec (bv_unsigned x8) 214) as [E|_]; [rewrite E in Hno; vm_compute in Hno; discriminate Hno|].
  intros Hl. discriminate Hl.
Qed.

Lemma uniform_halted : forall c, m_halted (cfg_model c) <> None -> uniform c.
Proof.
  intros c Hh tr c' Hstar. destruct (star_cfg_halted_nil segs ACFG c tr c' Hh Hstar) as [_ ->].
  split; [apply place_uniform_nonplacement | apply canon_fit_at_nonplacement];
    intros x8 len; exact (halted_not_placement c x8 len Hh).
Qed.

End Uniform.
