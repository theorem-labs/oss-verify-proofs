(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma injected_arm_214 : injected_arm 214 = Some (mkInjectedArm 214 FamAlloc []).
Proof. reflexivity. Qed.
Lemma injected_arm_216 : injected_arm 216 = Some (mkInjectedArm 216 FamAlloc mremap_errnos).
Proof. reflexivity. Qed.
Lemma injected_arm_222 : injected_arm 222 = Some (mkInjectedArm 222 FamAlloc mmap_errnos).
Proof. reflexivity. Qed.
Lemma injected_arm_226 : injected_arm 226 = Some (mkInjectedArm 226 FamAlloc mprotect_errnos).
Proof. reflexivity. Qed.
Lemma injected_arm_56 : injected_arm 56 = Some (mkInjectedArm 56 FamFs openat_errnos).
Proof. reflexivity. Qed.

Lemma injected_arm_29 : injected_arm 29 = None.   Proof. reflexivity. Qed.
Lemma injected_arm_57 : injected_arm 57 = None.   Proof. reflexivity. Qed.
Lemma injected_arm_63 : injected_arm 63 = None.   Proof. reflexivity. Qed.
Lemma injected_arm_64 : injected_arm 64 = None.   Proof. reflexivity. Qed.
Lemma injected_arm_66 : injected_arm 66 = None.   Proof. reflexivity. Qed.
Lemma injected_arm_93 : injected_arm 93 = None.   Proof. reflexivity. Qed.
Lemma injected_arm_94 : injected_arm 94 = None.   Proof. reflexivity. Qed.
Lemma injected_arm_96 : injected_arm 96 = None.   Proof. reflexivity. Qed.
Lemma injected_arm_215 : injected_arm 215 = None. Proof. reflexivity. Qed.

Lemma ret_in_errnos_1 : forall e r, ret_in_errnos [e] r = bv_eqb r (errno_ret e).
Proof. intros e r. unfold ret_in_errnos. cbn [existsb]. apply orb_false_r. Qed.

Lemma ret_in_errnos_nil : forall r, ret_in_errnos [] r = false.
Proof. reflexivity. Qed.

Lemma injected_family_off_none : forall cfg i,
  injected_arm (bv_unsigned (in_sysno i)) = None ->
  injected_family_off cfg i = false.
Proof. intros cfg i H. unfold injected_family_off. rewrite H. reflexivity. Qed.

Lemma injected_family_off_some : forall cfg i a,
  injected_arm (bv_unsigned (in_sysno i)) = Some a ->
  injected_family_off cfg i = negb (family_may_fail cfg (ia_family a)).
Proof. intros cfg i a H. unfold injected_family_off. rewrite H. reflexivity. Qed.

Lemma refusal_b_none : forall i m r,
  injected_arm (bv_unsigned (in_sysno i)) = None ->
  refusal_b i m r = false.
Proof.
  intros i m r H. unfold refusal_b.
  destruct (Z.eqb (bv_unsigned (in_sysno i)) 214) eqn:E.
  - apply Z.eqb_eq in E. rewrite E in H. rewrite injected_arm_214 in H. discriminate H.
  - rewrite H. reflexivity.
Qed.

Lemma refusal_b_errnos : forall i m r a,
  bv_unsigned (in_sysno i) <> 214%Z ->
  injected_arm (bv_unsigned (in_sysno i)) = Some a ->
  refusal_b i m r = ret_in_errnos (ia_errnos a) r.
Proof.
  intros i m r a Hne H. unfold refusal_b.
  destruct (Z.eqb (bv_unsigned (in_sysno i)) 214) eqn:E.
  - apply Z.eqb_eq in E. contradiction.
  - rewrite H. reflexivity.
Qed.

Lemma refusal_b_brk : forall i m r,
  bv_unsigned (in_sysno i) = 214%Z ->
  refusal_b i m r = brk_refusal_b m (in_arg i 0) r.
Proof. intros i m r H. unfold refusal_b. rewrite H. reflexivity. Qed.

Lemma refusal_b_mmap : forall i m r,
  bv_unsigned (in_sysno i) = 222%Z ->
  refusal_b i m r = bv_eqb r (errno_ret ENOMEM).
Proof.
  intros i m r H. rewrite (refusal_b_errnos i m r (mkInjectedArm 222 FamAlloc mmap_errnos));
    [| rewrite H; discriminate | rewrite H; exact injected_arm_222].
  cbn [ia_errnos]. unfold mmap_errnos. apply ret_in_errnos_1.
Qed.

Lemma refusal_b_mprotect : forall i m r,
  bv_unsigned (in_sysno i) = 226%Z ->
  refusal_b i m r = bv_eqb r (errno_ret ENOMEM).
Proof.
  intros i m r H. rewrite (refusal_b_errnos i m r (mkInjectedArm 226 FamAlloc mprotect_errnos));
    [| rewrite H; discriminate | rewrite H; exact injected_arm_226].
  cbn [ia_errnos]. unfold mprotect_errnos. apply ret_in_errnos_1.
Qed.

Lemma injected_family_off_alloc : forall cfg i n,
  bv_unsigned (in_sysno i) = n ->
  (n = 214 \/ n = 216 \/ n = 222 \/ n = 226)%Z ->
  injected_family_off cfg i = negb (sc_alloc cfg).
Proof.
  intros cfg i n Hn Hcases. unfold injected_family_off. rewrite Hn.
  destruct Hcases as [-> | [-> | [-> | ->]]];
    [ rewrite injected_arm_214 | rewrite injected_arm_216
    | rewrite injected_arm_222 | rewrite injected_arm_226 ]; reflexivity.
Qed.

Lemma injected_family_off_openat : forall cfg i,
  bv_unsigned (in_sysno i) = 56%Z ->
  injected_family_off cfg i = negb (sc_fs cfg).
Proof.
  intros cfg i Hn. unfold injected_family_off. rewrite Hn, injected_arm_56. reflexivity.
Qed.

Lemma not_spurious_on : forall cfg i m eff,
  injected_family_off cfg i = false -> ~ spurious_refusal_cfg cfg i m eff.
Proof. exact spurious_refusal_family_on. Qed.

Lemma not_spurious_nonrefusal : forall cfg i m eff,
  refusal_b i m (eff_ret eff) = false -> ~ spurious_refusal_cfg cfg i m eff.
Proof. exact spurious_refusal_not_refusal. Qed.

Lemma not_spurious_forced : forall cfg i m eff,
  (forall eff' m' evs', syscall_spec i m (Ok eff' m' evs') ->
     refusal_b i m (eff_ret eff') = true) ->
  ~ spurious_refusal_cfg cfg i m eff.
Proof.
  intros cfg i m eff Hall (_ & _ & eff' & m' & evs' & Hspec & Hnr).
  rewrite (Hall eff' m' evs' Hspec) in Hnr. discriminate Hnr.
Qed.

Lemma spurious_intro : forall cfg i m eff eff1 m1 evs1,
  injected_family_off cfg i = true ->
  refusal_b i m (eff_ret eff) = true ->
  syscall_spec i m (Ok eff1 m1 evs1) ->
  refusal_b i m (eff_ret eff1) = false ->
  spurious_refusal_cfg cfg i m eff.
Proof.
  intros cfg i m eff eff1 m1 evs1 Hoff Hr Hspec Hnr.
  split; [exact Hoff|]. split; [exact Hr|]. exists eff1, m1, evs1. split; assumption.
Qed.

Section WithSegs.
Variable segs : list Segment.
Variable scfg : SpuriousCfg.

Definition fam_on (ms : machine_state) : Prop :=
  forall x8, ms_svc_pending ms = Some x8 ->
    injected_family_off scfg (sys_input segs ms x8) = false.

Lemma fam_on_instr : forall ms, ms_svc_pending ms = None -> fam_on ms.
Proof. intros ms H x8 Hx. rewrite H in Hx. discriminate Hx. Qed.

Lemma fam_on_none : forall ms x8,
  ms_svc_pending ms = Some x8 ->
  injected_arm (bv_unsigned x8) = None ->
  fam_on ms.
Proof.
  intros ms x8 Hsvc Harm y Hy. rewrite Hsvc in Hy. injection Hy as <-.
  unfold injected_family_off. change (in_sysno (sys_input segs ms x8)) with x8.
  rewrite Harm. reflexivity.
Qed.

Lemma fam_on_sysno : forall ms x8 n,
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = n ->
  injected_arm n = None ->
  fam_on ms.
Proof. intros ms x8 n Hsvc <- Harm. exact (fam_on_none ms x8 Hsvc Harm). Qed.

Lemma fam_on_mayfail : forall ms x8 a,
  ms_svc_pending ms = Some x8 ->
  injected_arm (bv_unsigned x8) = Some a ->
  family_may_fail scfg (ia_family a) = true ->
  fam_on ms.
Proof.
  intros ms x8 a Hsvc Harm Hfam y Hy. rewrite Hsvc in Hy. injection Hy as <-.
  unfold injected_family_off. change (in_sysno (sys_input segs ms x8)) with x8.
  rewrite Harm, Hfam. reflexivity.
Qed.

Lemma fam_on_openat : forall ms x8,
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 56%Z ->
  sc_fs scfg = true ->
  fam_on ms.
Proof.
  intros ms x8 Hsvc Hno Hfs.
  apply (fam_on_mayfail ms x8 (mkInjectedArm 56 FamFs openat_errnos) Hsvc);
    [rewrite Hno; exact injected_arm_56 | exact Hfs].
Qed.

Lemma fam_on_exit : forall ms x8,
  ms_svc_pending ms = Some x8 -> (bv_unsigned x8 = 93%Z \/ bv_unsigned x8 = 94%Z) -> fam_on ms.
Proof.
  intros ms x8 Hsvc [H|H]; eapply fam_on_sysno; eauto using injected_arm_93, injected_arm_94.
Qed.

Lemma sstep_cfg_of_sstep : forall ms model e st,
  sstep segs (mkCfg ms model) e st ->
  fam_on ms ->
  sstep_cfg segs scfg (mkCfg ms model) e st.
Proof.
  intros ms model e st Hss Hon.
  inversion Hss; subst;
    [ eapply sstep_cfg_instr; eassumption
    | eapply sstep_cfg_instr_fault; eassumption
    | eapply sstep_cfg_instr_unmodeled; eassumption
    | eapply sstep_cfg_syscall; try eassumption; apply not_spurious_on; apply Hon; assumption
    | eapply sstep_cfg_syscall_materialization_fault; try eassumption;
        apply not_spurious_on; apply Hon; assumption
    | eapply sstep_cfg_exit; eassumption
    | eapply sstep_cfg_killed; eassumption
    | eapply sstep_cfg_syscall_unmodeled; eassumption ].
Qed.

Lemma sstep_cfg_of_sstep' : forall c e st,
  sstep segs c e st ->
  fam_on (cfg_ms c) ->
  sstep_cfg segs scfg c e st.
Proof. intros [ms model] e st; cbn. apply sstep_cfg_of_sstep. Qed.

Lemma sstep_of_sstep_cfg : forall c e st,
  sstep_cfg segs scfg c e st -> sstep segs c e st.
Proof. intros c e st H. exact (sstep_cfg_sub segs scfg c e st H). Qed.

Lemma star_cfg_one : forall c evs c',
  sstep_cfg segs scfg c evs (SNext c') -> star_cfg segs scfg c evs c'.
Proof.
  intros c evs c' H. rewrite <- (app_nil_r evs).
  eapply star_cfg_step; [exact H | apply star_cfg_refl].
Qed.

Lemma star_cfg_trans : forall c1 tr1 c2 tr2 c3,
  star_cfg segs scfg c1 tr1 c2 -> star_cfg segs scfg c2 tr2 c3 ->
  star_cfg segs scfg c1 (tr1 ++ tr2) c3.
Proof.
  intros c1 tr1 c2 tr2 c3 H12 H23.
  induction H12 as [c | c evs c' tr c'' Hs Hst IH].
  - exact H23.
  - rewrite <- app_assoc. eapply star_cfg_step; [exact Hs | apply IH; exact H23].
Qed.

Lemma obs_trace_cfg_nil : forall c0, obs_trace_cfg segs scfg c0 [].
Proof.
  intros c0. exists [], c0. split; [apply star_cfg_refl | exact I].
Qed.

Lemma sstep_cfg_halted_none : forall c e st,
  sstep_cfg segs scfg c e st -> m_halted (cfg_model c) = None.
Proof. intros c e st H; inversion H; subst; cbn; assumption. Qed.

Lemma star_cfg_halted_nil : forall c tr c',
  m_halted (cfg_model c) <> None -> star_cfg segs scfg c tr c' -> tr = [] /\ c' = c.
Proof.
  intros c tr c' Hh Hstar. inversion Hstar as [|c1 evs c2 tr2 c3 Hss Hstar2]; subst.
  - split; reflexivity.
  - exfalso. apply Hh. eapply sstep_cfg_halted_none. exact Hss.
Qed.

Lemma reaches_error_cfg_here : forall c evs,
  sstep_cfg segs scfg c evs SError -> reaches_error_cfg segs scfg c.
Proof.
  intros c evs H. exists [], c, evs. split; [apply star_cfg_refl | exact H].
Qed.

Lemma reaches_error_cfg_step : forall c evs c',
  sstep_cfg segs scfg c evs (SNext c') ->
  reaches_error_cfg segs scfg c' -> reaches_error_cfg segs scfg c.
Proof.
  intros c evs c' Hs (tr & c2 & evs2 & Hst & He).
  exists (evs ++ tr), c2, evs2. split; [eapply star_cfg_step; eassumption | exact He].
Qed.

End WithSegs.
