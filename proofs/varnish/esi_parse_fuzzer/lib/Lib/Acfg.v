(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Classical_Prop.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi Syscall Dispatch SyscallTable.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect Mremap.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope bv_scope.

Definition ACFG : SpuriousCfg := alloc_only_cfg false.

Definition alloc_no_b (n : Z) : bool := existsb (Z.eqb n) alloc_mark_sysnos.

(* Membership by [Z.eqb] in any list of integers, by recursion on the list. *)
Lemma cr2_existsb_zeqb : forall (l : list Z) (n : Z), existsb (Z.eqb n) l = true <-> In n l.
Proof.
  intros vl vn. induction vl as [| vx vl k1]; cbn [existsb In].
  - split; [discriminate | intros []].
  - rewrite Bool.orb_true_iff, Z.eqb_eq, k1.
    split; intros [k2 | k2]; [left; symmetry; exact k2 | right; exact k2
                             | left; symmetry; exact k2 | right; exact k2].
Qed.

Lemma alloc_no_b_In : forall n, alloc_no_b n = true <-> In n alloc_mark_sysnos.
Proof.
  intros vn. exact (cr2_existsb_zeqb alloc_mark_sysnos vn).
Qed.

Lemma alloc_no_b_false : forall n, alloc_no_b n = false -> ~ In n alloc_mark_sysnos.
Proof.
  intros vn k1 k2.
  rewrite (proj2 (alloc_no_b_In vn) k2) in k1. discriminate k1.
Qed.

Lemma acfg_family_off_in : forall i,
  injected_family_off ACFG i = true -> In (bv_unsigned (in_sysno i)) alloc_mark_sysnos.
Proof.
  intros vi k1. unfold injected_family_off in k1.
  destruct (injected_arm (bv_unsigned (in_sysno vi))) as [va |] eqn:k2; [| discriminate k1].
  apply (alloc_family_dispatched _ va k2).
  destruct (ia_family va); cbv in k1; first [reflexivity | discriminate k1].
Qed.

Lemma acfg_family_on_notin : forall i,
  ~ In (bv_unsigned (in_sysno i)) alloc_mark_sysnos -> injected_family_off ACFG i = false.
Proof.
  intros vi k1. apply Bool.not_true_is_false.
  intros k2. apply k1. exact (acfg_family_off_in vi k2).
Qed.

Lemma acfg_family_off_no : forall i n,
  bv_unsigned (in_sysno i) = n -> In n alloc_mark_sysnos -> injected_family_off ACFG i = true.
Proof.
  intros vi vn k1 k2. unfold injected_family_off. rewrite k1.
  cbn [alloc_mark_sysnos In] in k2.
  destruct k2 as [<- | [<- | [<- | [<- | []]]]]; reflexivity.
Qed.

Lemma acfg_nonspurious : forall i m eff,
  ~ In (bv_unsigned (in_sysno i)) alloc_mark_sysnos ->
  ~ spurious_refusal_cfg ACFG i m eff.
Proof.
  intros vi vm veff k1. apply spurious_refusal_family_on.
  apply acfg_family_on_notin. exact k1.
Qed.

Lemma acfg_nonspurious_b : forall i m eff,
  alloc_no_b (bv_unsigned (in_sysno i)) = false ->
  ~ spurious_refusal_cfg ACFG i m eff.
Proof.
  intros vi vm veff k1. apply acfg_nonspurious.
  apply alloc_no_b_false. exact k1.
Qed.

Lemma ret_in_errnos_errno : forall es e, In e es -> ret_in_errnos es (errno_ret e) = true.
Proof.
  intros ves ve k1. unfold ret_in_errnos. apply existsb_exists.
  exists ve. split; [exact k1 | apply Z.eqb_refl].
Qed.

Lemma ret_in_errnos_ENOMEM : forall r,
  ret_in_errnos [ENOMEM] r = bv_eqb r (errno_ret ENOMEM).
Proof.
  intros vr. unfold ret_in_errnos. cbn [existsb]. apply Bool.orb_false_r.
Qed.

Lemma page_aligned_not_ENOMEM : forall a : word,
  (bv_unsigned a mod page_size = 0)%Z -> bv_eqb a (errno_ret ENOMEM) = false.
Proof.
  intros va k1. unfold bv_eqb. apply Z.eqb_neq. intros k2.
  rewrite k2 in k1. vm_compute in k1. discriminate k1.
Qed.

Lemma ret_in_errnos_ENOMEM_aligned : forall a : word,
  (bv_unsigned a mod page_size = 0)%Z -> ret_in_errnos [ENOMEM] a = false.
Proof.
  intros va k1. rewrite ret_in_errnos_ENOMEM. exact (page_aligned_not_ENOMEM va k1).
Qed.

(* [refusal_b] read at a known syscall number. *)
Lemma cr2_refusal_b_at : forall i m r n, bv_unsigned (in_sysno i) = n ->
  refusal_b i m r =
  if Z.eqb n 214 then brk_refusal_b m (in_arg i 0) r
  else match injected_arm n with
       | Some a => ret_in_errnos (ia_errnos a) r
       | None => false
       end.
Proof.
  intros vi vm vr vn k1. subst vn. reflexivity.
Qed.

Lemma refusal_b_222 : forall i m r, bv_unsigned (in_sysno i) = 222%Z ->
  refusal_b i m r = ret_in_errnos mmap_errnos r.
Proof.
  intros vi vm vr k1. rewrite (cr2_refusal_b_at vi vm vr 222 k1). reflexivity.
Qed.
Lemma refusal_b_226 : forall i m r, bv_unsigned (in_sysno i) = 226%Z ->
  refusal_b i m r = ret_in_errnos mprotect_errnos r.
Proof.
  intros vi vm vr k1. rewrite (cr2_refusal_b_at vi vm vr 226 k1). reflexivity.
Qed.
Lemma refusal_b_216 : forall i m r, bv_unsigned (in_sysno i) = 216%Z ->
  refusal_b i m r = ret_in_errnos mremap_errnos r.
Proof.
  intros vi vm vr k1. rewrite (cr2_refusal_b_at vi vm vr 216 k1). reflexivity.
Qed.
Lemma refusal_b_214 : forall i m r, bv_unsigned (in_sysno i) = 214%Z ->
  refusal_b i m r = brk_refusal_b m (in_arg i 0) r.
Proof.
  intros vi vm vr k1. rewrite (cr2_refusal_b_at vi vm vr 214 k1). reflexivity.
Qed.

Definition spec_step_ok (i : SyscallInput) (m : Model) (o : outcome SyscallEffect) : Prop :=
  match o with
  | Ok eff m' _ => m_halted m' = None -> ~ spurious_refusal_cfg ACFG i m eff
  | Unmodeled => True
  end.

Definition syscall_spec_acfg : Sys SyscallEffect :=
  fun i m o => syscall_spec i m o /\ spec_step_ok i m o.

Lemma syscall_spec_acfg_spec : forall i m o, syscall_spec_acfg i m o -> syscall_spec i m o.
Proof.
  intros vi vm vo k1. exact (proj1 k1).
Qed.

Lemma syscall_spec_acfg_unmodeled : forall i m,
  syscall_spec_acfg i m Unmodeled <-> syscall_spec i m Unmodeled.
Proof.
  intros vi vm. split.
  - apply syscall_spec_acfg_spec.
  - intros k1. exact (conj k1 I).
Qed.

Lemma syscall_spec_acfg_nonalloc : forall i m o,
  ~ In (bv_unsigned (in_sysno i)) alloc_mark_sysnos ->
  syscall_spec_acfg i m o <-> syscall_spec i m o.
Proof.
  intros vi vm vo k1. split; [apply syscall_spec_acfg_spec |].
  intros k2. split; [exact k2 |].
  destruct vo as [veff vm' vevs |]; [| exact I].
  intros _. exact (acfg_nonspurious vi vm veff k1).
Qed.

Lemma syscall_spec_acfg_nonalloc_b : forall i m o,
  alloc_no_b (bv_unsigned (in_sysno i)) = false ->
  syscall_spec_acfg i m o <-> syscall_spec i m o.
Proof.
  intros vi vm vo k1. apply syscall_spec_acfg_nonalloc.
  exact (alloc_no_b_false _ k1).
Qed.

Lemma acfg_si_nonalloc : forall segs ms x8 m o,
  alloc_no_b (bv_unsigned x8) = false ->
  syscall_spec_acfg (sys_input segs ms x8) m o <-> syscall_spec (sys_input segs ms x8) m o.
Proof.
  intros vsegs vms vx8 vm vo k1.
  exact (syscall_spec_acfg_nonalloc_b (sys_input vsegs vms vx8) vm vo k1).
Qed.

Lemma syscall_spec_acfg_nonrefusal : forall i m eff m' evs,
  syscall_spec i m (Ok eff m' evs) ->
  refusal_b i m (eff_ret eff) = false ->
  syscall_spec_acfg i m (Ok eff m' evs).
Proof.
  intros vi vm veff vm' vevs k1 k2. split; [exact k1 |].
  intros _. exact (spurious_refusal_not_refusal ACFG vi vm veff k2).
Qed.

Lemma syscall_spec_acfg_forced : forall i m eff m' evs,
  syscall_spec i m (Ok eff m' evs) ->
  (forall eff' m'' evs', syscall_spec i m (Ok eff' m'' evs') -> refusal_b i m (eff_ret eff') = true) ->
  syscall_spec_acfg i m (Ok eff m' evs).
Proof.
  intros vi vm veff vm' vevs k1 k2. split; [exact k1 |].
  intros _ (_ & _ & veff2 & vm2 & vevs2 & k3 & k4).
  rewrite (k2 veff2 vm2 vevs2 k3) in k4. discriminate k4.
Qed.

Lemma syscall_spec_acfg_det : forall i m eff m' evs,
  (forall o, syscall_spec i m o <-> o = Ok eff m' evs) ->
  forall o, syscall_spec_acfg i m o <-> o = Ok eff m' evs.
Proof.
  intros vi vm veff vm' vevs k1 vo. split.
  - intros k2. apply k1. exact (proj1 k2).
  - intros k2. subst vo. split; [apply k1; reflexivity |].
    intros _ (_ & k3 & veff2 & vm2 & vevs2 & k4 & k5).
    apply k1 in k4. injection k4 as k6 k7 k8. subst veff2.
    rewrite k3 in k5. discriminate k5.
Qed.

Lemma syscall_spec_acfg_uniform : forall i m o,
  syscall_spec i m o ->
  (forall eff m' evs eff' m'' evs', syscall_spec i m (Ok eff m' evs) -> syscall_spec i m (Ok eff' m'' evs') ->
     refusal_b i m (eff_ret eff) = refusal_b i m (eff_ret eff')) ->
  syscall_spec_acfg i m o.
Proof.
  intros vi vm vo k1 k2. split; [exact k1 |].
  destruct vo as [veff vm' vevs |]; [| exact I].
  intros _ (_ & k3 & veff2 & vm2 & vevs2 & k4 & k5).
  rewrite (k2 _ _ _ _ _ _ k1 k4), k5 in k3. discriminate k3.
Qed.

Lemma syscall_spec_acfg_halted : forall i m eff m' evs,
  m_halted m' <> None ->
  syscall_spec_acfg i m (Ok eff m' evs) <-> syscall_spec i m (Ok eff m' evs).
Proof.
  intros vi vm veff vm' vevs k1. split; [apply syscall_spec_acfg_spec |].
  intros k2. split; [exact k2 |].
  intros k3. exfalso. exact (k1 k3).
Qed.

Lemma exists_nonspurious : forall cfg i m eff0 m0 evs0,
  syscall_spec i m (Ok eff0 m0 evs0) ->
  exists eff m' evs, syscall_spec i m (Ok eff m' evs) /\ ~ spurious_refusal_cfg cfg i m eff.
Proof.
  intros vcfg vi vm veff0 vm0 vevs0 k1.
  destruct (classic (spurious_refusal_cfg vcfg vi vm veff0)) as [k2 | k2].
  - (* the given outcome is filtered: its own witness is a non-refusal *)
    destruct k2 as (_ & _ & veff & vm' & vevs & k3 & k4).
    exists veff, vm', vevs.
    exact (conj k3 (spurious_refusal_not_refusal vcfg vi vm veff k4)).
  - exists veff0, vm0, vevs0. exact (conj k1 k2).
Qed.

Lemma exists_acfg : forall i m eff0 m0 evs0,
  syscall_spec i m (Ok eff0 m0 evs0) ->
  exists eff m' evs, syscall_spec_acfg i m (Ok eff m' evs).
Proof.
  intros vi vm veff0 vm0 vevs0 k1.
  destruct (exists_nonspurious ACFG vi vm veff0 vm0 vevs0 k1) as (veff & vm' & vevs & k2 & k3).
  exists veff, vm', vevs. split; [exact k2 |]. intros _. exact k3.
Qed.

Lemma nonspurious_refusal_forced : forall i m eff,
  ~ spurious_refusal_cfg ACFG i m eff ->
  injected_family_off ACFG i = true ->
  refusal_b i m (eff_ret eff) = true ->
  forall eff' m' evs', syscall_spec i m (Ok eff' m' evs') -> refusal_b i m (eff_ret eff') = true.
Proof.
  intros vi vm veff k1 k2 k3 veff2 vm2 vevs2 k4.
  apply Bool.not_false_is_true. intros k5.
  exact (k1 (conj k2 (conj k3 (ex_intro _ veff2 (ex_intro _ vm2 (ex_intro _ vevs2 (conj k4 k5))))))).
Qed.

Lemma acfg_refusal_forced : forall i m eff m' evs,
  syscall_spec_acfg i m (Ok eff m' evs) -> m_halted m' = None ->
  injected_family_off ACFG i = true ->
  refusal_b i m (eff_ret eff) = true ->
  forall eff' m'' evs', syscall_spec i m (Ok eff' m'' evs') -> refusal_b i m (eff_ret eff') = true.
Proof.
  intros vi vm veff vm' vevs k1 k2 k3 k4.
  exact (nonspurious_refusal_forced vi vm veff (proj2 k1 k2) k3 k4).
Qed.

Lemma acfg_char_split : forall i m (Ref Grant : outcome SyscallEffect -> Prop) (forced : bool),
  injected_family_off ACFG i = true ->
  (forall o, syscall_spec i m o <-> Ref o \/ Grant o) ->
  (forall eff m' evs, syscall_spec i m (Ok eff m' evs) -> m_halted m' = None) ->
  (forall o, Ref o -> exists eff m' evs, o = Ok eff m' evs /\ refusal_b i m (eff_ret eff) = true) ->
  (forall o, Grant o -> exists eff m' evs, o = Ok eff m' evs /\ refusal_b i m (eff_ret eff) = false) ->
  (forall o, Grant o -> forced = false) ->
  (forced = false -> exists o, Grant o) ->
  forall o, syscall_spec_acfg i m o <-> (forced = true /\ Ref o) \/ Grant o.
Proof.
  intros vi vm vRef vGrant vforced k1 k2 k3 k4 k5 k6 k7 vo.
  destruct vforced.
  - (* forced: there is no grant, so every admitted outcome is a refusal *)
    assert (k8 : forall vp, ~ vGrant vp) by (intros vp k9; discriminate (k6 vp k9)).
    assert (k10 : forall vp, syscall_spec vi vm vp -> vRef vp).
    { intros vp k11. destruct (proj1 (k2 vp) k11) as [k12 | k12];
        [exact k12 | destruct (k8 vp k12)]. }
    split.
    + intros k13. left. exact (conj eq_refl (k10 vo (proj1 k13))).
    + intros [[_ k13] | k13]; [| destruct (k8 vo k13)].
      destruct (k4 vo k13) as (veff & vm' & vevs & k14 & _). subst vo.
      apply syscall_spec_acfg_forced; [apply k2; left; exact k13 |].
      intros veff2 vm2 vevs2 k15.
      destruct (k4 _ (k10 _ k15)) as (veff3 & vm3 & vevs3 & k16 & k17).
      injection k16 as k18 k19 k20. subst veff3. exact k17.
  - (* not forced: a grant exists, and it makes every refusal spurious *)
    destruct (k7 eq_refl) as [vg k8].
    destruct (k5 vg k8) as (veffg & vmg & vevsg & k9 & k10). subst vg.
    assert (k11 : syscall_spec vi vm (Ok veffg vmg vevsg)) by (apply k2; right; exact k8).
    split.
    + intros k12. right.
      destruct (proj1 (k2 vo) (proj1 k12)) as [k13 | k13]; [exfalso | exact k13].
      destruct (k4 vo k13) as (veff & vm' & vevs & k14 & k15). subst vo.
      apply (proj2 k12 (k3 _ _ _ (proj1 k12))).
      split; [exact k1 |]. split; [exact k15 |].
      exists veffg, vmg, vevsg. exact (conj k11 k10).
    + intros [[k12 _] | k12]; [discriminate k12 |].
      destruct (k5 vo k12) as (veff & vm' & vevs & k13 & k14). subst vo.
      apply syscall_spec_acfg_nonrefusal; [apply k2; right; exact k12 | exact k14].
Qed.

Section WithSegs.
Variable segs : list Segment.

Lemma sstep_cfg_halted_none : forall c e st,
  sstep_cfg segs ACFG c e st -> m_halted (cfg_model c) = None.
Proof.
  intros vc ve vst k1. case k1; intros; cbn [cfg_model]; assumption.
Qed.

Lemma star_cfg_halted_nil : forall c tr c',
  m_halted (cfg_model c) <> None -> star_cfg segs ACFG c tr c' -> tr = [] /\ c' = c.
Proof.
  intros vc vtr vc' k1 k2.
  destruct k2 as [vd | vc1 vevs vc2 vtr2 vc3 k3 k4].
  - split; reflexivity.
  - exfalso. exact (k1 (sstep_cfg_halted_none vc1 vevs (SNext vc2) k3)).
Qed.

Lemma star_cfg_one : forall c evs c',
  sstep_cfg segs ACFG c evs (SNext c') -> star_cfg segs ACFG c evs c'.
Proof.
  intros vc vevs vc' k1. rewrite <- (app_nil_r vevs).
  exact (star_cfg_step segs ACFG vc vevs vc' [] vc' k1 (star_cfg_refl segs ACFG vc')).
Qed.

Lemma star_cfg_trans : forall c1 t1 c2 t2 c3,
  star_cfg segs ACFG c1 t1 c2 -> star_cfg segs ACFG c2 t2 c3 -> star_cfg segs ACFG c1 (t1 ++ t2) c3.
Proof.
  intros vc1 vt1 vc2 vt2 vc3 k1. induction k1 as [vd | va vevs vb vtr vd k2 k3 k4]; intros k5.
  - exact k5.
  - rewrite <- app_assoc. exact (star_cfg_step segs ACFG va vevs vb (vtr ++ vt2) vc3 k2 (k4 k5)).
Qed.

Lemma obs_trace_cfg_nil : forall c, obs_trace_cfg segs ACFG c [].
Proof.
  intros vc. exists [], vc. exact (conj (star_cfg_refl segs ACFG vc) I).
Qed.

Lemma star_cfg_inv (Inv : config -> Prop)
  (Hstep : forall c evs c', Inv c -> sstep_cfg segs ACFG c evs (SNext c') -> Inv c') :
  forall c tr c', Inv c -> star_cfg segs ACFG c tr c' -> Inv c'.
Proof.
  intros vc vtr vc' k1 k2. revert k1.
  induction k2 as [vd | va vevs vb vtr2 vd k3 k4 k5]; intros k6.
  - exact k6.
  - exact (k5 (Hstep va vevs vb k6 k3)).
Qed.

Lemma inv_no_reaches_error_cfg (Inv : config -> Prop)
  (Hstep : forall c evs c', Inv c -> sstep_cfg segs ACFG c evs (SNext c') -> Inv c')
  (Hnoerr : forall c evs, Inv c -> ~ sstep_cfg segs ACFG c evs SError) :
  forall c, Inv c -> ~ reaches_error_cfg segs ACFG c.
Proof.
  intros vc k1 (vtr & vd & vevs & k2 & k3).
  exact (Hnoerr vd vevs (star_cfg_inv Inv Hstep vc vtr vd k1 k2) k3).
Qed.

(* Any unfiltered step is a filtered one once each syscall outcome it may
   consume is known not to be a spurious refusal. *)
Lemma cr2_sstep_lift : forall c e st,
  sstep segs c e st ->
  (forall x8 eff m' evs,
     ms_svc_pending (cfg_ms c) = Some x8 ->
     syscall_spec (sys_input segs (cfg_ms c) x8) (cfg_model c) (Ok eff m' evs) ->
     m_halted m' = None ->
     ~ spurious_refusal_cfg ACFG (sys_input segs (cfg_ms c) x8) (cfg_model c) eff) ->
  sstep_cfg segs ACFG c e st.
Proof.
  intros vc ve vst k1.
  destruct k1 as
    [ vms vmodel vms' vmodel' k2 k3 k4
    | vms vmodel k2 k3 k4
    | vms vmodel k2 k3 k4
    | vms vmodel vx8 veff vmodel' vmodel'' vevs k2 k3 k4 k5 k6
    | vms vmodel vx8 veff vmodel' vevs k2 k3 k4 k5 k6
    | vms vmodel vx8 veff vmodel' vevs vcode k2 k3 k4 k5 k6
    | vms vmodel vx8 veff vmodel' vevs vsig k2 k3 k4 k5
    | vms vmodel vx8 k2 k3 k4 ];
    intros k9; cbn [cfg_ms cfg_model] in k9.
  - exact (sstep_cfg_instr segs ACFG vms vmodel vms' vmodel' k2 k3 k4).
  - exact (sstep_cfg_instr_fault segs ACFG vms vmodel k2 k3 k4).
  - exact (sstep_cfg_instr_unmodeled segs ACFG vms vmodel k2 k3 k4).
  - exact (sstep_cfg_syscall segs ACFG vms vmodel vx8 veff vmodel' vmodel'' vevs
             k2 k3 k4 (k9 vx8 veff vmodel' vevs k3 k4 k5) k5 k6).
  - exact (sstep_cfg_syscall_materialization_fault segs ACFG vms vmodel vx8 veff vmodel' vevs
             k2 k3 k4 (k9 vx8 veff vmodel' vevs k3 k4 k5) k5 k6).
  - exact (sstep_cfg_exit segs ACFG vms vmodel vx8 veff vmodel' vevs vcode k2 k3 k4 k5 k6).
  - exact (sstep_cfg_killed segs ACFG vms vmodel vx8 veff vmodel' vevs vsig k2 k3 k4 k5).
  - exact (sstep_cfg_syscall_unmodeled segs ACFG vms vmodel vx8 k2 k3 k4).
Qed.

Lemma sstep_cfg_of_instr : forall ms model e st,
  ms_svc_pending ms = None -> sstep segs (mkCfg ms model) e st -> sstep_cfg segs ACFG (mkCfg ms model) e st.
Proof.
  intros vms vmodel ve vst k1 k2. apply (cr2_sstep_lift _ _ _ k2).
  intros vx8 veff vm' vevs k3. cbn [cfg_ms] in k3. rewrite k1 in k3. discriminate k3.
Qed.

Lemma sstep_cfg_of_nonalloc : forall ms model x8 e st,
  ms_svc_pending ms = Some x8 ->
  ~ In (bv_unsigned x8) alloc_mark_sysnos ->
  sstep segs (mkCfg ms model) e st -> sstep_cfg segs ACFG (mkCfg ms model) e st.
Proof.
  intros vms vmodel vx8 ve vst k1 k2 k3. apply (cr2_sstep_lift _ _ _ k3).
  intros vy veff vm' vevs k4 _ _. cbn [cfg_ms cfg_model] in *.
  rewrite k1 in k4. injection k4 as k5. subst vy.
  exact (acfg_nonspurious (sys_input segs vms vx8) vmodel veff k2).
Qed.

Lemma sstep_cfg_of_acfg : forall ms model x8 e st,
  ms_svc_pending ms = Some x8 ->
  sstep segs (mkCfg ms model) e st ->
  (forall eff m' evs, syscall_spec (sys_input segs ms x8) model (Ok eff m' evs) ->
     m_halted m' = None -> syscall_spec_acfg (sys_input segs ms x8) model (Ok eff m' evs)) ->
  sstep_cfg segs ACFG (mkCfg ms model) e st.
Proof.
  intros vms vmodel vx8 ve vst k1 k2 k3. apply (cr2_sstep_lift _ _ _ k2).
  intros vy veff vm' vevs k4 k5 k6. cbn [cfg_ms cfg_model] in *.
  rewrite k1 in k4. injection k4 as k7. subst vy.
  exact (proj2 (k3 veff vm' vevs k5 k6) k6).
Qed.

(* An admitted, still-running outcome of the filtered spec is an outcome of
   the spec that the filter keeps. *)
Lemma cr2_acfg_running : forall i m eff m' evs,
  syscall_spec_acfg i m (Ok eff m' evs) -> m_halted m' = None ->
  syscall_spec i m (Ok eff m' evs) /\ ~ spurious_refusal_cfg ACFG i m eff.
Proof.
  intros vi vm veff vm' vevs [k1 k2] k3. exact (conj k1 (k2 k3)).
Qed.

Lemma sstep_cfg_syscall_acfg : forall ms model x8 eff model' model'' evs,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  syscall_spec_acfg (sys_input segs ms x8) model (Ok eff model' evs) ->
  m_halted model' = None ->
  materialize_model_accesses model' (syscall_effect_accesses eff) = Some model'' ->
  sstep_cfg segs ACFG (mkCfg ms model) evs
            (SNext (mkCfg (advance_past_svc (apply_effect ms eff)) model'')).
Proof.
  intros vms vmodel vx8 veff vmodel' vmodel'' vevs k1 k2 k3 k4 k5.
  destruct (cr2_acfg_running _ _ _ _ _ k3 k4) as [k6 k7].
  exact (sstep_cfg_syscall segs ACFG vms vmodel vx8 veff vmodel' vmodel'' vevs k1 k2 k6 k7 k4 k5).
Qed.

Lemma sstep_cfg_syscall_mf_acfg : forall ms model x8 eff model' evs,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  syscall_spec_acfg (sys_input segs ms x8) model (Ok eff model' evs) ->
  m_halted model' = None ->
  materialize_model_accesses model' (syscall_effect_accesses eff) = None ->
  sstep_cfg segs ACFG (mkCfg ms model) [] SError.
Proof.
  intros vms vmodel vx8 veff vmodel' vevs k1 k2 k3 k4 k5.
  destruct (cr2_acfg_running _ _ _ _ _ k3 k4) as [k6 k7].
  exact (sstep_cfg_syscall_materialization_fault segs ACFG vms vmodel vx8 veff vmodel' vevs
           k1 k2 k6 k7 k4 k5).
Qed.

Lemma sstep_cfg_sys_inv_acfg : forall ms model x8 evs st,
  ms_svc_pending ms = Some x8 ->
  sstep_cfg segs ACFG (mkCfg ms model) evs st ->
  let i := sys_input segs ms x8 in
  (exists eff model' evs0,
      syscall_spec_acfg i model (Ok eff model' evs0)
      /\ m_halted model' = None
      /\ match materialize_model_accesses model' (syscall_effect_accesses eff) with
         | Some model'' => evs = evs0 /\ st = SNext (mkCfg (advance_past_svc (apply_effect ms eff)) model'')
         | None => evs = [] /\ st = SError
         end)
  \/ (exists eff model' evs0 code',
      syscall_spec_acfg i model (Ok eff model' evs0)
      /\ m_halted model' = Some code' /\ m_killed model' = None
      /\ evs = evs0 ++ [ExitEv code' (m_fs model')] /\ st = SNext (mkCfg ms model'))
  \/ (exists eff model' evs0 sig,
      syscall_spec_acfg i model (Ok eff model' evs0)
      /\ m_killed model' = Some sig
      /\ evs = evs0 ++ [KillEv sig (m_fs model')] /\ st = SNext (mkCfg ms model'))
  \/ (syscall_spec_acfg i model Unmodeled /\ evs = [] /\ st = SError).
Proof.
  intros vms vmodel vx8 vevs vst k1 k2. cbv zeta.
  remember (mkCfg vms vmodel) as vc eqn:k3. revert k3.
  destruct k2 as
    [ vms2 vmodel2 vms' vmodel' k4 k5 k6
    | vms2 vmodel2 k4 k5 k6
    | vms2 vmodel2 k4 k5 k6
    | vms2 vmodel2 vy veff vmodel' vmodel'' vevs2 k4 k5 k6 k7 k8 k9
    | vms2 vmodel2 vy veff vmodel' vevs2 k4 k5 k6 k7 k8 k9
    | vms2 vmodel2 vy veff vmodel' vevs2 vcode k4 k5 k6 k7 k8
    | vms2 vmodel2 vy veff vmodel' vevs2 vsig k4 k5 k6 k7
    | vms2 vmodel2 vy k4 k5 k6 ];
    intros k10; injection k10 as k11 k12; subst vms2 vmodel2;
    try (rewrite k1 in k5; discriminate k5);
    rewrite k1 in k5; injection k5 as k13; subst vy.
  - (* a kept outcome that materializes *)
    left. exists veff, vmodel', vevs2.
    split; [exact (conj k6 (fun _ => k7)) |]. split; [exact k8 |].
    rewrite k9. split; reflexivity.
  - (* a kept outcome whose materialization faults *)
    left. exists veff, vmodel', vevs2.
    split; [exact (conj k6 (fun _ => k7)) |]. split; [exact k8 |].
    rewrite k9. split; reflexivity.
  - (* exit: the outcome is halted, so the filter does not apply *)
    right; left. exists veff, vmodel', vevs2, vcode.
    split; [split; [exact k6 | intros k14; rewrite k7 in k14; discriminate k14] |].
    repeat split; assumption.
  - (* kill: a killed model is halted, so again the filter does not apply *)
    right; right; left. exists veff, vmodel', vevs2, vsig.
    split; [split; [exact k6 |] |].
    + intros k14. rewrite (m_killed_of_m_halted_none vmodel' k14) in k7. discriminate k7.
    + repeat split; assumption.
  - right; right; right. split; [exact (conj k6 I) |]. split; reflexivity.
Qed.

End WithSegs.

Definition mmap_errnos_when (forced : bool) : list Z :=
  if forced then mmap_errnos else [].

Definition mmap_destructive_errnos : list Z := [].

Definition vm_base_ok (h : VmMaps) (nZ : Z) (a : word) : bool :=
  (bv_unsigned a mod page_size =? 0)%Z
  && (0 <? bv_unsigned a)%Z
  && (bv_unsigned a + nZ <=? alloc_top h)%Z
  && region_free (vm_reserved h ++ vm_maps h) a (Z_to_bv 64 nZ).

Definition vm_base_candidates (h : VmMaps) : list word :=
  Z_to_bv 64 page_size
  :: map (fun iv => Z_to_bv 64 (page_round_up_Z
                      (bv_unsigned (fst iv) + bv_unsigned (snd iv))))
         (vm_reserved h ++ vm_maps h).

Definition vm_find_base (h : VmMaps) (nZ : Z) : option word :=
  List.find (vm_base_ok h nZ) (vm_base_candidates h).

Definition vm_gap_available (h : VmMaps) (nZ : Z) : bool :=
  match vm_find_base h nZ with Some _ => true | None => false end.

(* [vm_base_ok] read as the four facts it tests. *)
Lemma cr2_vm_base_ok_iff : forall h nZ a,
  vm_base_ok h nZ a = true <->
  (bv_unsigned a mod page_size = 0)%Z
  /\ (0 < bv_unsigned a)%Z
  /\ (bv_unsigned a + nZ <= alloc_top h)%Z
  /\ region_free (vm_reserved h ++ vm_maps h) a (Z_to_bv 64 nZ) = true.
Proof.
  intros vh vnZ va. unfold vm_base_ok.
  rewrite !Bool.andb_true_iff, Z.eqb_eq, Z.ltb_lt, Z.leb_le.
  tauto.
Qed.

Lemma vm_base_ok_sound : forall h nZ a,
  vm_base_ok h nZ a = true ->
  (bv_unsigned a mod page_size = 0)%Z
  /\ (0 < bv_unsigned a)%Z
  /\ (bv_unsigned a + nZ <= alloc_top h)%Z
  /\ region_free (vm_reserved h ++ vm_maps h) a (Z_to_bv 64 nZ) = true.
Proof.
  intros vh vnZ va. apply cr2_vm_base_ok_iff.
Qed.

Lemma vm_find_base_sound : forall h nZ a,
  vm_find_base h nZ = Some a ->
  (bv_unsigned a mod page_size = 0)%Z
  /\ (0 < bv_unsigned a)%Z
  /\ (bv_unsigned a + nZ <= alloc_top h)%Z
  /\ region_free (vm_reserved h ++ vm_maps h) a (Z_to_bv 64 nZ) = true.
Proof.
  intros vh vnZ va k1. unfold vm_find_base in k1.
  apply vm_base_ok_sound. exact (proj2 (find_some _ _ k1)).
Qed.

Lemma vm_gap_available_find : forall h nZ,
  vm_gap_available h nZ = true -> exists a, vm_find_base h nZ = Some a.
Proof.
  intros vh vnZ k1. unfold vm_gap_available in k1.
  destruct (vm_find_base vh vnZ) as [va |]; [exists va; reflexivity | discriminate k1].
Qed.

Lemma region_free_false_In : forall maps lo n,
  region_free maps lo n = false ->
  exists a sz, In (a, sz) maps /\ iv_overlap lo n a sz = true.
Proof.
  intros vmaps vlo vn k1.
  destruct (existsb (fun vp => iv_overlap vlo vn (fst vp) (snd vp)) vmaps) eqn:k2.
  - (* some entry is met: name it *)
    destruct (proj1 (existsb_exists _ _) k2) as ([va vsz] & k3 & k4).
    exists va, vsz. exact (conj k3 k4).
  - (* no entry is met: then the region is free, against [k1] *)
    assert (k3 : region_free vmaps vlo vn = true).
    { apply region_free_intro. intros va vsz k4.
      apply Bool.not_true_is_false. intros k5.
      rewrite (proj2 (existsb_exists _ _) (ex_intro _ (va, vsz) (conj k4 k5))) in k2.
      discriminate k2. }
    rewrite k3 in k1. discriminate k1.
Qed.

Lemma vm_base_ok_step : forall h nZ a,
  vm_base_ok h nZ a = true ->
  In a (vm_base_candidates h)
  \/ exists a', bv_unsigned a' = (bv_unsigned a - page_size)%Z
                /\ vm_base_ok h nZ a' = true.
Proof.
  intros vh vnZ va k1.
  destruct (in_dec (fun vx vy => decide (vx = vy)) va (vm_base_candidates vh)) as [k2 | k2];
    [left; exact k2 | right].
  destruct (proj1 (cr2_vm_base_ok_iff vh vnZ va) k1) as (k3 & k4 & k5 & k6).
  pose proof (bv_unsigned_in_range _ va) as k7.
  assert (k8 : bv_modulus 64 = 18446744073709551616%Z) by reflexivity.
  rewrite k8 in k7.
  (* [a] is page-aligned and positive, and it is not the candidate [page_size] itself, so it is at least two pages *)
  assert (k9 : bv_unsigned va <> page_size).
  { intros k10. apply k2. left. apply bv_eq. rewrite k10.
    apply Z_to_bv_small. rewrite k8. unfold page_size. lia. }
  unfold page_size in *.
  assert (k11 : (8192 <= bv_unsigned va)%Z) by lia.
  exists (Z_to_bv 64 (bv_unsigned va - 4096)).
  assert (k12 : bv_unsigned (Z_to_bv 64 (bv_unsigned va - 4096)) = (bv_unsigned va - 4096)%Z).
  { apply Z_to_bv_small. rewrite k8. lia. }
  split; [exact k12 |].
  apply cr2_vm_base_ok_iff. rewrite k12. unfold page_size.
  split; [lia |]. split; [lia |]. split; [lia |].
  (* an entry the lower base would meet ends inside the page below [a],
     so [a] is that entry's rounded end: a candidate, which it is not *)
  apply region_free_intro. intros vq vsz k13.
  apply Bool.not_true_is_false. intros k14.
  apply k2. right. apply in_map_iff. exists (vq, vsz). split; [| exact k13].
  pose proof (region_free_In _ _ _ _ _ k6 k13) as k15.
  unfold iv_overlap in k14, k15. rewrite k12 in k14.
  rewrite Bool.andb_true_iff, !Z.ltb_lt in k14.
  rewrite Bool.andb_false_iff, !Z.ltb_ge in k15.
  cbn [fst snd]. apply bv_eq. unfold page_round_up_Z, page_size.
  pose proof (bv_unsigned_in_range _ (Z_to_bv 64 vnZ)) as k16.
  rewrite Z_to_bv_small; [lia |].
  rewrite k8. lia.
Qed.

Lemma vm_find_base_complete_aux : forall h nZ k a,
  (bv_unsigned a <= Z.of_nat k * page_size)%Z ->
  vm_base_ok h nZ a = true ->
  exists c, In c (vm_base_candidates h) /\ vm_base_ok h nZ c = true.
Proof.
  intros vh vnZ vk. unfold page_size.
  induction vk as [| vj k1]; intros va k2 k3;
    destruct (vm_base_ok_step vh vnZ va k3) as [k4 | (vb & k4 & k5)];
    try (exists va; exact (conj k4 k3)).
  - (* [k] is 0, so [a] lies at or below 0, yet the step puts a [b] a page below it, and no word is negative *)
    exfalso. pose proof (bv_unsigned_in_range _ vb) as k6. unfold page_size in k4. lia.
  - apply (k1 vb); [unfold page_size in k4; lia | exact k5].
Qed.

Lemma vm_find_base_complete : forall h nZ a,
  vm_base_ok h nZ a = true -> vm_gap_available h nZ = true.
Proof.
  intros vh vnZ va k1.
  pose proof (bv_unsigned_in_range _ va) as k2.
  destruct (vm_find_base_complete_aux vh vnZ (Z.to_nat (bv_unsigned va)) va) as (vc & k3 & k4);
    [unfold page_size; lia | exact k1 |].
  unfold vm_gap_available, vm_find_base.
  destruct (find (vm_base_ok vh vnZ) (vm_base_candidates vh)) eqn:k5; [reflexivity |].
  rewrite (find_none _ _ k5 vc k3) in k4. discriminate k4.
Qed.

(* A gap is available exactly when some base passes [vm_base_ok]. *)
Lemma cr2_gap_some_ok : forall h nZ,
  vm_gap_available h nZ = true <-> exists a, vm_base_ok h nZ a = true.
Proof.
  intros vh vnZ. split.
  - intros k1. destruct (vm_gap_available_find vh vnZ k1) as [va k2].
    exists va. exact (proj2 (find_some _ _ k2)).
  - intros [va k1]. exact (vm_find_base_complete vh vnZ va k1).
Qed.

Lemma vm_gap_available_iff : forall h nZ,
  vm_gap_available h nZ = true <->
  exists a, (bv_unsigned a mod page_size = 0)%Z
            /\ (0 < bv_unsigned a)%Z
            /\ (bv_unsigned a + nZ <= alloc_top h)%Z
            /\ region_free (vm_reserved h ++ vm_maps h) a (Z_to_bv 64 nZ) = true.
Proof.
  intros vh vnZ. rewrite cr2_gap_some_ok.
  split; intros [va k1]; exists va; apply cr2_vm_base_ok_iff; exact k1.
Qed.

Definition mmap_grant_refusable (flags : word) (m : Model) (nZ : Z) : bool :=
  negb (mmap_noreserve_backed_ok flags m nZ)
  || negb (vm_gap_available (m_vmmaps m) nZ).

Definition mmap_reserve_refusable (m : Model) (nZ : Z) : bool :=
  negb (vm_gap_available (m_vmmaps m) nZ).

Definition mmap_fixed_fresh_refusable (flags : word) (m : Model) (nZ : Z) : bool :=
  negb (mmap_noreserve_backed_ok flags m nZ).

Definition mmap_fixed_commit_refusable (flags : word) (m : Model) (addr n : word) : bool :=
  negb (mmap_fixed_rw_budget_ok flags m addr n).

Definition mmap_fixed_span_refusable (flags : word) (m : Model) (addr n : word) : bool :=
  negb (mmap_fixed_rw_span_budget_ok flags m addr n).

Definition mprotect_errnos_when (forced : bool) : list Z :=
  if forced then mprotect_errnos else [].

Definition mprotect_refusable (m : Model) (addr n : word) : bool :=
  negb (mprotect_budget_ok m addr n).
