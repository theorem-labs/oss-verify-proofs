(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect Mremap.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Abbreviation ACFG := (alloc_only_cfg false).

Lemma acfg_family_off_in : forall i,
  injected_family_off ACFG i = true -> In (bv_unsigned (in_sysno i)) alloc_mark_sysnos.
Proof.
  intros i fam_off.
  unfold injected_family_off in fam_off.
  destruct (injected_arm (bv_unsigned (in_sysno i))) as [arm|] eqn:arm_found;
    [|discriminate fam_off].
  refine (alloc_family_dispatched _ arm arm_found _).
  revert fam_off. case (ia_family arm); cbn; intro flag;
    first [reflexivity | discriminate flag].
Qed.

Lemma acfg_family_on_notin : forall i,
  ~ In (bv_unsigned (in_sysno i)) alloc_mark_sysnos -> injected_family_off ACFG i = false.
Proof.
  intros i outside. apply not_true_is_false.
  intro fam_off. exact (outside (acfg_family_off_in i fam_off)).
Qed.

Lemma acfg_nonspurious : forall i m eff,
  ~ In (bv_unsigned (in_sysno i)) alloc_mark_sysnos ->
  ~ spurious_refusal_cfg ACFG i m eff.
Proof.
  intros i m eff outside.
  exact (spurious_refusal_family_on ACFG i m eff (acfg_family_on_notin i outside)).
Qed.

Definition alloc_no_b (n : Z) : bool :=
  existsb (fun s => Z.eqb s n) alloc_mark_sysnos.

Lemma alloc_no_b_In : forall n, alloc_no_b n = true <-> In n alloc_mark_sysnos.
Proof.
  intros n. unfold alloc_no_b.
  generalize alloc_mark_sysnos as table.
  induction table as [|s rest step]; cbn [existsb In].
  - split; [intro absurd; discriminate absurd | intros []].
  - destruct (Z.eqb_spec s n) as [same | differ]; cbn [orb].
    + split; [intros _; left; exact same | intros _; reflexivity].
    + split.
      * intro later. right. apply step. exact later.
      * intros [clash | later]; [contradiction (differ clash) | apply step; exact later].
Qed.

Lemma alloc_no_b_false : forall n, alloc_no_b n = false -> ~ In n alloc_mark_sysnos.
Proof.
  intros n says_no listed.
  apply alloc_no_b_In in listed.
  rewrite says_no in listed. discriminate listed.
Qed.

Lemma refusal_spurious_of_grant : forall cfg i m eff eff' m' evs',
  injected_family_off cfg i = true ->
  refusal_b i m (eff_ret eff) = true ->
  syscall_spec i m (Ok eff' m' evs') ->
  refusal_b i m (eff_ret eff') = false ->
  spurious_refusal_cfg cfg i m eff.
Proof.
  intros cfg i m eff eff' m' evs' fam_off refused granted_spec granted.
  refine (conj fam_off (conj refused _)).
  exists eff', m', evs'. exact (conj granted_spec granted).
Qed.

Lemma refusal_b_222 : forall i m r, bv_unsigned (in_sysno i) = 222%Z ->
  refusal_b i m r = ret_in_errnos mmap_errnos r.
Proof. intros i m r is_mmap. unfold refusal_b. rewrite is_mmap. reflexivity. Qed.
Lemma refusal_b_226 : forall i m r, bv_unsigned (in_sysno i) = 226%Z ->
  refusal_b i m r = ret_in_errnos mprotect_errnos r.
Proof. intros i m r is_mprotect. unfold refusal_b. rewrite is_mprotect. reflexivity. Qed.
Lemma refusal_b_214 : forall i m r, bv_unsigned (in_sysno i) = 214%Z ->
  refusal_b i m r = brk_refusal_b m (in_arg i 0) r.
Proof. intros i m r is_brk. unfold refusal_b. rewrite is_brk. reflexivity. Qed.

Lemma acfg_family_off_alloc : forall i, bv_unsigned (in_sysno i) = 214%Z \/ bv_unsigned (in_sysno i) = 216%Z
  \/ bv_unsigned (in_sysno i) = 222%Z \/ bv_unsigned (in_sysno i) = 226%Z ->
  injected_family_off ACFG i = true.
Proof.
  intros i which. unfold injected_family_off.
  destruct which as [no | [no | [no | no]]]; rewrite no; reflexivity.
Qed.

Lemma ret_in_errnos_ENOMEM : forall r,
  ret_in_errnos [ENOMEM] r = bv_eqb r (errno_ret ENOMEM).
Proof.
  intros r. cbn [ret_in_errnos existsb]. apply orb_false_r.
Qed.

Lemma ret_in_errnos_errno : forall es e, In e es -> ret_in_errnos es (errno_ret e) = true.
Proof.
  intros es e Hin. unfold ret_in_errnos. apply existsb_exists. exists e. split; [exact Hin|].
  apply bv_eqb_eq. reflexivity.
Qed.

Section StepLift.
Variable segs : list Segment.

Lemma sstep_cfg_of_sstep : forall cfg ms mo evs X,
  sstep segs (mkCfg ms mo) evs X ->
  (forall x8 eff m' evs', ms_svc_pending ms = Some x8 ->
     syscall_spec (sys_input segs ms x8) mo (Ok eff m' evs') -> m_halted m' = None ->
     ~ spurious_refusal_cfg cfg (sys_input segs ms x8) mo eff) ->
  sstep_cfg segs cfg (mkCfg ms mo) evs X.
Proof.
  intros cfg ms mo evs X run filter.
  remember (mkCfg ms mo) as here eqn:here_is.
  revert here_is.
  destruct run as
    [ ms0 m0 ms1 m1 live idle acct
    | ms0 m0 live idle acct
    | ms0 m0 live idle acct
    | ms0 m0 n8 eff m1 m2 out live pend spec alive mat
    | ms0 m0 n8 eff m1 out live pend spec alive mat
    | ms0 m0 n8 eff m1 out code live pend spec stopped unkilled
    | ms0 m0 n8 eff m1 out sig live pend spec killed
    | ms0 m0 n8 live pend spec ];
    intros [= -> ->].
  - exact (sstep_cfg_instr segs cfg ms mo ms1 m1 live idle acct).
  - exact (sstep_cfg_instr_fault segs cfg ms mo live idle acct).
  - exact (sstep_cfg_instr_unmodeled segs cfg ms mo live idle acct).
  - exact (sstep_cfg_syscall segs cfg ms mo n8 eff m1 m2 out live pend spec
             (filter n8 eff m1 out pend spec alive) alive mat).
  - exact (sstep_cfg_syscall_materialization_fault segs cfg ms mo n8 eff m1 out
             live pend spec (filter n8 eff m1 out pend spec alive) alive mat).
  - exact (sstep_cfg_exit segs cfg ms mo n8 eff m1 out code live pend spec
             stopped unkilled).
  - exact (sstep_cfg_killed segs cfg ms mo n8 eff m1 out sig live pend spec killed).
  - exact (sstep_cfg_syscall_unmodeled segs cfg ms mo n8 live pend spec).
Qed.

Lemma sstep_cfg_of_sstep_nonalloc : forall ms mo x8 evs X,
  ms_svc_pending ms = Some x8 ->
  ~ In (bv_unsigned x8) alloc_mark_sysnos ->
  sstep segs (mkCfg ms mo) evs X -> sstep_cfg segs ACFG (mkCfg ms mo) evs X.
Proof.
  intros ms mo x8 evs X Hsvc Hn Hss. apply sstep_cfg_of_sstep; [exact Hss|].
  intros x8' eff m' evs' H _ _. rewrite Hsvc in H. injection H as <-.
  apply acfg_nonspurious. exact Hn.
Qed.

Lemma sstep_cfg_of_sstep_no : forall ms mo x8 n evs X,
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = n -> alloc_no_b n = false ->
  sstep segs (mkCfg ms mo) evs X -> sstep_cfg segs ACFG (mkCfg ms mo) evs X.
Proof.
  intros ms mo x8 n evs X pend number says_no run.
  pose proof (alloc_no_b_false n says_no) as off_list.
  rewrite <- number in off_list.
  exact (sstep_cfg_of_sstep_nonalloc ms mo x8 evs X pend off_list run).
Qed.

Lemma sstep_cfg_halted_none : forall cfg c e st,
  sstep_cfg segs cfg c e st -> m_halted (cfg_model c) = None.
Proof. intros cfg c e st H; inversion H; subst; cbn; assumption. Qed.

Lemma star_cfg_halted_nil : forall cfg c tr c',
  m_halted (cfg_model c) <> None -> star_cfg segs cfg c tr c' -> tr = [] /\ c' = c.
Proof.
  intros cfg c tr c' stopped path.
  revert stopped.
  destruct path as [c0 | c1 evs c2 rest c3 first _]; intro stopped.
  - split; reflexivity.
  - contradiction (stopped (sstep_cfg_halted_none _ _ _ _ first)).
Qed.

Lemma star_cfg_one : forall cfg c evs c',
  sstep_cfg segs cfg c evs (SNext c') -> star_cfg segs cfg c evs c'.
Proof.
  intros cfg c evs c' once.
  pose proof (star_cfg_step segs cfg c evs c' [] c' once (star_cfg_refl segs cfg c'))
    as chain.
  rewrite app_nil_r in chain. exact chain.
Qed.

Lemma obs_trace_cfg_nil : forall cfg c0, obs_trace_cfg segs cfg c0 [].
Proof.
  intros cfg c0. exists [], c0.
  exact (conj (star_cfg_refl segs cfg c0) (is_prefix_nil [])).
Qed.

Lemma sstep_cfg_sys_inv : forall cfg ms model x8 evs st,
  ms_svc_pending ms = Some x8 ->
  sstep_cfg segs cfg (mkCfg ms model) evs st ->
  (exists eff model' evs0,
      syscall_spec (sys_input segs ms x8) model (Ok eff model' evs0)
      /\ ~ spurious_refusal_cfg cfg (sys_input segs ms x8) model eff
      /\ m_halted model' = None
      /\ match materialize_model_accesses model' (syscall_effect_accesses eff) with
         | Some model'' => evs = evs0 /\ st = SNext (mkCfg (advance_past_svc (apply_effect ms eff)) model'')
         | None => evs = [] /\ st = SError
         end)
  \/ (exists eff model' evs0 code',
      syscall_spec (sys_input segs ms x8) model (Ok eff model' evs0)
      /\ m_halted model' = Some code' /\ m_killed model' = None
      /\ evs = evs0 ++ [ExitEv code' (m_fs model')] /\ st = SNext (mkCfg ms model'))
  \/ (exists eff model' evs0 sig,
      syscall_spec (sys_input segs ms x8) model (Ok eff model' evs0)
      /\ m_killed model' = Some sig
      /\ evs = evs0 ++ [KillEv sig (m_fs model')] /\ st = SNext (mkCfg ms model'))
  \/ (syscall_spec (sys_input segs ms x8) model Unmodeled /\ evs = [] /\ st = SError).
Proof.
  intros cfg ms model x8 evs st pend step.
  remember (mkCfg ms model) as here eqn:here_is.
  revert here_is.
  destruct step as
    [ ms0 m0 ms1 m1 live idle acct
    | ms0 m0 live idle acct
    | ms0 m0 live idle acct
    | ms0 m0 n8 eff m1 m2 out live pend0 spec fine alive mat
    | ms0 m0 n8 eff m1 out live pend0 spec fine alive mat
    | ms0 m0 n8 eff m1 out code live pend0 spec stopped unkilled
    | ms0 m0 n8 eff m1 out sig live pend0 spec killed
    | ms0 m0 n8 live pend0 spec ];
    intros [= -> ->].
  1-3: rewrite pend in idle; discriminate idle.
  all: rewrite pend in pend0; injection pend0 as <-.
  5: right; right; right; exact (conj spec (conj eq_refl eq_refl)).
  3: right; left; exists eff, m1, out, code;
     exact (conj spec (conj stopped (conj unkilled (conj eq_refl eq_refl)))).
  3: right; right; left; exists eff, m1, out, sig;
     exact (conj spec (conj killed (conj eq_refl eq_refl))).
  all: left; exists eff, m1, out;
       refine (conj spec (conj fine (conj alive _)));
       rewrite mat; split; reflexivity.
Qed.

Lemma nsp_no : forall ms x8 n m eff,
  bv_unsigned x8 = n -> alloc_no_b n = false ->
  ~ spurious_refusal_cfg ACFG (sys_input segs ms x8) m eff.
Proof.
  intros ms x8 n m eff number says_no.
  subst n.
  exact (acfg_nonspurious (sys_input segs ms x8) m eff (alloc_no_b_false _ says_no)).
Qed.

Lemma nsp_forced : forall cfg i m eff,
  (forall eff' m' evs', syscall_spec i m (Ok eff' m' evs') -> refusal_b i m (eff_ret eff') = true) ->
  ~ spurious_refusal_cfg cfg i m eff.
Proof.
  intros cfg i m eff all_refused [_ [_ [eff' [m' [evs' [spec' granted]]]]]].
  pose proof (all_refused eff' m' evs' spec') as refused.
  rewrite granted in refused. discriminate refused.
Qed.

Lemma nsp_det : forall cfg i m eff,
  (forall eff' m' evs', syscall_spec i m (Ok eff' m' evs') -> eff_ret eff' = eff_ret eff) ->
  ~ spurious_refusal_cfg cfg i m eff.
Proof.
  intros cfg i m eff same_ret.
  destruct (refusal_b i m (eff_ret eff)) eqn:verdict.
  - apply nsp_forced. intros eff' m' evs' spec'.
    rewrite (same_ret eff' m' evs' spec'). exact verdict.
  - exact (spurious_refusal_not_refusal cfg i m eff verdict).
Qed.

Lemma cfg_mat_nil : forall m, materialize_model_accesses m [] = Some m.
Proof. intros m. destruct m as [fd [maps lazy mat] io fs proc lim tm]; reflexivity. Qed.

Lemma node_chk_grant_cfg : forall ms model x8 (I : Type)
    (effs : I -> SyscallEffect) (ms' : I -> Model) (evs : I -> list event) (i0 : I),
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  injected_family_off ACFG (sys_input segs ms x8) = true ->
  (forall i, check_syscall (sys_input segs ms x8) (effs i) model = CheckOk (ms' i) (evs i)) ->
  (forall i, refusal_b (sys_input segs ms x8) model (eff_ret (effs i)) = false) ->
  (forall eff m' ev, check_syscall (sys_input segs ms x8) eff model = CheckOk m' ev ->
     refusal_b (sys_input segs ms x8) model (eff_ret eff) = false ->
     exists i, eff = effs i /\ m' = ms' i /\ ev = evs i) ->
  (forall eff m' ev, check_syscall (sys_input segs ms x8) eff model = CheckOk m' ev ->
     refusal_b (sys_input segs ms x8) model (eff_ret eff) = true -> m_halted m' = None) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  (forall i, m_halted (ms' i) = None) ->
  (forall i, syscall_effect_accesses (effs i) = []) ->
  (forall i, sstep_cfg segs ACFG (mkCfg ms model) (evs i)
               (SNext (mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i))))
  /\ (forall e st, sstep_cfg segs ACFG (mkCfg ms model) e st ->
        exists i, e = evs i /\ st = SNext (mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i))).
Proof.
  intros ms model x8 I effs ms' evs i0 live pend fam_off checked grants
    grants_listed refusals_live never_unmodeled outcomes_live no_access.
  split.
  - intros i.
    pose proof (check_syscall_sound_ok _ _ _ _ _ (checked i)) as spec_i.
    pose proof (spurious_refusal_not_refusal ACFG _ model (effs i) (grants i)) as fine_i.
    pose proof (cfg_mat_nil (ms' i)) as settles_i.
    rewrite <- (no_access i) in settles_i.
    exact (sstep_cfg_syscall segs ACFG ms model x8 (effs i) (ms' i) (ms' i) (evs i)
             live pend spec_i fine_i (outcomes_live i) settles_i).
  - intros e st step.
    remember (mkCfg ms model) as here eqn:here_is.
    revert here_is.
    destruct step as
      [ ms0 m0 ms1 m1 was_live idle acct
      | ms0 m0 was_live idle acct
      | ms0 m0 was_live idle acct
      | ms0 m0 n8 eff m1 m2 out was_live pend0 spec fine alive mat
      | ms0 m0 n8 eff m1 out was_live pend0 spec fine alive mat
      | ms0 m0 n8 eff m1 out code was_live pend0 spec stopped unkilled
      | ms0 m0 n8 eff m1 out sig was_live pend0 spec killed
      | ms0 m0 n8 was_live pend0 spec ];
      intros [= -> ->].
    1-3: congruence.
    all: assert (same_no : n8 = x8) by congruence; subst n8.
    5: exfalso; apply (never_unmodeled (effs i0));
       apply check_syscall_complete_unmodeled; exact spec.
    3-4: exfalso;
         assert (running : m_halted m1 = None)
           by (generalize (refusals_live eff m1 out (check_syscall_complete_ok _ _ _ _ _ spec))
                          (grants_listed eff m1 out (check_syscall_complete_ok _ _ _ _ _ spec));
               case (refusal_b (sys_input segs ms x8) model (eff_ret eff));
               [ intros when_refused _; exact (when_refused eq_refl)
               | intros _ when_granted;
                 destruct (when_granted eq_refl) as (i & _ & -> & _);
                 exact (outcomes_live i) ]);
         pose proof (m_killed_of_m_halted_none m1 running) as calm;
         congruence.
    1-2: assert (granted : refusal_b (sys_input segs ms x8) model (eff_ret eff) = false)
           by (apply not_true_is_false; intro refused; apply fine;
               exact (refusal_spurious_of_grant ACFG _ model eff (effs i0) (ms' i0) (evs i0)
                        fam_off refused (check_syscall_sound_ok _ _ _ _ _ (checked i0))
                        (grants i0)));
         destruct (grants_listed eff m1 out (check_syscall_complete_ok _ _ _ _ _ spec) granted)
           as (i & -> & -> & ->);
         pose proof (cfg_mat_nil (ms' i)) as settles;
         rewrite <- (no_access i) in settles.
    + exists i. split; [reflexivity | congruence].
    + congruence.
Qed.

End StepLift.

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

Lemma vm_base_ok_sound : forall h nZ a,
  vm_base_ok h nZ a = true ->
  (bv_unsigned a mod page_size = 0)%Z
  /\ (0 < bv_unsigned a)%Z
  /\ (bv_unsigned a + nZ <= alloc_top h)%Z
  /\ region_free (vm_reserved h ++ vm_maps h) a (Z_to_bv 64 nZ) = true.
Proof.
  intros h nZ a H. unfold vm_base_ok in H.
  apply andb_true_iff in H as [H Hfree].
  apply andb_true_iff in H as [H Htop].
  apply andb_true_iff in H as [Halign Hpos].
  apply Z.eqb_eq in Halign. apply Z.ltb_lt in Hpos. apply Z.leb_le in Htop.
  repeat split; assumption.
Qed.

Lemma vm_find_base_sound : forall h nZ a,
  vm_find_base h nZ = Some a ->
  (bv_unsigned a mod page_size = 0)%Z
  /\ (0 < bv_unsigned a)%Z
  /\ (bv_unsigned a + nZ <= alloc_top h)%Z
  /\ region_free (vm_reserved h ++ vm_maps h) a (Z_to_bv 64 nZ) = true.
Proof.
  intros h nZ a H. unfold vm_find_base in H.
  apply List.find_some in H as [_ H]. exact (vm_base_ok_sound h nZ a H).
Qed.

Lemma vm_gap_available_find : forall h nZ,
  vm_gap_available h nZ = true -> exists a, vm_find_base h nZ = Some a.
Proof.
  intros h nZ H. unfold vm_gap_available in H.
  destruct (vm_find_base h nZ) as [a|]; [now exists a | discriminate].
Qed.

Lemma region_free_false_In : forall maps lo n,
  region_free maps lo n = false ->
  exists a sz, In (a, sz) maps /\ iv_overlap lo n a sz = true.
Proof.
  induction maps as [|[b s] r IH]; intros lo n H; [discriminate|].
  cbn in H. destruct (iv_overlap lo n b s) eqn:Ho.
  - exists b, s. split; [now left|exact Ho].
  - cbn in H. destruct (IH lo n H) as (a & sz & Hin & Hov).
    exists a, sz. split; [now right|exact Hov].
Qed.

Lemma vm_base_ok_step : forall h nZ a,
  vm_base_ok h nZ a = true ->
  In a (vm_base_candidates h)
  \/ exists a', bv_unsigned a' = (bv_unsigned a - page_size)%Z
                /\ vm_base_ok h nZ a' = true.
Proof.
  intros h nZ a Hok.
  pose proof (vm_base_ok_sound h nZ a Hok) as (Hal & Hpos & Htop & Hfree).
  pose proof (bv_unsigned_in_range 64 a) as [_ Ha]. unfold bv_modulus in Ha.
  destruct (Z.eq_dec (bv_unsigned a) page_size) as [Heq|Hne].
  { left. left. rewrite <- Heq. apply Z_to_bv_bv_unsigned. }
  assert (Hge : (2 * page_size <= bv_unsigned a)%Z).
  { unfold page_size in *.
    pose proof (Z_div_mod_eq_full (bv_unsigned a) 4096). lia. }
  set (a' := Z_to_bv 64 (bv_unsigned a - page_size)).
  assert (Ua' : bv_unsigned a' = (bv_unsigned a - page_size)%Z).
  { subst a'. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
    unfold bv_modulus, page_size in *. lia. }
  destruct (vm_base_ok h nZ a') eqn:Hok'.
  { right. exists a'. split; [exact Ua'|exact Hok']. }
  left. unfold vm_base_ok in Hok'. rewrite Ua' in Hok'.
  assert (H1 : ((bv_unsigned a - page_size) mod page_size =? 0)%Z = true)
    by (apply Z.eqb_eq; rewrite Zminus_mod, Hal, Z_mod_same_full; reflexivity).
  assert (H2 : (0 <? bv_unsigned a - page_size)%Z = true)
    by (apply Z.ltb_lt; unfold page_size in *; lia).
  assert (H3 : (bv_unsigned a - page_size + nZ <=? alloc_top h)%Z = true)
    by (apply Z.leb_le; unfold page_size in *; lia).
  rewrite H1, H2, H3 in Hok'. cbn [andb] in Hok'.
  destruct (region_free_false_In _ _ _ Hok') as (lo & sz & Hin & Hov).
  pose proof (region_free_In _ _ _ _ _ Hfree Hin) as Hnov.
  unfold iv_overlap in Hov, Hnov. rewrite Ua' in Hov.
  apply andb_true_iff in Hov as [O1 O2].
  apply Z.ltb_lt in O1. apply Z.ltb_lt in O2.
  apply andb_false_iff in Hnov as [N|N]; apply Z.ltb_ge in N;
    [|unfold page_size in *; lia].
  right. apply in_map_iff. exists (lo, sz). split; [|exact Hin].
  cbn [fst snd].
  replace (page_round_up_Z (bv_unsigned lo + bv_unsigned sz))
    with (bv_unsigned a); [apply Z_to_bv_bv_unsigned|].
  unfold page_round_up_Z, page_size in *.
  pose proof (Z_div_mod_eq_full (bv_unsigned a) 4096) as Hq.
  rewrite Hal, Z.add_0_r in Hq.
  rewrite <- (Z.div_unique_pos (bv_unsigned lo + bv_unsigned sz + 4096 - 1)
                4096 (bv_unsigned a / 4096)
                (bv_unsigned lo + bv_unsigned sz + 4096 - 1
                 - 4096 * (bv_unsigned a / 4096))); lia.
Qed.

Lemma vm_find_base_complete_aux : forall h nZ k a,
  (bv_unsigned a <= Z.of_nat k * page_size)%Z ->
  vm_base_ok h nZ a = true ->
  exists c, In c (vm_base_candidates h) /\ vm_base_ok h nZ c = true.
Proof.
  intros h nZ k. induction k as [|k IH]; intros a Hk Hok.
  - pose proof (vm_base_ok_sound h nZ a Hok) as (_ & Hpos & _). cbn in Hk. lia.
  - destruct (vm_base_ok_step h nZ a Hok) as [Hin | (a' & Ua' & Hok')].
    + exists a. split; assumption.
    + apply (IH a'); [|exact Hok'].
      rewrite Ua'. rewrite Nat2Z.inj_succ in Hk. unfold page_size in *. lia.
Qed.

Lemma vm_find_base_complete : forall h nZ a,
  vm_base_ok h nZ a = true -> vm_gap_available h nZ = true.
Proof.
  intros h nZ a Hok.
  pose proof (bv_unsigned_in_range 64 a) as [Ha _].
  destruct (vm_find_base_complete_aux h nZ (Z.to_nat (bv_unsigned a)) a)
    as (c & Hin & Hc); [unfold page_size; lia|exact Hok|].
  unfold vm_gap_available, vm_find_base.
  destruct (List.find (vm_base_ok h nZ) (vm_base_candidates h)) eqn:Hf;
    [reflexivity|exfalso].
  pose proof (List.find_none _ _ Hf c Hin) as Hn. cbn beta in Hn.
  rewrite Hc in Hn. discriminate Hn.
Qed.

Lemma vm_gap_available_iff : forall h nZ,
  vm_gap_available h nZ = true <->
  exists a, (bv_unsigned a mod page_size = 0)%Z
            /\ (0 < bv_unsigned a)%Z
            /\ (bv_unsigned a + nZ <= alloc_top h)%Z
            /\ region_free (vm_reserved h ++ vm_maps h) a (Z_to_bv 64 nZ) = true.
Proof.
  intros h nZ. split.
  - intros H. apply vm_gap_available_find in H as [a Ha].
    exists a. exact (vm_find_base_sound h nZ a Ha).
  - intros (a & Hal & Hpos & Htop & Hfree).
    apply (vm_find_base_complete h nZ a). unfold vm_base_ok.
    rewrite (proj2 (Z.eqb_eq _ _) Hal), (proj2 (Z.ltb_lt _ _) Hpos),
      (proj2 (Z.leb_le _ _) Htop), Hfree. reflexivity.
Qed.

Definition mmap_grant_refusable (flags : word) (m : Model) (nZ : Z) : bool :=
  negb (mmap_noreserve_backed_ok flags m nZ)
  || negb (vm_gap_available (m_vmmaps m) nZ).

Definition mmap_reserve_refusable (m : Model) (nZ : Z) : bool :=
  negb (vm_gap_available (m_vmmaps m) nZ).

Definition mmap_fixed_fresh_refusable (flags : word) (m : Model) (nZ : Z)
    : bool :=
  negb (mmap_noreserve_backed_ok flags m nZ).

Definition mmap_fixed_commit_refusable (flags : word) (m : Model)
    (addr n : word) : bool :=
  negb (mmap_fixed_rw_budget_ok flags m addr n).

Definition mmap_fixed_span_refusable (flags : word) (m : Model)
    (addr n : word) : bool :=
  negb (mmap_fixed_rw_span_budget_ok flags m addr n).

Definition mprotect_errnos_when (forced : bool) : list Z :=
  if forced then mprotect_errnos else [].

Definition mprotect_refusable (m : Model) (addr n : word) : bool :=
  negb (mprotect_budget_ok m addr n).
