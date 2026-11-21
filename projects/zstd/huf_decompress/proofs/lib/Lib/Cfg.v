(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (alloc_no_b_false, transparent_instr, transparent_family_on and 1 more re-proved; adds acfg_family_off_215, refusal_b_215, sstep_cfg_svc_inv_g and 2 more; imports). *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool Classical_Prop.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi Syscall Dispatch SyscallTable.
(* [check_syscall] is 75d69e00:theories/LinuxProcessSem/Checks/ExecutableSpecs.v:61,
   and this file names it at :414, :416, :419, :421 and in five proofs below.  The
   module was missing here while the tree's other users of the name —
   lib/Lib/Nodes.v:8 and lib/AS/RefNodes.v:12 — both require it, so the file read
   as a missing definition and was a scope fault. *)
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect Mremap.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
Import ListNotations.
Open Scope bv_scope.

Definition ACFG : SpuriousCfg := alloc_only_cfg false.

(* [comment removed for export] *)

Lemma acfg_family_off_in : forall i,
  injected_family_off ACFG i = true -> In (bv_unsigned (in_sysno i)) alloc_mark_sysnos.
Proof.
  intros i fam_off.
  unfold injected_family_off in fam_off.
  destruct (injected_arm (bv_unsigned (in_sysno i))) as [arm|] eqn:arm_found;
    [|discriminate fam_off].
  assert (alloc_fam : ia_family arm = FamAlloc)
    by (destruct (ia_family arm); first [reflexivity | discriminate fam_off]).
  exact (alloc_family_dispatched _ arm arm_found alloc_fam).
Qed.

Lemma acfg_family_on_notin : forall i,
  ~ In (bv_unsigned (in_sysno i)) alloc_mark_sysnos -> injected_family_off ACFG i = false.
Proof.
  intros i outside.
  apply not_true_is_false. intro fam_off.
  exact (outside (acfg_family_off_in i fam_off)).
Qed.

(* [comment removed for export] *)
Lemma acfg_nonspurious : forall i m eff,
  ~ In (bv_unsigned (in_sysno i)) alloc_mark_sysnos ->
  ~ spurious_refusal_cfg ACFG i m eff.
Proof.
  intros i m eff outside.
  exact (spurious_refusal_family_on ACFG i m eff (acfg_family_on_notin i outside)).
Qed.

Definition alloc_no_b (n : Z) : bool := existsb (Z.eqb n) alloc_mark_sysnos.

Lemma alloc_no_b_false : forall n, alloc_no_b n = false -> ~ In n alloc_mark_sysnos.
Proof.
  intros n nonalloc.
  cbn [alloc_mark_sysnos In].
  (* 08b1429: alloc_mark_sysnos gained 215; walk the list without a fixed shape *)
  intros Hin; repeat (destruct Hin as [<- | Hin]; [exact (diff_true_false nonalloc)|]); destruct Hin.
Qed.

Lemma acfg_nonspurious_no : forall segs ms x8 n m eff,
  bv_unsigned x8 = n -> alloc_no_b n = false ->
  ~ spurious_refusal_cfg ACFG (sys_input segs ms x8) m eff.
Proof.
  intros segs ms x8 n m eff num_n nonalloc.
  pose proof (alloc_no_b_false n nonalloc) as outside.
  subst n.
  exact (acfg_nonspurious (sys_input segs ms x8) m eff outside).
Qed.

Lemma acfg_family_off_222 : forall i, bv_unsigned (in_sysno i) = 222%Z -> injected_family_off ACFG i = true.
Proof.
  intros i sysno_k.
  unfold injected_family_off. rewrite sysno_k. reflexivity.
Qed.
Lemma acfg_family_off_226 : forall i, bv_unsigned (in_sysno i) = 226%Z -> injected_family_off ACFG i = true.
Proof.
  intros i sysno_k.
  unfold injected_family_off. rewrite sysno_k. reflexivity.
Qed.
Lemma acfg_family_off_216 : forall i, bv_unsigned (in_sysno i) = 216%Z -> injected_family_off ACFG i = true.
Proof.
  intros i sysno_k.
  unfold injected_family_off. rewrite sysno_k. reflexivity.
Qed.
Lemma acfg_family_off_214 : forall i, bv_unsigned (in_sysno i) = 214%Z -> injected_family_off ACFG i = true.
Proof.
  intros i sysno_k.
  unfold injected_family_off. rewrite sysno_k. reflexivity.
Qed.
(* 215 (munmap) is the row the four lemmas above were missing.  At 727298f3 it IS
   in alloc_mark_sysnos ([214;215;216;222;226], Run.v:1865) and its injected_table
   row is FamAlloc (Run.v:1788 "munmap  mkInjectedArm 215 FamAlloc munmap_errnos"),
   so under ACFG = alloc_only_cfg false (sc_alloc = false, Run.v:1689) the family is
   OFF and the nonalloc route transparent_nonalloc_no takes for 64 is unavailable
   here -- alloc_no_b 215 = true. *)
Lemma acfg_family_off_215 : forall i, bv_unsigned (in_sysno i) = 215%Z -> injected_family_off ACFG i = true.
Proof.
  intros inp Hno. unfold injected_family_off.
  replace (bv_unsigned (in_sysno inp)) with 215%Z by (symmetry; exact Hno). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma refusal_b_222 : forall i m r, bv_unsigned (in_sysno i) = 222%Z ->
  refusal_b i m r = ret_in_errnos mmap_errnos r.
Proof.
  intros i m r sysno_k.
  unfold refusal_b. rewrite sysno_k. reflexivity.
Qed.
Lemma refusal_b_226 : forall i m r, bv_unsigned (in_sysno i) = 226%Z ->
  refusal_b i m r = ret_in_errnos mprotect_errnos r.
Proof.
  intros i m r sysno_k.
  unfold refusal_b. rewrite sysno_k. reflexivity.
Qed.
Lemma refusal_b_216 : forall i m r, bv_unsigned (in_sysno i) = 216%Z ->
  refusal_b i m r = ret_in_errnos mremap_errnos r.
Proof.
  intros i m r sysno_k.
  unfold refusal_b. rewrite sysno_k. reflexivity.
Qed.
Lemma refusal_b_214 : forall i m r, bv_unsigned (in_sysno i) = 214%Z ->
  refusal_b i m r = brk_refusal_b m (in_arg i 0) r.
Proof.
  intros i m r sysno_k.
  unfold refusal_b. rewrite sysno_k. reflexivity.
Qed.
Lemma refusal_b_215 : forall i m r, bv_unsigned (in_sysno i) = 215%Z ->
  refusal_b i m r = ret_in_errnos munmap_errnos r.
Proof.
  intros inp mdl ret Hno. unfold refusal_b.
  replace (bv_unsigned (in_sysno inp)) with 215%Z by (symmetry; exact Hno). reflexivity.
Qed.

Lemma ret_in_errnos_ENOMEM : forall r,
  ret_in_errnos [ENOMEM] r = bv_eqb r (errno_ret ENOMEM).
Proof.
  intros r.
  cbn [ret_in_errnos existsb].
  exact (orb_false_r _).
Qed.

Lemma ret_in_errnos_errno : forall es e, In e es -> ret_in_errnos es (errno_ret e) = true.
Proof.
  intros es e Hin. unfold ret_in_errnos. apply existsb_exists. exists e. split; [exact Hin|].
  apply bv_eqb_eq. reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma refusal_spurious_of_grant : forall cfg i m eff eff' m' evs',
  injected_family_off cfg i = true ->
  refusal_b i m (eff_ret eff) = true ->
  syscall_spec i m (Ok eff' m' evs') ->
  refusal_b i m (eff_ret eff') = false ->
  spurious_refusal_cfg cfg i m eff.
Proof.
  intros cfg i m eff eff' m' evs' fam_off refused grant grant_free.
  refine (conj fam_off (conj refused _)).
  exists eff', m', evs'. exact (conj grant grant_free).
Qed.

(* [comment removed for export] *)
Lemma nonspurious_not_refusal_of_grant : forall cfg i m eff eff' m' evs',
  injected_family_off cfg i = true ->
  ~ spurious_refusal_cfg cfg i m eff ->
  syscall_spec i m (Ok eff' m' evs') ->
  refusal_b i m (eff_ret eff') = false ->
  refusal_b i m (eff_ret eff) = false.
Proof.
  intros cfg i m eff eff' m' evs' fam_off not_spur grant grant_free.
  apply not_true_is_false. intro refused.
  exact (not_spur (refusal_spurious_of_grant cfg i m eff eff' m' evs'
                     fam_off refused grant grant_free)).
Qed.

(* [comment removed for export] *)
Lemma nonspurious_refusal_no_grant : forall cfg i m eff,
  ~ spurious_refusal_cfg cfg i m eff ->
  injected_family_off cfg i = true ->
  refusal_b i m (eff_ret eff) = true ->
  forall eff' m' evs', syscall_spec i m (Ok eff' m' evs') -> refusal_b i m (eff_ret eff') = true.
Proof.
  intros cfg i m eff not_spur fam_off refused eff' m' evs' grant.
  apply not_false_is_true. intro grant_free.
  exact (not_spur (refusal_spurious_of_grant cfg i m eff eff' m' evs'
                     fam_off refused grant grant_free)).
Qed.

(* [comment removed for export] *)
Lemma not_spurious_forced : forall cfg i m eff,
  (forall eff' m' evs', syscall_spec i m (Ok eff' m' evs') -> refusal_b i m (eff_ret eff') = true) ->
  ~ spurious_refusal_cfg cfg i m eff.
Proof.
  intros cfg i m eff Hall (_ & _ & eff' & m' & evs' & Hspec & Hnr).
  rewrite (Hall eff' m' evs' Hspec) in Hnr. discriminate Hnr.
Qed.

(* [comment removed for export] *)
Lemma spurious_refusal_transport : forall cfg i1 i2 m eff,
  in_sysno i1 = in_sysno i2 ->
  in_arg i1 0 = in_arg i2 0 ->
  (forall eff' m' evs', syscall_spec i1 m (Ok eff' m' evs') <-> syscall_spec i2 m (Ok eff' m' evs')) ->
  spurious_refusal_cfg cfg i1 m eff <-> spurious_refusal_cfg cfg i2 m eff.
Proof.
  intros cfg i1 i2 m eff same_no same_arg0 same_spec.
  unfold spurious_refusal_cfg, injected_family_off, refusal_b.
  rewrite same_no, same_arg0.
  setoid_rewrite same_spec.
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma exists_nonspurious : forall cfg i m eff0 m0 evs0,
  syscall_spec i m (Ok eff0 m0 evs0) ->
  exists eff m' evs, syscall_spec i m (Ok eff m' evs) /\ ~ spurious_refusal_cfg cfg i m eff.
Proof.
  intros cfg i m eff0 m0 evs0 spec0.
  apply NNPP. intro no_witness.
  assert (spur0 : spurious_refusal_cfg cfg i m eff0).
  { apply NNPP. intro not_spur0.
    apply no_witness. exists eff0, m0, evs0. exact (conj spec0 not_spur0). }
  destruct spur0 as (_ & _ & eff' & m' & evs' & grant & grant_free).
  apply no_witness. exists eff', m', evs'.
  exact (conj grant (spurious_refusal_not_refusal cfg i m eff' grant_free)).
Qed.

(* [comment removed for export] *)

Section Steps.
Variable segs : list Segment.

Lemma sstep_of_cfg : forall cfg c e st, sstep_cfg segs cfg c e st -> sstep segs c e st.
Proof. intros cfg c e st H. exact (sstep_cfg_sub segs cfg c e st H). Qed.

Lemma star_of_cfg : forall cfg c tr c', star_cfg segs cfg c tr c' -> star segs c tr c'.
Proof. intros cfg c tr c' H. exact (star_cfg_sub segs cfg c tr c' H). Qed.

(* [comment removed for export] *)
Definition cfg_transparent (c : config) : Prop :=
  forall e st, sstep segs c e st -> sstep_cfg segs ACFG c e st.

Lemma transparent_instr : forall ms model,
  ms_svc_pending ms = None -> cfg_transparent (mkCfg ms model).
Proof.
  intros ms model Hsvc e st H. inversion H; subst;
    try (match goal with H1 : ms_svc_pending ms = Some _ |- _ => rewrite Hsvc in H1; discriminate H1 end).
  - eapply sstep_cfg_instr; eassumption.
  - eapply sstep_cfg_instr_fault; eassumption.
  - eapply sstep_cfg_instr_unmodeled; eassumption.
  - eapply sstep_cfg_vdso_call; eassumption.
  - eapply sstep_cfg_vdso_materialization_fault; eassumption.
  - eapply sstep_cfg_vdso_unmodeled; eassumption.
Qed.

Lemma transparent_family_on : forall ms model x8,
  ms_svc_pending ms = Some x8 ->
  injected_family_off ACFG (sys_input segs ms x8) = false ->
  cfg_transparent (mkCfg ms model).
Proof.
  intros ms model x8 svc fam_on e st step.
  remember (mkCfg ms model) as here eqn:here_is.
  destruct step as
    [ms1 m1 ms' m' alive idle run | ms1 m1 alive idle run | ms1 m1 alive idle run nv
    | ms1 m1 fn n eff m' m'' out alive idle run efn eno spec eret alive' mat
    | ms1 m1 fn n eff m' out alive idle run efn eno spec eret alive' mat
    | ms1 m1 fn alive idle run efn unm
    | ms1 m1 y8 eff m' m'' out alive pend spec alive' mat
    | ms1 m1 y8 eff m' out alive pend spec alive' mat
    | ms1 m1 y8 eff m' out code alive pend spec halted unkilled
    | ms1 m1 y8 eff m' out sig alive pend spec killed
    | ms1 m1 y8 alive pend spec ];
    injection here_is as -> ->.
  1-6: rewrite svc in idle; discriminate idle.
  all: rewrite svc in pend; injection pend as <-.
  - exact (sstep_cfg_syscall segs ACFG ms model x8 eff m' m'' out alive svc spec
             (spurious_refusal_family_on _ _ _ _ fam_on) alive' mat).
  - exact (sstep_cfg_syscall_materialization_fault segs ACFG ms model x8 eff m' out alive svc spec
             (spurious_refusal_family_on _ _ _ _ fam_on) alive' mat).
  - exact (sstep_cfg_exit segs ACFG ms model x8 eff m' out code alive svc spec halted unkilled).
  - exact (sstep_cfg_killed segs ACFG ms model x8 eff m' out sig alive svc spec killed).
  - exact (sstep_cfg_syscall_unmodeled segs ACFG ms model x8 alive svc spec).
Qed.

Lemma transparent_nonalloc : forall ms model x8,
  ms_svc_pending ms = Some x8 ->
  ~ In (bv_unsigned x8) alloc_mark_sysnos ->
  cfg_transparent (mkCfg ms model).
Proof.
  intros ms model x8 Hsvc Hnin. apply (transparent_family_on ms model x8 Hsvc).
  apply acfg_family_on_notin. exact Hnin.
Qed.

Lemma transparent_nonalloc_no : forall ms model x8 n,
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = n -> alloc_no_b n = false ->
  cfg_transparent (mkCfg ms model).
Proof.
  intros ms model x8 n svc num_n nonalloc.
  pose proof (alloc_no_b_false n nonalloc) as outside.
  subst n.
  exact (transparent_nonalloc ms model x8 svc outside).
Qed.

(* [comment removed for export] *)
Lemma sstep_cfg_syscall_nonrefusal : forall cfg ms model x8 eff model' model'' evs,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
  refusal_b (sys_input segs ms x8) model (eff_ret eff) = false ->
  m_halted model' = None ->
  materialize_model_accesses model' (syscall_effect_accesses eff) = Some model'' ->
  sstep_cfg segs cfg (mkCfg ms model) evs
            (SNext (mkCfg (advance_past_svc (apply_effect ms eff)) model'')).
Proof.
  intros cfg ms model x8 eff model' model'' evs alive svc spec grant_free alive' mat.
  exact (sstep_cfg_syscall segs cfg ms model x8 eff model' model'' evs alive svc spec
           (spurious_refusal_not_refusal cfg _ model eff grant_free) alive' mat).
Qed.

(* The syscall-side inversion of sstep_cfg, generic in the configuration.  It is
   the text of this unit's own Lib/Nodes.v:857 sstep_cfg_svc_inv (which is fixed
   at ACFG and lives above this file in the dependency order, so it cannot be
   reused here) with cfg left free.  The three instr arms and the three vDSO arms
   of 727298f3:Run.v:2222-2284 all carry ms_svc_pending ms = None and die on
   congruence; the five that remain are Run.v:2285-2322.  What this gives that
   sstep_of_cfg throws away is the fourth premise of sstep_cfg_syscall
   (Run.v:2289), ~ spurious_refusal_cfg -- which is the whole content of the
   filter and the only way to refute a step. *)
Lemma sstep_cfg_svc_inv_g : forall cfg ms mo x8 evs X,
  ms_svc_pending ms = Some x8 -> sstep_cfg segs cfg (mkCfg ms mo) evs X ->
  (exists eff mo' mo'', syscall_spec (sys_input segs ms x8) mo (Ok eff mo' evs) /\
                  ~ spurious_refusal_cfg cfg (sys_input segs ms x8) mo eff /\ m_halted mo' = None /\
                  materialize_model_accesses mo' (syscall_effect_accesses eff) = Some mo'' /\
                  X = SNext (mkCfg (advance_past_svc (apply_effect ms eff)) mo''))
  \/ (exists eff mo' evs0, syscall_spec (sys_input segs ms x8) mo (Ok eff mo' evs0) /\
                  ~ spurious_refusal_cfg cfg (sys_input segs ms x8) mo eff /\ m_halted mo' = None /\
                  materialize_model_accesses mo' (syscall_effect_accesses eff) = None /\
                  evs = [] /\ X = SError)
  \/ (exists eff mo' evs0 code, syscall_spec (sys_input segs ms x8) mo (Ok eff mo' evs0) /\ m_halted mo' = Some code /\
                  m_killed mo' = None /\
                  evs = evs0 ++ [ExitEv code (m_fs mo')] /\ X = SNext (mkCfg ms mo'))
  \/ (exists eff mo' evs0 sig, syscall_spec (sys_input segs ms x8) mo (Ok eff mo' evs0) /\ m_killed mo' = Some sig /\
                  evs = evs0 ++ [KillEv sig (m_fs mo')] /\ X = SNext (mkCfg ms mo'))
  \/ (syscall_spec (sys_input segs ms x8) mo Unmodeled /\ evs = [] /\ X = SError).
Proof.
  intros cfg ms mo x8 evs X Hsvc Hst. inversion Hst; subst; try congruence;
    match goal with H : ms_svc_pending ms = Some ?x |- _ => rewrite Hsvc in H; inversion H; subst end.
  - left. eexists _, _, _. eauto.
  - right; left. eexists _, _, _. eauto 7.
  - right; right; left. eexists _, _, _, _. eauto 6.
  - right; right; right; left. eexists _, _, _, _. eauto.
  - right; right; right; right. auto.
Qed.

End Steps.

(* [comment removed for export] *)

Section Star.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.

Lemma star_cfg_one : forall c evs c',
  sstep_cfg segs cfg c evs (SNext c') -> star_cfg segs cfg c evs c'.
Proof.
  intros c evs c' one.
  rewrite <- (app_nil_r evs).
  exact (star_cfg_step segs cfg c evs c' [] c' one (star_cfg_refl segs cfg c')).
Qed.

Lemma star_cfg_trans : forall c1 tr1 c2 tr2 c3,
  star_cfg segs cfg c1 tr1 c2 -> star_cfg segs cfg c2 tr2 c3 ->
  star_cfg segs cfg c1 (tr1 ++ tr2) c3.
Proof.
  intros c1 tr1 c2 tr2 c3 first_leg.
  induction first_leg as [c | a evs b tr d run1 rest stitch]; intros second_leg.
  - exact second_leg.
  - rewrite <- app_assoc.
    exact (star_cfg_step segs cfg a evs b (tr ++ tr2) c3 run1 (stitch second_leg)).
Qed.

Lemma obs_trace_cfg_nil : forall c0, obs_trace_cfg segs cfg c0 [].
Proof. intros c0. exists [], c0. split; [apply star_cfg_refl | exact I]. Qed.

Lemma sstep_cfg_halted_none : forall c e st,
  sstep_cfg segs cfg c e st -> m_halted (cfg_model c) = None.
Proof. intros c e st H; inversion H; subst; cbn; assumption. Qed.

Lemma star_cfg_halted_nil : forall c tr c',
  m_halted (cfg_model c) <> None -> star_cfg segs cfg c tr c' -> tr = [] /\ c' = c.
Proof.
  intros c tr c' Hh Hstar. inversion Hstar as [|c1 evs c2 tr2 c3 Hss Hstar2]; subst.
  - split; reflexivity.
  - exfalso. apply Hh. eapply sstep_cfg_halted_none. exact Hss.
Qed.

Lemma reaches_error_cfg_here : forall c evs,
  sstep_cfg segs cfg c evs SError -> reaches_error_cfg segs cfg c.
Proof. intros c evs H. exists [], c, evs. split; [apply star_cfg_refl | exact H]. Qed.

Lemma reaches_error_cfg_step : forall c evs c',
  sstep_cfg segs cfg c evs (SNext c') ->
  reaches_error_cfg segs cfg c' -> reaches_error_cfg segs cfg c.
Proof.
  intros c evs c' Hs (tr & c2 & evs2 & Hst & He).
  exists (evs ++ tr), c2, evs2. split; [eapply star_cfg_step; eassumption | exact He].
Qed.

End Star.

Section SysInv.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.

Lemma sstep_cfg_sys_inv : forall ms model x8 evs st,
  ms_svc_pending ms = Some x8 ->
  sstep_cfg segs cfg (mkCfg ms model) evs st ->
  let i := sys_input segs ms x8 in
  (exists eff model' evs0,
      syscall_spec i model (Ok eff model' evs0)
      /\ ~ spurious_refusal_cfg cfg i model eff
      /\ m_halted model' = None
      /\ match materialize_model_accesses model' (syscall_effect_accesses eff) with
         | Some model'' => evs = evs0 /\ st = SNext (mkCfg (advance_past_svc (apply_effect ms eff)) model'')
         | None => evs = [] /\ st = SError
         end)
  \/ (exists eff model' evs0 code',
      syscall_spec i model (Ok eff model' evs0)
      /\ m_halted model' = Some code' /\ m_killed model' = None
      /\ evs = evs0 ++ [ExitEv code' (m_fs model')] /\ st = SNext (mkCfg ms model'))
  \/ (exists eff model' evs0 sig,
      syscall_spec i model (Ok eff model' evs0)
      /\ m_killed model' = Some sig
      /\ evs = evs0 ++ [KillEv sig (m_fs model')] /\ st = SNext (mkCfg ms model'))
  \/ (syscall_spec i model Unmodeled /\ evs = [] /\ st = SError).
Proof.
  intros ms model x8 evs st svc step i.
  remember (mkCfg ms model) as here eqn:here_is.
  destruct step as
    [ms1 m1 ms' m' alive idle run | ms1 m1 alive idle run | ms1 m1 alive idle run nv
    | ms1 m1 fn n eff m' m'' out alive idle run efn eno spec eret alive' mat
    | ms1 m1 fn n eff m' out alive idle run efn eno spec eret alive' mat
    | ms1 m1 fn alive idle run efn unm
    | ms1 m1 y8 eff m' m'' out alive pend spec not_spur alive' mat
    | ms1 m1 y8 eff m' out alive pend spec not_spur alive' mat
    | ms1 m1 y8 eff m' out code alive pend spec halted unkilled
    | ms1 m1 y8 eff m' out sig alive pend spec killed
    | ms1 m1 y8 alive pend spec ];
    injection here_is as -> ->.
  1-6: rewrite svc in idle; discriminate idle.
  all: rewrite svc in pend; injection pend as <-.
  1-2: left; exists eff, m', out;
       refine (conj spec (conj not_spur (conj alive' _))); rewrite mat; split; reflexivity.
  - right; left. exists eff, m', out, code.
    exact (conj spec (conj halted (conj unkilled (conj eq_refl eq_refl)))).
  - right; right; left. exists eff, m', out, sig.
    exact (conj spec (conj killed (conj eq_refl eq_refl))).
  - right; right; right. exact (conj spec (conj eq_refl eq_refl)).
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
      | ms0 m0 fn n eff m1 m2 out was_live idle acct
      | ms0 m0 fn n eff m1 out was_live idle acct
      | ms0 m0 fn was_live idle acct
      | ms0 m0 n8 eff m1 m2 out was_live pend0 spec fine alive mat
      | ms0 m0 n8 eff m1 out was_live pend0 spec fine alive mat
      | ms0 m0 n8 eff m1 out code was_live pend0 spec stopped unkilled
      | ms0 m0 n8 eff m1 out sig was_live pend0 spec killed
      | ms0 m0 n8 was_live pend0 spec ];
      intros [= -> ->].
    1-6: congruence.
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

End SysInv.
