(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Classical_Prop.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi Syscall Dispatch SyscallTable.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect Mremap.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
Import ListNotations.
Local Open Scope bv_scope.
Definition ACFG : SpuriousCfg := alloc_only_cfg false.
Lemma acfg_family_off_in (i : SyscallInput)
  : injected_family_off ACFG i = true
  -> In (bv_unsigned (in_sysno i)) alloc_mark_sysnos.
Proof.
  unfold injected_family_off.
  destruct (injected_arm (bv_unsigned (in_sysno i))) as [arm|] eqn:Earm; intros Hneg; [|discriminate Hneg].
  apply (alloc_family_dispatched _ arm Earm).
  destruct (ia_family arm); [reflexivity | discriminate Hneg ..].
Qed.

Lemma acfg_family_on_notin (i : SyscallInput)
  : ~ In (bv_unsigned (in_sysno i)) alloc_mark_sysnos
  -> injected_family_off ACFG i = false.
Proof.
  intros Hout. destruct (injected_family_off ACFG i) eqn:Efam; [|reflexivity].
  destruct (Hout (acfg_family_off_in i Efam)).
Qed.
Lemma acfg_nonspurious (i : SyscallInput) (m : Model) (eff : SyscallEffect)
  : ~ In (bv_unsigned (in_sysno i)) alloc_mark_sysnos
  -> ~ spurious_refusal_cfg ACFG i m eff.
Proof. intros Hout. exact (spurious_refusal_family_on ACFG i m eff (acfg_family_on_notin i Hout)). Qed.
Definition alloc_no_b (n : Z) : bool :=
  match List.find (Z.eqb n) alloc_mark_sysnos with Some _ => true | None => false end.
Lemma alloc_no_b_false (n : Z)
  : alloc_no_b n = false
  -> ~ In n alloc_mark_sysnos.
Proof.
  intros Hnb Hmark.
  destruct Hmark as [E | [E | [E | [E | []]]]]; subst n; discriminate Hnb.
Qed.
Lemma acfg_nonspurious_no (segs : list Segment) (ms : machine_state) (x8 : word) (n : Z)
    (m : Model) (eff : SyscallEffect)
  : bv_unsigned x8 = n
  -> alloc_no_b n = false
  -> ~ spurious_refusal_cfg ACFG (sys_input segs ms x8) m eff.
Proof. intros <- Hnb. apply acfg_nonspurious. exact (alloc_no_b_false _ Hnb). Qed.
Lemma acfg_family_off_of_in (i : SyscallInput)
  : In (bv_unsigned (in_sysno i)) alloc_mark_sysnos
  -> injected_family_off ACFG i = true.
Proof.
  intros Hmark. unfold injected_family_off.
  destruct Hmark as [E | [E | [E | [E | []]]]]; rewrite <- E; reflexivity.
Qed.

Lemma acfg_family_off_222 (i : SyscallInput)
  : bv_unsigned (in_sysno i) = 222%Z -> injected_family_off ACFG i = true.
Proof. intros Hsys. apply acfg_family_off_of_in. rewrite Hsys. now right; right; left. Qed.
Lemma acfg_family_off_226 (i : SyscallInput)
  : bv_unsigned (in_sysno i) = 226%Z -> injected_family_off ACFG i = true.
Proof. intros Hsys. apply acfg_family_off_of_in. rewrite Hsys. now right; right; right; left. Qed.
Lemma acfg_family_off_216 (i : SyscallInput)
  : bv_unsigned (in_sysno i) = 216%Z -> injected_family_off ACFG i = true.
Proof. intros Hsys. apply acfg_family_off_of_in. rewrite Hsys. now right; left. Qed.
Lemma acfg_family_off_214 (i : SyscallInput)
  : bv_unsigned (in_sysno i) = 214%Z -> injected_family_off ACFG i = true.
Proof. intros Hsys. apply acfg_family_off_of_in. rewrite Hsys. now left. Qed.

Lemma refusal_b_222 (i : SyscallInput) (m : Model) (r : word)
  : bv_unsigned (in_sysno i) = 222%Z -> refusal_b i m r = ret_in_errnos mmap_errnos r.
Proof. intros Hsys. unfold refusal_b. now rewrite Hsys. Qed.
Lemma refusal_b_226 (i : SyscallInput) (m : Model) (r : word)
  : bv_unsigned (in_sysno i) = 226%Z -> refusal_b i m r = ret_in_errnos mprotect_errnos r.
Proof. intros Hsys. unfold refusal_b. now rewrite Hsys. Qed.
Lemma refusal_b_216 (i : SyscallInput) (m : Model) (r : word)
  : bv_unsigned (in_sysno i) = 216%Z -> refusal_b i m r = ret_in_errnos mremap_errnos r.
Proof. intros Hsys. unfold refusal_b. now rewrite Hsys. Qed.
Lemma refusal_b_214 (i : SyscallInput) (m : Model) (r : word)
  : bv_unsigned (in_sysno i) = 214%Z -> refusal_b i m r = brk_refusal_b m (in_arg i 0) r.
Proof. intros Hsys. unfold refusal_b. now rewrite Hsys. Qed.
Lemma ret_in_errnos_ENOMEM (r : word)
  : ret_in_errnos [ENOMEM] r = bv_eqb r (errno_ret ENOMEM).
Proof. exact (orb_false_r (bv_eqb r (errno_ret ENOMEM))). Qed.
Lemma ret_in_errnos_errno : forall es e, In e es -> ret_in_errnos es (errno_ret e) = true.
Proof.
  intros es e Hin. unfold ret_in_errnos. apply existsb_exists. exists e. split; [exact Hin|].
  apply bv_eqb_eq. reflexivity.
Qed.

Lemma refusal_spurious_of_grant (cfg : SpuriousCfg) (i : SyscallInput) (m : Model)
    (eff eff' : SyscallEffect) (m' : Model) (evs' : list event)
  : injected_family_off cfg i = true
  -> refusal_b i m (eff_ret eff) = true
  -> syscall_spec i m (Ok eff' m' evs')
  -> refusal_b i m (eff_ret eff') = false
  -> spurious_refusal_cfg cfg i m eff.
Proof.
  intros Hfam Href Hspec Hgrant.
  refine (conj Hfam (conj Href _)). exists eff', m', evs'. exact (conj Hspec Hgrant).
Qed.
Lemma nonspurious_not_refusal_of_grant (cfg : SpuriousCfg) (i : SyscallInput) (m : Model)
    (eff eff' : SyscallEffect) (m' : Model) (evs' : list event)
  : injected_family_off cfg i = true
  -> ~ spurious_refusal_cfg cfg i m eff
  -> syscall_spec i m (Ok eff' m' evs')
  -> refusal_b i m (eff_ret eff') = false
  -> refusal_b i m (eff_ret eff) = false.
Proof.
  intros Hfam Hnot Hspec Hgrant.
  apply not_true_is_false. intros Href. apply Hnot.
  exact (refusal_spurious_of_grant cfg i m eff eff' m' evs' Hfam Href Hspec Hgrant).
Qed.
Lemma nonspurious_refusal_no_grant (cfg : SpuriousCfg) (i : SyscallInput) (m : Model)
    (eff : SyscallEffect)
  : ~ spurious_refusal_cfg cfg i m eff
  -> injected_family_off cfg i = true
  -> refusal_b i m (eff_ret eff) = true
  -> forall (eff' : SyscallEffect) (m' : Model) (evs' : list event), syscall_spec i m (Ok eff' m' evs')
  -> refusal_b i m (eff_ret eff') = true.
Proof.
  intros Hnot Hfam Href eff' m' evs' Hspec.
  apply not_false_is_true. intros Hgrant. apply Hnot.
  exact (refusal_spurious_of_grant cfg i m eff eff' m' evs' Hfam Href Hspec Hgrant).
Qed.

Lemma not_spurious_forced : forall cfg i m eff,
  (forall eff' m' evs', syscall_spec i m (Ok eff' m' evs') -> refusal_b i m (eff_ret eff') = true) ->
  ~ spurious_refusal_cfg cfg i m eff.
Proof.
  intros cfg i m eff Hall (_ & _ & eff' & m' & evs' & Hspec & Hnr).
  rewrite (Hall eff' m' evs' Hspec) in Hnr. discriminate Hnr.
Qed.
Lemma refusal_b_input_eq (i1 i2 : SyscallInput) (m : Model) (r : word)
  : in_sysno i1 = in_sysno i2
  -> in_arg i1 0 = in_arg i2 0
  -> refusal_b i1 m r = refusal_b i2 m r.
Proof. intros Esys Earg. unfold refusal_b. now rewrite Esys, Earg. Qed.

Lemma spurious_refusal_input_dir (cfg : SpuriousCfg) (i1 i2 : SyscallInput) (m : Model)
    (eff : SyscallEffect)
  : in_sysno i1 = in_sysno i2
  -> in_arg i1 0 = in_arg i2 0
  -> (forall (e : SyscallEffect) (m' : Model) (evs' : list event),
        syscall_spec i1 m (Ok e m' evs') -> syscall_spec i2 m (Ok e m' evs'))
  -> spurious_refusal_cfg cfg i1 m eff
  -> spurious_refusal_cfg cfg i2 m eff.
Proof.
  intros Esys Earg Hmove (Hfam & Href & e & m' & evs' & Hspec & Hgrant).
  apply (refusal_spurious_of_grant cfg i2 m eff e m' evs').
  - unfold injected_family_off in *. now rewrite <- Esys.
  - now rewrite <- (refusal_b_input_eq i1 i2 m _ Esys Earg).
  - exact (Hmove e m' evs' Hspec).
  - now rewrite <- (refusal_b_input_eq i1 i2 m _ Esys Earg).
Qed.

Lemma spurious_refusal_transport (cfg : SpuriousCfg) (i1 i2 : SyscallInput) (m : Model)
    (eff : SyscallEffect)
  : in_sysno i1 = in_sysno i2
  -> in_arg i1 0 = in_arg i2 0
  -> (forall (eff' : SyscallEffect) (m' : Model) (evs' : list event),
        syscall_spec i1 m (Ok eff' m' evs') <-> syscall_spec i2 m (Ok eff' m' evs'))
  -> (spurious_refusal_cfg cfg i1 m eff <-> spurious_refusal_cfg cfg i2 m eff).
Proof.
  intros Esys Earg Hiff. split.
  - apply spurious_refusal_input_dir; [exact Esys | exact Earg | intros e m' evs'; apply Hiff].
  - apply spurious_refusal_input_dir; [now symmetry | now symmetry | intros e m' evs'; apply Hiff].
Qed.
Lemma exists_nonspurious (cfg : SpuriousCfg) (i : SyscallInput) (m : Model)
    (eff0 : SyscallEffect) (m0 : Model) (evs0 : list event)
  : syscall_spec i m (Ok eff0 m0 evs0)
  -> exists (eff : SyscallEffect) (m' : Model) (evs : list event), syscall_spec i m (Ok eff m' evs)
     /\ ~ spurious_refusal_cfg cfg i m eff.
Proof.
  intros Hspec0.
  destruct (classic (exists (g : SyscallEffect) (mg : Model) (evg : list event),
    syscall_spec i m (Ok g mg evg) /\ refusal_b i m (eff_ret g) = false))
    as [(g & mg & evg & Hg & Hgrant) | Hnogrant].
  - exists g, mg, evg. split; [exact Hg|]. exact (spurious_refusal_not_refusal cfg i m g Hgrant).
  - exists eff0, m0, evs0. split; [exact Hspec0|]. intros (_ & _ & Hsome). exact (Hnogrant Hsome).
Qed.

Lemma nonspurious_of_listing : forall cfg i m (I : Type) (effs : I -> SyscallEffect),
  (forall eff m' evs, syscall_spec i m (Ok eff m' evs) -> exists j, eff = effs j) ->
  (forall j k, refusal_b i m (eff_ret (effs j)) = true -> refusal_b i m (eff_ret (effs k)) = true) ->
  forall j, ~ spurious_refusal_cfg cfg i m (effs j).
Proof.
  intros cfg i m I effs Hall Hu j (_ & Hr & eff' & m' & evs' & Hs & Hnr).
  destruct (Hall _ _ _ Hs) as [k ->]. rewrite (Hu j k Hr) in Hnr. discriminate Hnr.
Qed.
Lemma nonspurious_of_unique (cfg : SpuriousCfg) (i : SyscallInput) (m : Model) (eff0 : SyscallEffect)
  : (forall (eff : SyscallEffect) (m' : Model) (evs : list event), syscall_spec i m (Ok eff m' evs)
       -> eff = eff0)
  -> ~ spurious_refusal_cfg cfg i m eff0.
Proof.
  intros Hone (_ & Href & g & mg & evg & Hg & Hgrant).
  rewrite (Hone g mg evg Hg) in Hgrant. congruence.
Qed.
Section Steps.
Variable segs : list Segment.

Lemma sstep_of_cfg : forall cfg c e st, sstep_cfg segs cfg c e st -> sstep segs c e st.
Proof. intros cfg c e st H. exact (sstep_cfg_sub segs cfg c e st H). Qed.
Lemma star_of_cfg : forall cfg c tr c', star_cfg segs cfg c tr c' -> star segs c tr c'.
Proof. intros cfg c tr c' H. exact (star_cfg_sub segs cfg c tr c' H). Qed.
Definition cfg_transparent (c : config) : Prop :=
  forall (evs : list event) (r : step_to),
    sstep segs c evs r -> sstep_cfg segs ACFG c evs r.
Lemma transparent_instr : forall ms model,
  ms_svc_pending ms = None -> cfg_transparent (mkCfg ms model).
Proof.
  intros ms model Hsvc e st H. inversion H; subst;
    try (match goal with H1 : ms_svc_pending ms = Some _ |- _ => rewrite Hsvc in H1; discriminate H1 end).
  - eapply sstep_cfg_instr; eassumption.
  - eapply sstep_cfg_instr_fault; eassumption.
  - eapply sstep_cfg_instr_unmodeled; eassumption.
Qed.
Lemma transparent_family_on (ms : machine_state) (model : Model) (x8 : word)
  : ms_svc_pending ms = Some x8
  -> injected_family_off ACFG (sys_input segs ms x8) = false
  -> cfg_transparent (mkCfg ms model).
Proof.
  intros Hsvc Hfam evs r.
  pose proof (fun e => spurious_refusal_family_on ACFG (sys_input segs ms x8) model e Hfam) as Hok.
  remember (mkCfg ms model) as c eqn:Ec. intros Hstep. revert Ec.
  destruct Hstep as [ms0 m0 ms1 m1 Hh Hp Hst | ms0 m0 Hh Hp Hst | ms0 m0 Hh Hp Hst
    | ms0 m0 y e m1 m2 tr Hh Hp Hs Hm Hmat | ms0 m0 y e m1 tr Hh Hp Hs Hm Hmat
    | ms0 m0 y e m1 tr k Hh Hp Hs Hm Hk | ms0 m0 y e m1 tr k Hh Hp Hs Hk | ms0 m0 y Hh Hp Hs];
    intros Ec; injection Ec as -> ->; rewrite Hsvc in Hp; try discriminate Hp; injection Hp as <-.
  - exact (sstep_cfg_syscall segs ACFG ms model x8 e m1 m2 tr Hh Hsvc Hs (Hok e) Hm Hmat).
  - exact (sstep_cfg_syscall_materialization_fault segs ACFG ms model x8 e m1 tr Hh Hsvc Hs
      (Hok e) Hm Hmat).
  - exact (sstep_cfg_exit segs ACFG ms model x8 e m1 tr k Hh Hsvc Hs Hm Hk).
  - exact (sstep_cfg_killed segs ACFG ms model x8 e m1 tr k Hh Hsvc Hs Hk).
  - exact (sstep_cfg_syscall_unmodeled segs ACFG ms model x8 Hh Hsvc Hs).
Qed.

Lemma transparent_nonalloc : forall ms model x8,
  ms_svc_pending ms = Some x8 ->
  ~ In (bv_unsigned x8) alloc_mark_sysnos ->
  cfg_transparent (mkCfg ms model).
Proof.
  intros ms model x8 Hsvc Hnin. apply (transparent_family_on ms model x8 Hsvc).
  apply acfg_family_on_notin. exact Hnin.
Qed.
Lemma alloc_no_b_In (n : Z)
  : alloc_no_b n = true <-> In n alloc_mark_sysnos.
Proof.
  unfold alloc_no_b. split.
  - destruct (find (Z.eqb n) alloc_mark_sysnos) as [z|] eqn:Efind; intros Hnb; [|discriminate Hnb].
    destruct (find_some _ _ Efind) as [Hz Heqb]. apply Z.eqb_eq in Heqb. now subst z.
  - intros Hin. destruct (find (Z.eqb n) alloc_mark_sysnos) eqn:Efind; [reflexivity|].
    pose proof (find_none _ _ Efind n Hin) as Hself. rewrite Z.eqb_refl in Hself. discriminate Hself.
Qed.

Lemma transparent_nonalloc_no (ms : machine_state) (model : Model) (x8 : word) (n : Z)
  : ms_svc_pending ms = Some x8
  -> bv_unsigned x8 = n
  -> alloc_no_b n = false
  -> cfg_transparent (mkCfg ms model).
Proof. intros Hsvc <- Hnb. exact (transparent_nonalloc ms model x8 Hsvc (alloc_no_b_false _ Hnb)). Qed.

Lemma sstep_cfg_syscall_nonrefusal (cfg : SpuriousCfg) (ms : machine_state) (model : Model)
    (x8 : word) (eff : SyscallEffect) (model' model'' : Model) (evs : list event)
  : m_halted model = None
  -> ms_svc_pending ms = Some x8
  -> syscall_spec (sys_input segs ms x8) model (Ok eff model' evs)
  -> refusal_b (sys_input segs ms x8) model (eff_ret eff) = false
  -> m_halted model' = None
  -> materialize_model_accesses model' (syscall_effect_accesses eff) = Some model''
  -> sstep_cfg segs cfg (mkCfg ms model) evs
       (SNext (mkCfg (advance_past_svc (apply_effect ms eff)) model'')).
Proof.
  intros Hrun Hsvc Hspec Hgrant Hrun' Hmat.
  refine (sstep_cfg_syscall segs cfg ms model x8 eff model' model'' evs Hrun Hsvc Hspec _ Hrun' Hmat).
  exact (spurious_refusal_not_refusal cfg _ model eff Hgrant).
Qed.
End Steps.
Section Star.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Lemma star_cfg_one (c : config) (evs : list event) (c' : config)
  : sstep_cfg segs cfg c evs (SNext c') -> star_cfg segs cfg c evs c'.
Proof.
  intros Hone. rewrite <- (app_nil_r evs).
  exact (star_cfg_step segs cfg c evs c' [] c' Hone (star_cfg_refl segs cfg c')).
Qed.
Lemma star_cfg_trans (c1 : config) (tr1 : list event) (c2 : config) (tr2 : list event) (c3 : config)
  : star_cfg segs cfg c1 tr1 c2
  -> star_cfg segs cfg c2 tr2 c3
  -> star_cfg segs cfg c1 (tr1 ++ tr2) c3.
Proof.
  intros Hfirst. induction Hfirst as [x | x e y t z Hxy _ IH]; intros Hsecond; [exact Hsecond|].
  rewrite <- app_assoc. exact (star_cfg_step segs cfg x e y (t ++ tr2) c3 Hxy (IH Hsecond)).
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
Lemma star_cfg_inv (Inv : config -> Prop)
    (Hstep : forall (c : config) (evs : list event) (c' : config),
               Inv c -> sstep_cfg segs cfg c evs (SNext c') -> Inv c')
  : forall (c : config) (tr : list event) (c' : config), Inv c -> star_cfg segs cfg c tr c' -> Inv c'.
Proof.
  intros c tr c' Hc Hrun. revert Hc.
  induction Hrun as [x | x e y t z Hxy _ IH]; intros Hx; [exact Hx|].
  exact (IH (Hstep x e y Hx Hxy)).
Qed.
Lemma inv_no_reaches_error_cfg (Inv : config -> Prop)
    (Hstep : forall (c : config) (evs : list event) (c' : config),
               Inv c -> sstep_cfg segs cfg c evs (SNext c') -> Inv c')
    (Hnoerr : forall (c : config) (evs : list event), Inv c -> ~ sstep_cfg segs cfg c evs SError)
  : forall c : config, Inv c -> ~ reaches_error_cfg segs cfg c.
Proof.
  intros c Hc (tr & c' & evs & Hrun & Herr).
  exact (Hnoerr c' evs (star_cfg_inv Inv Hstep c tr c' Hc Hrun) Herr).
Qed.

End Star.