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
Lemma acfg_family_off_in (i : SyscallInput) : injected_family_off ACFG i = true ->
  List.In (bv_unsigned (in_sysno i)) alloc_mark_sysnos.
Proof.
  intros Hoff. unfold injected_family_off in Hoff.
  destruct (injected_arm (bv_unsigned (in_sysno i))) as [a|] eqn:Ha; [|discriminate Hoff].
  apply (alloc_family_dispatched _ a Ha).
  destruct (ia_family a); first [reflexivity | discriminate Hoff].
Qed.

Lemma acfg_family_on_notin (i : SyscallInput) :
  not (List.In (bv_unsigned (in_sysno i)) alloc_mark_sysnos) -> injected_family_off ACFG i = false.
Proof.
  intros Hn. apply not_true_is_false. intros Ht. exact (Hn (acfg_family_off_in i Ht)).
Qed.
Lemma acfg_nonspurious : forall (i : SyscallInput) (m : Model) (eff : SyscallEffect),
  ~ In (bv_unsigned (in_sysno i)) alloc_mark_sysnos -> ~ spurious_refusal_cfg ACFG i m eff.
Proof.
  intros i m eff Hn. exact (spurious_refusal_family_on ACFG i m eff (acfg_family_on_notin i Hn)).
Qed.
Class AllocMode := { amf : bool }.
Global Instance AcfgMode : AllocMode := {| amf := false |}.
Definition MayFail : AllocMode := {| amf := true |}.
Definition mcfg {AM : AllocMode} : SpuriousCfg := alloc_only_cfg amf.
Lemma mcfg_acfg : @mcfg AcfgMode = ACFG.
Proof. reflexivity. Qed.
Lemma mcfg_mayfail : @mcfg MayFail = may_fail_cfg.
Proof. reflexivity. Qed.
Lemma mcfg_family_off_in {AM : AllocMode} : forall i,
  injected_family_off mcfg i = true -> In (bv_unsigned (in_sysno i)) alloc_mark_sysnos.
Proof.
  destruct AM as [[|]]; [|exact acfg_family_off_in].
  intros i Hoff. unfold injected_family_off in Hoff.
  destruct (injected_arm (bv_unsigned (in_sysno i))) as [a|].
  - revert Hoff. case (ia_family a); cbn; congruence.
  - destruct (diff_false_true Hoff).
Qed.
Lemma mcfg_family_on_notin {AM : AllocMode} : forall i,
  ~ In (bv_unsigned (in_sysno i)) alloc_mark_sysnos -> injected_family_off mcfg i = false.
Proof.
  intros i Hn. apply not_true_is_false. intros Ht.
  exact (Hn (mcfg_family_off_in i Ht)).
Qed.
Lemma mcfg_nonspurious {AM : AllocMode} : forall (i : SyscallInput) (m : Model) (eff : SyscallEffect),
  ~ In (bv_unsigned (in_sysno i)) alloc_mark_sysnos -> ~ spurious_refusal_cfg (@mcfg AM) i m eff.
Proof.
  intros i m eff Hn.
  exact (spurious_refusal_family_on (@mcfg AM) i m eff (@mcfg_family_on_notin AM i Hn)).
Qed.
Lemma mayfail_family_off : forall i : SyscallInput, injected_family_off (@mcfg MayFail) i = false.
Proof.
  change (@mcfg MayFail) with may_fail_cfg. exact injected_family_off_may_fail.
Qed.
Definition alloc_no_b (n : Z) : bool :=
  match List.find (Z.eqb n) alloc_mark_sysnos with Some _ => true | None => false end.
Lemma alloc_no_b_false : forall n : Z, alloc_no_b n = false -> ~ In n alloc_mark_sysnos.
Proof.
  intros n Hb Hin. unfold alloc_no_b in Hb.
  destruct (List.find (Z.eqb n) alloc_mark_sysnos) eqn:Hf; [discriminate Hb|].
  pose proof (List.find_none _ _ Hf n Hin) as Hn. rewrite Z.eqb_refl in Hn. discriminate Hn.
Qed.
Lemma acfg_nonspurious_no (segs : list Segment) (ms : RiscvSemantics.machine_state) (x8 : word)
    (n : Z) (m : Model) (eff : SyscallEffect) : bv_unsigned x8 = n ->
  alloc_no_b n = false -> not (spurious_refusal_cfg ACFG (sys_input segs ms x8) m eff).
Proof.
  intros Hx Hb. subst n. apply acfg_nonspurious. exact (alloc_no_b_false _ Hb).
Qed.
Lemma acfg_family_off_of_in (i : SyscallInput) :
  List.In (bv_unsigned (in_sysno i)) alloc_mark_sysnos -> injected_family_off ACFG i = true.
Proof.
  intros Hin. cbn [alloc_mark_sysnos In] in Hin. unfold injected_family_off.
  destruct Hin as [E | [E | [E | [E | []]]]]; rewrite <- E; exact eq_refl.
Qed.

Lemma acfg_family_off_222 : forall i : SyscallInput,
  bv_unsigned (in_sysno i) = 222%Z -> injected_family_off ACFG i = true.
Proof. intros i Hno. unfold injected_family_off; rewrite Hno; exact eq_refl. Qed.
Lemma acfg_family_off_226 : forall i : SyscallInput,
  bv_unsigned (in_sysno i) = 226%Z -> injected_family_off ACFG i = true.
Proof. intros i Hno. unfold injected_family_off; rewrite Hno; exact eq_refl. Qed.
Lemma acfg_family_off_216 : forall i : SyscallInput,
  bv_unsigned (in_sysno i) = 216%Z -> injected_family_off ACFG i = true.
Proof. intros i Hno. unfold injected_family_off; rewrite Hno; exact eq_refl. Qed.
Lemma acfg_family_off_214 : forall i : SyscallInput,
  bv_unsigned (in_sysno i) = 214%Z -> injected_family_off ACFG i = true.
Proof. intros i Hno. unfold injected_family_off; rewrite Hno; exact eq_refl. Qed.

Lemma refusal_b_222 : forall (i : SyscallInput) (m : Model) (r : word),
  bv_unsigned (in_sysno i) = 222%Z -> refusal_b i m r = ret_in_errnos mmap_errnos r.
Proof. intros i m r H. unfold refusal_b. rewrite H. reflexivity. Qed.
Lemma refusal_b_226 : forall (i : SyscallInput) (m : Model) (r : word),
  bv_unsigned (in_sysno i) = 226%Z -> refusal_b i m r = ret_in_errnos mprotect_errnos r.
Proof. intros i m r H. unfold refusal_b. rewrite H. reflexivity. Qed.
Lemma refusal_b_216 : forall (i : SyscallInput) (m : Model) (r : word),
  bv_unsigned (in_sysno i) = 216%Z -> refusal_b i m r = ret_in_errnos mremap_errnos r.
Proof. intros i m r H. unfold refusal_b. rewrite H. reflexivity. Qed.
Lemma refusal_b_214 : forall (i : SyscallInput) (m : Model) (r : word),
  bv_unsigned (in_sysno i) = 214%Z -> refusal_b i m r = brk_refusal_b m (in_arg i 0) r.
Proof. intros i m r H. unfold refusal_b. rewrite H. reflexivity. Qed.
Lemma ret_in_errnos_ENOMEM (r : word) : ret_in_errnos (cons ENOMEM nil) r = bv_eqb r (errno_ret ENOMEM).
Proof.
  unfold ret_in_errnos; cbn [existsb]. exact (orb_false_r (bv_eqb r (errno_ret ENOMEM))).
Qed.
Lemma ret_in_errnos_errno : forall es e, In e es -> ret_in_errnos es (errno_ret e) = true.
Proof.
  intros es e Hin. unfold ret_in_errnos. apply existsb_exists. exists e. split; [exact Hin|].
  apply bv_eqb_eq. reflexivity.
Qed.

Lemma refusal_spurious_of_grant (cfg : SpuriousCfg) (i : SyscallInput) (m : Model)
    (eff eff' : SyscallEffect) (m' : Model) (evs' : list event) : injected_family_off cfg i = true ->
  refusal_b i m (eff_ret eff) = true -> syscall_spec i m (Ok eff' m' evs') ->
  refusal_b i m (eff_ret eff') = false -> spurious_refusal_cfg cfg i m eff.
Proof.
  intros Hfam Href Hspec Hgrant. unfold spurious_refusal_cfg.
  refine (conj Hfam (conj Href _)). exists eff', m', evs'. exact (conj Hspec Hgrant).
Qed.
Lemma nonspurious_not_refusal_of_grant (cfg : SpuriousCfg) (i : SyscallInput) (m : Model)
    (eff eff' : SyscallEffect) (m' : Model) (evs' : list event) : injected_family_off cfg i = true ->
  not (spurious_refusal_cfg cfg i m eff) -> syscall_spec i m (Ok eff' m' evs') ->
  refusal_b i m (eff_ret eff') = false -> refusal_b i m (eff_ret eff) = false.
Proof.
  intros Hfam Hns Hspec Hgrant. apply not_true_is_false. intros Href.
  exact (Hns (refusal_spurious_of_grant cfg i m eff eff' m' evs' Hfam Href Hspec Hgrant)).
Qed.
Lemma nonspurious_refusal_no_grant : forall (cfg : SpuriousCfg) (i : SyscallInput) (m : Model)
    (eff : SyscallEffect),
  ~ spurious_refusal_cfg cfg i m eff -> injected_family_off cfg i = true ->
  refusal_b i m (eff_ret eff) = true ->
  forall (eff' : SyscallEffect) (m' : Model) (evs' : list event),
  syscall_spec i m (Ok eff' m' evs') -> refusal_b i m (eff_ret eff') = true.
Proof.
  intros cfg i m eff Hns Hoff Hr eff' m' evs' Hs. apply not_false_is_true. intros Hnr.
  exact (Hns (refusal_spurious_of_grant cfg i m eff eff' m' evs' Hoff Hr Hs Hnr)).
Qed.

Lemma not_spurious_forced : forall cfg i m eff,
  (forall eff' m' evs', syscall_spec i m (Ok eff' m' evs') -> refusal_b i m (eff_ret eff') = true) ->
  ~ spurious_refusal_cfg cfg i m eff.
Proof.
  intros cfg i m eff Hall (_ & _ & eff' & m' & evs' & Hspec & Hnr).
  rewrite (Hall eff' m' evs' Hspec) in Hnr. discriminate Hnr.
Qed.
Lemma refusal_b_input_eq : forall (i1 i2 : SyscallInput) (m : Model) (r : word),
  in_sysno i1 = in_sysno i2 -> in_arg i1 0 = in_arg i2 0 -> refusal_b i1 m r = refusal_b i2 m r.
Proof. intros i1 i2 m r Hn Ha. unfold refusal_b. rewrite Hn, Ha. reflexivity. Qed.

Lemma spurious_refusal_input_dir : forall (cfg : SpuriousCfg) (i1 i2 : SyscallInput) (m : Model)
    (eff : SyscallEffect),
  in_sysno i1 = in_sysno i2 -> in_arg i1 0 = in_arg i2 0 ->
  (forall (e : SyscallEffect) (m' : Model) (evs' : list event),
     syscall_spec i1 m (Ok e m' evs') -> syscall_spec i2 m (Ok e m' evs')) ->
  spurious_refusal_cfg cfg i1 m eff -> spurious_refusal_cfg cfg i2 m eff.
Proof.
  intros cfg i1 i2 m eff Hn Ha Hs (Hoff & Hr & eff' & m' & evs' & Hspec & Hnr).
  rewrite (refusal_b_input_eq i1 i2 m _ Hn Ha) in Hr.
  rewrite (refusal_b_input_eq i1 i2 m _ Hn Ha) in Hnr.
  split; [unfold injected_family_off in *; rewrite <- Hn; exact Hoff|].
  split; [exact Hr|]. exists eff', m', evs'. split; [exact (Hs _ _ _ Hspec) | exact Hnr].
Qed.

Lemma spurious_refusal_transport : forall (cfg : SpuriousCfg) (i1 i2 : SyscallInput) (m : Model)
    (eff : SyscallEffect),
  in_sysno i1 = in_sysno i2 -> in_arg i1 0 = in_arg i2 0 ->
  (forall (eff' : SyscallEffect) (m' : Model) (evs' : list event),
     syscall_spec i1 m (Ok eff' m' evs') <-> syscall_spec i2 m (Ok eff' m' evs')) ->
  iff (spurious_refusal_cfg cfg i1 m eff) (spurious_refusal_cfg cfg i2 m eff).
Proof.
  intros cfg i1 i2 m eff Hn Ha Hs. split.
  - exact (spurious_refusal_input_dir cfg i1 i2 m eff Hn Ha
             (fun e m' evs' => proj1 (Hs e m' evs'))).
  - exact (spurious_refusal_input_dir cfg i2 i1 m eff (eq_sym Hn) (eq_sym Ha)
             (fun e m' evs' => proj2 (Hs e m' evs'))).
Qed.
Lemma exists_nonspurious (cfg : SpuriousCfg) (i : SyscallInput) (m : Model)
    (eff0 : SyscallEffect) (m0 : Model) (evs0 : list event) : syscall_spec i m (Ok eff0 m0 evs0) ->
  exists (eff : SyscallEffect) (m' : Model) (evs : list event),
    syscall_spec i m (Ok eff m' evs) /\ not (spurious_refusal_cfg cfg i m eff).
Proof.
  intros Hs.
  destruct (classic (spurious_refusal_cfg cfg i m eff0))
    as [(_ & _ & eff' & m' & evs' & Hs' & Hnr) | Hns].
  - exists eff', m', evs'. split; [exact Hs' | exact (spurious_refusal_not_refusal cfg i m eff' Hnr)].
  - exists eff0, m0, evs0. split; [exact Hs | exact Hns].
Qed.

Lemma nonspurious_of_listing : forall cfg i m (I : Type) (effs : I -> SyscallEffect),
  (forall eff m' evs, syscall_spec i m (Ok eff m' evs) -> exists j, eff = effs j) ->
  (forall j k, refusal_b i m (eff_ret (effs j)) = true -> refusal_b i m (eff_ret (effs k)) = true) ->
  forall j, ~ spurious_refusal_cfg cfg i m (effs j).
Proof.
  intros cfg i m I effs Hall Hu j (_ & Hr & eff' & m' & evs' & Hs & Hnr).
  destruct (Hall _ _ _ Hs) as [k ->]. rewrite (Hu j k Hr) in Hnr. discriminate Hnr.
Qed.
Lemma nonspurious_of_unique : forall (cfg : SpuriousCfg) (i : SyscallInput) (m : Model)
    (eff0 : SyscallEffect),
  (forall (eff : SyscallEffect) (m' : Model) (evs : list event),
     syscall_spec i m (Ok eff m' evs) -> eff = eff0) ->
  not (spurious_refusal_cfg cfg i m eff0).
Proof.
  intros cfg i m eff0 Hu (_ & Hr & eff' & m' & evs' & Hs & Hnr).
  specialize (Hu _ _ _ Hs). subst eff'. congruence.
Qed.
Section Steps.
Variable segs : list Segment.
Context {AM : AllocMode}.

Lemma sstep_of_cfg : forall cfg c e st, sstep_cfg segs cfg c e st -> sstep segs c e st.
Proof. intros cfg c e st H. exact (sstep_cfg_sub segs cfg c e st H). Qed.
Lemma star_of_cfg : forall cfg c tr c', star_cfg segs cfg c tr c' -> star segs c tr c'.
Proof. intros cfg c tr c' H. exact (star_cfg_sub segs cfg c tr c' H). Qed.
Definition cfg_transparent (c : config) : Prop :=
  forall (evs : list event) (r : step_to),
    sstep segs c evs r -> sstep_cfg segs mcfg c evs r.
Lemma transparent_instr : forall ms model,
  ms_svc_pending ms = None -> cfg_transparent (mkCfg ms model).
Proof.
  intros ms model Hsvc e st H. inversion H; subst;
    try (match goal with H1 : ms_svc_pending ms = Some _ |- _ => rewrite Hsvc in H1; discriminate H1 end).
  - eapply sstep_cfg_instr; eassumption.
  - eapply sstep_cfg_instr_fault; eassumption.
  - eapply sstep_cfg_instr_unmodeled; eassumption.
Qed.
Lemma transparent_family_on : forall ms model x8,
  ms_svc_pending ms = Some x8 ->
  injected_family_off mcfg (sys_input segs ms x8) = false ->
  cfg_transparent (mkCfg ms model).
Proof.
  intros ms model x8 Hsvc Hoff e st H. inversion H; subst;
    try (match goal with H1 : ms_svc_pending ms = None |- _ => rewrite Hsvc in H1; discriminate H1 end);
    match goal with H1 : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H1; injection H1; intro; subst y end.
  - eapply sstep_cfg_syscall; try eassumption. apply spurious_refusal_family_on. exact Hoff.
  - eapply sstep_cfg_syscall_materialization_fault; try eassumption.
    apply spurious_refusal_family_on. exact Hoff.
  - eapply sstep_cfg_exit; eassumption.
  - eapply sstep_cfg_killed; eassumption.
  - eapply sstep_cfg_syscall_unmodeled; eassumption.
Qed.

Lemma transparent_nonalloc : forall ms model x8,
  ms_svc_pending ms = Some x8 ->
  ~ In (bv_unsigned x8) alloc_mark_sysnos ->
  cfg_transparent (mkCfg ms model).
Proof.
  intros ms model x8 Hsvc Hnin. apply (transparent_family_on ms model x8 Hsvc).
  apply mcfg_family_on_notin. exact Hnin.
Qed.
Lemma alloc_no_b_In (n : Z) : alloc_no_b n = true <-> List.In n alloc_mark_sysnos.
Proof.
  split; intros H.
  - unfold alloc_no_b in H.
    destruct (List.find (Z.eqb n) alloc_mark_sysnos) as [z|] eqn:Hf; [|discriminate H].
    destruct (List.find_some _ _ Hf) as [Hin Hz]. apply Z.eqb_eq in Hz. subst z. exact Hin.
  - destruct (alloc_no_b n) eqn:Hb; [reflexivity|].
    destruct (alloc_no_b_false n Hb H).
Qed.

Lemma transparent_nonalloc_no : forall ms (model : Model) (x8 : word) (n : Z),
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = n -> alloc_no_b n = false ->
  cfg_transparent (mkCfg ms model).
Proof.
  intros ms model x8 n Hsvc Hx Hb. subst n.
  exact (transparent_nonalloc ms model x8 Hsvc (alloc_no_b_false _ Hb)).
Qed.

Lemma sstep_cfg_syscall_nonrefusal : forall (cfg : SpuriousCfg) ms (model : Model) (x8 : word)
    (eff : SyscallEffect) (model' model'' : Model) (evs : list event),
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
  refusal_b (sys_input segs ms x8) model (eff_ret eff) = false ->
  m_halted model' = None ->
  materialize_model_accesses model' (syscall_effect_accesses eff) = Some model'' ->
  sstep_cfg segs cfg (mkCfg ms model) evs
    (SNext (mkCfg (advance_past_svc (apply_effect ms eff)) model'')).
Proof.
  intros cfg ms model x8 eff model' model'' evs Hh Hsvc Hs Hnr Hh' Hm.
  exact (sstep_cfg_syscall segs cfg ms model x8 eff model' model'' evs Hh Hsvc Hs
           (spurious_refusal_not_refusal cfg _ model eff Hnr) Hh' Hm).
Qed.
End Steps.
Lemma transparent_mayfail : forall segs c, @cfg_transparent segs MayFail c.
Proof.
  intros segs [ms model]. destruct (ms_svc_pending ms) as [x8|] eqn:E.
  - exact (@transparent_family_on segs MayFail ms model x8 E (mayfail_family_off _)).
  - exact (@transparent_instr segs MayFail ms model E).
Qed.
Section Star.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Lemma star_cfg_one : forall (c : config) (evs : list event) (c' : config),
  sstep_cfg segs cfg c evs (SNext c') -> star_cfg segs cfg c evs c'.
Proof.
  intros c evs c' H. rewrite <- (app_nil_r evs).
  exact (star_cfg_step segs cfg c evs c' [] c' H (star_cfg_refl segs cfg c')).
Qed.
Lemma star_cfg_trans : forall (c1 : config) (tr1 : list event) (c2 : config)
    (tr2 : list event) (c3 : config),
  star_cfg segs cfg c1 tr1 c2 ->
  star_cfg segs cfg c2 tr2 c3 -> star_cfg segs cfg c1 (app tr1 tr2) c3.
Proof.
  intros c1 tr1 c2 tr2 c3 H1. induction H1 as [c | ca evs cb tr cc Hs _ IH]; intros H2; [exact H2|].
  rewrite <- app_assoc. exact (star_cfg_step segs cfg ca evs cb (tr ++ tr2) c3 Hs (IH H2)).
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
Lemma star_cfg_inv : forall (Inv : config -> Prop)
    (Hstep : forall (c : config) (evs : list event) (c' : config),
       Inv c -> sstep_cfg segs cfg c evs (SNext c') -> Inv c')
    (c : config) (tr : list event) (c' : config),
  Inv c -> star_cfg segs cfg c tr c' -> Inv c'.
Proof.
  intros Inv Hstep c tr c' Hc H. revert Hc.
  induction H as [c0 | ca evs cb tr cc Hs _ IH]; intros Hc; [exact Hc|].
  exact (IH (Hstep ca evs cb Hc Hs)).
Qed.
Lemma inv_no_reaches_error_cfg (Inv : config -> Prop)
    (Hstep : forall (c : config) (evs : list event) (c' : config),
       Inv c -> sstep_cfg segs cfg c evs (SNext c') -> Inv c')
    (Hnoerr : forall (c : config) (evs : list event), Inv c -> ~ sstep_cfg segs cfg c evs SError)
    (c : config) : Inv c -> ~ reaches_error_cfg segs cfg c.
Proof.
  intros Hc (tr & c2 & evs & Hst & He).
  exact (Hnoerr c2 evs (star_cfg_inv Inv Hstep c tr c2 Hc Hst) He).
Qed.

End Star.