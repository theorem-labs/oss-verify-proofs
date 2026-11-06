(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Classical_Prop.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK15.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.

(* [comment removed for export] *)
Definition ev_ok (S : list word) (e : event) : Prop :=
  match e with
  | ExitEv k _ => In k S
  | KillEv _ _ => False
  | _ => True
  end.
Definition trace_ok (S : list word) (tr : list event) : Prop := Forall (ev_ok S) tr.
Definition shape_ok (S : list word) (T : TSet) : Prop := forall tr, T tr -> trace_ok S tr.

Lemma trace_ok_app : forall S a b, trace_ok S (a ++ b) <-> trace_ok S a /\ trace_ok S b.
Proof. intros S a b. unfold trace_ok. apply Forall_app. Qed.
Lemma trace_ok_prefix : forall S tr tr', is_prefix tr tr' -> trace_ok S tr' -> trace_ok S tr.
Proof.
  intros S tr; induction tr as [|e tr IH]; intros tr' Hp Hok.
  - constructor.
  - destruct tr' as [|e' tr']; cbn in Hp; [destruct Hp|]. destruct Hp as [<- Hp].
    inversion Hok; subst. constructor; [assumption|]. eapply IH; eauto.
Qed.
Lemma shape_ok_eq : forall S T T', t_eq T T' -> shape_ok S T' -> shape_ok S T.
Proof. intros S T T' Heq H tr Htr. apply H. apply Heq. exact Htr. Qed.
Lemma shape_ok_eq' : forall S T T', t_eq T T' -> shape_ok S T -> shape_ok S T'.
Proof. intros S T T' Heq H tr Htr. apply H. apply Heq. exact Htr. Qed.
Lemma shape_ok_nil : forall S, shape_ok S t_nil.
Proof. intros S tr Htr. unfold t_nil in Htr. subst tr. constructor. Qed.
Lemma shape_ok_emit : forall S evs T, trace_ok S evs -> shape_ok S T -> shape_ok S (t_emit evs T).
Proof.
  intros S evs T Hevs HT tr [Hp | (tr' & -> & Htr')].
  - eapply trace_ok_prefix; eauto.
  - apply trace_ok_app. split; [exact Hevs | apply HT; exact Htr'].
Qed.
Lemma shape_ok_emit_inv : forall S evs T, T [] -> shape_ok S (t_emit evs T) -> trace_ok S evs /\ shape_ok S T.
Proof.
  intros S evs T H0 H. split.
  - apply (H evs). right. exists []. rewrite app_nil_r. split; [reflexivity | exact H0].
  - intros tr Htr. assert (Hc : trace_ok S (evs ++ tr)).
    { apply H. right. exists tr. split; [reflexivity | exact Htr]. }
    apply trace_ok_app in Hc. tauto.
Qed.
Lemma shape_ok_alt : forall S (I : Type) (f : I -> TSet), (forall i, shape_ok S (f i)) -> shape_ok S (t_alt f).
Proof. intros S I f H tr [i Hi]. exact (H i tr Hi). Qed.
Lemma shape_ok_alt_inv : forall S (I : Type) (f : I -> TSet) i, shape_ok S (t_alt f) -> shape_ok S (f i).
Proof. intros S I f i H tr Htr. apply H. exists i. exact Htr. Qed.
Lemma shape_ok_alt2 : forall S A B, shape_ok S A -> shape_ok S B -> shape_ok S (t_alt2 A B).
Proof. intros S A B HA HB tr [H|H]; [apply HA | apply HB]; exact H. Qed.
Lemma shape_ok_exit : forall S code fs, In code S -> shape_ok S (t_exit code fs).
Proof.
  intros S code fs Hin. unfold t_exit. apply shape_ok_emit; [|apply shape_ok_nil].
  constructor; [exact Hin | constructor].
Qed.

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
Definition fo_exits (c : config) (T : TSet) : Prop :=
  forall S : list word, shape_ok S T -> m_halted (cfg_model c) = None ->
    must_exit_in_at_cfg forced_only_cfg segs S c.

(* [comment removed for export] *)
Definition fo_dead (c c' : config) : Prop :=
  forall e, ~ sstep_cfg segs forced_only_cfg c e (SNext c').

Lemma fo_conseq : forall c T T', fo_exits c T -> t_eq T T' -> fo_exits c T'.
Proof. intros c T T' H E S HS Hh. exact (H S (shape_ok_eq S T T' E HS) Hh). Qed.

Lemma fo_halted : forall c T, m_halted (cfg_model c) <> None -> fo_exits c T.
Proof. intros c T Hh S _ Hn. exfalso. exact (Hh Hn). Qed.

(* [comment removed for export] *)
Lemma fo_progress : forall c (I : Type) (evs : I -> list event) (nx : I -> config) (i0 : I),
  node_ok segs c I evs nx ->
  exists e st, sstep_cfg segs forced_only_cfg c e st.
Proof.
  intros c I evs nx i0 [Hcomp Hsound].
  pose proof (Hcomp i0) as Hss.
  assert (NOERR : forall e, ~ sstep segs c e SError).
  { intros e He. destruct (Hsound e SError He) as (i & _ & Hbad). discriminate Hbad. }
  remember (evs i0) as e0. remember (SNext (nx i0)) as st0. clear Heqe0 Heqst0.
  destruct Hss.
  - eexists _, _. eapply sstep_cfg_instr; eassumption.
  - eexists _, _. eapply sstep_cfg_instr_fault; eassumption.
  - eexists _, _. eapply sstep_cfg_instr_unmodeled; eassumption.
  - destruct (classic (spurious_refusal_cfg forced_only_cfg (sys_input segs ms x8) model eff)) as [Hsp | Hns].
    + destruct Hsp as (_ & _ & eff' & m' & evs' & Hspec' & Hnr').
      assert (Hns' : ~ spurious_refusal_cfg forced_only_cfg (sys_input segs ms x8) model eff').
      { apply spurious_refusal_not_refusal. exact Hnr'. }
      destruct (m_halted m') as [code|] eqn:Hh'.
      * destruct (m_killed m') as [sig|] eqn:Hk'.
        -- eexists _, _. eapply sstep_cfg_killed; eassumption.
        -- eexists _, _. eapply sstep_cfg_exit; eassumption.
      * destruct (materialize_model_accesses m' (syscall_effect_accesses eff')) as [m''|] eqn:Hmat.
        -- eexists _, _. eapply sstep_cfg_syscall; eassumption.
        -- exfalso. apply (NOERR []). eapply sstep_syscall_materialization_fault; eassumption.
    + eexists _, _. eapply sstep_cfg_syscall; eassumption.
  - exfalso. eapply NOERR. eapply sstep_syscall_materialization_fault; eassumption.
  - eexists _, _. eapply sstep_cfg_exit; eassumption.
  - eexists _, _. eapply sstep_cfg_killed; eassumption.
  - exfalso. eapply NOERR. eapply sstep_syscall_unmodeled; eassumption.
Qed.

(* [comment removed for export] *)
Lemma fo_node : forall c (I : Type) (evs : I -> list event) (nx : I -> config) (T : I -> TSet) (i0 : I)
    (dead : I -> Prop),
  node_ok segs c I evs nx ->
  (forall i, dead i -> fo_dead c (nx i)) ->
  (forall i, ~ dead i -> fo_exits (nx i) (T i)) ->
  (forall i, ~ dead i -> T i []) ->
  fo_exits c (t_alt (fun i => t_emit (evs i) (T i))).
Proof.
  intros c I evs nx T i0 dead Hnode Hdead Hlive Hne S HS Hrun.
  destruct Hnode as [Hcomp Hsound].
  apply must_exit_in_at_cfg_running.
  - exact Hrun.
  - exact (fo_progress c I evs nx i0 (conj Hcomp Hsound)).
  - intros e Hss. apply sstep_cfg_sub in Hss. destruct (Hsound e SError Hss) as (i & _ & Hbad). discriminate Hbad.
  - intros e c' Hss.
    pose proof (sstep_cfg_sub _ _ _ _ _ Hss) as Hss'.
    destruct (Hsound e (SNext c') Hss') as (i & -> & Heq). injection Heq as Heq. subst c'.
    destruct (classic (dead i)) as [Hd | Hl].
    + exfalso. exact (Hdead i Hd _ Hss).
    + pose proof (shape_ok_alt_inv S I _ i HS) as HSi.
      destruct (shape_ok_emit_inv S (evs i) (T i) (Hne i Hl) HSi) as [Hevs HTi].
      destruct (sstep_next_halts_by_exit segs c (evs i) (nx i) Hss')
        as [Hn | [(evs0 & code & Hevs' & Hh & Hk) | (evs0 & sig & Hevs' & Hk)]].
      * exact (Hlive i Hl S HTi Hn).
      * apply (must_exit_in_at_cfg_halted forced_only_cfg segs S (nx i) code Hh); [|exact Hk].
        rewrite Hevs' in Hevs. apply trace_ok_app in Hevs as [_ Hev]. inversion Hev; subst. exact H1.
      * exfalso. rewrite Hevs' in Hevs. apply trace_ok_app in Hevs as [_ Hev]. inversion Hev; subst. exact H1.
Qed.

(* [comment removed for export] *)
Lemma fo_node_all : forall c (I : Type) (evs : I -> list event) (nx : I -> config) (T : I -> TSet) (i0 : I),
  node_ok segs c I evs nx ->
  (forall i, fo_exits (nx i) (T i)) ->
  (forall i, T i []) ->
  fo_exits c (t_alt (fun i => t_emit (evs i) (T i))).
Proof.
  intros c I evs nx T i0 Hnode Hlive Hne.
  apply (fo_node c I evs nx T i0 (fun _ => False) Hnode).
  - intros i f. destruct f.
  - intros i _. apply Hlive.
  - intros i _. apply Hne.
Qed.

(* [comment removed for export] *)
Lemma fo_of_realizes : forall c T, realizes segs c T -> fo_exits c T.
Proof.
  intros c T H; induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq].
  - apply (fo_node_all c I evs nx T i0 Hnode IH).
    intros i. eapply realizes_nonempty. exact (Hcont i).
  - apply fo_halted. exact Hh.
  - eapply fo_conseq; [exact IH | exact Heq].
Qed.

(* [comment removed for export] *)
Lemma fo_exits_must_exit : forall S c T,
  fo_exits c T -> shape_ok S T -> m_halted (cfg_model c) = None ->
  must_exit_in_at_cfg forced_only_cfg segs S c.
Proof. intros S c T H HS Hh. exact (H S HS Hh). Qed.

(* [comment removed for export] *)
Lemma injected_family_off_forced_only : forall i a,
  injected_arm (bv_unsigned (in_sysno i)) = Some a ->
  injected_family_off forced_only_cfg i = true.
Proof.
  intros i a Ha. unfold injected_family_off. rewrite Ha. destruct (ia_family a); reflexivity.
Qed.

Lemma fo_dead_refusal : forall ms model x8 c',
  ms_svc_pending ms = Some x8 ->
  injected_family_off forced_only_cfg (sys_input segs ms x8) = true ->
  (exists eff' m' evs', syscall_spec (sys_input segs ms x8) model (Ok eff' m' evs')
                       /\ refusal_b (sys_input segs ms x8) model (eff_ret eff') = false) ->
  ms_svc_pending (cfg_ms c') = None ->
  (forall eff model'', cfg_ms c' = advance_past_svc (apply_effect ms eff) ->
                       cfg_model c' = model'' ->
                       refusal_b (sys_input segs ms x8) model (eff_ret eff) = true) ->
  fo_dead (mkCfg ms model) c'.
Proof.
  intros ms model x8 c' Hsvc Hoff Hex Hsvc' Href e Hstep.
  inversion Hstep; subst.
  - (* [comment removed for export] *) congruence.
  - (* [comment removed for export] *)
    match goal with
    | [ H : ~ spurious_refusal_cfg _ _ _ ?eff, H8 : ms_svc_pending ms = Some ?y |- _ ] =>
        apply H; assert (y = x8) by congruence; subst y
    end.
    split; [exact Hoff | split; [| exact Hex]].
    eapply Href; reflexivity.
  - (* [comment removed for export] *) cbn in Hsvc'. congruence.
  - (* [comment removed for export] *) cbn in Hsvc'. congruence.
Qed.

(* [comment removed for export] *)
Lemma apply_effect_a0 : forall ms eff,
  reg_get (ms_regs (advance_past_svc (apply_effect ms eff))) (Z_to_bv 5 10) = eff_ret eff.
Proof.
  intros ms eff. cbn [advance_past_svc apply_effect ms_regs]. unfold set_reg.
  destruct (bv_eqb _ _) eqn:E.
  - apply bv_eqb_eq in E. exfalso. apply (f_equal bv_unsigned) in E. vm_compute in E. discriminate E.
  - cbn [ms_regs]. unfold reg_get.
    replace (Z_to_bv 5 10) with (10%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite bvmap_get_set_same. reflexivity.
Qed.

Lemma in_sysno_sys_input : forall ms x8, in_sysno (sys_input segs ms x8) = x8.
Proof. intros. reflexivity. Qed.

Lemma injected_family_off_mmap : forall ms x8,
  bv_unsigned x8 = 222%Z -> injected_family_off forced_only_cfg (sys_input segs ms x8) = true.
Proof. intros ms x8 H. unfold injected_family_off. rewrite in_sysno_sys_input, H. reflexivity. Qed.
Lemma injected_family_off_mprotect : forall ms x8,
  bv_unsigned x8 = 226%Z -> injected_family_off forced_only_cfg (sys_input segs ms x8) = true.
Proof. intros ms x8 H. unfold injected_family_off. rewrite in_sysno_sys_input, H. reflexivity. Qed.
Lemma injected_family_off_brk : forall ms x8,
  bv_unsigned x8 = 214%Z -> injected_family_off forced_only_cfg (sys_input segs ms x8) = true.
Proof. intros ms x8 H. unfold injected_family_off. rewrite in_sysno_sys_input, H. reflexivity. Qed.

Lemma refusal_b_mmap : forall ms x8 model r,
  bv_unsigned x8 = 222%Z ->
  refusal_b (sys_input segs ms x8) model r = ret_in_errnos mmap_errnos r.
Proof. intros ms x8 model r H. unfold refusal_b. rewrite in_sysno_sys_input, H. reflexivity. Qed.
Lemma refusal_b_mprotect : forall ms x8 model r,
  bv_unsigned x8 = 226%Z ->
  refusal_b (sys_input segs ms x8) model r = ret_in_errnos mprotect_errnos r.
Proof. intros ms x8 model r H. unfold refusal_b. rewrite in_sysno_sys_input, H. reflexivity. Qed.

Lemma ret_in_errnos_errno : forall es e, In e es -> ret_in_errnos es (errno_ret e) = true.
Proof.
  intros es e Hin. unfold ret_in_errnos. apply existsb_exists. exists e. split; [exact Hin|].
  apply bv_eqb_eq. reflexivity.
Qed.
Lemma ret_in_errnos_false : forall es r,
  (forall e, In e es -> r <> errno_ret e) -> ret_in_errnos es r = false.
Proof.
  intros es r H. unfold ret_in_errnos.
  destruct (existsb (fun e => bv_eqb r (errno_ret e)) es) eqn:E; [|reflexivity].
  apply existsb_exists in E. destruct E as (e & Hin & Heq). apply bv_eqb_eq in Heq.
  exfalso. exact (H e Hin Heq).
Qed.
Lemma small_not_errno : forall (r : word) (e : Z),
  (0 < e <= 4095)%Z -> (bv_unsigned r < 2^64 - 4095)%Z -> r <> errno_ret e.
Proof.
  intros r e He Hr ->. unfold errno_ret in Hr. rewrite Z_to_bv_unsigned in Hr.
  unfold bv_wrap, bv_modulus in Hr. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in Hr.
  assert (E : ((- e) mod 2^64 = 2^64 - e)%Z).
  { rewrite <- (Z.mod_unique (-e) (2^64) (-1) (2^64 - e)); lia. }
  rewrite E in Hr. lia.
Qed.

(* [comment removed for export] *)
Lemma mmap_enomem_refusal : forall ms x8 model,
  bv_unsigned x8 = 222%Z -> refusal_b (sys_input segs ms x8) model (errno_ret ENOMEM) = true.
Proof. intros ms x8 model H. rewrite (refusal_b_mmap ms x8 model _ H). apply ret_in_errnos_errno. left. reflexivity. Qed.
Lemma mmap_grant_not_refusal : forall ms x8 model (a : word),
  bv_unsigned x8 = 222%Z -> (bv_unsigned a < 2^64 - 4095)%Z -> refusal_b (sys_input segs ms x8) model a = false.
Proof.
  intros ms x8 model a H Ha. rewrite (refusal_b_mmap ms x8 model _ H). apply ret_in_errnos_false.
  intros e Hin. cbn in Hin. destruct Hin as [<-|[]]. apply small_not_errno; [unfold ENOMEM; lia | exact Ha].
Qed.

(* [comment removed for export] *)
Lemma fo_dead_refusal_sib : forall ms model x8 ej cj c',
  ms_svc_pending ms = Some x8 ->
  injected_family_off forced_only_cfg (sys_input segs ms x8) = true ->
  sstep segs (mkCfg ms model) ej (SNext cj) ->
  ms_svc_pending (cfg_ms cj) = None ->
  refusal_b (sys_input segs ms x8) model (reg_get (ms_regs (cfg_ms cj)) (Z_to_bv 5 10)) = false ->
  ms_svc_pending (cfg_ms c') = None ->
  refusal_b (sys_input segs ms x8) model (reg_get (ms_regs (cfg_ms c')) (Z_to_bv 5 10)) = true ->
  fo_dead (mkCfg ms model) c'.
Proof.
  intros ms model x8 ej cj c' Hsvc Hoff Hsib Hsvcj Hnr Hsvc' Hr.
  apply (fo_dead_refusal ms model x8 c' Hsvc Hoff).
  - inversion Hsib; subst; cbn [cfg_ms] in *; try congruence.
    match goal with
    | [ H : syscall_spec (sys_input segs ms ?y) model (Ok ?eff ?m' ?evs) |- _ ] =>
        assert (y = x8) by congruence; subst y; exists eff, m', evs; split; [exact H|]
    end.
    rewrite apply_effect_a0 in Hnr. exact Hnr.
  - exact Hsvc'.
  - intros eff model'' Hms _. rewrite Hms, apply_effect_a0 in Hr. exact Hr.
Qed.

(* [comment removed for export] *)
Lemma fo_dead_node : forall ms model x8 (I : Type) (evs : I -> list event) (nx : I -> config) (j i : I),
  node_ok segs (mkCfg ms model) I evs nx ->
  ms_svc_pending ms = Some x8 ->
  injected_family_off forced_only_cfg (sys_input segs ms x8) = true ->
  ms_svc_pending (cfg_ms (nx j)) = None ->
  refusal_b (sys_input segs ms x8) model (reg_get (ms_regs (cfg_ms (nx j))) (Z_to_bv 5 10)) = false ->
  ms_svc_pending (cfg_ms (nx i)) = None ->
  refusal_b (sys_input segs ms x8) model (reg_get (ms_regs (cfg_ms (nx i))) (Z_to_bv 5 10)) = true ->
  fo_dead (mkCfg ms model) (nx i).
Proof.
  intros ms model x8 I evs nx j i [Hcomp _] Hsvc Hoff Hj Hnr Hi Hr.
  exact (fo_dead_refusal_sib ms model x8 (evs j) (nx j) (nx i) Hsvc Hoff (Hcomp j) Hj Hnr Hi Hr).
Qed.

End WithSegs.

Definition codes02 : list word := [Z_to_bv 64 0; Z_to_bv 64 2].
Lemma in_codes02_0 : In (Z_to_bv 64 0) codes02. Proof. left. reflexivity. Qed.
Lemma in_codes02_2 : In (Z_to_bv 64 2) codes02. Proof. right. left. reflexivity. Qed.
