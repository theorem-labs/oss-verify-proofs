(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11-05: copied from projects/cgif/cgif_rgb_fuzzer/proofs/lib/HaltsFO.v at theorem-labs/oss-verify-proofs@c5665593c2d8,
   lines 13-171 and 314-316, with its lead comment replaced by this line.  The import of that tree's YK15 becomes
   OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.ShapeAlg, which holds the same TSet algebra, the same node_ok over
   plain sstep and the same three-constructor realizes.  Its lines 173-311 (injected_family_off_*, fo_dead_refusal*,
   fo_dead_node, refusal_b_*, ret_in_errnos_*, small_not_errno, mmap_*_refusal, apply_effect_a0) are not copied:
   nothing here needs a dead refusal arm, because the plain and UBSan closures of this target are built with realizes,
   which has no spin constructor. *)
(* Modified by Theorem Labs, 2026-11: for LPS 727298f3, fo_progress covers the three vDSO arms of sstep (the vDSO call steps by sstep_cfg_vdso_call, and NOERR refutes the vDSO materialization fault and the unmodeled vDSO call), the induction of fo_of_realizes binds the read-only-backing premise Hrob of rz_node, with a comment of this file's own on each of these two changes, the dead refusal arm (fo_dead_refusal, fo_dead_refusal_sib and fo_dead_node, with apply_effect_a0, in_sysno_sys_input and ret_in_errnos_errno) is copied from projects/cgif/cgif_rgb_fuzzer/proofs/lib/HaltsFO.v lines 173-310 at theorem-labs/oss-verify-proofs@f92feaf8b7e6, without the lemmas nothing here uses, and adapted to the vDSO arms, without the source's seven comments on those declarations (one above each of apply_effect_a0, fo_dead_refusal_sib and fo_dead_node, four in the proof of fo_dead_refusal) and with a comment of this file's own above fo_dead_refusal, and alloc3_family_off, alloc3_refusal_b, dead_sib, fo_dead_of_sib, dead_sib_eff and ret_in_enomem are added for the refused ENOMEM arm of munmap, mmap and mprotect; this line takes back what lines 3-9 say of the dead refusal arm and of the six declarations copied with it: the flagged derivation srealizesM of Common/SpinAlg.v needs that arm, through fo_dead_of_sib; the line above names its source commit by its public id. *)
From Stdlib Require Import ZArith NArith List Lia Bool Classical_Prop.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import ShapeAlg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.

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
  (* LPS 08b1429/75d69e00: [sstep] has three vDSO constructors after [sstep_instr_unmodeled]
     ([c0dd863a:theories/LinuxProcessSem/Run.v:724-761]), in the model's order: the call reaches [SNext] and has its own unfiltered
     [sstep_cfg_vdso_call] twin; the materialization fault and the unmodeled call conclude
     [SError], which [NOERR] refutes exactly as it does the syscall's. *)
  - eexists _, _. eapply sstep_cfg_vdso_call; eassumption.
  - exfalso. eapply NOERR. eapply sstep_vdso_materialization_fault; eassumption.
  - exfalso. eapply NOERR. eapply sstep_vdso_unmodeled; eassumption.
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
  (* (B2): [rz_node] asks [RomBase.sys_rob]; the halting argument does not read it. *)
  intros c T H; induction H as [c I evs nx T i0 Hnode Hrob Hcont IH | c Hh | c T T' H IH Heq].
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

(* The dead refusal arm, copied from projects/cgif/cgif_rgb_fuzzer/proofs/lib/HaltsFO.v lines 173-310
   (theorem-labs/oss-verify-proofs@f92feaf8b7e6).  [sstep_cfg] and [sstep] have the three vDSO
   arms after [*_instr_unmodeled]; the inversions below close them with the pending-call fact, as they close the
   instruction arm. *)
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
  inversion Hstep; subst; cbn [cfg_ms cfg_model] in *; try congruence.
  match goal with
  | [ H : ~ spurious_refusal_cfg _ (sys_input _ _ ?y) _ ?eff |- _ ] =>
      apply H; replace y with x8 by congruence
  end.
  split; [exact Hoff | split; [| exact Hex]].
  eapply Href; reflexivity.
Qed.

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

Lemma ret_in_errnos_errno : forall es e, In e es -> ret_in_errnos es (errno_ret e) = true.
Proof.
  intros es e Hin. unfold ret_in_errnos. apply existsb_exists. exists e. split; [exact Hin|].
  apply bv_eqb_eq. reflexivity.
Qed.

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
  - inversion Hsib; subst; cbn [cfg_ms cfg_model] in *; try congruence.
    match goal with
    | [ H : syscall_spec (sys_input segs ms ?y) model (Ok ?eff ?m' ?evs) |- _ ] =>
        assert (Hy : y = x8) by congruence; rewrite Hy in H; exists eff, m', evs; split; [exact H|]
    end.
    rewrite apply_effect_a0 in Hnr. exact Hnr.
  - exact Hsvc'.
  - intros eff model'' Hms _. rewrite Hms, apply_effect_a0 in Hr. exact Hr.
Qed.

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

(* The three allocation calls a plan's mapping nodes make -- munmap (215), mmap (222), mprotect (226) -- inject
   from the allocation family, which [forced_only_cfg] turns off, and each refuses with the one errno ENOMEM
   (Sys/Mm/Mmap.v [munmap_errnos], [mmap_errnos]; Sys/Mm/Mprotect.v [mprotect_errnos]). *)
Lemma alloc3_family_off : forall ms x8,
  In (bv_unsigned x8) [215; 222; 226]%Z -> injected_family_off forced_only_cfg (sys_input segs ms x8) = true.
Proof.
  intros ms x8 H. unfold injected_family_off. rewrite in_sysno_sys_input.
  destruct H as [H|[H|[H|[]]]]; rewrite <- H; reflexivity.
Qed.
Lemma alloc3_refusal_b : forall ms x8 model r,
  In (bv_unsigned x8) [215; 222; 226]%Z -> refusal_b (sys_input segs ms x8) model r = ret_in_errnos [ENOMEM] r.
Proof.
  intros ms x8 model r H. unfold refusal_b. rewrite in_sysno_sys_input.
  destruct H as [H|[H|[H|[]]]]; rewrite <- H; reflexivity.
Qed.

(* A refused arm of one of those calls whose node also has an arm that is no refusal: the arm a flagged
   derivation ([Common/SpinAlg.srealizesM]) may leave at the flag [false].  The statement reads only the
   machine states, so it survives a change of the segment list and of the read-only backing. *)
Definition dead_sib (c cj ci : config) : Prop :=
  exists x8, ms_svc_pending (cfg_ms c) = Some x8 /\ In (bv_unsigned x8) [215; 222; 226]%Z /\
    ms_svc_pending (cfg_ms cj) = None /\ ret_in_errnos [ENOMEM] (reg_get (ms_regs (cfg_ms cj)) (Z_to_bv 5 10)) = false /\
    ms_svc_pending (cfg_ms ci) = None /\ ret_in_errnos [ENOMEM] (reg_get (ms_regs (cfg_ms ci)) (Z_to_bv 5 10)) = true.

Lemma fo_dead_of_sib : forall c (I : Type) (evs : I -> list event) (nx : I -> config) (j i : I),
  node_ok segs c I evs nx -> dead_sib c (nx j) (nx i) -> fo_dead c (nx i).
Proof.
  intros [ms model] I evs nx j i Hn (x8 & Hsvc & H3 & Hj & Hjr & Hi & Hir). cbn [cfg_ms] in Hsvc.
  apply (fo_dead_node ms model x8 I evs nx j i Hn Hsvc (alloc3_family_off ms x8 H3) Hj); [| exact Hi |].
  - rewrite (alloc3_refusal_b ms x8 model _ H3). exact Hjr.
  - rewrite (alloc3_refusal_b ms x8 model _ H3). exact Hir.
Qed.

Lemma dead_sib_eff : forall ms model x8 (effj effi : SyscallEffect) (mj mi : Model),
  ms_svc_pending ms = Some x8 -> In (bv_unsigned x8) [215; 222; 226]%Z ->
  ret_in_errnos [ENOMEM] (eff_ret effj) = false -> ret_in_errnos [ENOMEM] (eff_ret effi) = true ->
  dead_sib (mkCfg ms model) (mkCfg (advance_past_svc (apply_effect ms effj)) mj)
           (mkCfg (advance_past_svc (apply_effect ms effi)) mi).
Proof.
  intros ms model x8 effj effi mj mi Hsvc H3 Hj Hi. exists x8. cbn [cfg_ms].
  rewrite !apply_effect_a0. exact (conj Hsvc (conj H3 (conj eq_refl (conj Hj (conj eq_refl Hi))))).
Qed.

Lemma ret_in_enomem : ret_in_errnos [ENOMEM] (errno_ret ENOMEM) = true.
Proof. apply ret_in_errnos_errno. left. reflexivity. Qed.

End WithSegs.

Definition codes02 : list word := [Z_to_bv 64 0; Z_to_bv 64 2].
Lemma in_codes02_0 : In (Z_to_bv 64 0) codes02. Proof. left. reflexivity. Qed.
Lemma in_codes02_2 : In (Z_to_bv 64 2) codes02. Proof. right. left. reflexivity. Qed.
