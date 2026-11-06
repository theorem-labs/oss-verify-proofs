(* Modified by Theorem Labs, 2026-10: ported from libreac/fuzz_decode proofs/libreac/fuzz_decode/lib/Reusable/YM06_cf.v at bf7779f81ed764787b77895d2f5c0db2627f33f3 for libdiginet/fuzz_decode; no image value changed; module path OSSVerify.Proofs.libdiginet.fuzz_decode.lib. *)
From Stdlib Require Import ZArith NArith List Lia Bool Classical_Prop.
From Stdlib Require Import Wellfounded.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Reusable Require Import YK11 YK0n YK0i YK15 YM06.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Reusable.R Require Import Cfg.
Import ListNotations.
Section d. Context {fx : YK11.FPState}.
Section e.
Variable segs : list Segment.

Inductive reach_av (Q : config -> Prop) : config -> config -> Prop :=
| ra_refl : forall c, ~ Q c -> reach_av Q c c
| ra_step : forall c e c1 c2, ~ Q c -> sstep_cfg segs ACFG c e (SNext c1) -> reach_av Q c1 c2 -> reach_av Q c c2.

Definition avoid (c : config) (Q : config -> Prop) : Prop :=
  forall c', reach_av Q c c' -> ~ budget_refused_at segs c'.

Definition SR_cf (c : config) (Q : config -> Prop) : Prop := SR segs c Q /\ avoid c Q.

Lemma SR_cf_SR : forall c Q, SR_cf c Q -> SR segs c Q.
Proof using. intros c Q H. exact (proj1 H). Qed.

Lemma avoid_here : forall c Q, avoid c Q -> ~ Q c -> ~ budget_refused_at segs c.
Proof using. intros c Q H HQ. apply H. apply ra_refl. exact HQ. Qed.

Lemma avoid_step : forall c e c1 Q, avoid c Q -> ~ Q c -> sstep_cfg segs ACFG c e (SNext c1) -> avoid c1 Q.
Proof using. intros c e c1 Q H HQ Hs c' Hr. apply H. eapply ra_step; eassumption. Qed.

Lemma avoid_cut_free : forall c Q,
  avoid c Q -> (forall c', Q c' -> cut_free segs c') -> cut_free segs c.
Proof using.
  intros c Q H HK tr c' Hstar. revert H.
  induction Hstar as [c | c1 evs c2 tr c3 Hs Hstar IH]; intros H.
  - destruct (classic (Q c)) as [HQ | HQ].
    + exact (cut_free_here segs c (HK c HQ)).
    + exact (avoid_here c Q H HQ).
  - destruct (classic (Q c1)) as [HQ | HQ].
    + apply (HK c1 HQ (evs ++ tr) c3). eapply star_cfg_step; eassumption.
    + apply IH. exact (avoid_step c1 evs c2 Q H HQ Hs).
Qed.

Theorem SR_cf_crealizes : forall c Q T,
  SR_cf c Q -> (forall c', Q c' -> realizes segs c' T /\ cut_free segs c') ->
  realizes segs c T /\ cut_free segs c.
Proof using.
  intros c Q T [HS HA] HK. split.
  - apply HS. intros c' HQ. exact (proj1 (HK c' HQ)).
  - apply (avoid_cut_free c Q HA). intros c' HQ. exact (proj2 (HK c' HQ)).
Qed.

Lemma avoid_ret : forall c (Q : config -> Prop), Q c -> avoid c Q.
Proof using. intros c Q HQ c' Hr. inversion Hr as [c0 H0 E1 E2 | c0 e c1 c2 H0 Hs Hr' E1 E2]; subst; contradiction. Qed.

Lemma avoid_mono : forall c (Q Q' : config -> Prop),
  avoid c Q -> (forall c', Q c' -> Q' c') -> avoid c Q'.
Proof using.
  intros c Q Q' H HQ c' Hr. apply H. clear H.
  induction Hr as [c HQ' | c e c1 c2 HQ' Hs Hr IH].
  - apply ra_refl. intros Hq. apply HQ', HQ, Hq.
  - eapply ra_step; [intros Hq; apply HQ', HQ, Hq | exact Hs | exact IH].
Qed.

Lemma avoid_bind : forall c (R Q : config -> Prop),
  avoid c R -> (forall c', R c' -> avoid c' Q) -> avoid c Q.
Proof using.
  intros c R Q H1 H2 c' Hr. revert H1.
  induction Hr as [c HQ | c e c1 c2 HQ Hs Hr IH]; intros H1.
  - destruct (classic (R c)) as [HR | HR].
    + apply (H2 c HR). apply ra_refl. exact HQ.
    + exact (avoid_here c R H1 HR).
  - destruct (classic (R c)) as [HR | HR].
    + apply (H2 c HR). eapply ra_step; eassumption.
    + apply IH. exact (avoid_step c e c1 R H1 HR Hs).
Qed.

Lemma avoid_node : forall c (I : Type) (nx : I -> config) Q,
  node_ok segs c I (fun _ => []) nx -> ~ budget_refused_at segs c ->
  (forall i, avoid (nx i) Q) -> avoid c Q.
Proof using.
  intros c I nx Q [_ Hc] Hb H c' Hr. inversion Hr as [c0 HQ E1 E2 | c0 e c1 c2 HQ Hs Hr' E1 E2]; subst.
  - exact Hb.
  - destruct (Hc e (SNext c1) Hs) as (i & _ & E). injection E as ->. exact (H i c' Hr').
Qed.

Lemma SR_cf_ret : forall c (Q : config -> Prop), Q c -> SR_cf c Q.
Proof using. intros c Q HQ. split; [apply SR_ret; exact HQ | apply avoid_ret; exact HQ]. Qed.

Lemma SR_cf_bind : forall c (R Q : config -> Prop),
  SR_cf c R -> (forall c', R c' -> SR_cf c' Q) -> SR_cf c Q.
Proof using.
  intros c R Q [H1 A1] H2. split.
  - apply (SR_bind segs c R Q H1). intros c' HR. exact (proj1 (H2 c' HR)).
  - apply (avoid_bind c R Q A1). intros c' HR. exact (proj2 (H2 c' HR)).
Qed.

Lemma SR_cf_mono : forall c (Q Q' : config -> Prop),
  SR_cf c Q -> (forall c', Q c' -> Q' c') -> SR_cf c Q'.
Proof using.
  intros c Q Q' [H A] HQ. split; [exact (SR_mono segs c Q Q' H HQ) | exact (avoid_mono c Q Q' A HQ)].
Qed.

Lemma SR_cf_node : forall c (I : Type) (nx : I -> config) (i0 : I) Q,
  node_ok segs c I (fun _ => []) nx -> ~ budget_refused_at segs c ->
  (forall i, SR_cf (nx i) Q) -> SR_cf c Q.
Proof using.
  intros c I nx i0 Q Hn Hb H. split.
  - apply (SR_node segs c I nx i0 Q Hn). intros i. exact (proj1 (H i)).
  - apply (avoid_node c I nx Q Hn Hb). intros i. exact (proj2 (H i)).
Qed.

Lemma SR_cf_step : forall ms model ms' Q,
  m_halted model = None -> m_vm_lazy model = [] -> ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  SR_cf (mkCfg ms' model) Q -> SR_cf (mkCfg ms model) Q.
Proof using.
  intros ms model ms' Q Hh Hl Hs Hst H.
  apply (SR_cf_node (mkCfg ms model) unit (fun _ => mkCfg ms' model) tt Q).
  - exact (node_instr segs ms model ms' Hh Hl Hs Hst).
  - exact (budget_refused_at_no_lazy_instr segs ms model Hl Hs).
  - intros []. exact H.
Qed.

Lemma SR_cf_msteps : forall ms ms' model Q,
  m_halted model = None -> m_vm_lazy model = [] -> msteps segs ms ms' ->
  SR_cf (mkCfg ms' model) Q -> SR_cf (mkCfg ms model) Q.
Proof using.
  intros ms ms' model Q Hh Hl Hms.
  induction Hms as [ms | ms ms1 ms2 Hsvc Hstep Hms IH]; intro H; [exact H|].
  eapply SR_cf_step; [exact Hh | exact Hl | exact Hsvc | exact Hstep | apply IH; exact H].
Qed.

Lemma SR_cf_case : forall (A : Prop) c Q,
  (A \/ ~ A) -> (A -> SR_cf c Q) -> (~ A -> SR_cf c Q) -> SR_cf c Q.
Proof using. intros A c Q [a|na] H1 H2; auto. Qed.

Lemma SR_cf_wf : forall (W : Type) (R : W -> W -> Prop),
  well_founded R ->
  forall (P : W -> config -> Prop) (Q : config -> Prop),
  (forall w c, P w c -> SR_cf c (fun c' => Q c' \/ exists w', R w' w /\ P w' c')) ->
  forall w c, P w c -> SR_cf c Q.
Proof using.
  intros W R Hwf P Q Hbody w.
  induction (Hwf w) as [w _ IH].
  intros c HP. eapply SR_cf_bind; [apply Hbody, HP|].
  intros c' [HQ | (w' & HR & HP')].
  - apply SR_cf_ret, HQ.
  - apply (IH w' HR c' HP').
Qed.

Lemma SR_cf_loop : forall (W : Type) (m : W -> nat)
  (P : W -> config -> Prop) (Q : config -> Prop),
  (forall w c, P w c -> SR_cf c (fun c' => Q c' \/ exists w', (m w' < m w)%nat /\ P w' c')) ->
  forall w c, P w c -> SR_cf c Q.
Proof using.
  intros W m P Q Hbody.
  apply (SR_cf_wf W (fun a b => (m a < m b)%nat)).
  - apply (wf_inverse_image W nat lt m), PeanoNat.Nat.lt_wf_0.
  - exact Hbody.
Qed.

Lemma SR_cf_loopZ : forall (W : Type) (m : W -> Z)
  (P : W -> config -> Prop) (Q : config -> Prop),
  (forall w c, P w c -> SR_cf c (fun c' => Q c' \/ exists w', (0 <= m w' < m w)%Z /\ P w' c')) ->
  forall w c, P w c -> SR_cf c Q.
Proof using.
  intros W m P Q Hbody.
  apply (SR_cf_wf W (fun a b => (0 <= m a < m b)%Z)).
  - apply (wf_inverse_image W Z (fun x y => (0 <= x < y)%Z) m). apply Z.lt_wf with (z := 0%Z).
  - exact Hbody.
Qed.

Definition vml (c : config) : Z := vm_limit (m_vmmaps (cfg_model c)).

Definition avoidv (c : config) (Q : config -> Prop) : Prop :=
  forall c', reach_av Q c c' ->
    ~ budget_refused_at segs c' /\ vml c' = vml c /\
    (forall e c'', sstep_cfg segs ACFG c' e (SNext c'') -> vml c'' = vml c').

Definition SR_cfv (c : config) (Q : config -> Prop) : Prop := SR segs c Q /\ avoidv c Q.

Lemma avoidv_avoid : forall c Q, avoidv c Q -> avoid c Q.
Proof using. intros c Q H c' Hr. exact (proj1 (H c' Hr)). Qed.

Lemma SR_cfv_SR_cf : forall c Q, SR_cfv c Q -> SR_cf c Q.
Proof using. intros c Q [H A]. split; [exact H | exact (avoidv_avoid c Q A)]. Qed.

Lemma SR_cfv_SR : forall c Q, SR_cfv c Q -> SR segs c Q.
Proof using. intros c Q H. exact (proj1 H). Qed.

Theorem SR_cfv_crealizes : forall c Q T,
  SR_cfv c Q -> (forall c', Q c' -> realizes segs c' T /\ cut_free segs c') ->
  realizes segs c T /\ cut_free segs c.
Proof using. intros c Q T H HK. exact (SR_cf_crealizes c Q T (SR_cfv_SR_cf c Q H) HK). Qed.

Lemma avoidv_step : forall c e c1 Q, avoidv c Q -> ~ Q c -> sstep_cfg segs ACFG c e (SNext c1) -> avoidv c1 Q.
Proof using.
  intros c e c1 Q H HQ Hs c' Hr.
  destruct (H c (ra_refl Q c HQ)) as (_ & _ & S0).
  destruct (H c' (ra_step Q c e c1 c' HQ Hs Hr)) as (B & V & S).
  pose proof (S0 e c1 Hs) as V1. split; [exact B|]. split; [congruence | exact S].
Qed.

Lemma avoidv_ret : forall c (Q : config -> Prop), Q c -> avoidv c Q.
Proof using. intros c Q HQ c' Hr. inversion Hr as [c0 H0 E1 E2 | c0 e c1 c2 H0 Hs Hr' E1 E2]; subst; contradiction. Qed.

Lemma avoidv_mono : forall c (Q Q' : config -> Prop),
  avoidv c Q -> (forall c', Q c' -> Q' c') -> avoidv c Q'.
Proof using.
  intros c Q Q' H HQ c' Hr. apply H. clear H.
  induction Hr as [c HQ' | c e c1 c2 HQ' Hs Hr IH].
  - apply ra_refl. intros Hq. apply HQ', HQ, Hq.
  - eapply ra_step; [intros Hq; apply HQ', HQ, Hq | exact Hs | exact IH].
Qed.

Lemma avoidv_bind : forall c (R Q : config -> Prop),
  avoidv c R -> (forall c', R c' -> vml c' = vml c -> avoidv c' Q) -> avoidv c Q.
Proof using.
  intros c R Q H1 H2 c' Hr. revert H1 H2.
  induction Hr as [c HQ | c e c1 c2 HQ Hs Hr IH]; intros H1 H2.
  - destruct (classic (R c)) as [HR | HR].
    + apply (H2 c HR eq_refl). apply ra_refl. exact HQ.
    + exact (H1 c (ra_refl R c HR)).
  - destruct (classic (R c)) as [HR | HR].
    + apply (H2 c HR eq_refl). eapply ra_step; eassumption.
    + destruct (H1 c (ra_refl R c HR)) as (_ & _ & S0). pose proof (S0 e c1 Hs) as V1.
      assert (H2' : forall c', R c' -> vml c' = vml c1 -> avoidv c' Q).
      { intros c' HR' V'. apply (H2 c' HR'). congruence. }
      destruct (IH (avoidv_step c e c1 R H1 HR Hs) H2') as (B & V & S).
      split; [exact B|]. split; [congruence | exact S].
Qed.

Lemma avoidv_node : forall c (I : Type) (nx : I -> config) Q,
  node_ok segs c I (fun _ => []) nx -> ~ budget_refused_at segs c ->
  (forall i, vml (nx i) = vml c) ->
  (forall i, avoidv (nx i) Q) -> avoidv c Q.
Proof using.
  intros c I nx Q [_ Hc] Hb HV H c' Hr. inversion Hr as [c0 HQ E1 E2 | c0 e c1 c2 HQ Hs Hr' E1 E2]; subst.
  - split; [exact Hb|]. split; [reflexivity|].
    intros e c'' Hs. destruct (Hc e (SNext c'') Hs) as (i & _ & E). injection E as ->. apply HV.
  - destruct (Hc e (SNext c1) Hs) as (i & _ & E). injection E as ->.
    destruct (H i c' Hr') as (B & V & S). split; [exact B|]. split; [rewrite V; apply HV | exact S].
Qed.

Lemma SR_cfv_ret : forall c (Q : config -> Prop), Q c -> SR_cfv c Q.
Proof using. intros c Q HQ. split; [apply SR_ret; exact HQ | apply avoidv_ret; exact HQ]. Qed.

Lemma SR_cfv_bind : forall c (R Q : config -> Prop),
  SR_cfv c R -> (forall c', R c' -> SR_cfv c' Q) -> SR_cfv c Q.
Proof using.
  intros c R Q [H1 A1] H2. split.
  - apply (SR_bind segs c R Q H1). intros c' HR. exact (proj1 (H2 c' HR)).
  - apply (avoidv_bind c R Q A1). intros c' HR _. exact (proj2 (H2 c' HR)).
Qed.

Lemma SR_cfv_mono : forall c (Q Q' : config -> Prop),
  SR_cfv c Q -> (forall c', Q c' -> Q' c') -> SR_cfv c Q'.
Proof using.
  intros c Q Q' [H A] HQ. split; [exact (SR_mono segs c Q Q' H HQ) | exact (avoidv_mono c Q Q' A HQ)].
Qed.

Lemma SR_cfv_node : forall c (I : Type) (nx : I -> config) (i0 : I) Q,
  node_ok segs c I (fun _ => []) nx -> ~ budget_refused_at segs c ->
  (forall i, vml (nx i) = vml c) ->
  (forall i, SR_cfv (nx i) Q) -> SR_cfv c Q.
Proof using.
  intros c I nx i0 Q Hn Hb HV H. split.
  - apply (SR_node segs c I nx i0 Q Hn). intros i. exact (proj1 (H i)).
  - apply (avoidv_node c I nx Q Hn Hb HV). intros i. exact (proj2 (H i)).
Qed.

Lemma SR_cfv_step : forall ms model ms' Q,
  m_halted model = None -> m_vm_lazy model = [] -> ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  SR_cfv (mkCfg ms' model) Q -> SR_cfv (mkCfg ms model) Q.
Proof using.
  intros ms model ms' Q Hh Hl Hs Hst H.
  apply (SR_cfv_node (mkCfg ms model) unit (fun _ => mkCfg ms' model) tt Q).
  - exact (node_instr segs ms model ms' Hh Hl Hs Hst).
  - exact (budget_refused_at_no_lazy_instr segs ms model Hl Hs).
  - intros []. reflexivity.
  - intros []. exact H.
Qed.

Lemma SR_cfv_msteps : forall ms ms' model Q,
  m_halted model = None -> m_vm_lazy model = [] -> msteps segs ms ms' ->
  SR_cfv (mkCfg ms' model) Q -> SR_cfv (mkCfg ms model) Q.
Proof using.
  intros ms ms' model Q Hh Hl Hms.
  induction Hms as [ms | ms ms1 ms2 Hsvc Hstep Hms IH]; intro H; [exact H|].
  eapply SR_cfv_step; [exact Hh | exact Hl | exact Hsvc | exact Hstep | apply IH; exact H].
Qed.

Lemma SR_cfv_case : forall (A : Prop) c Q,
  (A \/ ~ A) -> (A -> SR_cfv c Q) -> (~ A -> SR_cfv c Q) -> SR_cfv c Q.
Proof using. intros A c Q [a|na] H1 H2; auto. Qed.

Lemma SR_cfv_wf : forall (W : Type) (R : W -> W -> Prop),
  well_founded R ->
  forall (P : W -> config -> Prop) (Q : config -> Prop),
  (forall w c, P w c -> SR_cfv c (fun c' => Q c' \/ exists w', R w' w /\ P w' c')) ->
  forall w c, P w c -> SR_cfv c Q.
Proof using.
  intros W R Hwf P Q Hbody w.
  induction (Hwf w) as [w _ IH].
  intros c HP. eapply SR_cfv_bind; [apply Hbody, HP|].
  intros c' [HQ | (w' & HR & HP')].
  - apply SR_cfv_ret, HQ.
  - apply (IH w' HR c' HP').
Qed.

Lemma SR_cfv_loop : forall (W : Type) (m : W -> nat)
  (P : W -> config -> Prop) (Q : config -> Prop),
  (forall w c, P w c -> SR_cfv c (fun c' => Q c' \/ exists w', (m w' < m w)%nat /\ P w' c')) ->
  forall w c, P w c -> SR_cfv c Q.
Proof using.
  intros W m P Q Hbody.
  apply (SR_cfv_wf W (fun a b => (m a < m b)%nat)).
  - apply (wf_inverse_image W nat lt m), PeanoNat.Nat.lt_wf_0.
  - exact Hbody.
Qed.

Lemma SR_cfv_loopZ : forall (W : Type) (m : W -> Z)
  (P : W -> config -> Prop) (Q : config -> Prop),
  (forall w c, P w c -> SR_cfv c (fun c' => Q c' \/ exists w', (0 <= m w' < m w)%Z /\ P w' c')) ->
  forall w c, P w c -> SR_cfv c Q.
Proof using.
  intros W m P Q Hbody.
  apply (SR_cfv_wf W (fun a b => (0 <= m a < m b)%Z)).
  - apply (wf_inverse_image W Z (fun x y => (0 <= x < y)%Z) m). apply Z.lt_wf with (z := 0%Z).
  - exact Hbody.
Qed.

End e.
End d.
Arguments SR_cf segs c Q : clear implicits.
Arguments avoid segs c Q : clear implicits.
Arguments avoidv segs c Q : clear implicits.
Arguments SR_cfv segs c Q : clear implicits.
