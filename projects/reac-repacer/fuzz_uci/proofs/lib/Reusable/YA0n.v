(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs: copied from proofs/cgif/cgif_file_fuzzer/lib/YA0n.v, with its module paths changed. *)
(* Modified by Theorem Labs: copied from proofs/libreac/fuzz_grant/lib/YA0n.v (donor image sha256 c2c7559b29bd), with its module paths changed. *)
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Wellfounded.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YK0n YK0i YK15 YK0j YK18 YK0k.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YK04 YK05 YA0i.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Section d. Context {fx : YK11.FPState}.
Open Scope bv_scope.
Section e.
Variable segs : list Segment.
Record world := mkW {
w_H : word -> bool ;
w_A : list (Z * Z) ;
w_Hoff : H_off_segments segs w_H ;
w_Awf : A_wf w_A }.
Definition wle (W W' : world) : Prop := hsub (w_H W') (w_H W).
Lemma wle_refl : forall W, wle W W.
Proof. intros W. apply hsub_refl. Qed.
Lemma wle_trans : forall W1 W2 W3, wle W1 W2 -> wle W2 W3 -> wle W1 W3.
Proof. intros W1 W2 W3 Ha Hc. eapply hsub_trans; [exact Hc | exact Ha]. Qed.
Lemma wle_same_H : forall H A A' HO HA HA', wle (mkW H A HO HA) (mkW H A' HO HA').
Proof. intros. apply hsub_refl. Qed.
Lemma wle_app_A : forall H A A2 HO HA HA2, wle (mkW H A HO HA) (mkW H (A2 ++ A) HO HA2).
Proof. intros. apply hsub_refl. Qed.
Lemma wle_hsub : forall H H' A HO HO' HA, hsub H' H -> wle (mkW H A HO HA) (mkW H' A HO' HA).
Proof. intros H H' A HO HO' HA Hs. exact Hs. Qed.
Local Notation AIw W md := (AI segs (w_H W) (w_A W) md).
Definition SRr (W : world) (c : config) (Q : world -> config -> Prop) : Prop :=
AIw W (cfg_model c) ->
forall T, (forall W' c', wle W W' -> AIw W' (cfg_model c') -> Q W' c' -> srealizes segs c' T) ->
srealizes segs c T.
Lemma SRr_ret : forall W c (Q : world -> config -> Prop), Q W c -> SRr W c Q.
Proof. intros W c Q HQ HI T HK. exact (HK W c (wle_refl W) HI HQ). Qed.
Lemma SRr_bind : forall W c (R Q : world -> config -> Prop),
SRr W c R -> (forall W' c', wle W W' -> R W' c' -> SRr W' c' Q) -> SRr W c Q.
Proof.
intros W c R Q H1 H2 HI T HK. apply (H1 HI T). intros W' c' Hle HI' HR.
apply (H2 W' c' Hle HR HI' T). intros W'' c'' Hle' HI'' HQ.
exact (HK W'' c'' (wle_trans _ _ _ Hle Hle') HI'' HQ).
Qed.
Lemma SRr_mono : forall W c (Q Q' : world -> config -> Prop),
SRr W c Q -> (forall W' c', wle W W' -> Q W' c' -> Q' W' c') -> SRr W c Q'.
Proof.
intros W c Q Q' H HQQ HI T HK. apply (H HI T). intros W' c' Hle HI' HQ.
exact (HK W' c' Hle HI' (HQQ W' c' Hle HQ)).
Qed.
Lemma SRr_srealizes : forall W c Q T,
SRr W c Q -> AIw W (cfg_model c) ->
(forall W' c', wle W W' -> AIw W' (cfg_model c') -> Q W' c' -> srealizes segs c' T) ->
srealizes segs c T.
Proof. intros W c Q T H HI HK. exact (H HI T HK). Qed.
Lemma SRr_case : forall (P : Prop) W c Q,
(P \/ ~ P) -> (P -> SRr W c Q) -> (~ P -> SRr W c Q) -> SRr W c Q.
Proof. intros P W c Q [p|np] H1 H2; auto. Qed.
Lemma SRr_use_AI : forall W c Q, (AIw W (cfg_model c) -> SRr W c Q) -> SRr W c Q.
Proof. intros W c Q H HI. exact (H HI HI). Qed.
Lemma SRr_world_le : forall W W' c Q,
wle W W' ->
(AIw W (cfg_model c) -> AIw W' (cfg_model c)) ->
SRr W' c Q -> SRr W c Q.
Proof.
intros W W' c Q Hle Htr H HI T HK. apply (H (Htr HI) T).
intros W'' c'' Hle' HI'' HQ. exact (HK W'' c'' (wle_trans _ _ _ Hle Hle') HI'' HQ).
Qed.
Lemma SRr_wf : forall (X : Type) (R : X -> X -> Prop),
well_founded R ->
forall (P : X -> world -> config -> Prop) (Q : world -> config -> Prop),
(forall x W c, P x W c -> SRr W c (fun W' c' => Q W' c' \/ exists x', R x' x /\ P x' W' c')) ->
forall x W c, P x W c -> SRr W c Q.
Proof.
intros X R Hwf P Q Hbody x.
induction (Hwf x) as [x _ IH].
intros W c HP. eapply SRr_bind; [apply Hbody, HP|].
intros W' c' _ [HQ | (x' & HR & HP')].
- apply SRr_ret, HQ.
- apply (IH x' HR W' c' HP').
Qed.
Lemma SRr_loop : forall (X : Type) (m : X -> nat)
(P : X -> world -> config -> Prop) (Q : world -> config -> Prop),
(forall x W c, P x W c -> SRr W c (fun W' c' => Q W' c' \/ exists x', (m x' < m x)%nat /\ P x' W' c')) ->
forall x W c, P x W c -> SRr W c Q.
Proof.
intros X m P Q Hbody.
apply (SRr_wf X (fun a b => (m a < m b)%nat)).
- apply (wf_inverse_image X nat lt m), PeanoNat.Nat.lt_wf_0.
- exact Hbody.
Qed.
Lemma SRr_loopZ : forall (X : Type) (m : X -> Z)
(P : X -> world -> config -> Prop) (Q : world -> config -> Prop),
(forall x W c, P x W c -> SRr W c (fun W' c' => Q W' c' \/ exists x', (0 <= m x' < m x)%Z /\ P x' W' c')) ->
forall x W c, P x W c -> SRr W c Q.
Proof.
intros X m P Q Hbody.
apply (SRr_wf X (fun a b => (0 <= m a < m b)%Z)).
- apply (wf_inverse_image X Z (fun x y => (0 <= x < y)%Z) m). apply Z.lt_wf with (z := 0%Z).
- exact Hbody.
Qed.
Lemma SRr_node : forall W c (I : Type) (nx : I -> config) (i0 : I) Q,
node_ok segs c I (fun _ => []) nx ->
(forall i, AIw W (cfg_model c) -> AIw W (cfg_model (nx i))) ->
(forall i, SRr W (nx i) Q) ->
SRr W c Q.
Proof.
intros W c I nx i0 Q Hnode HIt H HI T HK.
assert (HT0 : T []).
{ eapply srealizes_nonempty. apply (H i0 (HIt i0 HI) T HK). }
apply (srz_conseq segs c (t_alt (fun _ : I => t_emit [] T))).
- apply (srz_node segs c I (fun _ => []) nx (fun _ => T) i0 Hnode).
intros i. apply (H i (HIt i HI) T HK).
- intro tr. split.
+ intros [i Hi]. exact (proj1 (t_emit_nil_eq T HT0 tr) Hi).
+ intros Htr. exists i0. exact (proj2 (t_emit_nil_eq T HT0 tr) Htr).
Qed.
Lemma SRr_nodeI : forall W c (I : Type) (nx : I -> config) (i0 : I) Q,
(AIw W (cfg_model c) ->
node_ok segs c I (fun _ => []) nx /\ (forall i, AIw W (cfg_model (nx i)))) ->
(forall i, SRr W (nx i) Q) ->
SRr W c Q.
Proof.
intros W c I nx i0 Q Hn H HI. destruct (Hn HI) as [Hnode HIt].
apply (SRr_node W c I nx i0 Q Hnode); [intros i _; exact (HIt i) | exact H | exact HI].
Qed.
Hypothesis Hwx : wx_segs_nowrap segs.
Let KP (W : world) (Q : world -> config -> Prop) (T : TSet) : config -> Prop :=
fun c => AIw W (cfg_model c) -> srealizes segs c T.
Lemma SRr_step : forall W ms msr' model Q,
ms_svc_pending ms = None ->
RiscvSemantics.step segs (restrict (w_H W) ms) = MachineOk msr' ->
(forall model', same_but_materialized model model' ->
SRr W (mkCfg (unrestrict (w_H W) (ms_mem ms) msr') model') Q) ->
SRr W (mkCfg ms model) Q.
Proof.
intros W ms msr' model Q Hsvc Hs Hk HI T HK.
destruct HI as (HH & Hwf & Hcov & Hinv & Hh).
destruct (node_instr_restricted segs (w_H W) HH Hwx (w_A W) ms msr' model Hcov Hwf Hinv Hh Hsvc Hs)
as (model' & Hinv' & Hsame & _ & _ & Hnode).
apply (srz_silent1 segs _ _ T Hnode).
apply (Hk model' Hsame).
- apply (AI_same segs (w_H W) (w_A W) model model'); [split; auto | exact Hsame | exact Hinv'].
- exact HK.
Qed.
Lemma SRr_msteps : forall W ms msr' model Q,
msteps segs (restrict (w_H W) ms) msr' ->
(forall model', same_but_materialized model model' ->
hclean (w_H W) msr' ->
SRr W (mkCfg (unrestrict (w_H W) (ms_mem ms) msr') model') Q) ->
SRr W (mkCfg ms model) Q.
Proof.
intros W ms msr' model Q Hms Hk HI T HK.
destruct HI as (HH & Hwf & Hcov & Hinv & Hh).
assert (P1 : forall c c', YK04.node_ok segs c unit (fun _ => []) (fun _ => c') ->
srealizes segs c' T -> srealizes segs c T).
{ intros c c' Hn Hr. exact (srz_silent1 segs c c' T Hn Hr). }
apply (rz_msteps_restricted' segs (w_H W) HH Hwx (fun c => srealizes segs c T) P1
(w_A W) ms msr' model Hcov Hwf Hinv Hh Hms).
intros model' Hinv' Hsame Hcl. apply (Hk model' Hsame Hcl).
- apply (AI_same segs (w_H W) (w_A W) model model'); [split; auto | exact Hsame | exact Hinv'].
- exact HK.
Qed.
Lemma to_spin_of_msteps : forall H (HH : H_off_segments segs H) A msr0 msr',
msteps segs msr0 msr' ->
forall ms model,
msr0 = restrict H ms ->
lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model -> m_halted model = None ->
is_self_jump segs msr' = true ->
to_spin segs ms model.
Proof.
intros H HH A msr0 msr' Hms.
induction Hms as [msr | msr msr1 msr2 Hsvc Hstep Hrest IH]; intros ms model -> Hcov Hwf Hinv Hh Hj.
- apply is_self_jump_to_spin.
unfold is_self_jump in *. rewrite restrict_svc_pending in Hj. exact Hj.
- rewrite restrict_svc_pending in Hsvc.
destruct (node_instr_restricted segs H HH Hwx A ms msr1 model Hcov Hwf Hinv Hh Hsvc Hstep)
as (model1 & Hinv1 & Hsame1 & Hcl1 & Hacc & _).
pose proof (same_but_materialized_frame model model1 Hsame1) as Hfr.
apply (ts_step segs ms model (unrestrict H (ms_mem ms) msr1) model1 Hsvc Hacc).
apply (IH (unrestrict H (ms_mem ms) msr1) model1).
+ symmetry. apply restrict_unrestrict_clean. exact Hcl1.
+ replace (m_vm_lazy model1) with (m_vm_lazy model) by (symmetry; apply Hfr). exact Hcov.
+ exact Hwf.
+ exact Hinv1.
+ replace (m_halted model1) with (m_halted model) by (symmetry; apply Hfr). exact Hh.
+ exact Hj.
Qed.
Lemma spin_of_msteps : forall W ms msr' model,
AIw W model ->
msteps segs (restrict (w_H W) ms) msr' ->
is_self_jump segs msr' = true ->
spinning segs (mkCfg ms model).
Proof.
intros W ms msr' model (HH & Hwf & Hcov & Hinv & Hh) Hms Hj. split; [|exact Hh].
exact (to_spin_of_msteps (w_H W) HH (w_A W) _ _ Hms ms model eq_refl Hcov Hwf Hinv Hh Hj).
Qed.
Definition SRrE (W : world) (c : config) (evs : list event) (Q : world -> config -> Prop) : Prop :=
AIw W (cfg_model c) ->
forall T, (forall W' c', wle W W' -> AIw W' (cfg_model c') -> Q W' c' -> srealizes segs c' T) ->
srealizes segs c (t_emit evs T).
Lemma SRrE_of_SRr : forall W c Q, SRr W c Q -> SRrE W c [] Q.
Proof.
intros W c Q H HI T HK.
assert (HR : srealizes segs c T) by exact (H HI T HK).
eapply srz_conseq; [exact HR|]. apply t_eq_sym. apply t_emit_nil_eq. eapply srealizes_nonempty. exact HR.
Qed.
Lemma SRrE_ret : forall W c (Q : world -> config -> Prop), Q W c -> SRrE W c [] Q.
Proof. intros W c Q HQ. apply SRrE_of_SRr. apply SRr_ret. exact HQ. Qed.
Lemma SRrE_mono : forall W c evs (Q Q' : world -> config -> Prop),
SRrE W c evs Q -> (forall W' c', wle W W' -> Q W' c' -> Q' W' c') -> SRrE W c evs Q'.
Proof.
intros W c evs Q Q' H HQQ HI T HK. apply (H HI T). intros W' c' Hle HI' HQ.
exact (HK W' c' Hle HI' (HQQ W' c' Hle HQ)).
Qed.
Lemma SRrE_bind : forall W c e1 e2 (R Q : world -> config -> Prop),
SRrE W c e1 R -> (forall W' c', wle W W' -> R W' c' -> SRrE W' c' e2 Q) -> SRrE W c (e1 ++ e2) Q.
Proof.
intros W c e1 e2 R Q H1 H2 HI T HK.
eapply srz_conseq; [| apply t_emit_app].
apply (H1 HI (t_emit e2 T)). intros W' c' Hle HI' HR.
apply (H2 W' c' Hle HR HI' T). intros W'' c'' Hle' HI'' HQ.
exact (HK W'' c'' (wle_trans _ _ _ Hle Hle') HI'' HQ).
Qed.
Lemma SRr_SRrE : forall W c evs (R Q : world -> config -> Prop),
SRr W c R -> (forall W' c', wle W W' -> R W' c' -> SRrE W' c' evs Q) -> SRrE W c evs Q.
Proof.
intros W c evs R Q H1 H2. change evs with ([] ++ evs).
eapply SRrE_bind; [apply SRrE_of_SRr; exact H1 | exact H2].
Qed.
Lemma SRrE_SRr : forall W c evs (R Q : world -> config -> Prop),
SRrE W c evs R -> (forall W' c', wle W W' -> R W' c' -> SRr W' c' Q) -> SRrE W c evs Q.
Proof.
intros W c evs R Q H1 H2. rewrite <- (app_nil_r evs).
eapply SRrE_bind; [exact H1|]. intros W' c' Hle HR. apply SRrE_of_SRr. exact (H2 W' c' Hle HR).
Qed.
Lemma SRrE_case : forall (P : Prop) W c evs Q,
(P \/ ~ P) -> (P -> SRrE W c evs Q) -> (~ P -> SRrE W c evs Q) -> SRrE W c evs Q.
Proof. intros P W c evs Q [p|np] H1 H2; auto. Qed.
Lemma SRrE_use_AI : forall W c evs Q, (AIw W (cfg_model c) -> SRrE W c evs Q) -> SRrE W c evs Q.
Proof. intros W c evs Q H HI. exact (H HI HI). Qed.
Lemma SRrE_world_le : forall W W' c evs Q,
wle W W' -> (AIw W (cfg_model c) -> AIw W' (cfg_model c)) -> SRrE W' c evs Q -> SRrE W c evs Q.
Proof.
intros W W' c evs Q Hle Htr H HI T HK. apply (H (Htr HI) T).
intros W'' c'' Hle' HI'' HQ. exact (HK W'' c'' (wle_trans _ _ _ Hle Hle') HI'' HQ).
Qed.
Lemma SRrE_srealizes : forall W c evs Q T,
SRrE W c evs Q -> AIw W (cfg_model c) ->
(forall W' c', wle W W' -> AIw W' (cfg_model c') -> Q W' c' -> srealizes segs c' T) ->
srealizes segs c (t_emit evs T).
Proof. intros W c evs Q T H HI HK. exact (H HI T HK). Qed.
Lemma SRrE_intro : forall W c evs (Q : world -> config -> Prop),
(AIw W (cfg_model c) ->
forall T, (forall c', AIw W (cfg_model c') -> Q W c' -> srealizes segs c' T) -> srealizes segs c (t_emit evs T)) ->
SRrE W c evs Q.
Proof.
intros W c evs Q H HI T HK. apply (H HI T). intros c' HI' HQ. exact (HK W c' (wle_refl W) HI' HQ).
Qed.
End e.
End d.
Arguments SRr segs W c Q : clear implicits.
Arguments SRrE segs W c evs Q : clear implicits.
Arguments world segs : clear implicits.
Arguments mkW segs w_H w_A w_Hoff w_Awf : clear implicits.
Arguments wle {segs} W W'.
Arguments w_H {segs} w.
Arguments w_A {segs} w.
Arguments w_Hoff {segs} w.
Arguments w_Awf {segs} w.
