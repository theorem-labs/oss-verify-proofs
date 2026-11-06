(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Wellfounded.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK0o YK0j YK15 YK0k YK18 YK0l.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YK06 YA0i.
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



Local Notation AIw W md := (AI segs (w_H W) (w_A W) md).
(* [comment removed for export] *)
Definition SRr (W : world) (c : config) (Q : world -> config -> Prop) : Prop :=
forall b : bool,
AIw W (cfg_model c) ->
forall T, (forall W' c', wle W W' -> AIw W' (cfg_model c') -> Q W' c' -> srealizesM segs b c' T) ->
srealizesM segs b c T.
Lemma SRr_ret : forall W c (Q : world -> config -> Prop), Q W c -> SRr W c Q.
Proof. intros W c Q HQ b HI T HK. exact (HK W c (wle_refl W) HI HQ). Qed.
Lemma SRr_bind : forall W c (R Q : world -> config -> Prop),
SRr W c R -> (forall W' c', wle W W' -> R W' c' -> SRr W' c' Q) -> SRr W c Q.
Proof.
intros W c R Q H1 H2 b HI T HK. apply (H1 b HI T). intros W' c' Hle HI' HR.
apply (H2 W' c' Hle HR b HI' T). intros W'' c'' Hle' HI'' HQ.
exact (HK W'' c'' (wle_trans _ _ _ Hle Hle') HI'' HQ).
Qed.
Lemma SRr_mono : forall W c (Q Q' : world -> config -> Prop),
SRr W c Q -> (forall W' c', wle W W' -> Q W' c' -> Q' W' c') -> SRr W c Q'.
Proof.
intros W c Q Q' H HQQ b HI T HK. apply (H b HI T). intros W' c' Hle HI' HQ.
exact (HK W' c' Hle HI' (HQQ W' c' Hle HQ)).
Qed.
Lemma SRr_srealizesM : forall b W c Q T,
SRr W c Q -> AIw W (cfg_model c) ->
(forall W' c', wle W W' -> AIw W' (cfg_model c') -> Q W' c' -> srealizesM segs b c' T) ->
srealizesM segs b c T.
Proof. intros b W c Q T H HI HK. exact (H b HI T HK). Qed.
Lemma SRr_srealizes : forall W c Q T,
SRr W c Q -> AIw W (cfg_model c) ->
(forall W' c', wle W W' -> AIw W' (cfg_model c') -> Q W' c' -> srealizes segs c' T) ->
srealizes segs c T.
Proof. intros W c Q T H HI HK. exact (H true HI T HK). Qed.

Lemma SRr_use_AI : forall W c Q, (AIw W (cfg_model c) -> SRr W c Q) -> SRr W c Q.
Proof. intros W c Q H b HI. exact (H HI b HI). Qed.
Lemma SRr_world_le : forall W W' c Q,
wle W W' ->
(AIw W (cfg_model c) -> AIw W' (cfg_model c)) ->
SRr W' c Q -> SRr W c Q.
Proof.
intros W W' c Q Hle Htr H b HI T HK. apply (H b (Htr HI) T).
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
intros W c I nx i0 Q Hnode HIt H b HI T HK.
assert (HT0 : T []).
{ eapply srealizesM_nonempty. apply (H i0 b (HIt i0 HI) T HK). }
apply (srzM_conseq segs b c (t_alt (fun _ : I => t_emit [] T))).
- apply (srzM_node segs b c I (fun _ => []) nx (fun _ => T) i0 Hnode).
intros i. apply (H i b (HIt i HI) T HK).
- intro tr. split.
+ intros [i Hi]. exact (proj1 (t_emit_nil_eq T HT0 tr) Hi).
+ intros Htr. exists i0. exact (proj2 (t_emit_nil_eq T HT0 tr) Htr).
Qed.




Hypothesis Hwx : wx_segs_nowrap segs.
Let KP (b : bool) (W : world) (Q : world -> config -> Prop) (T : TSet) : config -> Prop :=
fun c => AIw W (cfg_model c) -> srealizesM segs b c T.
Lemma SRr_step : forall W ms msr' model Q,
ms_svc_pending ms = None ->
RiscvSemantics.step segs (restrict (w_H W) ms) = MachineOk msr' ->
(forall model', same_but_materialized model model' ->
SRr W (mkCfg (unrestrict (w_H W) (ms_mem ms) msr') model') Q) ->
SRr W (mkCfg ms model) Q.
Proof.
intros W ms msr' model Q Hsvc Hs Hk b HI T HK.
destruct HI as (HH & Hwf & Hcov & Hinv & Hh).
destruct (node_instr_restricted segs (w_H W) HH Hwx (w_A W) ms msr' model Hcov Hwf Hinv Hh Hsvc Hs)
as (model' & Hinv' & Hsame & _ & _ & Hnode).
apply (srzM_silent1 segs b _ _ T Hnode).
apply (Hk model' Hsame b).
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
intros W ms msr' model Q Hms Hk b HI T HK.
destruct HI as (HH & Hwf & Hcov & Hinv & Hh).
assert (P1 : forall c c', YK05.node_ok segs c unit (fun _ => []) (fun _ => c') ->
srealizesM segs b c' T -> srealizesM segs b c T).
{ intros c c' Hn Hr. exact (srzM_silent1 segs b c c' T Hn Hr). }
apply (rz_msteps_restricted' segs (w_H W) HH Hwx (fun c => srealizesM segs b c T) P1
(w_A W) ms msr' model Hcov Hwf Hinv Hh Hms).
intros model' Hinv' Hsame Hcl. apply (Hk model' Hsame Hcl b).
- apply (AI_same segs (w_H W) (w_A W) model model'); [split; auto | exact Hsame | exact Hinv'].
- exact HK.
Qed.


Definition SRrE (W : world) (c : config) (evs : list event) (Q : world -> config -> Prop) : Prop :=
forall b : bool,
AIw W (cfg_model c) ->
forall T, (forall W' c', wle W W' -> AIw W' (cfg_model c') -> Q W' c' -> srealizesM segs b c' T) ->
srealizesM segs b c (t_emit evs T).











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
