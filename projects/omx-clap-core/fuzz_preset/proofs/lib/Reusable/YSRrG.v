(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* The machine-step and branch lemmas of the step relation over a world relation R (YA0nH.SRrG). A free or realloc of
   a live block can hide shadow again, so a walk that crosses one proves SRrG at a relation wider than wle (YA0nH.wle'
   at a zone). YA0n.v's SRr_step / SRr_msteps and YC1fP.v's paj_branch fix the relation to wle; the lemmas here are
   their R forms, with the same proofs: a step does not change the world, so no law of R is used.
   - SRrG_step / SRrG_msteps: YA0n.v SRr_step / SRr_msteps over R (arguments segs R Hwx, then SRr_step's).
   - paj_branchR: YC1fP.v paj_branch over R (R is its first argument after the class context).
   - psrr_branch_tokR: YC1fP.v's Ltac psrr_branch_tok for a BR of the form `paj_branchR .. R`. The tactic applies BR
     to its own binders W E ss ms _ _ c a b HS, and paj_branchR R has those binders in that order, so the body is
     psrr_branch_tok's.
  - SRr'_ret / SRr'_bind / SRr'_mono: YA0nH's SRrG_ret / SRrG_bind / SRrG_mono at R := wle' segs RZ, any zone RZ.
  - SRrG_wf / SRrG_loop / SRrG_loopZ: YA0n.v SRr_wf / SRr_loop / SRr_loopZ over R, with SRrG_bind / SRrG_ret for
    SRr_bind / SRr_ret; R and its two laws (reflexive, transitive) are the first arguments after segs, then the plain
    lemma's binders (SRr_wf's order relation is named Ro here). SRr'_wf / SRr'_loop / SRr'_loopZ are their instances
    at R := wle' segs RZ, any zone RZ.
  The lift from SRr is YA0nH.SRr_SRrG (any R that contains wle) and YA0nH.SRr_SRr' (at wle'). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Wellfounded.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn
YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YK05 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section e.
Variable segs : list Segment.
Variable R : world segs -> world segs -> Prop.
Hypothesis Hwx : wx_segs_nowrap segs.
Local Notation AIw W md := (AI segs (w_H W) (w_A W) md).
(* YA0n.v SRr_step over R *)
Lemma SRrG_step : forall W ms msr' model Q,
ms_svc_pending ms = None ->
RiscvSemantics.step segs (restrict (w_H W) ms) = MachineOk msr' ->
(forall model', same_but_materialized model model' ->
SRrG segs R W (mkCfg (unrestrict (w_H W) (ms_mem ms) msr') model') Q) ->
SRrG segs R W (mkCfg ms model) Q.
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
(* YA0n.v SRr_msteps over R *)
Lemma SRrG_msteps : forall W ms msr' model Q,
msteps segs (restrict (w_H W) ms) msr' ->
(forall model', same_but_materialized model model' ->
hclean (w_H W) msr' ->
SRrG segs R W (mkCfg (unrestrict (w_H W) (ms_mem ms) msr') model') Q) ->
SRrG segs R W (mkCfg ms model) Q.
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
End e.
Section g.
Context {L : ptable asym} {PL : PAListing L} {PI : PAImg L}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation VAL := (pa_val).
(* YC1fP.v paj_branch over R *)
Lemma paj_branchR : forall (R : world SEGS -> world SEGS -> Prop) W E ss ms md Q c a b,
st_ok_pi SEGS VAL E ss (restrict (w_H W) ms) ->
(branch_taken c (sv_denot E a) (sv_denot E b) = true -> st_ok_pi SEGS VAL E (add_cond ss (mkAC c a b)) (restrict (w_H W) ms) -> SRrG SEGS R W (mkCfg ms md) Q) ->
(branch_taken c (sv_denot E a) (sv_denot E b) = false -> st_ok_pi SEGS VAL E (add_cond ss (mkAC (neg_bc c) a b)) (restrict (w_H W) ms) -> SRrG SEGS R W (mkCfg ms md) Q) ->
SRrG SEGS R W (mkCfg ms md) Q.
Proof.
intros R W E ss ms md Q c a b HS HT HF. unfold st_ok_pi in HS, HT, HF.
destruct (branch_taken c (sv_denot E a) (sv_denot E b)) eqn:Hb.
- apply HT; [reflexivity|]. destruct ss. exact (st_ok_add_cond SEGS _ _ _ c a b HS Hb).
- apply HF; [reflexivity|]. destruct ss. exact (st_ok_add_cond_neg SEGS _ _ _ c a b HS Hb).
Qed.
End g.
Section w.
Variable segs : list Segment.
(* YA0n.v SRr_wf over R *)
Lemma SRrG_wf : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
(forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
forall (X : Type) (Ro : X -> X -> Prop),
well_founded Ro ->
forall (P : X -> world segs -> config -> Prop) (Q : world segs -> config -> Prop),
(forall x W c, P x W c -> SRrG segs R W c (fun W' c' => Q W' c' \/ exists x', Ro x' x /\ P x' W' c')) ->
forall x W c, P x W c -> SRrG segs R W c Q.
Proof.
intros R Rr Rt X Ro Hwf P Q Hbody x.
induction (Hwf x) as [x _ IH].
intros W c HP. eapply (SRrG_bind segs R Rt); [apply Hbody, HP|].
intros W' c' _ [HQ | (x' & HR & HP')].
- apply (SRrG_ret segs R Rr), HQ.
- apply (IH x' HR W' c' HP').
Qed.
(* YA0n.v SRr_loop over R *)
Lemma SRrG_loop : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
(forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
forall (X : Type) (m : X -> nat)
(P : X -> world segs -> config -> Prop) (Q : world segs -> config -> Prop),
(forall x W c, P x W c -> SRrG segs R W c (fun W' c' => Q W' c' \/ exists x', (m x' < m x)%nat /\ P x' W' c')) ->
forall x W c, P x W c -> SRrG segs R W c Q.
Proof.
intros R Rr Rt X m P Q Hbody.
apply (SRrG_wf R Rr Rt X (fun a b => (m a < m b)%nat)).
- apply (wf_inverse_image X nat _ m), PeanoNat.Nat.lt_wf_0.
- exact Hbody.
Qed.
(* YA0n.v SRr_loopZ over R *)
Lemma SRrG_loopZ : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
(forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
forall (X : Type) (m : X -> Z)
(P : X -> world segs -> config -> Prop) (Q : world segs -> config -> Prop),
(forall x W c, P x W c -> SRrG segs R W c (fun W' c' => Q W' c' \/ exists x', (0 <= m x' < m x)%Z /\ P x' W' c')) ->
forall x W c, P x W c -> SRrG segs R W c Q.
Proof.
intros R Rr Rt X m P Q Hbody.
apply (SRrG_wf R Rr Rt X (fun a b => (0 <= m a < m b)%Z)).
- apply (wf_inverse_image X Z (fun x y => (0 <= x < y)%Z) m). apply Z.lt_wf with (z := 0%Z).
- exact Hbody.
Qed.
End w.
Section f.
Variable segs : list Segment.
Variable RZ : Z -> Prop.
Lemma SRr'_ret : forall W c (Q : world segs -> config -> Prop), Q W c -> SRr' segs RZ W c Q.
Proof. exact (SRrG_ret segs (wle' segs RZ) (wle'_refl segs RZ)). Qed.
Lemma SRr'_bind : forall W c (P Q : world segs -> config -> Prop),
SRr' segs RZ W c P -> (forall W' c', wle' segs RZ W W' -> P W' c' -> SRr' segs RZ W' c' Q) -> SRr' segs RZ W c Q.
Proof. exact (SRrG_bind segs (wle' segs RZ) (wle'_trans segs RZ)). Qed.
Lemma SRr'_mono : forall W c (Q Q' : world segs -> config -> Prop),
SRr' segs RZ W c Q -> (forall W' c', wle' segs RZ W W' -> Q W' c' -> Q' W' c') -> SRr' segs RZ W c Q'.
Proof. exact (SRrG_mono segs (wle' segs RZ)). Qed.
Lemma SRr'_wf : forall (X : Type) (R : X -> X -> Prop),
well_founded R ->
forall (P : X -> world segs -> config -> Prop) (Q : world segs -> config -> Prop),
(forall x W c, P x W c -> SRr' segs RZ W c (fun W' c' => Q W' c' \/ exists x', R x' x /\ P x' W' c')) ->
forall x W c, P x W c -> SRr' segs RZ W c Q.
Proof. exact (SRrG_wf segs (wle' segs RZ) (wle'_refl segs RZ) (wle'_trans segs RZ)). Qed.
Lemma SRr'_loop : forall (X : Type) (m : X -> nat)
(P : X -> world segs -> config -> Prop) (Q : world segs -> config -> Prop),
(forall x W c, P x W c -> SRr' segs RZ W c (fun W' c' => Q W' c' \/ exists x', (m x' < m x)%nat /\ P x' W' c')) ->
forall x W c, P x W c -> SRr' segs RZ W c Q.
Proof. exact (SRrG_loop segs (wle' segs RZ) (wle'_refl segs RZ) (wle'_trans segs RZ)). Qed.
Lemma SRr'_loopZ : forall (X : Type) (m : X -> Z)
(P : X -> world segs -> config -> Prop) (Q : world segs -> config -> Prop),
(forall x W c, P x W c -> SRr' segs RZ W c (fun W' c' => Q W' c' \/ exists x', (0 <= m x' < m x)%Z /\ P x' W' c')) ->
forall x W c, P x W c -> SRr' segs RZ W c Q.
Proof. exact (SRrG_loopZ segs (wle' segs RZ) (wle'_refl segs RZ) (wle'_trans segs RZ)). Qed.
End f.
End d.
Ltac psrr_branch_tokR RUN BR HS SHOK Bspan := psrr_branch_tok RUN BR HS SHOK Bspan.
