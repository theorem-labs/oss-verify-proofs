(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import PropExec MState Mem Exec Cells Step Frame Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import Realize SafeReach AllocIF.
Import ListNotations.
Local Open Scope Z_scope.

Section S.
Context {HC : HasCeiling}.
Variable segs : list Segment.
Variable AI : alloc_if segs.

Let PS := ai_PS segs AI.
Let BL := list (block (ai_K segs AI)).

Definition linked (s0 : PS) (mo0 : Model) (Q : PS -> BL -> machine_state -> Prop) (c : config) : Prop :=
  exists s' LB', LINK segs AI s' LB' (cfg_model c) /\ ai_keep segs AI s0 s' /\ ai_mrel segs AI mo0 (cfg_model c)
                 /\ Q s' LB' (cfg_ms c).

Definition SREACH (Q : PS -> BL -> machine_state -> Prop) (ms : machine_state) (s : PS) (LB : BL) : Prop :=
  forall mo, LINK segs AI s LB mo -> safe_reach segs (linked s mo Q) (mkCfg ms mo).

#[using="Type"] Lemma sreach_ret : forall (Q : PS -> BL -> machine_state -> Prop) ms s LB,
  Q s LB ms -> SREACH Q ms s LB.
Proof.
  intros Q ms s LB H mo HL. apply sr_done. exists s, LB. split; [exact HL|].
  split; [apply ai_keep_refl|]. split; [apply ai_mrel_refl| exact H].
Qed.

#[using="Type"] Lemma sreach_mono : forall (P Q : PS -> BL -> machine_state -> Prop) ms s LB,
  SREACH P ms s LB -> (forall s' LB' ms', P s' LB' ms' -> Q s' LB' ms') -> SREACH Q ms s LB.
Proof.
  intros P Q ms s LB H K mo HL. eapply sr_mono; [exact (H mo HL)|].
  intros c' (s' & LB' & HL' & HK & HM & HP). exists s', LB'. auto 6.
Qed.

#[using="Type"] Lemma sreach_mono_keep : forall (P Q : PS -> BL -> machine_state -> Prop) ms s LB,
  SREACH P ms s LB -> (forall s' LB' ms', ai_keep segs AI s s' -> P s' LB' ms' -> Q s' LB' ms') -> SREACH Q ms s LB.
Proof.
  intros P Q ms s LB H K mo HL. eapply sr_mono; [exact (H mo HL)|].
  intros c' (s' & LB' & HL' & HK & HM & HP). exists s', LB'. auto 6.
Qed.

#[using="Type"] Lemma sreach_bind : forall (P Q : PS -> BL -> machine_state -> Prop) ms s LB,
  SREACH P ms s LB ->
  (forall s' LB' ms', P s' LB' ms' -> SREACH Q ms' s' LB') ->
  SREACH Q ms s LB.
Proof.
  intros P Q ms s LB H K mo HL. eapply sr_bind; [exact (H mo HL)|].
  intros [ms' mo'] (s' & LB' & HL' & HK & HM & HP). cbn in *.
  eapply sr_mono; [exact (K s' LB' ms' HP mo' HL')|].
  intros c'' (s'' & LB'' & HL'' & HK' & HM' & HQ). exists s'', LB''. split; [exact HL''|]. split; [| split; [|exact HQ]].
  - eapply ai_keep_trans; eauto.
  - eapply ai_mrel_trans; eauto.
Qed.

#[using="Type"] Lemma sreach_evt : forall (P : machine_state -> Prop) (Q : PS -> BL -> machine_state -> Prop) ms s LB,
  evt segs P ms ->
  (forall ms', P ms' -> SREACH Q ms' s LB) ->
  SREACH Q ms s LB.
Proof.
  intros P Q ms s LB (ms' & Hs & HP) K mo HL.
  destruct (ai_link_frame segs AI s LB mo HL) as [Hh Hlz].
  revert HL. induction Hs; intros HL.
  - exact (K _ HP mo HL).
  - destruct H as [Hsvc Hst]. eapply sr_step; eauto.
Qed.

#[using="Type"] Lemma sreach_of_evt : forall (P : machine_state -> Prop) ms s LB,
  evt segs P ms -> SREACH (fun s' LB' ms' => s' = s /\ LB' = LB /\ P ms') ms s LB.
Proof.
  intros P ms s LB H. eapply sreach_evt; [exact H|]. intros ms' HP. apply sreach_ret. auto.
Qed.

#[using="Type"] Lemma sreach_eq : forall Q ms ms' s LB, ms = ms' -> SREACH Q ms' s LB -> SREACH Q ms s LB.
Proof. intros; subst; assumption. Qed.

#[using="Type"] Lemma sreach_perm : forall Q ms s LB LB',
  Permutation.Permutation LB LB' -> SREACH Q ms s LB' -> SREACH Q ms s LB.
Proof.
  intros Q ms s LB LB' HP H mo HL. apply H. eapply ai_link_perm; eauto.
Qed.

End S.

Arguments linked {HC segs} AI s0 mo0 Q c.
Arguments SREACH {HC segs} AI Q ms s LB.
