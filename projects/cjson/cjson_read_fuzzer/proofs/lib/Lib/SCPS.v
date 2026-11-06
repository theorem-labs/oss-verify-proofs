(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import MState Mem Exec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.

Section WithSegs.
Variable segs : list Segment.

Definition MOK (mo : Model) : Prop := m_halted mo = None /\ m_vm_lazy mo = [].

(* [comment removed for export] *)

Lemma rz_rt_msteps : forall ms ms' mo T,
  MOK mo ->
  Exec.msteps segs ms ms' ->
  realizes segs (mkCfg ms' mo) T ->
  realizes segs (mkCfg ms mo) T.
Proof.
  intros ms ms' mo T [Hh Hl] Hms.
  induction Hms as [ms | ms ms1 ms2 [Hsvc Hstep] Hms IH]; intro Hc; [exact Hc|].
  eapply rz_step; [exact Hh | exact Hl | exact Hsvc | exact Hstep | apply IH; exact Hc].
Qed.

Lemma rz_evt : forall (Q : machine_state -> Prop) ms mo T,
  MOK mo ->
  evt segs Q ms ->
  (forall ms', Q ms' -> realizes segs (mkCfg ms' mo) T) ->
  realizes segs (mkCfg ms mo) T.
Proof.
  intros Q ms mo T HM (ms' & Hms & HQ) K.
  eapply rz_rt_msteps; [exact HM | exact Hms | apply K; exact HQ].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition vm_only (mo mo' : Model) : Prop :=
  m_fd mo' = m_fd mo /\ m_io mo' = m_io mo /\ m_fsys mo' = m_fsys mo /\ m_proc mo' = m_proc mo /\
  m_lim mo' = m_lim mo /\ m_time mo' = m_time mo.

Lemma vm_only_refl : forall mo, vm_only mo mo.
Proof. intros; repeat split; reflexivity. Qed.

Lemma vm_only_trans : forall a b c, vm_only a b -> vm_only b c -> vm_only a c.
Proof.
  intros a b c (A1 & A2 & A3 & A4 & A5 & A6) (B1 & B2 & B3 & B4 & B5 & B6).
  unfold vm_only. rewrite B1, B2, B3, B4, B5, B6. repeat split; assumption.
Qed.

Lemma vm_only_facts : forall mo mo', vm_only mo mo' ->
  m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo /\ m_halted mo' = m_halted mo /\
  m_tid mo' = m_tid mo /\ m_stdin mo' = m_stdin mo.
Proof.
  intros mo mo' (H1 & H2 & H3 & H4 & _). unfold m_fds, m_fs, m_halted, m_tid, m_stdin.
  rewrite H1, H2, H3, H4. repeat split; reflexivity.
Qed.

(* [comment removed for export] *)
Definition SCPS (P : machine_state -> Model -> Prop) (ms : machine_state) (mo : Model) : Prop :=
  forall T : TSet,
    (forall ms' mo', P ms' mo' -> vm_only mo mo' -> realizes segs (mkCfg ms' mo') T) ->
    realizes segs (mkCfg ms mo) T.

Lemma scps_done : forall (P : machine_state -> Model -> Prop) ms mo,
  P ms mo -> SCPS P ms mo.
Proof. intros P ms mo HP T K. apply K; [exact HP | apply vm_only_refl]. Qed.

Lemma scps_mono : forall (P Q : machine_state -> Model -> Prop) ms mo,
  SCPS P ms mo -> (forall ms' mo', P ms' mo' -> Q ms' mo') -> SCPS Q ms mo.
Proof. intros P Q ms mo H HPQ T K. apply H. intros ms' mo' HP HV. apply K; [apply HPQ, HP | exact HV]. Qed.

(* [comment removed for export] *)
Lemma scps_vm_only : forall (P : machine_state -> Model -> Prop) ms mo,
  SCPS P ms mo -> SCPS (fun ms' mo' => P ms' mo' /\ vm_only mo mo') ms mo.
Proof. intros P ms mo H T K. apply H. intros ms' mo' HP HV. apply K; [split; assumption | exact HV]. Qed.

(* [comment removed for export] *)
Lemma scps_bind : forall (P Q : machine_state -> Model -> Prop) ms mo,
  SCPS P ms mo -> (forall ms' mo', P ms' mo' -> SCPS Q ms' mo') -> SCPS Q ms mo.
Proof.
  intros P Q ms mo H K T HK. apply H. intros ms' mo' HP HV. apply (K ms' mo' HP).
  intros ms2 mo2 HQ HV2. apply HK; [exact HQ | eapply vm_only_trans; eassumption].
Qed.

(* [comment removed for export] *)
Lemma scps_evt : forall (Q : machine_state -> Prop) ms mo,
  MOK mo -> evt segs Q ms -> SCPS (fun ms' mo' => Q ms' /\ mo' = mo) ms mo.
Proof.
  intros Q ms mo HM He T K. eapply rz_evt; [exact HM | exact He |].
  intros ms' HQ. apply K; [split; [exact HQ | reflexivity] | apply vm_only_refl].
Qed.

(* [comment removed for export] *)
Lemma scps_evt_then : forall (Q : machine_state -> Prop) (P : machine_state -> Model -> Prop) ms mo,
  MOK mo -> evt segs Q ms -> (forall ms', Q ms' -> SCPS P ms' mo) -> SCPS P ms mo.
Proof.
  intros Q P ms mo HM He K. eapply scps_bind; [apply scps_evt; [exact HM | exact He] |].
  intros ms' mo' [HQ ->]. apply K. exact HQ.
Qed.

(* [comment removed for export] *)
Lemma scps_eq : forall P ms ms' mo, ms = ms' -> SCPS P ms' mo -> SCPS P ms mo.
Proof. intros; subst; assumption. Qed.

(* [comment removed for export] *)
Lemma scps_realizes : forall (P : machine_state -> Model -> Prop) ms mo T,
  SCPS P ms mo ->
  (forall ms' mo', P ms' mo' -> vm_only mo mo' -> realizes segs (mkCfg ms' mo') T) ->
  realizes segs (mkCfg ms mo) T.
Proof. intros P ms mo T H K. apply H. exact K. Qed.

End WithSegs.

Arguments MOK mo /.
Arguments vm_only mo mo' /.
