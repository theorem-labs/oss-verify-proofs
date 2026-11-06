(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import LiaTuning ITree Nodes Decode Ceiling VmGap.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.LZ Require Import ITreeLZ NodesLZ.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAA Require Import AEnv ADepot ALayout PEnv ASec LJ ALinkPg ALinkVm ALink.
Import ListNotations.
Open Scope Z_scope.

Section S.
Context {HC : HasCeiling}.
Variable Bs : vmbase.

#[using="Type"] Lemma link_base_entry : forall v mo e, LINK Bs v mo -> In e (vb_maps Bs) -> In e (vm_maps (m_vmmaps mo)).
Proof.
  intros v mo e LK Hin. eapply Permutation_in; [apply Permutation_sym; exact (lk_maps Bs v mo LK)|].
  apply in_or_app. right. exact Hin.
Qed.

#[using="Type"] Lemma link_chunks_in_maps : forall v mo, LINK Bs v mo ->
  Forall (fun c => exists e, In e (vm_maps (m_vmmaps mo)) /\ vlo e <= fst c /\ fst c + snd c <= vhi e) (va_chunks v).
Proof.
  intros v mo LK. pose proof (lk_sane Bs v mo LK) as SANE. unfold chunks_sane in SANE.
  apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) SANE c Hc) as CS.
  exists (sc_ent c). split.
  - eapply Permutation_in; [apply Permutation_sym; exact (lk_maps Bs v mo LK)|]. apply in_or_app. left. apply in_map. exact Hc.
  - destruct (sc_ent_unsigned c CS) as [E1 E2]. unfold vhi, vlo, vsz. rewrite E1, E2. lia.
Qed.

#[using="Type"] Lemma link_base_ranges : forall v mo (R : list (Z * Z)), LINK Bs v mo ->
  Forall (fun rg => exists e, In e (vb_maps Bs) /\ vlo e <= fst rg /\ fst rg + snd rg <= vhi e) R ->
  Forall (fun rg => exists e, In e (vm_maps (m_vmmaps mo)) /\ vlo e <= fst rg /\ fst rg + snd rg <= vhi e) R.
Proof.
  intros v mo R LK HR. eapply Forall_impl; [| exact HR]. intros rg (e & Hin & H1 & H2).
  exists e. split; [exact (link_base_entry v mo e LK Hin)| split; assumption].
Qed.

#[using="Type"] Lemma link_avoid_ok : forall v mo (lo q : Z) (R : list (Z * Z)), LINK Bs v mo -> alloc_ceiling <= lo ->
  Forall (fun rg => exists e, In e (vb_maps Bs) /\ vlo e <= fst rg /\ fst rg + snd rg <= vhi e) R ->
  avoid_ok mo ((lo, q) :: map (fun rg => (fst rg, fst rg + snd rg)) R ++ map (fun c => (fst c, fst c + snd c)) (va_chunks v)).
Proof.
  intros v mo lo q R LK CLO HR. unfold avoid_ok. apply Forall_cons; [left; exact CLO|].
  apply Forall_app. split.
  - apply Forall_map. eapply Forall_impl; [| exact (link_base_ranges v mo R LK HR)].
    intros rg (e & Hin & H1 & H2). right. exists e. cbn [fst snd]. split; [exact Hin| split; assumption].
  - apply Forall_map. eapply Forall_impl; [| exact (link_chunks_in_maps v mo LK)].
    intros c (e & Hin & H1 & H2). right. exists e. cbn [fst snd]. split; [exact Hin| split; assumption].
Qed.
End S.
