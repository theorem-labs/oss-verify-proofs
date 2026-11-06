(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAA Require Import AEnv ADepot.
Import ListNotations.
Open Scope Z_scope.

Notation A0_IMAGE_END := 6328320%Z.
Notation HIGHMEM := 17594333495296%Z.
Notation K_SPACE := 137438953472%Z.

Record alayout := mkAL {
  al_space : Z;
  al_parr : Z;
  al_thread : athread;
  al_fsb : Z;
  al_depot : dlayout;
  al_dtls : Z
}.

Definition apart (a s b t : Z) : Prop := a + s <= b \/ b + t <= a.

Section L.
Context {HC : HasCeiling}.
Variable L : alayout.

Definition al_regions : list (Z * Z) :=
  [ (al_space L, K_SPACE + 4096); (al_parr L, 2^23); (at_ctx (al_thread L), 4096); (at_thr (al_thread L), 4096);
    (al_fsb L, A0_FS_SIZE); (DN0 (al_depot L), 2^20); (SS0 (al_depot L), 2^23); (al_dtls L, 4096) ].

Definition region_ok (r : Z * Z) : Prop :=
  ((0 < fst r /\ fst r + snd r <= 0x10000) \/ (A0_IMAGE_END <= fst r /\ fst r + snd r <= 0x7fff7000) \/ HIGHMEM <= fst r)
  /\ fst r + snd r <= alloc_ceiling /\ fst r mod 4096 = 0.

Definition alayout_ok : Prop :=
  Forall region_ok al_regions
  /\ (forall i j, (i < j)%nat -> (j < 8)%nat ->
        apart (fst (nth i al_regions (0,0))) (snd (nth i al_regions (0,0))) (fst (nth j al_regions (0,0))) (snd (nth j al_regions (0,0))))
  /\ al_space L mod 65536 = 0
  /\ thread_layout_ok (al_thread L)
  /\ dl_ok (al_depot L) /\ SWIN (al_depot L) <= 2^23.

#[using="Type"] Lemma region_facts : forall i, alayout_ok -> (i < 8)%nat ->
  let r := nth i al_regions (0,0) in
  (((0 < fst r /\ fst r + snd r <= 0x10000) \/ (A0_IMAGE_END <= fst r /\ fst r + snd r <= 0x7fff7000) \/ HIGHMEM <= fst r) /\ HIGHMEM <= alloc_ceiling)
  /\ fst r + snd r <= alloc_ceiling /\ fst r mod 4096 = 0 /\ ((0 < fst r /\ fst r + snd r <= 0x10000) \/ A0_IMAGE_END <= fst r) /\ fst r + snd r <= 2^47
  /\ app_mem (fst r) (snd r) /\ (forall a, 0 <= a < 2^47 -> sh a < fst r \/ fst r + snd r <= sh a).
Proof.
  intros i (F & _) Hi r. pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  assert (R : region_ok r). { subst r. apply (proj1 (Forall_nth region_ok al_regions) F). cbn. lia. }
  destruct R as (R1 & R2 & R3). unfold app_mem, sh, SHADOW_OFF.
  split; [split; [exact R1| lia]|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  intros a Ha. Z.div_mod_to_equations. lia.
Qed.

#[using="Type"] Lemma region0_facts : alayout_ok ->
  let r := nth 0 al_regions (0,0) in
  HIGHMEM <= fst r /\ fst r + snd r <= alloc_ceiling /\ fst r mod 4096 = 0 /\ A0_IMAGE_END <= fst r /\ fst r + snd r <= 2^47
  /\ app_mem (fst r) (snd r) /\ (forall a, 0 <= a < 2^47 -> sh a < fst r).
Proof.
  intros (F & _) r. pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  assert (R : region_ok r). { subst r. apply (proj1 (Forall_nth region_ok al_regions) F). cbn. lia. }
  destruct R as (R1 & R2 & R3). subst r. cbn [nth al_regions fst snd] in *. unfold app_mem, sh, SHADOW_OFF.
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [right; lia|].
  intros a Ha. Z.div_mod_to_equations. lia.
Qed.

#[using="Type"] Lemma layout_apart : forall i j, alayout_ok -> (i < j)%nat -> (j < 8)%nat ->
  apart (fst (nth i al_regions (0,0))) (snd (nth i al_regions (0,0))) (fst (nth j al_regions (0,0))) (snd (nth j al_regions (0,0))).
Proof. intros i j (_ & A & _) Hi Hj. apply A; assumption. Qed.
End L.

Ltac layout_facts AO i H :=
  lazymatch i with
  | 0%nat => pose proof (region0_facts _ AO) as H
  | _ => pose proof (region_facts _ i AO ltac:(lia)) as H
  end; cbn [nth al_regions fst snd] in H.
Ltac layout_apart_fact AO i j H :=
  pose proof (layout_apart _ i j AO ltac:(lia) ltac:(lia)) as H; cbn [nth al_regions fst snd apart] in H; unfold apart in H.

Example layout_apart_example {HC : HasCeiling} (L : alayout) (AO : alayout_ok L) :
  at_thr (al_thread L) + 4096 <= DN0 (al_depot L) \/ DN0 (al_depot L) + 2^20 <= at_thr (al_thread L).
Proof. layout_apart_fact AO 3%nat 5%nat H. exact H. Qed.
Example layout_facts_example {HC : HasCeiling} (L : alayout) (AO : alayout_ok L) : HIGHMEM <= al_space L /\ al_fsb L + A0_FS_SIZE <= alloc_ceiling.
Proof. layout_facts AO 0%nat H0. layout_facts AO 4%nat H. destruct H0 as (H1 & _). destruct H as (_ & H2 & _). split; assumption. Qed.
