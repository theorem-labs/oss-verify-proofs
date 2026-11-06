(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.coturn.FuzzStunClient.images Require Import Asan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec StoreOk AgentLib.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AsanDepotMem.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.


(* [comment removed for export] *)
Record dstate := DS {
  d_n : Z;                 (* [comment removed for export] *)
  d_tf : Z;                (* [comment removed for export] *)
  d_st : Z;                (* [comment removed for export] *)
  d_tab : Z -> Z;          (* [comment removed for export] *)
  d_lnk : Z -> Z;          (* [comment removed for export] *)
  d_hsh : Z -> word        (* [comment removed for export] *)
}.

(* [comment removed for export] *)
Definition depot_cells (B P : Z) (d : dstate) (m : word -> option byte) : Prop :=
     (forall b, 0 <= b < 2 ^ 20 -> cell32 m (DEPOT + 4 * b) (d_tab d b) /\ 0 <= d_tab d b <= d_n d)
  /\ cell32 m NIDS (d_n d)
  /\ cell64 m MAP1 B
  /\ (forall id, 1 <= id <= d_n d ->
        rdn SEGS m (Z_to_bv 64 (B + 16 * id)) 8 = Some (word_to_le_bytes 8 (d_hsh d id))
        /\ cell32 m (B + 16 * id + 8) (d_lnk d id) /\ 0 <= d_lnk d id < id)
  /\ cell64 m SSB (d_tf d)
  /\ cell64 m (SSB + 16) P
  /\ cell32 m (SSB + 24) (d_st d)
  /\ 0 <= d_n d /\ 0 <= d_st d /\ 0 <= d_tf d.

(* [comment removed for export] *)
Definition depot_geom (B P ncap fcap : Z) : Prop :=
     IMGHI <= B /\ B + 16 * 2 ^ 16 < 2 ^ 64 /\ 2 <= ncap <= 2 ^ 16
  /\ IMGHI <= P /\ P + 8 * 2 ^ 20 < 2 ^ 64 /\ 257 <= fcap <= 2 ^ 20
  /\ (B + 16 * ncap <= P \/ P + 8 * fcap <= B).

Definition depot_inv (B P ncap fcap k : Z) (m : word -> option byte) : Prop :=
  exists d : dstate,
       depot_cells B P d m
    /\ depot_geom B P ncap fcap
    /\ 0 <= k /\ d_n d + k < ncap /\ d_tf d + 257 * k <= fcap /\ d_st d + 257 * k < 2 ^ 20
    /\ okr m B (16 * ncap) /\ okr m P (8 * fcap).

(* [comment removed for export] *)
Definition depot_foot (B P ncap fcap : Z) (x : Z) : Prop :=
     (DEPOT <= x < MAP1 + 8)
  \/ (B <= x < B + 16 * ncap)
  \/ (SSB <= x < SSB + 28)
  \/ (P <= x < P + 8 * fcap).

Lemma depot_cells_agree : forall B P ncap fcap d m m',
  depot_cells B P d m -> depot_geom B P ncap fcap -> d_n d < ncap ->
  (forall x : word, depot_foot B P ncap fcap (bv_unsigned x) -> m' x = m x) ->
  depot_cells B P d m'.
Proof.
  intros B P ncap fcap d m m' C G Hn AG.
  destruct C as (Ctab & Cn & Cmap & Cnodes & Ctf & CP & Cst & Cr).
  pose proof G as (GB1 & GB2 & GN & GP1 & GP2 & GF & GBP).
  assert (RD : forall a (j : nat), 0 <= a -> a + Z.of_nat j < 2 ^ 64 ->
             (forall x, a <= x < a + Z.of_nat j -> depot_foot B P ncap fcap x) ->
             rdn SEGS m' (Z_to_bv 64 a) j = rdn SEGS m (Z_to_bv 64 a) j).
  { intros a j Ha Hj Hin. apply rdn_ext; [rewrite u64_lit by lia; lia|].
    intros x Hx. rewrite u64_lit in Hx by lia. apply AG. apply Hin. exact Hx. }
  assert (CELL : forall j a v, 0 <= a -> a + Z.of_nat j < 2 ^ 64 ->
             (forall x, a <= x < a + Z.of_nat j -> depot_foot B P ncap fcap x) -> cellN m j a v -> cellN m' j a v).
  { intros j a v Ha Hj Hin [Hc Hv]. split; [|exact Hv]. rewrite (RD a j Ha Hj Hin). exact Hc. }
  unfold depot_foot in *.
  split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]; try exact Cr.
  - intros b Hb. destruct (Ctab b Hb) as [Hc Hr]. split; [|exact Hr]. apply CELL; [lia | cbn; lia | cbn; intros; lia | exact Hc].
  - apply CELL; [lia | cbn; lia | cbn; intros; lia | exact Cn].
  - apply CELL; [lia | cbn; lia | cbn; intros; lia | exact Cmap].
  - intros id Hid. destruct (Cnodes id Hid) as (Hh & Hl & Hr). split; [|split; [|exact Hr]].
    + rewrite (RD (B + 16 * id) 8%nat); [exact Hh | lia | cbn; nia | cbn; intros; right; left; nia].
    + apply CELL; [lia | cbn; nia | cbn; intros; right; left; nia | exact Hl].
  - apply CELL; [lia | cbn; lia | cbn; intros; lia | exact Ctf].
  - apply CELL; [lia | cbn; lia | cbn; intros; lia | exact CP].
  - apply CELL; [lia | cbn; lia | cbn; intros; lia | exact Cst].
Qed.

Lemma depot_inv_weaken : forall B P ncap fcap k k' m,
  depot_inv B P ncap fcap k m -> 0 <= k' <= k -> depot_inv B P ncap fcap k' m.
Proof.
  intros B P ncap fcap k k' m (d & C & G & Hk & Hn & Htf & Hst & OB & OP) Hk'.
  assert (257 * k' <= 257 * k) by nia.
  exists d. split; [exact C|]. split; [exact G|]. repeat split; try assumption; lia.
Qed.

Lemma depot_inv_agree : forall B P ncap fcap k m m',
  depot_inv B P ncap fcap k m ->
  (forall x : word, depot_foot B P ncap fcap (bv_unsigned x) -> m' x = m x) ->
  mem_grows m m' ->
  depot_inv B P ncap fcap k m'.
Proof.
  intros B P ncap fcap k m m' (d & C & G & Hk & Hn & Htf & Hst & OB & OP) AG GR.
  exists d. split; [eapply depot_cells_agree; [exact C | exact G | lia | exact AG]|].
  split; [exact G|]. split; [exact Hk|]. split; [exact Hn|]. split; [exact Htf|]. split; [exact Hst|].
  split; eapply okr_grows; eassumption.
Qed.
