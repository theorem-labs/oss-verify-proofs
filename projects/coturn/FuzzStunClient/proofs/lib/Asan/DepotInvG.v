(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec StoreOk AgentLib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section WithSegs.
  Variable segs : list Segment.

  (* [comment removed for export] *)
  Definition cellG (m : word -> option byte) (n : nat) (a v : Z) : Prop :=
    rdn segs m (Z_to_bv 64 a) n = Some (word_to_le_bytes n (Z_to_bv 64 v)) /\ 0 <= v < 2 ^ (8 * Z.of_nat n).

  (* [comment removed for export] *)
  Definition okrG (m : word -> option byte) (a n : Z) : Prop :=
    forall j, 0 <= j < n -> store_ok segs m (Z_to_bv 64 (a + j)) 1 = true.

  Lemma okrG_sub : forall m a n a' n', okrG m a n -> a <= a' -> a' + n' <= a + n -> okrG m a' n'.
  Proof. intros m a n a' n' H H1 H2 j Hj. replace (a' + j) with (a + (a' - a + j)) by lia. apply H. lia. Qed.

  Lemma okrG_grows : forall m m' a n, mem_grows m m' -> okrG m a n -> okrG m' a n.
  Proof. intros m m' a n G H j Hj. eapply store_ok_mono; [exact G | apply H; exact Hj]. Qed.

  (* [comment removed for export] *)
  Definition avail (m : word -> option byte) (x : word) : Prop :=
    m x <> None \/ find_segment segs (bv_unsigned x) 1 <> None.

  Lemma store_ok_avail : forall m x, store_ok segs m x 1 = true -> avail m x.
  Proof.
    intros m x H. cbn [store_ok] in H. unfold wview in H. unfold avail.
    destruct (m x); [left; discriminate|]. right.
    destruct (find_segment segs (bv_unsigned x) 1); [discriminate | discriminate].
  Qed.

  Lemma rdn_avail : forall k m (a : word) bs, rdn segs m a k = Some bs ->
    forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat k -> avail m x.
  Proof.
    induction k as [|k IH]; intros m a bs H x Hx; [lia|].
    cbn [rdn] in H. destruct (Z.eq_dec (bv_unsigned x) (bv_unsigned a)) as [Heq|Hne].
    - assert (x = a) by (apply bv_eq; exact Heq). subst x. unfold avail.
      destruct (m a) eqn:Ema; [left; congruence|]. right. unfold seg_rom, memory_read in H.
      change (Z.of_N 1) with 1%Z in H.
      destruct (find_segment segs (bv_unsigned a) 1); [discriminate | cbn in H; discriminate].
    - destruct (match m a with Some b => Some b | None => seg_rom segs a end); [|discriminate].
      destruct (rdn segs m (a + 1)%bv k) as [rest|] eqn:Hr; [|discriminate].
      pose proof (u64_range x). pose proof (u64_range a).
      assert (Hu1 : bv_unsigned (a + 1)%bv = bv_unsigned a + 1) by (apply u_add1; lia).
      eapply (IH m (a + 1)%bv rest Hr). rewrite Hu1. lia.
  Qed.

  Lemma okrG_agree : forall m m' a n, 0 <= a -> a + n < 2 ^ 64 ->
    (forall x : word, a <= bv_unsigned x < a + n -> avail m x -> m' x = m x) -> okrG m a n -> okrG m' a n.
  Proof.
    intros m m' a n Ha Hn AG H j Hj. pose proof (H j Hj) as S. pose proof (store_ok_avail _ _ S) as AV.
    cbn [store_ok] in *. unfold wview in *.
    rewrite AG; [exact S | rewrite u64_lit by lia; lia | exact AV].
  Qed.

  (* [comment removed for export] *)
  Record dstate := DS {
    d_n : Z;                 (* [comment removed for export] *)
    d_tf : Z;                (* [comment removed for export] *)
    d_st : Z;                (* [comment removed for export] *)
    d_tab : Z -> Z;          (* [comment removed for export] *)
    d_lnk : Z -> Z;          (* [comment removed for export] *)
    d_hsh : Z -> word        (* [comment removed for export] *)
  }.

  Variables (depot ssb imghi : Z).

  Definition depot_cellsG (B P : Z) (d : dstate) (m : word -> option byte) : Prop :=
       (forall b, 0 <= b < 2 ^ 20 -> cellG m 4 (depot + 4 * b) (d_tab d b) /\ 0 <= d_tab d b <= d_n d)
    /\ cellG m 4 (depot + 4194304) (d_n d)
    /\ cellG m 8 (depot + 4194320) B
    /\ (forall id, 1 <= id <= d_n d ->
          rdn segs m (Z_to_bv 64 (B + 16 * id)) 8 = Some (word_to_le_bytes 8 (d_hsh d id))
          /\ cellG m 4 (B + 16 * id + 8) (d_lnk d id) /\ 0 <= d_lnk d id < id)
    /\ cellG m 8 ssb (d_tf d)
    /\ cellG m 8 (ssb + 16) P
    /\ cellG m 4 (ssb + 24) (d_st d)
    /\ 0 <= d_n d /\ 0 <= d_st d /\ 0 <= d_tf d.

  Definition depot_geomG (B P ncap fcap : Z) : Prop :=
       imghi <= B /\ B + 16 * 2 ^ 16 < 2 ^ 64 /\ 2 <= ncap <= 2 ^ 16
    /\ imghi <= P /\ P + 8 * 2 ^ 20 < 2 ^ 64 /\ 257 <= fcap <= 2 ^ 20
    /\ (B + 16 * ncap <= P \/ P + 8 * fcap <= B)
    /\ 2 ^ 16 <= depot /\ depot + 4194328 <= imghi /\ 2 ^ 16 <= ssb /\ ssb + 28 <= imghi /\ imghi < 2 ^ 32
    /\ (depot + 4194328 <= ssb \/ ssb + 28 <= depot).

  Definition depot_invG (B P ncap fcap k : Z) (m : word -> option byte) : Prop :=
    exists d : dstate,
         depot_cellsG B P d m
      /\ depot_geomG B P ncap fcap
      /\ 0 <= k /\ d_n d + k < ncap /\ d_tf d + 257 * k <= fcap /\ d_st d + 257 * k < 2 ^ 20
      /\ okrG m B (16 * ncap) /\ okrG m P (8 * fcap).

  (* [comment removed for export] *)
  Definition depot_footG (B P ncap fcap : Z) (x : Z) : Prop :=
       (depot <= x < depot + 4194328)
    \/ (B <= x < B + 16 * ncap)
    \/ (ssb <= x < ssb + 28)
    \/ (P <= x < P + 8 * fcap).

  Lemma depot_cellsG_agree : forall B P ncap fcap d m m',
    depot_cellsG B P d m -> depot_geomG B P ncap fcap -> d_n d < ncap ->
    (forall x : word, depot_footG B P ncap fcap (bv_unsigned x) -> avail m x -> m' x = m x) ->
    depot_cellsG B P d m'.
  Proof.
    intros B P ncap fcap d m m' C G Hn AG.
    destruct C as (Ctab & Cn & Cmap & Cnodes & Ctf & CP & Cst & Cr).
    pose proof G as (GB1 & GB2 & GN & GP1 & GP2 & GF & GBP & GL).
    assert (RD : forall a (j : nat) bs, 0 <= a -> a + Z.of_nat j < 2 ^ 64 ->
               (forall x, a <= x < a + Z.of_nat j -> depot_footG B P ncap fcap x) ->
               rdn segs m (Z_to_bv 64 a) j = Some bs -> rdn segs m' (Z_to_bv 64 a) j = Some bs).
    { intros a j bs Ha Hj Hin Hr. rewrite <- Hr. apply rdn_ext; [rewrite u64_lit by lia; lia|].
      intros x Hx. rewrite u64_lit in Hx by lia. apply AG; [apply Hin; exact Hx|].
      eapply rdn_avail; [exact Hr|]. rewrite u64_lit by lia. exact Hx. }
    assert (CELL : forall j a v, 0 <= a -> a + Z.of_nat j < 2 ^ 64 ->
               (forall x, a <= x < a + Z.of_nat j -> depot_footG B P ncap fcap x) -> cellG m j a v -> cellG m' j a v).
    { intros j a v Ha Hj Hin [Hc Hv]. split; [|exact Hv]. exact (RD a j _ Ha Hj Hin Hc). }
    unfold depot_footG in *.
    split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]; try exact Cr.
    - intros b Hb. destruct (Ctab b Hb) as [Hc Hr]. split; [|exact Hr]. apply CELL; [lia | cbn; lia | cbn; intros; lia | exact Hc].
    - apply CELL; [lia | cbn; lia | cbn; intros; lia | exact Cn].
    - apply CELL; [lia | cbn; lia | cbn; intros; lia | exact Cmap].
    - intros id Hid. destruct (Cnodes id Hid) as (Hh & Hl & Hr). split; [|split; [|exact Hr]].
      + apply (RD (B + 16 * id) 8%nat); [lia | cbn; nia | cbn; intros; right; left; nia | exact Hh].
      + apply CELL; [lia | cbn; nia | cbn; intros; right; left; nia | exact Hl].
    - apply CELL; [lia | cbn; lia | cbn; intros; lia | exact Ctf].
    - apply CELL; [lia | cbn; lia | cbn; intros; lia | exact CP].
    - apply CELL; [lia | cbn; lia | cbn; intros; lia | exact Cst].
  Qed.

  Lemma depot_invG_weaken : forall B P ncap fcap k k' m,
    depot_invG B P ncap fcap k m -> 0 <= k' <= k -> depot_invG B P ncap fcap k' m.
  Proof.
    intros B P ncap fcap k k' m (d & C & G & Hk & Hn & Htf & Hst & OB & OP) Hk'.
    assert (257 * k' <= 257 * k) by nia.
    exists d. split; [exact C|]. split; [exact G|]. repeat split; try assumption; lia.
  Qed.

  Lemma depot_invG_agree : forall B P ncap fcap k m m',
    depot_invG B P ncap fcap k m ->
    (forall x : word, depot_footG B P ncap fcap (bv_unsigned x) -> avail m x -> m' x = m x) ->
    depot_invG B P ncap fcap k m'.
  Proof.
    intros B P ncap fcap k m m' (d & C & G & Hk & Hn & Htf & Hst & OB & OP) AG.
    pose proof G as (GB1 & GB2 & GN & GP1 & GP2 & GF & GBP & GL).
    exists d. split; [eapply depot_cellsG_agree; [exact C | exact G | lia | exact AG]|].
    split; [exact G|]. split; [exact Hk|]. split; [exact Hn|]. split; [exact Htf|]. split; [exact Hst|].
    unfold depot_footG in AG.
    split.
    - apply (okrG_agree m m' B (16 * ncap)); [lia | nia | | exact OB]. intros x Hx Ha. apply AG; [lia | exact Ha].
    - apply (okrG_agree m m' P (8 * fcap)); [lia | nia | | exact OP]. intros x Hx Ha. apply AG; [lia | exact Ha].
  Qed.

  Lemma depot_invG_pos : forall B P ncap fcap k m, depot_invG B P ncap fcap k m -> 0 <= k.
  Proof. intros B P ncap fcap k m (d & _ & _ & Hk & _). exact Hk. Qed.
End WithSegs.
