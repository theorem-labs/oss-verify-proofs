(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge Frame Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAA Require Import AEnv ALayout APrim ACells AQuar AHeap AAllocCarve.
Import ListNotations.
Open Scope Z_scope.

Section CARVES.
  Context {HC : HasCeiling}.

  #[using="Type"] Lemma cb_join : forall (m : mem) A (a b : nat) x y,
    rw_cells asegs m A [CB a x] -> rw_cells asegs m (A + Z.of_nat a) [CB b y] -> rw_cells asegs m A [CB (a + b) (x ++ y)].
  Proof.
    intros m A a b x y HX HY.
    assert (LX : length x = a) by (destruct HX as [[WF _] _]; cbn in WF; destruct WF as (W0 & _); exact W0).
    assert (LY : length y = b) by (destruct HY as [[WF _] _]; cbn in WF; destruct WF as (W0 & _); exact W0).
    assert (HXY : rw_cells asegs m A ([CB a x] ++ [CB b y])).
    { apply rw_cells_app. split; [exact HX|]. cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r. exact HY. }
    eapply rw_cells_rebytes; [exact HXY| | |].
    - cbn. rewrite length_app, LX, LY. tauto.
    - cbn. rewrite !app_nil_r. reflexivity.
    - cbn. lia.
  Qed.

  #[using="Type"] Lemma carve_map : forall (m : mem) B bs rz n jb js,
    0 <= B -> B mod 8 = 0 -> bs mod 8 = 0 -> 16 <= rz -> rz mod 16 = 0 -> 1 <= n -> rz + rup8 n <= bs ->
    rw_cells asegs m B [CB (Z.to_nat bs) jb] ->
    rw_cells asegs m (sh B) [CB (Z.to_nat (bs / 8)) js] ->
    (exists j0, rw_cells asegs m B [CB (Z.to_nat (rz - 16)) j0])
    /\ (exists b0 b1 j2 j4 j8, rw_cells asegs m (B + rz - 16) [C1 b0; C1 b1; CB 2 j2; CB 4 j4] /\ rw_cells asegs m (B + rz - 16 + 8) [CB 8 j8])
    /\ (exists ub, rw_cells asegs m (B + rz) [CB (Z.to_nat n) ub])
    /\ (exists sl, rw_cells asegs m (B + rz + n) [CB (Z.to_nat (bs - rz - n)) sl])
    /\ (exists j1, rw_cells asegs m (sh B) [CB (Z.to_nat (rz / 8)) j1])
    /\ (exists ju, rw_cells asegs m (sh (B + rz)) [CB (Z.to_nat (n / 8)) ju])
    /\ (n mod 8 <> 0 -> exists bp, rw_cells asegs m (sh (B + rz) + n / 8) [C1 bp])
    /\ (exists jt, rw_cells asegs m (sh (B + rz + rup8 n)) [CB (Z.to_nat ((bs - rz - rup8 n) / 8)) jt]).
  Proof.
    intros m B bs rz n jb js B0 B8 BS8 RZ16 RZM N1 FIT HB HS.
    assert (RU : n <= rup8 n < n + 8 /\ rup8 n mod 8 = 0) by (unfold rup8; Z.div_mod_to_equations; lia).

    destruct (cb_split3 m B (Z.to_nat bs) jb (Z.to_nat (rz - 16)) 16 ltac:(lia) HB) as (j0 & jh & jr & H0 & HH & HR).
    rewrite Z2Nat.id in HH, HR by lia. replace (B + (rz - 16) + Z.of_nat 16) with (B + rz) in HR by lia. replace (B + (rz - 16)) with (B + rz - 16) in HH by lia.
    destruct (cb_split3 m (B + rz) (Z.to_nat bs - Z.to_nat (rz - 16) - 16) jr (Z.to_nat n) (Z.to_nat (bs - rz - n)) ltac:(lia) HR) as (ub & sl & _ & HU & HL & _).
    rewrite Z2Nat.id in HL by lia.
    destruct (hdr_cells_of_CB m _ jh HH) as (b0 & b1 & j2 & j4 & j8 & HD).
    change (rw_cells asegs m (B + rz - 16) ([C1 b0; C1 b1; CB 2 j2; CB 4 j4] ++ [CB 8 j8])) in HD. apply rw_cells_app in HD. destruct HD as [HD1 HD2].
    cbn [cells_size csize Nat.add] in HD2. change (Z.of_nat 8) with 8 in HD2.

    destruct (cb_split3 m (sh B) (Z.to_nat (bs / 8)) js (Z.to_nat (rz / 8)) (Z.to_nat (rup8 n / 8)) ltac:(Z.div_mod_to_equations; lia) HS) as (j1 & jm & jt & S1 & S2 & S3).
    rewrite (Z2Nat.id (rz / 8)) in S2, S3 by (Z.div_mod_to_equations; lia). rewrite (Z2Nat.id (rup8 n / 8)) in S3 by (Z.div_mod_to_equations; lia).
    replace (sh B + rz / 8) with (sh (B + rz)) in S2, S3 by (unfold sh; Z.div_mod_to_equations; lia).
    replace (sh (B + rz) + rup8 n / 8) with (sh (B + rz + rup8 n)) in S3 by (unfold sh; Z.div_mod_to_equations; lia).
    replace (Z.to_nat (bs / 8) - Z.to_nat (rz / 8) - Z.to_nat (rup8 n / 8))%nat with (Z.to_nat ((bs - rz - rup8 n) / 8)) in S3 by (Z.div_mod_to_equations; lia).
    destruct (cb_split3 m (sh (B + rz)) (Z.to_nat (rup8 n / 8)) _ (Z.to_nat (n / 8)) (Z.to_nat (rup8 n / 8 - n / 8)) ltac:(Z.div_mod_to_equations; lia) S2) as (ju & jp & _ & SU & SP & _).
    rewrite Z2Nat.id in SP by (Z.div_mod_to_equations; lia).
    split; [exists j0; exact H0|]. split; [exists b0, b1, j2, j4, j8; split; [exact HD1| exact HD2]|].
    split; [exists ub; exact HU|]. split; [exists sl; exact HL|]. split; [exists j1; exact S1|]. split; [exists ju; exact SU|]. split; [| exists jt; exact S3].
    intros NM. replace (Z.to_nat (rup8 n / 8 - n / 8)) with 1%nat in SP by (unfold rup8 in *; Z.div_mod_to_equations; lia).
    exact (cb1_byte m _ jp SP).
  Qed.
End CARVES.

