(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge Frame Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts AllocA0 ATac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAA Require Import AEnv ADepot ALayout APrim APrimLem ACells LJ PEnv APrimSpec APrimSpec2 ASec AQuar AHeap F_prim_cid.
Import ListNotations.
Open Scope Z_scope.

Lemma class_of_fits : forall s, 1 <= s <= 65536 -> s <= class_size (class_of s).
Proof.
  intros s Hs. apply Z.leb_le.
  refine (check_from_ok (fun y => y <=? class_size (class_of y)) (Z.to_nat 65536) 1 _ s _); [vm_compute; reflexivity| lia].
Qed.

Section CARVE.
  Context {HC : HasCeiling}.

  #[using="Type"] Lemma cb_split3 : forall (m : mem) A (n : nat) j (a b : nat), (a + b <= n)%nat -> rw_cells asegs m A [CB n j] ->
    exists j1 j2 j3, rw_cells asegs m A [CB a j1] /\ rw_cells asegs m (A + Z.of_nat a) [CB b j2]
                     /\ rw_cells asegs m (A + Z.of_nat a + Z.of_nat b) [CB (n - a - b) j3].
  Proof.
    intros m A n j a b LE H.
    apply (rw_cells_split_CB asegs m A [] n j [] [a; b; (n - a - b)%nat]) in H; [| cbn [sum_nat]; lia].
    cbn [mk_CB_cells app] in H.
    lazymatch type of H with rw_cells _ _ _ [CB _ ?j1; CB _ ?j2; CB _ ?j3] =>
      exists j1, j2, j3;
      change (rw_cells asegs m A ([CB a j1] ++ [CB b j2; CB (n - a - b) j3])) in H; apply rw_cells_app in H; destruct H as [H1 H23];
      change (rw_cells asegs m (A + Z.of_nat (cells_size [CB a j1])) ([CB b j2] ++ [CB (n - a - b) j3])) in H23; apply rw_cells_app in H23; destruct H23 as [H2 H3] end.
    cbn [cells_size csize Nat.add] in H2, H3. rewrite Nat.add_0_r in H2. replace (a + 0)%nat with a in H3 by lia. replace (b + 0)%nat with b in H3 by lia.
    split; [exact H1|]. split; [exact H2| exact H3].
  Qed.

  #[using="Type"] Lemma hdr_cells_of_CB : forall (m : mem) A j, rw_cells asegs m A [CB 16 j] ->
    exists b0 b1 j2 j4 j8, rw_cells asegs m A [C1 b0; C1 b1; CB 2 j2; CB 4 j4; CB 8 j8].
  Proof.
    intros m A j H.
    apply (rw_cells_split_CB asegs m A [] 16 j [] [1; 1; 2; 4; 8]%nat) in H; [| reflexivity]. cbn [mk_CB_cells app] in H.
    lazymatch type of H with rw_cells _ _ _ [CB 1 ?x0; CB 1 ?x1; CB 2 ?x2; CB 4 ?x4; CB 8 ?x8] =>
      remember x0 as y0 eqn:E0; remember x1 as y1 eqn:E1; remember x2 as y2 eqn:E2; remember x4 as y4 eqn:E4; remember x8 as y8 eqn:E8 end.
    clear E0 E1 E2 E4 E8. pose proof H as [[WF _] _]. cbn in WF. destruct WF as (W0 & W1 & _).
    destruct y0 as [|b0 [|? ?]]; try discriminate W0. destruct y1 as [|b1 [|? ?]]; try discriminate W1.
    exists b0, b1, y2, y4, y8. eapply rw_cells_rebytes; [exact H| | reflexivity| reflexivity].
    pose proof H as [[WF _] _]. cbn in WF |- *. tauto.
  Qed.

  #[using="Type"] Lemma cells_bytes_shadow : forall ks, cells_bytes (shadow_cells ks) = map (Z_to_bv 8) ks.
  Proof. induction ks as [|k ks IH]; [reflexivity|]. cbn [shadow_cells map cells_bytes cbytes app] in *. unfold shadow_cells in IH. rewrite IH. reflexivity. Qed.
  #[using="Type"] Lemma cells_wf_shadow : forall ks, cells_wf (shadow_cells ks).
  Proof. induction ks as [|k ks IH]; [exact I|]. split; [exact I| exact IH]. Qed.
  #[using="Type"] Lemma shadow_cells_of_CB : forall (m : mem) A ks, rw_cells asegs m A [CB (length ks) (map (Z_to_bv 8) ks)] -> rw_cells asegs m A (shadow_cells ks).
  Proof.
    intros m A ks H. eapply rw_cells_rebytes; [exact H| apply cells_wf_shadow| |].
    - rewrite cells_bytes_shadow. cbn [cells_bytes cbytes]. rewrite app_nil_r. reflexivity.
    - rewrite cells_size_shadow. cbn [cells_size csize]. lia.
  Qed.

  #[using="Type"] Lemma block_shadow_cells : forall (m : mem) SA n, 0 <= n ->
    rw_cells asegs m SA [CB (Z.to_nat (n / 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (n / 8)))] ->
    (n mod 8 <> 0 -> rw_cells asegs m (SA + n / 8) [C1 (Z_to_bv 8 (n mod 8))]) ->
    rw_cells asegs m SA (shadow_cells (block_shadow n)).
  Proof.
    intros m SA n N0 HZ HP. unfold block_shadow. rewrite shadow_cells_app.
    assert (N8 : 0 <= n / 8) by (apply Z.div_pos; lia).
    apply rw_cells_app. split.
    - apply shadow_cells_of_CB. rewrite repeat_length, map_repeat. exact HZ.
    - rewrite cells_size_shadow, repeat_length, Z2Nat.id by exact N8.
      destruct (Z.eqb_spec (n mod 8) 0) as [E0|NE].
      + cbn [shadow_cells map]. destruct HZ as [[_ (B1 & B2 & _)] _]. cbn [cells_bytes cbytes app] in B2.
        rewrite app_nil_r, repeat_length, Z2Nat.id in B2 by exact N8.
        split; [split; [exact I|]|]; (split; [lia|]; split; [cbn; lia|]; intros i Hi; cbn in Hi; lia).
      + exact (HP NE).
  Qed.

  #[using="Type"] Lemma cb_split3_rep : forall (m : mem) A (n : nat) (x : byte) (a b : nat), (a + b <= n)%nat -> rw_cells asegs m A [CB n (repeat x n)] ->
    rw_cells asegs m A [CB a (repeat x a)] /\ rw_cells asegs m (A + Z.of_nat a) [CB b (repeat x b)]
    /\ rw_cells asegs m (A + Z.of_nat a + Z.of_nat b) [CB (n - a - b) (repeat x (n - a - b))].
  Proof.
    intros m A n x a b LE H.
    assert (H' : rw_cells asegs m A ([CB a (repeat x a)] ++ [CB b (repeat x b)] ++ [CB (n - a - b) (repeat x (n - a - b))])).
    { eapply rw_cells_rebytes; [exact H| | |].
      - cbn. rewrite !repeat_length. tauto.
      - cbn [app cells_bytes cbytes]. rewrite !app_nil_r. rewrite <- !repeat_app. f_equal. lia.
      - cbn [app cells_size csize]. lia. }
    apply rw_cells_app in H'. destruct H' as [H1 H23]. apply rw_cells_app in H23. destruct H23 as [H2 H3].
    cbn [cells_size csize Nat.add] in H2, H3. rewrite Nat.add_0_r in H2. replace (a + 0)%nat with a in H3 by lia. replace (b + 0)%nat with b in H3 by lia.
    split; [exact H1|]. split; [exact H2| exact H3].
  Qed.

  #[using="Type"] Lemma cb1_byte : forall (m : mem) A j, rw_cells asegs m A [CB 1 j] -> exists b, rw_cells asegs m A [C1 b].
  Proof.
    intros m A j H. pose proof H as [[WF _] _]. cbn in WF. destruct WF as (W0 & _).
    destruct j as [|b [|? ?]]; try discriminate W0. exists b. eapply rw_cells_rebytes; [exact H| cbn; tauto| reflexivity| reflexivity].
  Qed.

  #[using="Type"] Lemma carve_free : forall (m : mem) B bs rz n jb,
    0 <= B -> B mod 8 = 0 -> bs mod 8 = 0 -> 16 <= rz -> rz mod 16 = 0 -> 1 <= n -> rz + rup8 n <= bs ->
    rw_cells asegs m B [CB (Z.to_nat bs) jb] ->
    rw_cells asegs m (sh B) [CB (Z.to_nat (bs / 8)) (fa_bytes (bs / 8))] ->
    (exists j0, rw_cells asegs m B [CB (Z.to_nat (rz - 16)) j0])
    /\ (exists b0 b1 j2 j4 j8, rw_cells asegs m (B + rz - 16) [C1 b0; C1 b1; CB 2 j2; CB 4 j4] /\ rw_cells asegs m (B + rz - 16 + 8) [CB 8 j8])
    /\ (exists ub, rw_cells asegs m (B + rz) [CB (Z.to_nat n) ub])
    /\ (exists sl, rw_cells asegs m (B + rz + n) [CB (Z.to_nat (bs - rz - n)) sl])
    /\ rw_cells asegs m (sh B) [CB (Z.to_nat (rz / 8)) (fa_bytes (rz / 8))]
    /\ (exists ju, rw_cells asegs m (sh (B + rz)) [CB (Z.to_nat (n / 8)) ju])
    /\ (n mod 8 <> 0 -> exists bp, rw_cells asegs m (sh (B + rz) + n / 8) [C1 bp])
    /\ rw_cells asegs m (sh (B + rz + rup8 n)) [CB (Z.to_nat ((bs - rz - rup8 n) / 8)) (fa_bytes ((bs - rz - rup8 n) / 8))].
  Proof.
    intros m B bs rz n jb B0 B8 BS8 RZ16 RZM N1 FIT HB HS.
    assert (RU : n <= rup8 n < n + 8 /\ rup8 n mod 8 = 0) by (unfold rup8; Z.div_mod_to_equations; lia).

    destruct (cb_split3 m B (Z.to_nat bs) jb (Z.to_nat (rz - 16)) 16 ltac:(lia) HB) as (j0 & jh & jr & H0 & HH & HR).
    rewrite Z2Nat.id in HH, HR by lia. replace (B + (rz - 16) + Z.of_nat 16) with (B + rz) in HR by lia. replace (B + (rz - 16)) with (B + rz - 16) in HH by lia.
    destruct (cb_split3 m (B + rz) (Z.to_nat bs - Z.to_nat (rz - 16) - 16) jr (Z.to_nat n) (Z.to_nat (bs - rz - n)) ltac:(lia) HR) as (ub & sl & _ & HU & HL & _).
    rewrite Z2Nat.id in HL by lia.
    destruct (hdr_cells_of_CB m _ jh HH) as (b0 & b1 & j2 & j4 & j8 & HD).
    change (rw_cells asegs m (B + rz - 16) ([C1 b0; C1 b1; CB 2 j2; CB 4 j4] ++ [CB 8 j8])) in HD. apply rw_cells_app in HD. destruct HD as [HD1 HD2].
    cbn [cells_size csize Nat.add] in HD2. change (Z.of_nat 8) with 8 in HD2.

    unfold fa_bytes in HS |- *.
    destruct (cb_split3_rep m (sh B) (Z.to_nat (bs / 8)) (Z_to_bv 8 250) (Z.to_nat (rz / 8)) (Z.to_nat (rup8 n / 8)) ltac:(Z.div_mod_to_equations; lia) HS) as (S1 & S2 & S3).
    rewrite (Z2Nat.id (rz / 8)) in S2, S3 by (Z.div_mod_to_equations; lia). rewrite (Z2Nat.id (rup8 n / 8)) in S3 by (Z.div_mod_to_equations; lia).
    replace (sh B + rz / 8) with (sh (B + rz)) in S2, S3 by (unfold sh; Z.div_mod_to_equations; lia).
    replace (sh (B + rz) + rup8 n / 8) with (sh (B + rz + rup8 n)) in S3 by (unfold sh; Z.div_mod_to_equations; lia).
    replace (Z.to_nat (bs / 8) - Z.to_nat (rz / 8) - Z.to_nat (rup8 n / 8))%nat with (Z.to_nat ((bs - rz - rup8 n) / 8)) in S3 by (Z.div_mod_to_equations; lia).
    destruct (cb_split3 m (sh (B + rz)) (Z.to_nat (rup8 n / 8)) _ (Z.to_nat (n / 8)) (Z.to_nat (rup8 n / 8 - n / 8)) ltac:(Z.div_mod_to_equations; lia) S2) as (ju & jp & _ & SU & SP & _).
    rewrite Z2Nat.id in SP by (Z.div_mod_to_equations; lia).
    split; [exists j0; exact H0|]. split; [exists b0, b1, j2, j4, j8; split; [exact HD1| exact HD2]|].
    split; [exists ub; exact HU|]. split; [exists sl; exact HL|]. split; [exact S1|]. split; [exists ju; exact SU|]. split; [| exact S3].
    intros NM. replace (Z.to_nat (rup8 n / 8 - n / 8)) with 1%nat in SP by (unfold rup8 in *; Z.div_mod_to_equations; lia).
    exact (cb1_byte m _ jp SP).
  Qed.

  #[using="Type"] Lemma hdr_join : forall (m : mem) M (bits : byte) n actx,
    rw_cells asegs m M [C1 (Z_to_bv 8 2); C1 bits] -> rw_cells asegs m (M + 2) [C2 (wz 0); C4 (wz n)] -> rw_cells asegs m (M + 8) [C8 actx] ->
    rw_cells asegs m M [CB 4 [Z_to_bv 8 2; bits; Z_to_bv 8 0; Z_to_bv 8 0]; C4 (wz n); C8 actx].
  Proof.
    intros m M bits n actx H1 H2 H3.
    assert (HA : rw_cells asegs m M ([C1 (Z_to_bv 8 2); C1 bits] ++ [C2 (wz 0); C4 (wz n)] ++ [C8 actx])).
    { apply rw_cells_app. split; [exact H1|]. cbn [cells_size csize Nat.add]. change (Z.of_nat 2) with 2.
      apply rw_cells_app. split; [exact H2|]. cbn [cells_size csize Nat.add]. replace (M + 2 + Z.of_nat 6) with (M + 8) by lia. exact H3. }
    eapply rw_cells_rebytes; [exact HA| cbn; tauto| | reflexivity].
    cbn [app cells_bytes cbytes]. reflexivity.
  Qed.
End CARVE.
