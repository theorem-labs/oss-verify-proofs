(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Decode.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import KInv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition GRID_M : Z := 2^34.
Definition GRID_J : Z := 5461.
Definition GRID_W : Z := 2^33.     (* [comment removed for export] *)
Definition grid_floor : Z := 0x2aaaaaaab000.

Lemma grid_fits : grid_floor + GRID_J * GRID_M <= CEIL_MIN.
Proof. vm_compute. discriminate. Qed.
Lemma grid_floor_pos : 0 < grid_floor.
Proof. reflexivity. Qed.
Lemma grid_floor_aligned : grid_floor mod 4096 = 0.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma pigeon : forall (n : nat) (l : list Z), (length l < n)%nat -> exists i, 0 <= i < Z.of_nat n /\ ~ In i l.
Proof.
  induction n as [|n IH]; intros l Hl; [lia|].
  destruct (in_dec Z.eq_dec (Z.of_nat n) l) as [Hin|Hnot].
  - destruct (in_split _ _ Hin) as (l1 & l2 & ->).
    assert (Hl' : (length (l1 ++ l2) < n)%nat) by (rewrite length_app; rewrite length_app in Hl; cbn in Hl; lia).
    destruct (IH (l1 ++ l2) Hl') as (i & Hi & Hni).
    exists i. split; [lia|]. intros H. apply in_app_or in H as [H|[H|H]]; [apply Hni; apply in_or_app; auto| lia| apply Hni; apply in_or_app; auto].
  - exists (Z.of_nat n). split; [lia| exact Hnot].
Qed.

Section Grid.
Variable E : list (word * word).
Variable S : Z.
Hypothesis HS : 0 < S <= GRID_W.
Hypothesis HE : forall e, In e E -> elo e < ehi e /\ ehi e - elo e <= GRID_W.

Definition slot (i : Z) : Z := grid_floor + i * GRID_M.
(* [comment removed for export] *)
Definition cell (e : word * word) : Z := (elo e - grid_floor) / GRID_M.
Definition gslot (e : word * word) : Z :=
  let c := cell e in if elo e <? slot c + S then c else c + 1.

Lemma meets_unique : forall e i, In e E -> elo e < slot i + S -> slot i < ehi e -> i = gslot e.
Proof.
  intros e i He H1 H2. destruct (HE e He) as [W1 W2]. unfold gslot, cell, slot in *.
  unfold GRID_M, GRID_W in *.
  set (c := (elo e - grid_floor) / 2^34) in *.
  assert (Hc : grid_floor + c * 2^34 <= elo e < grid_floor + (c + 1) * 2^34) by (subst c; Z.div_mod_to_equations; lia).
  destruct (Z.ltb_spec (elo e) (grid_floor + c * 2^34 + S)); nia.
Qed.

Theorem grid_gap : Z.of_nat (length E) < GRID_J ->
  exists a, a mod 4096 = 0 /\ grid_floor <= a /\ a + S <= CEIL_MIN
            /\ forall e, In e E -> a + S <= elo e \/ ehi e <= a.
Proof.
  intros HL.
  assert (HL' : (length (map gslot E) < Z.to_nat GRID_J)%nat) by (rewrite length_map; unfold GRID_J in *; lia).
  destruct (pigeon (Z.to_nat GRID_J) (map gslot E) HL') as (i & Hi & Hni).
  rewrite Z2Nat.id in Hi by (unfold GRID_J; lia).
  exists (slot i). pose proof grid_fits as GF.
  unfold slot, GRID_M, GRID_J, GRID_W, grid_floor, CEIL_MIN in *.
  split; [| split; [lia| split; [nia|]]].
  { Z.div_mod_to_equations. nia. }
  intros e He. destruct (HE e He) as [W1 W2].
  destruct (Z.le_gt_cases (0x2aaaaaaab000 + i * 2^34 + S) (elo e)); [left; lia|].
  destruct (Z.le_gt_cases (ehi e) (0x2aaaaaaab000 + i * 2^34)); [right; lia|].
  exfalso. apply Hni. rewrite (meets_unique e i He) by (unfold slot, GRID_M, grid_floor; lia).
  apply in_map. exact He.
Qed.
End Grid.

Lemma region_free_introZ : forall maps (a n : word),
  (forall e sz, In (e, sz) maps -> bv_unsigned a + bv_unsigned n <= bv_unsigned e \/ bv_unsigned e + bv_unsigned sz <= bv_unsigned a) ->
  region_free maps a n = true.
Proof.
  induction maps as [|[e0 sz0] maps IH]; intros a n H; [reflexivity|]. cbn [region_free].
  rewrite IH by (intros; apply H; right; assumption).
  specialize (H e0 sz0 (or_introl eq_refl)). unfold iv_overlap.
  destruct (Z.ltb_spec0 (bv_unsigned a) (bv_unsigned e0 + bv_unsigned sz0));
  destruct (Z.ltb_spec0 (bv_unsigned e0) (bv_unsigned a + bv_unsigned n)); cbn; try reflexivity; lia.
Qed.

(* [comment removed for export] *)
Theorem gap_exists : forall (h : VmMaps) (nZ : Z),
  0 < nZ <= GRID_W -> nZ mod 4096 = 0 ->
  (forall e, In e (vm_reserved h ++ vm_maps h) -> elo e < ehi e /\ ehi e - elo e <= GRID_W) ->
  Z.of_nat (length (vm_reserved h ++ vm_maps h)) < GRID_J ->
  CEIL_MIN <= alloc_top h ->
  exists a : word,
    bv_unsigned a mod page_size = 0 /\ 0 < bv_unsigned a /\ bv_unsigned a + nZ <= alloc_top h
    /\ region_free (vm_reserved h ++ vm_maps h) a (Z_to_bv 64 nZ) = true.
Proof.
  intros h nZ HS Hal HE HL HT.
  destruct (grid_gap (vm_reserved h ++ vm_maps h) nZ HS HE HL) as (a & Ha & Hf & Hc & Hfree).
  pose proof grid_floor_pos as FP. unfold GRID_W in HS.
  assert (Ra : 0 <= a < 2^64) by (unfold grid_floor, CEIL_MIN in *; lia).
  assert (Ua : bv_unsigned (Z_to_bv 64 a) = a) by (rewrite Z_to_bv_unsigned; apply bv_wrap_small; unfold bv_modulus; lia).
  assert (Un : bv_unsigned (Z_to_bv 64 nZ) = nZ) by (rewrite Z_to_bv_unsigned; apply bv_wrap_small; unfold bv_modulus; lia).
  exists (Z_to_bv 64 a). rewrite Ua. split; [unfold page_size; exact Ha|]. split; [lia|]. split; [lia|].
  apply region_free_introZ; intros e sz He.
  specialize (Hfree (e, sz) He). unfold elo, ehi in Hfree. cbn in Hfree. rewrite Ua, Un. lia.
Qed.
