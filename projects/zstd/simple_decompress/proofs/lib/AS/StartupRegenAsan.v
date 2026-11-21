(* SPDX-License-Identifier: MIT *)
(* Start-up data of the Asan build at LPS 727298f3, the r-indexed tables, states, counters and shapes.  Written by gen_startup_regen.py from the start-up
   probe's printout (docs/343-certificate-data-method.md, sections 2, 3 and 5).  No state here is recorded: every
   state, table, counter and shape is computed by vm_compute from [check], and each certificate re-checks it. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zstd.simple_decompress.lib.AS Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanImages
  AsanInit AsanNodesWJoin StartupPlanAsan StartupPlan2Asan AsanCertDefs PlanRegen.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
From OSSVerify.Proofs.zstd.simple_decompress.lib.AS Require Export StartupRegenAsanPlans StartupRegenAsanR0 StartupRegenAsanR1.

Definition nxA (r : Z) : nat := NX0.
Definition hslA (r : Z) : list (nat * acs) := if Z.eqb r 1 then hslA_1 else hslA_0.
Definition hsA (r : Z) : nat -> option acs := hlookup (hslA r).
Definition stA (r : Z) : acs := if Z.eqb r 1 then stA_1 else stA_0.
Definition shapeA (r : Z) : shape := if Z.eqb r 1 then shapeA_1 else shapeA_0.
Lemma hsA_one : forall r h ch, hsA r h = Some ch -> h = 10%nat /\ ch = stA r.
Proof.
  intros r. unfold hsA, hslA, stA, stA_0, stA_1. destruct (Z.eqb r 1);
  apply hlookup_one; vm_compute; reflexivity.
Qed.

Definition nxB (r : Z) : nat := (if Z.eqb r 1 then nxt stA_1 else nxt stA_0).
Definition hslB (r : Z) : list (nat * acs) := if Z.eqb r 1 then hslB_1 else hslB_0.
Definition hsB (r : Z) : nat -> option acs := hlookup (hslB r).
Definition stB (r : Z) : acs := if Z.eqb r 1 then stB_1 else stB_0.
Definition shapeB (r : Z) : shape := if Z.eqb r 1 then shapeB_1 else shapeB_0.
Lemma nxB_ge : forall r, (NX0 <= nxB r)%nat.
Proof. intros r. apply Nat.leb_le. unfold nxB. destruct (Z.eqb r 1); vm_compute; reflexivity. Qed.
Lemma hsB_one : forall r h ch, hsB r h = Some ch -> h = 11%nat /\ ch = stB r.
Proof.
  intros r. unfold hsB, hslB, stB, stB_0, stB_1. destruct (Z.eqb r 1);
  apply hlookup_one; vm_compute; reflexivity.
Qed.

Definition nxC (r : Z) : nat := (if Z.eqb r 1 then nxt stB_1 else nxt stB_0).
Definition hslC (r : Z) : list (nat * acs) := if Z.eqb r 1 then hslC_1 else hslC_0.
Definition hsC (r : Z) : nat -> option acs := hlookup (hslC r).
Definition stC (r : Z) : acs := if Z.eqb r 1 then stC_1 else stC_0.
Definition shapeC (r : Z) : shape := if Z.eqb r 1 then shapeC_1 else shapeC_0.
Lemma nxC_ge : forall r, (NX0 <= nxC r)%nat.
Proof. intros r. apply Nat.leb_le. unfold nxC. destruct (Z.eqb r 1); vm_compute; reflexivity. Qed.
Lemma hsC_one : forall r h ch, hsC r h = Some ch -> h = 12%nat /\ ch = stC r.
Proof.
  intros r. unfold hsC, hslC, stC, stC_0, stC_1. destruct (Z.eqb r 1);
  apply hlookup_one; vm_compute; reflexivity.
Qed.

Definition nxD (r : Z) : nat := (if Z.eqb r 1 then nxt stC_1 else nxt stC_0).
Definition hslD (r : Z) : list (nat * acs) := if Z.eqb r 1 then hslD_1 else hslD_0.
Definition hsD (r : Z) : nat -> option acs := hlookup (hslD r).
Definition stD (r : Z) : acs := if Z.eqb r 1 then stD_1 else stD_0.
Definition shapeD (r : Z) : shape := if Z.eqb r 1 then shapeD_1 else shapeD_0.
Lemma nxD_ge : forall r, (NX0 <= nxD r)%nat.
Proof. intros r. apply Nat.leb_le. unfold nxD. destruct (Z.eqb r 1); vm_compute; reflexivity. Qed.
Lemma hsD_one : forall r h ch, hsD r h = Some ch -> h = 0%nat /\ ch = stD r.
Proof.
  intros r. unfold hsD, hslD, stD, stD_0, stD_1. destruct (Z.eqb r 1);
  apply hlookup_one; vm_compute; reflexivity.
Qed.

Definition nx2 (r : Z) : nat := (if Z.eqb r 1 then nxt stD_1 else nxt stD_0).
Definition hsl2 (r : Z) : list (nat * acs) := if Z.eqb r 1 then hsl2_1 else hsl2_0.
Definition hs2 (r : Z) : nat -> option acs := hlookup (hsl2 r).
Definition stS1 (r : Z) : acs := if Z.eqb r 1 then stS1_1 else stS1_0.
Definition stS2 (r : Z) : acs := if Z.eqb r 1 then stS2_1 else stS2_0.
Definition shape2 (r : Z) : shape := if Z.eqb r 1 then shape2_1 else shape2_0.
Lemma nx2_ge : forall r, (NX0 <= nx2 r)%nat.
Proof. intros r. apply Nat.leb_le. unfold nx2. destruct (Z.eqb r 1); vm_compute; reflexivity. Qed.
Lemma hs2_two : forall r h ch, hs2 r h = Some ch ->
  (h = 1%nat /\ ch = stS1 r) \/ (h = 2%nat /\ ch = stS2 r).
Proof.
  intros r. unfold hs2, hsl2, stS1, stS2, stS1_0, stS1_1, stS2_0, stS2_1. destruct (Z.eqb r 1);
  (apply hlookup_two_any; [vm_compute; first [left; reflexivity | right; reflexivity] | reflexivity]).
Qed.
