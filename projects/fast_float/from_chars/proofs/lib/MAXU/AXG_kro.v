(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk SeqExec AxSymExec3 AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Image.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require Import MallocModel MallocInv.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng MngRepr MngHeap.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxMalloc MngL4 AXG_as5 AXG_ag1.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Lemma kro_read1 : forall m lo hi A v, pristine m lo hi -> lo <= A -> A + 1 <= hi ->
  image_bytes SEGS A 1 = Some (word_to_le_bytes 1 (wa v)) -> rdn SEGS m (wa A) 1 = Some (word_to_le_bytes 1 (wa v)).
Proof.
  intros m lo hi A v P H1 H2 HI. rewrite <- ov_rdn. exact (pristine_read SEGS m lo hi A 1 _ P HI H1 H2).
Qed.

Lemma dbt_img : forall n : nat, (n < 32)%nat -> image_bytes SEGS (98952 + Z.of_nat n) 1 = Some (word_to_le_bytes 1 (wa (znth (Z.of_nat n) debruijn))).
Proof. intros n Hn. do 32 (destruct n as [|n]; [vm_compute; reflexivity|]). lia. Qed.

Lemma DBT_of_KRO : forall m, KRO m -> DBT m.
Proof.
  intros m (P1 & _) j Hj. replace j with (Z.of_nat (Z.to_nat j)) by lia.
  apply (kro_read1 m 0x18288 0x182a8); [exact P1 | lia | lia | apply dbt_img; lia].
Qed.

Lemma small_img : forall a b : nat, (a < 9)%nat -> (b < 3)%nat ->
  image_bytes SEGS (3 * Z.of_nat a + (99080 + Z.of_nat b)) 1 = Some (word_to_le_bytes 1 (wa (znth (Z.of_nat b) (nth a small_cnt_tab [])))).
Proof. intros a b Ha Hb. do 9 (destruct a as [|a]; [do 3 (destruct b as [|b]; [vm_compute; reflexivity|]); lia|]). lia. Qed.

Lemma med_img : forall b : nat, (b < 4)%nat -> image_bytes SEGS (Z.of_nat b + 99107) 1 = Some (word_to_le_bytes 1 (wa (znth (Z.of_nat b) med_cnt_tab))).
Proof. intros b Hb. do 4 (destruct b as [|b]; [vm_compute; reflexivity|]). lia. Qed.

Lemma TABS_of_KRO : forall m, KRO m -> TABS m.
Proof.
  intros m (_ & P2). split.
  - intros sc k Hsc Hk. replace sc with (Z.of_nat (Z.to_nat sc)) at 1 by lia. replace k with (Z.of_nat (Z.to_nat k)) by lia.
    apply (kro_read1 m 0x182a8 0x18327); [exact P2 | lia | lia | apply small_img; lia].
  - intros k Hk. replace k with (Z.of_nat (Z.to_nat k)) by lia.
    apply (kro_read1 m 0x182a8 0x18327); [exact P2 | lia | lia | apply med_img; lia].
Qed.

Lemma kro_read2 : forall m lo hi A v, pristine m lo hi -> lo <= A -> A + 2 <= hi ->
  image_bytes SEGS A 2 = Some (word_to_le_bytes 2 (wa v)) -> rdn SEGS m (wa A) 2 = Some (word_to_le_bytes 2 (wa v)).
Proof.
  intros m lo hi A v P H1 H2 HI. rewrite <- ov_rdn. exact (pristine_read SEGS m lo hi A 2 _ P HI H1 H2).
Qed.

Lemma bytes_eq_of_unsigned : forall (bs cs : list byte), map bv_unsigned bs = map bv_unsigned cs -> bs = cs.
Proof.
  induction bs as [|b bs IH]; intros [|c cs] H; cbn in H; try discriminate; [reflexivity|].
  injection H as H1 H2. f_equal; [apply bv_eq; exact H1 | apply IH; exact H2].
Qed.

Lemma img_of_unsigned : forall A n bs, option_map (map bv_unsigned) (image_bytes SEGS A n) = Some (map bv_unsigned bs) -> image_bytes SEGS A n = Some bs.
Proof.
  intros A n bs H. destruct (image_bytes SEGS A n) as [cs|]; cbn in H; [|discriminate]. injection H as H. rewrite (bytes_eq_of_unsigned _ _ H). reflexivity.
Qed.

Lemma sc_img : forall n : nat, (n < 48)%nat -> image_bytes SEGS (98984 + 2 * Z.of_nat n) 2 = Some (word_to_le_bytes 2 (wa (znth (Z.of_nat n) size_classes))).
Proof. intros n Hn. apply img_of_unsigned. do 48 (destruct n as [|n]; [vm_compute; reflexivity|]). lia. Qed.

Lemma SC_of_KRO : forall m, KRO m -> forall sc, 0 <= sc < 48 -> rdn SEGS m (wa (98984 + 2 * sc)) 2 = Some (word_to_le_bytes 2 (wa (znth sc size_classes))).
Proof.
  intros m (_ & P2) sc Hsc. replace sc with (Z.of_nat (Z.to_nat sc)) by lia.
  apply (kro_read2 m 0x182a8 0x18327); [exact P2 | lia | lia | apply sc_img; lia].
Qed.
