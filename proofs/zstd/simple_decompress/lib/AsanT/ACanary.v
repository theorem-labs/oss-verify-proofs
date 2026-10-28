(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem Cells Step Arr InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Lemma rw_bytes_b_any : forall bs A (m : word -> option byte),
  rw_bytes_b bsegs A bs = true -> (0 <= A)%Z -> (A + Z.of_nat (length bs) <= 2^64)%Z ->
  forall i, (i < length bs)%nat ->
    (exists b, mrd bsegs m (wa (A + Z.of_nat i)) = Some b) /\ wview bsegs m (wa (A + Z.of_nat i)) <> None.
Proof.
  induction bs as [|b0 bs IH]; intros A m Hb HA Hl i Hi; [cbn in Hi; lia|].
  cbn [rw_bytes_b] in Hb.
  destruct (seg_rom bsegs (wa A)) as [b'|] eqn:Er; [|discriminate].
  destruct (wview bsegs (fun _ => None) (wa A)) as [bw|] eqn:Ew; [|discriminate].
  apply andb_prop in Hb. destruct Hb as [_ Hb]. cbn [length] in Hl, Hi.
  destruct i as [|i].
  - rewrite Z.add_0_r. unfold mrd, wview in *. destruct (m (wa A)) as [b1|].
    + split; [exists b1; reflexivity| discriminate].
    + split; [exists b'; exact Er| rewrite Ew; discriminate].
  - replace (A + Z.of_nat (S i))%Z with ((A + 1) + Z.of_nat i)%Z by lia. apply (IH (A + 1)%Z m Hb); lia.
Qed.

Lemma rw_junk_image : forall (m : word -> option byte) A bs,
  rw_bytes_b bsegs A bs = true -> (0 <= A)%Z -> (A + Z.of_nat (length bs) <= 2^64)%Z ->
  exists bs', rw_cells bsegs m A [CB (length bs) bs'].
Proof.
  intros m A bs Hb HA Hl.
  set (f := fun i : nat => match mrd bsegs m (wa (A + Z.of_nat i)) with Some b => b | None => Z_to_bv 8 0 end).
  exists (map f (seq 0 (length bs))).
  split; [split|].
  - cbn. rewrite length_map, length_seq. split; [reflexivity| exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. split; [lia|]. rewrite length_map, length_seq. split; [lia|].
    intros i Hi. rewrite nth_error_map, nth_error_seq. replace (PeanoNat.Nat.ltb i (length bs)) with true by (symmetry; apply PeanoNat.Nat.ltb_lt; exact Hi). cbn [option_map Nat.add].
    destruct (rw_bytes_b_any bs A m Hb HA Hl i Hi) as [[b Hmb] _]. unfold f. rewrite Hmb. reflexivity.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. split; [lia|]. split; [lia|].
    intros i Hi. replace i with (Z.of_nat (Z.to_nat i)) by lia. apply (proj2 (rw_bytes_b_any bs A m Hb HA Hl (Z.to_nat i) ltac:(lia))).
Qed.

Lemma premap_canary_any : forall m : word -> option byte, exists cb, rw_cells bsegs m 0x622cf0 [CB 8 cb].
Proof.
  intros m. destruct (rw_junk_image m 0x622cf0 (le8 (Z_to_bv 64 0)) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(rewrite length_le8; lia)) as [bs H].
  rewrite length_le8 in H. exists bs. exact H.
Qed.

End CANSEC1.
