(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import PropExec MState Mem Cells Step Arr InitMem.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AImg.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Lemma rw_bytes_b_any : forall bs A (m : word -> option byte),
  rw_bytes_b asegs A bs = true -> (0 <= A)%Z -> (A + Z.of_nat (length bs) <= 2^64)%Z ->
  forall i, (i < length bs)%nat ->
    (exists b, mrd asegs m (wa (A + Z.of_nat i)) = Some b) /\ wview asegs m (wa (A + Z.of_nat i)) <> None.
Proof.
  Local Ltac2 Set LiaHints.tbl := fun () => "0050>13022274256.1519014448958.1551066064329.1554637255967.8 63592346137.1500000700>00E00I00SS2Hl2HiS2Hl2HiS2Hl2HiS2HiS2HA2Hl2Hi".
induction bs as [|b0 bs IH]; intros A m Hb HA Hl i Hi; [cbn in Hi; lia|].
  cbn [rw_bytes_b] in Hb.
  destruct (seg_rom asegs (wa A)) as [b'|] eqn:Er; [|discriminate].
  destruct (wview asegs (fun _ => None) (wa A)) as [bw|] eqn:Ew; [|discriminate].
  apply andb_prop in Hb. destruct Hb as [_ Hb]. cbn [length] in Hl, Hi.
  destruct i as [|i].
  - rewrite Z.add_0_r. unfold mrd, wview in *. destruct (m (wa A)) as [b1|].
    + split; [exists b1; reflexivity| discriminate].
    + split; [exists b'; exact Er| rewrite Ew; discriminate].
  - replace (A + Z.of_nat (S i))%Z with ((A + 1) + Z.of_nat i)%Z by lia. apply (IH (A + 1)%Z m Hb); lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma rw_junk_image : forall (m : word -> option byte) A bs,
  rw_bytes_b asegs A bs = true -> (0 <= A)%Z -> (A + Z.of_nat (length bs) <= 2^64)%Z ->
  exists bs', rw_cells asegs m A [CB (length bs) bs'].
Proof.
  intros m A bs Hb HA Hl.
  set (f := fun i : nat => match mrd asegs m (wa (A + Z.of_nat i)) with Some b => b | None => Z_to_bv 8 0 end).
  exists (map f (seq 0 (length bs))).
  split; [split|].
  - cbn. rewrite length_map, length_seq. split; [reflexivity| exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. Local Ltac2 Set LiaHints.tbl := fun () => "0040>1314912601.8  24937669871.8 53585280128.1066256213271.1000000400800<00@S2HlS2HAS2HiS2Hi".
split; [lia|]. rewrite length_map, length_seq. split; [lia|].
    intros i Hi. rewrite nth_error_map, nth_error_seq. replace (PeanoNat.Nat.ltb i (length bs)) with true by (symmetry; apply PeanoNat.Nat.ltb_lt; exact Hi). cbn [option_map Nat.add].
    destruct (rw_bytes_b_any bs A m Hb HA Hl i Hi) as [[b Hmb] _]. unfold f. rewrite Hmb. reflexivity.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. split; [lia|]. split; [lia|].
    intros i Hi. replace i with (Z.of_nat (Z.to_nat i)) by lia. apply (proj2 (rw_bytes_b_any bs A m Hb HA Hl (Z.to_nat i) ltac:(lia))).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma premap_canary_any : forall m : word -> option byte, exists cb, rw_cells asegs m 0x5f3e50 [CB 8 cb].
Proof.
  intros m. destruct (rw_junk_image m 0x5f3e50 (le8 (Z_to_bv 64 0)) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(rewrite length_le8; lia)) as [bs H].
  rewrite length_le8 in H. exists bs. exact H.
Qed.

End CANSEC1.
