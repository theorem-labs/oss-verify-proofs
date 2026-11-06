(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes PropExec Mem Cells Step.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Lemma le8_of_bytes8 : forall bs : list byte, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof.
  intros bs HL. unfold le8, word_to_le_bytes, le_bytes_to_word.
  pose proof (bytes_le_to_Z_bound bs) as HR. pose proof (bytes_le_to_Z_nonneg bs) as HR1. rewrite HL in HR. change (2 ^ (8 * Z.of_nat 8))%Z with (2^64)%Z in HR.
  rewrite unsigned_lit by lia. rewrite <- HL. apply Z_to_le_bytes_to_Z.
Qed.

(* [comment removed for export] *)
Lemma image_word_readable : forall (m : word -> option byte) (A : Z) (b0 b1 b2 b3 b4 b5 b6 b7 : byte),
  0 <= A -> A + 8 <= 2^64 ->
  seg_rom asegs (wa (A + 0)) = Some b0 -> seg_rom asegs (wa (A + 1)) = Some b1 ->
  seg_rom asegs (wa (A + 2)) = Some b2 -> seg_rom asegs (wa (A + 3)) = Some b3 ->
  seg_rom asegs (wa (A + 4)) = Some b4 -> seg_rom asegs (wa (A + 5)) = Some b5 ->
  seg_rom asegs (wa (A + 6)) = Some b6 -> seg_rom asegs (wa (A + 7)) = Some b7 ->
  exists v : word, ro_cells asegs m A [C8 v].
Proof.
  intros m A b0 b1 b2 b3 b4 b5 b6 b7 H0 H1 R0 R1 R2 R3 R4 R5 R6 R7.
  assert (RD : forall i b, seg_rom asegs (wa (A + i)) = Some b -> exists c, mrd asegs m (wa (A + i)) = Some c).
  { intros i b H. unfold mrd. destruct (m (wa (A + i))) as [c|]; [exists c; reflexivity| exists b; exact H]. }
  destruct (RD _ _ R0) as [c0 E0]. destruct (RD _ _ R1) as [c1 E1]. destruct (RD _ _ R2) as [c2 E2]. destruct (RD _ _ R3) as [c3 E3].
  destruct (RD _ _ R4) as [c4 E4]. destruct (RD _ _ R5) as [c5 E5]. destruct (RD _ _ R6) as [c6 E6]. destruct (RD _ _ R7) as [c7 E7].
  exists (le_bytes_to_word [c0; c1; c2; c3; c4; c5; c6; c7]).
  unfold ro_cells, cells_at. split; [cbn; auto|].
  cbn [cells_bytes cbytes app]. rewrite le8_of_bytes8 by reflexivity. rewrite app_nil_r.
  split; [exact H0|]. split; [cbn [length]; lia|].
  intros i Hi. cbn [length] in Hi.
  destruct i as [|[|[|[|[|[|[|[|i]]]]]]]]; cbn [nth_error Z.of_nat Pos.of_succ_nat Pos.succ]; try assumption; lia.
Qed.

Lemma sec_name_cell : forall m : word -> option byte, exists nmv : word, ro_cells asegs m 0xa3e40 [C8 nmv].
Proof.
  intros m.
  eapply (image_word_readable m 0xa3e40); [lia| lia| vm_compute; reflexivity..].
Qed.
