(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatSim StoreOk ArtMem Pm5ArtFp Pm5ArtCellEx.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Lemma art_seg_rom_off : forall x : word, (U x < 0x10000 \/ 0x6c4000 <= U x) -> seg_rom ASEGS x = None.
Proof.
  intros x Hx. unfold seg_rom, memory_read. change (Z.of_N 1) with 1.
  rewrite (art_find_segment_none ASEGS 0x10000 0x6c4000 (U x) art_asegs_in Hx). reflexivity.
Qed.

Lemma art_byte_of_cell1 : forall (M : word -> option byte) a v, (a < 0x10000 \/ 0x6c4000 <= a) -> 0 <= a < 2 ^ 64 -> 0 <= v < 256 ->
  cellA M a 1 v -> M (Z_to_bv 64 a) = Some (Z_to_bv 8 v).
Proof.
  intros M a v Ha Ha' Hv C. unfold cell in C. cbn [rdn] in C. rewrite art_bytes1 in C by lia.
  destruct (M (Z_to_bv 64 a)) as [b|] eqn:E.
  - injection C as C. rewrite C. reflexivity.
  - rewrite art_seg_rom_off in C by (rewrite art_u_lit by lia; exact Ha). discriminate C.
Qed.

Lemma art_cell1_iff_byte : forall (M : word -> option byte) a v, (a < 0x10000 \/ 0x6c4000 <= a) -> 0 <= a < 2 ^ 64 -> 0 <= v < 256 ->
  (cellA M a 1 v <-> M (Z_to_bv 64 a) = Some (Z_to_bv 8 v)).
Proof. intros M a v Ha Ha' Hv. split; [apply art_byte_of_cell1; assumption|apply art_cell1_of_byte; exact Hv]. Qed.
