(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase ADepot_iface ADepot.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AS Require Import AsanHexScan.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Notation S3 := Asan_seg_bytes_003 (only parsing).

Section CANSEC2. Context {rc : runConstT}.
Lemma tab_scan : zscanZ Asan_seg_bytes_003 0xe8bd8 4194304 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.   (* [comment removed for export] *)

Lemma seg3_chunk_bytes : Z.to_N (Uint63.to_Z (PrimString.length Asan_seg_bytes_003) / 2) = 0x55c000%N.
Proof. vm_compute. reflexivity. Qed.

Lemma tab_byte_at : forall off : N, (0xe8bd8 <= off < 0xe8bd8 + 4194304)%N ->
  segment_byte_at (seg_bytes Asan_segment_003) off = Some (Z_to_bv 8 0).
Proof.
  intros off Hoff. cbn [seg_bytes Asan_segment_003 segment_byte_at].
  rewrite seg3_chunk_bytes.
  replace (off <? 0x55c000)%N with true by (symmetry; apply N.ltb_lt; lia).
  apply (zscanZ_sound _ _ _ tab_scan off). lia.
Qed.

End CANSEC2.
