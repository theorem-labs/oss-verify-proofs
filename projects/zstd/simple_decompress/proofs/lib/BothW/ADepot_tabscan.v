(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr.
From OSSVerify.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF.
From OSSVerify.Proofs.zstd.simple_decompress.lib.BothW Require Import BImg ABase ADepot_iface ADepot.
From OSSVerify.Proofs.zstd.simple_decompress.lib.AS Require Import AsanHexScan.   (* [comment removed for export] *)
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Notation S3 := AsanUbsan_seg_bytes_003 (only parsing).

Section CANSEC2. Context {rc : runConstT}.
Lemma tab_scan : zscanZ AsanUbsan_seg_bytes_003 0xe91d8 4194304 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.   (* [comment removed for export] *)

Lemma seg3_chunk_bytes : Z.to_N (Uint63.to_Z (PrimString.length AsanUbsan_seg_bytes_003) / 2) = 0x55c000%N.
Proof. vm_compute. reflexivity. Qed.

Lemma tab_byte_at : forall off : N, (0xe91d8 <= off < 0xe91d8 + 4194304)%N ->
  segment_byte_at (seg_bytes AsanUbsan_segment_003) off = Some (Z_to_bv 8 0).
Proof.
  intros off Hoff. cbn [seg_bytes AsanUbsan_segment_003 segment_byte_at].
  rewrite seg3_chunk_bytes.
  replace (off <? 0x55c000)%N with true by (symmetry; apply N.ltb_lt; lia).
  apply (zscanZ_sound _ _ _ tab_scan off). lia.
Qed.

End CANSEC2.
