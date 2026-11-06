(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.yajl_ruby.json_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.XQ Require Import AsanHexScan.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.AS5 Require Import HexZeroFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

(* [comment removed for export] *)
Lemma asan_hex2 : scanN Asan_seg_bytes_002 64 0 8192 = true.
Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Lemma asan_hex3_head : scanN Asan_seg_bytes_003 64 0 17600 = true.
Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Lemma asan_bss_hex_zero : forall i : N, (17600 <= i < 5623808)%N ->
  hex_byte_at Asan_seg_bytes_003 i = Some (Z_to_bv 8 0).
Proof.
  apply (hex_zero_fast _ 17600%N 5606208%N).
  - vm_compute. reflexivity.
  - apply Z.leb_le. vm_compute. reflexivity.
  - apply Z.leb_le. vm_compute. reflexivity.
Qed.
Lemma asan_len2 : Z.to_N (Uint63.to_Z (PrimString.length Asan_seg_bytes_002) / 2) = 8192%N.
Proof. vm_compute. reflexivity. Qed.
Lemma asan_len3 : Z.to_N (Uint63.to_Z (PrimString.length Asan_seg_bytes_003) / 2) = 5623808%N.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma asan_seg3_some : forall off : N, (Z.of_N off < 5623808)%Z ->
  segment_byte_at [Asan_seg_bytes_003] off <> None.
Proof.
  intros off Hoff.
  apply (segment_byte_at_some_pw _ 17600%N 5623808%N off asan_hex3_head asan_bss_hex_zero); [rewrite asan_len3; lia | lia].
Qed.
