(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.yajl_ruby.json_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import PropExec.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.XQ Require Import CertRefl.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.AS5 Require Import AsanHex5.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import AImages.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Mem MState.
From Ltac2 Require Import Ltac2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Default Proof Mode "Classic".
Import ListNotations.
Open Scope Z_scope.

Definition A_BSS_LO : Z := 0xaa4c0.   (* [comment removed for export] *)
Definition A_IMG_HI : Z := 0x603000.   (* [comment removed for export] *)
Definition A_SEG3_LO : Z := 0xa6000.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition img_byte (a : Z) : option byte := seg_rom asegs (Mem.wa a).

(* [comment removed for export] *)

Lemma seg3_len : Z.to_N (Uint63.to_Z (PrimString.length Asan_seg_bytes_003) / 2) = 5623808%N.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma find_seg3 : forall z, A_SEG3_LO <= z -> z + 1 <= A_IMG_HI -> find_segment asegs z 1 = Some Asan_segment_003.
Proof.
  intros z H1 H2. unfold A_SEG3_LO, A_IMG_HI in *.
  unfold asegs, Asan.M.loaded_segments, Asan_loaded_segments. cbn [find_segment].
  replace (Z.of_N (seg_base Asan_segment_000)) with 0x10000%Z by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size Asan_segment_000)) with 0x21000%Z by (vm_compute; reflexivity).
  replace (Z.of_N (seg_base Asan_segment_001)) with 0x31000%Z by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size Asan_segment_001)) with 0x73000%Z by (vm_compute; reflexivity).
  replace (Z.of_N (seg_base Asan_segment_002)) with 0xa4000%Z by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size Asan_segment_002)) with 0x2000%Z by (vm_compute; reflexivity).
  replace (Z.of_N (seg_base Asan_segment_003)) with 0xa6000%Z by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size Asan_segment_003)) with 0x55d000%Z by (vm_compute; reflexivity).
  destruct (Z.leb_spec0 0x10000 z); destruct (Z.leb_spec0 (z + 1) (0x10000 + 0x21000)); cbn [andb]; try lia.
  all: destruct (Z.leb_spec0 0x31000 z); destruct (Z.leb_spec0 (z + 1) (0x31000 + 0x73000)); cbn [andb]; try lia.
  all: destruct (Z.leb_spec0 0xa4000 z); destruct (Z.leb_spec0 (z + 1) (0xa4000 + 0x2000)); cbn [andb]; try lia.
  all: destruct (Z.leb_spec0 0xa6000 z); destruct (Z.leb_spec0 (z + 1) (0xa6000 + 0x55d000)); cbn [andb]; try lia.
  all: reflexivity.
Qed.

Theorem bss_zero : forall a, A_BSS_LO <= a < A_IMG_HI -> img_byte a = Some (Z_to_bv 8 0).
Proof.
  intros a Ha. unfold A_BSS_LO, A_IMG_HI in Ha. unfold img_byte, seg_rom, memory_read, Mem.wa.
  rewrite MState.unsigned_lit by lia. change (Z.of_N 1) with 1. rewrite find_seg3 by (unfold A_SEG3_LO, A_IMG_HI; lia).
  replace (seg_readable Asan_segment_003) with true by (vm_compute; reflexivity). cbv iota.
  change (seg_bytes Asan_segment_003) with [Asan_seg_bytes_003].
  change (Z.of_N (seg_base Asan_segment_003)) with 0xa6000. change (N.to_nat 1) with 1%nat.
  cbn [segment_read_bytes segment_byte_at]. rewrite seg3_len.
  replace (Z.to_N (a - 0xa6000) <? 5623808)%N with true by (symmetry; apply N.ltb_lt; lia).
  pose proof (asan_bss_hex_zero (Z.to_N (a - 0xa6000)) ltac:(lia)) as Z0.
  rewrite Z0. reflexivity.
Qed.
