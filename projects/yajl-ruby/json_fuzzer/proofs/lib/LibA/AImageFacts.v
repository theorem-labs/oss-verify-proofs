(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.yajl_ruby.json_fuzzer.images Require Import Asan AsanUbsan.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec Mem.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import AImages.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition a_image_end : Z := 0x603000.

Lemma asan_find_segment_none : forall z n, 1 <= n -> (z + n <= 0x10000 \/ 0x603000 <= z) ->
  find_segment asegs z n = None.
Proof.
  intros z n Hn Hz. unfold asegs, Asan.M.loaded_segments, Asan_loaded_segments. cbn [find_segment].
  replace (Z.of_N (seg_base Asan_segment_000)) with 0x10000%Z by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size Asan_segment_000)) with 0x21000%Z by (vm_compute; reflexivity).
  replace (Z.of_N (seg_base Asan_segment_001)) with 0x31000%Z by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size Asan_segment_001)) with 0x73000%Z by (vm_compute; reflexivity).
  replace (Z.of_N (seg_base Asan_segment_002)) with 0xa4000%Z by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size Asan_segment_002)) with 0x2000%Z by (vm_compute; reflexivity).
  replace (Z.of_N (seg_base Asan_segment_003)) with 0xa6000%Z by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size Asan_segment_003)) with 0x55d000%Z by (vm_compute; reflexivity).
  destruct (Z.leb_spec0 0x10000 z); destruct (Z.leb_spec0 (z + n) (0x10000 + 0x21000)); cbn [andb]; try lia.
  all: destruct (Z.leb_spec0 0x31000 z); destruct (Z.leb_spec0 (z + n) (0x31000 + 0x73000)); cbn [andb]; try lia.
  all: destruct (Z.leb_spec0 0xa4000 z); destruct (Z.leb_spec0 (z + n) (0xa4000 + 0x2000)); cbn [andb]; try lia.
  all: destruct (Z.leb_spec0 0xa6000 z); destruct (Z.leb_spec0 (z + n) (0xa6000 + 0x55d000)); cbn [andb]; try lia.
  all: reflexivity.
Qed.

Lemma asan_ro_addr_false : forall x : word,
  (bv_unsigned x + 1 <= 0x10000 \/ 0x603000 <= bv_unsigned x)%Z -> ro_addr asegs x = false.
Proof. intros x Hx. unfold ro_addr. rewrite asan_find_segment_none by lia. reflexivity. Qed.

Lemma asan_memory_read_none : forall (x : word) n,
  (1 <= Z.of_N n)%Z -> (bv_unsigned x + Z.of_N n <= 0x10000 \/ 0x603000 <= bv_unsigned x)%Z -> memory_read asegs x n = None.
Proof. intros x n Hn Hx. unfold memory_read. rewrite asan_find_segment_none by lia. reflexivity. Qed.

Lemma asan_wview_overlay : forall m (x : word),
  (bv_unsigned x + 1 <= 0x10000 \/ 0x603000 <= bv_unsigned x)%Z -> wview asegs m x = m x.
Proof.
  intros m x Hx. unfold wview. destruct (m x); [reflexivity|]. rewrite asan_find_segment_none by lia. reflexivity.
Qed.

Lemma asan_seg_rom_none : forall (x : word),
  (bv_unsigned x + 1 <= 0x10000 \/ 0x603000 <= bv_unsigned x)%Z -> seg_rom asegs x = None.
Proof. intros x Hx. unfold seg_rom. rewrite asan_memory_read_none by (cbn; lia). reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition b_image_end : Z := 0x603000.

Lemma both_find_segment_none : forall z n, 1 <= n -> (z + n <= 0x10000 \/ 0x603000 <= z) ->
  find_segment bsegs z n = None.
Proof.
  intros z n Hn Hz. unfold bsegs, AsanUbsan.M.loaded_segments, AsanUbsan_loaded_segments. cbn [find_segment].
  replace (Z.of_N (seg_base AsanUbsan_segment_000)) with 0x10000%Z by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size AsanUbsan_segment_000)) with 0x21000%Z by (vm_compute; reflexivity).
  replace (Z.of_N (seg_base AsanUbsan_segment_001)) with 0x31000%Z by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size AsanUbsan_segment_001)) with 0x74000%Z by (vm_compute; reflexivity).
  replace (Z.of_N (seg_base AsanUbsan_segment_002)) with 0xa5000%Z by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size AsanUbsan_segment_002)) with 0x2000%Z by (vm_compute; reflexivity).
  replace (Z.of_N (seg_base AsanUbsan_segment_003)) with 0xa7000%Z by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size AsanUbsan_segment_003)) with 0x55c000%Z by (vm_compute; reflexivity).
  destruct (Z.leb_spec0 0x10000 z); destruct (Z.leb_spec0 (z + n) (0x10000 + 0x21000)); cbn [andb]; try lia.
  all: destruct (Z.leb_spec0 0x31000 z); destruct (Z.leb_spec0 (z + n) (0x31000 + 0x74000)); cbn [andb]; try lia.
  all: destruct (Z.leb_spec0 0xa5000 z); destruct (Z.leb_spec0 (z + n) (0xa5000 + 0x2000)); cbn [andb]; try lia.
  all: destruct (Z.leb_spec0 0xa7000 z); destruct (Z.leb_spec0 (z + n) (0xa7000 + 0x55c000)); cbn [andb]; try lia.
  all: reflexivity.
Qed.

Lemma both_ro_addr_false : forall x : word,
  (bv_unsigned x + 1 <= 0x10000 \/ 0x603000 <= bv_unsigned x)%Z -> ro_addr bsegs x = false.
Proof. intros x Hx. unfold ro_addr. rewrite both_find_segment_none by lia. reflexivity. Qed.

Lemma both_memory_read_none : forall (x : word) n,
  (1 <= Z.of_N n)%Z -> (bv_unsigned x + Z.of_N n <= 0x10000 \/ 0x603000 <= bv_unsigned x)%Z -> memory_read bsegs x n = None.
Proof. intros x n Hn Hx. unfold memory_read. rewrite both_find_segment_none by lia. reflexivity. Qed.

Lemma both_wview_overlay : forall m (x : word),
  (bv_unsigned x + 1 <= 0x10000 \/ 0x603000 <= bv_unsigned x)%Z -> wview bsegs m x = m x.
Proof.
  intros m x Hx. unfold wview. destruct (m x); [reflexivity|]. rewrite both_find_segment_none by lia. reflexivity.
Qed.

Lemma both_seg_rom_none : forall (x : word),
  (bv_unsigned x + 1 <= 0x10000 \/ 0x603000 <= bv_unsigned x)%Z -> seg_rom bsegs x = None.
Proof. intros x Hx. unfold seg_rom. rewrite both_memory_read_none by (cbn; lia). reflexivity. Qed.
