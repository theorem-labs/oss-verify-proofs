(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import PropExec MState Mem.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.P0 Require Import Segs.
From OSSVerify.pupnp.FuzzHttp.images Require Import Plain.
Import ListNotations.
Open Scope Z_scope.

Definition p0_reserved : list (Z * Z) := [(0x10000, 0x3000); (0x13000, 0x16000); (0x29000, 0x1000); (0x2a000, 0x32000)].
Notation P0_IMG_LO := 0x10000%Z (only parsing).
Notation P0_IMG_HI := 0x5c000%Z (only parsing).

Notation P0_RO_HI := 0x29000%Z (only parsing).

Lemma p0_find_segment_none : forall z n, 1 <= n -> (z + n <= 0x10000 \/ 0x5c000 <= z) ->
  find_segment rsegs z n = None.
Proof.
  intros z n Hn Hz. unfold rsegs, Plain.M.loaded_segments, Plain.Plain_loaded_segments. cbn [find_segment].
  replace (Z.of_N (seg_base Plain_segment_000)) with 0x10000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size Plain_segment_000)) with 0x3000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_base Plain_segment_001)) with 0x13000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size Plain_segment_001)) with 0x16000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_base Plain_segment_002)) with 0x29000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size Plain_segment_002)) with 0x1000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_base Plain_segment_003)) with 0x2a000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size Plain_segment_003)) with 0x32000 by (vm_compute; reflexivity).
  destruct (Z.leb_spec0 0x10000 z); destruct (Z.leb_spec0 (z + n) (0x10000 + 0x3000)); cbn [andb]; try lia.
  all: destruct (Z.leb_spec0 0x13000 z); destruct (Z.leb_spec0 (z + n) (0x13000 + 0x16000)); cbn [andb]; try lia.
  all: destruct (Z.leb_spec0 0x29000 z); destruct (Z.leb_spec0 (z + n) (0x29000 + 0x1000)); cbn [andb]; try lia.
  all: destruct (Z.leb_spec0 0x2a000 z); destruct (Z.leb_spec0 (z + n) (0x2a000 + 0x32000)); cbn [andb]; try lia.
  all: reflexivity.
Qed.

Lemma p0_ro_addr_false : forall x : word,
  (bv_unsigned x + 1 <= 0x10000 \/ 0x29000 <= bv_unsigned x) -> ro_addr rsegs x = false.
Proof.
  intros x Hx. unfold ro_addr, rsegs, Plain.M.loaded_segments, Plain.Plain_loaded_segments. cbn [find_segment].
  replace (Z.of_N (seg_base Plain_segment_000)) with 0x10000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size Plain_segment_000)) with 0x3000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_base Plain_segment_001)) with 0x13000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size Plain_segment_001)) with 0x16000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_base Plain_segment_002)) with 0x29000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size Plain_segment_002)) with 0x1000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_base Plain_segment_003)) with 0x2a000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size Plain_segment_003)) with 0x32000 by (vm_compute; reflexivity).
  destruct (Z.leb_spec0 0x10000 (bv_unsigned x)); destruct (Z.leb_spec0 (bv_unsigned x + 1) (0x10000 + 0x3000)); cbn [andb]; try lia.
  all: destruct (Z.leb_spec0 0x13000 (bv_unsigned x)); destruct (Z.leb_spec0 (bv_unsigned x + 1) (0x13000 + 0x16000)); cbn [andb]; try lia.
  all: destruct (Z.leb_spec0 0x29000 (bv_unsigned x)); destruct (Z.leb_spec0 (bv_unsigned x + 1) (0x29000 + 0x1000)); cbn [andb].
  all: try (destruct (Z.leb_spec0 0x2a000 (bv_unsigned x)); destruct (Z.leb_spec0 (bv_unsigned x + 1) (0x2a000 + 0x32000)); cbn [andb]).
  all: first [reflexivity | vm_compute; reflexivity].
Qed.

Lemma p0_memory_read_none : forall (x : word) n,
  1 <= Z.of_N n -> (bv_unsigned x + Z.of_N n <= 0x10000 \/ 0x5c000 <= bv_unsigned x) -> memory_read rsegs x n = None.
Proof. intros x n Hn Hx. unfold memory_read. rewrite p0_find_segment_none by lia. reflexivity. Qed.

Lemma p0_wview_overlay : forall m (x : word),
  (bv_unsigned x + 1 <= 0x10000 \/ 0x5c000 <= bv_unsigned x) -> wview rsegs m x = m x.
Proof.
  intros m x Hx. unfold wview. destruct (m x); [reflexivity|]. rewrite p0_find_segment_none by lia. reflexivity.
Qed.

Lemma p0_seg_rom_none : forall (x : word),
  (bv_unsigned x + 1 <= 0x10000 \/ 0x5c000 <= bv_unsigned x) -> seg_rom rsegs x = None.
Proof. intros x Hx. unfold seg_rom. rewrite p0_memory_read_none by (cbn; lia). reflexivity. Qed.

Notation P0_PAGE_SIZE := 0x5afe8%Z (only parsing).
Notation P0_VMLOCK := 0x5b808%Z (only parsing).
Notation P0_GOT_SSP := 0x29658%Z (only parsing).
Notation P0_SSP_GUARD := 0x5af98%Z (only parsing).
