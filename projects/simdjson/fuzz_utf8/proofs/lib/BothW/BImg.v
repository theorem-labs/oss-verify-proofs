(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib Require Import PropExec MState Mem Image.
From OSSVerify.simdjson.fuzz_utf8.images Require Export AsanUbsan.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import RunDraw.
(* [comment removed for export] *)
Ltac zify_pre_extra ::= atop_facts.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

Definition bsegs : list Segment := AsanUbsan.M.loaded_segments.
Definition b_init_pc : N := AsanUbsan.M.init_pc.
Definition b_phdrs : PhdrInfo := AsanUbsan.M.phdrs.

(* [comment removed for export] *)
Definition a_ro_lo   : Z := 0x10000.   Definition a_ro_hi   : Z := 0x58000.
Definition a_text_lo : Z := 0x58000.   Definition a_text_hi : Z := 0x16b000.
Definition a_rw1_lo  : Z := 0x16b000.  Definition a_rw1_hi  : Z := 0x173000.
Definition a_rw2_lo  : Z := 0x173000.  Definition a_rw2_hi  : Z := 0x6d2000.

(* [comment removed for export] *)
Definition asan_reserved : list (Z * Z) :=
  [(0x10000, 0x48000); (0x58000, 0x113000); (0x16b000, 0x8000); (0x173000, 0x55f000)].

Lemma reservedZ_asan : reservedZ bsegs = asan_reserved.
Proof. vm_compute. reflexivity. Qed.

Lemma segments_reserved_asan :
  segments_reserved bsegs =
  [(Z_to_bv 64 0x10000, Z_to_bv 64 0x48000); (Z_to_bv 64 0x58000, Z_to_bv 64 0x113000);
   (Z_to_bv 64 0x16b000, Z_to_bv 64 0x8000); (Z_to_bv 64 0x173000, Z_to_bv 64 0x55f000)].
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma reserved_top_asan : reserved_top (segments_reserved bsegs) = 0x6d2000.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma a_seg_flags :
  map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s), seg_readable s, seg_writable s, seg_executable s)) bsegs
  = [(0x10000, 0x48000, true, false, false); (0x58000, 0x113000, true, false, true);
     (0x16b000, 0x8000, true, true, false); (0x173000, 0x55f000, true, true, false)].
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma a_find_segment_1 : forall z, 0 <= z ->
  find_segment bsegs z 1 =
    if (0x10000 <=? z) && (z + 1 <=? 0x58000) then Some AsanUbsan_segment_000
    else if (0x58000 <=? z) && (z + 1 <=? 0x16b000) then Some AsanUbsan_segment_001
    else if (0x16b000 <=? z) && (z + 1 <=? 0x173000) then Some AsanUbsan_segment_002
    else if (0x173000 <=? z) && (z + 1 <=? 0x6d2000) then Some AsanUbsan_segment_003
    else None.
Proof. intros z Hz. reflexivity. Qed.

(* [comment removed for export] *)
Lemma a_ro_addr : forall a : word,
  ro_addr bsegs a = ((0x10000 <=? bv_unsigned a) && (bv_unsigned a <? 0x16b000))%bool.
Proof.
  intros a. unfold ro_addr. rewrite a_find_segment_1 by (pose proof (bv_unsigned_in_range 64 a); lia).
  pose proof (bv_unsigned_in_range 64 a) as R.
  destruct (Z.leb_spec0 0x10000 (bv_unsigned a)); destruct (Z.leb_spec0 (bv_unsigned a + 1) 0x58000);
  destruct (Z.leb_spec0 0x58000 (bv_unsigned a)); destruct (Z.leb_spec0 (bv_unsigned a + 1) 0x16b000);
  destruct (Z.leb_spec0 0x16b000 (bv_unsigned a)); destruct (Z.leb_spec0 (bv_unsigned a + 1) 0x173000);
  destruct (Z.leb_spec0 0x173000 (bv_unsigned a)); destruct (Z.leb_spec0 (bv_unsigned a + 1) 0x6d2000);
  destruct (Z.ltb_spec0 (bv_unsigned a) 0x16b000); cbn; try reflexivity; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ref_find_segment_none : forall z n, 1 <= n -> (z + n <= 0x10000 \/ 0x6d2000 <= z) ->
  find_segment bsegs z n = None.
Proof.
  intros z n Hn Hz. unfold bsegs, AsanUbsan.M.loaded_segments, AsanUbsan_loaded_segments. cbn [find_segment].
  replace (Z.of_N (seg_base AsanUbsan_segment_000)) with 0x10000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size AsanUbsan_segment_000)) with 0x48000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_base AsanUbsan_segment_001)) with 0x58000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size AsanUbsan_segment_001)) with 0x113000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_base AsanUbsan_segment_002)) with 0x16b000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size AsanUbsan_segment_002)) with 0x8000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_base AsanUbsan_segment_003)) with 0x173000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size AsanUbsan_segment_003)) with 0x55f000 by (vm_compute; reflexivity).
  destruct (Z.leb_spec0 0x10000 z); destruct (Z.leb_spec0 (z + n) (0x10000 + 0x48000)); cbn [andb]; try lia;
  destruct (Z.leb_spec0 0x58000 z); destruct (Z.leb_spec0 (z + n) (0x58000 + 0x113000)); cbn [andb]; try lia;
  destruct (Z.leb_spec0 0x16b000 z); destruct (Z.leb_spec0 (z + n) (0x16b000 + 0x8000)); cbn [andb]; try lia;
  destruct (Z.leb_spec0 0x173000 z); destruct (Z.leb_spec0 (z + n) (0x173000 + 0x55f000)); cbn [andb]; try lia; reflexivity.
Qed.

Lemma ref_ro_addr_false : forall x : word,
  (bv_unsigned x + 1 <= 0x10000 \/ 0x6d2000 <= bv_unsigned x)%Z -> ro_addr bsegs x = false.
Proof. intros x Hx. unfold ro_addr. rewrite ref_find_segment_none by lia. reflexivity. Qed.

Lemma ref_memory_read_none : forall (x : word) n,
  (1 <= Z.of_N n)%Z -> (bv_unsigned x + Z.of_N n <= 0x10000 \/ 0x6d2000 <= bv_unsigned x)%Z -> memory_read bsegs x n = None.
Proof. intros x n Hn Hx. unfold memory_read. rewrite ref_find_segment_none by lia. reflexivity. Qed.

Lemma ref_wview_overlay : forall m (x : word),
  (bv_unsigned x + 1 <= 0x10000 \/ 0x6d2000 <= bv_unsigned x)%Z -> wview bsegs m x = m x.
Proof.
  intros m x Hx. unfold wview. destruct (m x); [reflexivity|]. rewrite ref_find_segment_none by lia. reflexivity.
Qed.

Lemma ref_seg_rom_none : forall (x : word),
  (bv_unsigned x + 1 <= 0x10000 \/ 0x6d2000 <= bv_unsigned x)%Z -> seg_rom bsegs x = None.
Proof. intros x Hx. unfold seg_rom. rewrite ref_memory_read_none by (cbn; lia). reflexivity. Qed.

Lemma ref_mrd_overlay : forall m (x : word),
  (bv_unsigned x + 1 <= 0x10000 \/ 0x6d2000 <= bv_unsigned x)%Z -> mrd bsegs m x = m x.
Proof. intros m x Hx. unfold mrd. destruct (m x); [reflexivity|]. apply ref_seg_rom_none. exact Hx. Qed.

(* [comment removed for export] *)
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.LibA Require Import ExecF.
Notation rng_aimg RNG := (rng RNG 0x10000 0x6c2000).
