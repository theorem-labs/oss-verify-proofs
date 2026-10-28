(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Image.
From OssFuzzTheorems.zstd.huf_decompress.images Require Export AsanUbsan.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
(* [comment removed for export] *)
Ltac zify_pre_extra ::= atop_facts.
Import ListNotations.
Open Scope Z_scope.

Definition bsegs : list Segment := AsanUbsan.M.loaded_segments.
Definition b_init_pc : N := AsanUbsan.M.init_pc.
Definition b_phdrs : PhdrInfo := AsanUbsan.M.phdrs.

(* [comment removed for export] *)
Definition a_ro_lo   : Z := 0x10000.   Definition a_ro_hi   : Z := 0x30000.
Definition a_text_lo : Z := 0x30000.   Definition a_text_hi : Z := 0xb1000.
Definition a_rw1_lo  : Z := 0xb1000.  Definition a_rw1_hi  : Z := 0xb3000.
Definition a_rw2_lo  : Z := 0xb3000.  Definition a_rw2_hi  : Z := 0x60f000.

(* [comment removed for export] *)
Definition asan_reserved : list (Z * Z) :=
  [(0x10000, 0x20000); (0x30000, 0x81000); (0xb1000, 0x2000); (0xb3000, 0x55c000)].

Lemma reservedZ_asan : reservedZ bsegs = asan_reserved.
Proof. vm_compute. reflexivity. Qed.

Lemma segments_reserved_asan :
  segments_reserved bsegs =
  [(Z_to_bv 64 0x10000, Z_to_bv 64 0x20000); (Z_to_bv 64 0x30000, Z_to_bv 64 0x81000);
   (Z_to_bv 64 0xb1000, Z_to_bv 64 0x2000); (Z_to_bv 64 0xb3000, Z_to_bv 64 0x55c000)].
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma reserved_top_asan : reserved_top (segments_reserved bsegs) = 0x60f000.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma a_seg_flags :
  map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s), seg_readable s, seg_writable s, seg_executable s)) bsegs
  = [(0x10000, 0x20000, true, false, false); (0x30000, 0x81000, true, false, true);
     (0xb1000, 0x2000, true, true, false); (0xb3000, 0x55c000, true, true, false)].
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma a_find_segment_1 : forall z, 0 <= z ->
  find_segment bsegs z 1 =
    if (0x10000 <=? z) && (z + 1 <=? 0x30000) then Some AsanUbsan_segment_000
    else if (0x30000 <=? z) && (z + 1 <=? 0xb1000) then Some AsanUbsan_segment_001
    else if (0xb1000 <=? z) && (z + 1 <=? 0xb3000) then Some AsanUbsan_segment_002
    else if (0xb3000 <=? z) && (z + 1 <=? 0x60f000) then Some AsanUbsan_segment_003
    else None.
Proof. intros z Hz. reflexivity. Qed.

(* [comment removed for export] *)
Lemma a_ro_addr : forall a : word,
  ro_addr bsegs a = ((0x10000 <=? bv_unsigned a) && (bv_unsigned a <? 0xb1000))%bool.
Proof.
  intros a. unfold ro_addr. rewrite a_find_segment_1 by (pose proof (bv_unsigned_in_range 64 a); lia).
  pose proof (bv_unsigned_in_range 64 a) as R.
  destruct (Z.leb_spec0 0x10000 (bv_unsigned a)); destruct (Z.leb_spec0 (bv_unsigned a + 1) 0x30000);
  destruct (Z.leb_spec0 0x30000 (bv_unsigned a)); destruct (Z.leb_spec0 (bv_unsigned a + 1) 0xb1000);
  destruct (Z.leb_spec0 0xb1000 (bv_unsigned a)); destruct (Z.leb_spec0 (bv_unsigned a + 1) 0xb3000);
  destruct (Z.leb_spec0 0xb3000 (bv_unsigned a)); destruct (Z.leb_spec0 (bv_unsigned a + 1) 0x60f000);
  destruct (Z.ltb_spec0 (bv_unsigned a) 0xb1000); cbn; try reflexivity; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ref_find_segment_none : forall z n, 1 <= n -> (z + n <= 0x10000 \/ 0x60f000 <= z) ->
  find_segment bsegs z n = None.
Proof.
  intros z n Hn Hz. unfold bsegs, AsanUbsan.M.loaded_segments, AsanUbsan_loaded_segments. cbn [find_segment].
  replace (Z.of_N (seg_base AsanUbsan_segment_000)) with 0x10000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size AsanUbsan_segment_000)) with 0x20000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_base AsanUbsan_segment_001)) with 0x30000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size AsanUbsan_segment_001)) with 0x81000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_base AsanUbsan_segment_002)) with 0xb1000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size AsanUbsan_segment_002)) with 0x2000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_base AsanUbsan_segment_003)) with 0xb3000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size AsanUbsan_segment_003)) with 0x55c000 by (vm_compute; reflexivity).
  destruct (Z.leb_spec0 0x10000 z); destruct (Z.leb_spec0 (z + n) (0x10000 + 0x20000)); cbn [andb]; try lia;
  destruct (Z.leb_spec0 0x30000 z); destruct (Z.leb_spec0 (z + n) (0x30000 + 0x81000)); cbn [andb]; try lia;
  destruct (Z.leb_spec0 0xb1000 z); destruct (Z.leb_spec0 (z + n) (0xb1000 + 0x2000)); cbn [andb]; try lia;
  destruct (Z.leb_spec0 0xb3000 z); destruct (Z.leb_spec0 (z + n) (0xb3000 + 0x55c000)); cbn [andb]; try lia; reflexivity.
Qed.

Lemma ref_ro_addr_false : forall x : word,
  (bv_unsigned x + 1 <= 0x10000 \/ 0x60f000 <= bv_unsigned x)%Z -> ro_addr bsegs x = false.
Proof. intros x Hx. unfold ro_addr. rewrite ref_find_segment_none by lia. reflexivity. Qed.

Lemma ref_memory_read_none : forall (x : word) n,
  (1 <= Z.of_N n)%Z -> (bv_unsigned x + Z.of_N n <= 0x10000 \/ 0x60f000 <= bv_unsigned x)%Z -> memory_read bsegs x n = None.
Proof. intros x n Hn Hx. unfold memory_read. rewrite ref_find_segment_none by lia. reflexivity. Qed.

Lemma ref_wview_overlay : forall m (x : word),
  (bv_unsigned x + 1 <= 0x10000 \/ 0x60f000 <= bv_unsigned x)%Z -> wview bsegs m x = m x.
Proof.
  intros m x Hx. unfold wview. destruct (m x); [reflexivity|]. rewrite ref_find_segment_none by lia. reflexivity.
Qed.

Lemma ref_seg_rom_none : forall (x : word),
  (bv_unsigned x + 1 <= 0x10000 \/ 0x60f000 <= bv_unsigned x)%Z -> seg_rom bsegs x = None.
Proof. intros x Hx. unfold seg_rom. rewrite ref_memory_read_none by (cbn; lia). reflexivity. Qed.

Lemma ref_mrd_overlay : forall m (x : word),
  (bv_unsigned x + 1 <= 0x10000 \/ 0x60f000 <= bv_unsigned x)%Z -> mrd bsegs m x = m x.
Proof. intros m x Hx. unfold mrd. destruct (m x); [reflexivity|]. apply ref_seg_rom_none. exact Hx. Qed.

(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF.
Notation rng_aimg RNG := (rng RNG 0x10000 0x5ff000).
