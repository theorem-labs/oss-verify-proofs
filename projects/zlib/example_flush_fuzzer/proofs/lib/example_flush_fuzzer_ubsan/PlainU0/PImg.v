(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Lib Require Import PropExec MState Mem Image.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.World Require Export Tgt_example_flush_fuzzer_ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition psegs : list Segment := Tgt_example_flush_fuzzer_ubsan.M.loaded_segments.
Definition p_init_pc : N := Tgt_example_flush_fuzzer_ubsan.M.init_pc.
Definition p_phdrs : PhdrInfo := Tgt_example_flush_fuzzer_ubsan.M.phdrs.

Definition p_ro_hi   : Z := 0x15000.
Definition p_text_hi : Z := 0x2c000.
Definition p_rw1_hi  : Z := 0x2d000.
Definition p_rw2_hi  : Z := 0x5f000.


Lemma segments_reserved_plain :
  segments_reserved psegs =
  [(Z_to_bv 64 0x10000, Z_to_bv 64 0x5000); (Z_to_bv 64 0x15000, Z_to_bv 64 0x17000);
   (Z_to_bv 64 0x2c000, Z_to_bv 64 0x1000); (Z_to_bv 64 0x2d000, Z_to_bv 64 0x32000)].
Proof. vm_compute. reflexivity. Qed.

Lemma reserved_top_plain : reserved_top (segments_reserved psegs) = 0x5f000.
Proof. vm_compute. reflexivity. Qed.


Lemma p_find_segment_1 : forall z, 0 <= z ->
  find_segment psegs z 1 =
    if (0x10000 <=? z) && (z + 1 <=? 0x15000) then Some Tgt_example_flush_fuzzer_ubsan_segment_000
    else if (0x15000 <=? z) && (z + 1 <=? 0x2c000) then Some Tgt_example_flush_fuzzer_ubsan_segment_001
    else if (0x2c000 <=? z) && (z + 1 <=? 0x2d000) then Some Tgt_example_flush_fuzzer_ubsan_segment_002
    else if (0x2d000 <=? z) && (z + 1 <=? 0x5f000) then Some Tgt_example_flush_fuzzer_ubsan_segment_003
    else None.
Proof. intros z Hz. reflexivity. Qed.

Lemma p_ro_addr : forall a : word,
  ro_addr psegs a = ((0x10000 <=? bv_unsigned a) && (bv_unsigned a <? 0x2c000))%bool.
Proof.
  intros a. unfold ro_addr. rewrite p_find_segment_1 by (pose proof (bv_unsigned_in_range 64 a); lia).
  pose proof (bv_unsigned_in_range 64 a) as R.
  destruct (Z.leb_spec0 0x10000 (bv_unsigned a)); destruct (Z.leb_spec0 (bv_unsigned a + 1) 0x15000);
  destruct (Z.leb_spec0 0x15000 (bv_unsigned a)); destruct (Z.leb_spec0 (bv_unsigned a + 1) 0x2c000);
  destruct (Z.leb_spec0 0x2c000 (bv_unsigned a)); destruct (Z.leb_spec0 (bv_unsigned a + 1) 0x2d000);
  destruct (Z.leb_spec0 0x2d000 (bv_unsigned a)); destruct (Z.leb_spec0 (bv_unsigned a + 1) 0x5f000);
  destruct (Z.ltb_spec0 (bv_unsigned a) 0x2c000); cbn; try reflexivity; lia.
Qed.


Lemma ref_find_segment_none : forall z n, 1 <= n -> (z + n <= 0x10000 \/ 0x5f000 <= z) ->
  find_segment psegs z n = None.
Proof.
  intros z n Hn Hz. unfold psegs, Tgt_example_flush_fuzzer_ubsan.M.loaded_segments, Tgt_example_flush_fuzzer_ubsan_loaded_segments. cbn [find_segment].
  replace (Z.of_N (seg_base Tgt_example_flush_fuzzer_ubsan_segment_000)) with 0x10000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size Tgt_example_flush_fuzzer_ubsan_segment_000)) with 0x5000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_base Tgt_example_flush_fuzzer_ubsan_segment_001)) with 0x15000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size Tgt_example_flush_fuzzer_ubsan_segment_001)) with 0x17000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_base Tgt_example_flush_fuzzer_ubsan_segment_002)) with 0x2c000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size Tgt_example_flush_fuzzer_ubsan_segment_002)) with 0x1000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_base Tgt_example_flush_fuzzer_ubsan_segment_003)) with 0x2d000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size Tgt_example_flush_fuzzer_ubsan_segment_003)) with 0x32000 by (vm_compute; reflexivity).
  destruct (Z.leb_spec0 0x10000 z); destruct (Z.leb_spec0 (z + n) (0x10000 + 0x5000)); cbn [andb]; try lia;
  destruct (Z.leb_spec0 0x15000 z); destruct (Z.leb_spec0 (z + n) (0x15000 + 0x17000)); cbn [andb]; try lia;
  destruct (Z.leb_spec0 0x2c000 z); destruct (Z.leb_spec0 (z + n) (0x2c000 + 0x1000)); cbn [andb]; try lia;
  destruct (Z.leb_spec0 0x2d000 z); destruct (Z.leb_spec0 (z + n) (0x2d000 + 0x32000)); cbn [andb]; try lia; reflexivity.
Qed.

Lemma ref_ro_addr_false : forall x : word,
  (bv_unsigned x + 1 <= 0x10000 \/ 0x5f000 <= bv_unsigned x)%Z -> ro_addr psegs x = false.
Proof. intros x Hx. unfold ro_addr. rewrite ref_find_segment_none by lia. reflexivity. Qed.

Lemma ref_memory_read_none : forall (x : word) n,
  (1 <= Z.of_N n)%Z -> (bv_unsigned x + Z.of_N n <= 0x10000 \/ 0x5f000 <= bv_unsigned x)%Z -> memory_read psegs x n = None.
Proof. intros x n Hn Hx. unfold memory_read. rewrite ref_find_segment_none by lia. reflexivity. Qed.

Lemma ref_wview_overlay : forall m (x : word),
  (bv_unsigned x + 1 <= 0x10000 \/ 0x5f000 <= bv_unsigned x)%Z -> wview psegs m x = m x.
Proof.
  intros m x Hx. unfold wview. destruct (m x); [reflexivity|]. rewrite ref_find_segment_none by lia. reflexivity.
Qed.

Lemma ref_seg_rom_none : forall (x : word),
  (bv_unsigned x + 1 <= 0x10000 \/ 0x5f000 <= bv_unsigned x)%Z -> seg_rom psegs x = None.
Proof. intros x Hx. unfold seg_rom. rewrite ref_memory_read_none by (cbn; lia). reflexivity. Qed.

Lemma ref_mrd_overlay : forall m (x : word),
  (bv_unsigned x + 1 <= 0x10000 \/ 0x5f000 <= bv_unsigned x)%Z -> mrd psegs m x = m x.
Proof. intros m x Hx. unfold mrd. destruct (m x); [reflexivity|]. apply ref_seg_rom_none. exact Hx. Qed.

Definition RPAGE_SIZE : Z := 0x5da38.
Definition PREAD_STAGE : Z := 0x2d669.
Definition RAUXV_CELL : Z := 0x5da10.
Definition rmmap_entry : Z := 0x2532c.
Definition rmunmap_entry : Z := 0x25460.
Definition rmprotect_entry : Z := 0x25418.
