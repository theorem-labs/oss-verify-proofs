(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib Require Import PropExec MState Mem Image.
From OSSVerify.simdjson.fuzz_utf8.images Require Export Plain.
Import ListNotations.
Open Scope Z_scope.

Definition psegs : list Segment := Plain.M.loaded_segments.
Definition p_init_pc : N := Plain.M.init_pc.
Definition p_phdrs : PhdrInfo := Plain.M.phdrs.

(* [comment removed for export] *)
Definition p_ro_lo   : Z := 0x10000.  Definition p_ro_hi   : Z := 0x3a000.
Definition p_text_lo : Z := 0x3a000.  Definition p_text_hi : Z := 0xca000.
Definition p_rw1_lo  : Z := 0xca000.  Definition p_rw1_hi  : Z := 0xd0000.
Definition p_rw2_lo  : Z := 0xd0000.  Definition p_rw2_hi  : Z := 0x105000.

(* [comment removed for export] *)
Definition plain_reserved : list (Z * Z) :=
  [(0x10000, 0x2a000); (0x3a000, 0x90000); (0xca000, 0x6000); (0xd0000, 0x35000)].

Lemma reservedZ_plain : reservedZ psegs = plain_reserved.
Proof. vm_compute. reflexivity. Qed.

Lemma segments_reserved_plain :
  segments_reserved psegs =
  [(Z_to_bv 64 0x10000, Z_to_bv 64 0x2a000); (Z_to_bv 64 0x3a000, Z_to_bv 64 0x90000);
   (Z_to_bv 64 0xca000, Z_to_bv 64 0x6000); (Z_to_bv 64 0xd0000, Z_to_bv 64 0x35000)].
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma reserved_top_plain : reserved_top (segments_reserved psegs) = 0x105000.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma p_seg_flags :
  map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s), seg_readable s, seg_writable s, seg_executable s)) psegs
  = [(0x10000, 0x2a000, true, false, false); (0x3a000, 0x90000, true, false, true);
     (0xca000, 0x6000, true, true, false); (0xd0000, 0x35000, true, true, false)].
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma p_find_segment_1 : forall z, 0 <= z ->
  find_segment psegs z 1 =
    if (0x10000 <=? z) && (z + 1 <=? 0x3a000) then Some Plain_segment_000
    else if (0x3a000 <=? z) && (z + 1 <=? 0xca000) then Some Plain_segment_001
    else if (0xca000 <=? z) && (z + 1 <=? 0xd0000) then Some Plain_segment_002
    else if (0xd0000 <=? z) && (z + 1 <=? 0x105000) then Some Plain_segment_003
    else None.
Proof. intros z Hz. reflexivity. Qed.

(* [comment removed for export] *)
Lemma p_ro_addr : forall a : word,
  ro_addr psegs a = ((0x10000 <=? bv_unsigned a) && (bv_unsigned a <? 0xca000))%bool.
Proof.
  intros a. unfold ro_addr. rewrite p_find_segment_1 by (pose proof (bv_unsigned_in_range 64 a); lia).
  pose proof (bv_unsigned_in_range 64 a) as R.
  destruct (Z.leb_spec0 0x10000 (bv_unsigned a)); destruct (Z.leb_spec0 (bv_unsigned a + 1) 0x3a000);
  destruct (Z.leb_spec0 0x3a000 (bv_unsigned a)); destruct (Z.leb_spec0 (bv_unsigned a + 1) 0xca000);
  destruct (Z.leb_spec0 0xca000 (bv_unsigned a)); destruct (Z.leb_spec0 (bv_unsigned a + 1) 0xd0000);
  destruct (Z.leb_spec0 0xd0000 (bv_unsigned a)); destruct (Z.leb_spec0 (bv_unsigned a + 1) 0x105000);
  destruct (Z.ltb_spec0 (bv_unsigned a) 0xca000); cbn; try reflexivity; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ref_find_segment_none : forall z n, 1 <= n -> (z + n <= 0x10000 \/ 0x105000 <= z) ->
  find_segment psegs z n = None.
Proof.
  intros z n Hn Hz. unfold psegs, Plain.M.loaded_segments, Plain_loaded_segments. cbn [find_segment].
  replace (Z.of_N (seg_base Plain_segment_000)) with 0x10000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size Plain_segment_000)) with 0x2a000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_base Plain_segment_001)) with 0x3a000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size Plain_segment_001)) with 0x90000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_base Plain_segment_002)) with 0xca000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size Plain_segment_002)) with 0x6000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_base Plain_segment_003)) with 0xd0000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size Plain_segment_003)) with 0x35000 by (vm_compute; reflexivity).
  destruct (Z.leb_spec0 0x10000 z); destruct (Z.leb_spec0 (z + n) (0x10000 + 0x2a000)); cbn [andb]; try lia;
  destruct (Z.leb_spec0 0x3a000 z); destruct (Z.leb_spec0 (z + n) (0x3a000 + 0x90000)); cbn [andb]; try lia;
  destruct (Z.leb_spec0 0xca000 z); destruct (Z.leb_spec0 (z + n) (0xca000 + 0x6000)); cbn [andb]; try lia;
  destruct (Z.leb_spec0 0xd0000 z); destruct (Z.leb_spec0 (z + n) (0xd0000 + 0x35000)); cbn [andb]; try lia; reflexivity.
Qed.

Lemma ref_ro_addr_false : forall x : word,
  (bv_unsigned x + 1 <= 0x10000 \/ 0x105000 <= bv_unsigned x)%Z -> ro_addr psegs x = false.
Proof. intros x Hx. unfold ro_addr. rewrite ref_find_segment_none by lia. reflexivity. Qed.

Lemma ref_memory_read_none : forall (x : word) n,
  (1 <= Z.of_N n)%Z -> (bv_unsigned x + Z.of_N n <= 0x10000 \/ 0x105000 <= bv_unsigned x)%Z -> memory_read psegs x n = None.
Proof. intros x n Hn Hx. unfold memory_read. rewrite ref_find_segment_none by lia. reflexivity. Qed.

Lemma ref_wview_overlay : forall m (x : word),
  (bv_unsigned x + 1 <= 0x10000 \/ 0x105000 <= bv_unsigned x)%Z -> wview psegs m x = m x.
Proof.
  intros m x Hx. unfold wview. destruct (m x); [reflexivity|]. rewrite ref_find_segment_none by lia. reflexivity.
Qed.

Lemma ref_seg_rom_none : forall (x : word),
  (bv_unsigned x + 1 <= 0x10000 \/ 0x105000 <= bv_unsigned x)%Z -> seg_rom psegs x = None.
Proof. intros x Hx. unfold seg_rom. rewrite ref_memory_read_none by (cbn; lia). reflexivity. Qed.

Lemma ref_mrd_overlay : forall m (x : word),
  (bv_unsigned x + 1 <= 0x10000 \/ 0x105000 <= bv_unsigned x)%Z -> mrd psegs m x = m x.
Proof. intros m x Hx. unfold mrd. destruct (m x); [reflexivity|]. apply ref_seg_rom_none. exact Hx. Qed.

(* [comment removed for export] *)
Definition RPAGE_SIZE : Z := 0xe3738.    (* [comment removed for export] *)
Definition PREAD_STAGE : Z := 0xd1129.   (* [comment removed for export] *)
Definition RAUXV_CELL : Z := 0xe3710.    (* [comment removed for export] *)
Definition rmmap_entry : Z := 0xb7218.
Definition rmunmap_entry : Z := 0xb7420.
Definition rmprotect_entry : Z := 0xb7304.
