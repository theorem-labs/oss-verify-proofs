(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem Image.
From OSSVerify.zstd.simple_decompress.images Require Export Plain.
Import ListNotations.
Open Scope Z_scope.

Definition psegs : list Segment := Plain.M.loaded_segments.
Definition p_init_pc : N := Plain.M.init_pc.
Definition p_phdrs : PhdrInfo := Plain.M.phdrs.

(* [comment removed for export] *)
Definition p_ro_lo   : Z := 0x10000.  Definition p_ro_hi   : Z := 0x14000.
Definition p_text_lo : Z := 0x14000.  Definition p_text_hi : Z := 0x30000.
Definition p_rw1_lo  : Z := 0x30000.  Definition p_rw1_hi  : Z := 0x31000.
Definition p_rw2_lo  : Z := 0x31000.  Definition p_rw2_hi  : Z := 0x63000.

(* [comment removed for export] *)
Definition plain_reserved : list (Z * Z) :=
  [(0x10000, 0x4000); (0x14000, 0x1c000); (0x30000, 0x1000); (0x31000, 0x32000)].

Lemma reservedZ_plain : reservedZ psegs = plain_reserved.
Proof. vm_compute. reflexivity. Qed.

Lemma segments_reserved_plain :
  segments_reserved psegs =
  [(Z_to_bv 64 0x10000, Z_to_bv 64 0x4000); (Z_to_bv 64 0x14000, Z_to_bv 64 0x1c000);
   (Z_to_bv 64 0x30000, Z_to_bv 64 0x1000); (Z_to_bv 64 0x31000, Z_to_bv 64 0x32000)].
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma reserved_top_plain : reserved_top (segments_reserved psegs) = 0x63000.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma p_seg_flags :
  map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s), seg_readable s, seg_writable s, seg_executable s)) psegs
  = [(0x10000, 0x4000, true, false, false); (0x14000, 0x1c000, true, false, true);
     (0x30000, 0x1000, true, true, false); (0x31000, 0x32000, true, true, false)].
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma p_find_segment_1 : forall z, 0 <= z ->
  find_segment psegs z 1 =
    if (0x10000 <=? z) && (z + 1 <=? 0x14000) then Some Plain_segment_000
    else if (0x14000 <=? z) && (z + 1 <=? 0x30000) then Some Plain_segment_001
    else if (0x30000 <=? z) && (z + 1 <=? 0x31000) then Some Plain_segment_002
    else if (0x31000 <=? z) && (z + 1 <=? 0x63000) then Some Plain_segment_003
    else None.
Proof. intros z Hz. reflexivity. Qed.

(* [comment removed for export] *)
Lemma p_ro_addr : forall a : word,
  ro_addr psegs a = ((0x10000 <=? bv_unsigned a) && (bv_unsigned a <? 0x30000))%bool.
Proof.
  intros a. unfold ro_addr. rewrite p_find_segment_1 by (pose proof (bv_unsigned_in_range 64 a); lia).
  pose proof (bv_unsigned_in_range 64 a) as R.
  destruct (Z.leb_spec0 0x10000 (bv_unsigned a)); destruct (Z.leb_spec0 (bv_unsigned a + 1) 0x14000);
  destruct (Z.leb_spec0 0x14000 (bv_unsigned a)); destruct (Z.leb_spec0 (bv_unsigned a + 1) 0x30000);
  destruct (Z.leb_spec0 0x30000 (bv_unsigned a)); destruct (Z.leb_spec0 (bv_unsigned a + 1) 0x31000);
  destruct (Z.leb_spec0 0x31000 (bv_unsigned a)); destruct (Z.leb_spec0 (bv_unsigned a + 1) 0x63000);
  destruct (Z.ltb_spec0 (bv_unsigned a) 0x30000); cbn; try reflexivity; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ref_find_segment_none : forall z n, 1 <= n -> (z + n <= 0x10000 \/ 0x63000 <= z) ->
  find_segment psegs z n = None.
Proof.
  intros z n Hn Hz. unfold psegs, Plain.M.loaded_segments, Plain_loaded_segments. cbn [find_segment].
  replace (Z.of_N (seg_base Plain_segment_000)) with 0x10000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size Plain_segment_000)) with 0x4000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_base Plain_segment_001)) with 0x14000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size Plain_segment_001)) with 0x1c000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_base Plain_segment_002)) with 0x30000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size Plain_segment_002)) with 0x1000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_base Plain_segment_003)) with 0x31000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size Plain_segment_003)) with 0x32000 by (vm_compute; reflexivity).
  destruct (Z.leb_spec0 0x10000 z); destruct (Z.leb_spec0 (z + n) (0x10000 + 0x4000)); cbn [andb]; try lia;
  destruct (Z.leb_spec0 0x14000 z); destruct (Z.leb_spec0 (z + n) (0x14000 + 0x1c000)); cbn [andb]; try lia;
  destruct (Z.leb_spec0 0x30000 z); destruct (Z.leb_spec0 (z + n) (0x30000 + 0x1000)); cbn [andb]; try lia;
  destruct (Z.leb_spec0 0x31000 z); destruct (Z.leb_spec0 (z + n) (0x31000 + 0x32000)); cbn [andb]; try lia; reflexivity.
Qed.

Lemma ref_ro_addr_false : forall x : word,
  (bv_unsigned x + 1 <= 0x10000 \/ 0x63000 <= bv_unsigned x)%Z -> ro_addr psegs x = false.
Proof. intros x Hx. unfold ro_addr. rewrite ref_find_segment_none by lia. reflexivity. Qed.

Lemma ref_memory_read_none : forall (x : word) n,
  (1 <= Z.of_N n)%Z -> (bv_unsigned x + Z.of_N n <= 0x10000 \/ 0x63000 <= bv_unsigned x)%Z -> memory_read psegs x n = None.
Proof. intros x n Hn Hx. unfold memory_read. rewrite ref_find_segment_none by lia. reflexivity. Qed.

Lemma ref_wview_overlay : forall m (x : word),
  (bv_unsigned x + 1 <= 0x10000 \/ 0x63000 <= bv_unsigned x)%Z -> wview psegs m x = m x.
Proof.
  intros m x Hx. unfold wview. destruct (m x); [reflexivity|]. rewrite ref_find_segment_none by lia. reflexivity.
Qed.

Lemma ref_seg_rom_none : forall (x : word),
  (bv_unsigned x + 1 <= 0x10000 \/ 0x63000 <= bv_unsigned x)%Z -> seg_rom psegs x = None.
Proof. intros x Hx. unfold seg_rom. rewrite ref_memory_read_none by (cbn; lia). reflexivity. Qed.

Lemma ref_mrd_overlay : forall m (x : word),
  (bv_unsigned x + 1 <= 0x10000 \/ 0x63000 <= bv_unsigned x)%Z -> mrd psegs m x = m x.
Proof. intros m x Hx. unfold mrd. destruct (m x); [reflexivity|]. apply ref_seg_rom_none. exact Hx. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition RPAGE_SIZE : Z := 0x62378.    (* [comment removed for export] *)
Definition PREAD_STAGE : Z := 0x31fa9.   (* [comment removed for export] *)
Definition RAUXV_CELL : Z := 0x62350.    (* [comment removed for export] *)
Definition rmmap_entry : Z := 0x29b60.
Definition rmunmap_entry : Z := 0x29c94.
Definition rmprotect_entry : Z := 0x29c4c.
