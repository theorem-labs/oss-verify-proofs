(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import PropExec MState Mem Image.
From OSSVerify.simdjson.fuzz_minifyimpl.images Require Export Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition usegs : list Segment := Ubsan.M.loaded_segments.
Definition u_init_pc : N := Ubsan.M.init_pc.
Definition u_phdrs : PhdrInfo := Ubsan.M.phdrs.

(* [comment removed for export] *)
Definition u_ro_lo   : Z := 0x10000.  Definition u_ro_hi   : Z := 0x3b000.
Definition u_text_lo : Z := 0x3b000.  Definition u_text_hi : Z := 0xd4000.
Definition u_rw1_lo  : Z := 0xd4000.  Definition u_rw1_hi  : Z := 0xdb000.
Definition u_rw2_lo  : Z := 0xdb000.  Definition u_rw2_hi  : Z := 0x110000.

(* [comment removed for export] *)
Definition ubsan_reserved : list (Z * Z) :=
  [(0x10000, 0x2b000); (0x3b000, 0x99000); (0xd4000, 0x7000); (0xdb000, 0x35000)].

Lemma reservedZ_ubsan : reservedZ usegs = ubsan_reserved.
Proof. vm_compute. reflexivity. Qed.

Lemma segments_reserved_ubsan :
  segments_reserved usegs =
  [(Z_to_bv 64 0x10000, Z_to_bv 64 0x2b000); (Z_to_bv 64 0x3b000, Z_to_bv 64 0x99000);
   (Z_to_bv 64 0xd4000, Z_to_bv 64 0x7000); (Z_to_bv 64 0xdb000, Z_to_bv 64 0x35000)].
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma reserved_top_ubsan : reserved_top (segments_reserved usegs) = 0x110000.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma u_seg_flags :
  map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s), seg_readable s, seg_writable s, seg_executable s)) usegs
  = [(0x10000, 0x2b000, true, false, false); (0x3b000, 0x99000, true, false, true);
     (0xd4000, 0x7000, true, true, false); (0xdb000, 0x35000, true, true, false)].
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma u_find_segment_1 : forall z, 0 <= z ->
  find_segment usegs z 1 =
    if (0x10000 <=? z) && (z + 1 <=? 0x3b000) then Some Ubsan_segment_000
    else if (0x3b000 <=? z) && (z + 1 <=? 0xd4000) then Some Ubsan_segment_001
    else if (0xd4000 <=? z) && (z + 1 <=? 0xdb000) then Some Ubsan_segment_002
    else if (0xdb000 <=? z) && (z + 1 <=? 0x110000) then Some Ubsan_segment_003
    else None.
Proof. intros z Hz. reflexivity. Qed.

(* [comment removed for export] *)
Lemma u_ro_addr : forall a : word,
  ro_addr usegs a = ((0x10000 <=? bv_unsigned a) && (bv_unsigned a <? 0xd4000))%bool.
Proof.
  intros a. unfold ro_addr. rewrite u_find_segment_1 by (pose proof (bv_unsigned_in_range 64 a); lia).
  pose proof (bv_unsigned_in_range 64 a) as R.
  destruct (Z.leb_spec0 0x10000 (bv_unsigned a)); destruct (Z.leb_spec0 (bv_unsigned a + 1) 0x3b000);
  destruct (Z.leb_spec0 0x3b000 (bv_unsigned a)); destruct (Z.leb_spec0 (bv_unsigned a + 1) 0xd4000);
  destruct (Z.leb_spec0 0xd4000 (bv_unsigned a)); destruct (Z.leb_spec0 (bv_unsigned a + 1) 0xdb000);
  destruct (Z.leb_spec0 0xdb000 (bv_unsigned a)); destruct (Z.leb_spec0 (bv_unsigned a + 1) 0x110000);
  destruct (Z.ltb_spec0 (bv_unsigned a) 0xd4000); cbn; try reflexivity; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ref_find_segment_none : forall z n, 1 <= n -> (z + n <= 0x10000 \/ 0x110000 <= z) ->
  find_segment usegs z n = None.
Proof.
  intros z n Hn Hz. unfold usegs, Ubsan.M.loaded_segments, Ubsan_loaded_segments. cbn [find_segment].
  replace (Z.of_N (seg_base Ubsan_segment_000)) with 0x10000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size Ubsan_segment_000)) with 0x2b000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_base Ubsan_segment_001)) with 0x3b000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size Ubsan_segment_001)) with 0x99000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_base Ubsan_segment_002)) with 0xd4000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size Ubsan_segment_002)) with 0x7000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_base Ubsan_segment_003)) with 0xdb000 by (vm_compute; reflexivity).
  replace (Z.of_N (seg_size Ubsan_segment_003)) with 0x35000 by (vm_compute; reflexivity).
  destruct (Z.leb_spec0 0x10000 z); destruct (Z.leb_spec0 (z + n) (0x10000 + 0x2b000)); cbn [andb]; try lia;
  destruct (Z.leb_spec0 0x3b000 z); destruct (Z.leb_spec0 (z + n) (0x3b000 + 0x99000)); cbn [andb]; try lia;
  destruct (Z.leb_spec0 0xd4000 z); destruct (Z.leb_spec0 (z + n) (0xd4000 + 0x7000)); cbn [andb]; try lia;
  destruct (Z.leb_spec0 0xdb000 z); destruct (Z.leb_spec0 (z + n) (0xdb000 + 0x35000)); cbn [andb]; try lia; reflexivity.
Qed.

Lemma ref_ro_addr_false : forall x : word,
  (bv_unsigned x + 1 <= 0x10000 \/ 0x110000 <= bv_unsigned x)%Z -> ro_addr usegs x = false.
Proof. intros x Hx. unfold ro_addr. rewrite ref_find_segment_none by lia. reflexivity. Qed.

Lemma ref_memory_read_none : forall (x : word) n,
  (1 <= Z.of_N n)%Z -> (bv_unsigned x + Z.of_N n <= 0x10000 \/ 0x110000 <= bv_unsigned x)%Z -> memory_read usegs x n = None.
Proof. intros x n Hn Hx. unfold memory_read. rewrite ref_find_segment_none by lia. reflexivity. Qed.

Lemma ref_wview_overlay : forall m (x : word),
  (bv_unsigned x + 1 <= 0x10000 \/ 0x110000 <= bv_unsigned x)%Z -> wview usegs m x = m x.
Proof.
  intros m x Hx. unfold wview. destruct (m x); [reflexivity|]. rewrite ref_find_segment_none by lia. reflexivity.
Qed.

Lemma ref_seg_rom_none : forall (x : word),
  (bv_unsigned x + 1 <= 0x10000 \/ 0x110000 <= bv_unsigned x)%Z -> seg_rom usegs x = None.
Proof. intros x Hx. unfold seg_rom. rewrite ref_memory_read_none by (cbn; lia). reflexivity. Qed.

Lemma ref_mrd_overlay : forall m (x : word),
  (bv_unsigned x + 1 <= 0x10000 \/ 0x110000 <= bv_unsigned x)%Z -> mrd usegs m x = m x.
Proof. intros m x Hx. unfold mrd. destruct (m x); [reflexivity|]. apply ref_seg_rom_none. exact Hx. Qed.

(* [comment removed for export] *)
Definition RPAGE_SIZE : Z := 0x10e818.    (* [comment removed for export] *)
Definition UREAD_STAGE : Z := 0xdc2a9.   (* [comment removed for export] *)
Definition RAUXV_CELL : Z := 0x10e7f0.    (* [comment removed for export] *)
Definition rmmap_entry : Z := 0xc1e7c.
Definition rmunmap_entry : Z := 0xc2084.
Definition rmprotect_entry : Z := 0xc1f68.
