(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec Hoare AgentLib.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import MallocLayout.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Module ImgU16 := Ubsan.

(* [comment removed for export] *)
Instance LU16 : MallocLayout := {|
  ml_segs := ImgU16.M.loaded_segments;
  IMG_LO := 0x10000; RW_LO := 0x123000; IMG_HI := 0x159000;

  A_LOCK           := Z_to_bv 64 0x1584d0;
  A_CTX            := Z_to_bv 64 0x1584d8;
  A_INIT_DONE      := Z_to_bv 64 0x1584e0;
  A_MMAP_CTR       := Z_to_bv 64 0x1584e4;
  A_FREE_META_HEAD := Z_to_bv 64 0x1584e8;
  A_AVAIL_META     := Z_to_bv 64 0x1584f0;
  A_AVAIL_META_CNT := Z_to_bv 64 0x1584f8;
  A_AVAIL_AREA_CNT := Z_to_bv 64 0x158500;
  A_META_SHIFT     := Z_to_bv 64 0x158508;
  A_AREA_HEAD      := Z_to_bv 64 0x158510;
  A_AREA_TAIL      := Z_to_bv 64 0x158518;
  A_AVAIL_AREAS    := Z_to_bv 64 0x158520;
  Z_UNMAP_SEQ      := 0x158828;
  Z_BOUNCES        := 0x158848;
  A_SEQ            := Z_to_bv 64 0x158868;
  A_BRK            := Z_to_bv 64 0x158870;
  A_MALLOC_REPLACED := Z_to_bv 64 0x158878;

  A_LIBC       := Z_to_bv 64 0x158460;
  A_NEED_LOCKS := Z_to_bv 64 0x158463;
  A_PAGE_SIZE  := Z_to_bv 64 0x158490;
  A_TP         := Z_to_bv 64 0x1381d0;
  A_ERRNO      := Z_to_bv 64 0x13812c;
  A_GOT_SSP    := Z_to_bv 64 0x126c00;
  A_SSP        := Z_to_bv 64 0x158440;

  A_SIZE_CLASSES  := Z_to_bv 64 0x4de38;
  A_SMALL_CNT_TAB := Z_to_bv 64 0x4de98;
  A_MED_CNT_TAB   := Z_to_bv 64 0x1f12c;
  A_DEBRUIJN      := Z_to_bv 64 0x1f668;

  PC_MALLOC      := (0x10e958%bv : word);
  PC_FREE        := (0x10e818%bv : word);
  PC_CALLOC      := (0x10e6e0%bv : word);
  PC_LIBC_FREE   := (0x10e95c%bv : word);
  PC_MALLOC_IMPL := (0x10f2e8%bv : word);
  PC_GET_META    := (0x10eb28%bv : word);
  PC_NTFREE      := (0x10ec38%bv : word);
  PC_ALLOC_META  := (0x10f010%bv : word);
  PC_ALLOC_SLOT  := (0x10f658%bv : word);
  PC_ENFRAME     := (0x10fefc%bv : word);
  PC_ALLZEROP    := (0x11004c%bv : word);
  PC_MMAP        := (0x111b44%bv : word);
  PC_MPROTECT    := (0x111c30%bv : word);
  PC_MUNMAP      := (0x111d4c%bv : word);
  PC_VM_WAIT     := (0x111b40%bv : word);
  PC_SYSCALL_RET := (0x10e6a0%bv : word);
  PC_ERRNO_LOC   := (0x10e1d4%bv : word);
  PC_LOCK        := (0x11ecd8%bv : word);
  PC_UNLOCK      := (0x11ef60%bv : word);
  PC_MEMCPY      := (0x11e154%bv : word);
  PC_MEMSET      := (0x11e6d4%bv : word)
|}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Local Abbreviation SEG0 := ImgU16.Ubsan_segment_000.
Local Abbreviation SEG1 := ImgU16.Ubsan_segment_001.
Local Abbreviation SEG2 := ImgU16.Ubsan_segment_002.
Local Abbreviation SEG3 := ImgU16.Ubsan_segment_003.
(* [comment removed for export] *)
Local Abbreviation B0 := 0x10000.  Local Abbreviation B1 := 0x62000.  Local Abbreviation B2 := 0x123000.
Local Abbreviation B3 := 0x127000.  Local Abbreviation B4 := 0x159000.
Local Abbreviation P0 := 82%nat.  Local Abbreviation P1 := 193%nat.  Local Abbreviation P2 := 4%nat.  Local Abbreviation P3 := 50%nat.

Lemma u16_segs : ml_segs = [SEG0; SEG1; SEG2; SEG3].
Proof.
reflexivity. Qed.

Lemma u16_bases :
  Z.of_N (seg_base SEG0) = B0 /\ Z.of_N (seg_base SEG0) + Z.of_N (seg_size SEG0) = B1 /\
  Z.of_N (seg_base SEG1) = B1 /\ Z.of_N (seg_base SEG1) + Z.of_N (seg_size SEG1) = B2 /\
  Z.of_N (seg_base SEG2) = B2 /\ Z.of_N (seg_base SEG2) + Z.of_N (seg_size SEG2) = B3 /\
  Z.of_N (seg_base SEG3) = B3 /\ Z.of_N (seg_base SEG3) + Z.of_N (seg_size SEG3) = B4.
Proof.
repeat split; reflexivity. Qed.

(* [comment removed for export] *)
Lemma u16_find_none : forall a, (a < B0 \/ B4 <= a) -> find_segment ml_segs a 1 = None.
Proof.
intros a Ha. rewrite u16_segs. apply find_segment_none. pose proof u16_bases as B.
  repeat (apply Forall_cons || apply Forall_nil); unfold seg_misses; lia. Qed.

Lemma u16_find_seg0 : forall a, B0 <= a -> a + 1 <= B1 -> find_segment ml_segs a 1 = Some SEG0.
Proof.
intros a H1 H2. rewrite u16_segs. pose proof u16_bases as B.
  apply (find_segment_hit [] SEG0 [SEG1; SEG2; SEG3] a 1); [apply Forall_nil | lia | lia]. Qed.
Lemma u16_find_seg1 : forall a, B1 <= a -> a + 1 <= B2 -> find_segment ml_segs a 1 = Some SEG1.
Proof.
intros a H1 H2. rewrite u16_segs. pose proof u16_bases as B.
  apply (find_segment_hit [SEG0] SEG1 [SEG2; SEG3] a 1); [| lia | lia].
  repeat (apply Forall_cons || apply Forall_nil); unfold seg_misses; lia. Qed.
Lemma u16_find_seg2 : forall a, B2 <= a -> a + 1 <= B3 -> find_segment ml_segs a 1 = Some SEG2.
Proof.
intros a H1 H2. rewrite u16_segs. pose proof u16_bases as B.
  apply (find_segment_hit [SEG0; SEG1] SEG2 [SEG3] a 1); [| lia | lia].
  repeat (apply Forall_cons || apply Forall_nil); unfold seg_misses; lia. Qed.
Lemma u16_find_seg3 : forall a, B3 <= a -> a + 1 <= B4 -> find_segment ml_segs a 1 = Some SEG3.
Proof.
intros a H1 H2. rewrite u16_segs. pose proof u16_bases as B.
  apply (find_segment_hit [SEG0; SEG1; SEG2] SEG3 [] a 1); [| lia | lia].
  repeat (apply Forall_cons || apply Forall_nil); unfold seg_misses; lia. Qed.

(* [comment removed for export] *)
Definition chk_seg_byte (seg : Segment) (off : Z) : bool :=
  match segment_byte_at (seg_bytes seg) (Z.to_N off) with Some _ => true | None => false end.

Lemma u16_seg0_bytes : chk_range (chk_seg_byte SEG0) 0 P0 = true.
Proof.
vm_compute. reflexivity. Qed.
Lemma u16_seg1_bytes : chk_range (chk_seg_byte SEG1) 0 P1 = true.
Proof.
vm_compute. reflexivity. Qed.
Lemma u16_seg2_bytes : chk_range (chk_seg_byte SEG2) 0 P2 = true.
Proof.
vm_compute. reflexivity. Qed.
Lemma u16_seg3_bytes : chk_range (chk_seg_byte SEG3) 0 P3 = true.
Proof.
vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition chk_rom_zero (a : Z) : bool :=
  match seg_rom ml_segs (Z_to_bv 64 a) with Some v => bv_unsigned v =? 0 | None => false end.
Lemma u16_ctx_zero : chk_list chk_rom_zero (bv_unsigned A_LOCK) 940 = true.
Proof.
vm_compute. reflexivity. Qed.

Lemma u16_tables :
  chk_rom_bytes (seg_rom ml_segs) (bv_unsigned A_SIZE_CLASSES) (flat_map (fun c => [c mod 256; c / 256]) size_classes_tab) = true
  /\ chk_rom_bytes (seg_rom ml_segs) (bv_unsigned A_DEBRUIJN) debruijn32_tab = true
  /\ chk_rom_bytes (seg_rom ml_segs) (bv_unsigned A_SMALL_CNT_TAB) small_cnt_tab = true
  /\ chk_rom_bytes (seg_rom ml_segs) (bv_unsigned A_MED_CNT_TAB) med_cnt_tab = true
  /\ chk_rom_bytes (seg_rom ml_segs) (bv_unsigned A_GOT_SSP) (map (fun i => (bv_unsigned A_SSP / 2^(8*i)) mod 256) [0;1;2;3;4;5;6;7]) = true.
Proof.
vm_compute. repeat split; reflexivity. Qed.

Lemma Forall_map_mod256 : forall (l : list Z) (f : Z -> Z),
  Forall (fun b => 0 <= b < 256) (map (fun x => f x mod 256) l).
Proof.
intros l f. induction l; cbn; constructor; [apply Z.mod_pos_bound; lia | assumption]. Qed.

Lemma Forall_lt256_of_chk : forall l, forallb (fun b => (0 <=? b) && (b <? 256)) l = true -> Forall (fun b => 0 <= b < 256) l.
Proof.
intros l H. rewrite forallb_forall in H. apply Forall_forall. intros x Hx.
  specialize (H x Hx). apply andb_prop in H. destruct H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia. Qed.

Instance LU17ok : MallocLayoutOk LU16.
Proof.
  pose proof u16_bases as B.
  split.
  -  cbn. lia.
  -  intros a Ha. apply seg_rom_none_of_find. apply u16_find_none. exact Ha.
  -  intros m a Ha. apply wview_of_find_none. apply u16_find_none. exact Ha.
  -  intros m a Ha. cbn in Ha.
    destruct (Z.lt_ge_cases (bv_unsigned a) B1).
    + apply (wview_of_find_ro _ m a SEG0); [apply u16_find_seg0; lia | reflexivity].
    + apply (wview_of_find_ro _ m a SEG1); [apply u16_find_seg1; lia | reflexivity].
  -  intros m a Ha. cbn in Ha.
    destruct (Z.lt_ge_cases (bv_unsigned a) B3).
    + apply (wview_of_find_rw _ m a SEG2); [apply u16_find_seg2; lia | reflexivity |].
      pose proof (chk_range_sound _ _ _ u16_seg2_bytes (bv_unsigned a - B2) ltac:(lia)) as Hc.
      unfold chk_seg_byte in Hc. rewrite (proj1 (proj2 (proj2 (proj2 (proj2 B))))).
      destruct (segment_byte_at (seg_bytes SEG2) (Z.to_N (bv_unsigned a - B2))); [discriminate | discriminate].
    + apply (wview_of_find_rw _ m a SEG3); [apply u16_find_seg3; lia | reflexivity |].
      pose proof (chk_range_sound _ _ _ u16_seg3_bytes (bv_unsigned a - B3) ltac:(lia)) as Hc.
      unfold chk_seg_byte in Hc. rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 B))))))).
      destruct (segment_byte_at (seg_bytes SEG3) (Z.to_N (bv_unsigned a - B3))); [discriminate | discriminate].
  -  intros a Ha. cbn in Ha.
    destruct (Z.lt_ge_cases (bv_unsigned a) B1); [| destruct (Z.lt_ge_cases (bv_unsigned a) B2); [| destruct (Z.lt_ge_cases (bv_unsigned a) B3)]].
    + apply (seg_rom_some_of_find _ a SEG0); [apply u16_find_seg0; lia | reflexivity |].
      pose proof (chk_range_sound _ _ _ u16_seg0_bytes (bv_unsigned a - B0) ltac:(lia)) as Hc.
      unfold chk_seg_byte in Hc. rewrite (proj1 B).
      destruct (segment_byte_at (seg_bytes SEG0) (Z.to_N (bv_unsigned a - B0))); [discriminate | discriminate].
    + apply (seg_rom_some_of_find _ a SEG1); [apply u16_find_seg1; lia | reflexivity |].
      pose proof (chk_range_sound _ _ _ u16_seg1_bytes (bv_unsigned a - B1) ltac:(lia)) as Hc.
      unfold chk_seg_byte in Hc. rewrite (proj1 (proj2 (proj2 B))).
      destruct (segment_byte_at (seg_bytes SEG1) (Z.to_N (bv_unsigned a - B1))); [discriminate | discriminate].
    + apply (seg_rom_some_of_find _ a SEG2); [apply u16_find_seg2; lia | reflexivity |].
      pose proof (chk_range_sound _ _ _ u16_seg2_bytes (bv_unsigned a - B2) ltac:(lia)) as Hc.
      unfold chk_seg_byte in Hc. rewrite (proj1 (proj2 (proj2 (proj2 (proj2 B))))).
      destruct (segment_byte_at (seg_bytes SEG2) (Z.to_N (bv_unsigned a - B2))); [discriminate | discriminate].
    + apply (seg_rom_some_of_find _ a SEG3); [apply u16_find_seg3; lia | reflexivity |].
      pose proof (chk_range_sound _ _ _ u16_seg3_bytes (bv_unsigned a - B3) ltac:(lia)) as Hc.
      unfold chk_seg_byte in Hc. rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 B))))))).
      destruct (segment_byte_at (seg_bytes SEG3) (Z.to_N (bv_unsigned a - B3))); [discriminate | discriminate].
  -  intros b sz Hin. cbv -[Z_to_bv] in Hin.
    destruct Hin as [E|[E|[E|[E|[]]]]]; injection E as <- <-; rewrite !u64_lit by lia; cbn; lia.
  -  intros a Ha. cbn in Ha.
    destruct (Z.lt_ge_cases a B1); [| destruct (Z.lt_ge_cases a B2); [| destruct (Z.lt_ge_cases a B3)]].
    + exists (Z_to_bv 64 B0), (Z_to_bv 64 (B1 - B0)). split; [cbv -[Z_to_bv]; tauto | rewrite !u64_lit by lia; lia].
    + exists (Z_to_bv 64 B1), (Z_to_bv 64 (B2 - B1)). split; [cbv -[Z_to_bv]; tauto | rewrite !u64_lit by lia; lia].
    + exists (Z_to_bv 64 B2), (Z_to_bv 64 (B3 - B2)). split; [cbv -[Z_to_bv]; tauto | rewrite !u64_lit by lia; lia].
    + exists (Z_to_bv 64 B3), (Z_to_bv 64 (B4 - B3)). split; [cbv -[Z_to_bv]; tauto | rewrite !u64_lit by lia; lia].
  -  vm_compute. reflexivity.
  -  reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  -  reflexivity.
  -  reflexivity.
  - reflexivity.
  - reflexivity.
  -  reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  -  cbn; rewrite !u64_lit by lia; lia.
  - cbn; rewrite !u64_lit by lia; lia.
  - cbn; rewrite !u64_lit by lia; lia.
  - cbn; rewrite !u64_lit by lia; lia.
  - cbn; rewrite !u64_lit by lia; lia.
  - unfold CTX_SIZE; cbn; rewrite !u64_lit by lia; lia.
  - cbn; rewrite !u64_lit by lia; lia.
  -  apply chk_rom_bytes_sound; [apply Forall_map_mod256 | exact (proj2 (proj2 (proj2 (proj2 u16_tables))))].
  -  intros a Ha. cbn in Ha. rewrite !u64_lit in Ha by lia.
    pose proof (chk_list_sound _ _ _ u16_ctx_zero (bv_unsigned a) ltac:(cbn; rewrite !u64_lit by lia; lia)) as Hc.
    unfold chk_rom_zero in Hc. rewrite Z_to_bv_bv_unsigned in Hc.
    destruct (seg_rom ml_segs a) as [v|]; [|discriminate]. apply Z.eqb_eq in Hc.
    f_equal. rewrite <- (Z_to_bv_bv_unsigned 8 v). rewrite Hc. reflexivity.
  -  cbn; rewrite !u64_lit by lia; lia.
  - reflexivity.
  - apply chk_rom_bytes_sound; [apply Forall_lt256_of_chk; vm_compute; reflexivity | exact (proj1 u16_tables)].
  - apply chk_rom_bytes_sound; [apply Forall_lt256_of_chk; vm_compute; reflexivity | exact (proj1 (proj2 u16_tables))].
  - apply chk_rom_bytes_sound; [apply Forall_lt256_of_chk; vm_compute; reflexivity | exact (proj1 (proj2 (proj2 u16_tables)))].
  - apply chk_rom_bytes_sound; [apply Forall_lt256_of_chk; vm_compute; reflexivity | exact (proj1 (proj2 (proj2 (proj2 u16_tables))))].
  -  repeat (apply Forall_cons || apply Forall_nil); cbv; repeat split; congruence.
Qed.
