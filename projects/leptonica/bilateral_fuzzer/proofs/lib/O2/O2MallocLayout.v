(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.leptonica.bilateral_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec Hoare AgentLib.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Mallocng Require Import MallocLayout.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Module ImgS16 := Plain.

(* [comment removed for export] *)
Instance LS16 : MallocLayout := {|
  ml_segs := ImgS16.M.loaded_segments;
  IMG_LO := 0x10000; RW_LO := 0x38000; IMG_HI := 0x6b000;

  A_LOCK           := Z_to_bv 64 0x69b38;
  A_CTX            := Z_to_bv 64 0x69b40;
  A_INIT_DONE      := Z_to_bv 64 0x69b48;
  A_MMAP_CTR       := Z_to_bv 64 0x69b4c;
  A_FREE_META_HEAD := Z_to_bv 64 0x69b50;
  A_AVAIL_META     := Z_to_bv 64 0x69b58;
  A_AVAIL_META_CNT := Z_to_bv 64 0x69b60;
  A_AVAIL_AREA_CNT := Z_to_bv 64 0x69b68;
  A_META_SHIFT     := Z_to_bv 64 0x69b70;
  A_AREA_HEAD      := Z_to_bv 64 0x69b78;
  A_AREA_TAIL      := Z_to_bv 64 0x69b80;
  A_AVAIL_AREAS    := Z_to_bv 64 0x69b88;
  Z_UNMAP_SEQ      := 0x69e90;
  Z_BOUNCES        := 0x69eb0;
  A_SEQ            := Z_to_bv 64 0x69ed0;
  A_BRK            := Z_to_bv 64 0x69ed8;
  A_MALLOC_REPLACED := Z_to_bv 64 0x69ee0;

  A_LIBC       := Z_to_bv 64 0x69ac8;
  A_NEED_LOCKS := Z_to_bv 64 0x69acb;
  A_PAGE_SIZE  := Z_to_bv 64 0x69af8;
  A_TP         := Z_to_bv 64 0x49840;
  A_ERRNO      := Z_to_bv 64 0x4979c;
  A_GOT_SSP    := Z_to_bv 64 0x384a0;
  A_SSP        := Z_to_bv 64 0x69aa8;

  A_SIZE_CLASSES  := Z_to_bv 64 0x132e4;
  A_SMALL_CNT_TAB := Z_to_bv 64 0x13344;
  A_MED_CNT_TAB   := Z_to_bv 64 0x12774;
  A_DEBRUIJN      := Z_to_bv 64 0x132c4;

  PC_MALLOC      := (0x2f94c%bv : word);
  PC_FREE        := (0x2f80c%bv : word);
  PC_CALLOC      := (0x2f6d4%bv : word);
  PC_LIBC_FREE   := (0x2f950%bv : word);
  PC_MALLOC_IMPL := (0x302dc%bv : word);
  PC_GET_META    := (0x2fb1c%bv : word);
  PC_NTFREE      := (0x2fc2c%bv : word);
  PC_ALLOC_META  := (0x30004%bv : word);
  PC_ALLOC_SLOT  := (0x3064c%bv : word);
  PC_ENFRAME     := (0x30ef0%bv : word);
  PC_ALLZEROP    := (0x31040%bv : word);
  PC_MMAP        := (0x3136c%bv : word);
  PC_MPROTECT    := (0x31458%bv : word);
  PC_MUNMAP      := (0x314a0%bv : word);
  PC_VM_WAIT     := (0x31368%bv : word);
  PC_SYSCALL_RET := (0x2f694%bv : word);
  PC_ERRNO_LOC   := (0x2f28c%bv : word);
  PC_LOCK        := (0x37028%bv : word);
  PC_UNLOCK      := (0x372b0%bv : word);
  PC_MEMCPY      := (0x36a58%bv : word);
  PC_MEMSET      := (0x36e5c%bv : word)
|}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Local Abbreviation SEG0 := ImgS16.Plain_segment_000.
Local Abbreviation SEG1 := ImgS16.Plain_segment_001.
Local Abbreviation SEG2 := ImgS16.Plain_segment_002.
Local Abbreviation SEG3 := ImgS16.Plain_segment_003.
(* [comment removed for export] *)
Local Abbreviation B0 := 0x10000.  Local Abbreviation B1 := 0x17000.  Local Abbreviation B2 := 0x38000.
Local Abbreviation B3 := 0x39000.  Local Abbreviation B4 := 0x6b000.
Local Abbreviation P0 := 7%nat.  Local Abbreviation P1 := 33%nat.  Local Abbreviation P2 := 1%nat.  Local Abbreviation P3 := 50%nat.

Lemma s16_segs : ml_segs = [SEG0; SEG1; SEG2; SEG3].
Proof. reflexivity. Qed.

Lemma s16_bases :
  Z.of_N (seg_base SEG0) = B0 /\ Z.of_N (seg_base SEG0) + Z.of_N (seg_size SEG0) = B1 /\
  Z.of_N (seg_base SEG1) = B1 /\ Z.of_N (seg_base SEG1) + Z.of_N (seg_size SEG1) = B2 /\
  Z.of_N (seg_base SEG2) = B2 /\ Z.of_N (seg_base SEG2) + Z.of_N (seg_size SEG2) = B3 /\
  Z.of_N (seg_base SEG3) = B3 /\ Z.of_N (seg_base SEG3) + Z.of_N (seg_size SEG3) = B4.
Proof. repeat split; reflexivity. Qed.

(* [comment removed for export] *)
Lemma s16_find_none : forall a, (a < B0 \/ B4 <= a) -> find_segment ml_segs a 1 = None.
Proof.
  intros a Ha. rewrite s16_segs. apply find_segment_none. pose proof s16_bases as B.
  repeat (apply Forall_cons || apply Forall_nil); unfold seg_misses; lia.
Qed.

Lemma s16_find_seg0 : forall a, B0 <= a -> a + 1 <= B1 -> find_segment ml_segs a 1 = Some SEG0.
Proof.
  intros a H1 H2. rewrite s16_segs. pose proof s16_bases as B.
  apply (find_segment_hit [] SEG0 [SEG1; SEG2; SEG3] a 1); [apply Forall_nil | lia | lia].
Qed.
Lemma s16_find_seg1 : forall a, B1 <= a -> a + 1 <= B2 -> find_segment ml_segs a 1 = Some SEG1.
Proof.
  intros a H1 H2. rewrite s16_segs. pose proof s16_bases as B.
  apply (find_segment_hit [SEG0] SEG1 [SEG2; SEG3] a 1); [| lia | lia].
  repeat (apply Forall_cons || apply Forall_nil); unfold seg_misses; lia.
Qed.
Lemma s16_find_seg2 : forall a, B2 <= a -> a + 1 <= B3 -> find_segment ml_segs a 1 = Some SEG2.
Proof.
  intros a H1 H2. rewrite s16_segs. pose proof s16_bases as B.
  apply (find_segment_hit [SEG0; SEG1] SEG2 [SEG3] a 1); [| lia | lia].
  repeat (apply Forall_cons || apply Forall_nil); unfold seg_misses; lia.
Qed.
Lemma s16_find_seg3 : forall a, B3 <= a -> a + 1 <= B4 -> find_segment ml_segs a 1 = Some SEG3.
Proof.
  intros a H1 H2. rewrite s16_segs. pose proof s16_bases as B.
  apply (find_segment_hit [SEG0; SEG1; SEG2] SEG3 [] a 1); [| lia | lia].
  repeat (apply Forall_cons || apply Forall_nil); unfold seg_misses; lia.
Qed.

(* [comment removed for export] *)
Definition chk_seg_byte (seg : Segment) (off : Z) : bool :=
  match segment_byte_at (seg_bytes seg) (Z.to_N off) with Some _ => true | None => false end.

Lemma s16_seg0_bytes : chk_range (chk_seg_byte SEG0) 0 P0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma s16_seg1_bytes : chk_range (chk_seg_byte SEG1) 0 P1 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma s16_seg2_bytes : chk_range (chk_seg_byte SEG2) 0 P2 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma s16_seg3_bytes : chk_range (chk_seg_byte SEG3) 0 P3 = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition chk_rom_zero (a : Z) : bool :=
  match seg_rom ml_segs (Z_to_bv 64 a) with Some v => bv_unsigned v =? 0 | None => false end.
Lemma s16_ctx_zero : chk_list chk_rom_zero (bv_unsigned A_LOCK) 940 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma s16_tables :
  chk_rom_bytes (seg_rom ml_segs) (bv_unsigned A_SIZE_CLASSES) (flat_map (fun c => [c mod 256; c / 256]) size_classes_tab) = true
  /\ chk_rom_bytes (seg_rom ml_segs) (bv_unsigned A_DEBRUIJN) debruijn32_tab = true
  /\ chk_rom_bytes (seg_rom ml_segs) (bv_unsigned A_SMALL_CNT_TAB) small_cnt_tab = true
  /\ chk_rom_bytes (seg_rom ml_segs) (bv_unsigned A_MED_CNT_TAB) med_cnt_tab = true
  /\ chk_rom_bytes (seg_rom ml_segs) (bv_unsigned A_GOT_SSP) (map (fun i => (bv_unsigned A_SSP / 2^(8*i)) mod 256) [0;1;2;3;4;5;6;7]) = true.
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma Forall_map_mod256 : forall (l : list Z) (f : Z -> Z),
  Forall (fun b => 0 <= b < 256) (map (fun x => f x mod 256) l).
Proof. intros l f. induction l; cbn; constructor; [apply Z.mod_pos_bound; lia | assumption]. Qed.

Lemma Forall_lt256_of_chk : forall l, forallb (fun b => (0 <=? b) && (b <? 256)) l = true -> Forall (fun b => 0 <= b < 256) l.
Proof.
  intros l H. rewrite forallb_forall in H. apply Forall_forall. intros x Hx.
  specialize (H x Hx). apply andb_prop in H. destruct H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.

Instance LS17ok : MallocLayoutOk LS16.
Proof.
  pose proof s16_bases as B.
  split.
  -  cbn. lia.
  -  intros a Ha. apply seg_rom_none_of_find. apply s16_find_none. exact Ha.
  -  intros m a Ha. apply wview_of_find_none. apply s16_find_none. exact Ha.
  -  intros m a Ha. cbn in Ha.
    destruct (Z.lt_ge_cases (bv_unsigned a) B1).
    + apply (wview_of_find_ro _ m a SEG0); [apply s16_find_seg0; lia | reflexivity].
    + apply (wview_of_find_ro _ m a SEG1); [apply s16_find_seg1; lia | reflexivity].
  -  intros m a Ha. cbn in Ha.
    destruct (Z.lt_ge_cases (bv_unsigned a) B3).
    + apply (wview_of_find_rw _ m a SEG2); [apply s16_find_seg2; lia | reflexivity |].
      pose proof (chk_range_sound _ _ _ s16_seg2_bytes (bv_unsigned a - B2) ltac:(lia)) as Hc.
      unfold chk_seg_byte in Hc. rewrite (proj1 (proj2 (proj2 (proj2 (proj2 B))))).
      destruct (segment_byte_at (seg_bytes SEG2) (Z.to_N (bv_unsigned a - B2))); [discriminate | discriminate].
    + apply (wview_of_find_rw _ m a SEG3); [apply s16_find_seg3; lia | reflexivity |].
      pose proof (chk_range_sound _ _ _ s16_seg3_bytes (bv_unsigned a - B3) ltac:(lia)) as Hc.
      unfold chk_seg_byte in Hc. rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 B))))))).
      destruct (segment_byte_at (seg_bytes SEG3) (Z.to_N (bv_unsigned a - B3))); [discriminate | discriminate].
  -  intros a Ha. cbn in Ha.
    destruct (Z.lt_ge_cases (bv_unsigned a) B1); [| destruct (Z.lt_ge_cases (bv_unsigned a) B2); [| destruct (Z.lt_ge_cases (bv_unsigned a) B3)]].
    + apply (seg_rom_some_of_find _ a SEG0); [apply s16_find_seg0; lia | reflexivity |].
      pose proof (chk_range_sound _ _ _ s16_seg0_bytes (bv_unsigned a - B0) ltac:(lia)) as Hc.
      unfold chk_seg_byte in Hc. rewrite (proj1 B).
      destruct (segment_byte_at (seg_bytes SEG0) (Z.to_N (bv_unsigned a - B0))); [discriminate | discriminate].
    + apply (seg_rom_some_of_find _ a SEG1); [apply s16_find_seg1; lia | reflexivity |].
      pose proof (chk_range_sound _ _ _ s16_seg1_bytes (bv_unsigned a - B1) ltac:(lia)) as Hc.
      unfold chk_seg_byte in Hc. rewrite (proj1 (proj2 (proj2 B))).
      destruct (segment_byte_at (seg_bytes SEG1) (Z.to_N (bv_unsigned a - B1))); [discriminate | discriminate].
    + apply (seg_rom_some_of_find _ a SEG2); [apply s16_find_seg2; lia | reflexivity |].
      pose proof (chk_range_sound _ _ _ s16_seg2_bytes (bv_unsigned a - B2) ltac:(lia)) as Hc.
      unfold chk_seg_byte in Hc. rewrite (proj1 (proj2 (proj2 (proj2 (proj2 B))))).
      destruct (segment_byte_at (seg_bytes SEG2) (Z.to_N (bv_unsigned a - B2))); [discriminate | discriminate].
    + apply (seg_rom_some_of_find _ a SEG3); [apply s16_find_seg3; lia | reflexivity |].
      pose proof (chk_range_sound _ _ _ s16_seg3_bytes (bv_unsigned a - B3) ltac:(lia)) as Hc.
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
  -  apply chk_rom_bytes_sound; [apply Forall_map_mod256 | exact (proj2 (proj2 (proj2 (proj2 s16_tables))))].
  -  intros a Ha. cbn in Ha. rewrite !u64_lit in Ha by lia.
    pose proof (chk_list_sound _ _ _ s16_ctx_zero (bv_unsigned a) ltac:(cbn; rewrite !u64_lit by lia; lia)) as Hc.
    unfold chk_rom_zero in Hc. rewrite Z_to_bv_bv_unsigned in Hc.
    destruct (seg_rom ml_segs a) as [v|]; [|discriminate]. apply Z.eqb_eq in Hc.
    f_equal. rewrite <- (Z_to_bv_bv_unsigned 8 v). rewrite Hc. reflexivity.
  -  cbn; rewrite !u64_lit by lia; lia.
  - reflexivity.
  - apply chk_rom_bytes_sound; [apply Forall_lt256_of_chk; vm_compute; reflexivity | exact (proj1 s16_tables)].
  - apply chk_rom_bytes_sound; [apply Forall_lt256_of_chk; vm_compute; reflexivity | exact (proj1 (proj2 s16_tables))].
  - apply chk_rom_bytes_sound; [apply Forall_lt256_of_chk; vm_compute; reflexivity | exact (proj1 (proj2 (proj2 s16_tables)))].
  - apply chk_rom_bytes_sound; [apply Forall_lt256_of_chk; vm_compute; reflexivity | exact (proj1 (proj2 (proj2 (proj2 s16_tables))))].
  -  repeat (apply Forall_cons || apply Forall_nil); cbv; repeat split; congruence.
Qed.
