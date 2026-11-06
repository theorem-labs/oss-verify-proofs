(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require StackLayout.
From LinuxProcessSemantics.LinuxProcessSem Require Fs.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Monad.
From LinuxProcessSemantics.LinuxProcessSem Require Specs.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From OSSVerify.leptonica.edge_fuzzer.images Require Ubsan.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require PropExec.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require CatExec.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require Hoare.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require AgentLib.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng Require MallocLayout.
Module V9MallocLayout.
Import Stdlib.ZArith.ZArith.
Import Stdlib.NArith.NArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Import LinuxProcessSemantics.LinuxProcessSem.Fs.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.LinuxProcessSem.Monad.
Import LinuxProcessSemantics.LinuxProcessSem.Specs.
Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.leptonica.edge_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.AgentLib.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng.MallocLayout.
(* [comment removed for export] *)





Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Module ImgU16 := Ubsan.

(* [comment removed for export] *)
Instance LU16 : MallocLayout := {|
  ml_segs := ImgU16.M.loaded_segments;
  IMG_LO := 0x10000; RW_LO := 0xf5000; IMG_HI := 0x12c000;

  A_LOCK           := Z_to_bv 64 0x12ab58;
  A_CTX            := Z_to_bv 64 0x12ab60;
  A_INIT_DONE      := Z_to_bv 64 0x12ab68;
  A_MMAP_CTR       := Z_to_bv 64 0x12ab6c;
  A_FREE_META_HEAD := Z_to_bv 64 0x12ab70;
  A_AVAIL_META     := Z_to_bv 64 0x12ab78;
  A_AVAIL_META_CNT := Z_to_bv 64 0x12ab80;
  A_AVAIL_AREA_CNT := Z_to_bv 64 0x12ab88;
  A_META_SHIFT     := Z_to_bv 64 0x12ab90;
  A_AREA_HEAD      := Z_to_bv 64 0x12ab98;
  A_AREA_TAIL      := Z_to_bv 64 0x12aba0;
  A_AVAIL_AREAS    := Z_to_bv 64 0x12aba8;
  Z_UNMAP_SEQ      := 0x12aeb0;
  Z_BOUNCES        := 0x12aed0;
  A_SEQ            := Z_to_bv 64 0x12aef0;
  A_BRK            := Z_to_bv 64 0x12aef8;
  A_MALLOC_REPLACED := Z_to_bv 64 0x12af00;

  A_LIBC       := Z_to_bv 64 0x12aae8;
  A_NEED_LOCKS := Z_to_bv 64 0x12aaeb;
  A_PAGE_SIZE  := Z_to_bv 64 0x12ab18;
  A_TP         := Z_to_bv 64 0x10a858;
  A_ERRNO      := Z_to_bv 64 0x10a7b4;
  A_GOT_SSP    := Z_to_bv 64 0xf92a8;
  A_SSP        := Z_to_bv 64 0x12aac8;

  A_SIZE_CLASSES  := Z_to_bv 64 0x4b018;
  A_SMALL_CNT_TAB := Z_to_bv 64 0x4b078;
  A_MED_CNT_TAB   := Z_to_bv 64 0x1c8e4;
  A_DEBRUIJN      := Z_to_bv 64 0x48828;

  PC_MALLOC      := (0xe26f8%bv : word);
  PC_FREE        := (0xe25b8%bv : word);
  PC_CALLOC      := (0xe2480%bv : word);
  PC_LIBC_FREE   := (0xe26fc%bv : word);
  PC_MALLOC_IMPL := (0xe3088%bv : word);
  PC_GET_META    := (0xe28c8%bv : word);
  PC_NTFREE      := (0xe29d8%bv : word);
  PC_ALLOC_META  := (0xe2db0%bv : word);
  PC_ALLOC_SLOT  := (0xe33f8%bv : word);
  PC_ENFRAME     := (0xe3c9c%bv : word);
  PC_ALLZEROP    := (0xe3dec%bv : word);
  PC_MMAP        := (0xe53e0%bv : word);
  PC_MPROTECT    := (0xe54cc%bv : word);
  PC_MUNMAP      := (0xe55e8%bv : word);
  PC_VM_WAIT     := (0xe53dc%bv : word);
  PC_SYSCALL_RET := (0xe2440%bv : word);
  PC_ERRNO_LOC   := (0xe1f74%bv : word);
  PC_LOCK        := (0xf160c%bv : word);
  PC_UNLOCK      := (0xf1894%bv : word);
  PC_MEMCPY      := (0xf0a88%bv : word);
  PC_MEMSET      := (0xf1008%bv : word)
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
Local Abbreviation B0 := 0x10000.  Local Abbreviation B1 := 0x5c000.  Local Abbreviation B2 := 0xf5000.
Local Abbreviation B3 := 0xfa000.  Local Abbreviation B4 := 0x12c000.
Local Abbreviation P0 := 76%nat.  Local Abbreviation P1 := 153%nat.  Local Abbreviation P2 := 5%nat.   (* [comment removed for export] *)  Local Abbreviation P3 := 50%nat.

Lemma u16_segs : ml_segs = [SEG0; SEG1; SEG2; SEG3].
Proof. reflexivity. Qed.

Lemma u16_bases :
  Z.of_N (seg_base SEG0) = B0 /\ Z.of_N (seg_base SEG0) + Z.of_N (seg_size SEG0) = B1 /\
  Z.of_N (seg_base SEG1) = B1 /\ Z.of_N (seg_base SEG1) + Z.of_N (seg_size SEG1) = B2 /\
  Z.of_N (seg_base SEG2) = B2 /\ Z.of_N (seg_base SEG2) + Z.of_N (seg_size SEG2) = B3 /\
  Z.of_N (seg_base SEG3) = B3 /\ Z.of_N (seg_base SEG3) + Z.of_N (seg_size SEG3) = B4.
Proof. repeat split; reflexivity. Qed.

(* [comment removed for export] *)
Lemma u16_find_none : forall a, (a < B0 \/ B4 <= a) -> find_segment ml_segs a 1 = None.
Proof.
  intros a Ha. rewrite u16_segs. apply find_segment_none. pose proof u16_bases as B.
  repeat (apply Forall_cons || apply Forall_nil); unfold seg_misses; lia.
Qed.

Lemma u16_find_seg0 : forall a, B0 <= a -> a + 1 <= B1 -> find_segment ml_segs a 1 = Some SEG0.
Proof.
  intros a H1 H2. rewrite u16_segs. pose proof u16_bases as B.
  apply (find_segment_hit [] SEG0 [SEG1; SEG2; SEG3] a 1); [apply Forall_nil | lia | lia].
Qed.
Lemma u16_find_seg1 : forall a, B1 <= a -> a + 1 <= B2 -> find_segment ml_segs a 1 = Some SEG1.
Proof.
  intros a H1 H2. rewrite u16_segs. pose proof u16_bases as B.
  apply (find_segment_hit [SEG0] SEG1 [SEG2; SEG3] a 1); [| lia | lia].
  repeat (apply Forall_cons || apply Forall_nil); unfold seg_misses; lia.
Qed.
Lemma u16_find_seg2 : forall a, B2 <= a -> a + 1 <= B3 -> find_segment ml_segs a 1 = Some SEG2.
Proof.
  intros a H1 H2. rewrite u16_segs. pose proof u16_bases as B.
  apply (find_segment_hit [SEG0; SEG1] SEG2 [SEG3] a 1); [| lia | lia].
  repeat (apply Forall_cons || apply Forall_nil); unfold seg_misses; lia.
Qed.
Lemma u16_find_seg3 : forall a, B3 <= a -> a + 1 <= B4 -> find_segment ml_segs a 1 = Some SEG3.
Proof.
  intros a H1 H2. rewrite u16_segs. pose proof u16_bases as B.
  apply (find_segment_hit [SEG0; SEG1; SEG2] SEG3 [] a 1); [| lia | lia].
  repeat (apply Forall_cons || apply Forall_nil); unfold seg_misses; lia.
Qed.

(* [comment removed for export] *)
Definition chk_seg_byte (seg : Segment) (off : Z) : bool :=
  match segment_byte_at (seg_bytes seg) (Z.to_N off) with Some _ => true | None => false end.

Lemma u16_seg0_bytes : chk_range (chk_seg_byte SEG0) 0 P0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma u16_seg1_bytes : chk_range (chk_seg_byte SEG1) 0 P1 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma u16_seg2_bytes : chk_range (chk_seg_byte SEG2) 0 P2 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma u16_seg3_bytes : chk_range (chk_seg_byte SEG3) 0 P3 = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition chk_rom_zero (a : Z) : bool :=
  match seg_rom ml_segs (Z_to_bv 64 a) with Some v => bv_unsigned v =? 0 | None => false end.
Lemma u16_ctx_zero : chk_list chk_rom_zero (bv_unsigned A_LOCK) 940 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma u16_tables :
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

Instance LU17ok : MallocLayoutOk LU16.
Proof.
  pose proof u16_bases as B.
  split.
  - (* [comment removed for export] *) cbn. lia.
  - (* [comment removed for export] *) intros a Ha. apply seg_rom_none_of_find. apply u16_find_none. exact Ha.
  - (* [comment removed for export] *) intros m a Ha. apply wview_of_find_none. apply u16_find_none. exact Ha.
  - (* [comment removed for export] *) intros m a Ha. cbn in Ha.
    destruct (Z.lt_ge_cases (bv_unsigned a) B1).
    + apply (wview_of_find_ro _ m a SEG0); [apply u16_find_seg0; lia | reflexivity].
    + apply (wview_of_find_ro _ m a SEG1); [apply u16_find_seg1; lia | reflexivity].
  - (* [comment removed for export] *) intros m a Ha. cbn in Ha.
    destruct (Z.lt_ge_cases (bv_unsigned a) B3).
    + apply (wview_of_find_rw _ m a SEG2); [apply u16_find_seg2; lia | reflexivity |].
      pose proof (chk_range_sound _ _ _ u16_seg2_bytes (bv_unsigned a - B2) ltac:(lia)) as Hc.
      unfold chk_seg_byte in Hc. rewrite (proj1 (proj2 (proj2 (proj2 (proj2 B))))).
      destruct (segment_byte_at (seg_bytes SEG2) (Z.to_N (bv_unsigned a - B2))); [discriminate | discriminate].
    + apply (wview_of_find_rw _ m a SEG3); [apply u16_find_seg3; lia | reflexivity |].
      pose proof (chk_range_sound _ _ _ u16_seg3_bytes (bv_unsigned a - B3) ltac:(lia)) as Hc.
      unfold chk_seg_byte in Hc. rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 B))))))).
      destruct (segment_byte_at (seg_bytes SEG3) (Z.to_N (bv_unsigned a - B3))); [discriminate | discriminate].
  - (* [comment removed for export] *) intros a Ha. cbn in Ha.
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
  - (* [comment removed for export] *) intros b sz Hin. cbv -[Z_to_bv] in Hin.
    destruct Hin as [E|[E|[E|[E|[]]]]]; injection E as <- <-; rewrite !u64_lit by lia; cbn; lia.
  - (* [comment removed for export] *) intros a Ha. cbn in Ha.
    destruct (Z.lt_ge_cases a B1); [| destruct (Z.lt_ge_cases a B2); [| destruct (Z.lt_ge_cases a B3)]].
    + exists (Z_to_bv 64 B0), (Z_to_bv 64 (B1 - B0)). split; [cbv -[Z_to_bv]; tauto | rewrite !u64_lit by lia; lia].
    + exists (Z_to_bv 64 B1), (Z_to_bv 64 (B2 - B1)). split; [cbv -[Z_to_bv]; tauto | rewrite !u64_lit by lia; lia].
    + exists (Z_to_bv 64 B2), (Z_to_bv 64 (B3 - B2)). split; [cbv -[Z_to_bv]; tauto | rewrite !u64_lit by lia; lia].
    + exists (Z_to_bv 64 B3), (Z_to_bv 64 (B4 - B3)). split; [cbv -[Z_to_bv]; tauto | rewrite !u64_lit by lia; lia].
  - (* [comment removed for export] *) vm_compute. reflexivity.
  - (* [comment removed for export] *) reflexivity.
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
  - (* [comment removed for export] *) reflexivity.
  - (* [comment removed for export] *) reflexivity.
  - reflexivity.
  - reflexivity.
  - (* [comment removed for export] *) reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - (* [comment removed for export] *) cbn; rewrite !u64_lit by lia; lia.
  - cbn; rewrite !u64_lit by lia; lia.
  - cbn; rewrite !u64_lit by lia; lia.
  - cbn; rewrite !u64_lit by lia; lia.
  - cbn; rewrite !u64_lit by lia; lia.
  - unfold CTX_SIZE; cbn; rewrite !u64_lit by lia; lia.
  - cbn; rewrite !u64_lit by lia; lia.
  - (* [comment removed for export] *) apply chk_rom_bytes_sound; [apply Forall_map_mod256 | exact (proj2 (proj2 (proj2 (proj2 u16_tables))))].
  - (* [comment removed for export] *) intros a Ha. cbn in Ha. rewrite !u64_lit in Ha by lia.
    pose proof (chk_list_sound _ _ _ u16_ctx_zero (bv_unsigned a) ltac:(cbn; rewrite !u64_lit by lia; lia)) as Hc.
    unfold chk_rom_zero in Hc. rewrite Z_to_bv_bv_unsigned in Hc.
    destruct (seg_rom ml_segs a) as [v|]; [|discriminate]. apply Z.eqb_eq in Hc.
    f_equal. rewrite <- (Z_to_bv_bv_unsigned 8 v). rewrite Hc. reflexivity.
  - (* [comment removed for export] *) cbn; rewrite !u64_lit by lia; lia.
  - reflexivity.
  - apply chk_rom_bytes_sound; [apply Forall_lt256_of_chk; vm_compute; reflexivity | exact (proj1 u16_tables)].
  - apply chk_rom_bytes_sound; [apply Forall_lt256_of_chk; vm_compute; reflexivity | exact (proj1 (proj2 u16_tables))].
  - apply chk_rom_bytes_sound; [apply Forall_lt256_of_chk; vm_compute; reflexivity | exact (proj1 (proj2 (proj2 u16_tables)))].
  - apply chk_rom_bytes_sound; [apply Forall_lt256_of_chk; vm_compute; reflexivity | exact (proj1 (proj2 (proj2 (proj2 u16_tables))))].
  - (* [comment removed for export] *) repeat (apply Forall_cons || apply Forall_nil); cbv; repeat split; congruence.
Qed.
End V9MallocLayout.

From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require StoreOk.
Module V9MemPreds.
Import Stdlib.ZArith.ZArith.
Import Stdlib.NArith.NArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import OSSVerify.leptonica.edge_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.StoreOk.
(* [comment removed for export] *)
(* [comment removed for export] *)




Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Abbreviation RSEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)
Definition cell (M : word -> option byte) (a : Z) (n : nat) (v : Z) : Prop :=
  rdn RSEGS M (Z_to_bv 64 a) n = Some (word_to_le_bytes n (Z_to_bv 64 v)).

(* [comment removed for export] *)
Definition zero_bytes (M : word -> option byte) (a n : Z) : Prop :=
  forall i, 0 <= i < n -> M (Z_to_bv 64 (a + i)) = Some (Z_to_bv 8 0).

(* [comment removed for export] *)
Definition img_clear (M : word -> option byte) (lo hi : Z) : Prop :=
  forall i, lo <= i < hi -> M (Z_to_bv 64 i) = None.

(* [comment removed for export] *)
Definition bytes_at (M : word -> option byte) (a : Z) (bs : list byte) : Prop :=
  forall i, 0 <= i < Z.of_nat (length bs) -> M (Z_to_bv 64 (a + i)) = Some (nth (Z.to_nat i) bs (Z_to_bv 8 0)).

(* [comment removed for export] *)
Definition stack_writable (M : word -> option byte) (sp0 : word) : Prop :=
  forall d m, 0 <= d -> d + Z.of_nat m <= 8388608 ->
    store_ok RSEGS M (Z_to_bv 64 (bv_unsigned sp0 - 8388608 + d)) m = true.
End V9MemPreds.

Module V9PFBase.
Import OSSVerify.leptonica.edge_fuzzer.images.Ubsan.
(* [comment removed for export] *)

Abbreviation SEGS := Ubsan.M.loaded_segments.
End V9PFBase.

From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Reloc Require Reloc.
Module V9Reloc.
Import Stdlib.ZArith.ZArith.
Import Stdlib.Lists.List.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OSSVerify.leptonica.edge_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Reloc.Reloc.
(* [comment removed for export] *)




Import ListNotations.
Local Open Scope Z_scope.

Definition v9_dtab : list (positive * Z) :=
  [(8%positive, 0); (1000%positive, 301776); (1001%positive, 301776); (1002%positive, 301776); (1003%positive, 301776); (1004%positive, 301776); (1005%positive, 301776); (1006%positive, 301776); (1007%positive, 301776); (1008%positive, 301900);
   (1009%positive, 301924); (1010%positive, 301924); (1011%positive, 301924); (1012%positive, 301924); (1013%positive, 302052); (1014%positive, 302052); (1015%positive, 423848); (1016%positive, 837684); (1017%positive, 837684); (1018%positive, 837684);
   (1019%positive, 837684); (1020%positive, 837684); (1021%positive, 837684); (1022%positive, 837672); (1023%positive, 837672); (1024%positive, 837820); (1025%positive, 838272); (1026%positive, 838272); (1027%positive, 838272); (1028%positive, 838272);
   (1029%positive, 838272); (1030%positive, 838272); (1031%positive, 838272); (1032%positive, 838272); (1033%positive, 838272); (1034%positive, 838272); (1035%positive, 838272); (1036%positive, 838588); (1037%positive, 838588); (1038%positive, 838588);
   (1039%positive, 838588); (1040%positive, 838588); (1041%positive, 838588); (1042%positive, 838588); (1043%positive, 838588); (1044%positive, 838588); (1045%positive, 843676); (1046%positive, 843676); (1047%positive, 843676); (1048%positive, 843676);
   (1049%positive, 843888); (1050%positive, 845332); (1051%positive, 845332); (1052%positive, 845988); (1053%positive, 847140); (1054%positive, 847140); (1055%positive, 847140); (1056%positive, 847140); (1057%positive, 847140); (1058%positive, 847684);
   (1059%positive, 847684); (1060%positive, 848700); (1061%positive, 848700); (1062%positive, 848700); (1063%positive, 849456); (1064%positive, 849456); (1065%positive, 849456); (1066%positive, 849456); (1067%positive, 849456); (1068%positive, 849456);
   (1069%positive, 849456); (1070%positive, 849456); (1071%positive, 849456); (1072%positive, 849456); (1073%positive, 849456); (1074%positive, 849456); (1075%positive, 849644); (1076%positive, 849644); (1077%positive, 849644); (1078%positive, 849644);
   (1079%positive, 849644); (1080%positive, 849644); (1081%positive, 849644); (1082%positive, 849644); (1083%positive, 849644); (1084%positive, 849644); (1085%positive, 865316); (1086%positive, 830636); (1087%positive, 865156); (1088%positive, 865156);
   (1089%positive, 868516); (1090%positive, 868564); (1091%positive, 868944); (1092%positive, 869604); (1093%positive, 869916); (1094%positive, 870024); (1095%positive, 870024); (1096%positive, 870024); (1097%positive, 870024); (1098%positive, 870024);
   (1099%positive, 882884); (1100%positive, 883140); (1101%positive, 883140); (3000%positive, 301812); (3001%positive, 424096); (4000%positive, 1064); (4001%positive, 8670); (4002%positive, 10184); (4003%positive, 10184); (4004%positive, 10228);
   (4005%positive, 11580); (4006%positive, 13272); (4007%positive, 13272); (4008%positive, 19454); (4009%positive, 24974); (4010%positive, 24985); (4011%positive, 36958); (4012%positive, 36958); (4013%positive, 39764); (4014%positive, 41529);
   (4015%positive, 42575); (4016%positive, 45647); (4017%positive, 46992); (4018%positive, 46992); (5000%positive, 236644); (5001%positive, 226420); (5002%positive, 46229); (5003%positive, 44520); (5004%positive, 44848); (5005%positive, 44936);
   (5006%positive, 45088); (5007%positive, 45296); (5008%positive, 245064); (5009%positive, 44672); (5010%positive, 245048); (5011%positive, 255504); (5012%positive, 896352); (5013%positive, 896736); (5015%positive, 896800); (5016%positive, 883192);
   (5018%positive, 48588); (5019%positive, 896776); (5020%positive, 236612); (5021%positive, 44992); (5022%positive, 45008); (5023%positive, 45128); (5024%positive, 45160); (5025%positive, 45208); (5026%positive, 896368); (5027%positive, 896712);
   (5028%positive, 896744); (5029%positive, 897184); (5030%positive, 1028736); (5031%positive, 1028736); (5032%positive, 1028736); (5033%positive, 1028736); (230%positive, 260504); (240%positive, 260504); (241%positive, 260504); (242%positive, 260504);
   (243%positive, 260504); (231%positive, 261060); (232%positive, 261860); (244%positive, 261860); (245%positive, 261860); (246%positive, 261860); (233%positive, 262652); (234%positive, 263324); (247%positive, 263464); (235%positive, 263616);
   (236%positive, 267048); (237%positive, 271860); (248%positive, 271860); (238%positive, 275800); (249%positive, 276920); (250%positive, 293932); (239%positive, 357516); (400%positive, 165); (401%positive, 165); (402%positive, 165);
   (403%positive, 165); (404%positive, 165); (405%positive, 74); (406%positive, 1297); (407%positive, 1484); (408%positive, 2756); (409%positive, 2771); (410%positive, 4649); (411%positive, 5981); (412%positive, 5996);
   (413%positive, 7327); (414%positive, 7342); (415%positive, 7342); (416%positive, 7484); (417%positive, 8843); (418%positive, 8896); (419%positive, 11709); (420%positive, 11709); (421%positive, 12088); (422%positive, 14880);
   (423%positive, 16487); (424%positive, 16515); (425%positive, 16563); (426%positive, 18149); (427%positive, 18160); (428%positive, 19580); (429%positive, 19580); (430%positive, 19598); (431%positive, 19598); (432%positive, 19598);
   (433%positive, 19653); (434%positive, 21037); (435%positive, 21037); (436%positive, 22613); (437%positive, 22613); (438%positive, 22633); (439%positive, 23769); (440%positive, 23769); (441%positive, 25084); (442%positive, 25212);
   (443%positive, 25212); (444%positive, 27976); (445%positive, 27984); (446%positive, 28153); (447%positive, 29393); (448%positive, 29409); (449%positive, 29425); (450%positive, 31190); (451%positive, 32820); (452%positive, 34511);
   (453%positive, 34511); (454%positive, 34511); (455%positive, 34579); (456%positive, 34579); (457%positive, 34614); (458%positive, 37027); (459%positive, 37082); (460%positive, 37082); (461%positive, 37097); (462%positive, 38333);
   (463%positive, 38648); (464%positive, 39911); (465%positive, 39911); (466%positive, 41577); (467%positive, 44309); (468%positive, 45684); (469%positive, 45720); (470%positive, 45720); (471%positive, 45838); (5034%positive, 896360);
   (1900%positive, 837868); (5036%positive, 897240); (5037%positive, 1028520)].

Definition v9_stab : list (Z * Z) := [
  (0x13084, 0xfffb4197); (0x13088, 0xcac18193); (0x13090, 0xfffa3597); (0x13094, 0x4a058593);
  (0x1309c, 0x40006f); (0x130a4, 0x9c617); (0x130a8, 0x9c697); (0x130ac, 0x9c717);
  (0x130b0, 0x55c63783); (0x130b4, 0x5606b683); (0x130b8, 0x56473703); (0x130c8, 0x848506f);
  (0x130dc, 0x9e517); (0x130e0, 0x9a450513); (0x130f8, 0x9e517); (0x130fc, 0x98850593);
  (0x13108, 0x9c517); (0x1310c, 0x51053503); (0x13118, 0xffff3517); (0x1311c, 0x39050513);
  (0x13120, 0x9e597); (0x13124, 0x96858593); (0x13150, 0x9e517); (0x13154, 0x97850513);
  (0x1316c, 0x9e517); (0x13170, 0x95c50593); (0x1317c, 0x9c517); (0x13180, 0x4a453503);
  (0x1318c, 0x9d517); (0x13190, 0x67c50513); (0x131a0, 0x9c517); (0x131a4, 0x48853503);
  (0x131b0, 0xffff3517); (0x131b4, 0x2f850513); (0x1320c, 0x618850ef); (0x13220, 0x209850ef);
  (0x13230, 0x9e517); (0x13234, 0x89950b13); (0x1324c, 0x56d930ef); (0x13274, 0x1b5850ef);
  (0x13290, 0x529930ef); (0x13298, 0x51850ef); (0x132b4, 0x755970ef); (0x132c8, 0x5e1970ef);
  (0x1332c, 0x168000ef); (0x13340, 0x160000ef); (0x13350, 0x148000ef); (0x13368, 0x9c517);
  (0x1336c, 0x2d053503); (0x13378, 0xfffb7597); (0x1337c, 0xa2258593); (0x13380, 0x15d890ef);
  (0x13388, 0x9c517); (0x1338c, 0x2b053503); (0x13394, 0xfffbe517); (0x1339c, 0x1d650513);
  (0x133a4, 0x9c517); (0x133a8, 0x29453503); (0x133b0, 0xfffb7517); (0x133b8, 0x9fb50513);
  (0x133c0, 0x1808a0ef); (0x133c8, 0x720850ef); (0x133fc, 0x9c517); (0x13400, 0x23c53503);
  (0x13408, 0xfffbd597); (0x1340c, 0xa5258593); (0x13418, 0x9c517); (0x1341c, 0x22053503);
  (0x13424, 0xfffba597); (0x13428, 0x98d58593); (0x13430, 0xad890ef); (0x13438, 0x9c517);
  (0x1343c, 0x20053503); (0x13444, 0xfffb6517); (0x1344c, 0xcf950513); (0x13454, 0xec8a0ef);
  (0x1345c, 0x354850ef); (0x13460, 0x9c517); (0x13464, 0x1d853503); (0x1346c, 0xfffbd597);
  (0x13470, 0x9d958593); (0x13478, 0x9c517); (0x1347c, 0x1c053503); (0x13484, 0xfffb6517);
  (0x1348c, 0xcb950513); (0x135d8, 0xfffb6517); (0x135dc, 0xafd50513); (0x135e4, 0x179920ef);
  (0x13674, 0xfffbf517); (0x13678, 0xa8a50513); (0x1367c, 0x18000ef); (0x13708, 0x59920ef);
  (0x13710, 0x9d517); (0x13714, 0x9453583); (0x13744, 0xfffbf517); (0x13748, 0x9ba50513);
  (0x1374c, 0xf49ff0ef); (0x1376c, 0x9c597); (0x13770, 0xdb85b583); (0x13778, 0x7288906f);
  (0x13780, 0x517); (0x13784, 0xfe450513); (0x13788, 0x9d597); (0x1378c, 0xf8a5be23);
  (0x14d1c, 0xfc0006f); (0x15198, 0x63c0f0ef); (0x1519c, 0x18517); (0x151a0, 0x8b053503);
  (0x151b4, 0x49517); (0x151b8, 0x10050913); (0x15204, 0x49617); (0x15208, 0x10b63c23);
  (0x15210, 0x49597); (0x15214, 0x8a5b623); (0x1521c, 0x49517); (0x15220, 0x10053023);
  (0x15238, 0xfff31517); (0x1523c, 0x1e550413); (0x15240, 0x18517); (0x15244, 0x81453583);
  (0x15248, 0x18517); (0x1524c, 0x81453503); (0x1527c, 0x214000ef); (0x15284, 0x121000ef);
  (0x152f8, 0xfff3a517); (0x15304, 0x6d150593); (0x15328, 0xfff3a517); (0x15334, 0x6a150593);
  (0x15358, 0xfff3a517); (0x15364, 0x67150593); (0x153ac, 0xdc1ff0ef); (0x153b0, 0x17517);
  (0x153b4, 0x17597); (0x153b8, 0x6b453403); (0x153bc, 0x6b85b483); (0x15418, 0xd59ff0ef);
  (0x1541c, 0x517); (0x15420, 0x2c50313); (0x15478, 0xf25ff0ef); (0x1548c, 0x5c0000ef);
  (0x154b4, 0x49597); (0x154b8, 0xb7858593); (0x154bc, 0x49617); (0x154c0, 0xdf860493);
  (0x154d0, 0x19717); (0x154e0, 0x17297); (0x154e4, 0x82476f03); (0x154e8, 0x3b42b283);
  (0x15558, 0x83172223); (0x15600, 0xfff69597); (0x1560c, 0x8d858593); (0x15630, 0x29697);
  (0x15644, 0x92c68513); (0x1569c, 0x3b90e0ef); (0x156c0, 0x23d0f0ef); (0x156d8, 0x49597);
  (0x156e4, 0x95458513); (0x15700, 0x49517); (0x15704, 0xb9c53503); (0x15768, 0xfff69617);
  (0x15774, 0xf8060613); (0x15784, 0xfff68617); (0x15788, 0x7bc60613); (0x15790, 0x4c40006f);
  (0x157c4, 0x17517); (0x157c8, 0x17597); (0x157cc, 0x6c53503); (0x157d0, 0x705b403);
  (0x157fc, 0xfb5ff06f); (0x15818, 0x49697); (0x1581c, 0x82868693); (0x15860, 0xdbdff0ef);
  (0x15864, 0xf51ff0ef); (0x15868, 0x4d9030ef); (0x15870, 0xd61ff0ef); (0x15894, 0x17517);
  (0x15898, 0xf9453483); (0x158f0, 0x5bc0f0ef); (0x1592c, 0x94000ef); (0x15954, 0x64000ef);
  (0x15968, 0x17517); (0x1596c, 0xec053503); (0x15974, 0x6940e0ef); (0x1597c, 0x17517);
  (0x15980, 0xeac53503); (0x15994, 0x17517); (0x15998, 0xe9453503); (0x159dc, 0xb19ff0ef);
  (0x159fc, 0xffdff06f); (0x15a1c, 0xad9ff0ef); (0x15a4c, 0x22c000ef); (0x15a58, 0x49517);
  (0x15a5c, 0xa2852503); (0x15a84, 0x3050e0ef); (0x15aa0, 0x2e90e0ef); (0x15ae0, 0x2a90e0ef);
  (0x15b0c, 0x27d0e06f); (0x15b2c, 0x41010ef); (0x15b38, 0x1440006f); (0x15b3c, 0x1910006f);
  (0x15b60, 0x1ac000ef); (0x15b94, 0xfff69717); (0x15b9c, 0x8c870713); (0x15c40, 0x48717);
  (0x15c5c, 0x2ef74883); (0x15c94, 0x48597); (0x15c98, 0x30858593); (0x15ca4, 0x5ad0e0ef);
  (0x15cb0, 0x16c000ef); (0x15cbc, 0x48517); (0x15cc0, 0x2e050513); (0x15cc4, 0x140f0ef);
  (0x15ccc, 0xeecff0ef); (0x15ce0, 0x54d020ef); (0x15d9c, 0x48797); (0x15da8, 0x2087b783);
  (0x15dc8, 0xfff68797); (0x15dcc, 0x69478793); (0x15e34, 0x17617); (0x15e38, 0x8b863483);
  (0x15e84, 0x48817); (0x15e88, 0x12080913); (0x15e98, 0xfff68817); (0x15e9c, 0x5c480813);
  (0x15f90, 0x48697); (0x15f94, 0x1468693); (0x1608c, 0xc81ff0ef); (0x161f0, 0xe8cff0ef);
  (0x16210, 0x16517); (0x16214, 0x4dc53903); (0x1621c, 0x48597); (0x16224, 0xd8058993);
  (0x1622c, 0x48597); (0x16230, 0xd0058413); (0x1626c, 0x4610d0ef); (0x1637c, 0x4a8020ef);
  (0x163d4, 0x450020ef); (0x164a8, 0x468020ef); (0x164b0, 0xf09fe0ef); (0x164c8, 0xbb4ff0ef);
  (0x164f8, 0xec1fe0ef); (0x16534, 0x48597); (0x16538, 0xa6858493); (0x16560, 0x2c4020ef);
  (0x1656c, 0x48517); (0x16570, 0x9c354503); (0x16578, 0x48517); (0x1657c, 0xa2450513);
  (0x16580, 0x4d00e0ef); (0x165b0, 0xfff65617); (0x165b8, 0x6bc60993); (0x16620, 0xfff68617);
  (0x16634, 0xe3c60593); (0x16654, 0xba1ff0ef); (0x166c0, 0x48517); (0x166c4, 0x86f54503);
  (0x166cc, 0x48517); (0x166d0, 0x8d050513); (0x166d4, 0x37c0e0ef); (0x16718, 0x48517);
  (0x1671c, 0x88450513); (0x16720, 0x5b80e0ef); (0x1672c, 0x300020ef); (0x167d8, 0x64000ef);
  (0x167f8, 0x4e00e0ef); (0x16828, 0xb90006f); (0x1682c, 0x47517); (0x16830, 0x77050513);
  (0x16834, 0x4a40e0ef); (0x16874, 0x16517); (0x16878, 0xe7853a03); (0x16884, 0x47597);
  (0x16888, 0x71858b13); (0x16a04, 0xfff65597); (0x16a0c, 0x26858593); (0x16a20, 0xfff68517);
  (0x16a24, 0xa3c50c93); (0x16a30, 0xfc4ff0ef); (0x16a44, 0x47597); (0x16a48, 0x5185b583);
  (0x16a5c, 0xfff68697); (0x16a60, 0xa6068693); (0x16a8c, 0xfff39697); (0x16a90, 0x29c68693);
  (0x16ba4, 0xfff65697); (0x16bac, 0xc868693); (0x16c48, 0x498000ef); (0x16d18, 0xfff67717);
  (0x16d20, 0x74470713); (0x16ee8, 0x13d010ef); (0x170dc, 0xfa0fe0ef); (0x17108, 0xfff67797);
  (0x17110, 0x35478793); (0x172c4, 0x47797); (0x172cc, 0xce07b783); (0x172ec, 0xfff67817);
  (0x172f0, 0x17080813); (0x17360, 0xfff67597); (0x17364, 0xfc58593); (0x1738c, 0xfff67517);
  (0x17390, 0xd050513); (0x173b0, 0xfff37597); (0x173b4, 0x1545b787); (0x173e8, 0xfff37597);
  (0x173ec, 0x1ac5b787); (0x1746c, 0xb6dfc0ef); (0x17484, 0xb55fc0ef); (0x174e0, 0xf61ff0ef);
  (0x17528, 0xf7dfc0ef); (0x17538, 0x45697); (0x1753c, 0x6446b683); (0x17564, 0xf41fc0ef);
  (0x17590, 0xdddff0ef); (0x175a4, 0xe2dfc0ef); (0x17728, 0xfc010ef); (0x17734, 0x45517);
  (0x17738, 0xf3053403); (0x1774c, 0xbe5ff0ef); (0x17790, 0x14517); (0x17794, 0x4ec53403);
  (0x177a8, 0xb89ff0ef); (0x177ec, 0x14517); (0x177f0, 0x3a053403); (0x17804, 0xb2dff0ef);
  (0x17868, 0xac9ff0ef); (0x178ec, 0x13517); (0x178f0, 0xc9853a83); (0x1794c, 0xdd1fb0ef);
  (0x179d4, 0xd49fb0ef); (0x17a4c, 0xcc9fb0ef); (0x17a54, 0x5540e06f); (0x17a68, 0xff1ff0ef);
  (0x17a74, 0xca9fb0ef); (0x17a9c, 0x13817); (0x17aa0, 0xae883403); (0x17ac8, 0x401000ef);
  (0x17ae8, 0xc2dfb0ef); (0x17b5c, 0xf50a0ef); (0x17b74, 0x558000ef); (0x17c54, 0xaa1ff0ef);
  (0x17c9c, 0x2b1090ef); (0x17d14, 0xb85fe0ef); (0x17d28, 0xe75ff0ef); (0x17d38, 0xc5dfe0ef);
  (0x17d58, 0xe45ff0ef); (0x17d98, 0x44517); (0x17d9c, 0xe3c50413); (0x17da4, 0x52c0a0ef);
  (0x17de4, 0x12517); (0x17de8, 0xe9453903); (0x17e20, 0x14c000ef); (0x17e34, 0xf70fe0ef);
  (0x17e94, 0xd6cff0ef); (0x17ec0, 0xac000ef); (0x17f30, 0xf70fe0ef); (0x17f68, 0xea1fa0ef);
  (0x17fc4, 0x12517); (0x17fd0, 0xcb453603); (0x180b0, 0xff8ff0ef); (0x183d0, 0xfff66697);
  (0x183d4, 0x93868693); (0x18444, 0x159000ef); (0x1849c, 0xfff65597); (0x184a0, 0x72458593);
  (0x184dc, 0x2c9000ef); (0x1850c, 0xfff29597); (0x18514, 0xbd358593); (0x18538, 0xfff29517);
  (0x1853c, 0xba750513); (0x18554, 0xfff34517); (0x18558, 0x68350b93); (0x18560, 0xbe4fa0ef);
  (0x18568, 0xbe8fa0ef); (0x18580, 0x1ad090ef); (0x18598, 0xfff29617); (0x1859c, 0xb4760613);
  (0x185dc, 0xfff29597); (0x185e0, 0xb0358593); (0x18614, 0xfff65597); (0x18618, 0x68c58593);
  (0x18644, 0xfff29597); (0x18648, 0xa9b58893); (0x18680, 0xfff29517); (0x18684, 0xa5f50513);
  (0x186b8, 0xfff29597); (0x186bc, 0xa2758713); (0x186d0, 0xfff35697); (0x186d4, 0x94068693);
  (0x18734, 0x739010ef); (0x1876c, 0x764000ef); (0x18790, 0x6dd010ef); (0x187b4, 0x8f4ff0ef);
  (0x187c0, 0xfff29597); (0x187c4, 0x91f58593); (0x187e8, 0xfff29597); (0x187f0, 0x8f758893);
  (0x18938, 0xa0090ef); (0x18968, 0xf41fe0ef); (0x1898c, 0xf1dfe0ef); (0x189a8, 0xf01fe0ef);
  (0x189dc, 0x7fd080ef); (0x18a0c, 0xe9dfe0ef); (0x18a30, 0xe79fe0ef); (0x18a60, 0x779080ef);
  (0x18a90, 0xe19fe0ef); (0x18ab4, 0xdf5fe0ef); (0x18ad0, 0xdd9fe0ef); (0x18b04, 0x6d5080ef);
  (0x18b34, 0xd75fe0ef); (0x18b54, 0xd55fe0ef); (0x18b70, 0x360000ef); (0x18b94, 0x33c000ef);
  (0x18be4, 0xd61f90ef); (0x18c18, 0x184000ef); (0x18c2c, 0x170000ef); (0x18c40, 0x15c000ef);
  (0x18c54, 0x148000ef); (0x18c68, 0x134000ef); (0x18c7c, 0x120000ef); (0x18c90, 0x10c000ef);
  (0x18ca4, 0xf8000ef); (0x18cb8, 0xe4000ef); (0x18d38, 0xc0df90ef); (0x18d98, 0x870fa0ef);
  (0x18dac, 0xfff65697); (0x18db0, 0xf1468693); (0x18dfc, 0x1c1010ef); (0x18eec, 0x11517);
  (0x18ef0, 0xd8c53903); (0x18f24, 0x2b5080ef); (0x18f54, 0x955fe0ef); (0x18f74, 0x935fe0ef);
  (0x18fa0, 0xe69f90ef); (0x19000, 0x11517); (0x19004, 0xc7853a03); (0x1905c, 0xf1010ef);
  (0x19068, 0xfff2a517); (0x19070, 0xf4250513); (0x19084, 0xfff2a517); (0x1908c, 0xf2650513);
  (0x190c4, 0x91010ef); (0x190e0, 0xb9010ef); (0x190f0, 0x204020ef); (0x19104, 0x2f1010ef);
  (0x19118, 0x159010ef); (0x19154, 0xfff34517); (0x19158, 0xabc53507); (0x1915c, 0x660010ef);
  (0x19170, 0x285010ef); (0x191a0, 0xd1010ef); (0x191a8, 0xfff2d597); (0x191ac, 0xfff32617);
  (0x191b0, 0x98958593); (0x191b4, 0x41160993); (0x19210, 0xb05fc0ef); (0x19230, 0x58c010ef);
  (0x1924c, 0x1b0020ef); (0x19258, 0x1b4020ef); (0x19268, 0xfff2e597); (0x1926c, 0xfff32617);
  (0x19270, 0xfda58593); (0x19274, 0xc3460993); (0x192b0, 0x728080ef); (0x192e0, 0xdc8fe0ef);
  (0x19300, 0xda8fe0ef); (0x1931c, 0xd8cfe0ef); (0x19338, 0xd70fe0ef); (0x1936c, 0x66c080ef);
  (0x1939c, 0xd0cfe0ef); (0x193bc, 0xcecfe0ef); (0x19454, 0x7c0020ef); (0x19464, 0x691010ef);
  (0x19478, 0x31020ef); (0x1948c, 0x771010ef); (0x194a0, 0x754010ef); (0x194b4, 0x5bc010ef);
  (0x194c0, 0xfff34517); (0x194c4, 0xa0853503); (0x1975c, 0x60010ef); (0x19778, 0x495010ef);
  (0x19784, 0x479010ef); (0x19864, 0xfff33797); (0x19880, 0x7ac78913); (0x198a0, 0x1d0010ef);
  (0x198b4, 0x4e0020ef); (0x198d4, 0x221010ef); (0x198e4, 0x211010ef); (0x198f8, 0x305010ef);
  (0x1990c, 0x2e8010ef); (0x19934, 0x13c010ef); (0x199f4, 0x7e5070ef); (0x19a24, 0xe85fd0ef);
  (0x19a68, 0x8d010ef); (0x19a78, 0x3c4020ef); (0x19ab8, 0x3d010ef); (0x19acc, 0x141010ef);
  (0x19ae0, 0xfff33517); (0x19ae4, 0x32053507); (0x19b08, 0xda1fd0ef); (0x19b24, 0xd85fd0ef);
  (0x19b50, 0x689070ef); (0x19b80, 0xd29fd0ef); (0x19ba0, 0xd09fd0ef); (0x19bc4, 0xce5fd0ef);
  (0x19bec, 0x5ed070ef); (0x19c1c, 0xc8dfd0ef); (0x19c3c, 0xc6dfd0ef); (0x19c58, 0xc51fd0ef);
  (0x19c84, 0x555070ef); (0x19cb4, 0xbf5fd0ef); (0x19cd4, 0xbd5fd0ef); (0x19cf0, 0xfff33517);
  (0x19cf4, 0x7053507); (0x19cfc, 0xfff33517); (0x19d00, 0x1a453507); (0x19d04, 0x2b9000ef);
  (0x19d38, 0x5bc010ef); (0x19d54, 0x6a1000ef); (0x19d70, 0x685000ef); (0x19d90, 0x67c010ef);
  (0x19d9c, 0x4d5000ef); (0x1a0dc, 0xfd070ef); (0x1a110, 0xf98fd0ef); (0x1a138, 0xf70fd0ef);
  (0x1a158, 0xf50fd0ef); (0x1a194, 0x45070ef); (0x1a1c8, 0xee0fd0ef); (0x1a1f0, 0xeb8fd0ef);
  (0x1a2ec, 0xdbcfd0ef); (0x1a314, 0xfff2a597); (0x1a324, 0x85658513); (0x1a3dc, 0xcccfd0ef);
  (0x1a424, 0xc84fd0ef); (0x1a458, 0xc50fd0ef); (0x1a484, 0xa4dfe0ef); (0x1a4ac, 0xbfcfd0ef);
  (0x1a4c8, 0xfff29517); (0x1a4cc, 0x6a250513); (0x1a4d8, 0xbd0fd0ef); (0x1a5a0, 0xb08fd0ef);
  (0x1a5c8, 0x909fe0ef); (0x1a604, 0x3d4070ef); (0x1a634, 0xa74fd0ef); (0x1a654, 0xa54fd0ef);
  (0x1a668, 0xfa0f80ef); (0x1a67c, 0x14000ef); (0x1a76c, 0x9d8f80ef); (0x1a9d4, 0x9c000ef);
  (0x1a9dc, 0xfff32517); (0x1a9e0, 0x58453507); (0x1a9e4, 0xdd9ff0ef); (0x1a9f8, 0x1fc000ef);
  (0x1b34c, 0x40006f); (0x1ba70, 0xac000ef); (0x1bad0, 0x7c000ef); (0x1bb30, 0xfff62597);
  (0x1bb34, 0x2ec58593); (0x1c688, 0xb597); (0x1c68c, 0x98c58593); (0x1c69c, 0x92df706f);
  (0x1c6ac, 0x12697); (0x1c6b0, 0xf506b403); (0x1c6c0, 0xfffff717); (0x1c6c4, 0x27870713);
  (0x1c71c, 0xa1cff0ef); (0x1c73c, 0x850fb0ef); (0x1c760, 0x9617); (0x1c764, 0x7c463903);
  (0x1c7a0, 0x4e4010ef); (0x1c7a4, 0x517); (0x1c7b0, 0x6850513); (0x1c7dc, 0x88df70ef);
  (0x1c808, 0x8adf20ef); (0x1c864, 0x6a1000ef); (0x1c894, 0x671000ef); (0x1c940, 0xfff2c697);
  (0x1c944, 0xa646b683); (0x1c948, 0xfff2c717); (0x1c94c, 0xa0473703); (0x1ceec, 0xfff2b597);
  (0x1cef0, 0xfff2b717); (0x1cef4, 0x785b683); (0x1cef8, 0x1c73703); (0x1cf60, 0xc10ff0ef);
  (0x1cf84, 0x39597); (0x1cf88, 0x4df58683); (0x1cfb4, 0x4c058fa3); (0x1d2a4, 0xfddff06f);
  (0x1d2bc, 0xbfdf10ef); (0x1d2dc, 0xd8dfc0ef); (0x1d2f4, 0x889ed0ef); (0x1d310, 0xf6ced06f);
  (0x1d338, 0xc31fc0ef); (0x1d344, 0xf38ed06f); (0x237e0, 0x98000ef); (0x2381c, 0x6558d0ef);
  (0x23828, 0x96517); (0x2382c, 0xf6053503); (0x2383c, 0xfffaf517); (0x23840, 0xfffb1597);
  (0x23844, 0xe8e50513); (0x23848, 0x37158593); (0x2385c, 0x8a0fa06f); (0x2388c, 0x134000ef);
  (0x238b8, 0x97597); (0x238bc, 0xc858493); (0x238d8, 0x384020ef); (0x238e0, 0x96517);
  (0x238e4, 0xea853503); (0x238f4, 0xfffaf517); (0x238f8, 0xfffb0597); (0x238fc, 0xdd650513);
  (0x23900, 0xf9958593); (0x23918, 0xfe5f906f); (0x23948, 0x2d87f0ef); (0x2395c, 0x2d5030ef);
  (0x23968, 0x2b87f0ef); (0x2396c, 0x96517); (0x23970, 0xe1c53503); (0x23980, 0xfffb6517);
  (0x23984, 0xfffb0597); (0x23988, 0x67f50513); (0x2398c, 0xf0d58593); (0x23994, 0xf69f90ef);
  (0x23a14, 0x96697); (0x23a18, 0xd746b403); (0x23a28, 0xfffb7697); (0x23a2c, 0xfffb2717);
  (0x23a30, 0xb4d68693); (0x23a34, 0x87470713); (0x23a50, 0xe11f90ef); (0x23a5c, 0xfffb0517);
  (0x23a60, 0xfffb2597); (0x23a64, 0xe4550513); (0x23a68, 0x84058593); (0x23a70, 0x96517);
  (0x23a74, 0xd1853503); (0x23a84, 0xfffad517); (0x23a88, 0xfffb2597); (0x23a8c, 0xf2150513);
  (0x23a90, 0x81858593); (0x23a98, 0x96517); (0x23a9c, 0xcf053503); (0x23aac, 0xfffb3517);
  (0x23ab0, 0xfffb1597); (0x23ab4, 0x4cb50513); (0x23ab8, 0x7f058593); (0x23ad8, 0x96697);
  (0x23adc, 0xcb06b403); (0x23aec, 0xfffb7697); (0x23af0, 0xfffb1717); (0x23af4, 0xa8968693);
  (0x23af8, 0x7b070713); (0x23b14, 0xd4df90ef); (0x23b20, 0xfffb6517); (0x23b24, 0xfffb1597);
  (0x23b28, 0xa4f50513); (0x23b2c, 0x77c58593); (0x23b34, 0x96517); (0x23b38, 0xc5453503);
  (0x23b48, 0xfffaf517); (0x23b4c, 0xfffb1597); (0x23b50, 0x1c650513); (0x23b54, 0x75458593);
  (0x23b78, 0xd85f906f); (0x23b88, 0x96517); (0x23b8c, 0xc0053503); (0x23b9c, 0xfffae517);
  (0x23ba0, 0xfffb1597); (0x23ba4, 0x58450513); (0x23ba8, 0x70058593); (0x23bbc, 0x96517);
  (0x23bc0, 0xbcc53503); (0x23bd0, 0xfffb7517); (0x23bd4, 0xfffb1597); (0x23bd8, 0x1050513);
  (0x23bdc, 0x6cc58593); (0x23be8, 0x96517); (0x23bec, 0xba053503); (0x23bfc, 0xfffb4517);
  (0x23c00, 0xfffb1597); (0x23c04, 0xf0f50513); (0x23c08, 0x6a058593); (0x23c0c, 0xc55f90ef);
  (0x23c48, 0x6a17e0ef); (0x23c58, 0xb1000ef); (0x23c64, 0x12d000ef); (0x23c70, 0x1a9000ef);
  (0x23c9c, 0x96517); (0x23ca0, 0xaec53503); (0x23cb0, 0xfffaf517); (0x23cb4, 0xfffb1597);
  (0x23cb8, 0xa1a50513); (0x23cbc, 0x5ec58593); (0x23cf8, 0x96517); (0x23cfc, 0xa9053503);
  (0x23d0c, 0xfffad517); (0x23d10, 0xfffb6597); (0x23d14, 0x75150513); (0x23d18, 0x87758593);
  (0x23d20, 0xb0df906f); (0x23d7c, 0x97597); (0x23d80, 0xc0c5b583); (0x23d90, 0x6917e0ef);
  (0x23da4, 0x68c030ef); (0x23db0, 0x6717e0ef); (0x23dc0, 0x96517); (0x23dc4, 0x9c853503);
  (0x23dd4, 0xfffb7517); (0x23dd8, 0xfffb2597); (0x23ddc, 0x4d250513); (0x23de0, 0xa9258593);
  (0x23df4, 0xa6df906f); (0x23e8c, 0x95517); (0x23e90, 0x6d053503); (0x23ea0, 0xfffad517);
  (0x23ea4, 0xfffb8597); (0x23ea8, 0x39150513); (0x23eac, 0x24d58593); (0x23eb4, 0xf4cf906f);
  (0x23f04, 0x7e1020ef); (0x23f20, 0x4ad020ef); (0x23f34, 0x95517); (0x23f38, 0x30853503);
  (0x23f48, 0xfffad517); (0x23f4c, 0xfffb2597); (0x23f50, 0xfc950513); (0x23f54, 0x9658593);
  (0x23f6c, 0xb74f906f); (0x23f70, 0x95517); (0x23f74, 0x2cc53503); (0x23f84, 0xfffb5517);
  (0x23f88, 0xfffb2597); (0x23f8c, 0xc150513); (0x23f90, 0x5a58593); (0x23f98, 0xb48f90ef);
  (0x23fd8, 0x95517); (0x23fdc, 0x26453503); (0x23fec, 0xfffad517); (0x23ff0, 0xfffb6597);
  (0x23ff4, 0xf2550513); (0x23ff8, 0x6d858593); (0x24000, 0xae0f906f); (0x24008, 0x95597);
  (0x2400c, 0x2345b583); (0x24020, 0xfffb0517); (0x24024, 0xfffb6597); (0x24028, 0xfeb50513);
  (0x2402c, 0x6a458593); (0x24034, 0xaacf906f); (0x24060, 0x95517); (0x24064, 0x1dc53503);
  (0x24074, 0xfffad517); (0x24078, 0xfffb2597); (0x2407c, 0xe9d50513); (0x24080, 0xf5d58593);
  (0x24088, 0xa58f906f); (0x24090, 0x95597); (0x24094, 0x1ac5b583); (0x240a8, 0xfffb5517);
  (0x240ac, 0xfffb2597); (0x240b0, 0x8bc50513); (0x240b4, 0xf2958593); (0x240bc, 0xa24f906f);
  (0x240e8, 0x95517); (0x240ec, 0x15453503); (0x240fc, 0xfffad517); (0x24100, 0xfffac597);
  (0x24104, 0xe1550513); (0x24108, 0x37758593); (0x24110, 0x9d0f906f); (0x24114, 0x95517);
  (0x24118, 0x12853503); (0x24128, 0xfffb3517); (0x2412c, 0xfffac597); (0x24130, 0x4d450513);
  (0x24134, 0x34b58593); (0x2413c, 0x9a4f906f); (0x24160, 0x95517); (0x24164, 0xdc453503);
  (0x24174, 0xfffad517); (0x24178, 0xfffb3597); (0x2417c, 0xa8550513); (0x24180, 0x70c58593);
  (0x24188, 0xe41f806f); (0x241ac, 0x95517); (0x241b0, 0xad853503); (0x241c0, 0xfffac517);
  (0x241c4, 0xfffac597); (0x241c8, 0x79950513); (0x241cc, 0xcef58593); (0x241d4, 0xb55f806f);
  (0x241f8, 0x95517); (0x241fc, 0xa0053503); (0x2420c, 0xfffac517); (0x24210, 0xfffac597);
  (0x24214, 0x6c150513); (0x24218, 0x6dc58593); (0x24220, 0xb4df806f); (0x24244, 0x95517);
  (0x24248, 0x91c53503); (0x24258, 0xfffac517); (0x2425c, 0xfffb5597); (0x24260, 0x5dd50513);
  (0x24264, 0x1cf58593); (0x2426c, 0x999f806f); (0x242f8, 0xbb4fe0ef); (0x24310, 0x94517);
  (0x24314, 0xae853503); (0x24328, 0xfffb0517); (0x2432c, 0xfffb1597); (0x24330, 0xbbd50513);
  (0x24334, 0xd1858593); (0x24338, 0xb99f70ef); (0x24340, 0x94517); (0x24344, 0xab853503);
  (0x24354, 0xfffab517); (0x24358, 0xfffb1597); (0x2435c, 0x77950513); (0x24360, 0xcec58593);
  (0x2437c, 0xb21f706f); (0x2438c, 0x858ff0ef); (0x24398, 0xfbdfd0ef); (0x243d0, 0xfffb7597);
  (0x243d4, 0x15458713); (0x24544, 0xafdfd0ef); (0x24554, 0x92517); (0x24558, 0x5d853503);
  (0x24568, 0xfffae517); (0x2456c, 0xfffab597); (0x24570, 0xf750513); (0x24574, 0x52e58593);
  (0x24580, 0x92517); (0x24584, 0x5ac53503); (0x24594, 0xfffae517); (0x24598, 0xfffab597);
  (0x2459c, 0x9e750513); (0x245a0, 0x50258593); (0x245a8, 0x92517); (0x245ac, 0x58453503);
  (0x245bc, 0xfffa9517); (0x245c0, 0xfffab597); (0x245c4, 0x7b750513); (0x245c8, 0x4da58593);
  (0x245d0, 0x92517); (0x245d4, 0x55c53503); (0x245e4, 0xfffb2517); (0x245e8, 0xfffab597);
  (0x245ec, 0x3ab50513); (0x245f0, 0x4b258593); (0x24610, 0xdc0f606f); (0x24634, 0x92597);
  (0x24638, 0x4f85b583); (0x24648, 0xfffb2517); (0x2464c, 0xfffab597); (0x24650, 0x35e50513);
  (0x24654, 0x44e58593); (0x24664, 0x92597); (0x24668, 0x4c85b583); (0x24678, 0xfffaf517);
  (0x2467c, 0xfffab597); (0x24680, 0xbc450513); (0x24684, 0x41e58593); (0x2468c, 0xd78f60ef);
  (0x24698, 0x92517); (0x2469c, 0x49453503); (0x246b0, 0xfffaa517); (0x246b4, 0xfffab597);
  (0x246b8, 0xb6a50513); (0x246bc, 0x3e658593); (0x246c4, 0xd40f60ef); (0x246e0, 0x92597);
  (0x246e4, 0x44c5b583); (0x246f4, 0xfffaf517); (0x246f8, 0xfffab597); (0x246fc, 0xb7650513);
  (0x24700, 0x3a258593); (0x24718, 0x92517); (0x2471c, 0x41453503); (0x24730, 0xfffb1517);
  (0x24734, 0xfffab597); (0x24738, 0xd7950513); (0x2473c, 0x36658593); (0x24744, 0x92517);
  (0x24748, 0x3e853503); (0x2475c, 0xfffab517); (0x24760, 0xfffab597); (0x24764, 0xda750513);
  (0x24768, 0x33a58593); (0x2476c, 0xc98f60ef); (0x24780, 0x7b4010ef); (0x247a4, 0x92517);
  (0x247a8, 0x38853503); (0x247bc, 0xfffaf517); (0x247c0, 0xfffab597); (0x247c4, 0x5ca50513);
  (0x247c8, 0x2da58593); (0x24808, 0x7bc7b0ef); (0x24810, 0x7b47b0ef); (0x2481c, 0x92517);
  (0x24820, 0x31053503); (0x24830, 0xfffb4517); (0x24834, 0xfffab597); (0x24838, 0xe1a50513);
  (0x2483c, 0x25758593); (0x24850, 0xbb4f606f); (0x248b4, 0x91517); (0x248b8, 0x31453503);
  (0x248c8, 0xfffab517); (0x248cc, 0x8e250513); (0x248d4, 0x91517); (0x248d8, 0x2f453503);
  (0x248e8, 0xfffb0517); (0x248ec, 0xca750513); (0x24904, 0x91517); (0x24908, 0x2c453503);
  (0x24918, 0xfffad517); (0x2491c, 0x3d550513); (0x24924, 0x91517); (0x24928, 0x2a453503);
  (0x24938, 0xfffad517); (0x2493c, 0x3aa50513); (0x24940, 0xfffb2597); (0x24944, 0xb8458593);
  (0x2497c, 0xbc0f506f); (0x249e8, 0x5407a0ef); (0x24a14, 0x5147a0ef); (0x24a24, 0x91517);
  (0x24a2c, 0x1a453c83); (0x24a30, 0xfffb2517); (0x24a34, 0xa6f50a13); (0x24a38, 0xfffa8517);
  (0x24a3c, 0x3e850a93); (0x24b64, 0x908f50ef); (0x24bc0, 0xc5cfb0ef); (0x24be4, 0x8e0fb0ef);
  (0x24bf0, 0x964fc0ef); (0x24c10, 0x538040ef); (0x24c28, 0x91517); (0x24c2c, 0xb4053503);
  (0x24c3c, 0xfffb3517); (0x24c40, 0xfffb3597); (0x24c44, 0x6f650513); (0x24c48, 0x70858593);
  (0x24c50, 0x91517); (0x24c54, 0xb1853503); (0x24c64, 0xfffa8517); (0x24c68, 0xfffb3597);
  (0x24c6c, 0xd1050513); (0x24c70, 0x6e058593); (0x24c9c, 0xb71f406f); (0x24e60, 0x91517);
  (0x24e64, 0x90853503); (0x24e74, 0xfffad517); (0x24e78, 0xfffb3597); (0x24e7c, 0xa2750513);
  (0x24e80, 0x4d058593); (0x24e88, 0x985f40ef); (0x24f14, 0xcb1f70ef); (0x24f20, 0xae9f70ef);
  (0x24f34, 0xfe8f70ef); (0x24f40, 0xb11f60ef); (0x24f4c, 0xb95f70ef); (0x25020, 0x8c517);
  (0x25024, 0x4d453503); (0x25034, 0xfffa9517); (0x25038, 0xfffaf597); (0x2503c, 0x28950513);
  (0x25040, 0xad958593); (0x25048, 0x8c597); (0x2504c, 0x4ac5b583); (0x2505c, 0xfffa4517);
  (0x25060, 0xfffaf597); (0x25064, 0x16d50513); (0x25068, 0xab158593); (0x2508c, 0xd0cf006f);
  (0x25170, 0x7d517); (0x25174, 0xb2453503); (0x25184, 0xfff9a517); (0x25188, 0xfff99617);
  (0x2518c, 0x39250513); (0x25190, 0xc9b60693); (0x2519c, 0xbd1e00ef); (0x251a4, 0x7d517);
  (0x251a8, 0xaf053503); (0x251b8, 0xfff9b517); (0x251bc, 0xfff99597); (0x251c0, 0x4a350513);
  (0x251c4, 0xc6758593); (0x25278, 0x7d517); (0x2527c, 0xa1c53503); (0x2528c, 0xfff9e517);
  (0x25290, 0xfff99597); (0x25294, 0x95f50513); (0x25298, 0xb9358593); (0x252a0, 0x7d517);
  (0x252a4, 0x9f453503); (0x252b4, 0xfff9a517); (0x252b8, 0xfff99597); (0x252bc, 0x28550513);
  (0x252c0, 0xb6b58593); (0x252f0, 0xb19e006f); (0x25300, 0x7d517); (0x25304, 0x99453503);
  (0x25314, 0xfff95517); (0x25318, 0xfff99597); (0x2531c, 0xdd550513); (0x25320, 0xb0b58593);
  (0x25338, 0x7d517); (0x2533c, 0x95c53503); (0x2534c, 0xfff94517); (0x25350, 0xfff99597);
  (0x25354, 0x11650513); (0x25358, 0xad358593); (0x25390, 0xb3de60ef); (0x253a0, 0xe51e60ef);
  (0x253e4, 0xe59e60ef); (0x253fc, 0x8e5e60ef); (0x25424, 0xd14eb0ef); (0x25438, 0xcece70ef);
  (0x25444, 0xdf9e60ef); (0x25448, 0x7d517); (0x2544c, 0x84c53503); (0x2545c, 0xfff9c517);
  (0x25460, 0xfff99597); (0x25464, 0x70450513); (0x25468, 0x9c358593); (0x25470, 0x7d517);
  (0x25474, 0x82453503); (0x25484, 0xfff9b517); (0x25488, 0xfff99597); (0x2548c, 0xc8850513);
  (0x25490, 0x99b58593); (0x25498, 0x7c517); (0x2549c, 0x7fc53503); (0x254ac, 0xfff97517);
  (0x254b0, 0xfff99597); (0x254b4, 0xa8850513); (0x254b8, 0x97358593); (0x254c0, 0x7c517);
  (0x254c4, 0x7d453503); (0x254d4, 0xfff98517); (0x254d8, 0xfff99597); (0x254dc, 0xc5250513);
  (0x254e0, 0x94b58593); (0x254f0, 0x87de00ef); (0x254f8, 0x7c517); (0x254fc, 0x79c53503);
  (0x2550c, 0xfff9c517); (0x25510, 0xfff99597); (0x25514, 0x84550513); (0x25518, 0x91358593);
  (0x2552c, 0xd11e60ef); (0x25530, 0x7c517); (0x25534, 0x76453503); (0x25544, 0xfff9f517);
  (0x25548, 0xfff99597); (0x2554c, 0x3ba50513); (0x25550, 0x8db58593); (0x2555c, 0xd25e70ef);
  (0x2558c, 0x70740ef); (0x255a0, 0x884ea0ef); (0x255b8, 0xc85e60ef); (0x255bc, 0x7c517);
  (0x255c0, 0x6d853503); (0x255d0, 0xfff95517); (0x255d4, 0xfff99597); (0x255d8, 0x6cf50513);
  (0x255dc, 0x84f58593); (0x255e4, 0x825e00ef)].

Definition v9_reloc : Reloc := {|
  rl_segs := Ubsan.M.loaded_segments;
  rl_dtab := v9_dtab;
  rl_stab := v9_stab;
  rl_img_lo := 0x10000; rl_rw_lo := 0xf5000; rl_img_hi := 0x12c000;
  rl_dtab_ok := eq_refl |}.
End V9Reloc.

From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require StartupTac.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require ArgvEnv.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require RefLayout.
Module V9StartupDefs.
Import Stdlib.ZArith.ZArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.leptonica.edge_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.StartupTac.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.ArgvEnv.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.RefLayout.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)





Import ListNotations.
Open Scope bv_scope.

Abbreviation RPH := Ubsan.M.phdrs.

(* [comment removed for export] *)
Fixpoint after_last_slash (s : list byte) (i acc : nat) : nat :=
  match s with
  | [] => acc
  | b :: s' => after_last_slash s' (S i) (if bv_eqb b (Z_to_bv 8 47) then S i else acc)
  end.
Definition progname_off (s : list byte) : nat := after_last_slash s 0 0.

Section VP1. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma after_last_slash_le : forall s i acc, (acc <= i)%nat ->
  (after_last_slash s i acc <= i + length s)%nat.
Proof.
  induction s as [|c s IH]; intros i acc H; cbn [after_last_slash length]; [lia|].
  etransitivity; [apply IH; destruct (bv_eqb _ _); lia | lia].
Qed.
End VP1.

Section VP2. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma progname_off_le : forall s, (progname_off s <= length s)%nat.
Proof. intro s. unfold progname_off. pose proof (after_last_slash_le s 0 0). lia. Qed.
End VP2.

Section Canary.
Context {fx : FPState}.
  Variable drw : EntryDraw.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition RB : list byte := at_random_bytes (ed_random drw).
  Definition rba : list byte := firstn 4 (skipn 0 RB).
  Definition rbb : list byte := firstn 4 (skipn 4 RB).
  Definition rwa : word := Z_to_bv 64 (bytes_le_to_Z rba).
  Definition rwb : word := Z_to_bv 64 (bytes_le_to_Z rbb).
  Definition guard_bytes : list byte :=
    firstn 1 (word_to_le_bytes 4 (v_lw rwa)) ++ [Z_to_bv 8 0]
    ++ skipn 2 (word_to_le_bytes 4 (v_lw rwa)) ++ word_to_le_bytes 4 (v_lw rwb).
  Definition canary_w : word := Z_to_bv 64 (bytes_le_to_Z guard_bytes).

  Lemma length_RB : length RB = 16%nat.
  Proof. unfold RB. apply length_at_random_bytes. Qed.
  Lemma length_rba : length rba = 4%nat.
  Proof. unfold rba. rewrite firstn_length_le; [reflexivity|]. rewrite length_skipn, length_RB. lia. Qed.
  Lemma length_rbb : length rbb = 4%nat.
  Proof. unfold rbb. rewrite firstn_length_le; [reflexivity|]. rewrite length_skipn, length_RB. lia. Qed.
  Lemma length_guard_bytes : length guard_bytes = 8%nat.
  Proof.
    unfold guard_bytes. rewrite !length_app, length_skipn, !length_N_to_le_bytes.
    rewrite firstn_length_le by (rewrite length_N_to_le_bytes; lia). reflexivity.
  Qed.
  Lemma bytes_val : forall bs, (length bs <= 8)%nat ->
    bytes_le_to_Z bs = bv_unsigned (Z_to_bv 64 (bytes_le_to_Z bs)).
  Proof.
    intros bs Hl. pose proof (bytes_le_to_Z_bound bs) as Hb. pose proof (bytes_le_to_Z_nonneg bs) as Hn.
    assert (2 ^ (8 * Z.of_nat (length bs)) <= 2^64)%Z by (apply Z.pow_le_mono_r; lia).
    rewrite u_Z2bv by lia. reflexivity.
  Qed.
  Lemma rwa_val : bytes_le_to_Z rba = bv_unsigned rwa.
  Proof. unfold rwa. apply bytes_val. rewrite length_rba. lia. Qed.
  Lemma rwb_val : bytes_le_to_Z rbb = bv_unsigned rwb.
  Proof. unfold rwb. apply bytes_val. rewrite length_rbb. lia. Qed.
  Lemma canary_val : bytes_le_to_Z guard_bytes = bv_unsigned canary_w.
  Proof. unfold canary_w. apply bytes_val. rewrite length_guard_bytes. lia. Qed.

  (* [comment removed for export] *)
  Lemma rdn_guard : forall segs D,
    rdn segs (wbytes (wbytes (wbytes D
      (Z_to_bv 64 0x12aac8) (word_to_le_bytes 4 (v_lw rwa)))
      (Z_to_bv 64 0x12aacc) (word_to_le_bytes 4 (v_lw rwb)))
      (Z_to_bv 64 0x12aac9) [Z_to_bv 8 0]) (Z_to_bv 64 0x12aac8) 8 = Some guard_bytes.
  Proof.
    intros segs D. unfold guard_bytes.
    set (A := word_to_le_bytes 4 (v_lw rwa)). set (B := word_to_le_bytes 4 (v_lw rwb)).
    assert (HA : length A = 4%nat) by (subst A; apply length_N_to_le_bytes).
    assert (HB : length B = 4%nat) by (subst B; apply length_N_to_le_bytes).
    assert (Hin : rdn segs (wbytes D (Z_to_bv 64 0x12aac8) A) (Z_to_bv 64 0x12aac8) 4 = Some A).
    { rewrite <- HA at 1. apply rdn_wbytes_hit. rewrite HA. unorm. lia. }
    change 8%nat with (1 + (1 + (2 + 4)))%nat.
    apply rdn_app.
    { rewrite rdn_wbytes_out by (cbn [length]; unorm; lia).
      rewrite rdn_wbytes_out by (rewrite ?HB; unorm; lia).
      exact (SeqExec.rdn_firstn _ _ _ _ _ 1 Hin ltac:(lia)). }
    apply rdn_app.
    { change (Z_to_bv 64 1223368 + nat_to_word 1) with (Z_to_bv 64 0x12aac9 : word).
      exact (rdn_wbytes_hit segs [Z_to_bv 8 0] _ (Z_to_bv 64 0x12aac9) ltac:(cbn [length]; unorm; lia)). }
    apply rdn_app.
    { change (Z_to_bv 64 1223368 + nat_to_word 1 + nat_to_word 1) with (Z_to_bv 64 0x12aaca : word).
      rewrite rdn_wbytes_out by (cbn [length]; unorm; lia).
      rewrite rdn_wbytes_out by (rewrite ?HB; unorm; lia).
      exact (SeqExec.rdn_skipn _ _ _ _ _ 2 Hin ltac:(lia)). }
    change (Z_to_bv 64 1223368 + nat_to_word 1 + nat_to_word 1 + nat_to_word 2) with (Z_to_bv 64 0x12aacc : word).
    rewrite rdn_wbytes_out by (cbn [length]; unorm; lia).
    rewrite <- HB at 1. apply rdn_wbytes_hit. rewrite HB. unorm. lia.
  Qed.

End Canary.

Section Defs.
Context {fx : FPState}.   (* [comment removed for export] *)
  Variable sp0 : word.
  Variables av ev : list (list byte).
  Variable uid : word.
  Variables (hw : word) (drw : EntryDraw).   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition aux_base : word := Z_to_bv 64 (bv_unsigned sp0 - 368).
  (* [comment removed for export] *)
  Definition argv_w : word := Z_to_bv 64 (bv_unsigned sp0 + 8).
  Definition envp_w : word := Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av)).
  Definition auxv_w : word :=
    Z_to_bv 64 (bv_unsigned sp0 + 24 + 8 * Z.of_nat (length av) + 8 * Z.of_nat (length ev)).
  Definition argc_w : word := argcN av.
  (* [comment removed for export] *)
  Definition pn_w : word := cat_argv_ptr sp0 av ev 0.
  Definition progname_w : word :=
    Z_to_bv 64 (bv_unsigned pn_w + Z.of_nat (progname_off (nth 0 av []))).
  (* [comment removed for export] *)
  Definition rnd_w : word := at_random_ptr sp0 av ev.

  (* [comment removed for export] *)
  Definition D_libc : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (fun _ => None)
      (Z_to_bv 64 0x10a788) (word_to_le_bytes 8 envp_w))          (* [comment removed for export] *)
      (Z_to_bv 64 0x12aaf0) (word_to_le_bytes 8 auxv_w))          (* [comment removed for export] *)
      (Z_to_bv 64 0x12ab50) (word_to_le_bytes 8 hw))            (* [comment removed for export] *)
      (Z_to_bv 64 0x12ab18) (word_to_le_bytes 8 (Z_to_bv 64 4096))) (* [comment removed for export] *)
      (Z_to_bv 64 0x12aae0) (word_to_le_bytes 8 pn_w))            (* [comment removed for export] *)
      (Z_to_bv 64 0x12aad8) (word_to_le_bytes 8 progname_w).      (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition J_lsm (J : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes
    (wbytes (wbytes (wbytes (wbytes J
      (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0xe1c50)))
      (Z_to_bv 64 (bv_unsigned sp0 - 48)) (word_to_le_bytes 8 argv_w))
      (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 argc_w))
      (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0x5cca0)).

  (* [comment removed for export] *)
  Definition J_aux (Jf : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes
      (wbytes Jf aux_base (zeros 304))
      (Z_to_bv 64 (bv_unsigned sp0 - 344)) (word_to_le_bytes 8 (Z_to_bv 64 0x10040)))  (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 336)) (word_to_le_bytes 8 (Z_to_bv 64 56)))       (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 328)) (word_to_le_bytes 8 (Z_to_bv 64 10)))       (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 240)) (word_to_le_bytes 8 hw))                   (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 320)) (word_to_le_bytes 8 (Z_to_bv 64 4096)))     (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 280)) (word_to_le_bytes 8 uid))                  (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 272)) (word_to_le_bytes 8 uid))                  (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 184)) (word_to_le_bytes 8 (Z_to_bv 64 0)))        (* [comment removed for export] *)
      (Z_to_bv 64 (bv_unsigned sp0 - 168)) (word_to_le_bytes 8 rnd_w).                  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition D_tlsA (D : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes D
      (Z_to_bv 64 0x12a880) (word_to_le_bytes 8 (Z_to_bv 64 0)))        (* [comment removed for export] *)
      (Z_to_bv 64 0x12a890) (word_to_le_bytes 8 (Z_to_bv 64 0)))        (* [comment removed for export] *)
      (Z_to_bv 64 0x12a888) (word_to_le_bytes 8 (Z_to_bv 64 8)))        (* [comment removed for export] *)
      (Z_to_bv 64 0x12ab00) (word_to_le_bytes 8 (Z_to_bv 64 0xe0)))     (* [comment removed for export] *)
      (Z_to_bv 64 0x12ab08) (word_to_le_bytes 8 (Z_to_bv 64 8)))        (* [comment removed for export] *)
      (Z_to_bv 64 0x10a868) (word_to_le_bytes 8 (Z_to_bv 64 0)))        (* [comment removed for export] *)
      (Z_to_bv 64 0x10a850) (word_to_le_bytes 8 (Z_to_bv 64 0x10a868)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x10a790) (word_to_le_bytes 8 (Z_to_bv 64 0x10a790)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x12aae8) [Z_to_bv 8 1])                              (* [comment removed for export] *)
      (Z_to_bv 64 0x10a7b8) (word_to_le_bytes 4 (Z_to_bv 64 2)).        (* [comment removed for export] *)

  Definition D_tlsB (tid : word) (D : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes D
      (Z_to_bv 64 0x10a7b0) (word_to_le_bytes 4 tid))                   (* [comment removed for export] *)
      (Z_to_bv 64 0x10a828) (word_to_le_bytes 8 (Z_to_bv 64 0x12ab20)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x10a808) (word_to_le_bytes 8 (Z_to_bv 64 0x10a808)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x10a798) (word_to_le_bytes 8 (Z_to_bv 64 0x10a790)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x10a7a0) (word_to_le_bytes 8 (Z_to_bv 64 0x10a790)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x10a7a8) (word_to_le_bytes 8 (Z_to_bv 64 0)).        (* [comment removed for export] *)

  Definition D_tls (tid : word) (D : word -> option byte) : word -> option byte :=
    D_tlsB tid (D_tlsA D).

  (* [comment removed for export] *)
  Definition J_tls (J : word -> option byte) (ra s0 s1 s2 s3 s4 s5 : word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes J
      (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 ra))
      (Z_to_bv 64 (bv_unsigned sp0 - 432)) (word_to_le_bytes 8 s0))
      (Z_to_bv 64 (bv_unsigned sp0 - 440)) (word_to_le_bytes 8 s1))
      (Z_to_bv 64 (bv_unsigned sp0 - 448)) (word_to_le_bytes 8 s2))
      (Z_to_bv 64 (bv_unsigned sp0 - 456)) (word_to_le_bytes 8 s3))
      (Z_to_bv 64 (bv_unsigned sp0 - 464)) (word_to_le_bytes 8 s4))
      (Z_to_bv 64 (bv_unsigned sp0 - 472)) (word_to_le_bytes 8 s5).

  Definition D_ssp (D : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes D
      (Z_to_bv 64 0x12aac8) (word_to_le_bytes 4 (v_lw (rwa drw))))  (* [comment removed for export] *)
      (Z_to_bv 64 0x12aacc) (word_to_le_bytes 4 (v_lw (rwb drw))))  (* [comment removed for export] *)
      (Z_to_bv 64 0x12aac9) [Z_to_bv 8 0])                     (* [comment removed for export] *)
      (Z_to_bv 64 0x10a848) (word_to_le_bytes 8 (canary_w drw)).     (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition D_fd (D : word -> option byte) : word -> option byte :=
    wbytes D (Z_to_bv 64 0xfa550) [Z_to_bv 8 1].

  (* [comment removed for export] *)
  Definition D_main (tid : word) : word -> option byte := D_fd (D_ssp (D_tls tid D_libc)).

End Defs.
End V9StartupDefs.

From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Musl Require PFSpec.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica.VL Require LeptStderr.
Module V9LeptEnv.
Import Stdlib.ZArith.ZArith.
Import Stdlib.Lists.List.
Import Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Reloc.Reloc.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica.VL.LeptStderr.
Import V9Reloc.
(* [comment removed for export] *)







Lemma v9_lenv_ok1 : @PFSpec.ls_ok1 v9_reloc (@LG v9_reloc) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma v9_lenv_ok2 : @PFSpec.ls_ok2 v9_reloc (@LG v9_reloc) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition v9_lenv_vl : RelocLeptEnvVL v9_reloc := {| rl_lenv_ok1 := v9_lenv_ok1; rl_lenv_ok2 := v9_lenv_ok2 |}.
End V9LeptEnv.

From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require CatSim.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require SeqExec.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require StepTac.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require WalkTac.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require MmapSim.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require RefMemcpyLib.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Musl Require MemcpyBase.
Module V9MemcpyBase.
Import Stdlib.ZArith.ZArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude.
Import LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.Riscv.Decode.
Import LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.leptonica.edge_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.SeqExec.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.StepTac.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.StoreOk.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.WalkTac.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.MmapSim.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.RefMemcpyLib.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Reloc.Reloc.
Import V9Reloc.
(* [comment removed for export] *)








Import ListNotations.
Open Scope bv_scope.

Abbreviation RSEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)
Abbreviation mcH := (@MemcpyBase.mcH v9_reloc).
Abbreviation MCH := (@MemcpyBase.MCH v9_reloc).

(* [comment removed for export] *)
Ltac rwH :=
  repeat match goal with
         | H : getr ?rg ?i = _ |- context [getr ?rg ?i] => rewrite !H
         end.

(* [comment removed for export] *)
Ltac unorm :=
  repeat match goal with
         | |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
             lazymatch z with context [Z_to_bv 64 _] => fail | _ => rewrite (u_Z2bv z) by lia end
         end.

(* [comment removed for export] *)
Ltac mnorm := gres; imm_norm; rewrite ?v_addi_0; rwH; rewrite ?at_addi; vals_lit.

(* [comment removed for export] *)
Ltac cond_lia :=
  rwH; unfold c_ltu, c_eq, bv_ltu, bv_eqb; imm_norm; unorm;
  first [ apply Z.ltb_lt | apply Z.ltb_ge | apply Z.eqb_eq | apply Z.eqb_neq ]; lia.

(* [comment removed for export] *)
Abbreviation u_andi := MemcpyBase.u_andi.
Abbreviation land_3 := MemcpyBase.land_3.
Abbreviation land_1 := MemcpyBase.land_1.
Abbreviation bits_lt32 := MemcpyBase.bits_lt32.
Abbreviation at_mod4 := MemcpyBase.at_mod4.
End V9MemcpyBase.

From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Reloc Require RelocCode.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Reloc Require CanonCode.
Module V9RelocCode.
Import Stdlib.ZArith.ZArith.
Import Stdlib.Lists.List.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Reloc.Reloc.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Reloc.RelocCode.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Reloc.CanonCode.
Import V9Reloc.
(* [comment removed for export] *)





Lemma v9_code_ok : code_check (@rl_segs v9_reloc) (@rl_delta v9_reloc) canon_code = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Definition v9_code : RelocCode v9_reloc := {| rl_code_ok := v9_code_ok |}.
End V9RelocCode.

From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require StreamSim.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Reloc Require RelocImg.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Reloc Require CanonImg.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Reloc Require RelocSpan.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Reloc Require CanonSpans.
Module V9RelocImg.
Import Stdlib.ZArith.ZArith.
Import Stdlib.Lists.List.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.StreamSim.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Reloc.Reloc.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Reloc.RelocImg.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Reloc.CanonImg.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Reloc.RelocSpan.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Reloc.CanonSpans.
Import V9Reloc.
(* [comment removed for export] *)





Local Open Scope Z_scope.

Lemma v9_cells_ok : @cells_check v9_reloc canon_cells = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Definition v9_img : RelocImg v9_reloc := {| rl_cells_ok := v9_cells_ok |}.

Lemma v9_data_wseg : wseg_ok (@rl_segs v9_reloc) (Z_to_bv 64 0xfa000) (Z.to_nat (@rl_img_hi v9_reloc - 0xfa000)) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma v9_data_ok : (0 <=? 0xfa000) && (0xfa000 <=? @rl_img_hi v9_reloc) && (@rl_img_hi v9_reloc <=? 2^32) = true.
Proof. reflexivity. Qed.

Definition v9_data : RelocData v9_reloc := {| rl_data_lo := 0xfa000; rl_data_ok := v9_data_ok; rl_data_wseg := v9_data_wseg |}.

Lemma v9_hull_ok : @hull_okb v9_reloc v9_data = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma v9_spans_ok : @spans_check v9_reloc v9_data canon_spans = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma v9_orders_ok : @orders_check v9_reloc canon_spans canon_order = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition v9_spans : RelocSpans v9_reloc v9_data := {| rl_hull_ok := v9_hull_ok; rl_spans_ok := v9_spans_ok; rl_orders_ok := v9_orders_ok |}.
End V9RelocImg.

From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng Require RelocLayout.
Module V9RelocML.
Import Stdlib.ZArith.ZArith.
Import Stdlib.NArith.NArith.
Import Stdlib.Lists.List.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng.MallocLayout.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng.RelocLayout.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Reloc.Reloc.
Import V9MallocLayout.
Import V9Reloc.
(* [comment removed for export] *)







Lemma lv9_reloc : LU16 = reloc_layout v9_reloc.
Proof. unfold LU16, reloc_layout. f_equal; first [ reflexivity | apply bv_eq; reflexivity ]. Qed.

(* [comment removed for export] *)
Ltac v9_ml_tail t := rewrite lv9_reloc; exact t.
End V9RelocML.

From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Reloc Require RelocSites.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Reloc Require CanonSites.
Module V9RelocSites.
Import Stdlib.ZArith.ZArith.
Import Stdlib.Lists.List.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Reloc.Reloc.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Reloc.RelocCode.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Reloc.RelocSites.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Reloc.CanonSites.
Import V9Reloc.
(* [comment removed for export] *)





Lemma v9_sites_ok : @sites_check v9_reloc canon_sites = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Definition v9_sites : RelocSites v9_reloc := {| rl_sites_ok := v9_sites_ok |}.
End V9RelocSites.

From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Reloc Require CanonCodeVL.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Reloc Require CanonSitesVL.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Reloc Require CanonImgVL.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica Require RelocLept.
Module V9RelocVL.
Import Stdlib.ZArith.ZArith.
Import Stdlib.Lists.List.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Reloc.Reloc.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Reloc.RelocCode.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Reloc.RelocSites.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Reloc.RelocImg.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Reloc.CanonCodeVL.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Reloc.CanonSitesVL.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Reloc.CanonImgVL.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica.RelocLept.
Import V9Reloc.
(* [comment removed for export] *)






Lemma v9_code_vl_ok : code_check (@rl_segs v9_reloc) (@rl_delta v9_reloc) canon_code_VL = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition v9_code_vl : RelocCodeVL v9_reloc := {| rl_code_vl_ok := v9_code_vl_ok |}.

Lemma v9_sites_vl_ok : @sites_check v9_reloc canon_sites_VL = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition v9_sites_vl : RelocSitesVL v9_reloc := {| rl_sites_vl_ok := v9_sites_vl_ok |}.

Lemma v9_lept_ok : wr_readable_chk (@rl_segs v9_reloc) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition v9_lept : RelocLept v9_reloc := {| rl_wr_readable_ok := v9_lept_ok; rl_pages_ok := eq_refl; rl_clr_extra := nil |}.

Lemma v9_strs_vl_ok : @strs_check v9_reloc canon_strs_VL = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma v9_cells_vl_ok : @cells_check v9_reloc canon_cells_VL = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma v9_spans_vl_ok : @RelocLept.spans_check v9_reloc canon_spans_VL = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition v9_img_vl : RelocImgVL v9_reloc := {| rl_strs_vl_ok := v9_strs_vl_ok; rl_cells_vl_ok := v9_cells_vl_ok; rl_spans_vl_ok := v9_spans_vl_ok |}.
End V9RelocVL.

From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require ExitSim.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require ShapeAlg.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require Nodes.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica Require LibAtomic.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require SumWalkTac.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require RefNodes.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Musl Require ExitBase.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.CliDriver Require AgentNodesG.
Module V9ExitBase.
Import Stdlib.ZArith.ZArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude.
Import LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.Riscv.Decode.
Import LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.leptonica.edge_fuzzer.images.Ubsan.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Import LinuxProcessSemantics.LinuxProcessSem.Fs.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.LinuxProcessSem.Monad.
Import LinuxProcessSemantics.LinuxProcessSem.Specs.
Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.SeqExec.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.StepTac.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.WalkTac.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.StoreOk.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.StreamSim.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.MmapSim.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.ExitSim.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Nodes.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica.LibAtomic.
Export OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica.SumWalkTac.
Export OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.RefNodes.
Export OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.CliDriver.AgentNodesG.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)













Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation RSEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section VP2.
  Context {fx : FPState}.   (* [comment removed for export] *)
Lemma store_ok_data : forall m (a : word) n,
  (0xfa000 <= bv_unsigned a)%Z -> (bv_unsigned a + Z.of_nat n <= 0x12c000)%Z ->
  store_ok RSEGS m a n = true.
Proof.
  exact (@ExitBase.store_ok_data V9Reloc.v9_reloc V9RelocImg.v9_data).
Qed.
End VP2.

(* [comment removed for export] *)
Ltac sok_data := store_ok_peel; apply store_ok_data; zsimp; lia.

(* [comment removed for export] *)
Ltac sok_frame SOK :=
  store_ok_peel;
  eapply (store_ok_sub _ _ _ _ 112%nat); [ | exact SOK | | ]; zsimp; lia.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition file_clean (mem : word -> option byte) (f : Z) (wp rp : word) : Prop :=
  rdn RSEGS mem (Z_to_bv 64 (f + 140)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295))
  /\ rdn RSEGS mem (Z_to_bv 64 (f + 40)) 8%nat = Some (word_to_le_bytes 8 wp)
  /\ rdn RSEGS mem (Z_to_bv 64 (f + 56)) 8%nat = Some (word_to_le_bytes 8 wp)
  /\ rdn RSEGS mem (Z_to_bv 64 (f + 8)) 8%nat = Some (word_to_le_bytes 8 rp)
  /\ rdn RSEGS mem (Z_to_bv 64 (f + 16)) 8%nat = Some (word_to_le_bytes 8 rp).

(* [comment removed for export] *)
Definition stdio_globals (mem : word -> option byte) : Prop :=
  rdn RSEGS mem (Z_to_bv 64 0x12aaeb) 1%nat = Some [Z_to_bv 8 0]            (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0x12af18) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))       (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0x12af08) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))       (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0xfa520) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xfa438)) (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0xfa430) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xfa348)). (* [comment removed for export] *)

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End V9ExitBase.

From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require MuslStrlen.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica Require PortLib.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Musl Require Memchr.
Module V9Memchr.
Import Stdlib.ZArith.ZArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude.
Import LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.Riscv.Decode.
Import LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.leptonica.edge_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.SeqExec.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.StepTac.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.StoreOk.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.WalkTac.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.MmapSim.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.MuslStrlen.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.RefMemcpyLib.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica.PortLib.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Reloc.Reloc.
Import V9Reloc.
Import V9MemcpyBase.
(* [comment removed for export] *)










Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition rodata_clear (mem : word -> option byte) : Prop :=
  forall i, (0x1c3f0 <= i < 0x1c450)%Z -> mem (Z_to_bv 64 i) = None.

Record mchrH (mem : word -> option byte) (s : word) (buf : list byte) (K n : Z) : Prop := MCHRH {
  (* [comment removed for export] *)
  Hbuf : rdn RSEGS mem s (length buf) = Some buf;
  (* [comment removed for export] *)
  Hwin : ((bv_unsigned s + K) / 8 * 8 + 8 <= bv_unsigned s + Z.of_nat (length buf))%Z;
  Hnw  : (bv_unsigned s + Z.of_nat (length buf) < 2 ^ 64)%Z;
  (* [comment removed for export] *)
  HK0  : (0 <= K)%Z;
  Hzero : bv_unsigned (nth (Z.to_nat K) buf (Z_to_bv 8 0)) = 0%Z;
  Hnz  : forall j, (j < Z.to_nat K)%nat -> bv_unsigned (nth j buf (Z_to_bv 8 0)) <> 0%Z;
  (* [comment removed for export] *)
  HKn  : (K + 8 <= n)%Z;
  Hn64 : (n < 2 ^ 64)%Z;
  Hro  : rodata_clear mem }.

(* [comment removed for export] *)
Lemma mchrH_generic : forall mem s buf K n, mchrH mem s buf K n -> @Memchr.mchrH v9_reloc mem s buf K n.
Proof.
  intros mem s buf K n [H1 H2 H3 H4 H5 H6 H7 H8 H9].
  exact (@Memchr.MCHRH v9_reloc mem s buf K n H1 H2 H3 H4 H5 H6 H7 H8
           (@Memchr.rodata_clear_hull v9_reloc mem 0x1c3f0 0x1c450 eq_refl H9)).      (* [comment removed for export] *)
Qed.
End V9Memchr.

From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Musl Require Memcpy.
Module V9Memcpy.
Import Stdlib.ZArith.ZArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude.
Import LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.Riscv.Decode.
Import LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.leptonica.edge_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.SeqExec.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.StepTac.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.StoreOk.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.WalkTac.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.MmapSim.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.RefMemcpyLib.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Reloc.Reloc.
Import V9Reloc.
Import V9RelocCode.
Import V9MemcpyBase.
(* [comment removed for export] *)








Import ListNotations.
Open Scope bv_scope.

Abbreviation RSEGS := Ubsan.M.loaded_segments.

Section Contract.
  Context {fx : FPState}.

  Theorem ref_memcpy : forall (mem0 : word -> option byte) (dst src : word) (n : Z) (bs : list byte)
      (rom : word -> option byte) (HOK : mcH mem0 dst src n bs) regs (ret : word),
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 10 = dst -> getr regs 11 = src -> getr regs 12 = Z_to_bv 64 n ->
    exists regs',
      msteps RSEGS (mkst regs (0xf0a88 : word) mem0 rom) (mkst regs' ret (wbytes mem0 dst bs) rom)
      /\ keeps regs regs'.
  Proof. rl_tail (@Memcpy.ref_memcpy fx v9_reloc v9_code). Qed.
End Contract.
End V9Memcpy.

From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require PureModel.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica Require SumWalkTac.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica Require WalksLib.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Musl Require Memset.
Module V9Memset.
Import Stdlib.ZArith.ZArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.Riscv.Decode.
Import LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.leptonica.edge_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.StartupTac.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.RefMemcpyLib.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.PureModel.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica.SumWalkTac.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica.WalksLib.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Reloc.Reloc.
Import V9Reloc.
Import V9RelocCode.
(* [comment removed for export] *)









Import ListNotations.
Open Scope bv_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Abbreviation memset_clob := Memset.memset_clob.

Section Contract.
  Context {fx : FPState}.

  Theorem memset_spec : forall regs (M rom : word -> option byte) (d n : Z) (ret : word),
    (0 <= d)%Z -> (1 <= n < 2 ^ 64)%Z -> (d + n <= 2 ^ 64)%Z ->
    store_ok SEGS M (Z_to_bv 64 d) (Z.to_nat n) = true -> ret_ok ret ->
    getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 d -> getr regs 11 = Z_to_bv 64 0 ->
    getr regs 12 = Z_to_bv 64 n ->
    exists regs',
      msteps SEGS (mkst regs (0xf1008 : word) M rom) (mkst regs' ret (zf M d [(0, n)]%Z) rom)
      /\ getr regs' 10 = Z_to_bv 64 d
      /\ regs_agree (fun r => In r memset_clob) regs regs'.
  Proof. rl_tail (@Memset.memset_spec fx v9_reloc v9_code). Qed.

  Lemma memset_post_mem : forall (M : word -> option byte) (d n : Z),
    (0 <= d)%Z -> (d + n <= 2 ^ 64)%Z ->
    (forall i, (0 <= i < n)%Z -> zf M d [(0, n)]%Z (Z_to_bv 64 (d + i)) = Some (Z_to_bv 8 0))
    /\ (forall x : word, (bv_unsigned x < d \/ d + n <= bv_unsigned x)%Z -> zf M d [(0, n)]%Z x = M x)
    /\ mem_grows M (zf M d [(0, n)]%Z).
  Proof. exact Memset.memset_post_mem. Qed.

  Corollary memset_at : forall model regs (M rom : word -> option byte) (d n : Z) (ret : word) (S : TSet),
    md_pure model ->
    (0 <= d)%Z -> (1 <= n < 2 ^ 64)%Z -> (d + n <= 2 ^ 64)%Z ->
    store_ok SEGS M (Z_to_bv 64 d) (Z.to_nat n) = true -> ret_ok ret ->
    getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 d -> getr regs 11 = Z_to_bv 64 0 ->
    getr regs 12 = Z_to_bv 64 n ->
    (forall regs', getr regs' 10 = Z_to_bv 64 d -> regs_agree (fun r => In r memset_clob) regs regs' ->
       realizes SEGS (mkCfg (mkst regs' ret (zf M d [(0, n)]%Z) rom) model) S) ->
    realizes SEGS (mkCfg (mkst regs (0xf1008 : word) M rom) model) S.
  Proof. rl_tail (@Memset.memset_at fx v9_reloc v9_code). Qed.
End Contract.
End V9Memset.

From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng Require RefStmts.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng Require RRef_calloc.
Module V9Ref_calloc.
Import Stdlib.ZArith.ZArith.
Import Stdlib.NArith.NArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Import LinuxProcessSemantics.LinuxProcessSem.Fs.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.LinuxProcessSem.Monad.
Import LinuxProcessSemantics.LinuxProcessSem.Specs.
Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng.MallocLayout.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng.RefStmts.
Import V9MallocLayout.
Import V9Reloc.
Import V9RelocCode.
Import V9RelocSites.
Import V9RelocML.
(* [comment removed for export] *)







Section Calloc.
Context {fx : FPState}.

Theorem calloc_refines : calloc_stmt.
Proof. v9_ml_tail (@RRef_calloc.calloc_refines fx v9_reloc v9_code v9_sites). Qed.
End Calloc.
End V9Ref_calloc.

From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng Require RRef_free.
Module V9Ref_free.
Import Stdlib.ZArith.ZArith.
Import Stdlib.NArith.NArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Import LinuxProcessSemantics.LinuxProcessSem.Fs.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.LinuxProcessSem.Monad.
Import LinuxProcessSemantics.LinuxProcessSem.Specs.
Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng.MallocLayout.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng.RefStmts.
Import V9MallocLayout.
Import V9Reloc.
Import V9RelocCode.
Import V9RelocSites.
Import V9RelocML.
(* [comment removed for export] *)







Section Free.
Context {fx : FPState}.

Theorem free_refines : free_stmt.
Proof. v9_ml_tail (@RRef_free.free_refines fx v9_reloc v9_code v9_sites). Qed.
End Free.
End V9Ref_free.

From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng Require RRef_malloc.
Module V9Ref_malloc.
Import Stdlib.ZArith.ZArith.
Import Stdlib.NArith.NArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Import LinuxProcessSemantics.LinuxProcessSem.Fs.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.LinuxProcessSem.Monad.
Import LinuxProcessSemantics.LinuxProcessSem.Specs.
Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng.MallocLayout.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng.RefStmts.
Import V9MallocLayout.
Import V9Reloc.
Import V9RelocCode.
Import V9RelocSites.
Import V9RelocML.
(* [comment removed for export] *)







Section Malloc.
Context {fx : FPState}.

Theorem malloc_refines : malloc_stmt.
Proof. v9_ml_tail (@RRef_malloc.malloc_refines fx v9_reloc v9_code v9_sites). Qed.
End Malloc.
End V9Ref_malloc.

From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica Require PFLib.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Reloc Require RelocBlocks.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Musl Require RelocRW.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Musl Require RelocPF.
Module V9RelocMusl.
Import Stdlib.ZArith.ZArith.
Import Stdlib.Lists.List.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica.PFLib.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Reloc.Reloc.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Reloc.RelocBlocks.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Reloc.RelocImg.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Reloc.RelocSpan.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Reloc.CanonSpans.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Musl.RelocRW.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Musl.RelocPF.
Import V9Reloc.
Import V9RelocImg.
(* [comment removed for export] *)






Local Open Scope Z_scope.

Lemma v9_dwin_bounds : @dwin_bounds_chk v9_reloc v9_data = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition v9_rw : RelocRW v9_reloc v9_data := {| rl_dwin_bounds := v9_dwin_bounds; rl_rw_hull := v9_hull_ok; rl_rw_spans := v9_spans_ok; rl_rw_orders := v9_orders_ok |}.

Lemma v9_segs_lo : segs_lo (@rl_segs v9_reloc) = @rl_img_lo v9_reloc.
Proof. vm_cast_no_check (@eq_refl Z (@rl_img_lo v9_reloc)). Qed.
Lemma v9_segs_hi : segs_hi (@rl_segs v9_reloc) = @rl_img_hi v9_reloc.
Proof. vm_cast_no_check (@eq_refl Z (@rl_img_hi v9_reloc)). Qed.
Lemma v9_pf_bounds : @pf_bounds_chk v9_reloc = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma v9_pf_prefix : pf_prefix_ok (@rl_segs v9_reloc) (0x102e7 + @rl_delta v9_reloc B_S_102e7) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition v9_pf : RelocPF v9_reloc :=
  {| rl_segs_lo_val := v9_segs_lo; rl_segs_hi_val := v9_segs_hi; rl_pf_bounds := v9_pf_bounds; rl_pf_prefix := v9_pf_prefix |}.
End V9RelocMusl.

From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Musl Require RelocStart.
Module V9RelocStart.
Import Stdlib.ZArith.ZArith.
Import Stdlib.Lists.List.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Reloc.Reloc.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Reloc.RelocBlocks.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Reloc.RelocImg.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Musl.RelocStart.
Import V9Reloc.
Import V9RelocImg.
(* [comment removed for export] *)





Local Open Scope Z_scope.

Lemma v9_start_ok : start_ok (@rl_delta v9_reloc 8%positive) (@rl_data_lo v9_reloc v9_data) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition v9_start : RelocStart v9_reloc v9_data := {| rl_start_ok := v9_start_ok |}.
End V9RelocStart.

From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require VmLedger.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require AllocIface.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng Require MallocTree.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng Require MallocOps.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng Require MallocIface.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng Require MallocInv_defs.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng Require MallocIfaceX.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng Require MallocInv_aslot_iface.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng Require MallocInv_malloc_iface.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng Require MallocInv_aslot.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng Require MallocInv_mal6.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng Require MallocInv_calloc2.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng Require MallocInv_freetopX.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng Require AllocBase.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng Require AllocCalloc.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng Require MallocAllocLayout.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng Require MallocGlue.
Module V9Alloc.
Import Stdlib.ZArith.ZArith.
Import Stdlib.NArith.NArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Import LinuxProcessSemantics.LinuxProcessSem.Fs.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.LinuxProcessSem.Monad.
Import LinuxProcessSemantics.LinuxProcessSem.Specs.
Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.PureModel.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.VmLedger.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.AllocIface.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng.MallocLayout.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng.MallocTree.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng.MallocOps.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng.MallocIface.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng.MallocInv_defs.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng.MallocIfaceX.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng.MallocInv_aslot_iface.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng.MallocInv_malloc_iface.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng.MallocInv_aslot.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng.MallocInv_mal6.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng.MallocInv_calloc2.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng.MallocInv_freetopX.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng.AllocBase.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng.MallocAllocLayout.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng.MallocGlue.
Import V9MallocLayout.
Import V9Ref_malloc.
Import V9Ref_free.
Import V9Ref_calloc.
(* [comment removed for export] *)





Import ListNotations.
Local Open Scope Z_scope.

Definition u16_alloc_slot_okW (HT : HeapTop) : alloc_slot_specW (ML:=LU16) (HT:=HT) := alloc_slot_okW (HT:=HT).

Definition u16_free_okX (HT : HeapTop) := free_okX (ML:=LU16) (HT:=HT).

Definition u16_malloc_okX (HT : HeapTop) := malloc_okX (ML:=LU16) (HT:=HT) (u16_alloc_slot_okW HT).
Definition u16_calloc_okX (HT : HeapTop) := calloc_okX (ML:=LU16) (HT:=HT) (u16_malloc_okX HT).

Definition u16_base : AllocBase (AL:=mallocng_alloc_layout (ML:=LU16)) :=
  mallocng_base (ML:=LU16) u16_malloc_okX u16_free_okX (fun fx => malloc_refines (fx:=fx)) (fun fx => free_refines (fx:=fx)).
Definition u16_calloc : AllocCalloc (AL:=mallocng_alloc_layout (ML:=LU16)) (CL:=mallocng_calloc_layout (ML:=LU16)) :=
  mallocng_calloc (ML:=LU16) u16_malloc_okX u16_free_okX u16_calloc_okX
    (fun fx => malloc_refines (fx:=fx)) (fun fx => free_refines (fx:=fx)) (fun fx => calloc_refines (fx:=fx)).
End V9Alloc.

From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica Require SumSpecs.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica Require PFSpecLib.
Module V9PFSpec.
Import Stdlib.ZArith.ZArith.
Import Stdlib.Lists.List.
Import Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OSSVerify.leptonica.edge_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica.SumSpecs.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica.PFLib.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica.PFSpecLib.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Reloc.Reloc.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Reloc.RelocCode.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Reloc.RelocSites.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Reloc.RelocImg.
Import V9Reloc.
Import V9RelocCode.
Import V9RelocSites.
Import V9RelocImg.
Import V9RelocMusl.
Import V9PFBase.
(* [comment removed for export] *)








Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition ls_ok (nS : nat) (fmts : list Z) (L : SSP.ls_addrs) : bool := @PFSpec.ls_ok v9_reloc nS fmts L.
Definition ls_ok1 (L : SSP.ls_addrs) : bool := ls_ok 1 (SSP.ls_fmts1 L) L.
Definition ls_ok2 (L : SSP.ls_addrs) : bool := ls_ok 2 (SSP.ls_fmts2 L) L.

Section Contracts.
Context {fx : FPState}.
#[local] Existing Instance v9_reloc.
#[local] Existing Instance v9_code.
#[local] Existing Instance v9_sites.
#[local] Existing Instance v9_data.
#[local] Existing Instance v9_img.
#[local] Existing Instance v9_rw.
#[local] Existing Instance v9_pf.

(* [comment removed for export] *)
Theorem lept_stderr_s1_contract : forall L, ls_ok1 L = true -> SSP.sum_contract SEGS (SSP.spec_lept_stderr_s1 L).
Proof. exact PFSpec.lept_stderr_s1_contract. Qed.

(* [comment removed for export] *)
Theorem lept_stderr_s2_contract : forall L, ls_ok2 L = true -> SSP.sum_contract SEGS (SSP.spec_lept_stderr_s2 L).
Proof. exact PFSpec.lept_stderr_s2_contract. Qed.
End Contracts.
End V9PFSpec.

From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.CliDriver Require Amb.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require RefNodesMF.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Musl Require StartupBase.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Musl Require StartupDefs.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Musl Require Startup.
Module V9Startup.
Import Stdlib.ZArith.ZArith.
Import Stdlib.NArith.NArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Import LinuxProcessSemantics.LinuxProcessSem.Fs.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.LinuxProcessSem.Monad.
Import LinuxProcessSemantics.LinuxProcessSem.Specs.
Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.Riscv.Decode.
Import LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.leptonica.edge_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.CliDriver.Amb.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.PureModel.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.RefNodesMF.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.StartupTac.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.ArgvEnv.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.RefLayout.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Reloc.Reloc.
Import V9StartupDefs.
Import V9Reloc.
Import V9RelocCode.
Import V9RelocSites.
Import V9RelocImg.
Import V9RelocMusl.
Import V9RelocStart.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)











Import ListNotations.
Open Scope bv_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.
Abbreviation RPH := Ubsan.M.phdrs.
(* [comment removed for export] *)
Local Notation rsegs := Ubsan.M.loaded_segments (only parsing).
Local Notation rpc := Ubsan.M.init_pc (only parsing).
Local Notation rph := Ubsan.M.phdrs (only parsing).

(* [comment removed for export] *)

(* [comment removed for export] *)
Section VP1. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma bwd_rz : forall segs model K,
  m_halted model = None -> m_vm_lazy model = [] ->
  bwd segs (fun st => realizes segs (mkCfg st model) K).
Proof.
  intros segs model K Hh Hlazy st st' Hms Hst'. eapply rz_msteps; eassumption.
Qed.
End VP1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition J_main {AMB : Amb} (sp0 : word) (av ev : list (list byte)) (s1v : word) : word -> option byte :=
  let J6 := J_tls sp0 (J_aux sp0 av ev a_uid a_hwcap (J_lsm sp0 av (fun _ => Some (Z_to_bv 8 0))))
              (Z_to_bv 64 0xe1ab4) (pn_w sp0 av ev) s1v (Z_to_bv 64 0x12aae8)
              (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) in
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes J6
    (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 0xe1abc)))   (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))           (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))          (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)))          (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0)))          (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0)))          (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 0xe1cb0)))    (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (argv_w sp0)))             (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av)))              (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 0xe1c00)))    (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 96)) (word_to_le_bytes 8 (Z_to_bv 64 0xf5d48)).    (* [comment removed for export] *)

(* [comment removed for export] *)
Record main_entry {AMB : Amb} (sp0 : word) (av ev : list (list byte)) (tid : word)
       (regs : bvmap 5 word) (mem : word -> option byte) : Prop := {
  me_ra  : getr regs 1 = Z_to_bv 64 0xe1cc0;
  me_sp  : getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 48);
  me_gp  : getr regs 3 = Z_to_bv 64 0x10800;
  me_tp  : getr regs 4 = Z_to_bv 64 0x10a858;
  me_s0  : getr regs 8 = Z_to_bv 64 (bv_unsigned sp0 + 8);
  me_s1  : getr regs 9 = argcN av;
  me_a0  : getr regs 10 = argcN av;
  me_a1  : getr regs 11 = Z_to_bv 64 (bv_unsigned sp0 + 8);
  me_a2  : getr regs 12 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av));
  me_s2  : getr regs 18 = Z_to_bv 64 0x5cca0;
  me_s3  : getr regs 19 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av));
  me_szero : forall r : reg, In r [20; 21; 22; 23; 24; 25; 26; 27]%list -> getr regs r = Z_to_bv 64 0;
  me_mem : exists (J : word -> option byte) (s1v : word),
             wfJ sp0 J /\ J = J_main sp0 av ev s1v
             /\ mem = cmem sp0 (wrap_mem RPH sp0 av ev a_uid a_hwcap a_draw) J (D_main sp0 av ev a_hwcap a_draw tid)
}.

(* [comment removed for export] *)
Lemma main_entry_L : forall {AMB : Amb} sp0 av ev tid regs mem,
  @Startup.main_entry v9_reloc AMB sp0 av ev tid regs mem -> main_entry sp0 av ev tid regs mem.
Proof.
  intros AMB sp0 av ev tid regs mem [f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13].
  split; [exact f1|exact f2|exact f3|exact f4|exact f5|exact f6|exact f7|exact f8|exact f9|exact f10|exact f11|exact f12|exact f13].
Qed.

Section Assembly.
  Context {AMB : Amb}.
  #[local] Existing Instance fx0.   (* [comment removed for export] *)
  Variable sp : word.
  Variables argv envp : list (list byte).
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hvsp : valid_sp sp.

  Lemma Hlo : (0x7fff80000000 <= bv_unsigned sp)%Z.
  Proof. destruct Hvsp as [H _]. exact H. Qed.
  Lemma Hhi : (bv_unsigned sp <= 0x800000000000)%Z.
  Proof. destruct Hvsp as [_ [H _]]. exact H. Qed.
  Lemma Hal : (bv_unsigned sp mod 16 = 0)%Z.
  Proof. destruct Hvsp as [_ [_ H]]. exact H. Qed.

  Let J0 : word -> option byte := fun _ => Some (Z_to_bv 8 0).

  (* [comment removed for export] *)
  Ltac side Hva Hve HG :=
    first [ exact Hva | exact Hve | exact Hlo | exact Hhi | exact Hal | exact HG
          | apply wfJ_const
          | lazymatch goal with |- getr _ _ = _ =>
              gres; first [ assumption | reflexivity | bveq
                          | match goal with H : getr ?rs ?n = _ |- getr ?rs ?n = _ =>
                              rewrite H; unfold envp_w, envp_ptr, argv_w, pn_w, argc_w;
                              first [reflexivity | f_equal; lia | bveq] end ] end
          | idtac ].

  Theorem ref_startup_sec : forall brk mbase lim fs0 stdin0 K,
    (forall tid regs mem,
       (0 < bv_unsigned tid < 2^22)%Z ->
       main_entry sp argv envp tid regs mem ->
       realizes rsegs (mkCfg (mkst (fx:=fx0) regs (0x5cca0 : word) mem (seg_rom rsegs))
                             (with_tid tid (init_model (segments_reserved rsegs) brk mbase sp lim
                                                      (mkProcInputC argv envp fs0 stdin0)))) K) ->
    realizes rsegs (init_config rsegs rpc rph sp brk mbase a_draw lim (mkProcInputC argv envp fs0 stdin0)) K.
  Proof.
    intros brk mbase lim fs0 stdin0 K HK.
    refine (@Startup.ref_startup_sec v9_reloc v9_code v9_sites v9_img v9_data v9_rw v9_start AMB sp argv envp Hva Hve Hvsp
              rpc _ brk mbase lim fs0 stdin0 K _).
    - apply bv_eq; reflexivity.
    - intros tid regs mem Htid ME.
      pose proof (HK tid regs mem Htid (main_entry_L _ _ _ _ _ _ ME)) as R.
      bvlit64_to_Z_in R. exact R.
  Qed.

End Assembly.

(* [comment removed for export] *)
Theorem ref_startup : forall sp brk mbase draw lim inp K,
  valid_sp sp -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
  (forall tid regs mem,
     (0 < bv_unsigned tid < 2^22)%Z ->
     @main_entry (amb_of inp draw) sp (in_argv inp) (in_envp inp) tid regs mem ->
     realizes rsegs (mkCfg (mkst (fx:=fx0) regs (0x5cca0 : word) mem (seg_rom rsegs))
                           (with_tid tid (init_model (segments_reserved rsegs) brk mbase sp lim inp))) K) ->
  realizes rsegs (init_config rsegs rpc rph sp brk mbase draw lim inp) K.
Proof.
  intros sp brk mbase draw lim inp K Hsp Hva Hve HK.
  (* [comment removed for export] *)
  rewrite <- (init_config_C_of rsegs rpc rph sp brk mbase draw lim inp).
  apply (@ref_startup_sec (amb_of inp draw) sp (in_argv inp) (in_envp inp) Hva Hve Hsp brk mbase lim (in_fs inp) (in_stdin inp) K).
  intros tid regs mem Htid ME. rewrite init_model_C_of. exact (HK tid regs mem Htid ME).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Consumers.
  Context {AMB : Amb}.
  Variable sp0 : word.
  Variables av ev : list (list byte).
  Variable tid : word.
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Hypothesis ME : main_entry sp0 av ev tid regs mem.

  (* [comment removed for export] *)
  Lemma main_entry_rdn_above : forall segs (a : word) n,
    (bv_unsigned sp0 <= bv_unsigned a)%Z ->
    (bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
    rdn segs mem a n = rdn segs (wrap_mem RPH sp0 av ev a_uid a_hwcap a_draw) a n.
  Proof.
    intros segs a n Ha Hn. destruct (me_mem _ _ _ _ _ _ ME) as (J & s1v & HJ & _ & ->).
    apply rdn_cmem_above; assumption.
  Qed.

  Lemma main_entry_mem_above : forall (a : word),
    (bv_unsigned sp0 <= bv_unsigned a)%Z -> mem a = wrap_mem RPH sp0 av ev a_uid a_hwcap a_draw a.
  Proof.
    intros a Ha. destruct (me_mem _ _ _ _ _ _ ME) as (J & s1v & HJ & _ & ->).
    apply cmem_at_above. exact Ha.
  Qed.

  (* [comment removed for export] *)
  Lemma main_entry_win_mapped : forall (a : word),
    (bv_unsigned sp0 - stack_max_size <= bv_unsigned a < bv_unsigned sp0)%Z -> mem a <> None.
  Proof.
    intros a Ha. destruct (me_mem _ _ _ _ _ _ ME) as (J & s1v & HJ & _ & ->).
    rewrite cmem_at_win by (unfold in_win, win_lo; lia). apply HJ. unfold in_win, win_lo. lia.
  Qed.

  Lemma main_entry_store_ok_win : forall segs (a : word) n,
    (bv_unsigned sp0 - stack_max_size <= bv_unsigned a)%Z ->
    (bv_unsigned a + Z.of_nat n <= bv_unsigned sp0)%Z ->
    store_ok segs mem a n = true.
  Proof.
    intros segs a n Hlo Hhi. destruct (me_mem _ _ _ _ _ _ ME) as (J & s1v & HJ & _ & ->).
    apply store_ok_cmem_win; [exact HJ | unfold win_lo; lia | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma main_entry_mem_data : forall (a : word),
    (bv_unsigned a < bv_unsigned sp0 - stack_max_size)%Z ->
    mem a = D_main sp0 av ev a_hwcap a_draw tid a.
  Proof.
    intros a Ha. destruct (me_mem _ _ _ _ _ _ ME) as (J & s1v & HJ & _ & ->).
    apply cmem_at_data. unfold win_lo. exact Ha.
  Qed.

  Lemma main_entry_rdn_data : forall segs (a : word) n,
    (bv_unsigned a + Z.of_nat n <= bv_unsigned sp0 - stack_max_size)%Z ->
    rdn segs mem a n = rdn segs (D_main sp0 av ev a_hwcap a_draw tid) a n.
  Proof.
    intros segs a n Ha. destruct (me_mem _ _ _ _ _ _ ME) as (J & s1v & HJ & _ & ->).
    apply rdn_cmem_data. unfold win_lo. exact Ha.
  Qed.
End Consumers.
End V9Startup.

Module V9StdioDefs.
Import Stdlib.ZArith.ZArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Import LinuxProcessSemantics.LinuxProcessSem.Fs.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.LinuxProcessSem.Monad.
Import LinuxProcessSemantics.LinuxProcessSem.Specs.
Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.Riscv.Decode.
Import LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.leptonica.edge_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.SeqExec.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.StepTac.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.WalkTac.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.StoreOk.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.StreamSim.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.MmapSim.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.ExitSim.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Nodes.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica.SumWalkTac.
Export V9ExitBase.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)








Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record sw_file (mem : word -> option byte) (f : Z) (wb wp : Z) (fd : Z) (bufp bufsz : word) : Prop := {
  swf_wpos  : rdn RSEGS mem (Z_to_bv 64 (f + 40)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wp));
  swf_wbase : rdn RSEGS mem (Z_to_bv 64 (f + 56)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wb));
  swf_fd    : rdn RSEGS mem (Z_to_bv 64 (f + 120)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 fd));
  swf_buf   : rdn RSEGS mem (Z_to_bv 64 (f + 88)) 8%nat = Some (word_to_le_bytes 8 bufp);
  swf_bsz   : rdn RSEGS mem (Z_to_bv 64 (f + 96)) 8%nat = Some (word_to_le_bytes 8 bufsz)
}.

(* [comment removed for export] *)
Definition ssp_cells (mem : word -> option byte) (can : word) : Prop :=
  rdn RSEGS mem (Z_to_bv 64 0xf92a8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x12aac8))
  /\ rdn RSEGS mem (Z_to_bv 64 0x12aac8) 8%nat = Some (word_to_le_bytes 8 can).

(* [comment removed for export] *)
Record sw_post (mem : word -> option byte) (su f : Z) (bufp bufsz : word)
       (mem' : word -> option byte) : Prop := {
  swp_agree : forall x : word,
      ~ (su - 112 <= bv_unsigned x < su)%Z ->
      ~ (f + 32 <= bv_unsigned x < f + 48)%Z ->
      ~ (f + 56 <= bv_unsigned x < f + 64)%Z ->
      mem' x = mem x;
  swp_grows : mem_grows mem mem';
  swp_wend  : rdn RSEGS mem' (Z_to_bv 64 (f + 32)) 8%nat = Some (word_to_le_bytes 8 (v_add bufp bufsz));
  swp_wpos  : rdn RSEGS mem' (Z_to_bv 64 (f + 40)) 8%nat = Some (word_to_le_bytes 8 bufp);
  swp_wbase : rdn RSEGS mem' (Z_to_bv 64 (f + 56)) 8%nat = Some (word_to_le_bytes 8 bufp)
}.

(* [comment removed for export] *)
Section VP1.
  Context {fx : FPState}.   (* [comment removed for export] *)
Lemma sw_post_rdn : forall mem su f bufp bufsz mem' (a : word) n bs,
  sw_post mem su f bufp bufsz mem' ->
  rdn RSEGS mem a n = Some bs ->
  (bv_unsigned a + Z.of_nat n <= 2 ^ 64)%Z ->
  (bv_unsigned a + Z.of_nat n <= su - 112 \/ su <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat n <= f + 32 \/ f + 48 <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat n <= f + 56 \/ f + 64 <= bv_unsigned a)%Z ->
  rdn RSEGS mem' a n = Some bs.
Proof.
  intros mem su f bufp bufsz mem' a n bs P H Hnw D1 D2 D3.
  rewrite (rdn_ext RSEGS n mem' mem a Hnw); [exact H|].
  intros x Hx. apply (swp_agree _ _ _ _ _ _ P); lia.
Qed.
End VP1.

Section VP2.
  Context {fx : FPState}.   (* [comment removed for export] *)
Lemma sw_post_store_ok : forall mem su f bufp bufsz mem' (a : word) n,
  sw_post mem su f bufp bufsz mem' ->
  store_ok RSEGS mem a n = true -> store_ok RSEGS mem' a n = true.
Proof. intros mem su f bufp bufsz mem' a n P H. eapply store_ok_mono; [apply (swp_grows _ _ _ _ _ _ P) | exact H]. Qed.
End VP2.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition atexit_none (mem : word -> option byte) : Prop :=
  rdn RSEGS mem (Z_to_bv 64 0x12a8b0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).

Definition atexit_one (mem : word -> option byte) : Prop :=
  rdn RSEGS mem (Z_to_bv 64 0x12a8b0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x12a8b8))
  /\ rdn RSEGS mem (Z_to_bv 64 0x12a8a8) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1))
  /\ rdn RSEGS mem (Z_to_bv 64 0x12a8b8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
  /\ rdn RSEGS mem (Z_to_bv 64 0x12a8c0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xe222c))
  /\ rdn RSEGS mem (Z_to_bv 64 0x12a9c0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x5d0c8))
  /\ rdn RSEGS mem (Z_to_bv 64 0x10a5a4) 1%nat = Some [Z_to_bv 8 0].

Definition atexit_state (mem : word -> option byte) : Prop := atexit_none mem \/ atexit_one mem.

(* [comment removed for export] *)
Record exit_common (regs : bvmap 5 word) (mem : word -> option byte)
       (sp tp code : word) (tid : Z) (wp2 rp2 : word) : Prop := {
  ec_sp   : getr regs 2 = sp;
  ec_tp   : getr regs 4 = tp;
  ec_a0   : getr regs 10 = code;
  ec_splo : (4294967296 <= bv_unsigned sp - 144)%Z;
  ec_sphi : (bv_unsigned sp <= 0x800000000000)%Z;
  ec_sok  : store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true;
  ec_tplo : (168 <= bv_unsigned tp)%Z;
  ec_tphi : (bv_unsigned tp <= 4294967296)%Z;
  ec_tid  : (0 < tid < 2147483648)%Z;
  (* [comment removed for export] *)
  ec_mtid : rdn RSEGS mem (Z_to_bv 64 (bv_unsigned tp - 168)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 tid));
  (* [comment removed for export] *)
  ec_lock : rdn RSEGS mem (Z_to_bv 64 0x12aac0) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0));
  (* [comment removed for export] *)
  ec_fe   : rdn RSEGS mem (Z_to_bv 64 0xf92b0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xf5d50));
  ec_fs   : rdn RSEGS mem (Z_to_bv 64 0xf92b8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xf5d48));
  ec_fa   : rdn RSEGS mem (Z_to_bv 64 0xf5d48) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x5cc10));
  (* [comment removed for export] *)
  ec_comp : rdn RSEGS mem (Z_to_bv 64 0xfa598) 1%nat = Some [Z_to_bv 8 0];
  ec_g1   : rdn RSEGS mem (Z_to_bv 64 0xf90f0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xe2164));   (* [comment removed for export] *)
  ec_g2   : rdn RSEGS mem (Z_to_bv 64 0xf90f8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
  (* [comment removed for export] *)
  ec_glob : stdio_globals mem;
  (* [comment removed for export] *)
  ec_err  : file_clean mem 0xfa348 wp2 rp2;
  (* [comment removed for export] *)
  ec_dso  : rdn RSEGS mem (Z_to_bv 64 0xfa2d8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xfa2d8));
  ec_alock : rdn RSEGS mem (Z_to_bv 64 0x12a8a4) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0));
  ec_atexit : atexit_state mem
}.

(* [comment removed for export] *)
Record stdout_pending (mem : word -> option byte) (wb wp : Z) (bufp bufsz rp1 can : word)
       (pending : list byte) : Prop := {
  sp_lock  : rdn RSEGS mem (Z_to_bv 64 (0xfa438 + 140)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295));
  sp_wpos  : rdn RSEGS mem (Z_to_bv 64 (0xfa438 + 40)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wp));
  sp_wbase : rdn RSEGS mem (Z_to_bv 64 (0xfa438 + 56)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wb));
  sp_write : rdn RSEGS mem (Z_to_bv 64 (0xfa438 + 72)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xe65e4));
  sp_buf   : rdn RSEGS mem (Z_to_bv 64 (0xfa438 + 88)) 8%nat = Some (word_to_le_bytes 8 bufp);
  sp_bsz   : rdn RSEGS mem (Z_to_bv 64 (0xfa438 + 96)) 8%nat = Some (word_to_le_bytes 8 bufsz);
  sp_fd    : rdn RSEGS mem (Z_to_bv 64 (0xfa438 + 120)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1));
  sp_rpos  : rdn RSEGS mem (Z_to_bv 64 (0xfa438 + 8)) 8%nat = Some (word_to_le_bytes 8 rp1);
  sp_rend  : rdn RSEGS mem (Z_to_bv 64 (0xfa438 + 16)) 8%nat = Some (word_to_le_bytes 8 rp1);
  sp_range : (0x12aad0 <= wb < wp /\ wp <= 0x12c000)%Z;
  sp_len   : (wp - wb = Z.of_nat (length pending))%Z;
  sp_max   : (Z.of_nat (length pending) <= 2 ^ 30)%Z;
  sp_bytes : rdn RSEGS mem (Z_to_bv 64 wb) (length pending) = Some pending;
  sp_ssp   : ssp_cells mem can
}.

(* [comment removed for export] *)
Definition exit_pre (regs : bvmap 5 word) (mem : word -> option byte) (model : Model)
           (code : word) (pending : list byte) : Prop :=
  exists (sp tp : word) (tid : Z) (wp2 rp2 : word),
    exit_common regs mem sp tp code tid wp2 rp2
    /\ m_halted model = None /\ m_vm_lazy model = []
    /\ ( (pending = [] /\ exists wp1 rp1, file_clean mem 0xfa438 wp1 rp1)
       \/ (exists (wb wp : Z) (bufp bufsz rp1 can : word),
              stdout_pending mem wb wp bufp bufsz rp1 can pending
              /\ fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1))) ).

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End V9StdioDefs.

From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica Require Frame.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Musl Require Strnlen.
Module V9Strnlen.
Import Stdlib.ZArith.ZArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude.
Import LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.Riscv.Decode.
Import LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.leptonica.edge_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.SeqExec.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.StepTac.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.StoreOk.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.WalkTac.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.MmapSim.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.RefMemcpyLib.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica.PortLib.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica.Frame.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Reloc.Reloc.
Import V9Reloc.
Import V9RelocCode.
Import V9RelocSites.
Import V9RelocImg.
Import V9MemcpyBase.
Import V9Memchr.
(* [comment removed for export] *)










Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section VP1. Context {fx : FPState}.
Theorem ref_strnlen : forall mem (s sp : word) buf K n rom regs (ret : word),
  mchrH mem s buf K n ->
  (0 < bv_unsigned s + K)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 32)) 32 = true ->
  (0x1c450 <= bv_unsigned sp - 32)%Z ->
  (bv_unsigned s + Z.of_nat (length buf) <= bv_unsigned sp - 32 \/ bv_unsigned sp <= bv_unsigned s)%Z ->
  ret_ok ret -> getr regs 1 = ret -> getr regs 2 = sp ->
  getr regs 10 = s -> getr regs 11 = Z_to_bv 64 n ->
  exists regs' mem',
    msteps RSEGS (mkst regs (0xf155c : word) mem rom) (mkst regs' ret mem' rom)
    /\ keeps_cs regs regs'
    /\ getr regs' 10 = Z_to_bv 64 K
    /\ frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - 32), 32%Z)].
Proof.
  rl_tail (fun mem s sp buf K n rom regs ret (HOK : mchrH mem s buf K n) =>
             @Strnlen.ref_strnlen fx v9_reloc v9_code v9_sites v9_img mem s sp buf K n rom regs ret
               (mchrH_generic mem s buf K n HOK)).
Qed.
End VP1.
End V9Strnlen.

From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.CliDriver Require LibWritevG.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.CliDriver Require Spec.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Musl Require StdioDefs.
(* [comment removed for export] *)

From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require SpecConsts.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require SymExec.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.CliDriver Require SymExec2.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.CliDriver Require SymExec2Sound.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.CliDriver Require SymRun.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.CliDriver Require SymDrive.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.CliDriver Require SymDriveX.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.CliDriver Require LibKnowFrame.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Musl Require LibStdioCall.
Module V9LibStdioCall.
Import Stdlib.ZArith.ZArith.
Import Stdlib.NArith.NArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Import LinuxProcessSemantics.LinuxProcessSem.Fs.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.LinuxProcessSem.Monad.
Import LinuxProcessSemantics.LinuxProcessSem.Specs.
Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.Riscv.Decode.
Import LinuxProcessSemantics.Riscv.DecodeC.
Import LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.leptonica.edge_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.SeqExec.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.StoreOk.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Nodes.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.AgentLib.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.SpecConsts.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.SymExec.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.CliDriver.SymExec2.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.CliDriver.SymExec2Sound.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.CliDriver.SymRun.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.CliDriver.SymDrive.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.CliDriver.SymDriveX.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.CliDriver.LibKnowFrame.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Reloc.Reloc.
Import V9ExitBase.
Import V9StdioDefs.
Import V9Reloc.
Import V9RelocCode.
Import V9RelocSites.
Import V9RelocImg.
Import V9RelocMusl.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)










Import ListNotations.
Import SX2. Import SX2S.
Open Scope Z_scope.

#[local] Abbreviation RSEGS := Ubsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Notation SC_KEPT := LibStdioCall.SC_KEPT.
Notation stdio_res := LibStdioCall.stdio_res.
Notation SCR_ := LibStdioCall.SCR_.
Notation sc_f := LibStdioCall.sc_f.
Notation sc_fd := LibStdioCall.sc_fd.
Notation sc_ret := LibStdioCall.sc_ret.
Notation sc_wb := LibStdioCall.sc_wb.
Notation sc_wp := LibStdioCall.sc_wp.
Notation sc_bufp := LibStdioCall.sc_bufp.
Notation sc_bufsz := LibStdioCall.sc_bufsz.
Notation sc_s := LibStdioCall.sc_s.
Notation sc_l := LibStdioCall.sc_l.
Notation sc_sp := LibStdioCall.sc_sp.
Notation sc_sr := LibStdioCall.sc_sr.
Notation sc_kn := LibStdioCall.sc_kn.
Notation lit_even_ret := LibStdioCall.lit_even_ret.
Notation kimg_cut1 := LibStdioCall.kimg_cut1.
Notation kimg_cut := LibStdioCall.kimg_cut.
Notation stdio_call := (@LibStdioCall.stdio_call v9_reloc v9_data).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Notation inr := LibStdioCall.inr.
Notation inr_spec := LibStdioCall.inr_spec.
Notation inr_false := LibStdioCall.inr_false.
Notation Forall_one' := LibStdioCall.Forall_one'.
Notation u_lit0 := LibStdioCall.u_lit0.
Notation flat_abs0 := LibStdioCall.flat_abs0.
Notation split_lit_denot := LibStdioCall.split_lit_denot.
Notation split_lit_vars := LibStdioCall.split_lit_vars.
Notation kindex_some := LibStdioCall.kindex_some.
Notation ridx_lit := LibStdioCall.ridx_lit.
Notation sr_get_nat := LibStdioCall.sr_get_nat.
Notation length_sr_upd := LibStdioCall.length_sr_upd.
Notation nth_sr_upd_same := LibStdioCall.nth_sr_upd_same.
Notation nth_sr_upd_other := LibStdioCall.nth_sr_upd_other.
Notation length_sr_after_call_j := LibStdioCall.length_sr_after_call_j.

Lemma know_ok_frame3 : forall E M M' kn b1 o1 n1 b2 o2 n2 b3 o3 n3,
  know_ok RSEGS E M kn ->
  flat E (SA b1 o1) n1 -> flat E (SA b2 o2) n2 -> flat E (SA b3 o3) n3 ->
  (forall x : word,
     ~ (estart E (SA b1 o1) <= bv_unsigned x < estart E (SA b1 o1) + n1)%Z ->
     ~ (estart E (SA b2 o2) <= bv_unsigned x < estart E (SA b2 o2) + n2)%Z ->
     ~ (estart E (SA b3 o3) <= bv_unsigned x < estart E (SA b3 o3) + n3)%Z ->
     M' x = M x) ->
  mem_grows M M' ->
  know_ok RSEGS E M' (kn_frame (kn_frame (kn_frame kn b1 o1 n1) b2 o2 n2) b3 o3 n3).
Proof. exact (@LibStdioCall.know_ok_frame3 v9_reloc). Qed.

Lemma kimg_cut_sound : forall E M k a n, know_ok RSEGS E M k -> know_ok RSEGS E M (kimg_cut k a n).
Proof. exact (@LibStdioCall.kimg_cut_sound v9_reloc). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma sw_post_L : forall mem su f bufp bufsz mem',
  @StdioDefs.sw_post v9_reloc mem su f bufp bufsz mem' -> sw_post mem su f bufp bufsz mem'.
Proof.
  intros mem su f bufp bufsz mem' [f1 f2 f3 f4 f5].
  exact (Build_sw_post mem su f bufp bufsz mem' f1 f2 f3 f4 f5).
Qed.

Section VP17.
  Context {fx : FPState}.   (* [comment removed for export] *)
Theorem stdio_call_sound_fr :
  forall (vals : list word) (ebs : nat -> list byte) (sr : list expr) (kn : list kentry)
         (R : bvmap 5 word) (M : word -> option byte) (model : Model) (res : stdio_res)
         (pending extra : list byte) (K : TSet),
  let E := Env (vals_ev vals) ebs in
  regs_ok E sr R -> know_ok RSEGS E M kn ->
  stdio_call (length vals) sr kn = Some res ->
  let wb := bv_unsigned (edenot E (sc_wb res)) in
  let wp := bv_unsigned (edenot E (sc_wp res)) in
  let s := edenot E (sc_s res) in
  let l := edenot E (sc_l res) in
  let su := bv_unsigned (edenot E (sc_sp res)) in
  (wb <= wp)%Z -> (wp <= 0x800000000000)%Z ->   (* [comment removed for export] *)
  (wp - wb = Z.of_nat (length pending))%Z ->
  (bv_unsigned l = Z.of_nat (length extra))%Z ->
  (Z.of_nat (length pending) + Z.of_nat (length extra) <= 2 ^ 30)%Z ->
  (Z.of_nat (length pending) + Z.of_nat (length extra) <= 2 ^ 30)%Z ->
  (wp <= su - 112 \/ su <= wb)%Z ->
  (bv_unsigned s + bv_unsigned l <= su - 112 \/ su <= bv_unsigned s)%Z ->
  (bv_unsigned s + bv_unsigned l <= 0x800000000000)%Z ->
  rdn RSEGS M (Z_to_bv 64 wb) (length pending) = Some pending ->
  rdn RSEGS M s (length extra) = Some extra ->
  fd_lookup (m_fds model) (Z_to_bv 64 (sc_fd res)) = Some (FdChannel (Z_to_bv 64 (sc_fd res))) ->
  m_halted model = None -> m_vm_lazy model = [] ->
  K [] ->
  (forall R' M',
     regs_ok (Env (vals_ev (vals ++ junk_vals R')) ebs) (sc_sr res) R' ->
     know_ok RSEGS (Env (vals_ev (vals ++ junk_vals R')) ebs) M' (sc_kn res) ->
     sw_post M (bv_unsigned (edenot E (sc_sp res))) (sc_f res) (edenot E (sc_bufp res)) (edenot E (sc_bufsz res)) M' ->
     realizes RSEGS (mkCfg (mkst R' (Z_to_bv 64 (sc_ret res)) M' (seg_rom RSEGS)) model) K) ->
  realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0xe65e4) M (seg_rom RSEGS)) model)
           (t_emit (map (WriteEv (Z_to_bv 64 (sc_fd res))) (pending ++ extra)) K).
Proof.
  intros vals ebs sr kn R M model res pending extra K E HR HK Hc wb wp s l su
         H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 HCONT.
  rl_tail (@LibStdioCall.stdio_call_sound_fr _ v9_reloc v9_code v9_sites v9_data v9_rw
             vals ebs sr kn R M model res pending extra K HR HK Hc
             H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15
             (fun R' M' A B P => HCONT R' M' A B (sw_post_L _ _ _ _ _ _ P))).
Qed.

(* [comment removed for export] *)
Theorem stdio_call_sound :
  forall (vals : list word) (ebs : nat -> list byte) (sr : list expr) (kn : list kentry)
         (R : bvmap 5 word) (M : word -> option byte) (model : Model) (res : stdio_res)
         (pending extra : list byte) (K : TSet),
  let E := Env (vals_ev vals) ebs in
  regs_ok E sr R -> know_ok RSEGS E M kn ->
  stdio_call (length vals) sr kn = Some res ->
  let wb := bv_unsigned (edenot E (sc_wb res)) in
  let wp := bv_unsigned (edenot E (sc_wp res)) in
  let s := edenot E (sc_s res) in
  let l := edenot E (sc_l res) in
  let su := bv_unsigned (edenot E (sc_sp res)) in
  (wb <= wp)%Z -> (wp <= 0x800000000000)%Z ->
  (wp - wb = Z.of_nat (length pending))%Z ->
  (bv_unsigned l = Z.of_nat (length extra))%Z ->
  (Z.of_nat (length pending) + Z.of_nat (length extra) <= 2 ^ 30)%Z ->
  (Z.of_nat (length pending) + Z.of_nat (length extra) <= 2 ^ 30)%Z ->
  (wp <= su - 112 \/ su <= wb)%Z ->
  (bv_unsigned s + bv_unsigned l <= su - 112 \/ su <= bv_unsigned s)%Z ->
  (bv_unsigned s + bv_unsigned l <= 0x800000000000)%Z ->
  rdn RSEGS M (Z_to_bv 64 wb) (length pending) = Some pending ->
  rdn RSEGS M s (length extra) = Some extra ->
  fd_lookup (m_fds model) (Z_to_bv 64 (sc_fd res)) = Some (FdChannel (Z_to_bv 64 (sc_fd res))) ->
  m_halted model = None -> m_vm_lazy model = [] ->
  K [] ->
  (forall R' M',
     regs_ok (Env (vals_ev (vals ++ junk_vals R')) ebs) (sc_sr res) R' ->
     know_ok RSEGS (Env (vals_ev (vals ++ junk_vals R')) ebs) M' (sc_kn res) ->
     realizes RSEGS (mkCfg (mkst R' (Z_to_bv 64 (sc_ret res)) M' (seg_rom RSEGS)) model) K) ->
  realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0xe65e4) M (seg_rom RSEGS)) model)
           (t_emit (map (WriteEv (Z_to_bv 64 (sc_fd res))) (pending ++ extra)) K).
Proof.
  intros vals ebs sr kn R M model res pending extra K E HR HK Hc wb wp s l su; intros.
  eapply stdio_call_sound_fr; try eassumption. intros R' M' HR' HK' _. auto.
Qed.
End VP17.
End V9LibStdioCall.

From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require MemSplit.
Module V9StartupFacts.
Import Stdlib.ZArith.ZArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.leptonica.edge_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.CliDriver.Amb.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.StartupTac.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.ArgvEnv.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.RefLayout.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.RefMemcpyLib.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.MemSplit.
Import V9StartupDefs.
Import V9Startup.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)







Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation RPH := Ubsan.M.phdrs.

(* [comment removed for export] *)
Definition D_main_cells : list (Z * nat) :=
  [(0x10a788%Z, 8%nat); (0x12aaf0%Z, 8%nat); (0x12ab50%Z, 8%nat); (0x12ab18%Z, 8%nat); (0x12aae0%Z, 8%nat); (0x12aad8%Z, 8%nat); (0x12a880%Z, 8%nat); (0x12a890%Z, 8%nat); (0x12a888%Z, 8%nat); (0x12ab00%Z, 8%nat); (0x12ab08%Z, 8%nat); (0x10a868%Z, 8%nat); (0x10a850%Z, 8%nat); (0x10a790%Z, 8%nat); (0x12aae8%Z, 1%nat); (0x10a7b8%Z, 4%nat); (0x10a7b0%Z, 4%nat); (0x10a828%Z, 8%nat); (0x10a808%Z, 8%nat); (0x10a798%Z, 8%nat); (0x10a7a0%Z, 8%nat); (0x10a7a8%Z, 8%nat); (0x12aac8%Z, 4%nat); (0x12aacc%Z, 4%nat); (0x12aac9%Z, 1%nat); (0x10a848%Z, 8%nat); (0xfa550%Z, 1%nat)].

Definition range_disjoint_b (a : Z) (n : nat) (c : Z * nat) : bool :=
  ((a + Z.of_nat n <=? fst c) || (fst c + Z.of_nat (snd c) <=? a))%Z.

Definition D_main_missb (a : Z) (n : nat) : bool :=
  forallb (range_disjoint_b a n) D_main_cells && (0 <=? a)%Z && (a + Z.of_nat n <=? 0x12c000)%Z.

(* [comment removed for export] *)
Definition djw (P : Prop) : Prop := P.

Section VP1. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma range_disjoint_djw : forall a n c,
  range_disjoint_b a n c = true ->
  djw (a + Z.of_nat n <= fst c \/ fst c + Z.of_nat (snd c) <= a)%Z.
Proof.
  intros a n [c l] H. unfold range_disjoint_b in H. cbn [fst snd] in *.
  apply orb_true_iff in H. unfold djw. destruct H as [H|H]; apply Z.leb_le in H; lia.
Qed.
End VP1.

Section Facts.
Context {fx : FPState}.   (* [comment removed for export] *)
  Context {AMB : Amb}.
  Variable sp0 : word.
  Variables av ev : list (list byte).
  Variable tid : word.
  Hypothesis Hva : valid_argv av.
  Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
  Hypothesis Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z.

  Let D := D_main sp0 av ev a_hwcap a_draw tid.

  Lemma len_av : (1 <= Z.of_nat (length av) <= 1024)%Z.
  Proof. destruct Hva as [[H1 H2] _]. lia. Qed.

  (* [comment removed for export] *)
  Lemma D_main_miss : forall segs (a : Z) (n : nat),
    D_main_missb a n = true ->
    rdn segs (D_main sp0 av ev a_hwcap a_draw tid) (Z_to_bv 64 a) n = rdn segs (fun _ => None) (Z_to_bv 64 a) n.
  Proof.
    intros segs a n Hb. pose proof (u64_range tid).
    unfold D_main_missb, D_main_cells in Hb. cbn [forallb] in Hb.
    repeat match goal with
           | H : (_ && _)%bool = true |- _ => apply andb_true_iff in H; destruct H as [? ?]
           end.
    repeat match goal with
           | H : range_disjoint_b _ _ _ = true |- _ =>
               apply range_disjoint_djw in H; cbn [fst snd Z.of_nat Pos.of_succ_nat Pos.succ] in H
           | H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H
           | H : true = true |- _ => clear H
           end.
    cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in *.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc.
    repeat (rewrite rdn_wbytes_out by
      (rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; imm_norm; unorm;
       lazymatch goal with
       | |- (?A \/ ?B) => match goal with H : djw _ |- _ => exact H end
       | |- _ => lia
       end)).
    reflexivity.
  Qed.

  Ltac hitD :=
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc;
    pose proof len_av;
    peel; first [ apply rdn_wbytes_hit8; unorm; lia
                | match goal with |- rdn _ (wbytes _ ?a ?bs) ?a _ = _ =>
                    rewrite <- (length_N_to_le_bytes 4) at 1; apply rdn_wbytes_hit; rewrite length_N_to_le_bytes; unorm; lia end ].

  (* [comment removed for export] *)
  Lemma D_main_tid : forall segs,
    rdn segs D (Z_to_bv 64 0x10a7b0) 4 = Some (word_to_le_bytes 4 tid).
  Proof.
    intros segs. pose proof (u64_range tid). subst D.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    pose proof (rdn_wbytes_hit segs (word_to_le_bytes 4 tid)) as Hh.
    rewrite length_N_to_le_bytes in Hh. apply Hh. unorm; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma D_main_guard : forall segs,
    rdn segs D (Z_to_bv 64 0x12aac8) 8 = Some (guard_bytes a_draw).
  Proof.
    intros segs. pose proof (u64_range tid). subst D.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel. apply rdn_guard.
  Qed.

  (* [comment removed for export] *)
  Lemma D_main_guard_at : forall i, (0 <= i < 8)%Z ->
    D (Z_to_bv 64 (0x12aac8 + i)) = Some (nth (Z.to_nat i) (guard_bytes a_draw) (Z_to_bv 8 0)).
  Proof.
    intros i Hi. pose proof (u64_range tid). subst D.
    unfold D_main, D_fd, D_ssp.
    rewrite wbytes_outside by (cbn [length]; unorm; lia).
    rewrite wbytes_outside by (rewrite length_N_to_le_bytes; unorm; lia).
    unfold guard_bytes.
    set (A := word_to_le_bytes 4 (v_lw (rwa a_draw))). set (B := word_to_le_bytes 4 (v_lw (rwb a_draw))).
    assert (HA : length A = 4%nat) by (subst A; apply length_N_to_le_bytes).
    assert (HB : length B = 4%nat) by (subst B; apply length_N_to_le_bytes).
    destruct A as [|x0 [|x1 [|x2 [|x3 [|? ?]]]]]; try discriminate HA.
    destruct B as [|y0 [|y1 [|y2 [|y3 [|? ?]]]]]; try discriminate HB.
    cbn [firstn skipn app].
    assert (Hc : (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7)%Z) by lia.
    destruct Hc as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]];
      first [ rewrite wbytes_inside by (cbn [length]; unorm; lia); unorm; reflexivity
            | rewrite wbytes_outside by (cbn [length]; unorm; lia);
              first [ rewrite wbytes_inside by (cbn [length]; unorm; lia); unorm; reflexivity
                    | rewrite wbytes_outside by (cbn [length]; unorm; lia);
                      rewrite wbytes_inside by (cbn [length]; unorm; lia); unorm; reflexivity ] ].
  Qed.

  (* [comment removed for export] *)
  Lemma guard_bytes_w : guard_bytes a_draw = word_to_le_bytes 8 (canary_w a_draw).
  Proof.
    unfold word_to_le_bytes. rewrite <- canary_val, <- (length_guard_bytes a_draw).
    symmetry. apply Z_to_le_bytes_lez.
  Qed.

  Lemma D_main_guard_w : forall segs,
    rdn segs D (Z_to_bv 64 0x12aac8) 8 = Some (word_to_le_bytes 8 (canary_w a_draw)).
  Proof. intros segs. rewrite <- guard_bytes_w. apply D_main_guard. Qed.

  (* [comment removed for export] *)
  Lemma D_main_pagesize : forall segs,
    rdn segs D (Z_to_bv 64 0x12ab18) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 4096)).
  Proof.
    intros segs. pose proof (u64_range tid). pose proof len_av. subst D.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    apply rdn_wbytes_hit8. unorm; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma D_main_environ : forall segs,
    rdn segs D (Z_to_bv 64 0x10a788) 8 = Some (word_to_le_bytes 8 (envp_w sp0 av)).
  Proof.
    intros segs. pose proof (u64_range tid). pose proof len_av. subst D.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    apply rdn_wbytes_hit8. unorm; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma D_main_self : forall segs,
    rdn segs D (Z_to_bv 64 0x10a790) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x10a790)).
  Proof.
    intros segs. pose proof (u64_range tid). subst D.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    apply rdn_wbytes_hit8. unorm; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma D_main_canary : forall segs,
    rdn segs D (Z_to_bv 64 0x10a848) 8 = Some (word_to_le_bytes 8 (canary_w a_draw)).
  Proof.
    intros segs. pose proof (u64_range tid). subst D.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    apply rdn_wbytes_hit8. unorm; lia.
  Qed.

  (* [comment removed for export] *)
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Hypothesis ME : main_entry sp0 av ev tid regs mem.

  Lemma main_entry_rdn_image : forall segs (a : Z) (n : nat),
    D_main_missb a n = true ->
    rdn segs mem (Z_to_bv 64 a) n = rdn segs (fun _ => None) (Z_to_bv 64 a) n.
  Proof.
    intros segs a n Hb.
    assert (Hr : (0 <= a /\ a + Z.of_nat n <= 0x12c000)%Z).
    { unfold D_main_missb in Hb. apply andb_true_iff in Hb as [Hb H2]. apply andb_true_iff in Hb as [_ H1].
      apply Z.leb_le in H1. apply Z.leb_le in H2. lia. }
    rewrite (main_entry_rdn_data sp0 av ev tid regs mem ME)
      by (rewrite stack_max_size_val; unorm; lia).
    apply D_main_miss. exact Hb.
  Qed.

  Lemma main_entry_tid : forall segs,
    rdn segs mem (Z_to_bv 64 0x10a7b0) 4 = Some (word_to_le_bytes 4 tid).
  Proof.
    intros segs. rewrite (main_entry_rdn_data sp0 av ev tid regs mem ME)
      by (rewrite stack_max_size_val; unorm; lia). apply D_main_tid.
  Qed.

  Lemma main_entry_guard : forall segs,
    rdn segs mem (Z_to_bv 64 0x12aac8) 8 = Some (guard_bytes a_draw).
  Proof.
    intros segs. rewrite (main_entry_rdn_data sp0 av ev tid regs mem ME)
      by (rewrite stack_max_size_val; unorm; lia). apply D_main_guard.
  Qed.

  Lemma main_entry_guard_w : forall segs,
    rdn segs mem (Z_to_bv 64 0x12aac8) 8 = Some (word_to_le_bytes 8 (canary_w a_draw)).
  Proof. intros segs. rewrite <- guard_bytes_w. apply main_entry_guard. Qed.
End Facts.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End V9StartupFacts.

From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng Require AllocSure.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng Require MallocSure.
Module V9Sure.
Import Stdlib.ZArith.ZArith.
Import Stdlib.NArith.NArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Import LinuxProcessSemantics.LinuxProcessSem.Fs.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.LinuxProcessSem.Monad.
Import LinuxProcessSemantics.LinuxProcessSem.Specs.
Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.PureModel.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.VmLedger.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.AllocIface.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng.MallocLayout.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng.MallocTree.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng.MallocOps.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng.MallocIface.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng.MallocInv_defs.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng.MallocIfaceX.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng.AllocBase.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng.AllocSure.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng.MallocAllocLayout.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng.MallocGlue.
Import OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng.MallocSure.
Import V9MallocLayout.
Import V9Ref_malloc.
Import V9Ref_free.
Import V9Ref_calloc.
Import V9Alloc.
(* [comment removed for export] *)





Import ListNotations.
Local Open Scope Z_scope.

Definition u16_sure : AllocSure (AL:=mallocng_alloc_layout (ML:=LU16)) (CL:=mallocng_calloc_layout (ML:=LU16)) :=
  mallocng_sure (ML:=LU16) u16_malloc_okX u16_free_okX u16_calloc_okX
    (fun fx => malloc_refines (fx:=fx)) (fun fx => free_refines (fx:=fx)) (fun fx => calloc_refines (fx:=fx)).

Lemma u16_sure_calloc : asr_calloc (AllocSure:=u16_sure) = u16_calloc.
Proof. reflexivity. Qed.

Lemma u16_sure_base : aic_base (AllocCalloc:=asr_calloc (AllocSure:=u16_sure)) = u16_base.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma u16_sure_room : forall A h k b,
  aroom (AllocSure:=u16_sure) A h k b <-> g_room A h k b.
Proof. intros. reflexivity. Qed.
End V9Sure.
