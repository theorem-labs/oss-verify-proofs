(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
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
From OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images Require Ubsan.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require PropExec.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require CatExec.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require Hoare.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require AgentLib.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require MallocLayout.
Module V10MallocLayout.
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
Import OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images.Ubsan.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Hoare.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AgentLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.MallocLayout.
(* [comment removed for export] *)





Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Module ImgU16 := Ubsan.

(* [comment removed for export] *)
Instance LU16 : MallocLayout := {|
  ml_segs := ImgU16.M.loaded_segments;
  IMG_LO := 0x10000; RW_LO := 0x33000; IMG_HI := 0x66000;

  A_LOCK           := Z_to_bv 64 0x65778;
  A_CTX            := Z_to_bv 64 0x65780;
  A_INIT_DONE      := Z_to_bv 64 0x65788;
  A_MMAP_CTR       := Z_to_bv 64 0x6578c;
  A_FREE_META_HEAD := Z_to_bv 64 0x65790;
  A_AVAIL_META     := Z_to_bv 64 0x65798;
  A_AVAIL_META_CNT := Z_to_bv 64 0x657a0;
  A_AVAIL_AREA_CNT := Z_to_bv 64 0x657a8;
  A_META_SHIFT     := Z_to_bv 64 0x657b0;
  A_AREA_HEAD      := Z_to_bv 64 0x657b8;
  A_AREA_TAIL      := Z_to_bv 64 0x657c0;
  A_AVAIL_AREAS    := Z_to_bv 64 0x657c8;
  Z_UNMAP_SEQ      := 0x65ad0;
  Z_BOUNCES        := 0x65af0;
  A_SEQ            := Z_to_bv 64 0x65b10;
  A_BRK            := Z_to_bv 64 0x65b18;
  A_MALLOC_REPLACED := Z_to_bv 64 0x65b20;

  A_LIBC       := Z_to_bv 64 0x65708;
  A_NEED_LOCKS := Z_to_bv 64 0x6570b;
  A_PAGE_SIZE  := Z_to_bv 64 0x65738;
  A_TP         := Z_to_bv 64 0x45480;
  A_ERRNO      := Z_to_bv 64 0x453dc;
  A_GOT_SSP    := Z_to_bv 64 0x33dc0;
  A_SSP        := Z_to_bv 64 0x656e8;

  A_SIZE_CLASSES  := Z_to_bv 64 0x1232c;
  A_SMALL_CNT_TAB := Z_to_bv 64 0x1238c;
  A_MED_CNT_TAB   := Z_to_bv 64 0x116a0;
  A_DEBRUIJN      := Z_to_bv 64 0x1230c;

  PC_MALLOC      := (0x2b348%bv : word);
  PC_FREE        := (0x2b208%bv : word);
  PC_CALLOC      := (0x2b0d0%bv : word);
  PC_LIBC_FREE   := (0x2b34c%bv : word);
  PC_MALLOC_IMPL := (0x2bcd8%bv : word);
  PC_GET_META    := (0x2b518%bv : word);
  PC_NTFREE      := (0x2b628%bv : word);
  PC_ALLOC_META  := (0x2ba00%bv : word);
  PC_ALLOC_SLOT  := (0x2c048%bv : word);
  PC_ENFRAME     := (0x2c8ec%bv : word);
  PC_ALLZEROP    := (0x2ca3c%bv : word);
  PC_MMAP        := (0x2cc50%bv : word);
  PC_MPROTECT    := (0x2cd3c%bv : word);
  PC_MUNMAP      := (0x2cd84%bv : word);
  PC_VM_WAIT     := (0x2cc4c%bv : word);
  PC_SYSCALL_RET := (0x2b090%bv : word);
  PC_ERRNO_LOC   := (0x2ac88%bv : word);
  PC_LOCK        := (0x32944%bv : word);
  PC_UNLOCK      := (0x32bcc%bv : word);
  PC_MEMCPY      := (0x3233c%bv : word);
  PC_MEMSET      := (0x32740%bv : word)
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
Local Abbreviation B0 := 0x10000.  Local Abbreviation B1 := 0x15000.  Local Abbreviation B2 := 0x33000.
Local Abbreviation B3 := 0x34000.  Local Abbreviation B4 := 0x66000.
Local Abbreviation P0 := 5%nat.  Local Abbreviation P1 := 30%nat.  Local Abbreviation P2 := 1%nat.  Local Abbreviation P3 := 50%nat.

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

Instance LU16ok : MallocLayoutOk LU16.
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
End V10MallocLayout.

From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require StoreOk.
Module V10MemPreds.
Import Stdlib.ZArith.ZArith.
Import Stdlib.NArith.NArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images.Ubsan.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StoreOk.
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
End V10MemPreds.

Module V10PFBase.
Import OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images.Ubsan.
(* [comment removed for export] *)

Abbreviation SEGS := Ubsan.M.loaded_segments.
End V10PFBase.

From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc Require Reloc.
Module V10Reloc.
Import Stdlib.ZArith.ZArith.
Import Stdlib.Lists.List.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images.Ubsan.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.Reloc.
(* [comment removed for export] *)




Import ListNotations.
Local Open Scope Z_scope.

Definition v10_dtab : list (positive * Z) :=
  [(8%positive, 0); (1000%positive, 8252); (1001%positive, 8252); (1002%positive, 8252); (1003%positive, 8252); (1004%positive, 8252); (1005%positive, 8252); (1006%positive, 8252); (1007%positive, 8252); (1008%positive, 8376); (1009%positive, 8508); (1010%positive, 8508); (1011%positive, 8508); (1012%positive, 8508); (1013%positive, 8508); (1014%positive, 8508); (1015%positive, 72740); (1016%positive, 87368); (1017%positive, 87368); (1018%positive, 87368); (1019%positive, 87368); (1020%positive, 87368); (1021%positive, 87368); (1022%positive, 87356); (1023%positive, 87356); (1024%positive, 87356); (1025%positive, 87760); (1026%positive, 87760); (1027%positive, 87760); (1028%positive, 87760); (1029%positive, 87760); (1030%positive, 87760); (1031%positive, 87760); (1032%positive, 87760); (1033%positive, 87760); (1034%positive, 87760); (1035%positive, 87760); (1036%positive, 88076); (1037%positive, 88076); (1038%positive, 88076); (1039%positive, 88076); (1040%positive, 88076); (1041%positive, 88076); (1042%positive, 88076); (1043%positive, 88076); (1044%positive, 88076); (1045%positive, 88076); (1046%positive, 88076); (1047%positive, 88076); (1048%positive, 88076); (1049%positive, 88076); (1050%positive, 88076); (1051%positive, 88076); (1052%positive, 88444); (1053%positive, 88444); (1054%positive, 88444); (1055%positive, 88444); (1056%positive, 88444); (1057%positive, 88444); (1058%positive, 88444); (1059%positive, 88444); (1060%positive, 88444); (1061%positive, 88444); (1062%positive, 88444); (1063%positive, 88616); (1064%positive, 88616); (1065%positive, 88616); (1066%positive, 88616); (1067%positive, 88616); (1068%positive, 88616); (1069%positive, 88616); (1070%positive, 88616); (1071%positive, 88616); (1072%positive, 88616); (1073%positive, 88616); (1074%positive, 88616); (1075%positive, 88616); (1076%positive, 88616); (1077%positive, 88616); (1078%positive, 88616); (1079%positive, 88616); (1080%positive, 88616); (1081%positive, 88616); (1082%positive, 88616); (1083%positive, 88616); (1084%positive, 88616); (1085%positive, 88616); (1086%positive, 69796); (1087%positive, 88456); (1088%positive, 88456); (1089%positive, 88456); (1090%positive, 88456); (1091%positive, 88456); (1092%positive, 88512); (1093%positive, 88512); (1094%positive, 88512); (1095%positive, 88512); (1096%positive, 88512); (1097%positive, 88512); (1098%positive, 88512); (1099%positive, 88524); (1100%positive, 88524); (1101%positive, 88524); (3000%positive, 8376); (3001%positive, 72740); (4000%positive, 86); (4001%positive, 533); (4002%positive, 751); (4003%positive, 751); (4004%positive, 810); (4005%positive, 810); (4006%positive, 1061); (4007%positive, 1061); (4008%positive, 1502); (4009%positive, 1740); (4010%positive, 1740); (4011%positive, 2344); (4012%positive, 2344); (4013%positive, 2570); (4014%positive, 2686); (4015%positive, 2785); (4016%positive, 3004); (4017%positive, 3101); (4018%positive, 3101); (5000%positive, 3928); (5001%positive, 3928); (5002%positive, 593); (5003%positive, 728); (5004%positive, 752); (5005%positive, 752); (5006%positive, 760); (5007%positive, 760); (5008%positive, 3840); (5009%positive, 3840); (5010%positive, 3840); (5011%positive, 4400); (5012%positive, 88536); (5013%positive, 88544); (5015%positive, 89344); (5016%positive, 88528); (5018%positive, 3116); (5019%positive, 89344); (5020%positive, 3928); (5021%positive, 752); (5022%positive, 752); (5023%positive, 760); (5024%positive, 760); (5025%positive, 760); (5026%positive, 88544); (5027%positive, 88544); (5028%positive, 88544); (5029%positive, 89288); (5030%positive, 220832); (5031%positive, 220832); (5032%positive, 220832); (5033%positive, 220832);
   (230%positive, -56276); (240%positive, -56276); (241%positive, -56276); (242%positive, -56276); (243%positive, -56276); (231%positive, -55720); (232%positive, -54700); (244%positive, -54700); (245%positive, -54700); (246%positive, -54700); (233%positive, -53908); (234%positive, -53236); (247%positive, -53096); (235%positive, -53020); (236%positive, -50520); (237%positive, -44940); (248%positive, -44940); (238%positive, -42288); (249%positive, -42288); (250%positive, -27708); (239%positive, 6160); (400%positive, 17); (401%positive, 17); (402%positive, 17); (403%positive, 33); (404%positive, 33); (405%positive, -74); (406%positive, 96); (407%positive, 96); (408%positive, 127); (409%positive, 127); (410%positive, 292); (411%positive, 292); (412%positive, 307); (413%positive, 391); (414%positive, 406); (415%positive, 406); (416%positive, 472); (417%positive, 521); (418%positive, 597); (419%positive, 798); (420%positive, 798); (421%positive, 1023); (422%positive, 1141); (423%positive, 1251); (424%positive, 1279); (425%positive, 1321); (426%positive, 1359); (427%positive, 1359); (428%positive, 1471); (429%positive, 1471); (430%positive, 1496); (431%positive, 1496); (432%positive, 1496); (433%positive, 1496); (434%positive, 1561); (435%positive, 1561); (436%positive, 1625); (437%positive, 1625); (438%positive, 1681); (439%positive, 1705); (440%positive, 1705); (441%positive, 1730); (442%positive, 1753); (443%positive, 1753); (444%positive, 1873); (445%positive, 1881); (446%positive, 1909); (447%positive, 1950); (448%positive, 1966); (449%positive, 1982); (450%positive, 2081); (451%positive, 2100); (452%positive, 2167); (453%positive, 2167); (454%positive, 2167); (455%positive, 2223); (456%positive, 2223); (457%positive, 2239); (458%positive, 2327); (459%positive, 2382); (460%positive, 2395); (461%positive, 2395); (462%positive, 2466); (463%positive, 2539); (464%positive, 2576); (465%positive, 2576); (466%positive, 2657); (467%positive, 2962); (468%positive, 2975); (469%positive, 2991); (470%positive, 2991); (471%positive, 3072); (1900%positive, 87356); (5034%positive, 88536); (5035%positive, 89344); (5036%positive, 220624)].

Definition v10_stab : list (Z * Z) := [
  (0x13084, 0xffffb197); (0x13088, 0x74018193); (0x13090, 0xfffeb597); (0x13094, 0xf3458593);
  (0x1309c, 0x40006f); (0x130a4, 0x1f617); (0x130a8, 0x1f697); (0x130ac, 0x1f717);
  (0x130b0, 0xc6863783); (0x130b4, 0xc6c6b683); (0x130b8, 0xc7073703); (0x130c8, 0x2d1506f);
  (0x130dc, 0x20517); (0x130e0, 0x21850513); (0x130f8, 0x20517); (0x130fc, 0x1fc50593);
  (0x13108, 0x1f517); (0x1310c, 0xc1c53503); (0x13118, 0xffffe517); (0x1311c, 0x94450513);
  (0x13120, 0x20597); (0x13124, 0x1dc58593); (0x13150, 0x20517); (0x13154, 0x1ec50513);
  (0x1316c, 0x20517); (0x13170, 0x1d050593); (0x1317c, 0x1f517); (0x13180, 0xbb053503);
  (0x1318c, 0x20517); (0x13190, 0xc1050513); (0x131a0, 0x1f517); (0x131a4, 0xb9453503);
  (0x131b0, 0xffffe517); (0x131b4, 0x8ac50513); (0x1320c, 0x4fd150ef); (0x13220, 0xec160ef);
  (0x13230, 0x20517); (0x13234, 0x10d50b13); (0x1324c, 0xb41d0ef); (0x13274, 0x98160ef);
  (0x13290, 0x701d0ef); (0x13298, 0x735150ef); (0x132b4, 0x1f11d0ef); (0x132c8, 0x17d1d0ef);
  (0x1332c, 0x168000ef); (0x13340, 0x160000ef); (0x13350, 0x148000ef); (0x13368, 0x1f517);
  (0x1336c, 0x9d453503); (0x13378, 0xffffb597); (0x1337c, 0x50358593); (0x13380, 0x48180ef);
  (0x13388, 0x1f517); (0x1338c, 0x9b453503); (0x13394, 0xffffc517); (0x1339c, 0xfc50513);
  (0x133a4, 0x1f517); (0x133a8, 0x99853503); (0x133b0, 0xffffb517); (0x133b8, 0x4dc50513);
  (0x133c0, 0x254180ef); (0x133c8, 0x605150ef); (0x133fc, 0x1f517); (0x13400, 0x94053503);
  (0x13408, 0xffffc597); (0x1340c, 0xdb058593); (0x13418, 0x1f517); (0x1341c, 0x92453503);
  (0x13424, 0xffffc597); (0x13428, 0x95458593); (0x13430, 0x799170ef); (0x13438, 0x1f517);
  (0x1343c, 0x90453503); (0x13444, 0xffffb517); (0x1344c, 0x2b450513); (0x13454, 0x1c0180ef);
  (0x1345c, 0x239150ef); (0x13460, 0x1f517); (0x13464, 0x8dc53503); (0x1346c, 0xffffc597);
  (0x13470, 0xd3758593); (0x13478, 0x1f517); (0x1347c, 0x8c453503); (0x13484, 0xffffb517);
  (0x1348c, 0x27450513); (0x135d8, 0xffffb517); (0x135dc, 0xb850513); (0x135e4, 0x2111c0ef);
  (0x13674, 0xffffc517); (0x13678, 0xe1f50513); (0x1367c, 0x18000ef); (0x13708, 0x851c0ef);
  (0x13710, 0x1f517); (0x13714, 0x5bc53583); (0x13744, 0xffffc517); (0x13748, 0xd4f50513);
  (0x1374c, 0xf49ff0ef); (0x1376c, 0x1e597); (0x13770, 0x4d05b583); (0x13778, 0x4091706f);
  (0x13780, 0x517); (0x13784, 0xfe450513); (0x13788, 0x1f597); (0x1378c, 0x54a5b223);
  (0x14d1c, 0x40006f); (0x15198, 0x60080ef); (0x1519c, 0x9517); (0x151a0, 0x6b453503);
  (0x151b4, 0x3b517); (0x151b8, 0xc50913); (0x15204, 0x3b617); (0x15208, 0x2b63223);
  (0x15210, 0x3b597); (0x15214, 0xf8a5bc23); (0x1521c, 0x3b517); (0x15220, 0x53623);
  (0x15238, 0xfffe6517); (0x1523c, 0x750413); (0x15240, 0x9517); (0x15244, 0x61853583);
  (0x15248, 0x9517); (0x1524c, 0x61853503); (0x1527c, 0x214000ef); (0x15284, 0x5d000ef);
  (0x152f8, 0xfffe7517); (0x15304, 0xe4a50593); (0x15328, 0xfffe7517); (0x15334, 0xe1a50593);
  (0x15358, 0xfffe7517); (0x15364, 0xdea50593); (0x153ac, 0xdc1ff0ef); (0x153b0, 0x9517);
  (0x153b4, 0x9597); (0x153b8, 0x4b853403); (0x153bc, 0x4bc5b483); (0x15418, 0xd59ff0ef);
  (0x1541c, 0x517); (0x15420, 0x2c50313); (0x15478, 0xf25ff0ef); (0x1548c, 0x4fc000ef);
  (0x154b4, 0x3b597); (0x154b8, 0xa8c58593); (0x154bc, 0x3b617); (0x154c0, 0xd0460493);
  (0x154d0, 0xb717); (0x154e0, 0x9297); (0x154e4, 0x90876f03); (0x154e8, 0x3182b283);
  (0x15630, 0x1b697); (0x15644, 0x84068513); (0x156c0, 0x60080ef); (0x156d8, 0x3b597);
  (0x156e4, 0x86858513); (0x15700, 0x3b517); (0x15704, 0xaa853503); (0x15768, 0xfffe7617);
  (0x15774, 0x56060613); (0x15784, 0xfffe7617); (0x15788, 0xd9c60613); (0x15790, 0x4000006f);
  (0x157c4, 0x9517); (0x157c8, 0x9597); (0x157cc, 0xf3453503); (0x157d0, 0xf385b403);
  (0x157fc, 0xfb5ff06f); (0x15818, 0x3a697); (0x1581c, 0x7f868693); (0x15860, 0xdbdff0ef);
  (0x15864, 0xf51ff0ef); (0x15868, 0x160020ef); (0x15870, 0xd91ff0ef); (0x15894, 0x9517);
  (0x15898, 0xe5c53483); (0x158f0, 0x4a5070ef); (0x1592c, 0x94000ef); (0x15954, 0x64000ef);
  (0x15968, 0x9517); (0x1596c, 0xd8853503); (0x15974, 0x2f8070ef); (0x1597c, 0x9517);
  (0x15980, 0xd7453503); (0x15994, 0x9517); (0x15998, 0xd5c53503); (0x159dc, 0xbddff0ef);
  (0x159fc, 0xffdff06f); (0x15a1c, 0xb9dff0ef); (0x15a4c, 0x22c000ef); (0x15a58, 0x3b517);
  (0x15a5c, 0x9f852503); (0x15a84, 0x5ec070ef); (0x15aa0, 0x5d0070ef); (0x15ae0, 0x590070ef);
  (0x15b0c, 0x5640706f); (0x15b2c, 0x41010ef); (0x15b38, 0x1440006f); (0x15b3c, 0x1910006f);
  (0x15b60, 0x1ac000ef); (0x15b94, 0xfffe7717); (0x15b9c, 0xf8c70713); (0x15c40, 0x3a717);
  (0x15c5c, 0x2bf74883); (0x15c94, 0x3a597); (0x15c98, 0x2d858593); (0x15ca4, 0x494070ef);
  (0x15cb0, 0x16c000ef); (0x15cbc, 0x3a517); (0x15cc0, 0x2b050513); (0x15cc4, 0x6fc070ef);
  (0x15ccc, 0xfb0ff0ef); (0x15ce0, 0x99010ef); (0x15d9c, 0x3a797); (0x15da8, 0x1d87b783);
  (0x15dc8, 0xfffe7797); (0x15dcc, 0xd5878793); (0x15e34, 0x8617); (0x15e38, 0x78063483);
  (0x15e84, 0x3a817); (0x15e88, 0xf080913); (0x15e98, 0xfffe7817); (0x15e9c, 0xc8880813);
  (0x15f90, 0x3a697); (0x15f94, 0xfe468693); (0x1608c, 0xc81ff0ef); (0x161f0, 0xe8cff0ef);
  (0x16210, 0x8517); (0x16214, 0x3a453903); (0x1621c, 0x3a597); (0x16224, 0xd5058993);
  (0x1622c, 0x3a597); (0x16230, 0xcd058413); (0x1626c, 0xc5060ef); (0x1637c, 0xc8010ef);
  (0x163d4, 0x70010ef); (0x164a8, 0x88010ef); (0x164b0, 0xfcdfe0ef); (0x164c8, 0xbb4ff0ef);
  (0x164f8, 0xf85fe0ef); (0x16534, 0x3a597); (0x16538, 0xa3858493); (0x16560, 0x6e5000ef);
  (0x1656c, 0x3a517); (0x16570, 0x99354503); (0x16578, 0x3a517); (0x1657c, 0x9f450513);
  (0x16580, 0x3b9060ef); (0x165b0, 0xfffe6617); (0x165b8, 0x55060993); (0x16620, 0xfffe6617);
  (0x16634, 0x50060593); (0x16654, 0xba1ff0ef); (0x166c0, 0x3a517); (0x166c4, 0x83f54503);
  (0x166cc, 0x3a517); (0x166d0, 0x8a050513); (0x166d4, 0x265060ef); (0x16718, 0x3a517);
  (0x1671c, 0x85450513); (0x16720, 0x4a1060ef); (0x1672c, 0x64d000ef); (0x167d8, 0x64000ef);
  (0x167f8, 0x3c9060ef); (0x16828, 0xb90006f); (0x1682c, 0x39517); (0x16830, 0x74050513);
  (0x16834, 0x38d060ef); (0x16874, 0x8517); (0x16878, 0xd4053a03); (0x16884, 0x39597);
  (0x16888, 0x6e858b13); (0x16a04, 0xfffe6597); (0x16a0c, 0xfc58593); (0x16a20, 0xfffe6517);
  (0x16a24, 0x10050c93); (0x16a30, 0xfc4ff0ef); (0x16a44, 0x39597); (0x16a48, 0x4e85b583);
  (0x16a5c, 0xfffe6697); (0x16a60, 0x12468693); (0x16a8c, 0xfffe5697); (0x16a90, 0x40868693);
  (0x16ba4, 0xfffe6697); (0x16bac, 0xf5c68693); (0x16c48, 0x498000ef); (0x16d18, 0xfffe6717);
  (0x16d20, 0xe0870713); (0x16ee8, 0x55c000ef); (0x170dc, 0xfa0fe0ef); (0x17108, 0xfffe6797);
  (0x17110, 0xa1878793); (0x172c4, 0x39797); (0x172cc, 0xcb07b783); (0x172ec, 0xfffe6817);
  (0x172f0, 0x83480813); (0x17360, 0xfffe5597); (0x17364, 0x7c058593); (0x1738c, 0xfffe5517);
  (0x17390, 0x79450513); (0x173b0, 0xfffe5597); (0x173b4, 0xbbc5b787); (0x173e8, 0xfffe5597);
  (0x173ec, 0xb9c5b787); (0x1746c, 0x810fe0ef); (0x17484, 0xff9fd0ef); (0x174e0, 0xf61ff0ef);
  (0x17528, 0xb5cfe0ef); (0x17538, 0x39697); (0x1753c, 0x9f46b683); (0x17564, 0xb20fe0ef);
  (0x17590, 0xeb1ff0ef); (0x175a4, 0xae0fe0ef); (0x17728, 0x664000ef); (0x17734, 0x39517);
  (0x17738, 0xa7853403); (0x1774c, 0xd05ff0ef); (0x17790, 0x8517); (0x17794, 0x20c53403);
  (0x177a8, 0xca9ff0ef); (0x177ec, 0x8517); (0x177f0, 0xc053403); (0x17804, 0xc4dff0ef);
  (0x17868, 0xbe9ff0ef); (0x178ec, 0x7517); (0x178f0, 0xb5853a83); (0x1794c, 0xdc9fd0ef);
  (0x179d4, 0xd41fd0ef); (0x17a4c, 0xcc1fd0ef); (0x17a54, 0x1050506f); (0x17a68, 0xff1ff0ef);
  (0x17a74, 0xca1fd0ef); (0x17a9c, 0x7817); (0x17aa0, 0x9a883403); (0x17ac8, 0x3a0000ef);
  (0x17ae8, 0xc25fd0ef); (0x17b5c, 0x398050ef); (0x17b74, 0x160000ef); (0x17c54, 0xe99ff0ef);
  (0x17c9c, 0x525040ef); (0x17d14, 0xf3cff0ef); (0x17d28, 0xe75ff0ef); (0x17d38, 0x815ff0ef);
  (0x17d58, 0xe45ff0ef); (0x17d98, 0x38517); (0x17d9c, 0x41c50413); (0x17da4, 0x224050ef);
  (0x17de4, 0x6517); (0x17de8, 0x5b453903); (0x17e20, 0x14c000ef); (0x17e34, 0xd70ff0ef);
  (0x17e94, 0xbadff0ef); (0x17ec0, 0xac000ef); (0x17f30, 0xd70ff0ef); (0x17f68, 0xef8fd0ef);
  (0x17fc4, 0x6517); (0x17fd0, 0x3d453603); (0x180b0, 0xa41ff0ef); (0x183d0, 0xfffe4697);
  (0x183d4, 0x6f868693); (0x18444, 0x159000ef); (0x1849c, 0xfffe4597); (0x184a0, 0x4e458593);
  (0x184dc, 0x2c9000ef); (0x1850c, 0xfffe2597); (0x18514, 0x40958593); (0x18538, 0xfffe2517);
  (0x1853c, 0x3dd50513); (0x18554, 0xfffe3517); (0x18558, 0x71850b93); (0x18560, 0xd01fc0ef);
  (0x18568, 0xd05fc0ef); (0x18580, 0x159040ef); (0x18598, 0xfffe2617); (0x1859c, 0x37d60613);
  (0x185dc, 0xfffe2597); (0x185e0, 0x33958593); (0x18614, 0xfffe4597); (0x18618, 0x44c58593);
  (0x18644, 0xfffe2597); (0x18648, 0x2d158893); (0x18680, 0xfffe2517); (0x18684, 0x29550513);
  (0x186b8, 0xfffe2597); (0x186bc, 0x25d58713); (0x186d0, 0xfffe4697); (0x186d4, 0x5c868693);
  (0x18734, 0x739010ef); (0x1876c, 0x764000ef); (0x18790, 0x6dd010ef); (0x187b4, 0xb3cff0ef);
  (0x187c0, 0xfffe2597); (0x187c4, 0x15558593); (0x187e8, 0xfffe2597); (0x187f0, 0x12d58893);
  (0x18938, 0x3e0040ef); (0x18968, 0x988ff0ef); (0x1898c, 0x964ff0ef); (0x189a8, 0x948ff0ef);
  (0x189dc, 0x33c040ef); (0x18a0c, 0x8e4ff0ef); (0x18a30, 0x8c0ff0ef); (0x18a60, 0x2b8040ef);
  (0x18a90, 0x860ff0ef); (0x18ab4, 0x83cff0ef); (0x18ad0, 0x820ff0ef); (0x18b04, 0x214040ef);
  (0x18b34, 0xfbdfe0ef); (0x18b54, 0xf9dfe0ef); (0x18b70, 0x360000ef); (0x18b94, 0x33c000ef);
  (0x18be4, 0xe7cfc0ef); (0x18c18, 0x184000ef); (0x18c2c, 0x170000ef); (0x18c40, 0x15c000ef);
  (0x18c54, 0x148000ef); (0x18c68, 0x134000ef); (0x18c7c, 0x120000ef); (0x18c90, 0x10c000ef);
  (0x18ca4, 0xf8000ef); (0x18cb8, 0xe4000ef); (0x18d38, 0xd28fc0ef); (0x18d98, 0x8c9fc0ef);
  (0x18dac, 0xfffe4697); (0x18db0, 0xcd468693); (0x18dfc, 0x1c1010ef); (0x18eec, 0x5517);
  (0x18ef0, 0x4ac53903); (0x18f24, 0x5f5030ef); (0x18f54, 0xb9dfe0ef); (0x18f74, 0xb7dfe0ef);
  (0x18fa0, 0xec0fc0ef); (0x19000, 0x5517); (0x19004, 0x39853a03); (0x1905c, 0xf1010ef);
  (0x19068, 0xfffe2517); (0x19070, 0xb8150513); (0x19084, 0xfffe2517); (0x1908c, 0xb6550513);
  (0x190c4, 0x91010ef); (0x190e0, 0xb9010ef); (0x190f0, 0x148020ef); (0x19104, 0x235010ef);
  (0x19118, 0x159010ef); (0x19154, 0xfffe3517); (0x19158, 0xbb453507); (0x1915c, 0x660010ef);
  (0x19170, 0x1c9010ef); (0x191a0, 0xd1010ef); (0x191a8, 0xfffe2597); (0x191ac, 0xfffe3617);
  (0x191b0, 0xf7158593); (0x191b4, 0x85e60993); (0x19210, 0xf7dfd0ef); (0x19230, 0x58c010ef);
  (0x1924c, 0xf4020ef); (0x19258, 0xf8020ef); (0x19268, 0xfffe2597); (0x1926c, 0xfffe2617);
  (0x19270, 0x12058593); (0x19274, 0x6f260993); (0x192b0, 0x269030ef); (0x192e0, 0x811fe0ef);
  (0x19300, 0xff0fe0ef); (0x1931c, 0xfd4fe0ef); (0x19338, 0xfb8fe0ef); (0x1936c, 0x1ad030ef);
  (0x1939c, 0xf54fe0ef); (0x193bc, 0xf34fe0ef); (0x19454, 0x704020ef); (0x19464, 0x5d5010ef);
  (0x19478, 0x774020ef); (0x1948c, 0x6b5010ef); (0x194a0, 0x698010ef); (0x194b4, 0x5bc010ef);
  (0x194c0, 0xfffe3517); (0x194c4, 0x8a053503); (0x1975c, 0x60010ef); (0x19778, 0x3d9010ef);
  (0x19784, 0x3bd010ef); (0x19864, 0xfffe3797); (0x19880, 0x43478913); (0x198a0, 0x1d0010ef);
  (0x198b4, 0x424020ef); (0x198d4, 0x165010ef); (0x198e4, 0x155010ef); (0x198f8, 0x249010ef);
  (0x1990c, 0x22c010ef); (0x19934, 0x13c010ef); (0x199f4, 0x324030ef); (0x19a24, 0x8ccfe0ef);
  (0x19a68, 0x7d0010ef); (0x19a78, 0x308020ef); (0x19ab8, 0x780010ef); (0x19acc, 0x85010ef);
  (0x19ae0, 0xfffe2517); (0x19ae4, 0x25853507); (0x19b08, 0xfe9fd0ef); (0x19b24, 0xfcdfd0ef);
  (0x19b50, 0x1c8030ef); (0x19b80, 0xf71fd0ef); (0x19ba0, 0xf51fd0ef); (0x19bc4, 0xf2dfd0ef);
  (0x19bec, 0x12c030ef); (0x19c1c, 0xed5fd0ef); (0x19c3c, 0xeb5fd0ef); (0x19c58, 0xe99fd0ef);
  (0x19c84, 0x94030ef); (0x19cb4, 0xe3dfd0ef); (0x19cd4, 0xe1dfd0ef); (0x19cf0, 0xfffe2517);
  (0x19cf4, 0x3853507); (0x19cfc, 0xfffe2517); (0x19d00, 0x5c53507); (0x19d04, 0x2b9000ef);
  (0x19d38, 0x500010ef); (0x19d54, 0x5e5000ef); (0x19d70, 0x5c9000ef); (0x19d90, 0x5c0010ef);
  (0x19d9c, 0x4d5000ef); (0x1a0dc, 0x43d020ef); (0x1a110, 0x9e1fd0ef); (0x1a138, 0x9b9fd0ef);
  (0x1a158, 0x999fd0ef); (0x1a194, 0x385020ef); (0x1a1c8, 0x929fd0ef); (0x1a1f0, 0x901fd0ef);
  (0x1a2ec, 0x805fd0ef); (0x1a314, 0xfffe1597); (0x1a324, 0xa4c58513); (0x1a3dc, 0xf14fd0ef);
  (0x1a424, 0xeccfd0ef); (0x1a458, 0xe98fd0ef); (0x1a484, 0xa4dfe0ef); (0x1a4ac, 0xe44fd0ef);
  (0x1a4c8, 0xfffe1517); (0x1a4cc, 0x89850513); (0x1a4d8, 0xe18fd0ef); (0x1a5a0, 0xd50fd0ef);
  (0x1a5c8, 0x909fe0ef); (0x1a604, 0x714020ef); (0x1a634, 0xcbcfd0ef); (0x1a654, 0xc9cfd0ef);
  (0x1a668, 0xff9fa0ef); (0x1a67c, 0x14000ef); (0x1a76c, 0xaf5fa0ef); (0x1a9d4, 0x9c000ef);
  (0x1a9dc, 0xfffe1517); (0x1a9e0, 0x39453507); (0x1a9e4, 0xdd9ff0ef); (0x1a9f8, 0x140000ef);
  (0x1b34c, 0x40006f); (0x1ba70, 0xac000ef); (0x1bad0, 0x7c000ef); (0x1bb30, 0xfffe1597);
  (0x1bb34, 0x17858593); (0x1c688, 0x3597); (0x1c68c, 0x18058593); (0x1c69c, 0xf20fb06f);
  (0x1c6ac, 0x6697); (0x1c6b0, 0x6706b403); (0x1c6c0, 0x717); (0x1c6c4, 0xad870713);
  (0x1c71c, 0xa7dff0ef); (0x1c73c, 0x8a9fd0ef); (0x1c760, 0x2617); (0x1c764, 0xcd863903);
  (0x1c7a0, 0x618000ef); (0x1c7a4, 0x517); (0x1c7b0, 0x6850513); (0x1c7dc, 0xe80fb0ef);
  (0x1c808, 0xef9f80ef); (0x1c864, 0x150000ef); (0x1c894, 0x120000ef); (0x1c940, 0xfffdf697);
  (0x1c944, 0x4a06b683); (0x1c948, 0xfffdf717); (0x1c94c, 0x48873703); (0x1ceec, 0xfffdf597);
  (0x1cef0, 0xfffdf717); (0x1cef4, 0xebc5b683); (0x1cef8, 0xea873703); (0x1cf60, 0x951ff0ef);
  (0x1cf84, 0x33597); (0x1cf88, 0xdc758683); (0x1cfb4, 0xdc0583a3); (0x1d2a4, 0xfddff06f);
  (0x1d2bc, 0xf4cfa0ef); (0x1d2dc, 0xfbdff0ef); (0x1d2f4, 0xbd0f80ef); (0x1d310, 0xbb4f806f);
  (0x1d338, 0xf61ff0ef); (0x1d344, 0xb80f806f);
  (0x237e0, 159383791); (0x2381c, 798081263); (0x23828, 124183); (0x2382c, 331691267);
  (0x2383c, 4294948119); (0x23840, 4294948247); (0x23844, 2384790803); (0x23848, 3583346067);
  (0x2385c, 3193958511); (0x2388c, 322961647); (0x238b8, 128407); (0x238bc, 314934419);
  (0x238d8, 117448943); (0x238e0, 124183); (0x238e4, 138753283); (0x238f4, 4294948119);
  (0x238f8, 4294948247); (0x238fc, 2191852819); (0x23900, 2791671187); (0x23918, 2996826223);
  (0x23948, 1229017327); (0x2395c, 739258607); (0x23968, 1195462895); (0x2396c, 124183);
  (0x23970, 4286919939); (0x23980, 4294948119); (0x23984, 4294948247); (0x23988, 1173685523);
  (0x2398c, 2644870547); (0x23994, 2866802927); (0x23a14, 124567); (0x23a18, 4110857219);
  (0x23a28, 4294948503); (0x23a2c, 4294948631); (0x23a30, 1239844499); (0x23a34, 3299280659);
  (0x23a50, 2506092783); (0x23a5c, 4294948119); (0x23a60, 4294948247); (0x23a64, 2435122451);
  (0x23a68, 3244656019); (0x23a70, 124183); (0x23a74, 4014290179); (0x23a84, 4294944023);
  (0x23a88, 4294948247); (0x23a8c, 1066730771); (0x23a90, 3202712979); (0x23a98, 124183);
  (0x23a9c, 3972347139); (0x23aac, 4294948119); (0x23ab0, 4294948247); (0x23ab4, 4023715091);
  (0x23ab8, 3160769939); (0x23ad8, 124567); (0x23adc, 3905336323); (0x23aec, 4294948503);
  (0x23af0, 4294948631); (0x23af4, 1034323603); (0x23af8, 3093759763); (0x23b14, 2300571887);
  (0x23b20, 4294948119); (0x23b24, 4294948247); (0x23b28, 372573459); (0x23b2c, 3039135123);
  (0x23b34, 124183); (0x23b38, 3808769283); (0x23b48, 4294944023); (0x23b4c, 4294948247);
  (0x23b50, 1795491091); (0x23b54, 2997192083); (0x23b78, 2359292015); (0x23b88, 124183);
  (0x23b8c, 3720688899); (0x23b9c, 4294944023); (0x23ba0, 4294948247); (0x23ba4, 1265960211);
  (0x23ba8, 2909111699); (0x23bbc, 124183); (0x23bc0, 3666162947); (0x23bd0, 4294948119);
  (0x23bd4, 4294948247); (0x23bd8, 978650387); (0x23bdc, 2854585747); (0x23be8, 124183);
  (0x23bec, 3620025603); (0x23bfc, 4294948119); (0x23c00, 4294948247); (0x23c04, 3896837395);
  (0x23c08, 2808448403); (0x23c0c, 4186960111); (0x23c48, 96555247); (0x23c58, 416284911);
  (0x23c64, 546308335); (0x23c70, 676331759); (0x23c9c, 124183); (0x23ca0, 3431281923);
  (0x23cb0, 4294944023); (0x23cb4, 4294948247); (0x23cb8, 1189414163); (0x23cbc, 2619704723);
  (0x23cf8, 124183); (0x23cfc, 3334812931); (0x23d0c, 4294944023); (0x23d10, 4294948247);
  (0x23d14, 663029011); (0x23d18, 4172645779); (0x23d20, 3843027055); (0x23d7c, 128407);
  (0x23d80, 3339040131); (0x23d90, 79778031); (0x23da4, 1736454383); (0x23db0, 46223599);
  (0x23dc0, 124183); (0x23dc4, 3125097731); (0x23dd4, 4294948119); (0x23dd8, 4294948247);
  (0x23ddc, 593822995); (0x23de0, 2484438419); (0x23df4, 3675254895); (0x23e8c, 124183);
  (0x23e90, 2328179971); (0x23ea0, 4294944023); (0x23ea4, 4294948247); (0x23ea8, 3951363347);
  (0x23eac, 239437203); (0x23eb4, 2836394095); (0x23f04, 1863327983); (0x23f20, 1003495663);
  (0x23f34, 120087); (0x23f38, 1082471683); (0x23f48, 4294944023); (0x23f4c, 4294944151);
  (0x23f50, 2705655059); (0x23f54, 849708435); (0x23f6c, 3722436719); (0x23f70, 120087);
  (0x23f74, 1019557123); (0x23f84, 4294944023); (0x23f88, 4294944151); (0x23f8c, 1872037139);
  (0x23f90, 786793875); (0x23f98, 3676299503); (0x23fd8, 120087); (0x23fdc, 910505219);
  (0x23fec, 4294944023); (0x23ff0, 4294948247); (0x23ff4, 2533688595); (0x23ff8, 2568324499);
  (0x24000, 3567247471); (0x24008, 120215); (0x2400c, 860206467); (0x24020, 4294944023);
  (0x24024, 4294948247); (0x24028, 3976529171); (0x2402c, 2513798547); (0x24034, 3512721519);
  (0x24060, 120087); (0x24064, 767898883); (0x24074, 4294944023); (0x24078, 4294944151);
  (0x2407c, 2391082259); (0x24080, 521504147); (0x24088, 3424641135); (0x24090, 120215);
  (0x24094, 717600131); (0x240a8, 4294944023); (0x240ac, 4294944151); (0x240b0, 1422198035);
  (0x240b4, 466978195); (0x240bc, 3370115183); (0x240e8, 120087); (0x240ec, 625292547);
  (0x240fc, 4294944023); (0x24100, 4294940055); (0x24104, 2248475923); (0x24108, 1999996307);
  (0x24110, 3282034799); (0x24114, 120087); (0x24118, 579155203); (0x24128, 4294944023);
  (0x2412c, 4294940055); (0x24130, 919930131); (0x24134, 1953858963); (0x2413c, 3235897455);
  (0x24160, 120087); (0x24164, 3963958531); (0x24174, 4294939927); (0x24178, 4294944151);
  (0x2417c, 1292174611); (0x24180, 110462355); (0x24188, 2325733487); (0x241ac, 120087);
  (0x241b0, 3179623683); (0x241c0, 4294939927); (0x241c4, 4294940055); (0x241c8, 507839763);
  (0x241cc, 246777235); (0x241d4, 3687833711); (0x241f8, 120087); (0x241fc, 2953131267);
  (0x2420c, 4294939927); (0x24210, 4294940055); (0x24214, 281347347); (0x24218, 293963155);
  (0x24220, 3679445103); (0x24244, 120087); (0x24248, 2793747715); (0x24258, 4294939927);
  (0x2425c, 4294944151); (0x24260, 121963795); (0x24264, 4059399571); (0x2426c, 3301957743);
  (0x242f8, 3968852207); (0x24310, 115991); (0x24314, 4253365507); (0x24328, 4294939927);
  (0x2432c, 4294940055); (0x24330, 3624207635); (0x24334, 4135945619); (0x24338, 2669662447);
  (0x24340, 115991); (0x24344, 4203033859); (0x24354, 4294935831); (0x24358, 4294940055);
  (0x2435c, 1531249939); (0x24360, 4089808275); (0x2437c, 2543833199); (0x2438c, 3297767663);
  (0x24398, 2903498991); (0x243d0, 4294944151); (0x243d4, 2202371859); (0x24544, 3202339055);
  (0x24554, 107799); (0x24558, 2089104643); (0x24568, 4294931735); (0x2456c, 4294931863);
  (0x24570, 1298466067); (0x24574, 4184180115); (0x24580, 107799); (0x24584, 2042967299);
  (0x24594, 4294931735); (0x24598, 4294931863); (0x2459c, 1043662099); (0x245a0, 4138042771);
  (0x245a8, 107799); (0x245ac, 2001024259); (0x245bc, 4294931735); (0x245c0, 4294931863);
  (0x245c4, 3409249555); (0x245c8, 4096099731); (0x245d0, 107799); (0x245d4, 1959081219);
  (0x245e4, 4294935831); (0x245e8, 4294931863); (0x245ec, 2893350163); (0x245f0, 4054156691);
  (0x24610, 2442117231); (0x24634, 107927); (0x24638, 1854256515); (0x24648, 4294935831);
  (0x2464c, 4294931863); (0x24650, 2812609811); (0x24654, 3949299091); (0x24664, 107927);
  (0x24668, 1803924867); (0x24678, 4294931735); (0x2467c, 4294931863); (0x24680, 1392837907);
  (0x24684, 3898967443); (0x2468c, 2366619887); (0x24698, 107799); (0x2469c, 1749366019);
  (0x246b0, 4294931735); (0x246b4, 4294931863); (0x246b8, 3281323283); (0x246bc, 3840247187);
  (0x246c4, 2307899631); (0x246e0, 107927); (0x246e4, 1673901443); (0x246f4, 4294931735);
  (0x246f8, 4294931863); (0x246fc, 1311048979); (0x24700, 3768944019); (0x24718, 107799);
  (0x2471c, 1615148291); (0x24730, 4294931735); (0x24734, 4294931863); (0x24738, 2086995219);
  (0x2473c, 3706029459); (0x24744, 107799); (0x24748, 1569010947); (0x2475c, 4294931735);
  (0x24760, 4294931863); (0x24764, 3471115539); (0x24768, 3659892115); (0x2476c, 4280266991);
  (0x24780, 1691353327); (0x247a4, 107799); (0x247a8, 1468347651); (0x247bc, 4294931735);
  (0x247c0, 4294931863); (0x247c4, 1369769235); (0x247c8, 3559228819); (0x24808, 416354543);
  (0x24810, 407965935); (0x2481c, 107799); (0x24820, 1342518531); (0x24830, 4294935831);
  (0x24834, 4294931863); (0x24838, 3106211091); (0x2483c, 3421865363); (0x24850, 4041191535);
  (0x248b4, 107799); (0x248b8, 2697278723); (0x248c8, 4294927639); (0x248cc, 804586771);
  (0x248d4, 107799); (0x248d8, 2663724291); (0x248e8, 4294931735); (0x248ec, 3217360147);
  (0x24904, 107799); (0x24908, 2613392643); (0x24918, 4294927639); (0x2491c, 2054489363);
  (0x24924, 107799); (0x24928, 2579838211); (0x24938, 4294927639); (0x2493c, 2009400595);
  (0x24940, 4294931863); (0x24944, 3890578835); (0x2497c, 3255808111); (0x249e8, 1100021999);
  (0x24a14, 1053884655); (0x24a24, 107799); (0x24a2c, 2311404675); (0x24a30, 4294931735);
  (0x24a34, 3615820307); (0x24a38, 4294927639); (0x24a3c, 3737455251); (0x24b64, 2525999343);
  (0x24bc0, 3718230255); (0x24be4, 2782900463); (0x24bf0, 3152003311); (0x24c10, 999305455);
  (0x24c28, 103703); (0x24c2c, 1770337539); (0x24c3c, 4294931735); (0x24c40, 4294931863);
  (0x24c44, 4015326483); (0x24c48, 4034233747); (0x24c50, 103703); (0x24c54, 1728394499);
  (0x24c64, 4294927639); (0x24c68, 4294931863); (0x24c6c, 3057976595); (0x24c70, 3992290707);
  (0x24c9c, 2198843503); (0x24e60, 103703); (0x24e64, 1174746371); (0x24e74, 4294927639);
  (0x24e78, 4294931863); (0x24e7c, 630523155); (0x24e80, 3438642579); (0x24e88, 3831472367);
  (0x24f14, 2211418351); (0x24f20, 3961487599); (0x24f34, 3156181231); (0x24f40, 3772739823);
  (0x24f4c, 4141842671); (0x25020, 91415); (0x25024, 2596615427); (0x25034, 4294915351);
  (0x25038, 4294915479); (0x2503c, 2442462483); (0x25040, 468026771); (0x25048, 91543);
  (0x2504c, 2554705283); (0x2505c, 4294911255); (0x25060, 4294915479); (0x25064, 4177855763);
  (0x25068, 426083731); (0x2508c, 3033493615); (0x25170, 54551); (0x25174, 1090860291);
  (0x25184, 4294878487); (0x25188, 4294878743); (0x2518c, 1186268435); (0x25190, 581306003);
  (0x2519c, 3797868783); (0x251a4, 54551); (0x251a8, 1036334339); (0x251b8, 4294878487);
  (0x251bc, 4294878615); (0x251c0, 1589970195); (0x251c4, 526747027); (0x25278, 54551);
  (0x2527c, 814036227); (0x2528c, 4294882583); (0x25290, 4294878615); (0x25294, 2363819283);
  (0x25298, 304448915); (0x252a0, 54551); (0x252a4, 772093187); (0x252b4, 4294878487);
  (0x252b8, 4294878615); (0x252bc, 904201491); (0x252c0, 262505875); (0x252f0, 3604930671);
  (0x25300, 54551); (0x25304, 671429891); (0x25314, 4294878487); (0x25318, 4294878615);
  (0x2531c, 2495939859); (0x25320, 161842579); (0x25338, 54551); (0x2533c, 612709635);
  (0x2534c, 4294878487); (0x25350, 4294878615); (0x25354, 2187658515); (0x25358, 103122323);
  (0x25390, 2765025519); (0x253a0, 3591303407); (0x253e4, 3599692015); (0x253fc, 4284408047);
  (0x25424, 4035916015); (0x25438, 3449745647); (0x25444, 3499028719); (0x25448, 54551);
  (0x2544c, 327496963); (0x2545c, 4294878487); (0x25460, 4294878615); (0x25464, 1351943443);
  (0x25468, 4112876947); (0x25470, 54551); (0x25474, 285553923); (0x25484, 4294878487);
  (0x25488, 4294878615); (0x2548c, 671417619); (0x25490, 4070933907); (0x25498, 54551);
  (0x2549c, 243610883); (0x254ac, 4294878487); (0x254b0, 4294878615); (0x254b4, 3165979923);
  (0x254b8, 4028990867); (0x254c0, 54551); (0x254c4, 201667843); (0x254d4, 4294878487);
  (0x254d8, 4294878615); (0x254dc, 3561293075); (0x254e0, 3987047827); (0x254f0, 2904482031);
  (0x254f8, 54551); (0x254fc, 142947587); (0x2550c, 4294878487); (0x25510, 4294878615);
  (0x25514, 818218259); (0x25518, 3928327571); (0x2552c, 3255759087); (0x25530, 54551);
  (0x25534, 84227331); (0x25544, 4294882583); (0x25548, 4294878615); (0x2554c, 2458191123);
  (0x25550, 3869607315); (0x2555c, 3507421423); (0x2558c, 1509994735); (0x255a0, 4161741039);
  (0x255b8, 3108958447); (0x255bc, 54551); (0x255c0, 4232393987); (0x255d0, 4294874391);
  (0x255d4, 4294878615); (0x255d8, 2121598227); (0x255dc, 3722806675); (0x255e4, 2812207343)].

Definition v10_reloc : Reloc := {|
  rl_segs := Ubsan.M.loaded_segments;
  rl_dtab := v10_dtab;
  rl_stab := v10_stab;
  rl_img_lo := 0x10000; rl_rw_lo := 0x33000; rl_img_hi := 0x66000;
  rl_dtab_ok := eq_refl |}.
End V10Reloc.

From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require StartupTac.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require ArgvEnv.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require RefLayout.
Module V10StartupDefs.
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
Import OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images.Ubsan.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StartupTac.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ArgvEnv.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefLayout.
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
      (Z_to_bv 64 0x656e8) (word_to_le_bytes 4 (v_lw rwa)))
      (Z_to_bv 64 0x656ec) (word_to_le_bytes 4 (v_lw rwb)))
      (Z_to_bv 64 0x656e9) [Z_to_bv 8 0]) (Z_to_bv 64 0x656e8) 8 = Some guard_bytes.
  Proof.
    intros segs D. unfold guard_bytes.
    set (A := word_to_le_bytes 4 (v_lw rwa)). set (B := word_to_le_bytes 4 (v_lw rwb)).
    assert (HA : length A = 4%nat) by (subst A; apply length_N_to_le_bytes).
    assert (HB : length B = 4%nat) by (subst B; apply length_N_to_le_bytes).
    assert (Hin : rdn segs (wbytes D (Z_to_bv 64 0x656e8) A) (Z_to_bv 64 0x656e8) 4 = Some A).
    { rewrite <- HA at 1. apply rdn_wbytes_hit. rewrite HA. unorm. lia. }
    change 8%nat with (1 + (1 + (2 + 4)))%nat.
    apply rdn_app.
    { rewrite rdn_wbytes_out by (cbn [length]; unorm; lia).
      rewrite rdn_wbytes_out by (rewrite ?HB; unorm; lia).
      exact (SeqExec.rdn_firstn _ _ _ _ _ 1 Hin ltac:(lia)). }
    apply rdn_app.
    { change (Z_to_bv 64 415464 + nat_to_word 1) with (Z_to_bv 64 0x656e9 : word).
      exact (rdn_wbytes_hit segs [Z_to_bv 8 0] _ (Z_to_bv 64 0x656e9) ltac:(cbn [length]; unorm; lia)). }
    apply rdn_app.
    { change (Z_to_bv 64 415464 + nat_to_word 1 + nat_to_word 1) with (Z_to_bv 64 0x656ea : word).
      rewrite rdn_wbytes_out by (cbn [length]; unorm; lia).
      rewrite rdn_wbytes_out by (rewrite ?HB; unorm; lia).
      exact (SeqExec.rdn_skipn _ _ _ _ _ 2 Hin ltac:(lia)). }
    change (Z_to_bv 64 415464 + nat_to_word 1 + nat_to_word 1 + nat_to_word 2) with (Z_to_bv 64 0x656ec : word).
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
      (Z_to_bv 64 0x453b0) (word_to_le_bytes 8 envp_w))          (* [comment removed for export] *)
      (Z_to_bv 64 0x65710) (word_to_le_bytes 8 auxv_w))          (* [comment removed for export] *)
      (Z_to_bv 64 0x65770) (word_to_le_bytes 8 hw))            (* [comment removed for export] *)
      (Z_to_bv 64 0x65738) (word_to_le_bytes 8 (Z_to_bv 64 4096))) (* [comment removed for export] *)
      (Z_to_bv 64 0x65700) (word_to_le_bytes 8 pn_w))            (* [comment removed for export] *)
      (Z_to_bv 64 0x656f8) (word_to_le_bytes 8 progname_w).      (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition J_lsm (J : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes
    (wbytes (wbytes (wbytes (wbytes J
      (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0x2a964)))
      (Z_to_bv 64 (bv_unsigned sp0 - 48)) (word_to_le_bytes 8 argv_w))
      (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 argc_w))
      (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0x1520c)).

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
      (Z_to_bv 64 0x654a8) (word_to_le_bytes 8 (Z_to_bv 64 0)))        (* [comment removed for export] *)
      (Z_to_bv 64 0x654b8) (word_to_le_bytes 8 (Z_to_bv 64 0)))        (* [comment removed for export] *)
      (Z_to_bv 64 0x654b0) (word_to_le_bytes 8 (Z_to_bv 64 8)))        (* [comment removed for export] *)
      (Z_to_bv 64 0x65720) (word_to_le_bytes 8 (Z_to_bv 64 0xe0)))     (* [comment removed for export] *)
      (Z_to_bv 64 0x65728) (word_to_le_bytes 8 (Z_to_bv 64 8)))        (* [comment removed for export] *)
      (Z_to_bv 64 0x45490) (word_to_le_bytes 8 (Z_to_bv 64 0)))        (* [comment removed for export] *)
      (Z_to_bv 64 0x45478) (word_to_le_bytes 8 (Z_to_bv 64 0x45490)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x453b8) (word_to_le_bytes 8 (Z_to_bv 64 0x453b8)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x65708) [Z_to_bv 8 1])                              (* [comment removed for export] *)
      (Z_to_bv 64 0x453e0) (word_to_le_bytes 4 (Z_to_bv 64 2)).        (* [comment removed for export] *)

  Definition D_tlsB (tid : word) (D : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes D
      (Z_to_bv 64 0x453d8) (word_to_le_bytes 4 tid))                   (* [comment removed for export] *)
      (Z_to_bv 64 0x45450) (word_to_le_bytes 8 (Z_to_bv 64 0x65740)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x45430) (word_to_le_bytes 8 (Z_to_bv 64 0x45430)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x453c0) (word_to_le_bytes 8 (Z_to_bv 64 0x453b8)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x453c8) (word_to_le_bytes 8 (Z_to_bv 64 0x453b8)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x453d0) (word_to_le_bytes 8 (Z_to_bv 64 0)).        (* [comment removed for export] *)

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
      (Z_to_bv 64 0x656e8) (word_to_le_bytes 4 (v_lw (rwa drw))))  (* [comment removed for export] *)
      (Z_to_bv 64 0x656ec) (word_to_le_bytes 4 (v_lw (rwb drw))))  (* [comment removed for export] *)
      (Z_to_bv 64 0x656e9) [Z_to_bv 8 0])                     (* [comment removed for export] *)
      (Z_to_bv 64 0x45470) (word_to_le_bytes 8 (canary_w drw)).     (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition D_fd (D : word -> option byte) : word -> option byte :=
    wbytes D (Z_to_bv 64 0x35330) [Z_to_bv 8 1].

  (* [comment removed for export] *)
  Definition D_main (tid : word) : word -> option byte := D_fd (D_ssp (D_tls tid D_libc)).

End Defs.
End V10StartupDefs.

From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Musl Require PFSpec.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.VL Require LeptStderr.
Module V10LeptEnv.
Import Stdlib.ZArith.ZArith.
Import Stdlib.Lists.List.
Import Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.Reloc.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.VL.LeptStderr.
Import V10Reloc.
(* [comment removed for export] *)







Lemma v10_lenv_ok1 : @PFSpec.ls_ok1 v10_reloc (@LG v10_reloc) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma v10_lenv_ok2 : @PFSpec.ls_ok2 v10_reloc (@LG v10_reloc) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition v10_lenv_vl : RelocLeptEnvVL v10_reloc := {| rl_lenv_ok1 := v10_lenv_ok1; rl_lenv_ok2 := v10_lenv_ok2 |}.
End V10LeptEnv.

From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require CatSim.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require SeqExec.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require StepTac.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require WalkTac.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require MmapSim.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require RefMemcpyLib.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Musl Require MemcpyBase.
Module V10MemcpyBase.
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
Import OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images.Ubsan.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SeqExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StepTac.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Hoare.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StoreOk.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.WalkTac.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.MmapSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefMemcpyLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.Reloc.
Import V10Reloc.
(* [comment removed for export] *)








Import ListNotations.
Open Scope bv_scope.

Abbreviation RSEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)
Abbreviation mcH := (@MemcpyBase.mcH v10_reloc).
Abbreviation MCH := (@MemcpyBase.MCH v10_reloc).

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
End V10MemcpyBase.

From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc Require RelocCode.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc Require CanonCode.
Module V10RelocCode.
Import Stdlib.ZArith.ZArith.
Import Stdlib.Lists.List.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.Reloc.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.RelocCode.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.CanonCode.
Import V10Reloc.
(* [comment removed for export] *)





Lemma v10_code_ok : code_check (@rl_segs v10_reloc) (@rl_delta v10_reloc) canon_code = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Definition v10_code : RelocCode v10_reloc := {| rl_code_ok := v10_code_ok |}.
End V10RelocCode.

From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require StreamSim.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc Require RelocImg.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc Require CanonImg.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc Require RelocSpan.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc Require CanonSpans.
Module V10RelocImg.
Import Stdlib.ZArith.ZArith.
Import Stdlib.Lists.List.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StreamSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.Reloc.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.RelocImg.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.CanonImg.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.RelocSpan.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.CanonSpans.
Import V10Reloc.
(* [comment removed for export] *)





Local Open Scope Z_scope.

Lemma v10_cells_ok : @cells_check v10_reloc canon_cells = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Definition v10_img : RelocImg v10_reloc := {| rl_cells_ok := v10_cells_ok |}.

Lemma v10_data_wseg : wseg_ok (@rl_segs v10_reloc) (Z_to_bv 64 0x34000) (Z.to_nat (@rl_img_hi v10_reloc - 0x34000)) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma v10_data_ok : (0 <=? 0x34000) && (0x34000 <=? @rl_img_hi v10_reloc) && (@rl_img_hi v10_reloc <=? 2^32) = true.
Proof. reflexivity. Qed.

Definition v10_data : RelocData v10_reloc := {| rl_data_lo := 0x34000; rl_data_ok := v10_data_ok; rl_data_wseg := v10_data_wseg |}.

Lemma v10_hull_ok : @hull_okb v10_reloc v10_data = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma v10_spans_ok : @spans_check v10_reloc v10_data canon_spans = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma v10_orders_ok : @orders_check v10_reloc canon_spans canon_order = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition v10_spans : RelocSpans v10_reloc v10_data := {| rl_hull_ok := v10_hull_ok; rl_spans_ok := v10_spans_ok; rl_orders_ok := v10_orders_ok |}.
End V10RelocImg.

From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require RelocLayout.
Module V10RelocML.
Import Stdlib.ZArith.ZArith.
Import Stdlib.NArith.NArith.
Import Stdlib.Lists.List.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.MallocLayout.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.RelocLayout.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.Reloc.
Import V10MallocLayout.
Import V10Reloc.
(* [comment removed for export] *)







Lemma lv10_reloc : LU16 = reloc_layout v10_reloc.
Proof. unfold LU16, reloc_layout. f_equal; first [ reflexivity | apply bv_eq; reflexivity ]. Qed.

(* [comment removed for export] *)
Ltac v10_ml_tail t := rewrite lv10_reloc; exact t.
End V10RelocML.

From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc Require RelocSites.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc Require CanonSites.
Module V10RelocSites.
Import Stdlib.ZArith.ZArith.
Import Stdlib.Lists.List.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.Reloc.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.RelocCode.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.RelocSites.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.CanonSites.
Import V10Reloc.
(* [comment removed for export] *)





Lemma v10_sites_ok : @sites_check v10_reloc canon_sites = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Definition v10_sites : RelocSites v10_reloc := {| rl_sites_ok := v10_sites_ok |}.
End V10RelocSites.

From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc Require CanonCodeVL.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc Require CanonSitesVL.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc Require CanonImgVL.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require RelocLept.
Module V10RelocVL.
Import Stdlib.ZArith.ZArith.
Import Stdlib.Lists.List.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.Reloc.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.RelocCode.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.RelocSites.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.RelocImg.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.CanonCodeVL.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.CanonSitesVL.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.CanonImgVL.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.RelocLept.
Import V10Reloc.
(* [comment removed for export] *)






Lemma v10_code_vl_ok : code_check (@rl_segs v10_reloc) (@rl_delta v10_reloc) canon_code_VL = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition v10_code_vl : RelocCodeVL v10_reloc := {| rl_code_vl_ok := v10_code_vl_ok |}.

Lemma v10_sites_vl_ok : @sites_check v10_reloc canon_sites_VL = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition v10_sites_vl : RelocSitesVL v10_reloc := {| rl_sites_vl_ok := v10_sites_vl_ok |}.

Lemma v10_lept_ok : wr_readable_chk (@rl_segs v10_reloc) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition v10_lept : RelocLept v10_reloc := {| rl_wr_readable_ok := v10_lept_ok; rl_pages_ok := eq_refl; rl_clr_extra := (cons (0x34e20%Z, 0x35140%Z) nil) |}.

Lemma v10_strs_vl_ok : @strs_check v10_reloc canon_strs_VL = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma v10_cells_vl_ok : @cells_check v10_reloc canon_cells_VL = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma v10_spans_vl_ok : @RelocLept.spans_check v10_reloc canon_spans_VL = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition v10_img_vl : RelocImgVL v10_reloc := {| rl_strs_vl_ok := v10_strs_vl_ok; rl_cells_vl_ok := v10_cells_vl_ok; rl_spans_vl_ok := v10_spans_vl_ok |}.
End V10RelocVL.

From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require ExitSim.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require ShapeAlg.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require Nodes.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require LibAtomic.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require SumWalkTac.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require RefNodes.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Musl Require ExitBase.
Module V10ExitBase.
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
Import OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images.Ubsan.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Import LinuxProcessSemantics.LinuxProcessSem.Fs.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.LinuxProcessSem.Monad.
Import LinuxProcessSemantics.LinuxProcessSem.Specs.
Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SeqExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StepTac.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Hoare.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.WalkTac.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StoreOk.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StreamSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.MmapSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ExitSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ShapeAlg.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Nodes.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.LibAtomic.
Export OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.SumWalkTac.
Export OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefNodes.
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
  Context {fx : FPState}.
Lemma store_ok_data : forall m (a : word) n,
  (0x34000 <= bv_unsigned a)%Z -> (bv_unsigned a + Z.of_nat n <= 0x66000)%Z ->
  store_ok RSEGS m a n = true.
Proof.
  exact (@ExitBase.store_ok_data V10Reloc.v10_reloc V10RelocImg.v10_data).
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
  rdn RSEGS mem (Z_to_bv 64 0x6570b) 1%nat = Some [Z_to_bv 8 0]            (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0x65b38) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))       (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0x65b28) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))       (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0x35318) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x35230)) (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0x35228) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x35140)). (* [comment removed for export] *)

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End V10ExitBase.

From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require MuslStrlen.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require PortLib.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Musl Require Memchr.
Module V10Memchr.
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
Import OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images.Ubsan.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SeqExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StepTac.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Hoare.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StoreOk.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.WalkTac.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.MmapSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.MuslStrlen.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefMemcpyLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.PortLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.Reloc.
Import V10Reloc.
Import V10MemcpyBase.
(* [comment removed for export] *)










Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition rodata_clear (mem : word -> option byte) : Prop :=
  forall i, (0x11758 <= i < 0x11770)%Z -> mem (Z_to_bv 64 i) = None.

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
Lemma mchrH_generic : forall mem s buf K n, mchrH mem s buf K n -> @Memchr.mchrH v10_reloc mem s buf K n.
Proof.
  intros mem s buf K n [H1 H2 H3 H4 H5 H6 H7 H8 H9].
  exact (@Memchr.MCHRH v10_reloc mem s buf K n H1 H2 H3 H4 H5 H6 H7 H8
           (@Memchr.rodata_clear_hull v10_reloc mem 0x11758 0x11770 eq_refl H9)).      (* [comment removed for export] *)
Qed.
End V10Memchr.

From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Musl Require Memcpy.
Module V10Memcpy.
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
Import OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images.Ubsan.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SeqExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StepTac.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Hoare.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StoreOk.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.WalkTac.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.MmapSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefMemcpyLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.Reloc.
Import V10Reloc.
Import V10RelocCode.
Import V10MemcpyBase.
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
      msteps RSEGS (mkst regs (0x3233c : word) mem0 rom) (mkst regs' ret (wbytes mem0 dst bs) rom)
      /\ keeps regs regs'.
  Proof. rl_tail (@Memcpy.ref_memcpy fx v10_reloc v10_code). Qed.
End Contract.
End V10Memcpy.

From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require PureModel.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require SumWalkTac.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require WalksLib.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Musl Require Memset.
Module V10Memset.
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
Import OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images.Ubsan.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StartupTac.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefMemcpyLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ShapeAlg.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PureModel.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.SumWalkTac.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.WalksLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.Reloc.
Import V10Reloc.
Import V10RelocCode.
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
      msteps SEGS (mkst regs (0x32740 : word) M rom) (mkst regs' ret (zf M d [(0, n)]%Z) rom)
      /\ getr regs' 10 = Z_to_bv 64 d
      /\ regs_agree (fun r => In r memset_clob) regs regs'.
  Proof. rl_tail (@Memset.memset_spec fx v10_reloc v10_code). Qed.

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
    realizes SEGS (mkCfg (mkst regs (0x32740 : word) M rom) model) S.
  Proof. rl_tail (@Memset.memset_at fx v10_reloc v10_code). Qed.
End Contract.
End V10Memset.

From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require RefStmts.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require RRef_calloc.
Module V10Ref_calloc.
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
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.MallocLayout.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.RefStmts.
Import V10MallocLayout.
Import V10Reloc.
Import V10RelocCode.
Import V10RelocSites.
Import V10RelocML.
(* [comment removed for export] *)







Section Calloc.
Context {fx : FPState}.

Theorem calloc_refines : calloc_stmt.
Proof. v10_ml_tail (@RRef_calloc.calloc_refines fx v10_reloc v10_code v10_sites). Qed.
End Calloc.
End V10Ref_calloc.

From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require RRef_free.
Module V10Ref_free.
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
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.MallocLayout.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.RefStmts.
Import V10MallocLayout.
Import V10Reloc.
Import V10RelocCode.
Import V10RelocSites.
Import V10RelocML.
(* [comment removed for export] *)







Section Free.
Context {fx : FPState}.

Theorem free_refines : free_stmt.
Proof. v10_ml_tail (@RRef_free.free_refines fx v10_reloc v10_code v10_sites). Qed.
End Free.
End V10Ref_free.

From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require RRef_malloc.
Module V10Ref_malloc.
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
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.MallocLayout.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.RefStmts.
Import V10MallocLayout.
Import V10Reloc.
Import V10RelocCode.
Import V10RelocSites.
Import V10RelocML.
(* [comment removed for export] *)







Section Malloc.
Context {fx : FPState}.

Theorem malloc_refines : malloc_stmt.
Proof. v10_ml_tail (@RRef_malloc.malloc_refines fx v10_reloc v10_code v10_sites). Qed.
End Malloc.
End V10Ref_malloc.

From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require PFLib.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc Require RelocBlocks.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Musl Require RelocRW.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Musl Require RelocPF.
Module V10RelocMusl.
Import Stdlib.ZArith.ZArith.
Import Stdlib.Lists.List.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.PFLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.Reloc.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.RelocBlocks.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.RelocImg.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.RelocSpan.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.CanonSpans.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Musl.RelocRW.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Musl.RelocPF.
Import V10Reloc.
Import V10RelocImg.
(* [comment removed for export] *)






Local Open Scope Z_scope.

Lemma v10_dwin_bounds : @dwin_bounds_chk v10_reloc v10_data = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition v10_rw : RelocRW v10_reloc v10_data := {| rl_dwin_bounds := v10_dwin_bounds; rl_rw_hull := v10_hull_ok; rl_rw_spans := v10_spans_ok; rl_rw_orders := v10_orders_ok |}.

Lemma v10_segs_lo : segs_lo (@rl_segs v10_reloc) = @rl_img_lo v10_reloc.
Proof. vm_cast_no_check (@eq_refl Z (@rl_img_lo v10_reloc)). Qed.
Lemma v10_segs_hi : segs_hi (@rl_segs v10_reloc) = @rl_img_hi v10_reloc.
Proof. vm_cast_no_check (@eq_refl Z (@rl_img_hi v10_reloc)). Qed.
Lemma v10_pf_bounds : @pf_bounds_chk v10_reloc = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma v10_pf_prefix : pf_prefix_ok (@rl_segs v10_reloc) (0x102e7 + @rl_delta v10_reloc B_S_102e7) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition v10_pf : RelocPF v10_reloc :=
  {| rl_segs_lo_val := v10_segs_lo; rl_segs_hi_val := v10_segs_hi; rl_pf_bounds := v10_pf_bounds; rl_pf_prefix := v10_pf_prefix |}.
End V10RelocMusl.

From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Musl Require RelocStart.
Module V10RelocStart.
Import Stdlib.ZArith.ZArith.
Import Stdlib.Lists.List.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.Reloc.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.RelocBlocks.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.RelocImg.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Musl.RelocStart.
Import V10Reloc.
Import V10RelocImg.
(* [comment removed for export] *)





Local Open Scope Z_scope.

Lemma v10_start_ok : start_ok (@rl_delta v10_reloc 8%positive) (@rl_data_lo v10_reloc v10_data) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition v10_start : RelocStart v10_reloc v10_data := {| rl_start_ok := v10_start_ok |}.
End V10RelocStart.

From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require VmLedger.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require AllocIface.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require MallocTree.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require MallocOps.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require MallocIface.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require MallocInv_defs.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require MallocIfaceX.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require MallocInv_aslot_iface.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require MallocInv_malloc_iface.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require MallocInv_aslot.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require MallocInv_mal6.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require MallocInv_calloc2.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require MallocInv_freetopX.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require AllocBase.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require AllocCalloc.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require MallocAllocLayout.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require MallocGlue.
Module V10Alloc.
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
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Hoare.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ShapeAlg.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PureModel.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.VmLedger.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AllocIface.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.MallocLayout.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.MallocTree.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.MallocOps.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.MallocIface.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.MallocInv_defs.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.MallocIfaceX.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.MallocInv_aslot_iface.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.MallocInv_malloc_iface.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.MallocInv_aslot.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.MallocInv_mal6.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.MallocInv_calloc2.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.MallocInv_freetopX.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocBase.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.MallocAllocLayout.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.MallocGlue.
Import V10MallocLayout.
Import V10Ref_malloc.
Import V10Ref_free.
Import V10Ref_calloc.
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
End V10Alloc.

From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require SumSpecs.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require PFSpecLib.
Module V10PFSpec.
Import Stdlib.ZArith.ZArith.
Import Stdlib.Lists.List.
Import Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images.Ubsan.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.SumSpecs.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.PFLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.PFSpecLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.Reloc.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.RelocCode.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.RelocSites.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.RelocImg.
Import V10Reloc.
Import V10RelocCode.
Import V10RelocSites.
Import V10RelocImg.
Import V10RelocMusl.
Import V10PFBase.
(* [comment removed for export] *)








Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition ls_ok (nS : nat) (fmts : list Z) (L : SSP.ls_addrs) : bool := @PFSpec.ls_ok v10_reloc nS fmts L.
Definition ls_ok1 (L : SSP.ls_addrs) : bool := ls_ok 1 (SSP.ls_fmts1 L) L.
Definition ls_ok2 (L : SSP.ls_addrs) : bool := ls_ok 2 (SSP.ls_fmts2 L) L.

Section Contracts.
Context {fx : FPState}.
#[local] Existing Instance v10_reloc.
#[local] Existing Instance v10_code.
#[local] Existing Instance v10_sites.
#[local] Existing Instance v10_data.
#[local] Existing Instance v10_img.
#[local] Existing Instance v10_rw.
#[local] Existing Instance v10_pf.

(* [comment removed for export] *)
Theorem lept_stderr_s1_contract : forall L, ls_ok1 L = true -> SSP.sum_contract SEGS (SSP.spec_lept_stderr_s1 L).
Proof. exact PFSpec.lept_stderr_s1_contract. Qed.

(* [comment removed for export] *)
Theorem lept_stderr_s2_contract : forall L, ls_ok2 L = true -> SSP.sum_contract SEGS (SSP.spec_lept_stderr_s2 L).
Proof. exact PFSpec.lept_stderr_s2_contract. Qed.
End Contracts.
End V10PFSpec.

From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver Require Amb.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require RefNodesMF.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Musl Require StartupBase.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Musl Require StartupDefs.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Musl Require Startup.
Module V10Startup.
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
Import OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images.Ubsan.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.Amb.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ShapeAlg.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PureModel.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefNodesMF.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StartupTac.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ArgvEnv.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefLayout.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.Reloc.
Import V10StartupDefs.
Import V10Reloc.
Import V10RelocCode.
Import V10RelocSites.
Import V10RelocImg.
Import V10RelocMusl.
Import V10RelocStart.
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
              (Z_to_bv 64 0x2a7c8) (pn_w sp0 av ev) s1v (Z_to_bv 64 0x65708)
              (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) in
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes J6
    (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 0x2a7d0)))   (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))           (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))          (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)))          (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0)))          (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0)))          (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 0x2a9c4)))    (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (argv_w sp0)))             (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av)))              (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 0x2a914)))    (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 96)) (word_to_le_bytes 8 (Z_to_bv 64 0x33d20)).    (* [comment removed for export] *)

(* [comment removed for export] *)
Record main_entry {AMB : Amb} (sp0 : word) (av ev : list (list byte)) (tid : word)
       (regs : bvmap 5 word) (mem : word -> option byte) : Prop := {
  me_ra  : getr regs 1 = Z_to_bv 64 0x2a9d4;
  me_sp  : getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 48);
  me_gp  : getr regs 3 = Z_to_bv 64 0x10800;
  me_tp  : getr regs 4 = Z_to_bv 64 0x45480;
  me_s0  : getr regs 8 = Z_to_bv 64 (bv_unsigned sp0 + 8);
  me_s1  : getr regs 9 = argcN av;
  me_a0  : getr regs 10 = argcN av;
  me_a1  : getr regs 11 = Z_to_bv 64 (bv_unsigned sp0 + 8);
  me_a2  : getr regs 12 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av));
  me_s2  : getr regs 18 = Z_to_bv 64 0x1520c;
  me_s3  : getr regs 19 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av));
  me_szero : forall r : reg, In r [20; 21; 22; 23; 24; 25; 26; 27]%list -> getr regs r = Z_to_bv 64 0;
  me_mem : exists (J : word -> option byte) (s1v : word),
             wfJ sp0 J /\ J = J_main sp0 av ev s1v
             /\ mem = cmem sp0 (wrap_mem RPH sp0 av ev a_uid a_hwcap a_draw) J (D_main sp0 av ev a_hwcap a_draw tid)
}.

(* [comment removed for export] *)
Lemma main_entry_L : forall {AMB : Amb} sp0 av ev tid regs mem,
  @Startup.main_entry v10_reloc AMB sp0 av ev tid regs mem -> main_entry sp0 av ev tid regs mem.
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
       realizes rsegs (mkCfg (mkst (fx:=fx0) regs (0x1520c : word) mem (seg_rom rsegs))
                             (with_tid tid (init_model (segments_reserved rsegs) brk mbase sp lim
                                                      (mkProcInputC argv envp fs0 stdin0)))) K) ->
    realizes rsegs (init_config rsegs rpc rph sp brk mbase a_draw lim (mkProcInputC argv envp fs0 stdin0)) K.
  Proof.
    intros brk mbase lim fs0 stdin0 K HK.
    refine (@Startup.ref_startup_sec v10_reloc v10_code v10_sites v10_img v10_data v10_rw v10_start AMB sp argv envp Hva Hve Hvsp
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
     realizes rsegs (mkCfg (mkst (fx:=fx0) regs (0x1520c : word) mem (seg_rom rsegs))
                           (with_tid tid (init_model (segments_reserved rsegs) brk mbase sp lim inp))) K) ->
  realizes rsegs (init_config rsegs rpc rph sp brk mbase draw lim inp) K.
Proof.
  intros sp brk mbase draw lim inp K Hsp Hva Hve HK.
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
End V10Startup.

Module V10StdioDefs.
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
Import OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images.Ubsan.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SeqExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StepTac.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Hoare.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.WalkTac.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StoreOk.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StreamSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.MmapSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ExitSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ShapeAlg.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Nodes.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.SumWalkTac.
Export V10ExitBase.
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
  rdn RSEGS mem (Z_to_bv 64 0x33dc0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x656e8))
  /\ rdn RSEGS mem (Z_to_bv 64 0x656e8) 8%nat = Some (word_to_le_bytes 8 can).

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
  Context {fx : FPState}.
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
  Context {fx : FPState}.
Lemma sw_post_store_ok : forall mem su f bufp bufsz mem' (a : word) n,
  sw_post mem su f bufp bufsz mem' ->
  store_ok RSEGS mem a n = true -> store_ok RSEGS mem' a n = true.
Proof. intros mem su f bufp bufsz mem' a n P H. eapply store_ok_mono; [apply (swp_grows _ _ _ _ _ _ P) | exact H]. Qed.
End VP2.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition atexit_none (mem : word -> option byte) : Prop :=
  rdn RSEGS mem (Z_to_bv 64 0x654d0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).

Definition atexit_one (mem : word -> option byte) : Prop :=
  rdn RSEGS mem (Z_to_bv 64 0x654d0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x654d8))
  /\ rdn RSEGS mem (Z_to_bv 64 0x654c8) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1))
  /\ rdn RSEGS mem (Z_to_bv 64 0x654d8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
  /\ rdn RSEGS mem (Z_to_bv 64 0x654e0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x2ae7c))
  /\ rdn RSEGS mem (Z_to_bv 64 0x655e0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x15634))
  /\ rdn RSEGS mem (Z_to_bv 64 0x45384) 1%nat = Some [Z_to_bv 8 0].

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
  ec_lock : rdn RSEGS mem (Z_to_bv 64 0x656e0) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0));
  (* [comment removed for export] *)
  ec_fe   : rdn RSEGS mem (Z_to_bv 64 0x33dc8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x33d28));
  ec_fs   : rdn RSEGS mem (Z_to_bv 64 0x33dd0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x33d20));
  ec_fa   : rdn RSEGS mem (Z_to_bv 64 0x33d20) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1517c));
  (* [comment removed for export] *)
  ec_comp : rdn RSEGS mem (Z_to_bv 64 0x35378) 1%nat = Some [Z_to_bv 8 0];
  ec_g1   : rdn RSEGS mem (Z_to_bv 64 0x33d68) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x2adb4));
  ec_g2   : rdn RSEGS mem (Z_to_bv 64 0x33d70) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
  (* [comment removed for export] *)
  ec_glob : stdio_globals mem;
  (* [comment removed for export] *)
  ec_err  : file_clean mem 0x35140 wp2 rp2;
  ec_dso  : rdn RSEGS mem (Z_to_bv 64 0x34dd8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x34dd8));
  ec_alock : rdn RSEGS mem (Z_to_bv 64 0x654c4) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0));
  ec_atexit : atexit_state mem
}.

(* [comment removed for export] *)
Record stdout_pending (mem : word -> option byte) (wb wp : Z) (bufp bufsz rp1 can : word)
       (pending : list byte) : Prop := {
  sp_lock  : rdn RSEGS mem (Z_to_bv 64 (0x35230 + 140)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295));
  sp_wpos  : rdn RSEGS mem (Z_to_bv 64 (0x35230 + 40)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wp));
  sp_wbase : rdn RSEGS mem (Z_to_bv 64 (0x35230 + 56)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wb));
  sp_write : rdn RSEGS mem (Z_to_bv 64 (0x35230 + 72)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x2d23c));
  sp_buf   : rdn RSEGS mem (Z_to_bv 64 (0x35230 + 88)) 8%nat = Some (word_to_le_bytes 8 bufp);
  sp_bsz   : rdn RSEGS mem (Z_to_bv 64 (0x35230 + 96)) 8%nat = Some (word_to_le_bytes 8 bufsz);
  sp_fd    : rdn RSEGS mem (Z_to_bv 64 (0x35230 + 120)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1));
  sp_rpos  : rdn RSEGS mem (Z_to_bv 64 (0x35230 + 8)) 8%nat = Some (word_to_le_bytes 8 rp1);
  sp_rend  : rdn RSEGS mem (Z_to_bv 64 (0x35230 + 16)) 8%nat = Some (word_to_le_bytes 8 rp1);
  sp_range : (0x656f0 <= wb < wp /\ wp <= 0x66000)%Z;
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
    /\ ( (pending = [] /\ exists wp1 rp1, file_clean mem 0x35230 wp1 rp1)
       \/ (exists (wb wp : Z) (bufp bufsz rp1 can : word),
              stdout_pending mem wb wp bufp bufsz rp1 can pending
              /\ fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1))) ).

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End V10StdioDefs.

From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require Frame.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Musl Require Strnlen.
Module V10Strnlen.
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
Import OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images.Ubsan.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SeqExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StepTac.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Hoare.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StoreOk.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.WalkTac.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.MmapSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefMemcpyLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.PortLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.Frame.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.Reloc.
Import V10Reloc.
Import V10RelocCode.
Import V10RelocSites.
Import V10RelocImg.
Import V10MemcpyBase.
Import V10Memchr.
(* [comment removed for export] *)










Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section VP1. Context {fx : FPState}.
Theorem ref_strnlen : forall mem (s sp : word) buf K n rom regs (ret : word),
  mchrH mem s buf K n ->
  (0 < bv_unsigned s + K)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 32)) 32 = true ->
  (0x11770 <= bv_unsigned sp - 32)%Z ->
  (bv_unsigned s + Z.of_nat (length buf) <= bv_unsigned sp - 32 \/ bv_unsigned sp <= bv_unsigned s)%Z ->
  ret_ok ret -> getr regs 1 = ret -> getr regs 2 = sp ->
  getr regs 10 = s -> getr regs 11 = Z_to_bv 64 n ->
  exists regs' mem',
    msteps RSEGS (mkst regs (0x32900 : word) mem rom) (mkst regs' ret mem' rom)
    /\ keeps_cs regs regs'
    /\ getr regs' 10 = Z_to_bv 64 K
    /\ frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - 32), 32%Z)].
Proof.
  rl_tail (fun mem s sp buf K n rom regs ret (HOK : mchrH mem s buf K n) =>
             @Strnlen.ref_strnlen fx v10_reloc v10_code v10_sites v10_img mem s sp buf K n rom regs ret
               (mchrH_generic mem s buf K n HOK)).
Qed.
End VP1.
End V10Strnlen.

From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require LibWritev.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver Require Spec.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Musl Require StdioDefs.

From LinuxProcessSemantics.Riscv Require Sem.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require SpecConsts.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require SymExec.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver Require SymExec2.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver Require SymExec2Sound.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver Require SymRun.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver Require SymDrive.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver Require SymDriveX.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver Require LibKnowFrame.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Musl Require LibStdioCall.
Module V10LibStdioCall.
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
Import OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images.Ubsan.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SeqExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StoreOk.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ShapeAlg.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Nodes.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AgentLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SpecConsts.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SymExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Hoare.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymExec2.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymExec2Sound.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymRun.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDrive.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDriveX.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.LibKnowFrame.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.Reloc.
Import V10ExitBase.
Import V10StdioDefs.
Import V10Reloc.
Import V10RelocCode.
Import V10RelocSites.
Import V10RelocImg.
Import V10RelocMusl.
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
Notation stdio_call := (@LibStdioCall.stdio_call v10_reloc v10_data).

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
Proof. exact (@LibStdioCall.know_ok_frame3 v10_reloc). Qed.

Lemma kimg_cut_sound : forall E M k a n, know_ok RSEGS E M k -> know_ok RSEGS E M (kimg_cut k a n).
Proof. exact (@LibStdioCall.kimg_cut_sound v10_reloc). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma sw_post_L : forall mem su f bufp bufsz mem',
  @StdioDefs.sw_post v10_reloc mem su f bufp bufsz mem' -> sw_post mem su f bufp bufsz mem'.
Proof.
  intros mem su f bufp bufsz mem' [f1 f2 f3 f4 f5].
  exact (Build_sw_post mem su f bufp bufsz mem' f1 f2 f3 f4 f5).
Qed.

Section VP17.
  Context {fx : FPState}.
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
  realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x2d23c) M (seg_rom RSEGS)) model)
           (t_emit (map (WriteEv (Z_to_bv 64 (sc_fd res))) (pending ++ extra)) K).
Proof.
  intros vals ebs sr kn R M model res pending extra K E HR HK Hc wb wp s l su
         H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 HCONT.
  rl_tail (@LibStdioCall.stdio_call_sound_fr _ v10_reloc v10_code v10_sites v10_data v10_rw
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
  realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x2d23c) M (seg_rom RSEGS)) model)
           (t_emit (map (WriteEv (Z_to_bv 64 (sc_fd res))) (pending ++ extra)) K).
Proof.
  intros vals ebs sr kn R M model res pending extra K E HR HK Hc wb wp s l su; intros.
  eapply stdio_call_sound_fr; try eassumption. intros R' M' HR' HK' _. auto.
Qed.
End VP17.
End V10LibStdioCall.

From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require MemSplit.
Module V10StartupFacts.
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
Import OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images.Ubsan.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.Amb.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StartupTac.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ArgvEnv.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefLayout.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefMemcpyLib.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.MemSplit.
Import V10StartupDefs.
Import V10Startup.
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
  [(0x453b0%Z, 8%nat); (0x65710%Z, 8%nat); (0x65770%Z, 8%nat); (0x65738%Z, 8%nat); (0x65700%Z, 8%nat); (0x656f8%Z, 8%nat); (0x654a8%Z, 8%nat); (0x654b8%Z, 8%nat); (0x654b0%Z, 8%nat); (0x65720%Z, 8%nat); (0x65728%Z, 8%nat); (0x45490%Z, 8%nat); (0x45478%Z, 8%nat); (0x453b8%Z, 8%nat); (0x65708%Z, 1%nat); (0x453e0%Z, 4%nat); (0x453d8%Z, 4%nat); (0x45450%Z, 8%nat); (0x45430%Z, 8%nat); (0x453c0%Z, 8%nat); (0x453c8%Z, 8%nat); (0x453d0%Z, 8%nat); (0x656e8%Z, 4%nat); (0x656ec%Z, 4%nat); (0x656e9%Z, 1%nat); (0x45470%Z, 8%nat); (0x35330%Z, 1%nat)].

Definition range_disjoint_b (a : Z) (n : nat) (c : Z * nat) : bool :=
  ((a + Z.of_nat n <=? fst c) || (fst c + Z.of_nat (snd c) <=? a))%Z.

Definition D_main_missb (a : Z) (n : nat) : bool :=
  forallb (range_disjoint_b a n) D_main_cells && (0 <=? a)%Z && (a + Z.of_nat n <=? 0x66000)%Z.

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
    rdn segs D (Z_to_bv 64 0x453d8) 4 = Some (word_to_le_bytes 4 tid).
  Proof.
    intros segs. pose proof (u64_range tid). subst D.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    pose proof (rdn_wbytes_hit segs (word_to_le_bytes 4 tid)) as Hh.
    rewrite length_N_to_le_bytes in Hh. apply Hh. unorm; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma D_main_guard : forall segs,
    rdn segs D (Z_to_bv 64 0x656e8) 8 = Some (guard_bytes a_draw).
  Proof.
    intros segs. pose proof (u64_range tid). subst D.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel. apply rdn_guard.
  Qed.

  (* [comment removed for export] *)
  Lemma D_main_guard_at : forall i, (0 <= i < 8)%Z ->
    D (Z_to_bv 64 (0x656e8 + i)) = Some (nth (Z.to_nat i) (guard_bytes a_draw) (Z_to_bv 8 0)).
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
    rdn segs D (Z_to_bv 64 0x656e8) 8 = Some (word_to_le_bytes 8 (canary_w a_draw)).
  Proof. intros segs. rewrite <- guard_bytes_w. apply D_main_guard. Qed.

  (* [comment removed for export] *)
  Lemma D_main_pagesize : forall segs,
    rdn segs D (Z_to_bv 64 0x65738) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 4096)).
  Proof.
    intros segs. pose proof (u64_range tid). pose proof len_av. subst D.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    apply rdn_wbytes_hit8. unorm; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma D_main_environ : forall segs,
    rdn segs D (Z_to_bv 64 0x453b0) 8 = Some (word_to_le_bytes 8 (envp_w sp0 av)).
  Proof.
    intros segs. pose proof (u64_range tid). pose proof len_av. subst D.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    apply rdn_wbytes_hit8. unorm; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma D_main_self : forall segs,
    rdn segs D (Z_to_bv 64 0x453b8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x453b8)).
  Proof.
    intros segs. pose proof (u64_range tid). subst D.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    apply rdn_wbytes_hit8. unorm; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma D_main_canary : forall segs,
    rdn segs D (Z_to_bv 64 0x45470) 8 = Some (word_to_le_bytes 8 (canary_w a_draw)).
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
    assert (Hr : (0 <= a /\ a + Z.of_nat n <= 0x66000)%Z).
    { unfold D_main_missb in Hb. apply andb_true_iff in Hb as [Hb H2]. apply andb_true_iff in Hb as [_ H1].
      apply Z.leb_le in H1. apply Z.leb_le in H2. lia. }
    rewrite (main_entry_rdn_data sp0 av ev tid regs mem ME)
      by (rewrite stack_max_size_val; unorm; lia).
    apply D_main_miss. exact Hb.
  Qed.

  Lemma main_entry_tid : forall segs,
    rdn segs mem (Z_to_bv 64 0x453d8) 4 = Some (word_to_le_bytes 4 tid).
  Proof.
    intros segs. rewrite (main_entry_rdn_data sp0 av ev tid regs mem ME)
      by (rewrite stack_max_size_val; unorm; lia). apply D_main_tid.
  Qed.

  Lemma main_entry_guard : forall segs,
    rdn segs mem (Z_to_bv 64 0x656e8) 8 = Some (guard_bytes a_draw).
  Proof.
    intros segs. rewrite (main_entry_rdn_data sp0 av ev tid regs mem ME)
      by (rewrite stack_max_size_val; unorm; lia). apply D_main_guard.
  Qed.

  Lemma main_entry_guard_w : forall segs,
    rdn segs mem (Z_to_bv 64 0x656e8) 8 = Some (word_to_le_bytes 8 (canary_w a_draw)).
  Proof. intros segs. rewrite <- guard_bytes_w. apply main_entry_guard. Qed.
End Facts.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End V10StartupFacts.

From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require AllocSure.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require MallocSure.
Module V10Sure.
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
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatExec.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatSim.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Hoare.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ShapeAlg.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PureModel.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.VmLedger.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AllocIface.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.MallocLayout.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.MallocTree.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.MallocOps.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.MallocIface.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.MallocInv_defs.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.MallocIfaceX.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocBase.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocSure.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.MallocAllocLayout.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.MallocGlue.
Import OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.MallocSure.
Import V10MallocLayout.
Import V10Ref_malloc.
Import V10Ref_free.
Import V10Ref_calloc.
Import V10Alloc.
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
End V10Sure.
