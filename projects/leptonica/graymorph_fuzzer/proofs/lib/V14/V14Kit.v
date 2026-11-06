(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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
From OSSVerify.leptonica.graymorph_fuzzer.images Require Ubsan.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require PropExec.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require CatExec.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require Hoare.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require AgentLib.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng Require MallocLayout.
Module V14MallocLayout.
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
Import OSSVerify.leptonica.graymorph_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.AgentLib.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng.MallocLayout.
(* [comment removed for export] *)





Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Module ImgU16 := Ubsan.

(* [comment removed for export] *)
Instance LU16 : MallocLayout := {|
  ml_segs := ImgU16.M.loaded_segments;
  IMG_LO := 0x10000; RW_LO := 0x32000; IMG_HI := 0x65000;

  A_LOCK           := Z_to_bv 64 0x64438;
  A_CTX            := Z_to_bv 64 0x64440;
  A_INIT_DONE      := Z_to_bv 64 0x64448;
  A_MMAP_CTR       := Z_to_bv 64 0x6444c;
  A_FREE_META_HEAD := Z_to_bv 64 0x64450;
  A_AVAIL_META     := Z_to_bv 64 0x64458;
  A_AVAIL_META_CNT := Z_to_bv 64 0x64460;
  A_AVAIL_AREA_CNT := Z_to_bv 64 0x64468;
  A_META_SHIFT     := Z_to_bv 64 0x64470;
  A_AREA_HEAD      := Z_to_bv 64 0x64478;
  A_AREA_TAIL      := Z_to_bv 64 0x64480;
  A_AVAIL_AREAS    := Z_to_bv 64 0x64488;
  Z_UNMAP_SEQ      := 0x64790;
  Z_BOUNCES        := 0x647b0;
  A_SEQ            := Z_to_bv 64 0x647d0;
  A_BRK            := Z_to_bv 64 0x647d8;
  A_MALLOC_REPLACED := Z_to_bv 64 0x647e0;

  A_LIBC       := Z_to_bv 64 0x643c8;
  A_NEED_LOCKS := Z_to_bv 64 0x643cb;
  A_PAGE_SIZE  := Z_to_bv 64 0x643f8;
  A_TP         := Z_to_bv 64 0x44140;
  A_ERRNO      := Z_to_bv 64 0x4409c;
  A_GOT_SSP    := Z_to_bv 64 0x32da0;
  A_SSP        := Z_to_bv 64 0x643a8;

  A_SIZE_CLASSES  := Z_to_bv 64 0x120dc;
  A_SMALL_CNT_TAB := Z_to_bv 64 0x1213c;
  A_MED_CNT_TAB   := Z_to_bv 64 0x11474;
  A_DEBRUIJN      := Z_to_bv 64 0x120bc;

  PC_MALLOC      := (0x2a360%bv : word);
  PC_FREE        := (0x2a220%bv : word);
  PC_CALLOC      := (0x2a0e8%bv : word);
  PC_LIBC_FREE   := (0x2a364%bv : word);
  PC_MALLOC_IMPL := (0x2acf0%bv : word);
  PC_GET_META    := (0x2a530%bv : word);
  PC_NTFREE      := (0x2a640%bv : word);
  PC_ALLOC_META  := (0x2aa18%bv : word);
  PC_ALLOC_SLOT  := (0x2b060%bv : word);
  PC_ENFRAME     := (0x2b904%bv : word);
  PC_ALLZEROP    := (0x2ba54%bv : word);
  PC_MMAP        := (0x2bc68%bv : word);
  PC_MPROTECT    := (0x2bd54%bv : word);
  PC_MUNMAP      := (0x2bd9c%bv : word);
  PC_VM_WAIT     := (0x2bc64%bv : word);
  PC_SYSCALL_RET := (0x2a0a8%bv : word);
  PC_ERRNO_LOC   := (0x29ca0%bv : word);
  PC_LOCK        := (0x31924%bv : word);
  PC_UNLOCK      := (0x31bac%bv : word);
  PC_MEMCPY      := (0x31354%bv : word);
  PC_MEMSET      := (0x31758%bv : word)
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
Local Abbreviation B0 := 0x10000.  Local Abbreviation B1 := 0x14000.  Local Abbreviation B2 := 0x32000.
Local Abbreviation B3 := 0x33000.  Local Abbreviation B4 := 0x65000.
Local Abbreviation P0 := 4%nat.  Local Abbreviation P1 := 30%nat.  Local Abbreviation P2 := 1%nat.  Local Abbreviation P3 := 50%nat.

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
End V14MallocLayout.

From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require StoreOk.
Module V14MemPreds.
Import Stdlib.ZArith.ZArith.
Import Stdlib.NArith.NArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import OSSVerify.leptonica.graymorph_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.StoreOk.
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
End V14MemPreds.

Module V14PFBase.
Import OSSVerify.leptonica.graymorph_fuzzer.images.Ubsan.
(* [comment removed for export] *)

Abbreviation SEGS := Ubsan.M.loaded_segments.
End V14PFBase.

From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Reloc Require Reloc.
Module V14Reloc.
Import Stdlib.ZArith.ZArith.
Import Stdlib.Lists.List.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OSSVerify.leptonica.graymorph_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Reloc.Reloc.
(* [comment removed for export] *)




Import ListNotations.
Local Open Scope Z_scope.

Definition v14_dtab : list (positive * Z) :=
  [(8%positive, 0); (1000%positive, 7396); (1001%positive, 7396); (1002%positive, 7396); (1003%positive, 7396); (1004%positive, 7396); (1005%positive, 7396); (1006%positive, 7396); (1007%positive, 7396); (1008%positive, 7520); (1009%positive, 7708); (1010%positive, 7708); (1011%positive, 7708); (1012%positive, 7708); (1013%positive, 7708); (1014%positive, 7708); (1015%positive, 73792); (1016%positive, 83296); (1017%positive, 83296); (1018%positive, 83296); (1019%positive, 83296); (1020%positive, 83296); (1021%positive, 83296); (1022%positive, 83284); (1023%positive, 83284); (1024%positive, 83284); (1025%positive, 83688); (1026%positive, 83688); (1027%positive, 83688); (1028%positive, 83688); (1029%positive, 83688); (1030%positive, 83688); (1031%positive, 83688); (1032%positive, 83688); (1033%positive, 83688); (1034%positive, 83688); (1035%positive, 83688); (1036%positive, 84004); (1037%positive, 84004); (1038%positive, 84004); (1039%positive, 84004); (1040%positive, 84004); (1041%positive, 84004); (1042%positive, 84004); (1043%positive, 84004); (1044%positive, 84004); (1045%positive, 84004); (1046%positive, 84004); (1047%positive, 84004); (1048%positive, 84004); (1049%positive, 84004); (1050%positive, 84004); (1051%positive, 84004); (1052%positive, 84372); (1053%positive, 84372); (1054%positive, 84372); (1055%positive, 84372); (1056%positive, 84372); (1057%positive, 84372); (1058%positive, 84372); (1059%positive, 84372); (1060%positive, 84372); (1061%positive, 84372); (1062%positive, 84372); (1063%positive, 84544); (1064%positive, 84544); (1065%positive, 84544); (1066%positive, 84544); (1067%positive, 84544); (1068%positive, 84544); (1069%positive, 84544); (1070%positive, 84544); (1071%positive, 84544); (1072%positive, 84544); (1073%positive, 84544); (1074%positive, 84544); (1075%positive, 84544); (1076%positive, 84544); (1077%positive, 84544); (1078%positive, 84544); (1079%positive, 84544); (1080%positive, 84544); (1081%positive, 84544); (1082%positive, 84544); (1083%positive, 84544); (1084%positive, 84544); (1085%positive, 84544); (1086%positive, 65724); (1087%positive, 84384); (1088%positive, 84384); (1089%positive, 84384); (1090%positive, 84384); (1091%positive, 84384); (1092%positive, 84384); (1093%positive, 84384); (1094%positive, 84384); (1095%positive, 84384); (1096%positive, 84384); (1097%positive, 84384); (1098%positive, 84384); (1099%positive, 84396); (1100%positive, 84396); (1101%positive, 84396); (3000%positive, 7520); (3001%positive, 73792); (4000%positive, 69); (4001%positive, 343); (4002%positive, 487); (4003%positive, 487); (4004%positive, 529); (4005%positive, 529); (4006%positive, 754); (4007%positive, 754); (4008%positive, 1167); (4009%positive, 1401); (4010%positive, 1401); (4011%positive, 1910); (4012%positive, 1910); (4013%positive, 2091); (4014%positive, 2202); (4015%positive, 2268); (4016%positive, 2448); (4017%positive, 2545); (4018%positive, 2545); (5000%positive, 3336); (5001%positive, 3336); (5002%positive, 37); (5003%positive, 176); (5004%positive, 200); (5005%positive, 200); (5006%positive, 208); (5007%positive, 208); (5008%positive, 3248); (5009%positive, 3248); (5010%positive, 3248); (5011%positive, 3728); (5012%positive, 84408); (5013%positive, 84416); (5015%positive, 84416); (5016%positive, 84400); (5018%positive, 2560); (5019%positive, 84416); (5020%positive, 3336); (5021%positive, 200); (5022%positive, 200); (5023%positive, 208); (5024%positive, 208); (5025%positive, 208); (5026%positive, 84416); (5027%positive, 84416); (5028%positive, 84416); (5029%positive, 84360); (5030%positive, 215904); (5031%positive, 215904); (5032%positive, 215904); (5033%positive, 215904);
   (230%positive, -57404); (240%positive, -57404); (241%positive, -57404); (242%positive, -57404); (243%positive, -57404); (231%positive, -56848); (232%positive, -55828); (244%positive, -55828); (245%positive, -55828); (246%positive, -55828); (233%positive, -55036); (234%positive, -54364); (247%positive, -54224); (235%positive, -54148); (236%positive, -51648); (237%positive, -43888); (248%positive, -43888); (238%positive, -41236); (249%positive, -41236); (250%positive, -26656); (239%positive, 7212); (400%positive, 17); (401%positive, 17); (402%positive, 17); (403%positive, 33); (404%positive, 33); (405%positive, -74); (406%positive, 79); (407%positive, 79); (408%positive, 79); (409%positive, 79); (410%positive, 195); (411%positive, 195); (412%positive, 210); (413%positive, 250); (414%positive, 265); (415%positive, 265); (416%positive, 331); (417%positive, 331); (418%positive, 407); (419%positive, 517); (420%positive, 517); (421%positive, 742); (422%positive, 865); (423%positive, 967); (424%positive, 995); (425%positive, 1037); (426%positive, 1047); (427%positive, 1063); (428%positive, 1136); (429%positive, 1136); (430%positive, 1161); (431%positive, 1161); (432%positive, 1161); (433%positive, 1161); (434%positive, 1256); (435%positive, 1256); (436%positive, 1320); (437%positive, 1320); (438%positive, 1360); (439%positive, 1391); (440%positive, 1391); (441%positive, 1391); (442%positive, 1414); (443%positive, 1414); (444%positive, 1489); (445%positive, 1497); (446%positive, 1525); (447%positive, 1558); (448%positive, 1574); (449%positive, 1590); (450%positive, 1659); (451%positive, 1659); (452%positive, 1712); (453%positive, 1712); (454%positive, 1712); (455%positive, 1768); (456%positive, 1768); (457%positive, 1784); (458%positive, 1893); (459%positive, 1948); (460%positive, 1948); (461%positive, 1948); (462%positive, 2001); (463%positive, 2074); (464%positive, 2074); (465%positive, 2074); (466%positive, 2173); (467%positive, 2419); (468%positive, 2419); (469%positive, 2435); (470%positive, 2435); (471%positive, 2516); (1900%positive, 83284); (5034%positive, 84408); (5035%positive, 84416); (5036%positive, 215696)].

Definition v14_stab : list (Z * Z) := [
  (0x13084, 0xffffc197); (0x13088, 0xa9818193); (0x13090, 0xfffeb597); (0x13094, 0x28c58593);
  (0x1309c, 0x40006f); (0x130a4, 0x1e617); (0x130a8, 0x1e697); (0x130ac, 0x1e717);
  (0x130b0, 0xfa063783); (0x130b4, 0xfa46b683); (0x130b8, 0xfa873703); (0x130c8, 0x39d1406f);
  (0x130dc, 0x1f517); (0x130e0, 0x23050513); (0x130f8, 0x1f517); (0x130fc, 0x21450593);
  (0x13108, 0x1e517); (0x1310c, 0xf5453503); (0x13118, 0xffffe517); (0x1311c, 0x9fc50513);
  (0x13120, 0x1f597); (0x13124, 0x1f458593); (0x13150, 0x1f517); (0x13154, 0x20450513);
  (0x1316c, 0x1f517); (0x13170, 0x1e850593); (0x1317c, 0x1e517); (0x13180, 0xee853503);
  (0x1318c, 0x1f517); (0x13190, 0xf4850513); (0x131a0, 0x1e517); (0x131a4, 0xecc53503);
  (0x131b0, 0xffffe517); (0x131b4, 0x96450513); (0x1320c, 0x6c150ef); (0x13220, 0x45c150ef);
  (0x13230, 0x1f517); (0x13234, 0x12550b13); (0x1324c, 0x4241c0ef); (0x13274, 0x408150ef);
  (0x13290, 0x3e01c0ef); (0x13298, 0x2a4150ef); (0x132b4, 0x5291c0ef); (0x132c8, 0x4b51c0ef);
  (0x1332c, 0x168000ef); (0x13340, 0x160000ef); (0x13350, 0x148000ef); (0x13368, 0x1e517);
  (0x1336c, 0xd0c53503); (0x13378, 0xffffb597); (0x1337c, 0x72858593); (0x13380, 0x3b8170ef);
  (0x13388, 0x1e517); (0x1338c, 0xcec53503); (0x13394, 0xffffc517); (0x1339c, 0x24f50513);
  (0x133a4, 0x1e517); (0x133a8, 0xcd053503); (0x133b0, 0xffffb517); (0x133b8, 0x70150513);
  (0x133c0, 0x5c4170ef); (0x133c8, 0x174150ef); (0x133fc, 0x1e517); (0x13400, 0xc7853503);
  (0x13408, 0xffffc597); (0x1340c, 0xf5658593); (0x13418, 0x1e517); (0x1341c, 0xc5c53503);
  (0x13424, 0xffffc597); (0x13428, 0xb5958593); (0x13430, 0x308170ef); (0x13438, 0x1e517);
  (0x1343c, 0xc3c53503); (0x13444, 0xffffb517); (0x1344c, 0x50450513); (0x13454, 0x530170ef);
  (0x1345c, 0x5a9140ef); (0x13460, 0x1e517); (0x13464, 0xc1453503); (0x1346c, 0xffffc597);
  (0x13470, 0xedd58593); (0x13478, 0x1e517); (0x1347c, 0xbfc53503); (0x13484, 0xffffb517);
  (0x1348c, 0x4c450513); (0x135d8, 0xffffb517); (0x135dc, 0x30850513); (0x135e4, 0x5811b0ef);
  (0x13674, 0xffffc517); (0x13678, 0xf1350513); (0x1367c, 0x18000ef); (0x13708, 0x3bd1b0ef);
  (0x13710, 0x1f517); (0x13714, 0x8bc53583); (0x13744, 0xffffc517); (0x13748, 0xe4350513);
  (0x1374c, 0xf49ff0ef); (0x1376c, 0x1d597); (0x13770, 0x7d05b583); (0x13778, 0x7411606f);
  (0x13780, 0x517); (0x13784, 0xfe450513); (0x13788, 0x1f597); (0x1378c, 0x84a5b223);
  (0x14d1c, 0x40006f); (0x15198, 0x60080ef); (0x1519c, 0x9517); (0x151a0, 0x67c53503);
  (0x151b4, 0x3b517); (0x151b8, 0xcb450913); (0x15204, 0x3b617); (0x15208, 0xccb63623);
  (0x15210, 0x3b597); (0x15214, 0xc4a5b023); (0x1521c, 0x3b517); (0x15220, 0xca053a23);
  (0x15238, 0xfffe7517); (0x1523c, 0xed650413); (0x15240, 0x9517); (0x15244, 0x5e053583);
  (0x15248, 0x9517); (0x1524c, 0x5e053503); (0x1527c, 0x214000ef); (0x15284, 0x5d000ef);
  (0x152f8, 0xfffe8517); (0x15304, 0xc0650593); (0x15328, 0xfffe8517); (0x15334, 0xbd650593);
  (0x15358, 0xfffe8517); (0x15364, 0xba650593); (0x153ac, 0xdc1ff0ef); (0x153b0, 0x9517);
  (0x153b4, 0x9597); (0x153b8, 0x48053403); (0x153bc, 0x4845b483); (0x15418, 0xd59ff0ef);
  (0x1541c, 0x517); (0x15420, 0x2c50313); (0x15478, 0xf25ff0ef); (0x1548c, 0x4fc000ef);
  (0x154b4, 0x3a597); (0x154b8, 0x73458593); (0x154bc, 0x3b617); (0x154c0, 0x9ac60493);
  (0x154d0, 0xa717); (0x154e0, 0x9297); (0x154e4, 0x5b076f03); (0x154e8, 0x2e02b283);
  (0x15630, 0x1a697); (0x15644, 0x4e868513); (0x156c0, 0x28080ef); (0x156d8, 0x3a597);
  (0x156e4, 0x51058513); (0x15700, 0x3a517); (0x15704, 0x75053503); (0x15768, 0xfffe8617);
  (0x15774, 0x2f860613); (0x15784, 0xfffe8617); (0x15788, 0xb3460613); (0x15790, 0x4000006f);
  (0x157c4, 0x9517); (0x157c8, 0x9597); (0x157cc, 0xefc53503); (0x157d0, 0xf005b403);
  (0x157fc, 0xfb5ff06f); (0x15818, 0x3a697); (0x1581c, 0x4a068693); (0x15860, 0xdbdff0ef);
  (0x15864, 0xf51ff0ef); (0x15868, 0x160020ef); (0x15870, 0xd91ff0ef); (0x15894, 0x9517);
  (0x15898, 0xe2453483); (0x158f0, 0x46d070ef); (0x1592c, 0x94000ef); (0x15954, 0x64000ef);
  (0x15968, 0x9517); (0x1596c, 0xd5053503); (0x15974, 0x2f8070ef); (0x1597c, 0x9517);
  (0x15980, 0xd3c53503); (0x15994, 0x9517); (0x15998, 0xd2453503); (0x159dc, 0xbddff0ef);
  (0x159fc, 0xffdff06f); (0x15a1c, 0xb9dff0ef); (0x15a4c, 0x22c000ef); (0x15a58, 0x3a517);
  (0x15a5c, 0x6a052503); (0x15a84, 0x5ec070ef); (0x15aa0, 0x5d0070ef); (0x15ae0, 0x590070ef);
  (0x15b0c, 0x5640706f); (0x15b2c, 0x41010ef); (0x15b38, 0x1440006f); (0x15b3c, 0x1910006f);
  (0x15b60, 0x1ac000ef); (0x15b94, 0xfffe8717); (0x15b9c, 0xd2470713); (0x15c40, 0x3a717);
  (0x15c5c, 0xf6774883); (0x15c94, 0x3a597); (0x15c98, 0xf8058593); (0x15ca4, 0x45c070ef);
  (0x15cb0, 0x16c000ef); (0x15cbc, 0x3a517); (0x15cc0, 0xf5850513); (0x15cc4, 0x6c4070ef);
  (0x15ccc, 0xfb0ff0ef); (0x15ce0, 0x99010ef); (0x15d9c, 0x3a797); (0x15da8, 0xe807b783);
  (0x15dc8, 0xfffe8797); (0x15dcc, 0xaf078793); (0x15e34, 0x8617); (0x15e38, 0x74863483);
  (0x15e84, 0x3a817); (0x15e88, 0xd9880913); (0x15e98, 0xfffe8817); (0x15e9c, 0xa2080813);
  (0x15f90, 0x3a697); (0x15f94, 0xc8c68693); (0x1608c, 0xc81ff0ef); (0x161f0, 0xe8cff0ef);
  (0x16210, 0x8517); (0x16214, 0x36c53903); (0x1621c, 0x3a597); (0x16224, 0x9f858993);
  (0x1622c, 0x3a597); (0x16230, 0x97858413); (0x1626c, 0xc5060ef); (0x1637c, 0xc8010ef);
  (0x163d4, 0x70010ef); (0x164a8, 0x88010ef); (0x164b0, 0xfcdfe0ef); (0x164c8, 0xbb4ff0ef);
  (0x164f8, 0xf85fe0ef); (0x16534, 0x39597); (0x16538, 0x6e058493); (0x16560, 0x6e5000ef);
  (0x1656c, 0x39517); (0x16570, 0x63b54503); (0x16578, 0x39517); (0x1657c, 0x69c50513);
  (0x16580, 0x381060ef); (0x165b0, 0xfffe7617); (0x165b8, 0x2e860993); (0x16620, 0xfffe7617);
  (0x16634, 0x29860593); (0x16654, 0xba1ff0ef); (0x166c0, 0x39517); (0x166c4, 0x4e754503);
  (0x166cc, 0x39517); (0x166d0, 0x54850513); (0x166d4, 0x22d060ef); (0x16718, 0x39517);
  (0x1671c, 0x4fc50513); (0x16720, 0x469060ef); (0x1672c, 0x64d000ef); (0x167d8, 0x64000ef);
  (0x167f8, 0x391060ef); (0x16828, 0xb90006f); (0x1682c, 0x39517); (0x16830, 0x3e850513);
  (0x16834, 0x355060ef); (0x16874, 0x8517); (0x16878, 0xd0853a03); (0x16884, 0x39597);
  (0x16888, 0x39058b13); (0x16a04, 0xfffe7597); (0x16a0c, 0xe9458593); (0x16a20, 0xfffe7517);
  (0x16a24, 0xe9850c93); (0x16a30, 0xfc4ff0ef); (0x16a44, 0x39597); (0x16a48, 0x1905b583);
  (0x16a5c, 0xfffe7697); (0x16a60, 0xebc68693); (0x16a8c, 0xfffe6697); (0x16a90, 0x1c468693);
  (0x16ba4, 0xfffe7697); (0x16bac, 0xcf468693); (0x16c48, 0x498000ef); (0x16d18, 0xfffe7717);
  (0x16d20, 0xba070713); (0x16ee8, 0x55c000ef); (0x170dc, 0xfa0fe0ef); (0x17108, 0xfffe6797);
  (0x17110, 0x7b078793); (0x172c4, 0x39797); (0x172cc, 0x9587b783); (0x172ec, 0xfffe6817);
  (0x172f0, 0x5cc80813); (0x17360, 0xfffe6597); (0x17364, 0x55858593); (0x1738c, 0xfffe6517);
  (0x17390, 0x52c50513); (0x173b0, 0xfffe6597); (0x173b4, 0x97c5b787); (0x173e8, 0xfffe6597);
  (0x173ec, 0x95c5b787); (0x1746c, 0x810fe0ef); (0x17484, 0xff9fd0ef); (0x174e0, 0xf61ff0ef);
  (0x17528, 0xb5cfe0ef); (0x17538, 0x38697); (0x1753c, 0x69c6b683); (0x17564, 0xb20fe0ef);
  (0x17590, 0xeb1ff0ef); (0x175a4, 0xae0fe0ef); (0x17728, 0x664000ef); (0x17734, 0x38517);
  (0x17738, 0x72053403); (0x1774c, 0xd05ff0ef); (0x17790, 0x8517); (0x17794, 0xeb453403);
  (0x177a8, 0xca9ff0ef); (0x177ec, 0x8517); (0x177f0, 0xd6853403); (0x17804, 0xc4dff0ef);
  (0x17868, 0xbe9ff0ef); (0x178ec, 0x7517); (0x178f0, 0xb2053a83); (0x1794c, 0xdc9fd0ef);
  (0x179d4, 0xd41fd0ef); (0x17a4c, 0xcc1fd0ef); (0x17a54, 0xcd0506f); (0x17a68, 0xff1ff0ef);
  (0x17a74, 0xca1fd0ef); (0x17a9c, 0x7817); (0x17aa0, 0x97083403); (0x17ac8, 0x3a0000ef);
  (0x17ae8, 0xc25fd0ef); (0x17b5c, 0x360050ef); (0x17b74, 0x160000ef); (0x17c54, 0xe99ff0ef);
  (0x17c9c, 0x525040ef); (0x17d14, 0xf3cff0ef); (0x17d28, 0xe75ff0ef); (0x17d38, 0x815ff0ef);
  (0x17d58, 0xe45ff0ef); (0x17d98, 0x38517); (0x17d9c, 0xc450413); (0x17da4, 0x1ec050ef);
  (0x17de4, 0x6517); (0x17de8, 0x57c53903); (0x17e20, 0x14c000ef); (0x17e34, 0xd70ff0ef);
  (0x17e94, 0xbadff0ef); (0x17ec0, 0xac000ef); (0x17f30, 0xd70ff0ef); (0x17f68, 0xef8fd0ef);
  (0x17fc4, 0x6517); (0x17fd0, 0x39c53603); (0x180b0, 0xa41ff0ef); (0x183d0, 0xfffe5697);
  (0x183d4, 0x49068693); (0x18444, 0x159000ef); (0x1849c, 0xfffe5597); (0x184a0, 0x27c58593);
  (0x184dc, 0x2c9000ef); (0x1850c, 0xfffe3597); (0x18514, 0x3e058593); (0x18538, 0xfffe3517);
  (0x1853c, 0x3b450513); (0x18554, 0xfffe4517); (0x18558, 0x4d450b93); (0x18560, 0xd01fc0ef);
  (0x18568, 0xd05fc0ef); (0x18580, 0x121040ef); (0x18598, 0xfffe3617); (0x1859c, 0x35460613);
  (0x185dc, 0xfffe3597); (0x185e0, 0x31058593); (0x18614, 0xfffe5597); (0x18618, 0x1e458593);
  (0x18644, 0xfffe3597); (0x18648, 0x2a858893); (0x18680, 0xfffe3517); (0x18684, 0x26c50513);
  (0x186b8, 0xfffe3597); (0x186bc, 0x23458713); (0x186d0, 0xfffe5697); (0x186d4, 0x36068693);
  (0x18734, 0x739010ef); (0x1876c, 0x764000ef); (0x18790, 0x6dd010ef); (0x187b4, 0xb3cff0ef);
  (0x187c0, 0xfffe3597); (0x187c4, 0x12c58593); (0x187e8, 0xfffe3597); (0x187f0, 0x10458893);
  (0x18938, 0x3e0040ef); (0x18968, 0x988ff0ef); (0x1898c, 0x964ff0ef); (0x189a8, 0x948ff0ef);
  (0x189dc, 0x33c040ef); (0x18a0c, 0x8e4ff0ef); (0x18a30, 0x8c0ff0ef); (0x18a60, 0x2b8040ef);
  (0x18a90, 0x860ff0ef); (0x18ab4, 0x83cff0ef); (0x18ad0, 0x820ff0ef); (0x18b04, 0x214040ef);
  (0x18b34, 0xfbdfe0ef); (0x18b54, 0xf9dfe0ef); (0x18b70, 0x360000ef); (0x18b94, 0x33c000ef);
  (0x18be4, 0xe7cfc0ef); (0x18c18, 0x184000ef); (0x18c2c, 0x170000ef); (0x18c40, 0x15c000ef);
  (0x18c54, 0x148000ef); (0x18c68, 0x134000ef); (0x18c7c, 0x120000ef); (0x18c90, 0x10c000ef);
  (0x18ca4, 0xf8000ef); (0x18cb8, 0xe4000ef); (0x18d38, 0xd28fc0ef); (0x18d98, 0x8c9fc0ef);
  (0x18dac, 0xfffe5697); (0x18db0, 0xa6c68693); (0x18dfc, 0x1c1010ef); (0x18eec, 0x5517);
  (0x18ef0, 0x47453903); (0x18f24, 0x5f5030ef); (0x18f54, 0xb9dfe0ef); (0x18f74, 0xb7dfe0ef);
  (0x18fa0, 0xec0fc0ef); (0x19000, 0x5517); (0x19004, 0x36053a03); (0x1905c, 0xf1010ef);
  (0x19068, 0xfffe3517); (0x19070, 0xaab50513); (0x19084, 0xfffe3517); (0x1908c, 0xa8f50513);
  (0x190c4, 0x91010ef); (0x190e0, 0xb9010ef); (0x190f0, 0x148020ef); (0x19104, 0x235010ef);
  (0x19118, 0x159010ef); (0x19154, 0xfffe4517); (0x19158, 0x97453507); (0x1915c, 0x660010ef);
  (0x19170, 0x1c9010ef); (0x191a0, 0xd1010ef); (0x191a8, 0xfffe3597); (0x191ac, 0xfffe3617);
  (0x191b0, 0xe0a58593); (0x191b4, 0x66260993); (0x19210, 0xf7dfd0ef); (0x19230, 0x58c010ef);
  (0x1924c, 0xf4020ef); (0x19258, 0xf8020ef); (0x19268, 0xfffe3597); (0x1926c, 0xfffe3617);
  (0x19270, 0xfb558593); (0x19274, 0x4fb60993); (0x192b0, 0x269030ef); (0x192e0, 0x811fe0ef);
  (0x19300, 0xff0fe0ef); (0x1931c, 0xfd4fe0ef); (0x19338, 0xfb8fe0ef); (0x1936c, 0x1ad030ef);
  (0x1939c, 0xf54fe0ef); (0x193bc, 0xf34fe0ef); (0x19454, 0x704020ef); (0x19464, 0x5d5010ef);
  (0x19478, 0x774020ef); (0x1948c, 0x6b5010ef); (0x194a0, 0x698010ef); (0x194b4, 0x5bc010ef);
  (0x194c0, 0xfffe3517); (0x194c4, 0x66053503); (0x1975c, 0x60010ef); (0x19778, 0x3d9010ef);
  (0x19784, 0x3bd010ef); (0x19864, 0xfffe4797); (0x19880, 0x1cc78913); (0x198a0, 0x1d0010ef);
  (0x198b4, 0x424020ef); (0x198d4, 0x165010ef); (0x198e4, 0x155010ef); (0x198f8, 0x249010ef);
  (0x1990c, 0x22c010ef); (0x19934, 0x13c010ef); (0x199f4, 0x324030ef); (0x19a24, 0x8ccfe0ef);
  (0x19a68, 0x7d0010ef); (0x19a78, 0x308020ef); (0x19ab8, 0x780010ef); (0x19acc, 0x85010ef);
  (0x19ae0, 0xfffe3517); (0x19ae4, 0x1853507); (0x19b08, 0xfe9fd0ef); (0x19b24, 0xfcdfd0ef);
  (0x19b50, 0x1c8030ef); (0x19b80, 0xf71fd0ef); (0x19ba0, 0xf51fd0ef); (0x19bc4, 0xf2dfd0ef);
  (0x19bec, 0x12c030ef); (0x19c1c, 0xed5fd0ef); (0x19c3c, 0xeb5fd0ef); (0x19c58, 0xe99fd0ef);
  (0x19c84, 0x94030ef); (0x19cb4, 0xe3dfd0ef); (0x19cd4, 0xe1dfd0ef); (0x19cf0, 0xfffe3517);
  (0x19cf4, 0xdf853507); (0x19cfc, 0xfffe3517); (0x19d00, 0xe1c53507); (0x19d04, 0x2b9000ef);
  (0x19d38, 0x500010ef); (0x19d54, 0x5e5000ef); (0x19d70, 0x5c9000ef); (0x19d90, 0x5c0010ef);
  (0x19d9c, 0x4d5000ef); (0x1a0dc, 0x43d020ef); (0x1a110, 0x9e1fd0ef); (0x1a138, 0x9b9fd0ef);
  (0x1a158, 0x999fd0ef); (0x1a194, 0x385020ef); (0x1a1c8, 0x929fd0ef); (0x1a1f0, 0x901fd0ef);
  (0x1a2ec, 0x805fd0ef); (0x1a314, 0xfffe2597); (0x1a324, 0x91b58513); (0x1a3dc, 0xf14fd0ef);
  (0x1a424, 0xeccfd0ef); (0x1a458, 0xe98fd0ef); (0x1a484, 0xa4dfe0ef); (0x1a4ac, 0xe44fd0ef);
  (0x1a4c8, 0xfffe1517); (0x1a4cc, 0x76750513); (0x1a4d8, 0xe18fd0ef); (0x1a5a0, 0xd50fd0ef);
  (0x1a5c8, 0x909fe0ef); (0x1a604, 0x714020ef); (0x1a634, 0xcbcfd0ef); (0x1a654, 0xc9cfd0ef);
  (0x1a668, 0xff9fa0ef); (0x1a67c, 0x14000ef); (0x1a76c, 0xaf5fa0ef); (0x1a9d4, 0x9c000ef);
  (0x1a9dc, 0xfffe2517); (0x1a9e0, 0x15453507); (0x1a9e4, 0xdd9ff0ef); (0x1a9f8, 0x140000ef);
  (0x1b34c, 0x40006f); (0x1ba70, 0xac000ef); (0x1bad0, 0x7c000ef); (0x1bb30, 0xfffe2597);
  (0x1bb34, 0xf1058593); (0x1c688, 0x3597); (0x1c68c, 0xe2858593); (0x1c69c, 0xf20fb06f);
  (0x1c6ac, 0x6697); (0x1c6b0, 0x6386b403); (0x1c6c0, 0x717); (0x1c6c4, 0xad870713);
  (0x1c71c, 0xa7dff0ef); (0x1c73c, 0x8a9fd0ef); (0x1c760, 0x2617); (0x1c764, 0xca063903);
  (0x1c7a0, 0x618000ef); (0x1c7a4, 0x517); (0x1c7b0, 0x6850513); (0x1c7dc, 0xe80fb0ef);
  (0x1c808, 0xef9f80ef); (0x1c864, 0x150000ef); (0x1c894, 0x120000ef); (0x1c940, 0xfffe0697);
  (0x1c944, 0x2606b683); (0x1c948, 0xfffe0717); (0x1c94c, 0x24873703); (0x1ceec, 0xfffe0597);
  (0x1cef0, 0xfffe0717); (0x1cef4, 0xcb45b683); (0x1cef8, 0xca073703); (0x1cf60, 0x989ff0ef);
  (0x1cf84, 0x33597); (0x1cf88, 0xaa758683); (0x1cfb4, 0xaa0583a3); (0x1d2a4, 0xfddff06f);
  (0x1d2bc, 0xf84fa0ef); (0x1d2dc, 0xfbdff0ef); (0x1d2f4, 0xc08f80ef); (0x1d310, 0xbecf806f);
  (0x1d338, 0xf61ff0ef); (0x1d344, 0xbb8f806f);
  (0x237e0, 159383791); (0x2381c, 2006036719); (0x23828, 120087); (0x2382c, 1480930563);
  (0x2383c, 4294948119); (0x23840, 4294948247); (0x23844, 3419735315); (0x23848, 173376915);
  (0x2385c, 3537891439); (0x2388c, 322961647); (0x238b8, 124311); (0x238bc, 1464173715);
  (0x238d8, 117448943); (0x238e0, 120087); (0x238e4, 1287992579); (0x238f4, 4294948119);
  (0x238f8, 4294948247); (0x238fc, 3226797331); (0x23900, 3679815059); (0x23918, 3340759151);
  (0x23948, 290537711); (0x2395c, 876626159); (0x23968, 256983279); (0x2396c, 120087);
  (0x23970, 1141191939); (0x23980, 4294948119); (0x23984, 4294948247); (0x23988, 1901397267);
  (0x2398c, 3533014419); (0x23994, 3210735855); (0x23a14, 120471); (0x23a18, 965129219);
  (0x23a28, 4294948503); (0x23a2c, 4294948631); (0x23a30, 1935050387); (0x23a34, 4154918675);
  (0x23a50, 2850025711); (0x23a5c, 4294948119); (0x23a60, 4294948247); (0x23a64, 3323266323);
  (0x23a68, 4100294035); (0x23a70, 120087); (0x23a74, 868562179); (0x23a84, 4294948119);
  (0x23a88, 4294948247); (0x23a8c, 2249524499); (0x23a90, 4058350995); (0x23a98, 120087);
  (0x23a9c, 826619139); (0x23aac, 4294948119); (0x23ab0, 4294948247); (0x23ab4, 556074259);
  (0x23ab8, 4016407955); (0x23ad8, 120471); (0x23adc, 759608323); (0x23aec, 4294948503);
  (0x23af0, 4294948631); (0x23af4, 1729529491); (0x23af8, 3949397779); (0x23b14, 2644504815);
  (0x23b20, 4294948119); (0x23b24, 4294948247); (0x23b28, 1078265107); (0x23b2c, 3894773139);
  (0x23b34, 120087); (0x23b38, 663041283); (0x23b48, 4294948119); (0x23b4c, 4294948247);
  (0x23b50, 2779055379); (0x23b54, 3852830099); (0x23b78, 2703224943); (0x23b88, 120087);
  (0x23b8c, 574960899); (0x23b9c, 4294948119); (0x23ba0, 4294948247); (0x23ba4, 2347042067);
  (0x23ba8, 3764749715); (0x23bbc, 120087); (0x23bc0, 520434947); (0x23bd0, 4294948119);
  (0x23bd4, 4294948247); (0x23bd8, 1635058963); (0x23bdc, 3710223763); (0x23be8, 120087);
  (0x23bec, 474297603); (0x23bfc, 4294948119); (0x23c00, 4294948247); (0x23c04, 382010643);
  (0x23c08, 3664086419); (0x23c0c, 2384457967); (0x23c48, 1304510703); (0x23c58, 416284911);
  (0x23c64, 546308335); (0x23c70, 676331759); (0x23c9c, 120087); (0x23ca0, 285553923);
  (0x23cb0, 4294948119); (0x23cb4, 4294948247); (0x23cb8, 2224358675); (0x23cbc, 3475342739);
  (0x23cf8, 120087); (0x23cfc, 189084931); (0x23d0c, 4294944023); (0x23d10, 4294948247);
  (0x23d14, 1795491091); (0x23d18, 583370131); (0x23d20, 4186959983); (0x23d7c, 124311);
  (0x23d80, 193312131); (0x23d90, 1287733487); (0x23da4, 1875914991); (0x23db0, 1254179055);
  (0x23dc0, 120087); (0x23dc4, 4274337027); (0x23dd4, 4294948119); (0x23dd8, 4294948247);
  (0x23ddc, 1269105939); (0x23de0, 3315959187); (0x23df4, 4019187823); (0x23e8c, 120087);
  (0x23e90, 3477419267); (0x23ea0, 4294944023); (0x23ea4, 4294948247); (0x23ea8, 788858131);
  (0x23eac, 839222675); (0x23eb4, 3180327023); (0x23f04, 2000695535); (0x23f20, 1140863215);
  (0x23f34, 120087); (0x23f38, 2231710979); (0x23f48, 4294944023); (0x23f4c, 4294944151);
  (0x23f50, 3838117139); (0x23f54, 1712686483); (0x23f6c, 4066369647); (0x23f70, 120087);
  (0x23f74, 2168796419); (0x23f84, 4294948119); (0x23f88, 4294944151); (0x23f8c, 2577728787);
  (0x23f90, 1649771923); (0x23f98, 4020232431); (0x23fd8, 115991); (0x23fdc, 2059744515);
  (0x23fec, 4294944023); (0x23ff0, 4294948247); (0x23ff4, 3666150675); (0x23ff8, 3224733075);
  (0x24000, 3911180399); (0x24008, 116119); (0x2400c, 2009445763); (0x24020, 4294944023);
  (0x24024, 4294948247); (0x24028, 574948627); (0x2402c, 3170207123); (0x24034, 3856654447);
  (0x24060, 115991); (0x24064, 1917138179); (0x24074, 4294944023); (0x24078, 4294944151);
  (0x2407c, 3523544339); (0x24080, 1384482195); (0x24088, 3768574063); (0x24090, 116119);
  (0x24094, 1866839427); (0x240a8, 4294944023); (0x240ac, 4294944151); (0x240b0, 2142569747);
  (0x240b4, 1329956243); (0x240bc, 3714048111); (0x240e8, 115991); (0x240ec, 1774531843);
  (0x240fc, 4294944023); (0x24100, 4294944151); (0x24104, 3380938003); (0x24108, 3182790035);
  (0x24110, 3625967727); (0x24114, 115991); (0x24118, 1728394499); (0x24128, 4294944023);
  (0x2412c, 4294944151); (0x24130, 1700070675); (0x24134, 3136652691); (0x2413c, 3579830383);
  (0x24160, 115991); (0x24164, 818230531); (0x24174, 4294944023); (0x24178, 4294944151);
  (0x2417c, 2424636691); (0x24180, 882214291); (0x24188, 2669666415); (0x241ac, 115991);
  (0x241b0, 33895683); (0x241c0, 4294939927); (0x241c4, 4294940055); (0x241c8, 1640301843);
  (0x241cc, 1429570963); (0x241d4, 4031766639); (0x241f8, 115991); (0x241fc, 4102370563);
  (0x2420c, 4294939927); (0x24210, 4294940055); (0x24214, 1413809427); (0x24218, 1426425235);
  (0x24220, 4023378031); (0x24244, 115991); (0x24248, 3942987011); (0x24258, 4294939927);
  (0x2425c, 4294944151); (0x24260, 1254425875); (0x24264, 492144019); (0x2426c, 3645890671);
  (0x242f8, 3968852207); (0x24310, 111895); (0x24314, 1107637507); (0x24328, 4294939927);
  (0x2432c, 4294940055); (0x24330, 160761107); (0x24334, 694519187); (0x24338, 3013595375);
  (0x24340, 111895); (0x24344, 1057305859); (0x24354, 4294939927); (0x24358, 4294940055);
  (0x2435c, 2663712019); (0x24360, 648381843); (0x2437c, 2887766127); (0x2438c, 3297767663);
  (0x24398, 2903498991); (0x243d0, 4294944151); (0x243d4, 2802157331); (0x24544, 3062878447);
  (0x24554, 103703); (0x24558, 952448259); (0x24568, 4294931735); (0x2456c, 4294931863);
  (0x24570, 4179952915); (0x24574, 2933228947); (0x24580, 103703); (0x24584, 906310915);
  (0x24594, 4294931735); (0x24598, 4294931863); (0x2459c, 3937731859); (0x245a0, 2887091603);
  (0x245a8, 103703); (0x245ac, 864367875); (0x245bc, 4294931735); (0x245c0, 4294931863);
  (0x245c4, 2306147603); (0x245c8, 2845148563); (0x245d0, 103703); (0x245d4, 822424835);
  (0x245e4, 4294931735); (0x245e8, 4294931863); (0x245ec, 1313146131); (0x245f0, 2803205523);
  (0x24610, 2648682607); (0x24634, 103831); (0x24638, 717600131); (0x24648, 4294931735);
  (0x2464c, 4294931863); (0x24650, 1232405779); (0x24654, 2698347923); (0x24664, 103831);
  (0x24668, 667268483); (0x24678, 4294931735); (0x2467c, 4294931863); (0x24680, 4264887571);
  (0x24684, 2648016275); (0x2468c, 2573185263); (0x24698, 103703); (0x2469c, 612709635);
  (0x246b0, 4294931735); (0x246b4, 4294931863); (0x246b8, 2160395539); (0x246bc, 2589296019);
  (0x246c4, 2514465007); (0x246e0, 103831); (0x246e4, 537245059); (0x246f4, 4294931735);
  (0x246f8, 4294931863); (0x246fc, 4183098643); (0x24700, 2517992851); (0x24718, 103703);
  (0x2471c, 478491907); (0x24730, 4294931735); (0x24734, 4294931863); (0x24738, 572851475);
  (0x2473c, 2455078291); (0x24744, 103703); (0x24748, 432354563); (0x2475c, 4294931735);
  (0x24760, 4294931863); (0x24764, 2266301715); (0x24768, 2408940947); (0x2476c, 2338304239);
  (0x24780, 1691353327); (0x247a4, 103703); (0x247a8, 331691267); (0x247bc, 4294931735);
  (0x247c0, 4294931863); (0x247c4, 4232381715); (0x247c8, 2308277651); (0x24808, 1484849391);
  (0x24810, 1476460783); (0x2481c, 103703); (0x24820, 205862147); (0x24830, 4294931735);
  (0x24834, 4294931863); (0x24838, 1495598355); (0x2483c, 2170914195); (0x24850, 4245663855);
  (0x248b4, 99607); (0x248b8, 1560622339); (0x248c8, 4294927639); (0x248cc, 3797222675);
  (0x248d4, 99607); (0x248d8, 1527067907); (0x248e8, 4294927639); (0x248ec, 1703216403);
  (0x24904, 99607); (0x24908, 1476736259); (0x24918, 4294927639); (0x2491c, 600114451);
  (0x24924, 99607); (0x24928, 1443181827); (0x24938, 4294927639); (0x2493c, 555025683);
  (0x24940, 4294931863); (0x24944, 2318763411); (0x2497c, 3462373487); (0x249e8, 22081775);
  (0x24a14, 2122379503); (0x24a24, 99607); (0x24a2c, 1174748291); (0x24a30, 4294927639);
  (0x24a34, 2044004883); (0x24a38, 4294927639); (0x24a3c, 2634353299); (0x24b64, 2732564719);
  (0x24bc0, 3578769647); (0x24be4, 2643439855); (0x24bf0, 3012542703); (0x24c10, 999305455);
  (0x24c28, 99607); (0x24c2c, 633681155); (0x24c3c, 4294931735); (0x24c40, 4294931863);
  (0x24c44, 2329216275); (0x24c48, 2348123539); (0x24c50, 99607); (0x24c54, 591738115);
  (0x24c64, 4294923543); (0x24c68, 4294931863); (0x24c6c, 1954874643); (0x24c70, 2306180499);
  (0x24c9c, 2405408879); (0x24e60, 99607); (0x24e64, 38089987); (0x24e74, 4294927639);
  (0x24e78, 4294927767); (0x24e7c, 3471115539); (0x24e80, 1752532371); (0x24e88, 4035944687);
  (0x24f14, 4220485871); (0x24f20, 3822026991); (0x24f34, 3016720623); (0x24f40, 3633279215);
  (0x24f4c, 4002382063); (0x25020, 83223); (0x25024, 1459959043); (0x25034, 4294911255);
  (0x25038, 4294915479); (0x2503c, 1002767635); (0x25040, 3090515347); (0x25048, 83351);
  (0x2504c, 1418048899); (0x2505c, 4294911255); (0x25060, 4294915479); (0x25064, 3024422163);
  (0x25068, 3048572307); (0x2508c, 3240058991); (0x25170, 50455); (0x25174, 4249171203);
  (0x25184, 4294878487); (0x25188, 4294878743); (0x2518c, 4022666515); (0x25190, 3421898387);
  (0x2519c, 4002341103); (0x251a4, 50455); (0x251a8, 4194645251); (0x251b8, 4294878487);
  (0x251bc, 4294878615); (0x251c0, 75826451); (0x251c4, 3367339411); (0x25278, 50455);
  (0x2527c, 3972347139); (0x2528c, 4294878487); (0x25290, 4294878615); (0x25294, 773129491);
  (0x25298, 3145041299); (0x252a0, 50455); (0x252a4, 3930404099); (0x252b4, 4294878487);
  (0x252b8, 4294878615); (0x252bc, 3740599571); (0x252c0, 3103098259); (0x252f0, 3809402991);
  (0x25300, 50455); (0x25304, 3829740803); (0x25314, 4294874391); (0x25318, 4294878615);
  (0x2531c, 1291126035); (0x25320, 3002434963); (0x25338, 50455); (0x2533c, 3771020547);
  (0x2534c, 4294874391); (0x25350, 4294878615); (0x25354, 1066730771); (0x25358, 2943714707);
  (0x25390, 2627657967); (0x253a0, 3453935855); (0x253e4, 3462324463); (0x253fc, 4144947439);
  (0x25424, 4035916015); (0x25438, 3310285039); (0x25444, 3361661167); (0x25448, 50455);
  (0x2544c, 3485807875); (0x2545c, 4294878487); (0x25460, 4294878615); (0x25464, 4066706707);
  (0x25468, 2658502035); (0x25470, 50455); (0x25474, 3443864835); (0x25484, 4294878487);
  (0x25488, 4294878615); (0x2548c, 3460629779); (0x25490, 2616558995); (0x25498, 50455);
  (0x2549c, 3401921795); (0x254ac, 4294874391); (0x254b0, 4294878615); (0x254b4, 1768228115);
  (0x254b8, 2574615955); (0x254c0, 50455); (0x254c4, 3359978755); (0x254d4, 4294878487);
  (0x254d8, 4294878615); (0x254dc, 2160395539); (0x254e0, 2532672915); (0x254f0, 3108954351);
  (0x254f8, 50455); (0x254fc, 3301258499); (0x2550c, 4294878487); (0x25510, 4294878615);
  (0x25514, 3567584531); (0x25518, 2473952659); (0x2552c, 3118391535); (0x25530, 50455);
  (0x25534, 3242538243); (0x25544, 4294878487); (0x25548, 4294878615); (0x2554c, 772080915);
  (0x25550, 2415232403); (0x2555c, 3370053871); (0x2558c, 432054511); (0x255a0, 4161741039);
  (0x255b8, 2971590895); (0x255bc, 50455); (0x255c0, 3095737603); (0x255d0, 4294874391);
  (0x255d4, 4294878615); (0x255d8, 870647059); (0x255dc, 2268431763); (0x255e4, 3016679663)].

Definition v14_reloc : Reloc := {|
  rl_segs := Ubsan.M.loaded_segments;
  rl_dtab := v14_dtab;
  rl_stab := v14_stab;
  rl_img_lo := 0x10000; rl_rw_lo := 0x32000; rl_img_hi := 0x65000;
  rl_dtab_ok := eq_refl |}.
End V14Reloc.

From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require StartupTac.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require ArgvEnv.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require RefLayout.
Module V14StartupDefs.
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
Import OSSVerify.leptonica.graymorph_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.StartupTac.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.ArgvEnv.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.RefLayout.
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
      (Z_to_bv 64 0x643a8) (word_to_le_bytes 4 (v_lw rwa)))
      (Z_to_bv 64 0x643ac) (word_to_le_bytes 4 (v_lw rwb)))
      (Z_to_bv 64 0x643a9) [Z_to_bv 8 0]) (Z_to_bv 64 0x643a8) 8 = Some guard_bytes.
  Proof.
    intros segs D. unfold guard_bytes.
    set (A := word_to_le_bytes 4 (v_lw rwa)). set (B := word_to_le_bytes 4 (v_lw rwb)).
    assert (HA : length A = 4%nat) by (subst A; apply length_N_to_le_bytes).
    assert (HB : length B = 4%nat) by (subst B; apply length_N_to_le_bytes).
    assert (Hin : rdn segs (wbytes D (Z_to_bv 64 0x643a8) A) (Z_to_bv 64 0x643a8) 4 = Some A).
    { rewrite <- HA at 1. apply rdn_wbytes_hit. rewrite HA. unorm. lia. }
    change 8%nat with (1 + (1 + (2 + 4)))%nat.
    apply rdn_app.
    { rewrite rdn_wbytes_out by (cbn [length]; unorm; lia).
      rewrite rdn_wbytes_out by (rewrite ?HB; unorm; lia).
      exact (SeqExec.rdn_firstn _ _ _ _ _ 1 Hin ltac:(lia)). }
    apply rdn_app.
    { change (Z_to_bv 64 410536 + nat_to_word 1) with (Z_to_bv 64 0x643a9 : word).
      exact (rdn_wbytes_hit segs [Z_to_bv 8 0] _ (Z_to_bv 64 0x643a9) ltac:(cbn [length]; unorm; lia)). }
    apply rdn_app.
    { change (Z_to_bv 64 410536 + nat_to_word 1 + nat_to_word 1) with (Z_to_bv 64 0x643aa : word).
      rewrite rdn_wbytes_out by (cbn [length]; unorm; lia).
      rewrite rdn_wbytes_out by (rewrite ?HB; unorm; lia).
      exact (SeqExec.rdn_skipn _ _ _ _ _ 2 Hin ltac:(lia)). }
    change (Z_to_bv 64 410536 + nat_to_word 1 + nat_to_word 1 + nat_to_word 2) with (Z_to_bv 64 0x643ac : word).
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
      (Z_to_bv 64 0x44070) (word_to_le_bytes 8 envp_w))          (* [comment removed for export] *)
      (Z_to_bv 64 0x643d0) (word_to_le_bytes 8 auxv_w))          (* [comment removed for export] *)
      (Z_to_bv 64 0x64430) (word_to_le_bytes 8 hw))            (* [comment removed for export] *)
      (Z_to_bv 64 0x643f8) (word_to_le_bytes 8 (Z_to_bv 64 4096))) (* [comment removed for export] *)
      (Z_to_bv 64 0x643c0) (word_to_le_bytes 8 pn_w))            (* [comment removed for export] *)
      (Z_to_bv 64 0x643b8) (word_to_le_bytes 8 progname_w).      (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition J_lsm (J : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes
    (wbytes (wbytes (wbytes (wbytes J
      (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0x2997c)))
      (Z_to_bv 64 (bv_unsigned sp0 - 48)) (word_to_le_bytes 8 argv_w))
      (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 argc_w))
      (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0x14eb4)).

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
      (Z_to_bv 64 0x64168) (word_to_le_bytes 8 (Z_to_bv 64 0)))        (* [comment removed for export] *)
      (Z_to_bv 64 0x64178) (word_to_le_bytes 8 (Z_to_bv 64 0)))        (* [comment removed for export] *)
      (Z_to_bv 64 0x64170) (word_to_le_bytes 8 (Z_to_bv 64 8)))        (* [comment removed for export] *)
      (Z_to_bv 64 0x643e0) (word_to_le_bytes 8 (Z_to_bv 64 0xe0)))     (* [comment removed for export] *)
      (Z_to_bv 64 0x643e8) (word_to_le_bytes 8 (Z_to_bv 64 8)))        (* [comment removed for export] *)
      (Z_to_bv 64 0x44150) (word_to_le_bytes 8 (Z_to_bv 64 0)))        (* [comment removed for export] *)
      (Z_to_bv 64 0x44138) (word_to_le_bytes 8 (Z_to_bv 64 0x44150)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x44078) (word_to_le_bytes 8 (Z_to_bv 64 0x44078)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x643c8) [Z_to_bv 8 1])                              (* [comment removed for export] *)
      (Z_to_bv 64 0x440a0) (word_to_le_bytes 4 (Z_to_bv 64 2)).        (* [comment removed for export] *)

  Definition D_tlsB (tid : word) (D : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes D
      (Z_to_bv 64 0x44098) (word_to_le_bytes 4 tid))                   (* [comment removed for export] *)
      (Z_to_bv 64 0x44110) (word_to_le_bytes 8 (Z_to_bv 64 0x64400)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x440f0) (word_to_le_bytes 8 (Z_to_bv 64 0x440f0)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x44080) (word_to_le_bytes 8 (Z_to_bv 64 0x44078)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x44088) (word_to_le_bytes 8 (Z_to_bv 64 0x44078)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x44090) (word_to_le_bytes 8 (Z_to_bv 64 0)).        (* [comment removed for export] *)

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
      (Z_to_bv 64 0x643a8) (word_to_le_bytes 4 (v_lw (rwa drw))))  (* [comment removed for export] *)
      (Z_to_bv 64 0x643ac) (word_to_le_bytes 4 (v_lw (rwb drw))))  (* [comment removed for export] *)
      (Z_to_bv 64 0x643a9) [Z_to_bv 8 0])                     (* [comment removed for export] *)
      (Z_to_bv 64 0x44130) (word_to_le_bytes 8 (canary_w drw)).     (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition D_fd (D : word -> option byte) : word -> option byte :=
    wbytes D (Z_to_bv 64 0x33ff0) [Z_to_bv 8 1].

  (* [comment removed for export] *)
  Definition D_main (tid : word) : word -> option byte := D_fd (D_ssp (D_tls tid D_libc)).

End Defs.
End V14StartupDefs.

From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Musl Require PFSpec.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica.VL Require LeptStderr.
Module V14LeptEnv.
Import Stdlib.ZArith.ZArith.
Import Stdlib.Lists.List.
Import Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Reloc.Reloc.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica.VL.LeptStderr.
Import V14Reloc.
(* [comment removed for export] *)







Lemma v14_lenv_ok1 : @PFSpec.ls_ok1 v14_reloc (@LG v14_reloc) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma v14_lenv_ok2 : @PFSpec.ls_ok2 v14_reloc (@LG v14_reloc) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition v14_lenv_vl : RelocLeptEnvVL v14_reloc := {| rl_lenv_ok1 := v14_lenv_ok1; rl_lenv_ok2 := v14_lenv_ok2 |}.
End V14LeptEnv.

From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require CatSim.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require SeqExec.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require StepTac.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require WalkTac.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require MmapSim.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require RefMemcpyLib.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Musl Require MemcpyBase.
Module V14MemcpyBase.
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
Import OSSVerify.leptonica.graymorph_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.SeqExec.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.StepTac.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.StoreOk.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.WalkTac.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.MmapSim.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.RefMemcpyLib.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Reloc.Reloc.
Import V14Reloc.
(* [comment removed for export] *)








Import ListNotations.
Open Scope bv_scope.

Abbreviation RSEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)
Abbreviation mcH := (@MemcpyBase.mcH v14_reloc).
Abbreviation MCH := (@MemcpyBase.MCH v14_reloc).

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
End V14MemcpyBase.

From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Reloc Require RelocCode.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Reloc Require CanonCode.
Module V14RelocCode.
Import Stdlib.ZArith.ZArith.
Import Stdlib.Lists.List.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Reloc.Reloc.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Reloc.RelocCode.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Reloc.CanonCode.
Import V14Reloc.
(* [comment removed for export] *)





Lemma v14_code_ok : code_check (@rl_segs v14_reloc) (@rl_delta v14_reloc) canon_code = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Definition v14_code : RelocCode v14_reloc := {| rl_code_ok := v14_code_ok |}.
End V14RelocCode.

From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require StreamSim.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Reloc Require RelocImg.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Reloc Require CanonImg.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Reloc Require RelocSpan.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Reloc Require CanonSpans.
Module V14RelocImg.
Import Stdlib.ZArith.ZArith.
Import Stdlib.Lists.List.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.StreamSim.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Reloc.Reloc.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Reloc.RelocImg.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Reloc.CanonImg.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Reloc.RelocSpan.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Reloc.CanonSpans.
Import V14Reloc.
(* [comment removed for export] *)





Local Open Scope Z_scope.

Lemma v14_cells_ok : @cells_check v14_reloc canon_cells = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Definition v14_img : RelocImg v14_reloc := {| rl_cells_ok := v14_cells_ok |}.

Lemma v14_data_wseg : wseg_ok (@rl_segs v14_reloc) (Z_to_bv 64 0x33000) (Z.to_nat (@rl_img_hi v14_reloc - 0x33000)) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma v14_data_ok : (0 <=? 0x33000) && (0x33000 <=? @rl_img_hi v14_reloc) && (@rl_img_hi v14_reloc <=? 2^32) = true.
Proof. reflexivity. Qed.

Definition v14_data : RelocData v14_reloc := {| rl_data_lo := 0x33000; rl_data_ok := v14_data_ok; rl_data_wseg := v14_data_wseg |}.

Lemma v14_hull_ok : @hull_okb v14_reloc v14_data = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma v14_spans_ok : @spans_check v14_reloc v14_data canon_spans = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma v14_orders_ok : @orders_check v14_reloc canon_spans canon_order = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition v14_spans : RelocSpans v14_reloc v14_data := {| rl_hull_ok := v14_hull_ok; rl_spans_ok := v14_spans_ok; rl_orders_ok := v14_orders_ok |}.
End V14RelocImg.

From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng Require RelocLayout.
Module V14RelocML.
Import Stdlib.ZArith.ZArith.
Import Stdlib.NArith.NArith.
Import Stdlib.Lists.List.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng.MallocLayout.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng.RelocLayout.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Reloc.Reloc.
Import V14MallocLayout.
Import V14Reloc.
(* [comment removed for export] *)







Lemma lv14_reloc : LU16 = reloc_layout v14_reloc.
Proof. unfold LU16, reloc_layout. f_equal; first [ reflexivity | apply bv_eq; reflexivity ]. Qed.

(* [comment removed for export] *)
Ltac v14_ml_tail t := rewrite lv14_reloc; exact t.
End V14RelocML.

From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Reloc Require RelocSites.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Reloc Require CanonSites.
Module V14RelocSites.
Import Stdlib.ZArith.ZArith.
Import Stdlib.Lists.List.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Reloc.Reloc.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Reloc.RelocCode.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Reloc.RelocSites.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Reloc.CanonSites.
Import V14Reloc.
(* [comment removed for export] *)





Lemma v14_sites_ok : @sites_check v14_reloc canon_sites = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Definition v14_sites : RelocSites v14_reloc := {| rl_sites_ok := v14_sites_ok |}.
End V14RelocSites.

From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Reloc Require CanonCodeVL.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Reloc Require CanonSitesVL.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Reloc Require CanonImgVL.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica Require RelocLept.
Module V14RelocVL.
Import Stdlib.ZArith.ZArith.
Import Stdlib.Lists.List.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Reloc.Reloc.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Reloc.RelocCode.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Reloc.RelocSites.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Reloc.RelocImg.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Reloc.CanonCodeVL.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Reloc.CanonSitesVL.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Reloc.CanonImgVL.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica.RelocLept.
Import V14Reloc.
(* [comment removed for export] *)






Lemma v14_code_vl_ok : code_check (@rl_segs v14_reloc) (@rl_delta v14_reloc) canon_code_VL = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition v14_code_vl : RelocCodeVL v14_reloc := {| rl_code_vl_ok := v14_code_vl_ok |}.

Lemma v14_sites_vl_ok : @sites_check v14_reloc canon_sites_VL = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition v14_sites_vl : RelocSitesVL v14_reloc := {| rl_sites_vl_ok := v14_sites_vl_ok |}.

Lemma v14_lept_ok : wr_readable_chk (@rl_segs v14_reloc) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition v14_lept : RelocLept v14_reloc := {| rl_wr_readable_ok := v14_lept_ok; rl_pages_ok := eq_refl; rl_clr_extra := nil |}.

Lemma v14_strs_vl_ok : @strs_check v14_reloc canon_strs_VL = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma v14_cells_vl_ok : @cells_check v14_reloc canon_cells_VL = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma v14_spans_vl_ok : @RelocLept.spans_check v14_reloc canon_spans_VL = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition v14_img_vl : RelocImgVL v14_reloc := {| rl_strs_vl_ok := v14_strs_vl_ok; rl_cells_vl_ok := v14_cells_vl_ok; rl_spans_vl_ok := v14_spans_vl_ok |}.
End V14RelocVL.

From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require ExitSim.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require ShapeAlg.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require Nodes.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica Require LibAtomic.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require SumWalkTac.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require RefNodes.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Musl Require ExitBase.
Module V14ExitBase.
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
Import OSSVerify.leptonica.graymorph_fuzzer.images.Ubsan.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Import LinuxProcessSemantics.LinuxProcessSem.Fs.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.LinuxProcessSem.Monad.
Import LinuxProcessSemantics.LinuxProcessSem.Specs.
Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.SeqExec.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.StepTac.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.WalkTac.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.StoreOk.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.StreamSim.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.MmapSim.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.ExitSim.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Nodes.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica.LibAtomic.
Export OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica.SumWalkTac.
Export OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.RefNodes.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)












Import ListNotations.
Open Scope bv_scope.
#[local] Existing Instance PropExec.fx0.   (* [comment removed for export] *)

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation RSEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section VP2.
Lemma store_ok_data : forall m (a : word) n,
  (0x33000 <= bv_unsigned a)%Z -> (bv_unsigned a + Z.of_nat n <= 0x65000)%Z ->
  store_ok RSEGS m a n = true.
Proof.
  exact (@ExitBase.store_ok_data V14Reloc.v14_reloc V14RelocImg.v14_data).
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
  rdn RSEGS mem (Z_to_bv 64 0x643cb) 1%nat = Some [Z_to_bv 8 0]            (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0x647f8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))       (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0x647e8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))       (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0x33fd8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x33ef0)) (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0x33ee8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x33e00)). (* [comment removed for export] *)

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End V14ExitBase.

From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require MuslStrlen.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica Require PortLib.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Musl Require Memchr.
Module V14Memchr.
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
Import OSSVerify.leptonica.graymorph_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.SeqExec.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.StepTac.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.StoreOk.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.WalkTac.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.MmapSim.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.MuslStrlen.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.RefMemcpyLib.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica.PortLib.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Reloc.Reloc.
Import V14Reloc.
Import V14MemcpyBase.
(* [comment removed for export] *)










Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition rodata_clear (mem : word -> option byte) : Prop :=
  forall i, (0x11530 <= i < 0x11548)%Z -> mem (Z_to_bv 64 i) = None.

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
Lemma mchrH_generic : forall mem s buf K n, mchrH mem s buf K n -> @Memchr.mchrH v14_reloc mem s buf K n.
Proof.
  intros mem s buf K n [H1 H2 H3 H4 H5 H6 H7 H8 H9].
  exact (@Memchr.MCHRH v14_reloc mem s buf K n H1 H2 H3 H4 H5 H6 H7 H8
           (@Memchr.rodata_clear_hull v14_reloc mem 0x11530 0x11548 eq_refl H9)).      (* [comment removed for export] *)
Qed.
End V14Memchr.

From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Musl Require Memcpy.
Module V14Memcpy.
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
Import OSSVerify.leptonica.graymorph_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.SeqExec.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.StepTac.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.StoreOk.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.WalkTac.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.MmapSim.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.RefMemcpyLib.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Reloc.Reloc.
Import V14Reloc.
Import V14RelocCode.
Import V14MemcpyBase.
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
      msteps RSEGS (mkst regs (0x31354 : word) mem0 rom) (mkst regs' ret (wbytes mem0 dst bs) rom)
      /\ keeps regs regs'.
  Proof. rl_tail (@Memcpy.ref_memcpy fx v14_reloc v14_code). Qed.
End Contract.
End V14Memcpy.

From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require PureModel.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica Require SumWalkTac.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica Require WalksLib.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Musl Require Memset.
Module V14Memset.
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
Import OSSVerify.leptonica.graymorph_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.StartupTac.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.RefMemcpyLib.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.PureModel.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica.SumWalkTac.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica.WalksLib.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Reloc.Reloc.
Import V14Reloc.
Import V14RelocCode.
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
      msteps SEGS (mkst regs (0x31758 : word) M rom) (mkst regs' ret (zf M d [(0, n)]%Z) rom)
      /\ getr regs' 10 = Z_to_bv 64 d
      /\ regs_agree (fun r => In r memset_clob) regs regs'.
  Proof. rl_tail (@Memset.memset_spec fx v14_reloc v14_code). Qed.

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
    realizes SEGS (mkCfg (mkst regs (0x31758 : word) M rom) model) S.
  Proof. rl_tail (@Memset.memset_at fx v14_reloc v14_code). Qed.
End Contract.
End V14Memset.

From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng Require RefStmts.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng Require RRef_calloc.
Module V14Ref_calloc.
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
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng.MallocLayout.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng.RefStmts.
Import V14MallocLayout.
Import V14Reloc.
Import V14RelocCode.
Import V14RelocSites.
Import V14RelocML.
(* [comment removed for export] *)







Section Calloc.
Context {fx : FPState}.

Theorem calloc_refines : calloc_stmt.
Proof. v14_ml_tail (@RRef_calloc.calloc_refines fx v14_reloc v14_code v14_sites). Qed.
End Calloc.
End V14Ref_calloc.

From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng Require RRef_free.
Module V14Ref_free.
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
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng.MallocLayout.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng.RefStmts.
Import V14MallocLayout.
Import V14Reloc.
Import V14RelocCode.
Import V14RelocSites.
Import V14RelocML.
(* [comment removed for export] *)







Section Free.
Context {fx : FPState}.

Theorem free_refines : free_stmt.
Proof. v14_ml_tail (@RRef_free.free_refines fx v14_reloc v14_code v14_sites). Qed.
End Free.
End V14Ref_free.

From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng Require RRef_malloc.
Module V14Ref_malloc.
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
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng.MallocLayout.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng.RefStmts.
Import V14MallocLayout.
Import V14Reloc.
Import V14RelocCode.
Import V14RelocSites.
Import V14RelocML.
(* [comment removed for export] *)







Section Malloc.
Context {fx : FPState}.

Theorem malloc_refines : malloc_stmt.
Proof. v14_ml_tail (@RRef_malloc.malloc_refines fx v14_reloc v14_code v14_sites). Qed.
End Malloc.
End V14Ref_malloc.

From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica Require PFLib.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Reloc Require RelocBlocks.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Musl Require RelocRW.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Musl Require RelocPF.
Module V14RelocMusl.
Import Stdlib.ZArith.ZArith.
Import Stdlib.Lists.List.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica.PFLib.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Reloc.Reloc.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Reloc.RelocBlocks.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Reloc.RelocImg.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Reloc.RelocSpan.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Reloc.CanonSpans.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Musl.RelocRW.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Musl.RelocPF.
Import V14Reloc.
Import V14RelocImg.
(* [comment removed for export] *)






Local Open Scope Z_scope.

Lemma v14_dwin_bounds : @dwin_bounds_chk v14_reloc v14_data = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition v14_rw : RelocRW v14_reloc v14_data := {| rl_dwin_bounds := v14_dwin_bounds; rl_rw_hull := v14_hull_ok; rl_rw_spans := v14_spans_ok; rl_rw_orders := v14_orders_ok |}.

Lemma v14_segs_lo : segs_lo (@rl_segs v14_reloc) = @rl_img_lo v14_reloc.
Proof. vm_cast_no_check (@eq_refl Z (@rl_img_lo v14_reloc)). Qed.
Lemma v14_segs_hi : segs_hi (@rl_segs v14_reloc) = @rl_img_hi v14_reloc.
Proof. vm_cast_no_check (@eq_refl Z (@rl_img_hi v14_reloc)). Qed.
Lemma v14_pf_bounds : @pf_bounds_chk v14_reloc = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma v14_pf_prefix : pf_prefix_ok (@rl_segs v14_reloc) (0x102e7 + @rl_delta v14_reloc B_S_102e7) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition v14_pf : RelocPF v14_reloc :=
  {| rl_segs_lo_val := v14_segs_lo; rl_segs_hi_val := v14_segs_hi; rl_pf_bounds := v14_pf_bounds; rl_pf_prefix := v14_pf_prefix |}.
End V14RelocMusl.

From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Musl Require RelocStart.
Module V14RelocStart.
Import Stdlib.ZArith.ZArith.
Import Stdlib.Lists.List.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Reloc.Reloc.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Reloc.RelocBlocks.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Reloc.RelocImg.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Musl.RelocStart.
Import V14Reloc.
Import V14RelocImg.
(* [comment removed for export] *)





Local Open Scope Z_scope.

Lemma v14_start_ok : start_ok (@rl_delta v14_reloc 8%positive) (@rl_data_lo v14_reloc v14_data) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition v14_start : RelocStart v14_reloc v14_data := {| rl_start_ok := v14_start_ok |}.
End V14RelocStart.

From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require VmLedger.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require AllocIface.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng Require MallocTree.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng Require MallocOps.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng Require MallocIface.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng Require MallocInv_defs.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng Require MallocIfaceX.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng Require MallocInv_aslot_iface.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng Require MallocInv_malloc_iface.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng Require MallocInv_aslot.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng Require MallocInv_mal6.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng Require MallocInv_calloc2.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng Require MallocInv_freetopX.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng Require AllocBase.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng Require AllocCalloc.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng Require MallocAllocLayout.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng Require MallocGlue.
Module V14Alloc.
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
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.PureModel.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.VmLedger.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.AllocIface.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng.MallocLayout.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng.MallocTree.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng.MallocOps.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng.MallocIface.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng.MallocInv_defs.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng.MallocIfaceX.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng.MallocInv_aslot_iface.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng.MallocInv_malloc_iface.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng.MallocInv_aslot.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng.MallocInv_mal6.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng.MallocInv_calloc2.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng.MallocInv_freetopX.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng.AllocBase.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng.MallocAllocLayout.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng.MallocGlue.
Import V14MallocLayout.
Import V14Ref_malloc.
Import V14Ref_free.
Import V14Ref_calloc.
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
End V14Alloc.

From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica Require SumSpecs.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica Require PFSpecLib.
Module V14PFSpec.
Import Stdlib.ZArith.ZArith.
Import Stdlib.Lists.List.
Import Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OSSVerify.leptonica.graymorph_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica.SumSpecs.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica.PFLib.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica.PFSpecLib.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Reloc.Reloc.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Reloc.RelocCode.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Reloc.RelocSites.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Reloc.RelocImg.
Import V14Reloc.
Import V14RelocCode.
Import V14RelocSites.
Import V14RelocImg.
Import V14RelocMusl.
Import V14PFBase.
(* [comment removed for export] *)








Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition ls_ok (nS : nat) (fmts : list Z) (L : SSP.ls_addrs) : bool := @PFSpec.ls_ok v14_reloc nS fmts L.
Definition ls_ok1 (L : SSP.ls_addrs) : bool := ls_ok 1 (SSP.ls_fmts1 L) L.
Definition ls_ok2 (L : SSP.ls_addrs) : bool := ls_ok 2 (SSP.ls_fmts2 L) L.

Section Contracts.
Context {fx : FPState}.
#[local] Existing Instance v14_reloc.
#[local] Existing Instance v14_code.
#[local] Existing Instance v14_sites.
#[local] Existing Instance v14_data.
#[local] Existing Instance v14_img.
#[local] Existing Instance v14_rw.
#[local] Existing Instance v14_pf.

(* [comment removed for export] *)
Theorem lept_stderr_s1_contract : forall L, ls_ok1 L = true -> SSP.sum_contract SEGS (SSP.spec_lept_stderr_s1 L).
Proof. exact PFSpec.lept_stderr_s1_contract. Qed.

(* [comment removed for export] *)
Theorem lept_stderr_s2_contract : forall L, ls_ok2 L = true -> SSP.sum_contract SEGS (SSP.spec_lept_stderr_s2 L).
Proof. exact PFSpec.lept_stderr_s2_contract. Qed.
End Contracts.
End V14PFSpec.

From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.CliDriver Require Amb.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require RefNodesMF.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Musl Require StartupBase.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Musl Require StartupDefs.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Musl Require Startup.
Module V14Startup.
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
Import OSSVerify.leptonica.graymorph_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.CliDriver.Amb.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.PureModel.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.RefNodesMF.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.StartupTac.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.ArgvEnv.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.RefLayout.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Reloc.Reloc.
Import V14StartupDefs.
Import V14Reloc.
Import V14RelocCode.
Import V14RelocSites.
Import V14RelocImg.
Import V14RelocMusl.
Import V14RelocStart.
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
              (Z_to_bv 64 0x297e0) (pn_w sp0 av ev) s1v (Z_to_bv 64 0x643c8)
              (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) in
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes J6
    (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 0x297e8)))   (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))           (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))          (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)))          (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0)))          (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0)))          (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 0x299dc)))    (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (argv_w sp0)))             (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av)))              (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 0x2992c)))    (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 96)) (word_to_le_bytes 8 (Z_to_bv 64 0x32d00)).    (* [comment removed for export] *)

(* [comment removed for export] *)
Record main_entry {AMB : Amb} (sp0 : word) (av ev : list (list byte)) (tid : word)
       (regs : bvmap 5 word) (mem : word -> option byte) : Prop := {
  me_ra  : getr regs 1 = Z_to_bv 64 0x299ec;
  me_sp  : getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 48);
  me_gp  : getr regs 3 = Z_to_bv 64 0x10800;
  me_tp  : getr regs 4 = Z_to_bv 64 0x44140;
  me_s0  : getr regs 8 = Z_to_bv 64 (bv_unsigned sp0 + 8);
  me_s1  : getr regs 9 = argcN av;
  me_a0  : getr regs 10 = argcN av;
  me_a1  : getr regs 11 = Z_to_bv 64 (bv_unsigned sp0 + 8);
  me_a2  : getr regs 12 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av));
  me_s2  : getr regs 18 = Z_to_bv 64 0x14eb4;
  me_s3  : getr regs 19 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av));
  me_szero : forall r : reg, In r [20; 21; 22; 23; 24; 25; 26; 27]%list -> getr regs r = Z_to_bv 64 0;
  me_mem : exists (J : word -> option byte) (s1v : word),
             wfJ sp0 J /\ J = J_main sp0 av ev s1v
             /\ mem = cmem sp0 (wrap_mem RPH sp0 av ev a_uid a_hwcap a_draw) J (D_main sp0 av ev a_hwcap a_draw tid)
}.

(* [comment removed for export] *)
Lemma main_entry_L : forall {AMB : Amb} sp0 av ev tid regs mem,
  @Startup.main_entry v14_reloc AMB sp0 av ev tid regs mem -> main_entry sp0 av ev tid regs mem.
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
       realizes rsegs (mkCfg (mkst (fx:=fx0) regs (0x14eb4 : word) mem (seg_rom rsegs))
                             (with_tid tid (init_model (segments_reserved rsegs) brk mbase sp lim
                                                      (mkProcInputC argv envp fs0 stdin0)))) K) ->
    realizes rsegs (init_config rsegs rpc rph sp brk mbase a_draw lim (mkProcInputC argv envp fs0 stdin0)) K.
  Proof.
    intros brk mbase lim fs0 stdin0 K HK.
    refine (@Startup.ref_startup_sec v14_reloc v14_code v14_sites v14_img v14_data v14_rw v14_start AMB sp argv envp Hva Hve Hvsp
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
     realizes rsegs (mkCfg (mkst (fx:=fx0) regs (0x14eb4 : word) mem (seg_rom rsegs))
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
End V14Startup.

Module V14StdioDefs.
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
Import OSSVerify.leptonica.graymorph_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.SeqExec.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.StepTac.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.WalkTac.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.StoreOk.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.StreamSim.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.MmapSim.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.ExitSim.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Nodes.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica.SumWalkTac.
Export V14ExitBase.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)








Import ListNotations.
Open Scope bv_scope.
#[local] Existing Instance PropExec.fx0.   (* [comment removed for export] *)

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
  rdn RSEGS mem (Z_to_bv 64 0x32da0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x643a8))
  /\ rdn RSEGS mem (Z_to_bv 64 0x643a8) 8%nat = Some (word_to_le_bytes 8 can).

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
Lemma sw_post_store_ok : forall mem su f bufp bufsz mem' (a : word) n,
  sw_post mem su f bufp bufsz mem' ->
  store_ok RSEGS mem a n = true -> store_ok RSEGS mem' a n = true.
Proof. intros mem su f bufp bufsz mem' a n P H. eapply store_ok_mono; [apply (swp_grows _ _ _ _ _ _ P) | exact H]. Qed.
End VP2.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition atexit_none (mem : word -> option byte) : Prop :=
  rdn RSEGS mem (Z_to_bv 64 0x64190) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).

Definition atexit_one (mem : word -> option byte) : Prop :=
  rdn RSEGS mem (Z_to_bv 64 0x64190) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x64198))
  /\ rdn RSEGS mem (Z_to_bv 64 0x64188) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1))
  /\ rdn RSEGS mem (Z_to_bv 64 0x64198) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
  /\ rdn RSEGS mem (Z_to_bv 64 0x641a0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x29e94))
  /\ rdn RSEGS mem (Z_to_bv 64 0x642a0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x152dc))
  /\ rdn RSEGS mem (Z_to_bv 64 0x44044) 1%nat = Some [Z_to_bv 8 0].

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
  ec_lock : rdn RSEGS mem (Z_to_bv 64 0x643a0) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0));
  (* [comment removed for export] *)
  ec_fe   : rdn RSEGS mem (Z_to_bv 64 0x32da8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x32d08));
  ec_fs   : rdn RSEGS mem (Z_to_bv 64 0x32db0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x32d00));
  ec_fa   : rdn RSEGS mem (Z_to_bv 64 0x32d00) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x14e24));
  (* [comment removed for export] *)
  ec_comp : rdn RSEGS mem (Z_to_bv 64 0x34038) 1%nat = Some [Z_to_bv 8 0];
  ec_g1   : rdn RSEGS mem (Z_to_bv 64 0x32d48) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x29dcc));
  ec_g2   : rdn RSEGS mem (Z_to_bv 64 0x32d50) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
  (* [comment removed for export] *)
  ec_glob : stdio_globals mem;
  (* [comment removed for export] *)
  ec_err  : file_clean mem 0x33e00 wp2 rp2;
  ec_dso  : rdn RSEGS mem (Z_to_bv 64 0x33db8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x33db8));
  ec_alock : rdn RSEGS mem (Z_to_bv 64 0x64184) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0));
  ec_atexit : atexit_state mem
}.

(* [comment removed for export] *)
Record stdout_pending (mem : word -> option byte) (wb wp : Z) (bufp bufsz rp1 can : word)
       (pending : list byte) : Prop := {
  sp_lock  : rdn RSEGS mem (Z_to_bv 64 (0x33ef0 + 140)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295));
  sp_wpos  : rdn RSEGS mem (Z_to_bv 64 (0x33ef0 + 40)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wp));
  sp_wbase : rdn RSEGS mem (Z_to_bv 64 (0x33ef0 + 56)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wb));
  sp_write : rdn RSEGS mem (Z_to_bv 64 (0x33ef0 + 72)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x2c254));
  sp_buf   : rdn RSEGS mem (Z_to_bv 64 (0x33ef0 + 88)) 8%nat = Some (word_to_le_bytes 8 bufp);
  sp_bsz   : rdn RSEGS mem (Z_to_bv 64 (0x33ef0 + 96)) 8%nat = Some (word_to_le_bytes 8 bufsz);
  sp_fd    : rdn RSEGS mem (Z_to_bv 64 (0x33ef0 + 120)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1));
  sp_rpos  : rdn RSEGS mem (Z_to_bv 64 (0x33ef0 + 8)) 8%nat = Some (word_to_le_bytes 8 rp1);
  sp_rend  : rdn RSEGS mem (Z_to_bv 64 (0x33ef0 + 16)) 8%nat = Some (word_to_le_bytes 8 rp1);
  sp_range : (0x643b0 <= wb < wp /\ wp <= 0x65000)%Z;
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
    /\ ( (pending = [] /\ exists wp1 rp1, file_clean mem 0x33ef0 wp1 rp1)
       \/ (exists (wb wp : Z) (bufp bufsz rp1 can : word),
              stdout_pending mem wb wp bufp bufsz rp1 can pending
              /\ fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1))) ).

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End V14StdioDefs.

From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica Require Frame.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Musl Require Strnlen.
Module V14Strnlen.
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
Import OSSVerify.leptonica.graymorph_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.SeqExec.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.StepTac.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.StoreOk.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.WalkTac.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.MmapSim.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.RefMemcpyLib.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica.PortLib.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica.Frame.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Reloc.Reloc.
Import V14Reloc.
Import V14RelocCode.
Import V14RelocSites.
Import V14RelocImg.
Import V14MemcpyBase.
Import V14Memchr.
(* [comment removed for export] *)










Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section VP1. Context {fx : FPState}.
Theorem ref_strnlen : forall mem (s sp : word) buf K n rom regs (ret : word),
  mchrH mem s buf K n ->
  (0 < bv_unsigned s + K)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 32)) 32 = true ->
  (0x11548 <= bv_unsigned sp - 32)%Z ->
  (bv_unsigned s + Z.of_nat (length buf) <= bv_unsigned sp - 32 \/ bv_unsigned sp <= bv_unsigned s)%Z ->
  ret_ok ret -> getr regs 1 = ret -> getr regs 2 = sp ->
  getr regs 10 = s -> getr regs 11 = Z_to_bv 64 n ->
  exists regs' mem',
    msteps RSEGS (mkst regs (0x318e0 : word) mem rom) (mkst regs' ret mem' rom)
    /\ keeps_cs regs regs'
    /\ getr regs' 10 = Z_to_bv 64 K
    /\ frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - 32), 32%Z)].
Proof.
  rl_tail (fun mem s sp buf K n rom regs ret (HOK : mchrH mem s buf K n) =>
             @Strnlen.ref_strnlen fx v14_reloc v14_code v14_sites v14_img mem s sp buf K n rom regs ret
               (mchrH_generic mem s buf K n HOK)).
Qed.
End VP1.
End V14Strnlen.

From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require LibWritev.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.CliDriver Require Spec.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Musl Require StdioDefs.

From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require SpecConsts.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require SymExec.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.CliDriver Require SymExec2.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.CliDriver Require SymExec2Sound.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.CliDriver Require SymRun.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.CliDriver Require SymDrive.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.CliDriver Require SymDriveX.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.CliDriver Require LibKnowFrame.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Musl Require LibStdioCall.
Module V14LibStdioCall.
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
Import OSSVerify.leptonica.graymorph_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.SeqExec.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.StoreOk.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Nodes.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.AgentLib.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.SpecConsts.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.SymExec.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.CliDriver.SymExec2.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.CliDriver.SymExec2Sound.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.CliDriver.SymRun.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.CliDriver.SymDrive.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.CliDriver.SymDriveX.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.CliDriver.LibKnowFrame.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Reloc.Reloc.
Import V14ExitBase.
Import V14StdioDefs.
Import V14Reloc.
Import V14RelocCode.
Import V14RelocSites.
Import V14RelocImg.
Import V14RelocMusl.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)










Import ListNotations.
Import SX2. Import SX2S.
Open Scope Z_scope.
#[local] Existing Instance PropExec.fx0.   (* [comment removed for export] *)

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
Notation stdio_call := (@LibStdioCall.stdio_call v14_reloc v14_data).

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
Proof. exact (@LibStdioCall.know_ok_frame3 v14_reloc). Qed.

Lemma kimg_cut_sound : forall E M k a n, know_ok RSEGS E M k -> know_ok RSEGS E M (kimg_cut k a n).
Proof. exact (@LibStdioCall.kimg_cut_sound v14_reloc). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma sw_post_L : forall mem su f bufp bufsz mem',
  @StdioDefs.sw_post v14_reloc mem su f bufp bufsz mem' -> sw_post mem su f bufp bufsz mem'.
Proof.
  intros mem su f bufp bufsz mem' [f1 f2 f3 f4 f5].
  exact (Build_sw_post mem su f bufp bufsz mem' f1 f2 f3 f4 f5).
Qed.

Section VP17.
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
  realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x2c254) M (seg_rom RSEGS)) model)
           (t_emit (map (WriteEv (Z_to_bv 64 (sc_fd res))) (pending ++ extra)) K).
Proof.
  intros vals ebs sr kn R M model res pending extra K E HR HK Hc wb wp s l su
         H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 HCONT.
  rl_tail (@LibStdioCall.stdio_call_sound_fr _ v14_reloc v14_code v14_sites v14_data v14_rw
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
  realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x2c254) M (seg_rom RSEGS)) model)
           (t_emit (map (WriteEv (Z_to_bv 64 (sc_fd res))) (pending ++ extra)) K).
Proof.
  intros vals ebs sr kn R M model res pending extra K E HR HK Hc wb wp s l su; intros.
  eapply stdio_call_sound_fr; try eassumption. intros R' M' HR' HK' _. auto.
Qed.
End VP17.
End V14LibStdioCall.

From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require MemSplit.
Module V14StartupFacts.
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
Import OSSVerify.leptonica.graymorph_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.CliDriver.Amb.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.StartupTac.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.ArgvEnv.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.RefLayout.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.RefMemcpyLib.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.MemSplit.
Import V14StartupDefs.
Import V14Startup.
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
  [(0x44070%Z, 8%nat); (0x643d0%Z, 8%nat); (0x64430%Z, 8%nat); (0x643f8%Z, 8%nat); (0x643c0%Z, 8%nat); (0x643b8%Z, 8%nat); (0x64168%Z, 8%nat); (0x64178%Z, 8%nat); (0x64170%Z, 8%nat); (0x643e0%Z, 8%nat); (0x643e8%Z, 8%nat); (0x44150%Z, 8%nat); (0x44138%Z, 8%nat); (0x44078%Z, 8%nat); (0x643c8%Z, 1%nat); (0x440a0%Z, 4%nat); (0x44098%Z, 4%nat); (0x44110%Z, 8%nat); (0x440f0%Z, 8%nat); (0x44080%Z, 8%nat); (0x44088%Z, 8%nat); (0x44090%Z, 8%nat); (0x643a8%Z, 4%nat); (0x643ac%Z, 4%nat); (0x643a9%Z, 1%nat); (0x44130%Z, 8%nat); (0x33ff0%Z, 1%nat)].

Definition range_disjoint_b (a : Z) (n : nat) (c : Z * nat) : bool :=
  ((a + Z.of_nat n <=? fst c) || (fst c + Z.of_nat (snd c) <=? a))%Z.

Definition D_main_missb (a : Z) (n : nat) : bool :=
  forallb (range_disjoint_b a n) D_main_cells && (0 <=? a)%Z && (a + Z.of_nat n <=? 0x65000)%Z.

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
    rdn segs D (Z_to_bv 64 0x44098) 4 = Some (word_to_le_bytes 4 tid).
  Proof.
    intros segs. pose proof (u64_range tid). subst D.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    pose proof (rdn_wbytes_hit segs (word_to_le_bytes 4 tid)) as Hh.
    rewrite length_N_to_le_bytes in Hh. apply Hh. unorm; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma D_main_guard : forall segs,
    rdn segs D (Z_to_bv 64 0x643a8) 8 = Some (guard_bytes a_draw).
  Proof.
    intros segs. pose proof (u64_range tid). subst D.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel. apply rdn_guard.
  Qed.

  (* [comment removed for export] *)
  Lemma D_main_guard_at : forall i, (0 <= i < 8)%Z ->
    D (Z_to_bv 64 (0x643a8 + i)) = Some (nth (Z.to_nat i) (guard_bytes a_draw) (Z_to_bv 8 0)).
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
    rdn segs D (Z_to_bv 64 0x643a8) 8 = Some (word_to_le_bytes 8 (canary_w a_draw)).
  Proof. intros segs. rewrite <- guard_bytes_w. apply D_main_guard. Qed.

  (* [comment removed for export] *)
  Lemma D_main_pagesize : forall segs,
    rdn segs D (Z_to_bv 64 0x643f8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 4096)).
  Proof.
    intros segs. pose proof (u64_range tid). pose proof len_av. subst D.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    apply rdn_wbytes_hit8. unorm; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma D_main_environ : forall segs,
    rdn segs D (Z_to_bv 64 0x44070) 8 = Some (word_to_le_bytes 8 (envp_w sp0 av)).
  Proof.
    intros segs. pose proof (u64_range tid). pose proof len_av. subst D.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    apply rdn_wbytes_hit8. unorm; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma D_main_self : forall segs,
    rdn segs D (Z_to_bv 64 0x44078) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x44078)).
  Proof.
    intros segs. pose proof (u64_range tid). subst D.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    apply rdn_wbytes_hit8. unorm; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma D_main_canary : forall segs,
    rdn segs D (Z_to_bv 64 0x44130) 8 = Some (word_to_le_bytes 8 (canary_w a_draw)).
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
    assert (Hr : (0 <= a /\ a + Z.of_nat n <= 0x65000)%Z).
    { unfold D_main_missb in Hb. apply andb_true_iff in Hb as [Hb H2]. apply andb_true_iff in Hb as [_ H1].
      apply Z.leb_le in H1. apply Z.leb_le in H2. lia. }
    rewrite (main_entry_rdn_data sp0 av ev tid regs mem ME)
      by (rewrite stack_max_size_val; unorm; lia).
    apply D_main_miss. exact Hb.
  Qed.

  Lemma main_entry_tid : forall segs,
    rdn segs mem (Z_to_bv 64 0x44098) 4 = Some (word_to_le_bytes 4 tid).
  Proof.
    intros segs. rewrite (main_entry_rdn_data sp0 av ev tid regs mem ME)
      by (rewrite stack_max_size_val; unorm; lia). apply D_main_tid.
  Qed.

  Lemma main_entry_guard : forall segs,
    rdn segs mem (Z_to_bv 64 0x643a8) 8 = Some (guard_bytes a_draw).
  Proof.
    intros segs. rewrite (main_entry_rdn_data sp0 av ev tid regs mem ME)
      by (rewrite stack_max_size_val; unorm; lia). apply D_main_guard.
  Qed.

  Lemma main_entry_guard_w : forall segs,
    rdn segs mem (Z_to_bv 64 0x643a8) 8 = Some (word_to_le_bytes 8 (canary_w a_draw)).
  Proof. intros segs. rewrite <- guard_bytes_w. apply main_entry_guard. Qed.
End Facts.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End V14StartupFacts.

From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng Require AllocSure.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng Require MallocSure.
Module V14Sure.
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
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.PureModel.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.VmLedger.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.AllocIface.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng.MallocLayout.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng.MallocTree.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng.MallocOps.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng.MallocIface.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng.MallocInv_defs.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng.MallocIfaceX.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng.AllocBase.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng.AllocSure.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng.MallocAllocLayout.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng.MallocGlue.
Import OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng.MallocSure.
Import V14MallocLayout.
Import V14Ref_malloc.
Import V14Ref_free.
Import V14Ref_calloc.
Import V14Alloc.
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
End V14Sure.
