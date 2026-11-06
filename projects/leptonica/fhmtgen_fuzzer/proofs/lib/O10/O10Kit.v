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
From OSSVerify.leptonica.fhmtgen_fuzzer.images Require Plain.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require PropExec.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require CatExec.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require Hoare.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require AgentLib.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require MallocLayout.
Module O10MallocLayout.
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
Import OSSVerify.leptonica.fhmtgen_fuzzer.images.Plain.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AgentLib.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.MallocLayout.
(* [comment removed for export] *)





Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Module ImgS16 := Plain.

(* [comment removed for export] *)
Instance LS16 : MallocLayout := {|
  ml_segs := ImgS16.M.loaded_segments;
  IMG_LO := 0x10000; RW_LO := 0x2b000; IMG_HI := 0x5e000;

  A_LOCK           := Z_to_bv 64 0x5d3f8;
  A_CTX            := Z_to_bv 64 0x5d400;
  A_INIT_DONE      := Z_to_bv 64 0x5d408;
  A_MMAP_CTR       := Z_to_bv 64 0x5d40c;
  A_FREE_META_HEAD := Z_to_bv 64 0x5d410;
  A_AVAIL_META     := Z_to_bv 64 0x5d418;
  A_AVAIL_META_CNT := Z_to_bv 64 0x5d420;
  A_AVAIL_AREA_CNT := Z_to_bv 64 0x5d428;
  A_META_SHIFT     := Z_to_bv 64 0x5d430;
  A_AREA_HEAD      := Z_to_bv 64 0x5d438;
  A_AREA_TAIL      := Z_to_bv 64 0x5d440;
  A_AVAIL_AREAS    := Z_to_bv 64 0x5d448;
  Z_UNMAP_SEQ      := 0x5d750;
  Z_BOUNCES        := 0x5d770;
  A_SEQ            := Z_to_bv 64 0x5d790;
  A_BRK            := Z_to_bv 64 0x5d798;
  A_MALLOC_REPLACED := Z_to_bv 64 0x5d7a0;

  A_LIBC       := Z_to_bv 64 0x5d388;
  A_NEED_LOCKS := Z_to_bv 64 0x5d38b;
  A_PAGE_SIZE  := Z_to_bv 64 0x5d3b8;
  A_TP         := Z_to_bv 64 0x3d100;
  A_ERRNO      := Z_to_bv 64 0x3d05c;
  A_GOT_SSP    := Z_to_bv 64 0x2ba48;
  A_SSP        := Z_to_bv 64 0x5d368;

  A_SIZE_CLASSES  := Z_to_bv 64 0x12314;
  A_SMALL_CNT_TAB := Z_to_bv 64 0x12374;
  A_MED_CNT_TAB   := Z_to_bv 64 0x11724;
  A_DEBRUIJN      := Z_to_bv 64 0x122f4;

  PC_MALLOC      := (0x22fd4%bv : word);
  PC_FREE        := (0x22e94%bv : word);
  PC_CALLOC      := (0x22d5c%bv : word);
  PC_LIBC_FREE   := (0x22fd8%bv : word);
  PC_MALLOC_IMPL := (0x23964%bv : word);
  PC_GET_META    := (0x231a4%bv : word);
  PC_NTFREE      := (0x232b4%bv : word);
  PC_ALLOC_META  := (0x2368c%bv : word);
  PC_ALLOC_SLOT  := (0x23cd4%bv : word);
  PC_ENFRAME     := (0x24578%bv : word);
  PC_ALLZEROP    := (0x246c8%bv : word);
  PC_MMAP        := (0x248dc%bv : word);
  PC_MPROTECT    := (0x249c8%bv : word);
  PC_MUNMAP      := (0x24a10%bv : word);
  PC_VM_WAIT     := (0x248d8%bv : word);
  PC_SYSCALL_RET := (0x22d1c%bv : word);
  PC_ERRNO_LOC   := (0x22914%bv : word);
  PC_LOCK        := (0x2a5d0%bv : word);
  PC_UNLOCK      := (0x2a858%bv : word);
  PC_MEMCPY      := (0x29fc8%bv : word);
  PC_MEMSET      := (0x2a3cc%bv : word)
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
Local Abbreviation B0 := 0x10000.  Local Abbreviation B1 := 0x14000.  Local Abbreviation B2 := 0x2b000.
Local Abbreviation B3 := 0x2c000.  Local Abbreviation B4 := 0x5e000.
Local Abbreviation P0 := 4%nat.  Local Abbreviation P1 := 23%nat.  Local Abbreviation P2 := 1%nat.  Local Abbreviation P3 := 50%nat.

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

Instance LS16ok : MallocLayoutOk LS16.
Proof.
  pose proof s16_bases as B.
  split.
  - (* [comment removed for export] *) cbn. lia.
  - (* [comment removed for export] *) intros a Ha. apply seg_rom_none_of_find. apply s16_find_none. exact Ha.
  - (* [comment removed for export] *) intros m a Ha. apply wview_of_find_none. apply s16_find_none. exact Ha.
  - (* [comment removed for export] *) intros m a Ha. cbn in Ha.
    destruct (Z.lt_ge_cases (bv_unsigned a) B1).
    + apply (wview_of_find_ro _ m a SEG0); [apply s16_find_seg0; lia | reflexivity].
    + apply (wview_of_find_ro _ m a SEG1); [apply s16_find_seg1; lia | reflexivity].
  - (* [comment removed for export] *) intros m a Ha. cbn in Ha.
    destruct (Z.lt_ge_cases (bv_unsigned a) B3).
    + apply (wview_of_find_rw _ m a SEG2); [apply s16_find_seg2; lia | reflexivity |].
      pose proof (chk_range_sound _ _ _ s16_seg2_bytes (bv_unsigned a - B2) ltac:(lia)) as Hc.
      unfold chk_seg_byte in Hc. rewrite (proj1 (proj2 (proj2 (proj2 (proj2 B))))).
      destruct (segment_byte_at (seg_bytes SEG2) (Z.to_N (bv_unsigned a - B2))); [discriminate | discriminate].
    + apply (wview_of_find_rw _ m a SEG3); [apply s16_find_seg3; lia | reflexivity |].
      pose proof (chk_range_sound _ _ _ s16_seg3_bytes (bv_unsigned a - B3) ltac:(lia)) as Hc.
      unfold chk_seg_byte in Hc. rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 B))))))).
      destruct (segment_byte_at (seg_bytes SEG3) (Z.to_N (bv_unsigned a - B3))); [discriminate | discriminate].
  - (* [comment removed for export] *) intros a Ha. cbn in Ha.
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
  - (* [comment removed for export] *) apply chk_rom_bytes_sound; [apply Forall_map_mod256 | exact (proj2 (proj2 (proj2 (proj2 s16_tables))))].
  - (* [comment removed for export] *) intros a Ha. cbn in Ha. rewrite !u64_lit in Ha by lia.
    pose proof (chk_list_sound _ _ _ s16_ctx_zero (bv_unsigned a) ltac:(cbn; rewrite !u64_lit by lia; lia)) as Hc.
    unfold chk_rom_zero in Hc. rewrite Z_to_bv_bv_unsigned in Hc.
    destruct (seg_rom ml_segs a) as [v|]; [|discriminate]. apply Z.eqb_eq in Hc.
    f_equal. rewrite <- (Z_to_bv_bv_unsigned 8 v). rewrite Hc. reflexivity.
  - (* [comment removed for export] *) cbn; rewrite !u64_lit by lia; lia.
  - reflexivity.
  - apply chk_rom_bytes_sound; [apply Forall_lt256_of_chk; vm_compute; reflexivity | exact (proj1 s16_tables)].
  - apply chk_rom_bytes_sound; [apply Forall_lt256_of_chk; vm_compute; reflexivity | exact (proj1 (proj2 s16_tables))].
  - apply chk_rom_bytes_sound; [apply Forall_lt256_of_chk; vm_compute; reflexivity | exact (proj1 (proj2 (proj2 s16_tables)))].
  - apply chk_rom_bytes_sound; [apply Forall_lt256_of_chk; vm_compute; reflexivity | exact (proj1 (proj2 (proj2 (proj2 s16_tables))))].
  - (* [comment removed for export] *) repeat (apply Forall_cons || apply Forall_nil); cbv; repeat split; congruence.
Qed.
End O10MallocLayout.

From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require StoreOk.
Module O10MemPreds.
Import Stdlib.ZArith.ZArith.
Import Stdlib.NArith.NArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import OSSVerify.leptonica.fhmtgen_fuzzer.images.Plain.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StoreOk.
(* [comment removed for export] *)




Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Abbreviation RSEGS := Plain.M.loaded_segments.

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
End O10MemPreds.

Module O10PFBase.
Import OSSVerify.leptonica.fhmtgen_fuzzer.images.Plain.
(* [comment removed for export] *)

Abbreviation SEGS := Plain.M.loaded_segments.
End O10PFBase.

From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc Require Reloc.
Module O10Reloc.
Import Stdlib.ZArith.ZArith.
Import Stdlib.Lists.List.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OSSVerify.leptonica.fhmtgen_fuzzer.images.Plain.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.Reloc.
(* [comment removed for export] *)




Import ListNotations.
Local Open Scope Z_scope.

Definition o10_dtab : list (positive * Z) :=
  [(8%positive, 0); (1000%positive, 7948); (1001%positive, 7948); (1002%positive, 7948); (1003%positive, 7948); (1004%positive, 7948); (1005%positive, 7948); (1006%positive, 7948); (1007%positive, 7948); (1008%positive, 8072); (1009%positive, 8204); (1010%positive, 8204); (1011%positive, 8204); (1012%positive, 8204); (1013%positive, 8204); (1014%positive, 8204); (1015%positive, 44068); (1016%positive, 53716); (1017%positive, 53716); (1018%positive, 53716); (1019%positive, 53716); (1020%positive, 53716); (1021%positive, 53716); (1022%positive, 53704); (1023%positive, 53704); (1024%positive, 53704); (1025%positive, 54108); (1026%positive, 54108); (1027%positive, 54108); (1028%positive, 54108); (1029%positive, 54108); (1030%positive, 54108); (1031%positive, 54108); (1032%positive, 54108); (1033%positive, 54108); (1034%positive, 54108); (1035%positive, 54108); (1036%positive, 54424); (1037%positive, 54424); (1038%positive, 54424); (1039%positive, 54424); (1040%positive, 54424); (1041%positive, 54424); (1042%positive, 54424); (1043%positive, 54424); (1044%positive, 54424); (1045%positive, 54424); (1046%positive, 54424); (1047%positive, 54424); (1048%positive, 54424); (1049%positive, 54424); (1050%positive, 54424); (1051%positive, 54424); (1052%positive, 54792); (1053%positive, 54792); (1054%positive, 54792); (1055%positive, 54792); (1056%positive, 54792); (1057%positive, 54792); (1058%positive, 54792); (1059%positive, 54792); (1060%positive, 54792); (1061%positive, 54792); (1062%positive, 54792); (1063%positive, 54964); (1064%positive, 54964); (1065%positive, 54964); (1066%positive, 54964); (1067%positive, 54964); (1068%positive, 54964); (1069%positive, 54964); (1070%positive, 54964); (1071%positive, 54964); (1072%positive, 54964); (1073%positive, 54964); (1074%positive, 54964); (1075%positive, 54964); (1076%positive, 54964); (1077%positive, 54964); (1078%positive, 54964); (1079%positive, 54964); (1080%positive, 54964); (1081%positive, 54964); (1082%positive, 54964); (1083%positive, 54964); (1084%positive, 54964); (1085%positive, 54964); (1086%positive, 36144); (1087%positive, 54804); (1088%positive, 54804); (1089%positive, 54804); (1090%positive, 54804); (1091%positive, 54804); (1092%positive, 54860); (1093%positive, 54860); (1094%positive, 54860); (1095%positive, 54860); (1096%positive, 54860); (1097%positive, 54860); (1098%positive, 54860); (1099%positive, 54872); (1100%positive, 54872); (1101%positive, 54872); (3001%positive, 44068); (4000%positive, 86); (4001%positive, 533); (4002%positive, 751); (4003%positive, 751); (4004%positive, 810); (4005%positive, 810); (4006%positive, 1061); (4007%positive, 1061); (4008%positive, 1502); (4009%positive, 1740); (4010%positive, 1740); (4011%positive, 2344); (4012%positive, 2344); (4013%positive, 2570); (4014%positive, 2686); (4015%positive, 2785); (4016%positive, 3004); (4017%positive, 3101); (4018%positive, 3101); (5000%positive, 3904); (5001%positive, 3904); (5002%positive, 725); (5003%positive, 728); (5004%positive, 736); (5005%positive, 736); (5006%positive, 736); (5007%positive, 736); (5008%positive, 3816); (5009%positive, 3816); (5010%positive, 3816); (5011%positive, 4344); (5012%positive, 54880); (5013%positive, 54888); (5015%positive, 55680); (5016%positive, 54872); (5018%positive, 3100); (5019%positive, 55688); (5020%positive, 3904); (5021%positive, 736); (5022%positive, 736); (5023%positive, 736); (5024%positive, 736); (5025%positive, 736); (5026%positive, 54888); (5027%positive, 54888); (5028%positive, 54888); (5029%positive, 55624); (5030%positive, 187168); (5031%positive, 187168); (5032%positive, 187168); (5033%positive, 187168);
   (200%positive, -56432); (210%positive, -56432); (211%positive, -56432); (212%positive, -56432); (213%positive, -56432); (201%positive, -55936); (202%positive, -54964); (203%positive, -54292); (204%positive, -53672); (214%positive, -53544); (205%positive, -53480); (206%positive, -51608); (207%positive, -46864); (215%positive, -46864); (208%positive, -44600); (216%positive, -44600); (217%positive, -34176); (209%positive, -21072); (300%positive, 17); (301%positive, 17); (302%positive, 45); (303%positive, 45); (304%positive, -62); (305%positive, 108); (306%positive, 108); (307%positive, 139); (308%positive, 139); (309%positive, 304); (310%positive, 304); (311%positive, 319); (312%positive, 403); (313%positive, 418); (314%positive, 418); (315%positive, 484); (316%positive, 533); (317%positive, 609); (318%positive, 810); (319%positive, 810); (320%positive, 1035); (321%positive, 1282); (322%positive, 1310); (323%positive, 1352); (324%positive, 1390); (325%positive, 1390); (326%positive, 1502); (327%positive, 1502); (328%positive, 1527); (329%positive, 1527); (330%positive, 1527); (331%positive, 1527); (332%positive, 1592); (333%positive, 1592); (334%positive, 1669); (335%positive, 1725); (336%positive, 1749); (337%positive, 1749); (338%positive, 1774); (339%positive, 1797); (340%positive, 1797); (341%positive, 1917); (342%positive, 1968); (343%positive, 2009); (344%positive, 2025); (345%positive, 2041); (346%positive, 2140); (347%positive, 2241); (348%positive, 2241); (349%positive, 2241); (350%positive, 2297); (351%positive, 2297); (352%positive, 2313); (353%positive, 2401); (354%positive, 2456); (355%positive, 2469); (356%positive, 2469); (357%positive, 2540); (358%positive, 2613); (359%positive, 2650); (360%positive, 2743); (361%positive, 3048); (362%positive, 3061); (363%positive, 3077); (364%positive, 3077); (365%positive, 3158); (5034%positive, 54880); (1900%positive, 53704); (5035%positive, 55680); (5036%positive, 186960)].

Definition o10_stab : list (Z * Z) := [
  (0x13084, 0xffffc197); (0x13088, 0x87018193); (0x13090, 0xfffeb597); (0x13094, 0x6458593);
  (0x1309c, 0x40006f); (0x130a4, 0x17617); (0x130a8, 0x17697); (0x130ac, 0x17717);
  (0x130b0, 0xa2063783); (0x130b4, 0xa246b683); (0x130b8, 0xa2873703); (0x130c8, 0x5e80d06f);
  (0x130dc, 0x18517); (0x130e0, 0xfc850513); (0x130f8, 0x18517); (0x130fc, 0xfac50593);
  (0x13108, 0x17517); (0x1310c, 0x9d453503); (0x13118, 0xffffe517); (0x1311c, 0xa3c50513);
  (0x13120, 0x18597); (0x13124, 0xf8c58593); (0x13150, 0x18517); (0x13154, 0xf9c50513);
  (0x1316c, 0x18517); (0x13170, 0xf8050593); (0x1317c, 0x17517); (0x13180, 0x96853503);
  (0x1318c, 0x18517); (0x13190, 0x9c850513); (0x131a0, 0x17517); (0x131a4, 0x94c53503);
  (0x131b0, 0xffffe517); (0x131b4, 0x9a450513); (0x1320c, 0x2b90d0ef); (0x13220, 0x6a90d0ef);
  (0x13230, 0x18517); (0x13234, 0xebd50b13); (0x1324c, 0x671140ef); (0x13274, 0x6550d0ef);
  (0x13290, 0x62d140ef); (0x13298, 0x4f10d0ef); (0x132b4, 0x7ac150ef); (0x132c8, 0x738150ef);
  (0x1332c, 0x168000ef); (0x13340, 0x160000ef); (0x13350, 0x148000ef); (0x13368, 0x16517);
  (0x1336c, 0x78c53503); (0x13378, 0xffffb597); (0x1337c, 0x63358593); (0x13380, 0x6050f0ef);
  (0x13388, 0x16517); (0x1338c, 0x76c53503); (0x13394, 0xffffc517); (0x1339c, 0x22c50513);
  (0x133a4, 0x16517); (0x133a8, 0x75053503); (0x133b0, 0xffffb517); (0x133b8, 0x60c50513);
  (0x133c0, 0x10100ef); (0x133c8, 0x3c10d0ef); (0x133fc, 0x16517); (0x13400, 0x6f853503);
  (0x13408, 0xffffc597); (0x1340c, 0xee058593); (0x13418, 0x16517); (0x1341c, 0x6dc53503);
  (0x13424, 0xffffc597); (0x13428, 0xa8458593); (0x13430, 0x5550f0ef); (0x13438, 0x16517);
  (0x1343c, 0x6bc53503); (0x13444, 0xffffb517); (0x1344c, 0x3e450513); (0x13454, 0x77d0f0ef);
  (0x1345c, 0x7f40d0ef); (0x13460, 0x16517); (0x13464, 0x69453503); (0x1346c, 0xffffc597);
  (0x13470, 0xe6758593); (0x13478, 0x16517); (0x1347c, 0x67c53503); (0x13484, 0xffffb517);
  (0x1348c, 0x3a450513); (0x13084, 0xffffc197); (0x13084, 0xffffc197); (0x13084, 0xffffc197);
  (0x13084, 0xffffc197); (0x13084, 0xffffc197); (0x13084, 0xffffc197); (0x13084, 0xffffc197);
  (0x13084, 0xffffc197); (0x13084, 0xffffc197); (0x13084, 0xffffc197); (0x13084, 0xffffc197);
  (0x135d8, 0xffffb517); (0x135dc, 0x1e850513); (0x135e4, 0x7cc140ef); (0x13674, 0xffffc517);
  (0x13678, 0xf4f50513); (0x1367c, 0x18000ef); (0x13708, 0x640140ef); (0x13710, 0x17517);
  (0x13714, 0x37453583); (0x13744, 0xffffc517); (0x13748, 0xe7f50513); (0x1374c, 0xf49ff0ef);
  (0x1376c, 0x16597); (0x13770, 0x2885b583); (0x13778, 0x1c50f06f); (0x13780, 0x517);
  (0x13784, 0xfe450513); (0x13788, 0x17597); (0x1378c, 0x2ea5be23); (0x14d1c, 0x40006f);
  (0x15198, 0x60080ef); (0x1519c, 0x9517); (0x151a0, 0x6b053503); (0x151b4, 0x3b517);
  (0x151b8, 0x50913); (0x15204, 0x3b617); (0x15208, 0xb63c23); (0x15210, 0x3b597);
  (0x15214, 0xf8a5b623); (0x1521c, 0x3b517); (0x15220, 0x53023); (0x15238, 0xfffee517);
  (0x1523c, 0x37b50413); (0x15240, 0x9517); (0x15244, 0x61453583); (0x15248, 0x9517);
  (0x1524c, 0x61453503); (0x1527c, 0x214000ef); (0x15284, 0x5d000ef); (0x152f8, 0xfffef517);
  (0x15304, 0x1be50593); (0x15328, 0xfffef517); (0x15334, 0x18e50593); (0x15358, 0xfffef517);
  (0x15364, 0x15e50593); (0x153ac, 0xdc1ff0ef); (0x153b0, 0x9517); (0x153b4, 0x9597);
  (0x153b8, 0x4b453403); (0x153bc, 0x4b85b483); (0x15418, 0xd59ff0ef); (0x1541c, 0x517);
  (0x15420, 0x2c50313); (0x15478, 0xf25ff0ef); (0x1548c, 0x4fc000ef); (0x154b4, 0x3b597);
  (0x154b8, 0xa8058593); (0x154bc, 0x3b617); (0x154c0, 0xcf860493); (0x154d0, 0xb717);
  (0x154e0, 0x9297); (0x154e4, 0x90476f03); (0x154e8, 0x3142b283); (0x15630, 0x1b697);
  (0x15644, 0x83468513); (0x156c0, 0x60080ef); (0x156d8, 0x3b597); (0x156e4, 0x85c58513);
  (0x15700, 0x3b517); (0x15704, 0xa9c53503); (0x15768, 0xffff0617); (0x15774, 0x8bc60613);
  (0x15784, 0xfffef617); (0x15788, 0xf860613); (0x15790, 0x4000006f); (0x157c4, 0x9517);
  (0x157c8, 0x9597); (0x157cc, 0xf3053503); (0x157d0, 0xf345b403); (0x157fc, 0xfb5ff06f);
  (0x15818, 0x3a697); (0x1581c, 0x7ec68693); (0x15860, 0xdbdff0ef); (0x15864, 0xf51ff0ef);
  (0x15868, 0x160020ef); (0x15870, 0xd91ff0ef); (0x15894, 0x9517); (0x15898, 0xe5853483);
  (0x158f0, 0x4a5070ef); (0x1592c, 0x94000ef); (0x15954, 0x64000ef); (0x15968, 0x9517);
  (0x1596c, 0xd8453503); (0x15974, 0x2f8070ef); (0x1597c, 0x9517); (0x15980, 0xd7053503);
  (0x15994, 0x9517); (0x15998, 0xd5853503); (0x159dc, 0xbddff0ef); (0x159fc, 0xffdff06f);
  (0x15a1c, 0xb9dff0ef); (0x15a4c, 0x22c000ef); (0x15a58, 0x3b517); (0x15a5c, 0x9ec52503);
  (0x15a84, 0x5ec070ef); (0x15aa0, 0x5d0070ef); (0x15ae0, 0x590070ef); (0x15b0c, 0x5640706f);
  (0x15b2c, 0x41010ef); (0x15b38, 0x1440006f); (0x15b3c, 0x1910006f); (0x15b60, 0x1ac000ef);
  (0x15b94, 0xfffef717); (0x15b9c, 0x2e870713); (0x15c40, 0x3a717); (0x15c5c, 0x2b374883);
  (0x15c94, 0x3a597); (0x15c98, 0x2cc58593); (0x15ca4, 0x494070ef); (0x15cb0, 0x16c000ef);
  (0x15cbc, 0x3a517); (0x15cc0, 0x2a450513); (0x15cc4, 0x6fc070ef); (0x15ccc, 0xfb0ff0ef);
  (0x15ce0, 0x99010ef); (0x15d9c, 0x3a797); (0x15da8, 0x1cc7b783); (0x15dc8, 0xfffef797);
  (0x15dcc, 0xb478793); (0x15e34, 0x8617); (0x15e38, 0x77c63483); (0x15e84, 0x3a817);
  (0x15e88, 0xe480913); (0x15e98, 0xfffef817); (0x15e9c, 0xfe480813); (0x15f90, 0x3a697);
  (0x15f94, 0xfd868693); (0x1608c, 0xc81ff0ef); (0x161f0, 0xe8cff0ef); (0x16210, 0x8517);
  (0x16214, 0x3a053903); (0x1621c, 0x3a597); (0x16224, 0xd4458993); (0x1622c, 0x3a597);
  (0x16230, 0xcc458413); (0x1626c, 0xc5060ef); (0x1637c, 0xc8010ef); (0x163d4, 0x70010ef);
  (0x164a8, 0x88010ef); (0x164b0, 0xfcdfe0ef); (0x164c8, 0xbb4ff0ef); (0x164f8, 0xf85fe0ef);
  (0x16534, 0x3a597); (0x16538, 0xa2c58493); (0x16560, 0x6e5000ef); (0x1656c, 0x3a517);
  (0x16570, 0x98754503); (0x16578, 0x3a517); (0x1657c, 0x9e850513); (0x16580, 0x3b9060ef);
  (0x165b0, 0xfffef617); (0x165b8, 0x8ac60993); (0x16620, 0xfffef617); (0x16634, 0x85c60593);
  (0x16654, 0xba1ff0ef); (0x166c0, 0x3a517); (0x166c4, 0x83354503); (0x166cc, 0x3a517);
  (0x166d0, 0x89450513); (0x166d4, 0x265060ef); (0x16718, 0x3a517); (0x1671c, 0x84850513);
  (0x16720, 0x4a1060ef); (0x1672c, 0x64d000ef); (0x167d8, 0x64000ef); (0x167f8, 0x3c9060ef);
  (0x16828, 0xb90006f); (0x1682c, 0x39517); (0x16830, 0x73450513); (0x16834, 0x38d060ef);
  (0x16874, 0x8517); (0x16878, 0xd3c53a03); (0x16884, 0x39597); (0x16888, 0x6dc58b13);
  (0x16a04, 0xfffee597); (0x16a0c, 0x45858593); (0x16a20, 0xfffee517); (0x16a24, 0x45c50c93);
  (0x16a30, 0xfc4ff0ef); (0x16a44, 0x39597); (0x16a48, 0x4dc5b583); (0x16a5c, 0xfffee697);
  (0x16a60, 0x48068693); (0x16a8c, 0xfffee697); (0x16a90, 0x80068693); (0x16ba4, 0xfffee697);
  (0x16bac, 0x2b868693); (0x16c48, 0x498000ef); (0x16d18, 0xfffee717); (0x16d20, 0x16470713);
  (0x16ee8, 0x55c000ef); (0x170dc, 0xfa0fe0ef); (0x17108, 0xfffee797); (0x17110, 0xd7478793);
  (0x172c4, 0x39797); (0x172cc, 0xca47b783); (0x172ec, 0xfffee817); (0x172f0, 0xb9080813);
  (0x17360, 0xfffee597); (0x17364, 0xb1c58593); (0x1738c, 0xfffee517); (0x17390, 0xaf050513);
  (0x173b0, 0xfffed597); (0x173b4, 0xf185b787); (0x173e8, 0xfffed597); (0x173ec, 0xef85b787);
  (0x1746c, 0x810fe0ef); (0x17484, 0xff9fd0ef); (0x174e0, 0xf61ff0ef); (0x17528, 0xb5cfe0ef);
  (0x17538, 0x39697); (0x1753c, 0x9e86b683); (0x17564, 0xb20fe0ef); (0x17590, 0xeb1ff0ef);
  (0x175a4, 0xae0fe0ef); (0x17728, 0x664000ef); (0x17734, 0x39517); (0x17738, 0xa6c53403);
  (0x1774c, 0xd05ff0ef); (0x17790, 0x8517); (0x17794, 0x20853403); (0x177a8, 0xca9ff0ef);
  (0x177ec, 0x8517); (0x177f0, 0xbc53403); (0x17804, 0xc4dff0ef); (0x17868, 0xbe9ff0ef);
  (0x178ec, 0x7517); (0x178f0, 0xb5453a83); (0x1794c, 0xdc9fd0ef); (0x179d4, 0xd41fd0ef);
  (0x17a4c, 0xcc1fd0ef); (0x17a54, 0x1050506f); (0x17a68, 0xff1ff0ef); (0x17a74, 0xca1fd0ef);
  (0x17a9c, 0x7817); (0x17aa0, 0x9a483403); (0x17ac8, 0x3a0000ef); (0x17ae8, 0xc25fd0ef);
  (0x17b5c, 0x398050ef); (0x17b74, 0x160000ef); (0x17c54, 0xe99ff0ef); (0x17c9c, 0x525040ef);
  (0x17d14, 0xf3cff0ef); (0x17d28, 0xe75ff0ef); (0x17d38, 0x815ff0ef); (0x17d58, 0xe45ff0ef);
  (0x17d98, 0x38517); (0x17d9c, 0x41050413); (0x17da4, 0x224050ef); (0x17de4, 0x6517);
  (0x17de8, 0x5b053903); (0x17e20, 0x14c000ef); (0x17e34, 0xd70ff0ef); (0x17e94, 0xbadff0ef);
  (0x17ec0, 0xac000ef); (0x17f30, 0xd70ff0ef); (0x17f68, 0xef8fd0ef); (0x17fc4, 0x6517);
  (0x17fd0, 0x3d053603); (0x180b0, 0xa41ff0ef); (0x183d0, 0xfffed697); (0x183d4, 0xa5468693);
  (0x18444, 0x159000ef); (0x1849c, 0xfffed597); (0x184a0, 0x84058593); (0x184dc, 0x2c9000ef);
  (0x1850c, 0xfffea597); (0x18514, 0x77d58593); (0x18538, 0xfffea517); (0x1853c, 0x75150513);
  (0x18554, 0xfffec517); (0x18558, 0xa8c50b93); (0x18560, 0xd01fc0ef); (0x18568, 0xd05fc0ef);
  (0x18580, 0x159040ef); (0x18598, 0xfffea617); (0x1859c, 0x6f160613); (0x185dc, 0xfffea597);
  (0x185e0, 0x6ad58593); (0x18614, 0xfffec597); (0x18618, 0x7a858593); (0x18644, 0xfffea597);
  (0x18648, 0x64558893); (0x18680, 0xfffea517); (0x18684, 0x60950513); (0x186b8, 0xfffea597);
  (0x186bc, 0x5d158713); (0x186d0, 0xfffed697); (0x186d4, 0x92468693); (0x18734, 0x739010ef);
  (0x1876c, 0x764000ef); (0x18790, 0x6dd010ef); (0x187b4, 0xb3cff0ef); (0x187c0, 0xfffea597);
  (0x187c4, 0x4c958593); (0x187e8, 0xfffea597); (0x187f0, 0x4a158893); (0x18938, 0x3e0040ef);
  (0x18968, 0x988ff0ef); (0x1898c, 0x964ff0ef); (0x189a8, 0x948ff0ef); (0x189dc, 0x33c040ef);
  (0x18a0c, 0x8e4ff0ef); (0x18a30, 0x8c0ff0ef); (0x18a60, 0x2b8040ef); (0x18a90, 0x860ff0ef);
  (0x18ab4, 0x83cff0ef); (0x18ad0, 0x820ff0ef); (0x18b04, 0x214040ef); (0x18b34, 0xfbdfe0ef);
  (0x18b54, 0xf9dfe0ef); (0x18b70, 0x360000ef); (0x18b94, 0x33c000ef); (0x18be4, 0xe7cfc0ef);
  (0x18c18, 0x184000ef); (0x18c2c, 0x170000ef); (0x18c40, 0x15c000ef); (0x18c54, 0x148000ef);
  (0x18c68, 0x134000ef); (0x18c7c, 0x120000ef); (0x18c90, 0x10c000ef); (0x18ca4, 0xf8000ef);
  (0x18cb8, 0xe4000ef); (0x18d38, 0xd28fc0ef); (0x18d98, 0x8c9fc0ef); (0x18dac, 0xfffec697);
  (0x18db0, 0x3068693); (0x18dfc, 0x1c1010ef); (0x18eec, 0x5517); (0x18ef0, 0x4a853903);
  (0x18f24, 0x5f5030ef); (0x18f54, 0xb9dfe0ef); (0x18f74, 0xb7dfe0ef); (0x18fa0, 0xec0fc0ef);
  (0x19000, 0x5517); (0x19004, 0x39453a03); (0x1905c, 0xf1010ef); (0x19068, 0xfffea517);
  (0x19070, 0xef550513); (0x19084, 0xfffea517); (0x1908c, 0xed950513); (0x190c4, 0x91010ef);
  (0x190e0, 0xb9010ef); (0x190f0, 0x148020ef); (0x19104, 0x235010ef); (0x19118, 0x159010ef);
  (0x19154, 0xfffeb517); (0x19158, 0xf2853507); (0x1915c, 0x660010ef); (0x19170, 0x1c9010ef);
  (0x191a0, 0xd1010ef); (0x191a8, 0xfffea597); (0x191ac, 0xfffeb617); (0x191b0, 0x2e558593);
  (0x191b4, 0xbd260993); (0x19210, 0xf7dfd0ef); (0x19230, 0x58c010ef); (0x1924c, 0xf4020ef);
  (0x19258, 0xf8020ef); (0x19268, 0xfffea597); (0x1926c, 0xfffeb617); (0x19270, 0x49458593);
  (0x19274, 0xa6660993); (0x192b0, 0x269030ef); (0x192e0, 0x811fe0ef); (0x19300, 0xff0fe0ef);
  (0x1931c, 0xfd4fe0ef); (0x19338, 0xfb8fe0ef); (0x1936c, 0x1ad030ef); (0x1939c, 0xf54fe0ef);
  (0x193bc, 0xf34fe0ef); (0x19454, 0x704020ef); (0x19464, 0x5d5010ef); (0x19478, 0x774020ef);
  (0x1948c, 0x6b5010ef); (0x194a0, 0x698010ef); (0x194b4, 0x5bc010ef); (0x194c0, 0xfffeb517);
  (0x194c4, 0xbfc53503); (0x1975c, 0x60010ef); (0x19778, 0x3d9010ef); (0x19784, 0x3bd010ef);
  (0x19864, 0xfffeb797); (0x19880, 0x79078913); (0x198a0, 0x1d0010ef); (0x198b4, 0x424020ef);
  (0x198d4, 0x165010ef); (0x198e4, 0x155010ef); (0x198f8, 0x249010ef); (0x1990c, 0x22c010ef);
  (0x19934, 0x13c010ef); (0x199f4, 0x324030ef); (0x19a24, 0x8ccfe0ef); (0x19a68, 0x7d0010ef);
  (0x19a78, 0x308020ef); (0x19ab8, 0x780010ef); (0x19acc, 0x85010ef); (0x19ae0, 0xfffea517);
  (0x19ae4, 0x5bc53507); (0x19b08, 0xfe9fd0ef); (0x19b24, 0xfcdfd0ef); (0x19b50, 0x1c8030ef);
  (0x19b80, 0xf71fd0ef); (0x19ba0, 0xf51fd0ef); (0x19bc4, 0xf2dfd0ef); (0x19bec, 0x12c030ef);
  (0x19c1c, 0xed5fd0ef); (0x19c3c, 0xeb5fd0ef); (0x19c58, 0xe99fd0ef); (0x19c84, 0x94030ef);
  (0x19cb4, 0xe3dfd0ef); (0x19cd4, 0xe1dfd0ef); (0x19cf0, 0xfffea517); (0x19cf4, 0x39c53507);
  (0x19cfc, 0xfffea517); (0x19d00, 0x3b853507); (0x19d04, 0x2b9000ef); (0x19d38, 0x500010ef);
  (0x19d54, 0x5e5000ef); (0x19d70, 0x5c9000ef); (0x19d90, 0x5c0010ef); (0x19d9c, 0x4d5000ef);
  (0x1a0dc, 0x43d020ef); (0x1a110, 0x9e1fd0ef); (0x1a138, 0x9b9fd0ef); (0x1a158, 0x999fd0ef);
  (0x1a194, 0x385020ef); (0x1a1c8, 0x929fd0ef); (0x1a1f0, 0x901fd0ef); (0x1a2ec, 0x805fd0ef);
  (0x1a314, 0xfffe9597); (0x1a324, 0xdc058513); (0x1a3dc, 0xf14fd0ef); (0x1a424, 0xeccfd0ef);
  (0x1a458, 0xe98fd0ef); (0x1a484, 0xa4dfe0ef); (0x1a4ac, 0xe44fd0ef); (0x1a4c8, 0xfffe9517);
  (0x1a4cc, 0xc0c50513); (0x1a4d8, 0xe18fd0ef); (0x1a5a0, 0xd50fd0ef); (0x1a5c8, 0x909fe0ef);
  (0x1a604, 0x714020ef); (0x1a634, 0xcbcfd0ef); (0x1a654, 0xc9cfd0ef); (0x1a668, 0xff9fa0ef);
  (0x1a67c, 0x14000ef); (0x1a76c, 0xaf5fa0ef); (0x1a9d4, 0x9c000ef); (0x1a9dc, 0xfffe9517);
  (0x1a9e0, 0x6f053507); (0x1a9e4, 0xdd9ff0ef); (0x1a9f8, 0x140000ef); (0x1b34c, 0x40006f);
  (0x1ba70, 0xac000ef); (0x1bad0, 0x7c000ef); (0x1bb30, 0xfffe9597); (0x1bb34, 0x4d458593);
  (0x1c688, 0x3597); (0x1c68c, 0x17c58593); (0x1c69c, 0xf20fb06f); (0x1c6ac, 0x6697);
  (0x1c6b0, 0x66c6b403); (0x1c6c0, 0x717); (0x1c6c4, 0xad870713); (0x1c71c, 0xa7dff0ef);
  (0x1c73c, 0x8a9fd0ef); (0x1c760, 0x2617); (0x1c764, 0xcd463903); (0x1c7a0, 0x618000ef);
  (0x1c7a4, 0x517); (0x1c7b0, 0x6850513); (0x1c7dc, 0xe80fb0ef); (0x1c808, 0xef9f80ef);
  (0x1c864, 0x150000ef); (0x1c894, 0x120000ef); (0x1c940, 0xfffe8697); (0x1c944, 0x8046b683);
  (0x1c948, 0xfffe7717); (0x1c94c, 0x7ec73703); (0x1ceec, 0xfffe7597); (0x1cef0, 0xfffe7717);
  (0x1cef4, 0x2205b683); (0x1cef8, 0x20c73703); (0x1cf60, 0x951ff0ef); (0x1cf84, 0x33597);
  (0x1cf88, 0xdbb58683); (0x1cfb4, 0xda058da3); (0x1d2a4, 0xfddff06f); (0x1d2bc, 0xf4cfa0ef);
  (0x1d2dc, 0xfbdff0ef); (0x1d2f4, 0xbd0f80ef); (0x1d310, 0xbb4f806f); (0x1d338, 0xf61ff0ef);
  (0x1d344, 0xb80f806f);
  (0x2372c, 134217967); (0x23754, 244400367); (0x23760, 91415); (0x23764, 4068816131);
  (0x23774, 4294948119); (0x23778, 4294948247); (0x2377c, 2758083859); (0x23780, 3956639123);
  (0x23794, 3248484463); (0x237c4, 306184431); (0x237d4, 95639); (0x237d8, 4081420563);
  (0x237fc, 663752943); (0x23804, 91415); (0x23808, 3896849667); (0x23818, 4294948119);
  (0x2381c, 4294948247); (0x23820, 2586117395); (0x23824, 3185935763); (0x23840, 3068129391);
  (0x23870, 692113647); (0x23884, 251670767); (0x23890, 658559215); (0x23894, 91415);
  (0x23898, 3745854723); (0x238a8, 4294948119); (0x238ac, 4294948247); (0x238b0, 1563755795);
  (0x238b4, 3034940819); (0x238bc, 2938106095); (0x2393c, 91799); (0x23940, 3569792003);
  (0x23950, 4294948503); (0x23954, 4294948631); (0x23958, 1629914771); (0x2395c, 3689350931);
  (0x23978, 2577395951); (0x23984, 4294948119); (0x23988, 4294948247); (0x2398c, 2825192723);
  (0x23990, 3634726291); (0x23998, 91415); (0x2399c, 3473224963); (0x239ac, 4294944023);
  (0x239b0, 4294948247); (0x239b4, 1456801043); (0x239b8, 3592783251); (0x239c0, 91415);
  (0x239c4, 3431281923); (0x239d4, 4294948119); (0x239d8, 4294948247); (0x239dc, 118818067);
  (0x239e0, 3550840211); (0x23a00, 91799); (0x23a04, 3364271107); (0x23a14, 4294948503);
  (0x23a18, 4294948631); (0x23a1c, 1424393875); (0x23a20, 3483830035); (0x23a3c, 2371875055);
  (0x23a48, 4294948119); (0x23a4c, 4294948247); (0x23a50, 762643731); (0x23a54, 3429205395);
  (0x23a5c, 91415); (0x23a60, 3267704067); (0x23a70, 4294948119); (0x23a74, 4294948247);
  (0x23a78, 2185561363); (0x23a7c, 3387262355); (0x23aa0, 2430595183); (0x23ab0, 91415);
  (0x23ab4, 3179623683); (0x23ac4, 4294944023); (0x23ac8, 4294948247); (0x23acc, 1656030483);
  (0x23ad0, 3299181971); (0x23ae4, 91415); (0x23ae8, 3125097731); (0x23af8, 4294948119);
  (0x23afc, 4294948247); (0x23b00, 1368720659); (0x23b04, 3244656019); (0x23b10, 91415);
  (0x23b14, 3078960387); (0x23b24, 4294948119); (0x23b28, 4294948247); (0x23b2c, 4286907667);
  (0x23b30, 3198518675); (0x23b34, 4258263279); (0x23b74, 1703985391); (0x23ba0, 91415);
  (0x23ba4, 2927965443); (0x23bb4, 4294944023); (0x23bb8, 4294948247); (0x23bbc, 1617233171);
  (0x23bc0, 3047523731); (0x23bf0, 91415); (0x23bf4, 2844079363); (0x23c04, 4294944023);
  (0x23c08, 4294948247); (0x23c0c, 1103430931); (0x23c10, 318080403); (0x23c18, 3964661871);
  (0x23c60, 95639); (0x23c64, 2869278083); (0x23c74, 1762705647); (0x23c88, 1322262767);
  (0x23c94, 1729151215); (0x23ca4, 91415); (0x23ca8, 2655335683); (0x23cb8, 4294948119);
  (0x23cbc, 4294948247); (0x23cc0, 1055196435); (0x23cc4, 2945811859); (0x23cd8, 3817861231);
  (0x23d3c, 87319); (0x23d40, 1975858435); (0x23d50, 4294944023); (0x23d54, 4294948247);
  (0x23d58, 235210003); (0x23d5c, 818251155); (0x23d64, 3096440943); (0x23da0, 1635786991);
  (0x23dbc, 805314799); (0x23dd0, 87319); (0x23dd4, 801453315); (0x23de4, 4294944023);
  (0x23de8, 4294944151); (0x23dec, 3355772179); (0x23df0, 1499825555); (0x23e08, 4053786735);
  (0x23e0c, 87319); (0x23e10, 738538755); (0x23e20, 4294948119); (0x23e24, 4294944151);
  (0x23e28, 2522154259); (0x23e2c, 1436910995); (0x23e34, 4007649519); (0x23e60, 87319);
  (0x23e64, 4240782595); (0x23e74, 4294944023); (0x23e78, 4294944151); (0x23e7c, 2500134163);
  (0x23e80, 1318421907); (0x23e88, 3214925935); (0x23ea0, 87319); (0x23ea4, 3523556611);
  (0x23eb4, 4294939927); (0x23eb8, 4294940055); (0x23ebc, 1782908179); (0x23ec0, 1521845651);
  (0x23ec8, 2497699951); (0x23ee0, 87319); (0x23ee4, 3322230019); (0x23ef4, 4294939927);
  (0x23ef8, 4294940055); (0x23efc, 1581581587); (0x23f00, 1594197395); (0x23f08, 2514477167);
  (0x23f20, 87319); (0x23f24, 3188012291); (0x23f34, 4294939927); (0x23f38, 4294944151);
  (0x23f3c, 1447363859); (0x23f40, 1089832339); (0x23f48, 2162155631); (0x23fc8, 3290423535);
  (0x23fe0, 83223); (0x23fe4, 1023751427); (0x23ff8, 4294939927); (0x23ffc, 4294940055);
  (0x24000, 1325729043); (0x24004, 1837467027); (0x24008, 2198855919); (0x24010, 83223);
  (0x24014, 973419779); (0x24024, 4294939927); (0x24028, 4294940055); (0x2402c, 3527738643);
  (0x24030, 1791329683); (0x2404c, 4221554799); (0x2405c, 4002410735); (0x24068, 2321539311);
  (0x240a4, 4294944407); (0x240a8, 4177954451); (0x24190, 2798641391); (0x241a0, 79127);
  (0x241a4, 4169479427); (0x241b4, 4294935831); (0x241b8, 4294935959); (0x241bc, 15009043);
  (0x241c0, 2900723091); (0x241cc, 79127); (0x241d0, 4123342083); (0x241e0, 4294935831);
  (0x241e4, 4294935959); (0x241e8, 4055172371); (0x241ec, 2854585747); (0x241f4, 79127);
  (0x241f8, 4081399043); (0x24208, 4294931735); (0x2420c, 4294935959); (0x24210, 2125792531);
  (0x24214, 2812642707); (0x2421c, 79127); (0x24220, 4039456003); (0x24230, 4294935831);
  (0x24234, 4294935959); (0x24238, 1609893139); (0x2423c, 2770699667); (0x2425c, 2988425327);
  (0x24280, 79255); (0x24284, 3934631299); (0x24294, 4294935831); (0x24298, 4294935959);
  (0x2429c, 1529152787); (0x242a0, 2665842067); (0x242b0, 79255); (0x242b4, 3884299651);
  (0x242c4, 4294935831); (0x242c8, 4294935959); (0x242cc, 109380883); (0x242d0, 2615510419);
  (0x242d8, 2912927983); (0x242e4, 79127); (0x242e8, 3829740803); (0x242fc, 4294931735);
  (0x24300, 4294935959); (0x24304, 1997866259); (0x24308, 2556790163); (0x24310, 2854207727);
  (0x24324, 79255); (0x24328, 3762664835); (0x24338, 4294935831); (0x2433c, 4294935959);
  (0x24340, 35980563); (0x24344, 2493875603); (0x2435c, 79127); (0x24360, 3703911683);
  (0x24374, 4294935831); (0x24378, 4294935959); (0x2437c, 811926803); (0x24380, 2430961043);
  (0x24388, 79127); (0x2438c, 3657774339); (0x243a0, 4294935831); (0x243a4, 4294935959);
  (0x243a8, 2196047123); (0x243ac, 2384823699); (0x243b0, 2686435567); (0x243c4, 1049624815);
  (0x243e8, 79127); (0x243ec, 3557111043); (0x24400, 4294935831); (0x24404, 4294935959);
  (0x24408, 94700819); (0x2440c, 2284160403); (0x24438, 381722863); (0x24440, 373334255);
  (0x2444c, 79127); (0x24450, 3452253443); (0x24460, 4294935831); (0x24464, 4294935959);
  (0x24468, 1852114195); (0x2446c, 2167768467); (0x24480, 2468331631); (0x244d8, 75031);
  (0x244dc, 931476739); (0x244ec, 4294931735); (0x244f0, 4264887571); (0x244f8, 75031);
  (0x244fc, 897922307); (0x2450c, 4294935831); (0x24510, 2382693651); (0x24524, 75031);
  (0x24528, 851784963); (0x24538, 4294931735); (0x2453c, 1224017171); (0x24544, 75031);
  (0x24548, 818230531); (0x24558, 4294931735); (0x2455c, 1178928403); (0x24560, 4294935959);
  (0x24564, 3060106643); (0x24598, 4259295343); (0x2460c, 1484820719); (0x24628, 1455460591);
  (0x2463c, 75159); (0x24648, 558218243); (0x2464c, 4294935831); (0x24650, 2789542163);
  (0x24654, 4294931735); (0x24658, 2911177107); (0x246cc, 3718230255); (0x24718, 2568995055);
  (0x2473c, 3876569327); (0x24748, 3385839855); (0x24760, 793780463); (0x24778, 75031);
  (0x2477c, 226833667); (0x2478c, 4294935831); (0x24790, 4294935959); (0x24794, 3402958099);
  (0x24798, 3421865363); (0x247a0, 75031); (0x247a4, 184890627); (0x247b4, 4294931735);
  (0x247b8, 4294935959); (0x247bc, 2445608211); (0x247c0, 3379922323); (0x247e8, 3420434543);
  (0x24930, 75031); (0x24934, 4060427523); (0x24944, 4294931735); (0x24948, 4294935959);
  (0x2494c, 152372499); (0x24950, 2960491923); (0x24958, 3034558703); (0x249d8, 2640290031);
  (0x249e4, 2292162799); (0x249f0, 3708788975); (0x249fc, 2946470127); (0x24a08, 2455740655);
  (0x24a7c, 62743); (0x24a80, 1371878659); (0x24a90, 4294923543); (0x24a94, 4294923671);
  (0x24a98, 2148861203); (0x24a9c, 174425491); (0x24aa4, 62871); (0x24aa8, 1329968515);
  (0x24ab8, 4294919447); (0x24abc, 4294923671); (0x24ac0, 3884254483); (0x24ac4, 132482451);
  (0x24aec, 2416939119); (0x24bd8, 50455); (0x24bdc, 151336195); (0x24bec, 4294907159);
  (0x24bf0, 4294907415); (0x24bf4, 1177879827); (0x24bf8, 572917395); (0x24c04, 3470741743);
  (0x24c0c, 50455); (0x24c10, 96810243); (0x24c20, 4294907159); (0x24c24, 4294907287);
  (0x24c28, 1581581587); (0x24c2c, 518358419); (0x24c78, 50455); (0x24c7c, 4278531331);
  (0x24c8c, 4294911255); (0x24c90, 4294907287); (0x24c94, 2464482579); (0x24c98, 405112211);
  (0x24ca0, 50455); (0x24ca4, 4236588291); (0x24cb4, 4294907159); (0x24cb8, 4294907287);
  (0x24cbc, 1004864787); (0x24cc0, 363169171); (0x24cf8, 3378466927); (0x24d08, 50455);
  (0x24d0c, 4127536387); (0x24d1c, 4294907159); (0x24d20, 4294907287); (0x24d24, 2588214547);
  (0x24d28, 254117267); (0x24d40, 50455); (0x24d44, 4068816131); (0x24d54, 4294907159);
  (0x24d58, 4294907287); (0x24d5c, 2279933203); (0x24d60, 195397011); (0x24d98, 2467258607);
  (0x24da8, 3251593455); (0x24dd0, 3276759279); (0x24de8, 4053749999); (0x24e04, 2866778351);
  (0x24e18, 2942263535); (0x24e24, 3188678895); (0x24e28, 50455); (0x24e2c, 3825546499);
  (0x24e3c, 4294907159); (0x24e40, 4294907287); (0x24e44, 1486161171); (0x24e48, 4247094675);
  (0x24e50, 50455); (0x24e54, 3783603459); (0x24e64, 4294907159); (0x24e68, 4294907287);
  (0x24e6c, 805635347); (0x24e70, 4205151635); (0x24e78, 50455); (0x24e7c, 3741660419);
  (0x24e8c, 4294907159); (0x24e90, 4294907287); (0x24e94, 3300197651); (0x24e98, 4163208595);
  (0x24ea0, 50455); (0x24ea4, 3699717379); (0x24eb4, 4294907159); (0x24eb8, 4294907287);
  (0x24ebc, 3695510803); (0x24ec0, 4121265555); (0x24ed0, 2719961327); (0x24ed8, 50455);
  (0x24edc, 3640997123); (0x24eec, 4294907159); (0x24ef0, 4294907287); (0x24ef4, 952435987);
  (0x24ef8, 4062545299); (0x24f0c, 2945409263); (0x24f10, 50455); (0x24f14, 3582276867);
  (0x24f24, 4294911255); (0x24f28, 4294907287); (0x24f2c, 2592408851); (0x24f30, 4003825043);
  (0x24f3c, 2349822191); (0x24f48, 755015919); (0x24f5c, 3487531247); (0x24f74, 2836357359);
  (0x24f78, 50455); (0x24f7c, 3473224963); (0x24f8c, 4294907159); (0x24f90, 4294907287);
  (0x24f94, 2293564691); (0x24f98, 3894773139); (0x24fa0, 2665435375)].

Definition o10_reloc : Reloc := {|
  rl_segs := Plain.M.loaded_segments;
  rl_dtab := o10_dtab;
  rl_stab := o10_stab;
  rl_img_lo := 0x10000; rl_rw_lo := 0x2b000; rl_img_hi := 0x5e000;
  rl_dtab_ok := eq_refl |}.
End O10Reloc.

From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require StartupTac.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require ArgvEnv.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require RefLayout.
Module O10StartupDefs.
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
Import OSSVerify.leptonica.fhmtgen_fuzzer.images.Plain.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StartupTac.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ArgvEnv.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefLayout.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)





Import ListNotations.
Open Scope bv_scope.

Abbreviation RPH := Plain.M.phdrs.

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
      (Z_to_bv 64 0x5d368) (word_to_le_bytes 4 (v_lw rwa)))
      (Z_to_bv 64 0x5d36c) (word_to_le_bytes 4 (v_lw rwb)))
      (Z_to_bv 64 0x5d369) [Z_to_bv 8 0]) (Z_to_bv 64 0x5d368) 8 = Some guard_bytes.
  Proof.
    intros segs D. unfold guard_bytes.
    set (A := word_to_le_bytes 4 (v_lw rwa)). set (B := word_to_le_bytes 4 (v_lw rwb)).
    assert (HA : length A = 4%nat) by (subst A; apply length_N_to_le_bytes).
    assert (HB : length B = 4%nat) by (subst B; apply length_N_to_le_bytes).
    assert (Hin : rdn segs (wbytes D (Z_to_bv 64 0x5d368) A) (Z_to_bv 64 0x5d368) 4 = Some A).
    { rewrite <- HA at 1. apply rdn_wbytes_hit. rewrite HA. unorm. lia. }
    change 8%nat with (1 + (1 + (2 + 4)))%nat.
    apply rdn_app.
    { rewrite rdn_wbytes_out by (cbn [length]; unorm; lia).
      rewrite rdn_wbytes_out by (rewrite ?HB; unorm; lia).
      exact (SeqExec.rdn_firstn _ _ _ _ _ 1 Hin ltac:(lia)). }
    apply rdn_app.
    { change (Z_to_bv 64 381800 + nat_to_word 1) with (Z_to_bv 64 0x5d369 : word).
      exact (rdn_wbytes_hit segs [Z_to_bv 8 0] _ (Z_to_bv 64 0x5d369) ltac:(cbn [length]; unorm; lia)). }
    apply rdn_app.
    { change (Z_to_bv 64 381800 + nat_to_word 1 + nat_to_word 1) with (Z_to_bv 64 0x5d36a : word).
      rewrite rdn_wbytes_out by (cbn [length]; unorm; lia).
      rewrite rdn_wbytes_out by (rewrite ?HB; unorm; lia).
      exact (SeqExec.rdn_skipn _ _ _ _ _ 2 Hin ltac:(lia)). }
    change (Z_to_bv 64 381800 + nat_to_word 1 + nat_to_word 1 + nat_to_word 2) with (Z_to_bv 64 0x5d36c : word).
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
      (Z_to_bv 64 0x3d030) (word_to_le_bytes 8 envp_w))          (* [comment removed for export] *)
      (Z_to_bv 64 0x5d390) (word_to_le_bytes 8 auxv_w))          (* [comment removed for export] *)
      (Z_to_bv 64 0x5d3f0) (word_to_le_bytes 8 hw))            (* [comment removed for export] *)
      (Z_to_bv 64 0x5d3b8) (word_to_le_bytes 8 (Z_to_bv 64 4096))) (* [comment removed for export] *)
      (Z_to_bv 64 0x5d380) (word_to_le_bytes 8 pn_w))            (* [comment removed for export] *)
      (Z_to_bv 64 0x5d378) (word_to_le_bytes 8 progname_w).      (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition J_lsm (J : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes
    (wbytes (wbytes (wbytes (wbytes J
      (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0x225f0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 48)) (word_to_le_bytes 8 argv_w))
      (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 argc_w))
      (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0x150dc)).

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
      (Z_to_bv 64 0x5d128) (word_to_le_bytes 8 (Z_to_bv 64 0)))        (* [comment removed for export] *)
      (Z_to_bv 64 0x5d138) (word_to_le_bytes 8 (Z_to_bv 64 0)))        (* [comment removed for export] *)
      (Z_to_bv 64 0x5d130) (word_to_le_bytes 8 (Z_to_bv 64 8)))        (* [comment removed for export] *)
      (Z_to_bv 64 0x5d3a0) (word_to_le_bytes 8 (Z_to_bv 64 0xe0)))     (* [comment removed for export] *)
      (Z_to_bv 64 0x5d3a8) (word_to_le_bytes 8 (Z_to_bv 64 8)))        (* [comment removed for export] *)
      (Z_to_bv 64 0x3d110) (word_to_le_bytes 8 (Z_to_bv 64 0)))        (* [comment removed for export] *)
      (Z_to_bv 64 0x3d0f8) (word_to_le_bytes 8 (Z_to_bv 64 0x3d110)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x3d038) (word_to_le_bytes 8 (Z_to_bv 64 0x3d038)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x5d388) [Z_to_bv 8 1])                              (* [comment removed for export] *)
      (Z_to_bv 64 0x3d060) (word_to_le_bytes 4 (Z_to_bv 64 2)).        (* [comment removed for export] *)

  Definition D_tlsB (tid : word) (D : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes D
      (Z_to_bv 64 0x3d058) (word_to_le_bytes 4 tid))                   (* [comment removed for export] *)
      (Z_to_bv 64 0x3d0d0) (word_to_le_bytes 8 (Z_to_bv 64 0x5d3c0)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x3d0b0) (word_to_le_bytes 8 (Z_to_bv 64 0x3d0b0)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x3d040) (word_to_le_bytes 8 (Z_to_bv 64 0x3d038)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x3d048) (word_to_le_bytes 8 (Z_to_bv 64 0x3d038)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x3d050) (word_to_le_bytes 8 (Z_to_bv 64 0)).        (* [comment removed for export] *)

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
      (Z_to_bv 64 0x5d368) (word_to_le_bytes 4 (v_lw (rwa drw))))  (* [comment removed for export] *)
      (Z_to_bv 64 0x5d36c) (word_to_le_bytes 4 (v_lw (rwb drw))))  (* [comment removed for export] *)
      (Z_to_bv 64 0x5d369) [Z_to_bv 8 0])                     (* [comment removed for export] *)
      (Z_to_bv 64 0x3d0f0) (word_to_le_bytes 8 (canary_w drw)).     (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition D_fd (D : word -> option byte) : word -> option byte :=
    wbytes D (Z_to_bv 64 0x2cfb0) [Z_to_bv 8 1].

  (* [comment removed for export] *)
  Definition D_main (tid : word) : word -> option byte := D_fd (D_ssp (D_tls tid D_libc)).

End Defs.
End O10StartupDefs.

From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Musl Require PFSpec.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.OL Require LeptStderr.
Module O10LeptEnv.
Import Stdlib.ZArith.ZArith.
Import Stdlib.Lists.List.
Import Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.Reloc.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.OL.LeptStderr.
Import O10Reloc.
(* [comment removed for export] *)







Lemma o10_lenv_ok1 : @PFSpec.ls_ok1 o10_reloc (@LG o10_reloc) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma o10_lenv_ok2 : @PFSpec.ls_ok2 o10_reloc (@LG o10_reloc) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition o10_lenv_ol : RelocLeptEnvOL o10_reloc := {| rl_lenv_ok1 := o10_lenv_ok1; rl_lenv_ok2 := o10_lenv_ok2 |}.
End O10LeptEnv.

From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require CatSim.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require SeqExec.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require StepTac.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require WalkTac.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require MmapSim.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require RefMemcpyLib.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Musl Require MemcpyBase.
Module O10MemcpyBase.
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
Import OSSVerify.leptonica.fhmtgen_fuzzer.images.Plain.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SeqExec.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StepTac.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StoreOk.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.WalkTac.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.MmapSim.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefMemcpyLib.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.Reloc.
Import O10Reloc.
(* [comment removed for export] *)








Import ListNotations.
Open Scope bv_scope.

Abbreviation RSEGS := Plain.M.loaded_segments.

(* [comment removed for export] *)
Abbreviation mcH := (@MemcpyBase.mcH o10_reloc).
Abbreviation MCH := (@MemcpyBase.MCH o10_reloc).

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
End O10MemcpyBase.

From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc Require RelocCode.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc Require CanonCode.
Module O10RelocCode.
Import Stdlib.ZArith.ZArith.
Import Stdlib.Lists.List.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.Reloc.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.RelocCode.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.CanonCode.
Import O10Reloc.
(* [comment removed for export] *)





Lemma o10_code_ok : code_check (@rl_segs o10_reloc) (@rl_delta o10_reloc) canon_code = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Definition o10_code : RelocCode o10_reloc := {| rl_code_ok := o10_code_ok |}.
End O10RelocCode.

From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require StreamSim.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc Require RelocImg.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc Require CanonImg.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc Require RelocSpan.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc Require CanonSpans.
Module O10RelocImg.
Import Stdlib.ZArith.ZArith.
Import Stdlib.Lists.List.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StreamSim.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.Reloc.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.RelocImg.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.CanonImg.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.RelocSpan.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.CanonSpans.
Import O10Reloc.
(* [comment removed for export] *)





Local Open Scope Z_scope.

Lemma o10_cells_ok : @cells_check o10_reloc canon_cells = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Definition o10_img : RelocImg o10_reloc := {| rl_cells_ok := o10_cells_ok |}.

Lemma o10_data_wseg : wseg_ok (@rl_segs o10_reloc) (Z_to_bv 64 0x2c000) (Z.to_nat (@rl_img_hi o10_reloc - 0x2c000)) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma o10_data_ok : (0 <=? 0x2c000) && (0x2c000 <=? @rl_img_hi o10_reloc) && (@rl_img_hi o10_reloc <=? 2^32) = true.
Proof. reflexivity. Qed.

Definition o10_data : RelocData o10_reloc := {| rl_data_lo := 0x2c000; rl_data_ok := o10_data_ok; rl_data_wseg := o10_data_wseg |}.

Lemma o10_hull_ok : @hull_okb o10_reloc o10_data = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma o10_spans_ok : @spans_check o10_reloc o10_data canon_spans = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma o10_orders_ok : @orders_check o10_reloc canon_spans canon_order = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition o10_spans : RelocSpans o10_reloc o10_data := {| rl_hull_ok := o10_hull_ok; rl_spans_ok := o10_spans_ok; rl_orders_ok := o10_orders_ok |}.
End O10RelocImg.

From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require RelocLayout.
Module O10RelocML.
Import Stdlib.ZArith.ZArith.
Import Stdlib.NArith.NArith.
Import Stdlib.Lists.List.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.MallocLayout.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.RelocLayout.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.Reloc.
Import O10MallocLayout.
Import O10Reloc.
(* [comment removed for export] *)







Lemma lo10_reloc : LS16 = reloc_layout o10_reloc.
Proof. unfold LS16, reloc_layout. f_equal; first [ reflexivity | apply bv_eq; reflexivity ]. Qed.

(* [comment removed for export] *)
Ltac o10_ml_tail t := rewrite lo10_reloc; exact t.
End O10RelocML.

From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc Require RelocSites.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc Require CanonCodeOL.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc Require CanonSitesOL.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc Require CanonImgOL.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require RelocLept.
Module O10RelocOL.
Import Stdlib.ZArith.ZArith.
Import Stdlib.Lists.List.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.Reloc.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.RelocCode.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.RelocSites.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.RelocImg.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.CanonCodeOL.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.CanonSitesOL.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.CanonImgOL.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.RelocLept.
Import O10Reloc.
(* [comment removed for export] *)






Lemma o10_code_ol_ok : code_check (@rl_segs o10_reloc) (@rl_delta o10_reloc) canon_code_OL = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition o10_code_ol : RelocCodeOL o10_reloc := {| rl_code_ol_ok := o10_code_ol_ok |}.

Lemma o10_sites_ol_ok : @sites_check o10_reloc canon_sites_OL = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition o10_sites_ol : RelocSitesOL o10_reloc := {| rl_sites_ol_ok := o10_sites_ol_ok |}.

Lemma o10_lept_ok : wr_readable_chk (@rl_segs o10_reloc) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition o10_lept : RelocLept o10_reloc := {| rl_wr_readable_ok := o10_lept_ok; rl_pages_ok := eq_refl; rl_clr_extra := (cons (0x2caa8%Z, 0x2cdc8%Z) nil) |}.

Lemma o10_strs_ol_ok : @strs_check o10_reloc canon_strs_OL = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma o10_cells_ol_ok : @cells_check o10_reloc canon_cells_OL = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma o10_spans_ol_ok : @RelocLept.spans_check o10_reloc canon_spans_OL = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition o10_img_ol : RelocImgOL o10_reloc := {| rl_strs_ol_ok := o10_strs_ol_ok; rl_cells_ol_ok := o10_cells_ol_ok; rl_spans_ol_ok := o10_spans_ol_ok |}.
End O10RelocOL.

From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc Require CanonSites.
Module O10RelocSites.
Import Stdlib.ZArith.ZArith.
Import Stdlib.Lists.List.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.Reloc.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.RelocCode.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.RelocSites.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.CanonSites.
Import O10Reloc.
(* [comment removed for export] *)





Lemma o10_sites_ok : @sites_check o10_reloc canon_sites = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Definition o10_sites : RelocSites o10_reloc := {| rl_sites_ok := o10_sites_ok |}.
End O10RelocSites.

From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require ExitSim.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require ShapeAlg.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require Nodes.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require LibAtomic.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require SumWalkTac.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require RefNodes.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Musl Require ExitBase.
Module O10ExitBase.
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
Import OSSVerify.leptonica.fhmtgen_fuzzer.images.Plain.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Import LinuxProcessSemantics.LinuxProcessSem.Fs.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.LinuxProcessSem.Monad.
Import LinuxProcessSemantics.LinuxProcessSem.Specs.
Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SeqExec.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StepTac.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.WalkTac.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StoreOk.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StreamSim.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.MmapSim.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ExitSim.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Nodes.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.LibAtomic.
Export OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.SumWalkTac.
Export OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefNodes.
(* [comment removed for export] *)
(* [comment removed for export] *)












Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation RSEGS := Plain.M.loaded_segments.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section VP2.
  Context {fx : FPState}.
Lemma store_ok_data : forall m (a : word) n,
  (0x2c000 <= bv_unsigned a)%Z -> (bv_unsigned a + Z.of_nat n <= 0x5e000)%Z ->
  store_ok RSEGS m a n = true.
Proof.
  exact (@ExitBase.store_ok_data O10Reloc.o10_reloc O10RelocImg.o10_data).
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
  rdn RSEGS mem (Z_to_bv 64 0x5d38b) 1%nat = Some [Z_to_bv 8 0]            (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0x5d7b8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))       (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0x5d7a8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))       (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0x2cfa0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x2ceb8)) (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0x2ceb0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x2cdc8)). (* [comment removed for export] *)

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End O10ExitBase.

From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require MuslStrlen.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require PortLib.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Musl Require Memchr.
Module O10Memchr.
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
Import OSSVerify.leptonica.fhmtgen_fuzzer.images.Plain.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SeqExec.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StepTac.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StoreOk.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.WalkTac.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.MmapSim.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.MuslStrlen.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefMemcpyLib.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.PortLib.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.Reloc.
Import O10Reloc.
Import O10MemcpyBase.
(* [comment removed for export] *)










Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition rodata_clear (mem : word -> option byte) : Prop :=
  forall i, (0x11748 <= i < 0x11760)%Z -> mem (Z_to_bv 64 i) = None.

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
Lemma mchrH_generic : forall mem s buf K n, mchrH mem s buf K n -> @Memchr.mchrH o10_reloc mem s buf K n.
Proof.
  intros mem s buf K n [H1 H2 H3 H4 H5 H6 H7 H8 H9].
  exact (@Memchr.MCHRH o10_reloc mem s buf K n H1 H2 H3 H4 H5 H6 H7 H8
           (@Memchr.rodata_clear_hull o10_reloc mem 0x11748 0x11760 eq_refl H9)).      (* [comment removed for export] *)
Qed.
End O10Memchr.

From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Musl Require Memcpy.
Module O10Memcpy.
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
Import OSSVerify.leptonica.fhmtgen_fuzzer.images.Plain.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SeqExec.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StepTac.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StoreOk.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.WalkTac.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.MmapSim.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefMemcpyLib.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.Reloc.
Import O10Reloc.
Import O10RelocCode.
Import O10MemcpyBase.
(* [comment removed for export] *)








Import ListNotations.
Open Scope bv_scope.

Abbreviation RSEGS := Plain.M.loaded_segments.

Section Contract.
  Context {fx : FPState}.

  Theorem ref_memcpy : forall (mem0 : word -> option byte) (dst src : word) (n : Z) (bs : list byte)
      (rom : word -> option byte) (HOK : mcH mem0 dst src n bs) regs (ret : word),
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 10 = dst -> getr regs 11 = src -> getr regs 12 = Z_to_bv 64 n ->
    exists regs',
      msteps RSEGS (mkst regs (0x29fc8 : word) mem0 rom) (mkst regs' ret (wbytes mem0 dst bs) rom)
      /\ keeps regs regs'.
  Proof. rl_tail (@Memcpy.ref_memcpy fx o10_reloc o10_code). Qed.
End Contract.
End O10Memcpy.

From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require PureModel.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require SumWalkTac.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require WalksLib.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Musl Require Memset.
Module O10Memset.
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
Import OSSVerify.leptonica.fhmtgen_fuzzer.images.Plain.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StartupTac.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefMemcpyLib.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PureModel.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.SumWalkTac.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.WalksLib.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.Reloc.
Import O10Reloc.
Import O10RelocCode.
(* [comment removed for export] *)









Import ListNotations.
Open Scope bv_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Abbreviation memset_clob := Memset.memset_clob.

Section Contract.
  Context {fx : FPState}.

  Theorem memset_spec : forall regs (M rom : word -> option byte) (d n : Z) (ret : word),
    (0 <= d)%Z -> (1 <= n < 2 ^ 64)%Z -> (d + n <= 2 ^ 64)%Z ->
    store_ok SEGS M (Z_to_bv 64 d) (Z.to_nat n) = true -> ret_ok ret ->
    getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 d -> getr regs 11 = Z_to_bv 64 0 ->
    getr regs 12 = Z_to_bv 64 n ->
    exists regs',
      msteps SEGS (mkst regs (0x2a3cc : word) M rom) (mkst regs' ret (zf M d [(0, n)]%Z) rom)
      /\ getr regs' 10 = Z_to_bv 64 d
      /\ regs_agree (fun r => In r memset_clob) regs regs'.
  Proof. rl_tail (@Memset.memset_spec fx o10_reloc o10_code). Qed.

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
    realizes SEGS (mkCfg (mkst regs (0x2a3cc : word) M rom) model) S.
  Proof. rl_tail (@Memset.memset_at fx o10_reloc o10_code). Qed.
End Contract.
End O10Memset.

From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require RefStmts.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require RRef_calloc.
Module O10Ref_calloc.
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
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.MallocLayout.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.RefStmts.
Import O10MallocLayout.
Import O10Reloc.
Import O10RelocCode.
Import O10RelocSites.
Import O10RelocML.
(* [comment removed for export] *)







Section Calloc.
Context {fx : FPState}.

Theorem calloc_refines : calloc_stmt.
Proof. o10_ml_tail (@RRef_calloc.calloc_refines fx o10_reloc o10_code o10_sites). Qed.
End Calloc.
End O10Ref_calloc.

From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require RRef_free.
Module O10Ref_free.
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
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.MallocLayout.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.RefStmts.
Import O10MallocLayout.
Import O10Reloc.
Import O10RelocCode.
Import O10RelocSites.
Import O10RelocML.
(* [comment removed for export] *)







Section Free.
Context {fx : FPState}.

Theorem free_refines : free_stmt.
Proof. o10_ml_tail (@RRef_free.free_refines fx o10_reloc o10_code o10_sites). Qed.
End Free.
End O10Ref_free.

From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require RRef_malloc.
Module O10Ref_malloc.
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
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.MallocLayout.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.RefStmts.
Import O10MallocLayout.
Import O10Reloc.
Import O10RelocCode.
Import O10RelocSites.
Import O10RelocML.
(* [comment removed for export] *)







Section Malloc.
Context {fx : FPState}.

Theorem malloc_refines : malloc_stmt.
Proof. o10_ml_tail (@RRef_malloc.malloc_refines fx o10_reloc o10_code o10_sites). Qed.
End Malloc.
End O10Ref_malloc.

From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require PFLib.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc Require RelocBlocks.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Musl Require RelocRW.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Musl Require RelocPF.
Module O10RelocMusl.
Import Stdlib.ZArith.ZArith.
Import Stdlib.Lists.List.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.PFLib.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.Reloc.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.RelocBlocks.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.RelocImg.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.RelocSpan.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.CanonSpans.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Musl.RelocRW.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Musl.RelocPF.
Import O10Reloc.
Import O10RelocImg.
(* [comment removed for export] *)






Local Open Scope Z_scope.

Lemma o10_dwin_bounds : @dwin_bounds_chk o10_reloc o10_data = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition o10_rw : RelocRW o10_reloc o10_data := {| rl_dwin_bounds := o10_dwin_bounds; rl_rw_hull := o10_hull_ok; rl_rw_spans := o10_spans_ok; rl_rw_orders := o10_orders_ok |}.

Lemma o10_segs_lo : segs_lo (@rl_segs o10_reloc) = @rl_img_lo o10_reloc.
Proof. vm_cast_no_check (@eq_refl Z (@rl_img_lo o10_reloc)). Qed.
Lemma o10_segs_hi : segs_hi (@rl_segs o10_reloc) = @rl_img_hi o10_reloc.
Proof. vm_cast_no_check (@eq_refl Z (@rl_img_hi o10_reloc)). Qed.
Lemma o10_pf_bounds : @pf_bounds_chk o10_reloc = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma o10_pf_prefix : pf_prefix_ok (@rl_segs o10_reloc) (0x102e7 + @rl_delta o10_reloc B_S_102e7) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition o10_pf : RelocPF o10_reloc :=
  {| rl_segs_lo_val := o10_segs_lo; rl_segs_hi_val := o10_segs_hi; rl_pf_bounds := o10_pf_bounds; rl_pf_prefix := o10_pf_prefix |}.
End O10RelocMusl.

From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Musl Require RelocStart.
Module O10RelocStart.
Import Stdlib.ZArith.ZArith.
Import Stdlib.Lists.List.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.Reloc.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.RelocBlocks.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.RelocImg.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Musl.RelocStart.
Import O10Reloc.
Import O10RelocImg.
(* [comment removed for export] *)





Local Open Scope Z_scope.

Lemma o10_start_ok : start_ok (@rl_delta o10_reloc 8%positive) (@rl_data_lo o10_reloc o10_data) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition o10_start : RelocStart o10_reloc o10_data := {| rl_start_ok := o10_start_ok |}.
End O10RelocStart.

From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require VmLedger.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require AllocIface.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require MallocTree.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require MallocOps.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require MallocIface.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require MallocInv_defs.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require MallocIfaceX.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require MallocInv_aslot_iface.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require MallocInv_malloc_iface.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require MallocInv_aslot.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require MallocInv_mal6.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require MallocInv_calloc2.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require MallocInv_freetopX.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require AllocBase.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require AllocCalloc.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require MallocAllocLayout.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require MallocGlue.
Module O10Alloc.
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
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PureModel.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.VmLedger.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AllocIface.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.MallocLayout.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.MallocTree.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.MallocOps.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.MallocIface.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.MallocInv_defs.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.MallocIfaceX.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.MallocInv_aslot_iface.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.MallocInv_malloc_iface.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.MallocInv_aslot.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.MallocInv_mal6.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.MallocInv_calloc2.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.MallocInv_freetopX.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocBase.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.MallocAllocLayout.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.MallocGlue.
Import O10MallocLayout.
Import O10Ref_malloc.
Import O10Ref_free.
Import O10Ref_calloc.
(* [comment removed for export] *)





Import ListNotations.
Local Open Scope Z_scope.

Definition s16_alloc_slot_okW (HT : HeapTop) : alloc_slot_specW (ML:=LS16) (HT:=HT) := alloc_slot_okW (HT:=HT).

Definition s16_free_okX (HT : HeapTop) := free_okX (ML:=LS16) (HT:=HT).

Definition s16_malloc_okX (HT : HeapTop) := malloc_okX (ML:=LS16) (HT:=HT) (s16_alloc_slot_okW HT).
Definition s16_calloc_okX (HT : HeapTop) := calloc_okX (ML:=LS16) (HT:=HT) (s16_malloc_okX HT).

Definition s16_base : AllocBase (AL:=mallocng_alloc_layout (ML:=LS16)) :=
  mallocng_base (ML:=LS16) s16_malloc_okX s16_free_okX (fun fx => malloc_refines (fx:=fx)) (fun fx => free_refines (fx:=fx)).
Definition s16_calloc : AllocCalloc (AL:=mallocng_alloc_layout (ML:=LS16)) (CL:=mallocng_calloc_layout (ML:=LS16)) :=
  mallocng_calloc (ML:=LS16) s16_malloc_okX s16_free_okX s16_calloc_okX
    (fun fx => malloc_refines (fx:=fx)) (fun fx => free_refines (fx:=fx)) (fun fx => calloc_refines (fx:=fx)).
End O10Alloc.

From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require SumSpecs.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require PFSpecLib.
Module O10PFSpec.
Import Stdlib.ZArith.ZArith.
Import Stdlib.Lists.List.
Import Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OSSVerify.leptonica.fhmtgen_fuzzer.images.Plain.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.SumSpecs.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.PFLib.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.PFSpecLib.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.Reloc.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.RelocCode.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.RelocSites.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.RelocImg.
Import O10Reloc.
Import O10RelocCode.
Import O10RelocSites.
Import O10RelocImg.
Import O10RelocMusl.
Import O10PFBase.
(* [comment removed for export] *)








Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition ls_ok (nS : nat) (fmts : list Z) (L : SSP.ls_addrs) : bool := @PFSpec.ls_ok o10_reloc nS fmts L.
Definition ls_ok1 (L : SSP.ls_addrs) : bool := ls_ok 1 (SSP.ls_fmts1 L) L.
Definition ls_ok2 (L : SSP.ls_addrs) : bool := ls_ok 2 (SSP.ls_fmts2 L) L.

Section Contracts.
Context {fx : FPState}.
#[local] Existing Instance o10_reloc.
#[local] Existing Instance o10_code.
#[local] Existing Instance o10_sites.
#[local] Existing Instance o10_data.
#[local] Existing Instance o10_img.
#[local] Existing Instance o10_rw.
#[local] Existing Instance o10_pf.

(* [comment removed for export] *)
Theorem lept_stderr_s1_contract : forall L, ls_ok1 L = true -> SSP.sum_contract SEGS (SSP.spec_lept_stderr_s1 L).
Proof. exact PFSpec.lept_stderr_s1_contract. Qed.

(* [comment removed for export] *)
Theorem lept_stderr_s2_contract : forall L, ls_ok2 L = true -> SSP.sum_contract SEGS (SSP.spec_lept_stderr_s2 L).
Proof. exact PFSpec.lept_stderr_s2_contract. Qed.
End Contracts.
End O10PFSpec.

From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver Require Amb.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require RefNodesMF.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Musl Require StartupBase.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Musl Require StartupDefs.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Musl Require Startup.
Module O10Startup.
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
Import OSSVerify.leptonica.fhmtgen_fuzzer.images.Plain.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.Amb.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PureModel.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefNodesMF.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StartupTac.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ArgvEnv.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefLayout.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.Reloc.
Import O10StartupDefs.
Import O10Reloc.
Import O10RelocCode.
Import O10RelocSites.
Import O10RelocImg.
Import O10RelocMusl.
Import O10RelocStart.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)











Import ListNotations.
Open Scope bv_scope.

Abbreviation SEGS := Plain.M.loaded_segments.
Abbreviation RPH := Plain.M.phdrs.
(* [comment removed for export] *)
Local Notation rsegs := Plain.M.loaded_segments (only parsing).
Local Notation rpc := Plain.M.init_pc (only parsing).
Local Notation rph := Plain.M.phdrs (only parsing).

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
              (Z_to_bv 64 0x22454) (pn_w sp0 av ev) s1v (Z_to_bv 64 0x5d388)
              (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) in
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes J6
    (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 0x2245c)))   (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))           (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))          (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)))          (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0)))          (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0)))          (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 0x22650)))    (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (argv_w sp0)))             (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av)))              (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 0x225a0)))    (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 96)) (word_to_le_bytes 8 (Z_to_bv 64 0x2b9a8)).    (* [comment removed for export] *)

(* [comment removed for export] *)
Record main_entry {AMB : Amb} (sp0 : word) (av ev : list (list byte)) (tid : word)
       (regs : bvmap 5 word) (mem : word -> option byte) : Prop := {
  me_ra  : getr regs 1 = Z_to_bv 64 0x22660;
  me_sp  : getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 48);
  me_gp  : getr regs 3 = Z_to_bv 64 0x10800;
  me_tp  : getr regs 4 = Z_to_bv 64 0x3d100;
  me_s0  : getr regs 8 = Z_to_bv 64 (bv_unsigned sp0 + 8);
  me_s1  : getr regs 9 = argcN av;
  me_a0  : getr regs 10 = argcN av;
  me_a1  : getr regs 11 = Z_to_bv 64 (bv_unsigned sp0 + 8);
  me_a2  : getr regs 12 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av));
  me_s2  : getr regs 18 = Z_to_bv 64 0x150dc;
  me_s3  : getr regs 19 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av));
  me_szero : forall r : reg, In r [20; 21; 22; 23; 24; 25; 26; 27]%list -> getr regs r = Z_to_bv 64 0;
  me_mem : exists (J : word -> option byte) (s1v : word),
             wfJ sp0 J /\ J = J_main sp0 av ev s1v
             /\ mem = cmem sp0 (wrap_mem RPH sp0 av ev a_uid a_hwcap a_draw) J (D_main sp0 av ev a_hwcap a_draw tid)
}.

(* [comment removed for export] *)
Lemma main_entry_L : forall {AMB : Amb} sp0 av ev tid regs mem,
  @Startup.main_entry o10_reloc AMB sp0 av ev tid regs mem -> main_entry sp0 av ev tid regs mem.
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
       realizes rsegs (mkCfg (mkst (fx:=fx0) regs (0x150dc : word) mem (seg_rom rsegs))
                             (with_tid tid (init_model (segments_reserved rsegs) brk mbase sp lim
                                                      (mkProcInputC argv envp fs0 stdin0)))) K) ->
    realizes rsegs (init_config rsegs rpc rph sp brk mbase a_draw lim (mkProcInputC argv envp fs0 stdin0)) K.
  Proof.
    intros brk mbase lim fs0 stdin0 K HK.
    refine (@Startup.ref_startup_sec o10_reloc o10_code o10_sites o10_img o10_data o10_rw o10_start AMB sp argv envp Hva Hve Hvsp
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
     realizes rsegs (mkCfg (mkst (fx:=fx0) regs (0x150dc : word) mem (seg_rom rsegs))
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
End O10Startup.

Module O10StdioDefs.
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
Import OSSVerify.leptonica.fhmtgen_fuzzer.images.Plain.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SeqExec.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StepTac.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.WalkTac.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StoreOk.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StreamSim.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.MmapSim.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ExitSim.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Nodes.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.SumWalkTac.
Export O10ExitBase.
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
  rdn RSEGS mem (Z_to_bv 64 0x2ba48) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x5d368))
  /\ rdn RSEGS mem (Z_to_bv 64 0x5d368) 8%nat = Some (word_to_le_bytes 8 can).

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
  rdn RSEGS mem (Z_to_bv 64 0x5d150) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).

Definition atexit_one (mem : word -> option byte) : Prop :=
  rdn RSEGS mem (Z_to_bv 64 0x5d150) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x5d158))
  /\ rdn RSEGS mem (Z_to_bv 64 0x5d148) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1))
  /\ rdn RSEGS mem (Z_to_bv 64 0x5d158) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
  /\ rdn RSEGS mem (Z_to_bv 64 0x5d160) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x22b08))
  /\ rdn RSEGS mem (Z_to_bv 64 0x5d260) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x15504))
  /\ rdn RSEGS mem (Z_to_bv 64 0x3d004) 1%nat = Some [Z_to_bv 8 0].

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
  ec_lock : rdn RSEGS mem (Z_to_bv 64 0x5d360) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0));
  (* [comment removed for export] *)
  ec_fe   : rdn RSEGS mem (Z_to_bv 64 0x2ba50) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x2b9b0));
  ec_fs   : rdn RSEGS mem (Z_to_bv 64 0x2ba58) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x2b9a8));
  ec_fa   : rdn RSEGS mem (Z_to_bv 64 0x2b9a8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1504c));
  (* [comment removed for export] *)
  ec_comp : rdn RSEGS mem (Z_to_bv 64 0x2cff8) 1%nat = Some [Z_to_bv 8 0];
  ec_g1   : rdn RSEGS mem (Z_to_bv 64 0x2b9f0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x22a40));
  ec_g2   : rdn RSEGS mem (Z_to_bv 64 0x2b9f8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
  (* [comment removed for export] *)
  ec_glob : stdio_globals mem;
  (* [comment removed for export] *)
  ec_err  : file_clean mem 0x2cdc8 wp2 rp2;
  ec_dso  : rdn RSEGS mem (Z_to_bv 64 0x2ca60) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x2ca60));
  ec_alock : rdn RSEGS mem (Z_to_bv 64 0x5d144) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0));
  ec_atexit : atexit_state mem
}.

(* [comment removed for export] *)
Record stdout_pending (mem : word -> option byte) (wb wp : Z) (bufp bufsz rp1 can : word)
       (pending : list byte) : Prop := {
  sp_lock  : rdn RSEGS mem (Z_to_bv 64 (0x2ceb8 + 140)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295));
  sp_wpos  : rdn RSEGS mem (Z_to_bv 64 (0x2ceb8 + 40)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wp));
  sp_wbase : rdn RSEGS mem (Z_to_bv 64 (0x2ceb8 + 56)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wb));
  sp_write : rdn RSEGS mem (Z_to_bv 64 (0x2ceb8 + 72)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x24ec8));
  sp_buf   : rdn RSEGS mem (Z_to_bv 64 (0x2ceb8 + 88)) 8%nat = Some (word_to_le_bytes 8 bufp);
  sp_bsz   : rdn RSEGS mem (Z_to_bv 64 (0x2ceb8 + 96)) 8%nat = Some (word_to_le_bytes 8 bufsz);
  sp_fd    : rdn RSEGS mem (Z_to_bv 64 (0x2ceb8 + 120)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1));
  sp_rpos  : rdn RSEGS mem (Z_to_bv 64 (0x2ceb8 + 8)) 8%nat = Some (word_to_le_bytes 8 rp1);
  sp_rend  : rdn RSEGS mem (Z_to_bv 64 (0x2ceb8 + 16)) 8%nat = Some (word_to_le_bytes 8 rp1);
  sp_range : (0x5d370 <= wb < wp /\ wp <= 0x5e000)%Z;
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
    /\ ( (pending = [] /\ exists wp1 rp1, file_clean mem 0x2ceb8 wp1 rp1)
       \/ (exists (wb wp : Z) (bufp bufsz rp1 can : word),
              stdout_pending mem wb wp bufp bufsz rp1 can pending
              /\ fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1))) ).

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End O10StdioDefs.

From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require Frame.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Musl Require Strnlen.
Module O10Strnlen.
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
Import OSSVerify.leptonica.fhmtgen_fuzzer.images.Plain.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SeqExec.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StepTac.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StoreOk.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.WalkTac.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.MmapSim.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefMemcpyLib.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.PortLib.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica.Frame.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.Reloc.
Import O10Reloc.
Import O10RelocCode.
Import O10RelocSites.
Import O10RelocImg.
Import O10MemcpyBase.
Import O10Memchr.
(* [comment removed for export] *)










Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section VP1. Context {fx : FPState}.
Theorem ref_strnlen : forall mem (s sp : word) buf K n rom regs (ret : word),
  mchrH mem s buf K n ->
  (0 < bv_unsigned s + K)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 32)) 32 = true ->
  (0x11760 <= bv_unsigned sp - 32)%Z ->
  (bv_unsigned s + Z.of_nat (length buf) <= bv_unsigned sp - 32 \/ bv_unsigned sp <= bv_unsigned s)%Z ->
  ret_ok ret -> getr regs 1 = ret -> getr regs 2 = sp ->
  getr regs 10 = s -> getr regs 11 = Z_to_bv 64 n ->
  exists regs' mem',
    msteps RSEGS (mkst regs (0x2a58c : word) mem rom) (mkst regs' ret mem' rom)
    /\ keeps_cs regs regs'
    /\ getr regs' 10 = Z_to_bv 64 K
    /\ frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - 32), 32%Z)].
Proof.
  rl_tail (fun mem s sp buf K n rom regs ret (HOK : mchrH mem s buf K n) =>
             @Strnlen.ref_strnlen fx o10_reloc o10_code o10_sites o10_img mem s sp buf K n rom regs ret
               (mchrH_generic mem s buf K n HOK)).
Qed.
End VP1.
End O10Strnlen.

From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require LibWritev.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver Require Spec.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Musl Require StdioDefs.

From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require SpecConsts.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require SymExec.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver Require SymExec2.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver Require SymExec2Sound.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver Require SymRun.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver Require SymDrive.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver Require SymDriveX.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver Require LibKnowFrame.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Musl Require LibStdioCall.
Module O10LibStdioCall.
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
Import OSSVerify.leptonica.fhmtgen_fuzzer.images.Plain.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SeqExec.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StoreOk.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Nodes.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AgentLib.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SpecConsts.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.SymExec.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymExec2.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymExec2Sound.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymRun.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDrive.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.SymDriveX.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.LibKnowFrame.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc.Reloc.
Import O10ExitBase.
Import O10StdioDefs.
Import O10Reloc.
Import O10RelocCode.
Import O10RelocSites.
Import O10RelocImg.
Import O10RelocMusl.
(* [comment removed for export] *)
(* [comment removed for export] *)










Import ListNotations.
Import SX2. Import SX2S.
Open Scope Z_scope.

#[local] Abbreviation RSEGS := Plain.M.loaded_segments.

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
Notation stdio_call := (@LibStdioCall.stdio_call o10_reloc o10_data).

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
Proof. exact (@LibStdioCall.know_ok_frame3 o10_reloc). Qed.

Lemma kimg_cut_sound : forall E M k a n, know_ok RSEGS E M k -> know_ok RSEGS E M (kimg_cut k a n).
Proof. exact (@LibStdioCall.kimg_cut_sound o10_reloc). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma sw_post_L : forall mem su f bufp bufsz mem',
  @StdioDefs.sw_post o10_reloc mem su f bufp bufsz mem' -> sw_post mem su f bufp bufsz mem'.
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
  realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x24ec8) M (seg_rom RSEGS)) model)
           (t_emit (map (WriteEv (Z_to_bv 64 (sc_fd res))) (pending ++ extra)) K).
Proof.
  intros vals ebs sr kn R M model res pending extra K E HR HK Hc wb wp s l su
         H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 HCONT.
  rl_tail (@LibStdioCall.stdio_call_sound_fr _ o10_reloc o10_code o10_sites o10_data o10_rw
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
  realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x24ec8) M (seg_rom RSEGS)) model)
           (t_emit (map (WriteEv (Z_to_bv 64 (sc_fd res))) (pending ++ extra)) K).
Proof.
  intros vals ebs sr kn R M model res pending extra K E HR HK Hc wb wp s l su; intros.
  eapply stdio_call_sound_fr; try eassumption. intros R' M' HR' HK' _. auto.
Qed.
End VP17.
End O10LibStdioCall.

From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require MemSplit.
Module O10StartupFacts.
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
Import OSSVerify.leptonica.fhmtgen_fuzzer.images.Plain.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CliDriver.Amb.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.StartupTac.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ArgvEnv.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefLayout.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.RefMemcpyLib.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.MemSplit.
Import O10StartupDefs.
Import O10Startup.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)







Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation RPH := Plain.M.phdrs.

(* [comment removed for export] *)
Definition D_main_cells : list (Z * nat) :=
  [(0x3d030%Z, 8%nat); (0x5d390%Z, 8%nat); (0x5d3f0%Z, 8%nat); (0x5d3b8%Z, 8%nat); (0x5d380%Z, 8%nat); (0x5d378%Z, 8%nat); (0x5d128%Z, 8%nat); (0x5d138%Z, 8%nat); (0x5d130%Z, 8%nat); (0x5d3a0%Z, 8%nat); (0x5d3a8%Z, 8%nat); (0x3d110%Z, 8%nat); (0x3d0f8%Z, 8%nat); (0x3d038%Z, 8%nat); (0x5d388%Z, 1%nat); (0x3d060%Z, 4%nat); (0x3d058%Z, 4%nat); (0x3d0d0%Z, 8%nat); (0x3d0b0%Z, 8%nat); (0x3d040%Z, 8%nat); (0x3d048%Z, 8%nat); (0x3d050%Z, 8%nat); (0x5d368%Z, 4%nat); (0x5d36c%Z, 4%nat); (0x5d369%Z, 1%nat); (0x3d0f0%Z, 8%nat); (0x2cfb0%Z, 1%nat)].

Definition range_disjoint_b (a : Z) (n : nat) (c : Z * nat) : bool :=
  ((a + Z.of_nat n <=? fst c) || (fst c + Z.of_nat (snd c) <=? a))%Z.

Definition D_main_missb (a : Z) (n : nat) : bool :=
  forallb (range_disjoint_b a n) D_main_cells && (0 <=? a)%Z && (a + Z.of_nat n <=? 0x5e000)%Z.

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
    rdn segs D (Z_to_bv 64 0x3d058) 4 = Some (word_to_le_bytes 4 tid).
  Proof.
    intros segs. pose proof (u64_range tid). subst D.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    pose proof (rdn_wbytes_hit segs (word_to_le_bytes 4 tid)) as Hh.
    rewrite length_N_to_le_bytes in Hh. apply Hh. unorm; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma D_main_guard : forall segs,
    rdn segs D (Z_to_bv 64 0x5d368) 8 = Some (guard_bytes a_draw).
  Proof.
    intros segs. pose proof (u64_range tid). subst D.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel. apply rdn_guard.
  Qed.

  (* [comment removed for export] *)
  Lemma D_main_guard_at : forall i, (0 <= i < 8)%Z ->
    D (Z_to_bv 64 (0x5d368 + i)) = Some (nth (Z.to_nat i) (guard_bytes a_draw) (Z_to_bv 8 0)).
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
    rdn segs D (Z_to_bv 64 0x5d368) 8 = Some (word_to_le_bytes 8 (canary_w a_draw)).
  Proof. intros segs. rewrite <- guard_bytes_w. apply D_main_guard. Qed.

  (* [comment removed for export] *)
  Lemma D_main_pagesize : forall segs,
    rdn segs D (Z_to_bv 64 0x5d3b8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 4096)).
  Proof.
    intros segs. pose proof (u64_range tid). pose proof len_av. subst D.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    apply rdn_wbytes_hit8. unorm; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma D_main_environ : forall segs,
    rdn segs D (Z_to_bv 64 0x3d030) 8 = Some (word_to_le_bytes 8 (envp_w sp0 av)).
  Proof.
    intros segs. pose proof (u64_range tid). pose proof len_av. subst D.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    apply rdn_wbytes_hit8. unorm; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma D_main_self : forall segs,
    rdn segs D (Z_to_bv 64 0x3d038) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x3d038)).
  Proof.
    intros segs. pose proof (u64_range tid). subst D.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    apply rdn_wbytes_hit8. unorm; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma D_main_canary : forall segs,
    rdn segs D (Z_to_bv 64 0x3d0f0) 8 = Some (word_to_le_bytes 8 (canary_w a_draw)).
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
    assert (Hr : (0 <= a /\ a + Z.of_nat n <= 0x5e000)%Z).
    { unfold D_main_missb in Hb. apply andb_true_iff in Hb as [Hb H2]. apply andb_true_iff in Hb as [_ H1].
      apply Z.leb_le in H1. apply Z.leb_le in H2. lia. }
    rewrite (main_entry_rdn_data sp0 av ev tid regs mem ME)
      by (rewrite stack_max_size_val; unorm; lia).
    apply D_main_miss. exact Hb.
  Qed.

  Lemma main_entry_tid : forall segs,
    rdn segs mem (Z_to_bv 64 0x3d058) 4 = Some (word_to_le_bytes 4 tid).
  Proof.
    intros segs. rewrite (main_entry_rdn_data sp0 av ev tid regs mem ME)
      by (rewrite stack_max_size_val; unorm; lia). apply D_main_tid.
  Qed.

  Lemma main_entry_guard : forall segs,
    rdn segs mem (Z_to_bv 64 0x5d368) 8 = Some (guard_bytes a_draw).
  Proof.
    intros segs. rewrite (main_entry_rdn_data sp0 av ev tid regs mem ME)
      by (rewrite stack_max_size_val; unorm; lia). apply D_main_guard.
  Qed.

  Lemma main_entry_guard_w : forall segs,
    rdn segs mem (Z_to_bv 64 0x5d368) 8 = Some (word_to_le_bytes 8 (canary_w a_draw)).
  Proof. intros segs. rewrite <- guard_bytes_w. apply main_entry_guard. Qed.
End Facts.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End O10StartupFacts.

From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require AllocSure.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require MallocSure.
Module O10Sure.
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
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.PureModel.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.VmLedger.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.AllocIface.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.MallocLayout.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.MallocTree.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.MallocOps.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.MallocIface.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.MallocInv_defs.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.MallocIfaceX.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocBase.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.AllocSure.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.MallocAllocLayout.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.MallocGlue.
Import OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng.MallocSure.
Import O10MallocLayout.
Import O10Ref_malloc.
Import O10Ref_free.
Import O10Ref_calloc.
Import O10Alloc.
(* [comment removed for export] *)





Import ListNotations.
Local Open Scope Z_scope.

Definition s16_sure : AllocSure (AL:=mallocng_alloc_layout (ML:=LS16)) (CL:=mallocng_calloc_layout (ML:=LS16)) :=
  mallocng_sure (ML:=LS16) s16_malloc_okX s16_free_okX s16_calloc_okX
    (fun fx => malloc_refines (fx:=fx)) (fun fx => free_refines (fx:=fx)) (fun fx => calloc_refines (fx:=fx)).

Lemma s16_sure_calloc : asr_calloc (AllocSure:=s16_sure) = s16_calloc.
Proof. reflexivity. Qed.

Lemma s16_sure_base : aic_base (AllocCalloc:=asr_calloc (AllocSure:=s16_sure)) = s16_base.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma s16_sure_room : forall A h k b,
  aroom (AllocSure:=s16_sure) A h k b <-> g_room A h k b.
Proof. intros. reflexivity. Qed.
End O10Sure.
