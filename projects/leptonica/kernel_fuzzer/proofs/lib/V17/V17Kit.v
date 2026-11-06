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
From OSSVerify.leptonica.kernel_fuzzer.images Require Ubsan.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require PropExec.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require CatExec.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require Hoare.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require AgentLib.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng Require MallocLayout.
Module V17MallocLayout.
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
Import OSSVerify.leptonica.kernel_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.AgentLib.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.MallocLayout.
(* [comment removed for export] *)





Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Module ImgU17 := Ubsan.

(* [comment removed for export] *)
Instance LU17 : MallocLayout := {|
  ml_segs := ImgU17.M.loaded_segments;
  IMG_LO := 0x10000; RW_LO := 0x1f000; IMG_HI := 0x52000;

  A_LOCK           := Z_to_bv 64 0x51098;
  A_CTX            := Z_to_bv 64 0x510a0;
  A_INIT_DONE      := Z_to_bv 64 0x510a8;
  A_MMAP_CTR       := Z_to_bv 64 0x510ac;
  A_FREE_META_HEAD := Z_to_bv 64 0x510b0;
  A_AVAIL_META     := Z_to_bv 64 0x510b8;
  A_AVAIL_META_CNT := Z_to_bv 64 0x510c0;
  A_AVAIL_AREA_CNT := Z_to_bv 64 0x510c8;
  A_META_SHIFT     := Z_to_bv 64 0x510d0;
  A_AREA_HEAD      := Z_to_bv 64 0x510d8;
  A_AREA_TAIL      := Z_to_bv 64 0x510e0;
  A_AVAIL_AREAS    := Z_to_bv 64 0x510e8;
  Z_UNMAP_SEQ      := 0x513f0;
  Z_BOUNCES        := 0x51410;
  A_SEQ            := Z_to_bv 64 0x51430;
  A_BRK            := Z_to_bv 64 0x51438;
  A_MALLOC_REPLACED := Z_to_bv 64 0x51440;

  A_LIBC       := Z_to_bv 64 0x51028;
  A_NEED_LOCKS := Z_to_bv 64 0x5102b;
  A_PAGE_SIZE  := Z_to_bv 64 0x51058;
  A_TP         := Z_to_bv 64 0x30da0;
  A_ERRNO      := Z_to_bv 64 0x30cfc;
  A_GOT_SSP    := Z_to_bv 64 0x1fa00;
  A_SSP        := Z_to_bv 64 0x51008;

  A_SIZE_CLASSES  := Z_to_bv 64 0x11648;
  A_SMALL_CNT_TAB := Z_to_bv 64 0x116a8;
  A_MED_CNT_TAB   := Z_to_bv 64 0x116c3;
  A_DEBRUIJN      := Z_to_bv 64 0x11628;

  PC_MALLOC      := (0x16fc0%bv : word);
  PC_FREE        := (0x16e80%bv : word);
  PC_CALLOC      := (0x16d48%bv : word);
  PC_LIBC_FREE   := (0x16fc4%bv : word);
  PC_MALLOC_IMPL := (0x17950%bv : word);
  PC_GET_META    := (0x17190%bv : word);
  PC_NTFREE      := (0x172a0%bv : word);
  PC_ALLOC_META  := (0x17678%bv : word);
  PC_ALLOC_SLOT  := (0x17cc0%bv : word);
  PC_ENFRAME     := (0x18564%bv : word);
  PC_ALLZEROP    := (0x186b4%bv : word);
  PC_MMAP        := (0x188c8%bv : word);
  PC_MPROTECT    := (0x189b4%bv : word);
  PC_MUNMAP      := (0x189fc%bv : word);
  PC_VM_WAIT     := (0x188c4%bv : word);
  PC_SYSCALL_RET := (0x16d08%bv : word);
  PC_ERRNO_LOC   := (0x16900%bv : word);
  PC_LOCK        := (0x1e584%bv : word);
  PC_UNLOCK      := (0x1e80c%bv : word);
  PC_MEMCPY      := (0x1dfb4%bv : word);
  PC_MEMSET      := (0x1e3b8%bv : word)
|}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Local Abbreviation SEG0 := ImgU17.Ubsan_segment_000.
Local Abbreviation SEG1 := ImgU17.Ubsan_segment_001.
Local Abbreviation SEG2 := ImgU17.Ubsan_segment_002.
Local Abbreviation SEG3 := ImgU17.Ubsan_segment_003.
(* [comment removed for export] *)
Local Abbreviation B0 := 0x10000.  Local Abbreviation B1 := 0x13000.  Local Abbreviation B2 := 0x1f000.
Local Abbreviation B3 := 0x20000.  Local Abbreviation B4 := 0x52000.
Local Abbreviation P0 := 3%nat.  Local Abbreviation P1 := 12%nat.  Local Abbreviation P2 := 1%nat.  Local Abbreviation P3 := 50%nat.

Lemma u17_segs : ml_segs = [SEG0; SEG1; SEG2; SEG3].
Proof. reflexivity. Qed.

Lemma u17_bases :
  Z.of_N (seg_base SEG0) = B0 /\ Z.of_N (seg_base SEG0) + Z.of_N (seg_size SEG0) = B1 /\
  Z.of_N (seg_base SEG1) = B1 /\ Z.of_N (seg_base SEG1) + Z.of_N (seg_size SEG1) = B2 /\
  Z.of_N (seg_base SEG2) = B2 /\ Z.of_N (seg_base SEG2) + Z.of_N (seg_size SEG2) = B3 /\
  Z.of_N (seg_base SEG3) = B3 /\ Z.of_N (seg_base SEG3) + Z.of_N (seg_size SEG3) = B4.
Proof. repeat split; reflexivity. Qed.

(* [comment removed for export] *)
Lemma u17_find_none : forall a, (a < B0 \/ B4 <= a) -> find_segment ml_segs a 1 = None.
Proof.
  intros a Ha. rewrite u17_segs. apply find_segment_none. pose proof u17_bases as B.
  repeat (apply Forall_cons || apply Forall_nil); unfold seg_misses; lia.
Qed.

Lemma u17_find_seg0 : forall a, B0 <= a -> a + 1 <= B1 -> find_segment ml_segs a 1 = Some SEG0.
Proof.
  intros a H1 H2. rewrite u17_segs. pose proof u17_bases as B.
  apply (find_segment_hit [] SEG0 [SEG1; SEG2; SEG3] a 1); [apply Forall_nil | lia | lia].
Qed.
Lemma u17_find_seg1 : forall a, B1 <= a -> a + 1 <= B2 -> find_segment ml_segs a 1 = Some SEG1.
Proof.
  intros a H1 H2. rewrite u17_segs. pose proof u17_bases as B.
  apply (find_segment_hit [SEG0] SEG1 [SEG2; SEG3] a 1); [| lia | lia].
  repeat (apply Forall_cons || apply Forall_nil); unfold seg_misses; lia.
Qed.
Lemma u17_find_seg2 : forall a, B2 <= a -> a + 1 <= B3 -> find_segment ml_segs a 1 = Some SEG2.
Proof.
  intros a H1 H2. rewrite u17_segs. pose proof u17_bases as B.
  apply (find_segment_hit [SEG0; SEG1] SEG2 [SEG3] a 1); [| lia | lia].
  repeat (apply Forall_cons || apply Forall_nil); unfold seg_misses; lia.
Qed.
Lemma u17_find_seg3 : forall a, B3 <= a -> a + 1 <= B4 -> find_segment ml_segs a 1 = Some SEG3.
Proof.
  intros a H1 H2. rewrite u17_segs. pose proof u17_bases as B.
  apply (find_segment_hit [SEG0; SEG1; SEG2] SEG3 [] a 1); [| lia | lia].
  repeat (apply Forall_cons || apply Forall_nil); unfold seg_misses; lia.
Qed.

(* [comment removed for export] *)
Definition chk_seg_byte (seg : Segment) (off : Z) : bool :=
  match segment_byte_at (seg_bytes seg) (Z.to_N off) with Some _ => true | None => false end.

Lemma u17_seg0_bytes : chk_range (chk_seg_byte SEG0) 0 P0 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma u17_seg1_bytes : chk_range (chk_seg_byte SEG1) 0 P1 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma u17_seg2_bytes : chk_range (chk_seg_byte SEG2) 0 P2 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma u17_seg3_bytes : chk_range (chk_seg_byte SEG3) 0 P3 = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition chk_rom_zero (a : Z) : bool :=
  match seg_rom ml_segs (Z_to_bv 64 a) with Some v => bv_unsigned v =? 0 | None => false end.
Lemma u17_ctx_zero : chk_list chk_rom_zero (bv_unsigned A_LOCK) 940 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma u17_tables :
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

Instance LU17ok : MallocLayoutOk LU17.
Proof.
  pose proof u17_bases as B.
  split.
  - (* [comment removed for export] *) cbn. lia.
  - (* [comment removed for export] *) intros a Ha. apply seg_rom_none_of_find. apply u17_find_none. exact Ha.
  - (* [comment removed for export] *) intros m a Ha. apply wview_of_find_none. apply u17_find_none. exact Ha.
  - (* [comment removed for export] *) intros m a Ha. cbn in Ha.
    destruct (Z.lt_ge_cases (bv_unsigned a) B1).
    + apply (wview_of_find_ro _ m a SEG0); [apply u17_find_seg0; lia | reflexivity].
    + apply (wview_of_find_ro _ m a SEG1); [apply u17_find_seg1; lia | reflexivity].
  - (* [comment removed for export] *) intros m a Ha. cbn in Ha.
    destruct (Z.lt_ge_cases (bv_unsigned a) B3).
    + apply (wview_of_find_rw _ m a SEG2); [apply u17_find_seg2; lia | reflexivity |].
      pose proof (chk_range_sound _ _ _ u17_seg2_bytes (bv_unsigned a - B2) ltac:(lia)) as Hc.
      unfold chk_seg_byte in Hc. rewrite (proj1 (proj2 (proj2 (proj2 (proj2 B))))).
      destruct (segment_byte_at (seg_bytes SEG2) (Z.to_N (bv_unsigned a - B2))); [discriminate | discriminate].
    + apply (wview_of_find_rw _ m a SEG3); [apply u17_find_seg3; lia | reflexivity |].
      pose proof (chk_range_sound _ _ _ u17_seg3_bytes (bv_unsigned a - B3) ltac:(lia)) as Hc.
      unfold chk_seg_byte in Hc. rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 B))))))).
      destruct (segment_byte_at (seg_bytes SEG3) (Z.to_N (bv_unsigned a - B3))); [discriminate | discriminate].
  - (* [comment removed for export] *) intros a Ha. cbn in Ha.
    destruct (Z.lt_ge_cases (bv_unsigned a) B1); [| destruct (Z.lt_ge_cases (bv_unsigned a) B2); [| destruct (Z.lt_ge_cases (bv_unsigned a) B3)]].
    + apply (seg_rom_some_of_find _ a SEG0); [apply u17_find_seg0; lia | reflexivity |].
      pose proof (chk_range_sound _ _ _ u17_seg0_bytes (bv_unsigned a - B0) ltac:(lia)) as Hc.
      unfold chk_seg_byte in Hc. rewrite (proj1 B).
      destruct (segment_byte_at (seg_bytes SEG0) (Z.to_N (bv_unsigned a - B0))); [discriminate | discriminate].
    + apply (seg_rom_some_of_find _ a SEG1); [apply u17_find_seg1; lia | reflexivity |].
      pose proof (chk_range_sound _ _ _ u17_seg1_bytes (bv_unsigned a - B1) ltac:(lia)) as Hc.
      unfold chk_seg_byte in Hc. rewrite (proj1 (proj2 (proj2 B))).
      destruct (segment_byte_at (seg_bytes SEG1) (Z.to_N (bv_unsigned a - B1))); [discriminate | discriminate].
    + apply (seg_rom_some_of_find _ a SEG2); [apply u17_find_seg2; lia | reflexivity |].
      pose proof (chk_range_sound _ _ _ u17_seg2_bytes (bv_unsigned a - B2) ltac:(lia)) as Hc.
      unfold chk_seg_byte in Hc. rewrite (proj1 (proj2 (proj2 (proj2 (proj2 B))))).
      destruct (segment_byte_at (seg_bytes SEG2) (Z.to_N (bv_unsigned a - B2))); [discriminate | discriminate].
    + apply (seg_rom_some_of_find _ a SEG3); [apply u17_find_seg3; lia | reflexivity |].
      pose proof (chk_range_sound _ _ _ u17_seg3_bytes (bv_unsigned a - B3) ltac:(lia)) as Hc.
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
  - (* [comment removed for export] *) apply chk_rom_bytes_sound; [apply Forall_map_mod256 | exact (proj2 (proj2 (proj2 (proj2 u17_tables))))].
  - (* [comment removed for export] *) intros a Ha. cbn in Ha. rewrite !u64_lit in Ha by lia.
    pose proof (chk_list_sound _ _ _ u17_ctx_zero (bv_unsigned a) ltac:(cbn; rewrite !u64_lit by lia; lia)) as Hc.
    unfold chk_rom_zero in Hc. rewrite Z_to_bv_bv_unsigned in Hc.
    destruct (seg_rom ml_segs a) as [v|]; [|discriminate]. apply Z.eqb_eq in Hc.
    f_equal. rewrite <- (Z_to_bv_bv_unsigned 8 v). rewrite Hc. reflexivity.
  - (* [comment removed for export] *) cbn; rewrite !u64_lit by lia; lia.
  - reflexivity.
  - apply chk_rom_bytes_sound; [apply Forall_lt256_of_chk; vm_compute; reflexivity | exact (proj1 u17_tables)].
  - apply chk_rom_bytes_sound; [apply Forall_lt256_of_chk; vm_compute; reflexivity | exact (proj1 (proj2 u17_tables))].
  - apply chk_rom_bytes_sound; [apply Forall_lt256_of_chk; vm_compute; reflexivity | exact (proj1 (proj2 (proj2 u17_tables)))].
  - apply chk_rom_bytes_sound; [apply Forall_lt256_of_chk; vm_compute; reflexivity | exact (proj1 (proj2 (proj2 (proj2 u17_tables))))].
  - (* [comment removed for export] *) repeat (apply Forall_cons || apply Forall_nil); cbv; repeat split; congruence.
Qed.
End V17MallocLayout.

From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require StoreOk.
Module V17MemPreds.
Import Stdlib.ZArith.ZArith.
Import Stdlib.NArith.NArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import OSSVerify.leptonica.kernel_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.StoreOk.
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
End V17MemPreds.

Module V17PFBase.
Import OSSVerify.leptonica.kernel_fuzzer.images.Ubsan.
(* [comment removed for export] *)

Abbreviation SEGS := Ubsan.M.loaded_segments.
End V17PFBase.

From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Reloc Require Reloc.
Module V17Reloc.
Import Stdlib.ZArith.ZArith.
Import Stdlib.Lists.List.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OSSVerify.leptonica.kernel_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Reloc.Reloc.
(* [comment removed for export] *)




Import ListNotations.
Local Open Scope Z_scope.

Definition v17_dtab : list (positive * Z) :=
  [(8%positive, 0); (1000%positive, 1000); (1001%positive, 1000); (1002%positive, 1000); (1003%positive, 1000); (1004%positive, 1000); (1005%positive, 1000); (1006%positive, 1000); (1007%positive, 1000); (1008%positive, 1124); (1009%positive, 1140); (1010%positive, 1140); (1011%positive, 1140); (1012%positive, 1140); (1013%positive, 1140); (1014%positive, 1140); (1015%positive, 2708); (1016%positive, 4544); (1017%positive, 4544); (1018%positive, 4544); (1019%positive, 4544); (1020%positive, 4544); (1021%positive, 4544); (1022%positive, 4532); (1023%positive, 4532); (1024%positive, 4532); (1025%positive, 4936); (1026%positive, 4936); (1027%positive, 4936); (1028%positive, 4936); (1029%positive, 4936); (1030%positive, 4936); (1031%positive, 4936); (1032%positive, 4936); (1033%positive, 4936); (1034%positive, 4936); (1035%positive, 4936); (1036%positive, 5252); (1037%positive, 5252); (1038%positive, 5252); (1039%positive, 5252); (1040%positive, 5252); (1041%positive, 5252); (1042%positive, 5252); (1043%positive, 5252); (1044%positive, 5252); (1045%positive, 5252); (1046%positive, 5252); (1047%positive, 5252); (1048%positive, 5252); (1049%positive, 5252); (1050%positive, 5252); (1051%positive, 5252); (1052%positive, 5620); (1053%positive, 5620); (1054%positive, 5620); (1055%positive, 5620); (1056%positive, 5620); (1057%positive, 5620); (1058%positive, 5620); (1059%positive, 5620); (1060%positive, 5620); (1061%positive, 5620); (1062%positive, 5620); (1063%positive, 5792); (1064%positive, 5792); (1065%positive, 5792); (1066%positive, 5792); (1067%positive, 5792); (1068%positive, 5792); (1069%positive, 5792); (1070%positive, 5792); (1071%positive, 5792); (1072%positive, 5792); (1073%positive, 5792); (1074%positive, 5792); (1075%positive, 5792); (1076%positive, 5792); (1077%positive, 5792); (1078%positive, 5792); (1079%positive, 5792); (1080%positive, 5792); (1081%positive, 5792); (1082%positive, 5792); (1083%positive, 5792); (1084%positive, 5792); (1085%positive, 5792); (1086%positive, -13028); (1087%positive, 5632); (1088%positive, 5632); (1089%positive, 5632); (1090%positive, 5632); (1091%positive, 5632); (1092%positive, 5632); (1093%positive, 5632); (1094%positive, 5632); (1095%positive, 5632); (1096%positive, 5632); (1097%positive, 5632); (1098%positive, 5632); (1099%positive, 5644); (1100%positive, 5644); (1101%positive, 5644); (3000%positive, 1124); (3001%positive, 2708); (4000%positive, 12); (4001%positive, 77); (4002%positive, 130); (4003%positive, 130); (4004%positive, 149); (4005%positive, 149); (4006%positive, 149); (4007%positive, 149); (4008%positive, 227); (4009%positive, 206); (4010%positive, 206); (4011%positive, 266); (4012%positive, 266); (4013%positive, 266); (4014%positive, 295); (4015%positive, 298); (4016%positive, 366); (4017%positive, 407); (4018%positive, 407); (5000%positive, 628); (5001%positive, 628); (5002%positive, 628); (5003%positive, 624); (5004%positive, 624); (5005%positive, 624); (5006%positive, 624); (5007%positive, 624); (5008%positive, 624); (5009%positive, 624); (5010%positive, 624); (5011%positive, 680); (5012%positive, 5656); (5013%positive, 5664); (5015%positive, 5664); (5016%positive, 5648); (5018%positive, 536); (5019%positive, 5664); (5020%positive, 628); (5021%positive, 624); (5022%positive, 624); (5023%positive, 624); (5024%positive, 624); (5025%positive, 624); (5026%positive, 5664); (5027%positive, 5664); (5028%positive, 5664); (5029%positive, 5608); (5030%positive, 137152); (5031%positive, 137152); (5032%positive, 137152); (5033%positive, 137152);
   (230%positive, -64460); (240%positive, -64460); (241%positive, -64460); (242%positive, -64460); (243%positive, -64460); (231%positive, -64460); (232%positive, -64460); (244%positive, -64460); (245%positive, -64460); (246%positive, -64460); (233%positive, -64460); (234%positive, -64460); (247%positive, -64460); (235%positive, -64460); (236%positive, -63764); (237%positive, -63764); (248%positive, -63764); (238%positive, -63764); (249%positive, -63764); (250%positive, -63764); (239%positive, -63872); (400%positive, 0); (401%positive, 0); (402%positive, 0); (403%positive, 0); (404%positive, 0); (405%positive, 0); (406%positive, 17); (407%positive, 17); (408%positive, 17); (409%positive, 17); (410%positive, 49); (411%positive, 49); (412%positive, 49); (413%positive, 65); (414%positive, 65); (415%positive, 65); (416%positive, 65); (417%positive, 65); (418%positive, 65); (419%positive, 137); (420%positive, 137); (421%positive, 137); (422%positive, 154); (423%positive, 179); (424%positive, 179); (425%positive, 179); (426%positive, 179); (427%positive, 179); (428%positive, 196); (429%positive, 196); (430%positive, 196); (431%positive, 196); (432%positive, 196); (433%positive, 196); (434%positive, 196); (435%positive, 196); (436%positive, 196); (437%positive, 196); (438%positive, 196); (439%positive, 196); (440%positive, 196); (441%positive, 196); (442%positive, 196); (443%positive, 196); (444%positive, 258); (445%positive, 258); (446%positive, 258); (447%positive, 258); (448%positive, 258); (449%positive, 258); (450%positive, 270); (451%positive, 270); (452%positive, 249); (453%positive, 249); (454%positive, 249); (455%positive, 249); (456%positive, 249); (457%positive, 249); (458%positive, 249); (459%positive, 249); (460%positive, 249); (461%positive, 249); (462%positive, 249); (463%positive, 249); (464%positive, 249); (465%positive, 249); (466%positive, 266); (467%positive, 269); (468%positive, 337); (469%positive, 337); (470%positive, 337); (471%positive, 337); (1900%positive, 4532); (5034%positive, 5656); (5035%positive, 5664); (5036%positive, 136944)].

Definition v17_stab : list (Z * Z) := [
  (0x13084, 0xffffd197); (0x13088, 0x39418193); (0x13090, 0xfffed597); (0x13094, 0xb8858593);
  (0x1309c, 0x40006f); (0x130a4, 0xc617); (0x130a8, 0xc697); (0x130ac, 0xc717);
  (0x130b0, 0x4fc63783); (0x130b4, 0x5006b683); (0x130b8, 0x50473703); (0x130c8, 0xf80306f);
  (0x130dc, 0xd517); (0x130e0, 0x78c50513); (0x130f8, 0xd517); (0x130fc, 0x77050593);
  (0x13108, 0xc517); (0x1310c, 0x4b053503); (0x13118, 0xffffe517); (0x1311c, 0x71050513);
  (0x13120, 0xd597); (0x13124, 0x75058593); (0x13150, 0xd517); (0x13154, 0x76050513);
  (0x1316c, 0xd517); (0x13170, 0x74450593); (0x1317c, 0xc517); (0x13180, 0x44453503);
  (0x1318c, 0xd517); (0x13190, 0x4a450513); (0x131a0, 0xc517); (0x131a4, 0x42853503);
  (0x131b0, 0xffffe517); (0x131b4, 0x67850513); (0x1320c, 0x5c8030ef); (0x13220, 0x1b9030ef);
  (0x13230, 0xd517); (0x13234, 0x68150b13); (0x1324c, 0x1810a0ef); (0x13274, 0x165030ef);
  (0x13290, 0x13d0a0ef); (0x13298, 0x1030ef); (0x132b4, 0x2840b0ef); (0x132c8, 0x2100b0ef);
  (0x1332c, 0x168000ef); (0x13340, 0x160000ef); (0x13350, 0x148000ef); (0x13368, 0xc517);
  (0x1336c, 0x26853503); (0x13378, 0xffffd597); (0x1337c, 0xdc758593); (0x13380, 0x115050ef);
  (0x13388, 0xc517); (0x1338c, 0x24853503); (0x13394, 0xffffd517); (0x1339c, 0x39950513);
  (0x133a4, 0xc517); (0x133a8, 0x22c53503); (0x133b0, 0xffffd517); (0x133b8, 0xda050513);
  (0x133c0, 0x321050ef); (0x133c8, 0x6d0030ef); (0x133fc, 0xc517); (0x13400, 0x1d453503);
  (0x13408, 0xffffd597); (0x1340c, 0x1e658593); (0x13418, 0xc517); (0x1341c, 0x1b853503);
  (0x13424, 0xffffd597); (0x13428, 0xfaa58593); (0x13430, 0x65050ef); (0x13438, 0xc517);
  (0x1343c, 0x19853503); (0x13444, 0xffffd517); (0x1344c, 0xc9b50513); (0x13454, 0x28d050ef);
  (0x1345c, 0x304030ef); (0x13460, 0xc517); (0x13464, 0x17053503); (0x1346c, 0xffffd597);
  (0x13470, 0x16d58593); (0x13478, 0xc517); (0x1347c, 0x15853503); (0x13484, 0xffffd517);
  (0x1348c, 0xc5b50513); (0x135d8, 0xffffd517); (0x135dc, 0xa9f50513); (0x135e4, 0x2dc0a0ef);
  (0x13674, 0xffffd517); (0x13678, 0x9950513); (0x1367c, 0x18000ef); (0x13708, 0x1c40a0ef);
  (0x13710, 0xd517); (0x13714, 0xec453583); (0x13744, 0xffffd517); (0x13748, 0xfc950513);
  (0x1374c, 0xf49ff0ef); (0x1376c, 0xc597); (0x13770, 0xdd85b583); (0x13778, 0x5480506f);
  (0x13780, 0x517); (0x13784, 0xfe450513); (0x13788, 0xd597); (0x1378c, 0xe4a5b623);
  (0x14d1c, 0x40006f); (0x15198, 0x60080ef); (0x1519c, 0x9517); (0x151a0, 0x67c53503);
  (0x151b4, 0x3b517); (0x151b8, 0xcb450913); (0x15204, 0x3b617); (0x15208, 0xccb63623);
  (0x15210, 0x3b597); (0x15214, 0xc4a5b023); (0x1521c, 0x3b517); (0x15220, 0xca053a23);
  (0x15238, 0xffffa517); (0x1523c, 0xfa50413); (0x15240, 0x9517); (0x15244, 0x5e053583);
  (0x15248, 0x9517); (0x1524c, 0x5e053503); (0x1527c, 0x214000ef); (0x15284, 0x5d000ef);
  (0x152f8, 0xffffa517); (0x15304, 0x74c50593); (0x15328, 0xffffa517); (0x15334, 0x71c50593);
  (0x15358, 0xffffa517); (0x15364, 0x6ec50593); (0x153ac, 0xdc1ff0ef); (0x153b0, 0x9517);
  (0x153b4, 0x9597); (0x153b8, 0x48053403); (0x153bc, 0x4845b483); (0x15418, 0xd59ff0ef);
  (0x1541c, 0x517); (0x15420, 0x2c50313); (0x15478, 0xf25ff0ef); (0x1548c, 0x4fc000ef);
  (0x154b4, 0x3a597); (0x154b8, 0x73458593); (0x154bc, 0x3b617); (0x154c0, 0x9ac60493);
  (0x154d0, 0xa717); (0x154e0, 0x9297); (0x154e4, 0x5b076f03); (0x154e8, 0x2e02b283);
  (0x15630, 0x1a697); (0x15644, 0x4e868513); (0x156c0, 0x28080ef); (0x156d8, 0x3a597);
  (0x156e4, 0x51058513); (0x15700, 0x3a517); (0x15704, 0x75053503); (0x15768, 0xffffb617);
  (0x15774, 0xc0460613); (0x15784, 0xffffa617); (0x15788, 0x44060613); (0x15790, 0x4000006f);
  (0x157c4, 0x9517); (0x157c8, 0x9597); (0x157cc, 0xefc53503); (0x157d0, 0xf005b403);
  (0x157fc, 0xfb5ff06f); (0x15818, 0x3a697); (0x1581c, 0x4a068693); (0x15860, 0xdbdff0ef);
  (0x15864, 0xf51ff0ef); (0x15868, 0x160020ef); (0x15870, 0xd91ff0ef); (0x15894, 0x9517);
  (0x15898, 0xe2453483); (0x158f0, 0x46d070ef); (0x1592c, 0x94000ef); (0x15954, 0x64000ef);
  (0x15968, 0x9517); (0x1596c, 0xd5053503); (0x15974, 0x2f8070ef); (0x1597c, 0x9517);
  (0x15980, 0xd3c53503); (0x15994, 0x9517); (0x15998, 0xd2453503); (0x159dc, 0xbddff0ef);
  (0x159fc, 0xffdff06f); (0x15a1c, 0xb9dff0ef); (0x15a4c, 0x22c000ef); (0x15a58, 0x3a517);
  (0x15a5c, 0x6a052503); (0x15a84, 0x5ec070ef); (0x15aa0, 0x5d0070ef); (0x15ae0, 0x590070ef);
  (0x15b0c, 0x5640706f); (0x15b2c, 0x41010ef); (0x15b38, 0x1440006f); (0x15b3c, 0x1910006f);
  (0x15b60, 0x1ac000ef); (0x15b94, 0xffffa717); (0x15b9c, 0x63070713); (0x15c40, 0x3a717);
  (0x15c5c, 0xf6774883); (0x15c94, 0x3a597); (0x15c98, 0xf8058593); (0x15ca4, 0x45c070ef);
  (0x15cb0, 0x16c000ef); (0x15cbc, 0x3a517); (0x15cc0, 0xf5850513); (0x15cc4, 0x6c4070ef);
  (0x15ccc, 0xfb0ff0ef); (0x15ce0, 0x99010ef); (0x15d9c, 0x3a797); (0x15da8, 0xe807b783);
  (0x15dc8, 0xffffa797); (0x15dcc, 0x3fc78793); (0x15e34, 0x8617); (0x15e38, 0x74863483);
  (0x15e84, 0x3a817); (0x15e88, 0xd9880913); (0x15e98, 0xffffa817); (0x15e9c, 0x32c80813);
  (0x15f90, 0x3a697); (0x15f94, 0xc8c68693); (0x1608c, 0xc81ff0ef); (0x161f0, 0xe8cff0ef);
  (0x16210, 0x8517); (0x16214, 0x36c53903); (0x1621c, 0x3a597); (0x16224, 0x9f858993);
  (0x1622c, 0x3a597); (0x16230, 0x97858413); (0x1626c, 0xc5060ef); (0x1637c, 0xc8010ef);
  (0x163d4, 0x70010ef); (0x164a8, 0x88010ef); (0x164b0, 0xfcdfe0ef); (0x164c8, 0xbb4ff0ef);
  (0x164f8, 0xf85fe0ef); (0x16534, 0x39597); (0x16538, 0x6e058493); (0x16560, 0x6e5000ef);
  (0x1656c, 0x39517); (0x16570, 0x63b54503); (0x16578, 0x39517); (0x1657c, 0x69c50513);
  (0x16580, 0x381060ef); (0x165b0, 0xffffa617); (0x165b8, 0xbf460993); (0x16620, 0xffffa617);
  (0x16634, 0xba460593); (0x16654, 0xba1ff0ef); (0x166c0, 0x39517); (0x166c4, 0x4e754503);
  (0x166cc, 0x39517); (0x166d0, 0x54850513); (0x166d4, 0x22d060ef); (0x16718, 0x39517);
  (0x1671c, 0x4fc50513); (0x16720, 0x469060ef); (0x1672c, 0x64d000ef); (0x167d8, 0x64000ef);
  (0x167f8, 0x391060ef); (0x16828, 0xb90006f); (0x1682c, 0x39517); (0x16830, 0x3e850513);
  (0x16834, 0x355060ef); (0x16874, 0x8517); (0x16878, 0xd0853a03); (0x16884, 0x39597);
  (0x16888, 0x39058b13); (0x16a04, 0xffff9597); (0x16a0c, 0x7a058593); (0x16a20, 0xffff9517);
  (0x16a24, 0x7a450c93); (0x16a30, 0xfc4ff0ef); (0x16a44, 0x39597); (0x16a48, 0x1905b583);
  (0x16a5c, 0xffff9697); (0x16a60, 0x7c868693); (0x16a8c, 0xffff9697); (0x16a90, 0x7b368693);
  (0x16ba4, 0xffff9697); (0x16bac, 0x60068693); (0x16c48, 0x498000ef); (0x16d18, 0xffff9717);
  (0x16d20, 0x4ac70713); (0x16ee8, 0x55c000ef); (0x170dc, 0xfa0fe0ef); (0x17108, 0xffff9797);
  (0x17110, 0xbc78793); (0x172c4, 0x39797); (0x172cc, 0x9587b783); (0x172ec, 0xffff9817);
  (0x172f0, 0xed880813); (0x17360, 0xffff9597); (0x17364, 0xe6458593); (0x1738c, 0xffff9517);
  (0x17390, 0xe3850513); (0x173b0, 0xffff9597); (0x173b4, 0xebc5b787); (0x173e8, 0xffff9597);
  (0x173ec, 0xe9c5b787); (0x1746c, 0x810fe0ef); (0x17484, 0xff9fd0ef); (0x174e0, 0xf61ff0ef);
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
  (0x17fc4, 0x6517); (0x17fd0, 0x39c53603); (0x180b0, 0xa41ff0ef); (0x183d0, 0xffff8697);
  (0x183d4, 0xdf068693); (0x18444, 0x159000ef); (0x1849c, 0xffff8597); (0x184a0, 0xbdc58593);
  (0x184dc, 0x2c9000ef); (0x1850c, 0xffff6597); (0x18514, 0x74758593); (0x18538, 0xffff6517);
  (0x1853c, 0x71b50513); (0x18554, 0xffff7517); (0x18558, 0x1a50b93); (0x18560, 0xd01fc0ef);
  (0x18568, 0xd05fc0ef); (0x18580, 0x121040ef); (0x18598, 0xffff6617); (0x1859c, 0x6bb60613);
  (0x185dc, 0xffff6597); (0x185e0, 0x67758593); (0x18614, 0xffff8597); (0x18618, 0xb4458593);
  (0x18644, 0xffff6597); (0x18648, 0x60f58893); (0x18680, 0xffff6517); (0x18684, 0x5d350513);
  (0x186b8, 0xffff6597); (0x186bc, 0x59b58713); (0x186d0, 0xffff8697); (0x186d4, 0xcc068693);
  (0x18734, 0x739010ef); (0x1876c, 0x764000ef); (0x18790, 0x6dd010ef); (0x187b4, 0xb3cff0ef);
  (0x187c0, 0xffff6597); (0x187c4, 0x49358593); (0x187e8, 0xffff6597); (0x187f0, 0x46b58893);
  (0x18938, 0x3e0040ef); (0x18968, 0x988ff0ef); (0x1898c, 0x964ff0ef); (0x189a8, 0x948ff0ef);
  (0x189dc, 0x33c040ef); (0x18a0c, 0x8e4ff0ef); (0x18a30, 0x8c0ff0ef); (0x18a60, 0x2b8040ef);
  (0x18a90, 0x860ff0ef); (0x18ab4, 0x83cff0ef); (0x18ad0, 0x820ff0ef); (0x18b04, 0x214040ef);
  (0x18b34, 0xfbdfe0ef); (0x18b54, 0xf9dfe0ef); (0x18b70, 0x360000ef); (0x18b94, 0x33c000ef);
  (0x18be4, 0xe7cfc0ef); (0x18c18, 0x184000ef); (0x18c2c, 0x170000ef); (0x18c40, 0x15c000ef);
  (0x18c54, 0x148000ef); (0x18c68, 0x134000ef); (0x18c7c, 0x120000ef); (0x18c90, 0x10c000ef);
  (0x18ca4, 0xf8000ef); (0x18cb8, 0xe4000ef); (0x18d38, 0xd28fc0ef); (0x18d98, 0x8c9fc0ef);
  (0x18dac, 0xffff7697); (0x18db0, 0x3cc68693); (0x18dfc, 0x1c1010ef); (0x18eec, 0x5517);
  (0x18ef0, 0x47453903); (0x18f24, 0x5f5030ef); (0x18f54, 0xb9dfe0ef); (0x18f74, 0xb7dfe0ef);
  (0x18fa0, 0xec0fc0ef); (0x19000, 0x5517); (0x19004, 0x36053a03); (0x1905c, 0xf1010ef);
  (0x19068, 0xffff6517); (0x19070, 0xd4150513); (0x19084, 0xffff6517); (0x1908c, 0xd2550513);
  (0x190c4, 0x91010ef); (0x190e0, 0xb9010ef); (0x190f0, 0x148020ef); (0x19104, 0x235010ef);
  (0x19118, 0x159010ef); (0x19154, 0xffff7517); (0x19158, 0xed453507); (0x1915c, 0x660010ef);
  (0x19170, 0x1c9010ef); (0x191a0, 0xd1010ef); (0x191a8, 0xffff6597); (0x191ac, 0xffff6617);
  (0x191b0, 0xdfe58593); (0x191b4, 0x28f60993); (0x19210, 0xf7dfd0ef); (0x19230, 0x58c010ef);
  (0x1924c, 0xf4020ef); (0x19258, 0xf8020ef); (0x19268, 0xffff6597); (0x1926c, 0xffff6617);
  (0x19270, 0xeaa58593); (0x19274, 0x17a60993); (0x192b0, 0x269030ef); (0x192e0, 0x811fe0ef);
  (0x19300, 0xff0fe0ef); (0x1931c, 0xfd4fe0ef); (0x19338, 0xfb8fe0ef); (0x1936c, 0x1ad030ef);
  (0x1939c, 0xf54fe0ef); (0x193bc, 0xf34fe0ef); (0x19454, 0x704020ef); (0x19464, 0x5d5010ef);
  (0x19478, 0x774020ef); (0x1948c, 0x6b5010ef); (0x194a0, 0x698010ef); (0x194b4, 0x5bc010ef);
  (0x194c0, 0xffff7517); (0x194c4, 0xba053503); (0x1975c, 0x60010ef); (0x19778, 0x3d9010ef);
  (0x19784, 0x3bd010ef); (0x19864, 0xffff7797); (0x19880, 0xb2c78913); (0x198a0, 0x1d0010ef);
  (0x198b4, 0x424020ef); (0x198d4, 0x165010ef); (0x198e4, 0x155010ef); (0x198f8, 0x249010ef);
  (0x1990c, 0x22c010ef); (0x19934, 0x13c010ef); (0x199f4, 0x324030ef); (0x19a24, 0x8ccfe0ef);
  (0x19a68, 0x7d0010ef); (0x19a78, 0x308020ef); (0x19ab8, 0x780010ef); (0x19acc, 0x85010ef);
  (0x19ae0, 0xffff6517); (0x19ae4, 0x56053507); (0x19b08, 0xfe9fd0ef); (0x19b24, 0xfcdfd0ef);
  (0x19b50, 0x1c8030ef); (0x19b80, 0xf71fd0ef); (0x19ba0, 0xf51fd0ef); (0x19bc4, 0xf2dfd0ef);
  (0x19bec, 0x12c030ef); (0x19c1c, 0xed5fd0ef); (0x19c3c, 0xeb5fd0ef); (0x19c58, 0xe99fd0ef);
  (0x19c84, 0x94030ef); (0x19cb4, 0xe3dfd0ef); (0x19cd4, 0xe1dfd0ef); (0x19cf0, 0xffff6517);
  (0x19cf4, 0x34053507); (0x19cfc, 0xffff6517); (0x19d00, 0x35c53507); (0x19d04, 0x2b9000ef);
  (0x19d38, 0x500010ef); (0x19d54, 0x5e5000ef); (0x19d70, 0x5c9000ef); (0x19d90, 0x5c0010ef);
  (0x19d9c, 0x4d5000ef); (0x1a0dc, 0x43d020ef); (0x1a110, 0x9e1fd0ef); (0x1a138, 0x9b9fd0ef);
  (0x1a158, 0x999fd0ef); (0x1a194, 0x385020ef); (0x1a1c8, 0x929fd0ef); (0x1a1f0, 0x901fd0ef);
  (0x1a2ec, 0x805fd0ef); (0x1a314, 0xffff5597); (0x1a324, 0xb3f58513); (0x1a3dc, 0xf14fd0ef);
  (0x1a424, 0xeccfd0ef); (0x1a458, 0xe98fd0ef); (0x1a484, 0xa4dfe0ef); (0x1a4ac, 0xe44fd0ef);
  (0x1a4c8, 0xffff5517); (0x1a4cc, 0x98b50513); (0x1a4d8, 0xe18fd0ef); (0x1a5a0, 0xd50fd0ef);
  (0x1a5c8, 0x909fe0ef); (0x1a604, 0x714020ef); (0x1a634, 0xcbcfd0ef); (0x1a654, 0xc9cfd0ef);
  (0x1a668, 0xff9fa0ef); (0x1a67c, 0x14000ef); (0x1a76c, 0xaf5fa0ef); (0x1a9d4, 0x9c000ef);
  (0x1a9dc, 0xffff5517); (0x1a9e0, 0x69453507); (0x1a9e4, 0xdd9ff0ef); (0x1a9f8, 0x140000ef);
  (0x1b34c, 0x40006f); (0x1ba70, 0xac000ef); (0x1bad0, 0x7c000ef); (0x1bb30, 0xffff5597);
  (0x1bb34, 0x87058593); (0x1c688, 0x3597); (0x1c68c, 0xe2858593); (0x1c69c, 0xf20fb06f);
  (0x1c6ac, 0x6697); (0x1c6b0, 0x6386b403); (0x1c6c0, 0x717); (0x1c6c4, 0xad870713);
  (0x1c71c, 0xa7dff0ef); (0x1c73c, 0x8a9fd0ef); (0x1c760, 0x2617); (0x1c764, 0xca063903);
  (0x1c7a0, 0x618000ef); (0x1c7a4, 0x517); (0x1c7b0, 0x6850513); (0x1c7dc, 0xe80fb0ef);
  (0x1c808, 0xef9f80ef); (0x1c864, 0x150000ef); (0x1c894, 0x120000ef); (0x1c940, 0xffff3697);
  (0x1c944, 0x7a86b683); (0x1c948, 0xffff3717); (0x1c94c, 0x79073703); (0x1ceec, 0xffff3597);
  (0x1cef0, 0xffff3717); (0x1cef4, 0x1fc5b683); (0x1cef8, 0x1e873703); (0x1cf60, 0x989ff0ef);
  (0x1cf84, 0x33597); (0x1cf88, 0xaa758683); (0x1cfb4, 0xaa0583a3); (0x1d2a4, 0xfddff06f);
  (0x1d2bc, 0xf84fa0ef); (0x1d2dc, 0xfbdff0ef); (0x1d2f4, 0xc08f80ef); (0x1d310, 0xbecf806f);
  (0x1d338, 0xf61ff0ef); (0x1d344, 0xbb8f806f);
  (0x237e0, 159383791); (0x2381c, 1988141295); (0x23828, 50455); (0x2382c, 3611636995);
  (0x2383c, 4294952215); (0x23840, 4294956439); (0x23844, 2034566419); (0x23848, 2450883987);
  (0x2385c, 4049596527); (0x2388c, 322961647); (0x238b8, 54679); (0x238bc, 3594880147);
  (0x238d8, 1255145711); (0x238e0, 50455); (0x238e4, 3418699011); (0x238f4, 4294952215);
  (0x238f8, 4294952343); (0x238fc, 1841628435); (0x23900, 2090173843); (0x23918, 3852464239);
  (0x23948, 272642287); (0x2395c, 318771439); (0x23968, 239087855); (0x2396c, 50455);
  (0x23970, 3271898371); (0x23980, 4294956311); (0x23984, 4294952343); (0x23988, 3281323283);
  (0x2398c, 1943373203); (0x23994, 3722440943); (0x23a14, 50839); (0x23a18, 3095835651);
  (0x23a28, 4294956695); (0x23a2c, 4294952727); (0x23a30, 3201730195); (0x23a34, 2053572371);
  (0x23a50, 3361730799); (0x23a5c, 4294952215); (0x23a60, 4294952343); (0x23a64, 1733625107);
  (0x23a68, 1998947731); (0x23a70, 50455); (0x23a74, 2999268611); (0x23a84, 4294952215);
  (0x23a88, 4294952343); (0x23a8c, 1040516371); (0x23a90, 1957004691); (0x23a98, 50455);
  (0x23a9c, 2957325571); (0x23aac, 4294956311); (0x23ab0, 4294952343); (0x23ab4, 2406810899);
  (0x23ab8, 1915061651); (0x23ad8, 50839); (0x23adc, 2890314755); (0x23aec, 4294956695);
  (0x23af0, 4294952727); (0x23af4, 2996209299); (0x23af8, 1848051475); (0x23b14, 3156209903);
  (0x23b20, 4294956311); (0x23b24, 4294952343); (0x23b28, 2647983379); (0x23b2c, 1793426835);
  (0x23b34, 50455); (0x23b38, 2793747715); (0x23b48, 4294952215); (0x23b4c, 4294952343);
  (0x23b50, 1308951827); (0x23b54, 1751483795); (0x23b78, 3214930031); (0x23b88, 50455);
  (0x23b8c, 2705667331); (0x23b9c, 4294952215); (0x23ba0, 4294952343); (0x23ba4, 1002767635);
  (0x23ba8, 1663403411); (0x23bbc, 50455); (0x23bc0, 2651141379); (0x23bd0, 4294956311);
  (0x23bd4, 4294952343); (0x23bd8, 2825192723); (0x23bdc, 1608877459); (0x23be8, 50455);
  (0x23bec, 2605004035); (0x23bfc, 4294956311); (0x23c00, 4294952343); (0x23c04, 2194998547);
  (0x23c08, 1562740115); (0x23c0c, 2896163055); (0x23c48, 1288708335); (0x23c58, 910164207);
  (0x23c64, 1040187631); (0x23c70, 1170211055); (0x23c9c, 50455); (0x23ca0, 2416260355);
  (0x23cb0, 4294952215); (0x23cb4, 4294952343); (0x23cb8, 839189779); (0x23cbc, 1373996435);
  (0x23cf8, 50455); (0x23cfc, 2319791363); (0x23d0c, 4294952215); (0x23d10, 4294956439);
  (0x23d14, 539297043); (0x23d18, 2153088403); (0x23d20, 2552229999); (0x23d7c, 54679);
  (0x23d80, 2324018563); (0x23d90, 1271931119); (0x23da4, 1318060271); (0x23db0, 1238376687);
  (0x23dc0, 46359); (0x23dc4, 2110076163); (0x23dd4, 4294956311); (0x23dd8, 4294952343);
  (0x23ddc, 2373256467); (0x23de0, 1139115411); (0x23df4, 2384457839); (0x23e8c, 46359);
  (0x23e90, 1896166659); (0x23ea0, 4294952215); (0x23ea4, 4294956439); (0x23ea8, 115672339);
  (0x23eac, 2342880659); (0x23eb4, 4275040367); (0x23f04, 948961519); (0x23f20, 89129199);
  (0x23f34, 46359); (0x23f38, 1720005891); (0x23f48, 4294952215); (0x23f4c, 4294952343);
  (0x23f50, 4234478867); (0x23f54, 995460499); (0x23f6c, 4082102383); (0x23f70, 46359);
  (0x23f74, 1657091331); (0x23f84, 4294952215); (0x23f88, 4294952343); (0x23f8c, 1505035539);
  (0x23f90, 932545939); (0x23f98, 4035965167); (0x23fd8, 46359); (0x23fdc, 1548039427);
  (0x23fec, 4294952215); (0x23ff0, 4294952343); (0x23ff4, 4062512403); (0x23ff8, 1772455315);
  (0x24000, 3926913135); (0x24008, 46487); (0x2400c, 1497740675); (0x24020, 4294952215);
  (0x24024, 4294952343); (0x24028, 290784531); (0x2402c, 1717929363); (0x24034, 3872387183);
  (0x24060, 46359); (0x24064, 1405433091); (0x24074, 4294952215); (0x24078, 4294952343);
  (0x2407c, 3919906067); (0x24080, 667256211); (0x24088, 3784306799); (0x24090, 46487);
  (0x24094, 1355134339); (0x240a8, 4294952215); (0x240ac, 4294952343); (0x240b0, 1147471123);
  (0x240b4, 612730259); (0x240bc, 3729780847); (0x240e8, 46359); (0x240ec, 1262826755);
  (0x240fc, 4294952215); (0x24100, 4294952343); (0x24104, 3777299731); (0x24108, 3626337683);
  (0x24110, 3641700463); (0x24114, 46359); (0x24118, 1216689411); (0x24128, 4294952215);
  (0x2412c, 4294952343); (0x24130, 862258451); (0x24134, 3580200339); (0x2413c, 3595563119);
  (0x24160, 46359); (0x24164, 1136997635); (0x24174, 4294952215); (0x24178, 4294952343);
  (0x2417c, 3651470611); (0x24180, 810911123); (0x24188, 3515871343); (0x241ac, 46359);
  (0x241b0, 1057305859); (0x241c0, 4294952215); (0x241c4, 4294952343); (0x241c8, 3571778835);
  (0x241cc, 3408233875); (0x241d4, 3436179567); (0x241f8, 46359); (0x241fc, 977614083);
  (0x2420c, 4294952215); (0x24210, 4294952343); (0x24214, 3492087059); (0x24218, 3504702867);
  (0x24220, 3574591599); (0x24244, 46359); (0x24248, 897922307); (0x24258, 4294952215);
  (0x2425c, 4294952343); (0x24260, 3412395283); (0x24264, 933594515); (0x2426c, 3276796015);
  (0x242f8, 2250240239); (0x24310, 46359); (0x24314, 4249171203); (0x24328, 4294952215);
  (0x2432c, 4294952343); (0x24330, 3289711891); (0x24334, 3556083091); (0x24338, 2387603695);
  (0x24340, 46359); (0x24344, 4198839555); (0x24354, 4294952215); (0x24358, 4294952343);
  (0x2435c, 2418345235); (0x24360, 3509945747); (0x2437c, 2261774447); (0x2438c, 3122655471);
  (0x24398, 3914330351); (0x243d0, 4294952343); (0x243d4, 499484435); (0x24544, 2581590255);
  (0x24554, 46359); (0x24558, 3640997123); (0x24568, 4294952215); (0x2456c, 4294948247);
  (0x24570, 2619671827); (0x24574, 2090173843); (0x24580, 46359); (0x24584, 3594859779);
  (0x24594, 4294952215); (0x24598, 4294948247); (0x2459c, 2448753939); (0x245a0, 2044036499);
  (0x245a8, 46359); (0x245ac, 3552916739); (0x245bc, 4294948119); (0x245c0, 4294948247);
  (0x245c4, 1638204691); (0x245c8, 2002093459); (0x245d0, 46359); (0x245d4, 3510973699);
  (0x245e4, 4294952215); (0x245e8, 4294948247); (0x245ec, 3381986579); (0x245f0, 1960150419);
  (0x24610, 3718242415); (0x24634, 46487); (0x24638, 3406148995); (0x24648, 4294952215);
  (0x2464c, 4294948247); (0x24650, 3301246227); (0x24654, 1855292819); (0x24664, 46487);
  (0x24668, 3355817347); (0x24678, 4294952215); (0x2467c, 4294948247); (0x24680, 2520057107);
  (0x24684, 1804961171); (0x2468c, 3642745071); (0x24698, 46359); (0x2469c, 3301258499);
  (0x246b0, 4294948119); (0x246b4, 4294948247); (0x246b8, 1462043923); (0x246bc, 1746240915);
  (0x246c4, 3584024815); (0x246e0, 46487); (0x246e4, 3225793923); (0x246f4, 4294952215);
  (0x246f8, 4294948247); (0x246fc, 2438268179); (0x24700, 1674937747); (0x24718, 46359);
  (0x2471c, 3167040771); (0x24730, 4294952215); (0x24734, 4294948247); (0x24738, 2854552851);
  (0x2473c, 1612023187); (0x24744, 46359); (0x24748, 3120903427); (0x2475c, 4294948119);
  (0x24760, 4294948247); (0x24764, 1464141075); (0x24768, 1565885843); (0x2476c, 3407864047);
  (0x24780, 1056964847); (0x247a4, 46359); (0x247a8, 3020240131); (0x247bc, 4294952215);
  (0x247c0, 4294948247); (0x247c4, 2345993491); (0x247c8, 1465222547); (0x24808, 2026901743);
  (0x24810, 2018513135); (0x2481c, 46359); (0x24820, 2894411011); (0x24830, 4294952215);
  (0x24834, 4294948247); (0x24838, 3157591315); (0x2483c, 1327859091); (0x24850, 3168788591);
  (0x248b4, 46359); (0x248b8, 2735027459); (0x248c8, 4294948119); (0x248cc, 1291126035);
  (0x248d4, 46359); (0x248d8, 2701473027); (0x248e8, 4294952215); (0x248ec, 2453996819);
  (0x24904, 46359); (0x24908, 2651141379); (0x24918, 4294948119); (0x2491c, 1735722259);
  (0x24924, 46359); (0x24928, 2617586947); (0x24938, 4294948119); (0x2493c, 1690633491);
  (0x24940, 4294952343); (0x24944, 2684716435); (0x2497c, 3017793647); (0x249e8, 1196429551);
  (0x24a14, 1150292207); (0x24a24, 46359); (0x24a2c, 2349153411); (0x24a30, 4294952215);
  (0x24a34, 2409957907); (0x24a38, 4294948119); (0x24a3c, 452266643); (0x24b64, 2287984879);
  (0x24bc0, 4188004591); (0x24be4, 3835683055); (0x24bf0, 3016749295); (0x24c10, 742392047);
  (0x24c28, 42263); (0x24c2c, 1808086275); (0x24c3c, 4294952215); (0x24c40, 4294952343);
  (0x24c44, 2276787475); (0x24c48, 2295694739); (0x24c50, 42263); (0x24c54, 1766143235);
  (0x24c64, 4294948119); (0x24c68, 4294952343); (0x24c6c, 4179952915); (0x24c70, 2253751699);
  (0x24c9c, 4107264111); (0x24e60, 42263); (0x24e64, 1212495107); (0x24e74, 4294948119);
  (0x24e78, 4294948247); (0x24e7c, 311756051); (0x24e80, 1700103571); (0x24e88, 3591364847);
  (0x24f14, 2253385967); (0x24f20, 4229947631); (0x24f34, 4129284335); (0x24f40, 2933907695);
  (0x24f4c, 4263502063); (0x25020, 42263); (0x25024, 742733059); (0x25034, 4294948119);
  (0x25038, 4294948247); (0x2503c, 38077715); (0x25040, 1091929491); (0x25048, 42391);
  (0x2504c, 700822915); (0x2505c, 4294948119); (0x25060, 4294948247); (0x25064, 3215262995);
  (0x25068, 1049986451); (0x2508c, 3050299503); (0x25170, 42263); (0x25174, 503657731);
  (0x25184, 4294948119); (0x25188, 4294948375); (0x2518c, 4268033299); (0x25190, 3932554899);
  (0x2519c, 2932859119); (0x251a4, 42263); (0x251a8, 449131779); (0x251b8, 4294948119);
  (0x251bc, 4294948247); (0x251c0, 201655571); (0x251c4, 3877995923); (0x25278, 42263);
  (0x2527c, 226833667); (0x2528c, 4294948119); (0x25290, 4294948247); (0x25294, 382010643);
  (0x25298, 3655697811); (0x252a0, 42263); (0x252a4, 184890627); (0x252b4, 4294948119);
  (0x252b8, 4294948247); (0x252bc, 3985966355); (0x252c0, 3613754771); (0x252f0, 2739921007);
  (0x25300, 42263); (0x25304, 84227331); (0x25314, 4294948119); (0x25318, 4294948247);
  (0x2531c, 2660566291); (0x25320, 3513091475); (0x25338, 42263); (0x2533c, 25507075);
  (0x2534c, 4294948119); (0x25350, 4294948247); (0x25354, 2524251411); (0x25358, 3454371219);
  (0x25390, 3192905967); (0x253a0, 4019183855); (0x253e4, 4027572463); (0x253fc, 2563760367);
  (0x25424, 3411013871); (0x25438, 2225070319); (0x25444, 3926909167); (0x25448, 42263);
  (0x2544c, 4035261699); (0x2545c, 4294948119); (0x25460, 4294948247); (0x25464, 3979674899);
  (0x25468, 3169158547); (0x25470, 42263); (0x25474, 3993318659); (0x25484, 4294948119);
  (0x25488, 4294948247); (0x2548c, 3654616339); (0x25490, 3127215507); (0x25498, 42263);
  (0x2549c, 3951375619); (0x254ac, 4294948119); (0x254b0, 4294948247); (0x254b4, 2656371987);
  (0x254b8, 3085272467); (0x254c0, 42263); (0x254c4, 3909432579); (0x254d4, 4294948119);
  (0x254d8, 4294948247); (0x254dc, 2783249683); (0x254e0, 3043329427); (0x254f0, 4188000495);
  (0x254f8, 42263); (0x254fc, 3850712323); (0x2550c, 4294948119); (0x25510, 4294948247);
  (0x25514, 3633644819); (0x25518, 2984609171); (0x2552c, 3683639535); (0x25530, 42263);
  (0x25534, 3791992067); (0x25544, 4294948119); (0x25548, 4294948247); (0x2554c, 9766163);
  (0x25550, 2925888915); (0x2555c, 2749358319); (0x2558c, 981500143); (0x255a0, 4171227375);
  (0x255b8, 3536838895); (0x255bc, 42263); (0x255c0, 3645191427); (0x255d0, 4294944023);
  (0x255d4, 4294948247); (0x255d8, 2114258195); (0x255dc, 2779088275); (0x255e4, 4095725807)].

Definition v17_reloc : Reloc := {|
  rl_segs := Ubsan.M.loaded_segments;
  rl_dtab := v17_dtab;
  rl_stab := v17_stab;
  rl_img_lo := 0x10000; rl_rw_lo := 0x1f000; rl_img_hi := 0x52000;
  rl_dtab_ok := eq_refl |}.
End V17Reloc.

From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require StartupTac.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require ArgvEnv.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require RefLayout.
Module V17StartupDefs.
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
Import OSSVerify.leptonica.kernel_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.StartupTac.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.ArgvEnv.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.RefLayout.
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
      (Z_to_bv 64 0x51008) (word_to_le_bytes 4 (v_lw rwa)))
      (Z_to_bv 64 0x5100c) (word_to_le_bytes 4 (v_lw rwb)))
      (Z_to_bv 64 0x51009) [Z_to_bv 8 0]) (Z_to_bv 64 0x51008) 8 = Some guard_bytes.
  Proof.
    intros segs D. unfold guard_bytes.
    set (A := word_to_le_bytes 4 (v_lw rwa)). set (B := word_to_le_bytes 4 (v_lw rwb)).
    assert (HA : length A = 4%nat) by (subst A; apply length_N_to_le_bytes).
    assert (HB : length B = 4%nat) by (subst B; apply length_N_to_le_bytes).
    assert (Hin : rdn segs (wbytes D (Z_to_bv 64 0x51008) A) (Z_to_bv 64 0x51008) 4 = Some A).
    { rewrite <- HA at 1. apply rdn_wbytes_hit. rewrite HA. unorm. lia. }
    change 8%nat with (1 + (1 + (2 + 4)))%nat.
    apply rdn_app.
    { rewrite rdn_wbytes_out by (cbn [length]; unorm; lia).
      rewrite rdn_wbytes_out by (rewrite ?HB; unorm; lia).
      exact (SeqExec.rdn_firstn _ _ _ _ _ 1 Hin ltac:(lia)). }
    apply rdn_app.
    { change (Z_to_bv 64 331784 + nat_to_word 1) with (Z_to_bv 64 0x51009 : word).
      exact (rdn_wbytes_hit segs [Z_to_bv 8 0] _ (Z_to_bv 64 0x51009) ltac:(cbn [length]; unorm; lia)). }
    apply rdn_app.
    { change (Z_to_bv 64 331784 + nat_to_word 1 + nat_to_word 1) with (Z_to_bv 64 0x5100a : word).
      rewrite rdn_wbytes_out by (cbn [length]; unorm; lia).
      rewrite rdn_wbytes_out by (rewrite ?HB; unorm; lia).
      exact (SeqExec.rdn_skipn _ _ _ _ _ 2 Hin ltac:(lia)). }
    change (Z_to_bv 64 331784 + nat_to_word 1 + nat_to_word 1 + nat_to_word 2) with (Z_to_bv 64 0x5100c : word).
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
      (Z_to_bv 64 0x30cd0) (word_to_le_bytes 8 envp_w))          (* [comment removed for export] *)
      (Z_to_bv 64 0x51030) (word_to_le_bytes 8 auxv_w))          (* [comment removed for export] *)
      (Z_to_bv 64 0x51090) (word_to_le_bytes 8 hw))            (* [comment removed for export] *)
      (Z_to_bv 64 0x51058) (word_to_le_bytes 8 (Z_to_bv 64 4096))) (* [comment removed for export] *)
      (Z_to_bv 64 0x51020) (word_to_le_bytes 8 pn_w))            (* [comment removed for export] *)
      (Z_to_bv 64 0x51018) (word_to_le_bytes 8 progname_w).      (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition J_lsm (J : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes
    (wbytes (wbytes (wbytes (wbytes J
      (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
      (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0x165dc)))
      (Z_to_bv 64 (bv_unsigned sp0 - 48)) (word_to_le_bytes 8 argv_w))
      (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 argc_w))
      (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0x135b8)).

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
      (Z_to_bv 64 0x50dc8) (word_to_le_bytes 8 (Z_to_bv 64 0)))        (* [comment removed for export] *)
      (Z_to_bv 64 0x50dd8) (word_to_le_bytes 8 (Z_to_bv 64 0)))        (* [comment removed for export] *)
      (Z_to_bv 64 0x50dd0) (word_to_le_bytes 8 (Z_to_bv 64 8)))        (* [comment removed for export] *)
      (Z_to_bv 64 0x51040) (word_to_le_bytes 8 (Z_to_bv 64 0xe0)))     (* [comment removed for export] *)
      (Z_to_bv 64 0x51048) (word_to_le_bytes 8 (Z_to_bv 64 8)))        (* [comment removed for export] *)
      (Z_to_bv 64 0x30db0) (word_to_le_bytes 8 (Z_to_bv 64 0)))        (* [comment removed for export] *)
      (Z_to_bv 64 0x30d98) (word_to_le_bytes 8 (Z_to_bv 64 0x30db0)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x30cd8) (word_to_le_bytes 8 (Z_to_bv 64 0x30cd8)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x51028) [Z_to_bv 8 1])                              (* [comment removed for export] *)
      (Z_to_bv 64 0x30d00) (word_to_le_bytes 4 (Z_to_bv 64 2)).        (* [comment removed for export] *)

  Definition D_tlsB (tid : word) (D : word -> option byte) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes D
      (Z_to_bv 64 0x30cf8) (word_to_le_bytes 4 tid))                   (* [comment removed for export] *)
      (Z_to_bv 64 0x30d70) (word_to_le_bytes 8 (Z_to_bv 64 0x51060)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x30d50) (word_to_le_bytes 8 (Z_to_bv 64 0x30d50)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x30ce0) (word_to_le_bytes 8 (Z_to_bv 64 0x30cd8)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x30ce8) (word_to_le_bytes 8 (Z_to_bv 64 0x30cd8)))  (* [comment removed for export] *)
      (Z_to_bv 64 0x30cf0) (word_to_le_bytes 8 (Z_to_bv 64 0)).        (* [comment removed for export] *)

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
      (Z_to_bv 64 0x51008) (word_to_le_bytes 4 (v_lw (rwa drw))))  (* [comment removed for export] *)
      (Z_to_bv 64 0x5100c) (word_to_le_bytes 4 (v_lw (rwb drw))))  (* [comment removed for export] *)
      (Z_to_bv 64 0x51009) [Z_to_bv 8 0])                     (* [comment removed for export] *)
      (Z_to_bv 64 0x30d90) (word_to_le_bytes 8 (canary_w drw)).     (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition D_fd (D : word -> option byte) : word -> option byte :=
    wbytes D (Z_to_bv 64 0x20c50) [Z_to_bv 8 1].

  (* [comment removed for export] *)
  Definition D_main (tid : word) : word -> option byte := D_fd (D_ssp (D_tls tid D_libc)).

End Defs.
End V17StartupDefs.

From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Musl Require PFSpec.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica.VL Require LeptStderr.
Module V17LeptEnv.
Import Stdlib.ZArith.ZArith.
Import Stdlib.Lists.List.
Import Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Reloc.Reloc.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica.VL.LeptStderr.
Import V17Reloc.
(* [comment removed for export] *)







Lemma v17_lenv_ok1 : @PFSpec.ls_ok1 v17_reloc (@LG v17_reloc) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma v17_lenv_ok2 : @PFSpec.ls_ok2 v17_reloc (@LG v17_reloc) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition v17_lenv_vl : RelocLeptEnvVL v17_reloc := {| rl_lenv_ok1 := v17_lenv_ok1; rl_lenv_ok2 := v17_lenv_ok2 |}.
End V17LeptEnv.

From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require CatSim.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require SeqExec.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require StepTac.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require WalkTac.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require MmapSim.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require RefMemcpyLib.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Musl Require MemcpyBase.
Module V17MemcpyBase.
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
Import OSSVerify.leptonica.kernel_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.SeqExec.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.StepTac.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.StoreOk.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.WalkTac.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.MmapSim.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.RefMemcpyLib.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Reloc.Reloc.
Import V17Reloc.
(* [comment removed for export] *)








Import ListNotations.
Open Scope bv_scope.

Abbreviation RSEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)
Abbreviation mcH := (@MemcpyBase.mcH v17_reloc).
Abbreviation MCH := (@MemcpyBase.MCH v17_reloc).

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
End V17MemcpyBase.

From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Reloc Require RelocCode.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Reloc Require CanonCode.
Module V17RelocCode.
Import Stdlib.ZArith.ZArith.
Import Stdlib.Lists.List.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Reloc.Reloc.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Reloc.RelocCode.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Reloc.CanonCode.
Import V17Reloc.
(* [comment removed for export] *)





Lemma v17_code_ok : code_check (@rl_segs v17_reloc) (@rl_delta v17_reloc) canon_code = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Definition v17_code : RelocCode v17_reloc := {| rl_code_ok := v17_code_ok |}.
End V17RelocCode.

From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require StreamSim.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Reloc Require RelocImg.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Reloc Require CanonImg.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Reloc Require RelocSpan.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Reloc Require CanonSpans.
Module V17RelocImg.
Import Stdlib.ZArith.ZArith.
Import Stdlib.Lists.List.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.StreamSim.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Reloc.Reloc.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Reloc.RelocImg.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Reloc.CanonImg.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Reloc.RelocSpan.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Reloc.CanonSpans.
Import V17Reloc.
(* [comment removed for export] *)





Local Open Scope Z_scope.

Lemma v17_cells_ok : @cells_check v17_reloc canon_cells = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Definition v17_img : RelocImg v17_reloc := {| rl_cells_ok := v17_cells_ok |}.

Lemma v17_data_wseg : wseg_ok (@rl_segs v17_reloc) (Z_to_bv 64 0x20000) (Z.to_nat (@rl_img_hi v17_reloc - 0x20000)) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma v17_data_ok : (0 <=? 0x20000) && (0x20000 <=? @rl_img_hi v17_reloc) && (@rl_img_hi v17_reloc <=? 2^32) = true.
Proof. reflexivity. Qed.

Definition v17_data : RelocData v17_reloc := {| rl_data_lo := 0x20000; rl_data_ok := v17_data_ok; rl_data_wseg := v17_data_wseg |}.

Lemma v17_hull_ok : @hull_okb v17_reloc v17_data = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma v17_spans_ok : @spans_check v17_reloc v17_data canon_spans = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma v17_orders_ok : @orders_check v17_reloc canon_spans canon_order = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition v17_spans : RelocSpans v17_reloc v17_data := {| rl_hull_ok := v17_hull_ok; rl_spans_ok := v17_spans_ok; rl_orders_ok := v17_orders_ok |}.
End V17RelocImg.

From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng Require RelocLayout.
Module V17RelocML.
Import Stdlib.ZArith.ZArith.
Import Stdlib.NArith.NArith.
Import Stdlib.Lists.List.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.MallocLayout.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.RelocLayout.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Reloc.Reloc.
Import V17MallocLayout.
Import V17Reloc.
(* [comment removed for export] *)







Lemma lv17_reloc : LU17 = reloc_layout v17_reloc.
Proof. unfold LU17, reloc_layout. f_equal; first [ reflexivity | apply bv_eq; reflexivity ]. Qed.

(* [comment removed for export] *)
Ltac v17_ml_tail t := rewrite lv17_reloc; exact t.
End V17RelocML.

From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Reloc Require RelocSites.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Reloc Require CanonSites.
Module V17RelocSites.
Import Stdlib.ZArith.ZArith.
Import Stdlib.Lists.List.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Reloc.Reloc.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Reloc.RelocCode.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Reloc.RelocSites.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Reloc.CanonSites.
Import V17Reloc.
(* [comment removed for export] *)





Lemma v17_sites_ok : @sites_check v17_reloc canon_sites = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Definition v17_sites : RelocSites v17_reloc := {| rl_sites_ok := v17_sites_ok |}.
End V17RelocSites.

From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Reloc Require CanonCodeVL.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Reloc Require CanonSitesVL.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Reloc Require CanonImgVL.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica Require RelocLept.
Module V17RelocVL.
Import Stdlib.ZArith.ZArith.
Import Stdlib.Lists.List.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Reloc.Reloc.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Reloc.RelocCode.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Reloc.RelocSites.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Reloc.RelocImg.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Reloc.CanonCodeVL.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Reloc.CanonSitesVL.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Reloc.CanonImgVL.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica.RelocLept.
Import V17Reloc.
(* [comment removed for export] *)






Lemma v17_code_vl_ok : code_check (@rl_segs v17_reloc) (@rl_delta v17_reloc) canon_code_VL = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition v17_code_vl : RelocCodeVL v17_reloc := {| rl_code_vl_ok := v17_code_vl_ok |}.

Lemma v17_sites_vl_ok : @sites_check v17_reloc canon_sites_VL = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition v17_sites_vl : RelocSitesVL v17_reloc := {| rl_sites_vl_ok := v17_sites_vl_ok |}.

Lemma v17_lept_ok : wr_readable_chk (@rl_segs v17_reloc) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition v17_lept : RelocLept v17_reloc := {| rl_wr_readable_ok := v17_lept_ok; rl_pages_ok := eq_refl; rl_clr_extra := nil |}.

Lemma v17_strs_vl_ok : @strs_check v17_reloc canon_strs_VL = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma v17_cells_vl_ok : @cells_check v17_reloc canon_cells_VL = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma v17_spans_vl_ok : @RelocLept.spans_check v17_reloc canon_spans_VL = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition v17_img_vl : RelocImgVL v17_reloc := {| rl_strs_vl_ok := v17_strs_vl_ok; rl_cells_vl_ok := v17_cells_vl_ok; rl_spans_vl_ok := v17_spans_vl_ok |}.
End V17RelocVL.

From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require ExitSim.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require ShapeAlg.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require Nodes.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica Require LibAtomic.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require SumWalkTac.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require RefNodes.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Musl Require ExitBase.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.CliDriver Require AgentNodesG.
Module V17ExitBase.
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
Import OSSVerify.leptonica.kernel_fuzzer.images.Ubsan.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Import LinuxProcessSemantics.LinuxProcessSem.Fs.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.LinuxProcessSem.Monad.
Import LinuxProcessSemantics.LinuxProcessSem.Specs.
Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.SeqExec.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.StepTac.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.WalkTac.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.StoreOk.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.StreamSim.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.MmapSim.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.ExitSim.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Nodes.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica.LibAtomic.
Export OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica.SumWalkTac.
Export OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.RefNodes.
Export OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.CliDriver.AgentNodesG.
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
  (0x20000 <= bv_unsigned a)%Z -> (bv_unsigned a + Z.of_nat n <= 0x52000)%Z ->
  store_ok RSEGS m a n = true.
Proof.
  exact (@ExitBase.store_ok_data V17Reloc.v17_reloc V17RelocImg.v17_data).
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
  rdn RSEGS mem (Z_to_bv 64 0x5102b) 1%nat = Some [Z_to_bv 8 0]            (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0x51458) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))       (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0x51448) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))       (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0x20c38) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x20b50)) (* [comment removed for export] *)
  /\ rdn RSEGS mem (Z_to_bv 64 0x20b48) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x20a60)). (* [comment removed for export] *)

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End V17ExitBase.

From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require MuslStrlen.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica Require PortLib.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Musl Require Memchr.
Module V17Memchr.
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
Import OSSVerify.leptonica.kernel_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.SeqExec.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.StepTac.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.StoreOk.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.WalkTac.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.MmapSim.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.MuslStrlen.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.RefMemcpyLib.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica.PortLib.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Reloc.Reloc.
Import V17Reloc.
Import V17MemcpyBase.
(* [comment removed for export] *)










Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition rodata_clear (mem : word -> option byte) : Prop :=
  forall i, (0x116d8 <= i < 0x116f0)%Z -> mem (Z_to_bv 64 i) = None.

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
Lemma mchrH_generic : forall mem s buf K n, mchrH mem s buf K n -> @Memchr.mchrH v17_reloc mem s buf K n.
Proof.
  intros mem s buf K n [H1 H2 H3 H4 H5 H6 H7 H8 H9].
  exact (@Memchr.MCHRH v17_reloc mem s buf K n H1 H2 H3 H4 H5 H6 H7 H8
           (@Memchr.rodata_clear_hull v17_reloc mem 0x116d8 0x116f0 eq_refl H9)).      (* [comment removed for export] *)
Qed.
End V17Memchr.

From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Musl Require Memcpy.
Module V17Memcpy.
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
Import OSSVerify.leptonica.kernel_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.SeqExec.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.StepTac.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.StoreOk.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.WalkTac.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.MmapSim.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.RefMemcpyLib.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Reloc.Reloc.
Import V17Reloc.
Import V17RelocCode.
Import V17MemcpyBase.
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
      msteps RSEGS (mkst regs (0x1dfb4 : word) mem0 rom) (mkst regs' ret (wbytes mem0 dst bs) rom)
      /\ keeps regs regs'.
  Proof. rl_tail (@Memcpy.ref_memcpy fx v17_reloc v17_code). Qed.
End Contract.
End V17Memcpy.

From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require PureModel.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica Require SumWalkTac.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica Require WalksLib.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Musl Require Memset.
Module V17Memset.
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
Import OSSVerify.leptonica.kernel_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.StartupTac.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.RefMemcpyLib.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.PureModel.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica.SumWalkTac.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica.WalksLib.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Reloc.Reloc.
Import V17Reloc.
Import V17RelocCode.
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
      msteps SEGS (mkst regs (0x1e3b8 : word) M rom) (mkst regs' ret (zf M d [(0, n)]%Z) rom)
      /\ getr regs' 10 = Z_to_bv 64 d
      /\ regs_agree (fun r => In r memset_clob) regs regs'.
  Proof. rl_tail (@Memset.memset_spec fx v17_reloc v17_code). Qed.

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
    realizes SEGS (mkCfg (mkst regs (0x1e3b8 : word) M rom) model) S.
  Proof. rl_tail (@Memset.memset_at fx v17_reloc v17_code). Qed.
End Contract.
End V17Memset.

From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng Require RefStmts.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng Require RRef_calloc.
Module V17Ref_calloc.
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
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.MallocLayout.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.RefStmts.
Import V17MallocLayout.
Import V17Reloc.
Import V17RelocCode.
Import V17RelocSites.
Import V17RelocML.
(* [comment removed for export] *)







Section Calloc.
Context {fx : FPState}.

Theorem calloc_refines : calloc_stmt.
Proof. v17_ml_tail (@RRef_calloc.calloc_refines fx v17_reloc v17_code v17_sites). Qed.
End Calloc.
End V17Ref_calloc.

From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng Require RRef_free.
Module V17Ref_free.
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
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.MallocLayout.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.RefStmts.
Import V17MallocLayout.
Import V17Reloc.
Import V17RelocCode.
Import V17RelocSites.
Import V17RelocML.
(* [comment removed for export] *)







Section Free.
Context {fx : FPState}.

Theorem free_refines : free_stmt.
Proof. v17_ml_tail (@RRef_free.free_refines fx v17_reloc v17_code v17_sites). Qed.
End Free.
End V17Ref_free.

From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng Require RRef_malloc.
Module V17Ref_malloc.
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
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.MallocLayout.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.RefStmts.
Import V17MallocLayout.
Import V17Reloc.
Import V17RelocCode.
Import V17RelocSites.
Import V17RelocML.
(* [comment removed for export] *)







Section Malloc.
Context {fx : FPState}.

Theorem malloc_refines : malloc_stmt.
Proof. v17_ml_tail (@RRef_malloc.malloc_refines fx v17_reloc v17_code v17_sites). Qed.
End Malloc.
End V17Ref_malloc.

From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica Require PFLib.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Reloc Require RelocBlocks.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Musl Require RelocRW.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Musl Require RelocPF.
Module V17RelocMusl.
Import Stdlib.ZArith.ZArith.
Import Stdlib.Lists.List.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica.PFLib.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Reloc.Reloc.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Reloc.RelocBlocks.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Reloc.RelocImg.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Reloc.RelocSpan.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Reloc.CanonSpans.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Musl.RelocRW.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Musl.RelocPF.
Import V17Reloc.
Import V17RelocImg.
(* [comment removed for export] *)






Local Open Scope Z_scope.

Lemma v17_dwin_bounds : @dwin_bounds_chk v17_reloc v17_data = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition v17_rw : RelocRW v17_reloc v17_data := {| rl_dwin_bounds := v17_dwin_bounds; rl_rw_hull := v17_hull_ok; rl_rw_spans := v17_spans_ok; rl_rw_orders := v17_orders_ok |}.

Lemma v17_segs_lo : segs_lo (@rl_segs v17_reloc) = @rl_img_lo v17_reloc.
Proof. vm_cast_no_check (@eq_refl Z (@rl_img_lo v17_reloc)). Qed.
Lemma v17_segs_hi : segs_hi (@rl_segs v17_reloc) = @rl_img_hi v17_reloc.
Proof. vm_cast_no_check (@eq_refl Z (@rl_img_hi v17_reloc)). Qed.
Lemma v17_pf_bounds : @pf_bounds_chk v17_reloc = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma v17_pf_prefix : pf_prefix_ok (@rl_segs v17_reloc) (0x102e7 + @rl_delta v17_reloc B_S_102e7) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition v17_pf : RelocPF v17_reloc :=
  {| rl_segs_lo_val := v17_segs_lo; rl_segs_hi_val := v17_segs_hi; rl_pf_bounds := v17_pf_bounds; rl_pf_prefix := v17_pf_prefix |}.
End V17RelocMusl.

From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Musl Require RelocStart.
Module V17RelocStart.
Import Stdlib.ZArith.ZArith.
Import Stdlib.Lists.List.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Reloc.Reloc.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Reloc.RelocBlocks.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Reloc.RelocImg.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Musl.RelocStart.
Import V17Reloc.
Import V17RelocImg.
(* [comment removed for export] *)





Local Open Scope Z_scope.

Lemma v17_start_ok : start_ok (@rl_delta v17_reloc 8%positive) (@rl_data_lo v17_reloc v17_data) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Definition v17_start : RelocStart v17_reloc v17_data := {| rl_start_ok := v17_start_ok |}.
End V17RelocStart.

From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require VmLedger.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require AllocIface.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng Require MallocTree.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng Require MallocOps.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng Require MallocIface.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng Require MallocInv_defs.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng Require MallocIfaceX.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng Require MallocInv_aslot_iface.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng Require MallocInv_malloc_iface.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng Require MallocInv_aslot.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng Require MallocInv_mal6.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng Require MallocInv_calloc2.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng Require MallocInv_freetopX.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng Require AllocBase.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng Require AllocCalloc.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng Require MallocAllocLayout.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng Require MallocGlue.
Module V17Alloc.
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
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.PureModel.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.VmLedger.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.AllocIface.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.MallocLayout.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.MallocTree.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.MallocOps.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.MallocIface.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.MallocInv_defs.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.MallocIfaceX.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.MallocInv_aslot_iface.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.MallocInv_malloc_iface.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.MallocInv_aslot.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.MallocInv_mal6.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.MallocInv_calloc2.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.MallocInv_freetopX.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.AllocBase.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.MallocAllocLayout.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.MallocGlue.
Import V17MallocLayout.
Import V17Ref_malloc.
Import V17Ref_free.
Import V17Ref_calloc.
(* [comment removed for export] *)





Import ListNotations.
Local Open Scope Z_scope.

Definition u17_alloc_slot_okW (HT : HeapTop) : alloc_slot_specW (ML:=LU17) (HT:=HT) := alloc_slot_okW (HT:=HT).

Definition u17_free_okX (HT : HeapTop) := free_okX (ML:=LU17) (HT:=HT).

Definition u17_malloc_okX (HT : HeapTop) := malloc_okX (ML:=LU17) (HT:=HT) (u17_alloc_slot_okW HT).
Definition u17_calloc_okX (HT : HeapTop) := calloc_okX (ML:=LU17) (HT:=HT) (u17_malloc_okX HT).

Definition u17_base : AllocBase (AL:=mallocng_alloc_layout (ML:=LU17)) :=
  mallocng_base (ML:=LU17) u17_malloc_okX u17_free_okX (fun fx => malloc_refines (fx:=fx)) (fun fx => free_refines (fx:=fx)).
Definition u17_calloc : AllocCalloc (AL:=mallocng_alloc_layout (ML:=LU17)) (CL:=mallocng_calloc_layout (ML:=LU17)) :=
  mallocng_calloc (ML:=LU17) u17_malloc_okX u17_free_okX u17_calloc_okX
    (fun fx => malloc_refines (fx:=fx)) (fun fx => free_refines (fx:=fx)) (fun fx => calloc_refines (fx:=fx)).
End V17Alloc.

From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica Require SumSpecs.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica Require PFSpecLib.
Module V17PFSpec.
Import Stdlib.ZArith.ZArith.
Import Stdlib.Lists.List.
Import Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OSSVerify.leptonica.kernel_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica.SumSpecs.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica.PFLib.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica.PFSpecLib.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Reloc.Reloc.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Reloc.RelocCode.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Reloc.RelocSites.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Reloc.RelocImg.
Import V17Reloc.
Import V17RelocCode.
Import V17RelocSites.
Import V17RelocImg.
Import V17RelocMusl.
Import V17PFBase.
(* [comment removed for export] *)








Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition ls_ok (nS : nat) (fmts : list Z) (L : SSP.ls_addrs) : bool := @PFSpec.ls_ok v17_reloc nS fmts L.
Definition ls_ok1 (L : SSP.ls_addrs) : bool := ls_ok 1 (SSP.ls_fmts1 L) L.
Definition ls_ok2 (L : SSP.ls_addrs) : bool := ls_ok 2 (SSP.ls_fmts2 L) L.

Section Contracts.
Context {fx : FPState}.
#[local] Existing Instance v17_reloc.
#[local] Existing Instance v17_code.
#[local] Existing Instance v17_sites.
#[local] Existing Instance v17_data.
#[local] Existing Instance v17_img.
#[local] Existing Instance v17_rw.
#[local] Existing Instance v17_pf.

(* [comment removed for export] *)
Theorem lept_stderr_s1_contract : forall L, ls_ok1 L = true -> SSP.sum_contract SEGS (SSP.spec_lept_stderr_s1 L).
Proof. exact PFSpec.lept_stderr_s1_contract. Qed.

(* [comment removed for export] *)
Theorem lept_stderr_s2_contract : forall L, ls_ok2 L = true -> SSP.sum_contract SEGS (SSP.spec_lept_stderr_s2 L).
Proof. exact PFSpec.lept_stderr_s2_contract. Qed.
End Contracts.
End V17PFSpec.

From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.CliDriver Require Amb.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require RefNodesMF.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Musl Require StartupBase.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Musl Require StartupDefs.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Musl Require Startup.
Module V17Startup.
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
Import OSSVerify.leptonica.kernel_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.CliDriver.Amb.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.PureModel.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.RefNodesMF.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.StartupTac.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.ArgvEnv.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.RefLayout.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Reloc.Reloc.
Import V17StartupDefs.
Import V17Reloc.
Import V17RelocCode.
Import V17RelocSites.
Import V17RelocImg.
Import V17RelocMusl.
Import V17RelocStart.
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
              (Z_to_bv 64 0x16440) (pn_w sp0 av ev) s1v (Z_to_bv 64 0x51028)
              (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) in
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes J6
    (Z_to_bv 64 (bv_unsigned sp0 - 424)) (word_to_le_bytes 8 (Z_to_bv 64 0x16448)))   (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))           (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))          (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)))          (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0)))          (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0)))          (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 56)) (word_to_le_bytes 8 (Z_to_bv 64 0x1663c)))    (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 64)) (word_to_le_bytes 8 (argv_w sp0)))             (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 72)) (word_to_le_bytes 8 (argc_w av)))              (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 88)) (word_to_le_bytes 8 (Z_to_bv 64 0x1658c)))    (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp0 - 96)) (word_to_le_bytes 8 (Z_to_bv 64 0x1f960)).    (* [comment removed for export] *)

(* [comment removed for export] *)
Record main_entry {AMB : Amb} (sp0 : word) (av ev : list (list byte)) (tid : word)
       (regs : bvmap 5 word) (mem : word -> option byte) : Prop := {
  me_ra  : getr regs 1 = Z_to_bv 64 0x1664c;
  me_sp  : getr regs 2 = Z_to_bv 64 (bv_unsigned sp0 - 48);
  me_gp  : getr regs 3 = Z_to_bv 64 0x10800;
  me_tp  : getr regs 4 = Z_to_bv 64 0x30da0;
  me_s0  : getr regs 8 = Z_to_bv 64 (bv_unsigned sp0 + 8);
  me_s1  : getr regs 9 = argcN av;
  me_a0  : getr regs 10 = argcN av;
  me_a1  : getr regs 11 = Z_to_bv 64 (bv_unsigned sp0 + 8);
  me_a2  : getr regs 12 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av));
  me_s2  : getr regs 18 = Z_to_bv 64 0x135b8;
  me_s3  : getr regs 19 = Z_to_bv 64 (bv_unsigned sp0 + 16 + 8 * Z.of_nat (length av));
  me_szero : forall r : reg, In r [20; 21; 22; 23; 24; 25; 26; 27]%list -> getr regs r = Z_to_bv 64 0;
  me_mem : exists (J : word -> option byte) (s1v : word),
             wfJ sp0 J /\ J = J_main sp0 av ev s1v
             /\ mem = cmem sp0 (wrap_mem RPH sp0 av ev a_uid a_hwcap a_draw) J (D_main sp0 av ev a_hwcap a_draw tid)
}.

(* [comment removed for export] *)
Lemma main_entry_L : forall {AMB : Amb} sp0 av ev tid regs mem,
  @Startup.main_entry v17_reloc AMB sp0 av ev tid regs mem -> main_entry sp0 av ev tid regs mem.
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
       realizes rsegs (mkCfg (mkst (fx:=fx0) regs (0x135b8 : word) mem (seg_rom rsegs))
                             (with_tid tid (init_model (segments_reserved rsegs) brk mbase sp lim
                                                      (mkProcInputC argv envp fs0 stdin0)))) K) ->
    realizes rsegs (init_config rsegs rpc rph sp brk mbase a_draw lim (mkProcInputC argv envp fs0 stdin0)) K.
  Proof.
    intros brk mbase lim fs0 stdin0 K HK.
    refine (@Startup.ref_startup_sec v17_reloc v17_code v17_sites v17_img v17_data v17_rw v17_start AMB sp argv envp Hva Hve Hvsp
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
     realizes rsegs (mkCfg (mkst (fx:=fx0) regs (0x135b8 : word) mem (seg_rom rsegs))
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
End V17Startup.

Module V17StdioDefs.
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
Import OSSVerify.leptonica.kernel_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.SeqExec.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.StepTac.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.WalkTac.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.StoreOk.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.StreamSim.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.MmapSim.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.ExitSim.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Nodes.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica.SumWalkTac.
Export V17ExitBase.
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
  rdn RSEGS mem (Z_to_bv 64 0x1fa00) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x51008))
  /\ rdn RSEGS mem (Z_to_bv 64 0x51008) 8%nat = Some (word_to_le_bytes 8 can).

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

Definition atexit_none (mem : word -> option byte) : Prop :=
  rdn RSEGS mem (Z_to_bv 64 0x50df0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).

Definition atexit_one (mem : word -> option byte) : Prop :=
  rdn RSEGS mem (Z_to_bv 64 0x50df0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x50df8))
  /\ rdn RSEGS mem (Z_to_bv 64 0x50de8) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1))
  /\ rdn RSEGS mem (Z_to_bv 64 0x50df8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
  /\ rdn RSEGS mem (Z_to_bv 64 0x50e00) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x16af4))
  /\ rdn RSEGS mem (Z_to_bv 64 0x50f00) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x139e0))
  /\ rdn RSEGS mem (Z_to_bv 64 0x30ca4) 1%nat = Some [Z_to_bv 8 0].

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
  ec_lock : rdn RSEGS mem (Z_to_bv 64 0x51000) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0));
  (* [comment removed for export] *)
  ec_fe   : rdn RSEGS mem (Z_to_bv 64 0x1fa08) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1f968));
  ec_fs   : rdn RSEGS mem (Z_to_bv 64 0x1fa10) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1f960));
  ec_fa   : rdn RSEGS mem (Z_to_bv 64 0x1f960) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x13528));
  (* [comment removed for export] *)
  ec_comp : rdn RSEGS mem (Z_to_bv 64 0x20c98) 1%nat = Some [Z_to_bv 8 0];
  ec_g1   : rdn RSEGS mem (Z_to_bv 64 0x1f9a8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x16a2c));
  ec_g2   : rdn RSEGS mem (Z_to_bv 64 0x1f9b0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
  (* [comment removed for export] *)
  ec_glob : stdio_globals mem;
  (* [comment removed for export] *)
  ec_err  : file_clean mem 0x20a60 wp2 rp2;
  ec_dso  : rdn RSEGS mem (Z_to_bv 64 0x20a18) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x20a18));
  ec_alock : rdn RSEGS mem (Z_to_bv 64 0x50de4) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0));
  ec_atexit : atexit_state mem
}.

(* [comment removed for export] *)
Record stdout_pending (mem : word -> option byte) (wb wp : Z) (bufp bufsz rp1 can : word)
       (pending : list byte) : Prop := {
  sp_lock  : rdn RSEGS mem (Z_to_bv 64 (0x20b50 + 140)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295));
  sp_wpos  : rdn RSEGS mem (Z_to_bv 64 (0x20b50 + 40)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wp));
  sp_wbase : rdn RSEGS mem (Z_to_bv 64 (0x20b50 + 56)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wb));
  sp_write : rdn RSEGS mem (Z_to_bv 64 (0x20b50 + 72)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x18eb4));
  sp_buf   : rdn RSEGS mem (Z_to_bv 64 (0x20b50 + 88)) 8%nat = Some (word_to_le_bytes 8 bufp);
  sp_bsz   : rdn RSEGS mem (Z_to_bv 64 (0x20b50 + 96)) 8%nat = Some (word_to_le_bytes 8 bufsz);
  sp_fd    : rdn RSEGS mem (Z_to_bv 64 (0x20b50 + 120)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1));
  sp_rpos  : rdn RSEGS mem (Z_to_bv 64 (0x20b50 + 8)) 8%nat = Some (word_to_le_bytes 8 rp1);
  sp_rend  : rdn RSEGS mem (Z_to_bv 64 (0x20b50 + 16)) 8%nat = Some (word_to_le_bytes 8 rp1);
  sp_range : (0x51010 <= wb < wp /\ wp <= 0x52000)%Z;
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
    /\ ( (pending = [] /\ exists wp1 rp1, file_clean mem 0x20b50 wp1 rp1)
       \/ (exists (wb wp : Z) (bufp bufsz rp1 can : word),
              stdout_pending mem wb wp bufp bufsz rp1 can pending
              /\ fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1))) ).

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End V17StdioDefs.

From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica Require Frame.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Musl Require Strnlen.
Module V17Strnlen.
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
Import OSSVerify.leptonica.kernel_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.SeqExec.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.StepTac.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.StoreOk.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.WalkTac.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.MmapSim.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.RefMemcpyLib.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica.PortLib.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica.Frame.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Reloc.Reloc.
Import V17Reloc.
Import V17RelocCode.
Import V17RelocSites.
Import V17RelocImg.
Import V17MemcpyBase.
Import V17Memchr.
(* [comment removed for export] *)










Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section VP1. Context {fx : FPState}.
Theorem ref_strnlen : forall mem (s sp : word) buf K n rom regs (ret : word),
  mchrH mem s buf K n ->
  (0 < bv_unsigned s + K)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 32)) 32 = true ->
  (0x116f0 <= bv_unsigned sp - 32)%Z ->
  (bv_unsigned s + Z.of_nat (length buf) <= bv_unsigned sp - 32 \/ bv_unsigned sp <= bv_unsigned s)%Z ->
  ret_ok ret -> getr regs 1 = ret -> getr regs 2 = sp ->
  getr regs 10 = s -> getr regs 11 = Z_to_bv 64 n ->
  exists regs' mem',
    msteps RSEGS (mkst regs (0x1e540 : word) mem rom) (mkst regs' ret mem' rom)
    /\ keeps_cs regs regs'
    /\ getr regs' 10 = Z_to_bv 64 K
    /\ frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - 32), 32%Z)].
Proof.
  rl_tail (fun mem s sp buf K n rom regs ret (HOK : mchrH mem s buf K n) =>
             @Strnlen.ref_strnlen fx v17_reloc v17_code v17_sites v17_img mem s sp buf K n rom regs ret
               (mchrH_generic mem s buf K n HOK)).
Qed.
End VP1.
End V17Strnlen.

From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.CliDriver Require LibWritevG.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.CliDriver Require Spec.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Musl Require StdioDefs.

From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require SpecConsts.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require SymExec.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.CliDriver Require SymExec2.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.CliDriver Require SymExec2Sound.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.CliDriver Require SymRun.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.CliDriver Require SymDrive.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.CliDriver Require SymDriveX.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.CliDriver Require LibKnowFrame.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Musl Require LibStdioCall.
Module V17LibStdioCall.
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
Import OSSVerify.leptonica.kernel_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.SeqExec.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.StoreOk.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Nodes.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.AgentLib.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.SpecConsts.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.SymExec.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.CliDriver.SymExec2.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.CliDriver.SymExec2Sound.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.CliDriver.SymRun.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.CliDriver.SymDrive.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.CliDriver.SymDriveX.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.CliDriver.LibKnowFrame.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Reloc.Reloc.
Import V17ExitBase.
Import V17StdioDefs.
Import V17Reloc.
Import V17RelocCode.
Import V17RelocSites.
Import V17RelocImg.
Import V17RelocMusl.
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
Notation stdio_call := (@LibStdioCall.stdio_call v17_reloc v17_data).

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
Proof. exact (@LibStdioCall.know_ok_frame3 v17_reloc). Qed.

Lemma kimg_cut_sound : forall E M k a n, know_ok RSEGS E M k -> know_ok RSEGS E M (kimg_cut k a n).
Proof. exact (@LibStdioCall.kimg_cut_sound v17_reloc). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma sw_post_L : forall mem su f bufp bufsz mem',
  @StdioDefs.sw_post v17_reloc mem su f bufp bufsz mem' -> sw_post mem su f bufp bufsz mem'.
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
  realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x18eb4) M (seg_rom RSEGS)) model)
           (t_emit (map (WriteEv (Z_to_bv 64 (sc_fd res))) (pending ++ extra)) K).
Proof.
  intros vals ebs sr kn R M model res pending extra K E HR HK Hc wb wp s l su
         H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 HCONT.
  rl_tail (@LibStdioCall.stdio_call_sound_fr _ v17_reloc v17_code v17_sites v17_data v17_rw
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
  realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x18eb4) M (seg_rom RSEGS)) model)
           (t_emit (map (WriteEv (Z_to_bv 64 (sc_fd res))) (pending ++ extra)) K).
Proof.
  intros vals ebs sr kn R M model res pending extra K E HR HK Hc wb wp s l su; intros.
  eapply stdio_call_sound_fr; try eassumption. intros R' M' HR' HK' _. auto.
Qed.
End VP17.
End V17LibStdioCall.

From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require MemSplit.
Module V17StartupFacts.
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
Import OSSVerify.leptonica.kernel_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.CliDriver.Amb.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.StartupTac.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.ArgvEnv.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.RefLayout.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.RefMemcpyLib.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.MemSplit.
Import V17StartupDefs.
Import V17Startup.
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
  [(0x30cd0%Z, 8%nat); (0x51030%Z, 8%nat); (0x51090%Z, 8%nat); (0x51058%Z, 8%nat); (0x51020%Z, 8%nat); (0x51018%Z, 8%nat); (0x50dc8%Z, 8%nat); (0x50dd8%Z, 8%nat); (0x50dd0%Z, 8%nat); (0x51040%Z, 8%nat); (0x51048%Z, 8%nat); (0x30db0%Z, 8%nat); (0x30d98%Z, 8%nat); (0x30cd8%Z, 8%nat); (0x51028%Z, 1%nat); (0x30d00%Z, 4%nat); (0x30cf8%Z, 4%nat); (0x30d70%Z, 8%nat); (0x30d50%Z, 8%nat); (0x30ce0%Z, 8%nat); (0x30ce8%Z, 8%nat); (0x30cf0%Z, 8%nat); (0x51008%Z, 4%nat); (0x5100c%Z, 4%nat); (0x51009%Z, 1%nat); (0x30d90%Z, 8%nat); (0x20c50%Z, 1%nat)].

Definition range_disjoint_b (a : Z) (n : nat) (c : Z * nat) : bool :=
  ((a + Z.of_nat n <=? fst c) || (fst c + Z.of_nat (snd c) <=? a))%Z.

Definition D_main_missb (a : Z) (n : nat) : bool :=
  forallb (range_disjoint_b a n) D_main_cells && (0 <=? a)%Z && (a + Z.of_nat n <=? 0x52000)%Z.

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
    rdn segs D (Z_to_bv 64 0x30cf8) 4 = Some (word_to_le_bytes 4 tid).
  Proof.
    intros segs. pose proof (u64_range tid). subst D.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    pose proof (rdn_wbytes_hit segs (word_to_le_bytes 4 tid)) as Hh.
    rewrite length_N_to_le_bytes in Hh. apply Hh. unorm; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma D_main_guard : forall segs,
    rdn segs D (Z_to_bv 64 0x51008) 8 = Some (guard_bytes a_draw).
  Proof.
    intros segs. pose proof (u64_range tid). subst D.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel. apply rdn_guard.
  Qed.

  (* [comment removed for export] *)
  Lemma D_main_guard_at : forall i, (0 <= i < 8)%Z ->
    D (Z_to_bv 64 (0x51008 + i)) = Some (nth (Z.to_nat i) (guard_bytes a_draw) (Z_to_bv 8 0)).
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
    rdn segs D (Z_to_bv 64 0x51008) 8 = Some (word_to_le_bytes 8 (canary_w a_draw)).
  Proof. intros segs. rewrite <- guard_bytes_w. apply D_main_guard. Qed.

  (* [comment removed for export] *)
  Lemma D_main_pagesize : forall segs,
    rdn segs D (Z_to_bv 64 0x51058) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 4096)).
  Proof.
    intros segs. pose proof (u64_range tid). pose proof len_av. subst D.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    apply rdn_wbytes_hit8. unorm; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma D_main_environ : forall segs,
    rdn segs D (Z_to_bv 64 0x30cd0) 8 = Some (word_to_le_bytes 8 (envp_w sp0 av)).
  Proof.
    intros segs. pose proof (u64_range tid). pose proof len_av. subst D.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    apply rdn_wbytes_hit8. unorm; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma D_main_self : forall segs,
    rdn segs D (Z_to_bv 64 0x30cd8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x30cd8)).
  Proof.
    intros segs. pose proof (u64_range tid). subst D.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    apply rdn_wbytes_hit8. unorm; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma D_main_canary : forall segs,
    rdn segs D (Z_to_bv 64 0x30d90) 8 = Some (word_to_le_bytes 8 (canary_w a_draw)).
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
    assert (Hr : (0 <= a /\ a + Z.of_nat n <= 0x52000)%Z).
    { unfold D_main_missb in Hb. apply andb_true_iff in Hb as [Hb H2]. apply andb_true_iff in Hb as [_ H1].
      apply Z.leb_le in H1. apply Z.leb_le in H2. lia. }
    rewrite (main_entry_rdn_data sp0 av ev tid regs mem ME)
      by (rewrite stack_max_size_val; unorm; lia).
    apply D_main_miss. exact Hb.
  Qed.

  Lemma main_entry_tid : forall segs,
    rdn segs mem (Z_to_bv 64 0x30cf8) 4 = Some (word_to_le_bytes 4 tid).
  Proof.
    intros segs. rewrite (main_entry_rdn_data sp0 av ev tid regs mem ME)
      by (rewrite stack_max_size_val; unorm; lia). apply D_main_tid.
  Qed.

  Lemma main_entry_guard : forall segs,
    rdn segs mem (Z_to_bv 64 0x51008) 8 = Some (guard_bytes a_draw).
  Proof.
    intros segs. rewrite (main_entry_rdn_data sp0 av ev tid regs mem ME)
      by (rewrite stack_max_size_val; unorm; lia). apply D_main_guard.
  Qed.

  Lemma main_entry_guard_w : forall segs,
    rdn segs mem (Z_to_bv 64 0x51008) 8 = Some (word_to_le_bytes 8 (canary_w a_draw)).
  Proof. intros segs. rewrite <- guard_bytes_w. apply main_entry_guard. Qed.
End Facts.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End V17StartupFacts.

From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng Require AllocSure.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng Require MallocSure.
Module V17Sure.
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
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.PureModel.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.VmLedger.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.AllocIface.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.MallocLayout.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.MallocTree.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.MallocOps.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.MallocIface.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.MallocInv_defs.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.MallocIfaceX.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.AllocBase.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.AllocSure.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.MallocAllocLayout.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.MallocGlue.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.MallocSure.
Import V17MallocLayout.
Import V17Ref_malloc.
Import V17Ref_free.
Import V17Ref_calloc.
Import V17Alloc.
(* [comment removed for export] *)





Import ListNotations.
Local Open Scope Z_scope.

Definition u17_sure : AllocSure (AL:=mallocng_alloc_layout (ML:=LU17)) (CL:=mallocng_calloc_layout (ML:=LU17)) :=
  mallocng_sure (ML:=LU17) u17_malloc_okX u17_free_okX u17_calloc_okX
    (fun fx => malloc_refines (fx:=fx)) (fun fx => free_refines (fx:=fx)) (fun fx => calloc_refines (fx:=fx)).

Lemma u17_sure_calloc : asr_calloc (AllocSure:=u17_sure) = u17_calloc.
Proof. reflexivity. Qed.

Lemma u17_sure_base : aic_base (AllocCalloc:=asr_calloc (AllocSure:=u17_sure)) = u17_base.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma u17_sure_room : forall A h k b,
  aroom (AllocSure:=u17_sure) A h k b <-> g_room A h k b.
Proof. intros. reflexivity. Qed.
End V17Sure.

From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng Require AllocCredit.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng Require MallocCredit.
Module V17Credit.
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
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.PropExec.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.CatExec.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.CatSim.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Hoare.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.PureModel.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.VmLedger.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.AllocIface.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.MallocLayout.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.MallocTree.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.MallocOps.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.MallocIface.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.MallocInv_defs.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.MallocIfaceX.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.AllocBase.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.AllocSure.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.AllocCredit.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.MallocAllocLayout.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.MallocGlue.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.MallocSure.
Import OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng.MallocCredit.
Import V17MallocLayout.
Import V17Ref_malloc.
Import V17Ref_free.
Import V17Ref_calloc.
Import V17Alloc.
Import V17Sure.
(* [comment removed for export] *)





Import ListNotations.
Local Open Scope Z_scope.

Definition u17_credit : AllocCredit (AL:=mallocng_alloc_layout (ML:=LU17)) (CL:=mallocng_calloc_layout (ML:=LU17)) :=
  mallocng_credit (ML:=LU17) u17_malloc_okX u17_free_okX u17_calloc_okX
    (fun fx => malloc_refines (fx:=fx)) (fun fx => free_refines (fx:=fx)) (fun fx => calloc_refines (fx:=fx)).

Lemma u17_credit_sure : acr_sure (AllocCredit:=u17_credit) = u17_sure.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma u17_credit_room : forall A h k p,
  aroomP (AllocCredit:=u17_credit) A h k p <-> g_roomP A h k p.
Proof. intros. reflexivity. Qed.
End V17Credit.
