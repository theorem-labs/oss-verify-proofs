(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanHexScan__Common.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanHexZero.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Img.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require AsanShadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Syms__A3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module A3RW.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanHexScan__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AsanHexZero. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexScan__Common.AsanHexScan OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AsanHexZero.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require Import A3Img.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition RW_LO : Z := 0xa4000.

Lemma seg2_scan : scanN Asan_seg_bytes_002 64 0 0x3000 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma seg3_scan : scanN Asan_seg_bytes_003 64 0 0x55c000 = true.
Proof. (* [comment removed for export] *)
  apply (scanN_prefix_zwin Asan_seg_bytes_003 16384 0x55c000 (Uint63.of_Z 32768) (Uint63.of_Z 11206656)).
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
  - reflexivity.
  - reflexivity.
  - vm_compute. discriminate.
  - vm_compute. discriminate.
Qed.
Lemma seg2_len : (0x3000 <= Z.to_N (Uint63.to_Z (PrimString.length Asan_seg_bytes_002) / 2))%N.
Proof. vm_compute. discriminate. Qed.
Lemma seg3_len : (0x55c000 <= Z.to_N (Uint63.to_Z (PrimString.length Asan_seg_bytes_003) / 2))%N.
Proof. vm_compute. discriminate. Qed.

Lemma seg2_w : seg_writable Asan_segment_002 = true. Proof. reflexivity. Qed.
Lemma seg3_w : seg_writable Asan_segment_003 = true. Proof. reflexivity. Qed.

Lemma rw_window_img : forall m (x : word), RW_LO <= bv_unsigned x < IMG_HI -> wview SEGS m x <> None.
Proof.
  intros m x Hx. unfold RW_LO, IMG_HI in Hx. unfold wview. destruct (m x) as [b|]; [discriminate|].
  unfold SEGS, IMGM.loaded_segments, Asan_loaded_segments.
  cbn [find_segment seg_base seg_size Asan_segment_000 Asan_segment_001].
  replace ((Z.of_N 65536 <=? bv_unsigned x) && (bv_unsigned x + 1 <=? Z.of_N 65536 + Z.of_N 139264))%bool with false
    by (symmetry; apply andb_false_iff; right; apply Z.leb_gt; lia).
  replace ((Z.of_N 204800 <=? bv_unsigned x) && (bv_unsigned x + 1 <=? Z.of_N 204800 + Z.of_N 466944))%bool with false
    by (symmetry; apply andb_false_iff; right; apply Z.leb_gt; lia).
  destruct (Z.lt_ge_cases (bv_unsigned x) 0xa7000) as [Hlo|Hhi].
  - cbn [find_segment seg_base seg_size Asan_segment_002].
    replace ((Z.of_N 671744 <=? bv_unsigned x) && (bv_unsigned x + 1 <=? Z.of_N 671744 + Z.of_N 12288))%bool with true
      by (symmetry; apply andb_true_intro; split; apply Z.leb_le; lia).
    rewrite seg2_w. cbn [seg_bytes seg_base].
    apply (segment_byte_at_some1 _ 0x3000%N); [exact seg2_scan | exact seg2_len | cbn [seg_base Asan_segment_002]; rewrite Z2N.id by lia; lia].
  - cbn [find_segment seg_base seg_size Asan_segment_002].
    replace ((Z.of_N 671744 <=? bv_unsigned x) && (bv_unsigned x + 1 <=? Z.of_N 671744 + Z.of_N 12288))%bool with false
      by (symmetry; apply andb_false_iff; right; apply Z.leb_gt; lia).
    cbn [find_segment seg_base seg_size Asan_segment_003].
    replace ((Z.of_N 684032 <=? bv_unsigned x) && (bv_unsigned x + 1 <=? Z.of_N 684032 + Z.of_N 5619712))%bool with true
      by (symmetry; apply andb_true_intro; split; apply Z.leb_le; lia).
    rewrite seg3_w. cbn [seg_bytes seg_base].
    apply (segment_byte_at_some1 _ 0x55c000%N); [exact seg3_scan | exact seg3_len | cbn [seg_base Asan_segment_003]; rewrite Z2N.id by lia; lia].
Qed.
End A3RW.

(* [comment removed for export] *)
Module MuslMemcpy_code.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require Import A3Img.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_9dd58 : bv 32 := 0x0035f693.
Lemma F_9dd58 : fetch_word SEGS (0x9e6a0 : word) = Some W_9dd58.
Proof. vm_refl. Qed.
Lemma D_9dd58 : decode_any W_9dd58 = Some (OpImm ALU_AND 13 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dd5c : bv 32 := 0x10068863.
Lemma F_9dd5c : fetch_word SEGS (0x9e6a4 : word) = Some W_9dd5c.
Proof. vm_refl. Qed.
Lemma D_9dd5c : decode_any W_9dd5c = Some (Branch BC_EQ 13 0 272, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dd60 : bv 32 := 0x02060e63.
Lemma F_9dd60 : fetch_word SEGS (0x9e6a8 : word) = Some W_9dd60.
Proof. vm_refl. Qed.
Lemma D_9dd60 : decode_any W_9dd60 = Some (Branch BC_EQ 12 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dd64 : bv 32 := 0x00158713.
Lemma F_9dd64 : fetch_word SEGS (0x9e6ac : word) = Some W_9dd64.
Proof. vm_refl. Qed.
Lemma D_9dd64 : decode_any W_9dd64 = Some (OpImm ALU_ADD 14 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dd68 : bv 32 := 0x00100793.
Lemma F_9dd68 : fetch_word SEGS (0x9e6b0 : word) = Some W_9dd68.
Proof. vm_refl. Qed.
Lemma D_9dd68 : decode_any W_9dd68 = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dd6c : bv 32 := 0x00050693.
Lemma F_9dd6c : fetch_word SEGS (0x9e6b4 : word) = Some W_9dd6c.
Proof. vm_refl. Qed.
Lemma D_9dd6c : decode_any W_9dd6c = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dd70 : bv 32 := 0x0005c883.
Lemma F_9dd70 : fetch_word SEGS (0x9e6b8 : word) = Some W_9dd70.
Proof. vm_refl. Qed.
Lemma D_9dd70 : decode_any W_9dd70 = Some (Load SZ1 false 17 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dd74 : bv 32 := 0x00060813.
Lemma F_9dd74 : fetch_word SEGS (0x9e6bc : word) = Some W_9dd74.
Proof. vm_refl. Qed.
Lemma D_9dd74 : decode_any W_9dd74 = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dd78 : bv 32 := 0x00158593.
Lemma F_9dd78 : fetch_word SEGS (0x9e6c0 : word) = Some W_9dd78.
Proof. vm_refl. Qed.
Lemma D_9dd78 : decode_any W_9dd78 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dd7c : bv 32 := 0x00377293.
Lemma F_9dd7c : fetch_word SEGS (0x9e6c4 : word) = Some W_9dd7c.
Proof. vm_refl. Qed.
Lemma D_9dd7c : decode_any W_9dd7c = Some (OpImm ALU_AND 5 14 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dd80 : bv 32 := 0x01168023.
Lemma F_9dd80 : fetch_word SEGS (0x9e6c8 : word) = Some W_9dd80.
Proof. vm_refl. Qed.
Lemma D_9dd80 : decode_any W_9dd80 = Some (Store SZ1 13 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dd84 : bv 32 := 0x00168693.
Lemma F_9dd84 : fetch_word SEGS (0x9e6cc : word) = Some W_9dd84.
Proof. vm_refl. Qed.
Lemma D_9dd84 : decode_any W_9dd84 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dd88 : bv 32 := 0xfff60613.
Lemma F_9dd88 : fetch_word SEGS (0x9e6d0 : word) = Some W_9dd88.
Proof. vm_refl. Qed.
Lemma D_9dd88 : decode_any W_9dd88 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dd8c : bv 32 := 0x00028a63.
Lemma F_9dd8c : fetch_word SEGS (0x9e6d4 : word) = Some W_9dd8c.
Proof. vm_refl. Qed.
Lemma D_9dd8c : decode_any W_9dd8c = Some (Branch BC_EQ 5 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dd90 : bv 32 := 0x00170713.
Lemma F_9dd90 : fetch_word SEGS (0x9e6d8 : word) = Some W_9dd90.
Proof. vm_refl. Qed.
Lemma D_9dd90 : decode_any W_9dd90 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dd94 : bv 32 := 0xfcf81ee3.
Lemma F_9dd94 : fetch_word SEGS (0x9e6dc : word) = Some W_9dd94.
Proof. vm_refl. Qed.
Lemma D_9dd94 : decode_any W_9dd94 = Some (Branch BC_NE 16 15 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dd98 : bv 32 := 0x0080006f.
Lemma F_9dd98 : fetch_word SEGS (0x9e6e0 : word) = Some W_9dd98.
Proof. vm_refl. Qed.
Lemma D_9dd98 : decode_any W_9dd98 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dd9c : bv 32 := 0x00050693.
Lemma F_9dd9c : fetch_word SEGS (0x9e6e4 : word) = Some W_9dd9c.
Proof. vm_refl. Qed.
Lemma D_9dd9c : decode_any W_9dd9c = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dda0 : bv 32 := 0x0036f793.
Lemma F_9dda0 : fetch_word SEGS (0x9e6e8 : word) = Some W_9dda0.
Proof. vm_refl. Qed.
Lemma D_9dda0 : decode_any W_9dda0 = Some (OpImm ALU_AND 15 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dda4 : bv 32 := 0x0c078a63.
Lemma F_9dda4 : fetch_word SEGS (0x9e6ec : word) = Some W_9dda4.
Proof. vm_refl. Qed.
Lemma D_9dda4 : decode_any W_9dda4 = Some (Branch BC_EQ 15 0 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dda8 : bv 32 := 0x02000713.
Lemma F_9dda8 : fetch_word SEGS (0x9e6f0 : word) = Some W_9dda8.
Proof. vm_refl. Qed.
Lemma D_9dda8 : decode_any W_9dda8 = Some (OpImm ALU_ADD 14 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ddac : bv 32 := 0x02e67063.
Lemma F_9ddac : fetch_word SEGS (0x9e6f4 : word) = Some W_9ddac.
Proof. vm_refl. Qed.
Lemma D_9ddac : decode_any W_9ddac = Some (Branch BC_GEU 12 14 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ddb0 : bv 32 := 0x01000713.
Lemma F_9ddb0 : fetch_word SEGS (0x9e6f8 : word) = Some W_9ddb0.
Proof. vm_refl. Qed.
Lemma D_9ddb0 : decode_any W_9ddb0 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ddb4 : bv 32 := 0x24e67863.
Lemma F_9ddb4 : fetch_word SEGS (0x9e6fc : word) = Some W_9ddb4.
Proof. vm_refl. Qed.
Lemma D_9ddb4 : decode_any W_9ddb4 = Some (Branch BC_GEU 12 14 592, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ddb8 : bv 32 := 0x00867713.
Lemma F_9ddb8 : fetch_word SEGS (0x9e700 : word) = Some W_9ddb8.
Proof. vm_refl. Qed.
Lemma D_9ddb8 : decode_any W_9ddb8 = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ddbc : bv 32 := 0x2c071e63.
Lemma F_9ddbc : fetch_word SEGS (0x9e704 : word) = Some W_9ddbc.
Proof. vm_refl. Qed.
Lemma D_9ddbc : decode_any W_9ddbc = Some (Branch BC_NE 14 0 732, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ddc0 : bv 32 := 0x00467713.
Lemma F_9ddc0 : fetch_word SEGS (0x9e708 : word) = Some W_9ddc0.
Proof. vm_refl. Qed.
Lemma D_9ddc0 : decode_any W_9ddc0 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ddc4 : bv 32 := 0x32071463.
Lemma F_9ddc4 : fetch_word SEGS (0x9e70c : word) = Some W_9ddc4.
Proof. vm_refl. Qed.
Lemma D_9ddc4 : decode_any W_9ddc4 = Some (Branch BC_NE 14 0 808, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ddc8 : bv 32 := 0x3500006f.
Lemma F_9ddc8 : fetch_word SEGS (0x9e710 : word) = Some W_9ddc8.
Proof. vm_refl. Qed.
Lemma D_9ddc8 : decode_any W_9ddc8 = Some (Jal 0 848, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ddcc : bv 32 := 0x0005a703.
Lemma F_9ddcc : fetch_word SEGS (0x9e714 : word) = Some W_9ddcc.
Proof. vm_refl. Qed.
Lemma D_9ddcc : decode_any W_9ddcc = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ddd0 : bv 32 := 0x00300813.
Lemma F_9ddd0 : fetch_word SEGS (0x9e718 : word) = Some W_9ddd0.
Proof. vm_refl. Qed.
Lemma D_9ddd0 : decode_any W_9ddd0 = Some (OpImm ALU_ADD 16 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ddd4 : bv 32 := 0x11078e63.
Lemma F_9ddd4 : fetch_word SEGS (0x9e71c : word) = Some W_9ddd4.
Proof. vm_refl. Qed.
Lemma D_9ddd4 : decode_any W_9ddd4 = Some (Branch BC_EQ 15 16 284, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ddd8 : bv 32 := 0x00200813.
Lemma F_9ddd8 : fetch_word SEGS (0x9e720 : word) = Some W_9ddd8.
Proof. vm_refl. Qed.
Lemma D_9ddd8 : decode_any W_9ddd8 = Some (OpImm ALU_ADD 16 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dddc : bv 32 := 0x19079c63.
Lemma F_9dddc : fetch_word SEGS (0x9e724 : word) = Some W_9dddc.
Proof. vm_refl. Qed.
Lemma D_9dddc : decode_any W_9dddc = Some (Branch BC_NE 15 16 408, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dde0 : bv 32 := 0x00875793.
Lemma F_9dde0 : fetch_word SEGS (0x9e728 : word) = Some W_9dde0.
Proof. vm_refl. Qed.
Lemma D_9dde0 : decode_any W_9dde0 = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dde4 : bv 32 := 0xffe60613.
Lemma F_9dde4 : fetch_word SEGS (0x9e72c : word) = Some W_9dde4.
Proof. vm_refl. Qed.
Lemma D_9dde4 : decode_any W_9dde4 = Some (OpImm ALU_ADD 12 12 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dde8 : bv 32 := 0x00e68023.
Lemma F_9dde8 : fetch_word SEGS (0x9e730 : word) = Some W_9dde8.
Proof. vm_refl. Qed.
Lemma D_9dde8 : decode_any W_9dde8 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ddec : bv 32 := 0x00f680a3.
Lemma F_9ddec : fetch_word SEGS (0x9e734 : word) = Some W_9ddec.
Proof. vm_refl. Qed.
Lemma D_9ddec : decode_any W_9ddec = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ddf0 : bv 32 := 0x00268693.
Lemma F_9ddf0 : fetch_word SEGS (0x9e738 : word) = Some W_9ddf0.
Proof. vm_refl. Qed.
Lemma D_9ddf0 : decode_any W_9ddf0 = Some (OpImm ALU_ADD 13 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ddf4 : bv 32 := 0x01058593.
Lemma F_9ddf4 : fetch_word SEGS (0x9e73c : word) = Some W_9ddf4.
Proof. vm_refl. Qed.
Lemma D_9ddf4 : decode_any W_9ddf4 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ddf8 : bv 32 := 0x01100793.
Lemma F_9ddf8 : fetch_word SEGS (0x9e740 : word) = Some W_9ddf8.
Proof. vm_refl. Qed.
Lemma D_9ddf8 : decode_any W_9ddf8 = Some (OpImm ALU_ADD 15 0 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ddfc : bv 32 := 0x0107581b.
Lemma F_9ddfc : fetch_word SEGS (0x9e744 : word) = Some W_9ddfc.
Proof. vm_refl. Qed.
Lemma D_9ddfc : decode_any W_9ddfc = Some (ShiftImm32 ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9de00 : bv 32 := 0xff45a883.
Lemma F_9de00 : fetch_word SEGS (0x9e748 : word) = Some W_9de00.
Proof. vm_refl. Qed.
Lemma D_9de00 : decode_any W_9de00 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9de04 : bv 32 := 0xff85a283.
Lemma F_9de04 : fetch_word SEGS (0x9e74c : word) = Some W_9de04.
Proof. vm_refl. Qed.
Lemma D_9de04 : decode_any W_9de04 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9de08 : bv 32 := 0xffc5a303.
Lemma F_9de08 : fetch_word SEGS (0x9e750 : word) = Some W_9de08.
Proof. vm_refl. Qed.
Lemma D_9de08 : decode_any W_9de08 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9de0c : bv 32 := 0x0005a703.
Lemma F_9de0c : fetch_word SEGS (0x9e754 : word) = Some W_9de0c.
Proof. vm_refl. Qed.
Lemma D_9de0c : decode_any W_9de0c = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9de10 : bv 32 := 0x01089393.
Lemma F_9de10 : fetch_word SEGS (0x9e758 : word) = Some W_9de10.
Proof. vm_refl. Qed.
Lemma D_9de10 : decode_any W_9de10 = Some (ShiftImm ALU_SLL 7 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9de14 : bv 32 := 0x0108d89b.
Lemma F_9de14 : fetch_word SEGS (0x9e75c : word) = Some W_9de14.
Proof. vm_refl. Qed.
Lemma D_9de14 : decode_any W_9de14 = Some (ShiftImm32 ALU_SRL 17 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9de18 : bv 32 := 0x0103e833.
Lemma F_9de18 : fetch_word SEGS (0x9e760 : word) = Some W_9de18.
Proof. vm_refl. Qed.
Lemma D_9de18 : decode_any W_9de18 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9de1c : bv 32 := 0x01029393.
Lemma F_9de1c : fetch_word SEGS (0x9e764 : word) = Some W_9de1c.
Proof. vm_refl. Qed.
Lemma D_9de1c : decode_any W_9de1c = Some (ShiftImm ALU_SLL 7 5 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9de20 : bv 32 := 0x0102d29b.
Lemma F_9de20 : fetch_word SEGS (0x9e768 : word) = Some W_9de20.
Proof. vm_refl. Qed.
Lemma D_9de20 : decode_any W_9de20 = Some (ShiftImm32 ALU_SRL 5 5 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9de24 : bv 32 := 0x0113e8b3.
Lemma F_9de24 : fetch_word SEGS (0x9e76c : word) = Some W_9de24.
Proof. vm_refl. Qed.
Lemma D_9de24 : decode_any W_9de24 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9de28 : bv 32 := 0x01031393.
Lemma F_9de28 : fetch_word SEGS (0x9e770 : word) = Some W_9de28.
Proof. vm_refl. Qed.
Lemma D_9de28 : decode_any W_9de28 = Some (ShiftImm ALU_SLL 7 6 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9de2c : bv 32 := 0x0103531b.
Lemma F_9de2c : fetch_word SEGS (0x9e774 : word) = Some W_9de2c.
Proof. vm_refl. Qed.
Lemma D_9de2c : decode_any W_9de2c = Some (ShiftImm32 ALU_SRL 6 6 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9de30 : bv 32 := 0x0053e2b3.
Lemma F_9de30 : fetch_word SEGS (0x9e778 : word) = Some W_9de30.
Proof. vm_refl. Qed.
Lemma D_9de30 : decode_any W_9de30 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9de34 : bv 32 := 0x01071393.
Lemma F_9de34 : fetch_word SEGS (0x9e77c : word) = Some W_9de34.
Proof. vm_refl. Qed.
Lemma D_9de34 : decode_any W_9de34 = Some (ShiftImm ALU_SLL 7 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9de38 : bv 32 := 0x0063e333.
Lemma F_9de38 : fetch_word SEGS (0x9e780 : word) = Some W_9de38.
Proof. vm_refl. Qed.
Lemma D_9de38 : decode_any W_9de38 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9de3c : bv 32 := 0xff060613.
Lemma F_9de3c : fetch_word SEGS (0x9e784 : word) = Some W_9de3c.
Proof. vm_refl. Qed.
Lemma D_9de3c : decode_any W_9de3c = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9de40 : bv 32 := 0x0106a023.
Lemma F_9de40 : fetch_word SEGS (0x9e788 : word) = Some W_9de40.
Proof. vm_refl. Qed.
Lemma D_9de40 : decode_any W_9de40 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9de44 : bv 32 := 0x0116a223.
Lemma F_9de44 : fetch_word SEGS (0x9e78c : word) = Some W_9de44.
Proof. vm_refl. Qed.
Lemma D_9de44 : decode_any W_9de44 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9de48 : bv 32 := 0x0056a423.
Lemma F_9de48 : fetch_word SEGS (0x9e790 : word) = Some W_9de48.
Proof. vm_refl. Qed.
Lemma D_9de48 : decode_any W_9de48 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9de4c : bv 32 := 0x0066a623.
Lemma F_9de4c : fetch_word SEGS (0x9e794 : word) = Some W_9de4c.
Proof. vm_refl. Qed.
Lemma D_9de4c : decode_any W_9de4c = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9de50 : bv 32 := 0x01068693.
Lemma F_9de50 : fetch_word SEGS (0x9e798 : word) = Some W_9de50.
Proof. vm_refl. Qed.
Lemma D_9de50 : decode_any W_9de50 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9de54 : bv 32 := 0x01058593.
Lemma F_9de54 : fetch_word SEGS (0x9e79c : word) = Some W_9de54.
Proof. vm_refl. Qed.
Lemma D_9de54 : decode_any W_9de54 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9de58 : bv 32 := 0xfac7e2e3.
Lemma F_9de58 : fetch_word SEGS (0x9e7a0 : word) = Some W_9de58.
Proof. vm_refl. Qed.
Lemma D_9de58 : decode_any W_9de58 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9de5c : bv 32 := 0xff258593.
Lemma F_9de5c : fetch_word SEGS (0x9e7a4 : word) = Some W_9de5c.
Proof. vm_refl. Qed.
Lemma D_9de5c : decode_any W_9de5c = Some (OpImm ALU_ADD 11 11 4082, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9de60 : bv 32 := 0x01000713.
Lemma F_9de60 : fetch_word SEGS (0x9e7a8 : word) = Some W_9de60.
Proof. vm_refl. Qed.
Lemma D_9de60 : decode_any W_9de60 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9de64 : bv 32 := 0xf4e66ae3.
Lemma F_9de64 : fetch_word SEGS (0x9e7ac : word) = Some W_9de64.
Proof. vm_refl. Qed.
Lemma D_9de64 : decode_any W_9de64 = Some (Branch BC_LTU 12 14 8020, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9de68 : bv 32 := 0x19c0006f.
Lemma F_9de68 : fetch_word SEGS (0x9e7b0 : word) = Some W_9de68.
Proof. vm_refl. Qed.
Lemma D_9de68 : decode_any W_9de68 = Some (Jal 0 412, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9de6c : bv 32 := 0x00050693.
Lemma F_9de6c : fetch_word SEGS (0x9e7b4 : word) = Some W_9de6c.
Proof. vm_refl. Qed.
Lemma D_9de6c : decode_any W_9de6c = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9de70 : bv 32 := 0x00357793.
Lemma F_9de70 : fetch_word SEGS (0x9e7b8 : word) = Some W_9de70.
Proof. vm_refl. Qed.
Lemma D_9de70 : decode_any W_9de70 = Some (OpImm ALU_AND 15 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9de74 : bv 32 := 0xf2079ae3.
Lemma F_9de74 : fetch_word SEGS (0x9e7bc : word) = Some W_9de74.
Proof. vm_refl. Qed.
Lemma D_9de74 : decode_any W_9de74 = Some (Branch BC_NE 15 0 7988, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9de78 : bv 32 := 0x01000713.
Lemma F_9de78 : fetch_word SEGS (0x9e7c0 : word) = Some W_9de78.
Proof. vm_refl. Qed.
Lemma D_9de78 : decode_any W_9de78 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9de7c : bv 32 := 0x02e66c63.
Lemma F_9de7c : fetch_word SEGS (0x9e7c4 : word) = Some W_9de7c.
Proof. vm_refl. Qed.
Lemma D_9de7c : decode_any W_9de7c = Some (Branch BC_LTU 12 14 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9de80 : bv 32 := 0x00f00713.
Lemma F_9de80 : fetch_word SEGS (0x9e7c8 : word) = Some W_9de80.
Proof. vm_refl. Qed.
Lemma D_9de80 : decode_any W_9de80 = Some (OpImm ALU_ADD 14 0 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9de84 : bv 32 := 0x0005a783.
Lemma F_9de84 : fetch_word SEGS (0x9e7cc : word) = Some W_9de84.
Proof. vm_refl. Qed.
Lemma D_9de84 : decode_any W_9de84 = Some (Load SZ4 true 15 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9de88 : bv 32 := 0x0045a803.
Lemma F_9de88 : fetch_word SEGS (0x9e7d0 : word) = Some W_9de88.
Proof. vm_refl. Qed.
Lemma D_9de88 : decode_any W_9de88 = Some (Load SZ4 true 16 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9de8c : bv 32 := 0x0085a883.
Lemma F_9de8c : fetch_word SEGS (0x9e7d4 : word) = Some W_9de8c.
Proof. vm_refl. Qed.
Lemma D_9de8c : decode_any W_9de8c = Some (Load SZ4 true 17 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9de90 : bv 32 := 0x00c5a283.
Lemma F_9de90 : fetch_word SEGS (0x9e7d8 : word) = Some W_9de90.
Proof. vm_refl. Qed.
Lemma D_9de90 : decode_any W_9de90 = Some (Load SZ4 true 5 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9de94 : bv 32 := 0x01058593.
Lemma F_9de94 : fetch_word SEGS (0x9e7dc : word) = Some W_9de94.
Proof. vm_refl. Qed.
Lemma D_9de94 : decode_any W_9de94 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9de98 : bv 32 := 0xff060613.
Lemma F_9de98 : fetch_word SEGS (0x9e7e0 : word) = Some W_9de98.
Proof. vm_refl. Qed.
Lemma D_9de98 : decode_any W_9de98 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9de9c : bv 32 := 0x00f6a023.
Lemma F_9de9c : fetch_word SEGS (0x9e7e4 : word) = Some W_9de9c.
Proof. vm_refl. Qed.
Lemma D_9de9c : decode_any W_9de9c = Some (Store SZ4 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dea0 : bv 32 := 0x0106a223.
Lemma F_9dea0 : fetch_word SEGS (0x9e7e8 : word) = Some W_9dea0.
Proof. vm_refl. Qed.
Lemma D_9dea0 : decode_any W_9dea0 = Some (Store SZ4 13 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dea4 : bv 32 := 0x0116a423.
Lemma F_9dea4 : fetch_word SEGS (0x9e7ec : word) = Some W_9dea4.
Proof. vm_refl. Qed.
Lemma D_9dea4 : decode_any W_9dea4 = Some (Store SZ4 13 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dea8 : bv 32 := 0x0056a623.
Lemma F_9dea8 : fetch_word SEGS (0x9e7f0 : word) = Some W_9dea8.
Proof. vm_refl. Qed.
Lemma D_9dea8 : decode_any W_9dea8 = Some (Store SZ4 13 5 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9deac : bv 32 := 0x01068693.
Lemma F_9deac : fetch_word SEGS (0x9e7f4 : word) = Some W_9deac.
Proof. vm_refl. Qed.
Lemma D_9deac : decode_any W_9deac = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9deb0 : bv 32 := 0xfcc76ae3.
Lemma F_9deb0 : fetch_word SEGS (0x9e7f8 : word) = Some W_9deb0.
Proof. vm_refl. Qed.
Lemma D_9deb0 : decode_any W_9deb0 = Some (Branch BC_LTU 14 12 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9deb4 : bv 32 := 0x00800713.
Lemma F_9deb4 : fetch_word SEGS (0x9e7fc : word) = Some W_9deb4.
Proof. vm_refl. Qed.
Lemma D_9deb4 : decode_any W_9deb4 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9deb8 : bv 32 := 0x00e66e63.
Lemma F_9deb8 : fetch_word SEGS (0x9e800 : word) = Some W_9deb8.
Proof. vm_refl. Qed.
Lemma D_9deb8 : decode_any W_9deb8 = Some (Branch BC_LTU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9debc : bv 32 := 0x0005a703.
Lemma F_9debc : fetch_word SEGS (0x9e804 : word) = Some W_9debc.
Proof. vm_refl. Qed.
Lemma D_9debc : decode_any W_9debc = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dec0 : bv 32 := 0x0045a783.
Lemma F_9dec0 : fetch_word SEGS (0x9e808 : word) = Some W_9dec0.
Proof. vm_refl. Qed.
Lemma D_9dec0 : decode_any W_9dec0 = Some (Load SZ4 true 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dec4 : bv 32 := 0x00e6a023.
Lemma F_9dec4 : fetch_word SEGS (0x9e80c : word) = Some W_9dec4.
Proof. vm_refl. Qed.
Lemma D_9dec4 : decode_any W_9dec4 = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dec8 : bv 32 := 0x00f6a223.
Lemma F_9dec8 : fetch_word SEGS (0x9e810 : word) = Some W_9dec8.
Proof. vm_refl. Qed.
Lemma D_9dec8 : decode_any W_9dec8 = Some (Store SZ4 13 15 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9decc : bv 32 := 0x00868693.
Lemma F_9decc : fetch_word SEGS (0x9e814 : word) = Some W_9decc.
Proof. vm_refl. Qed.
Lemma D_9decc : decode_any W_9decc = Some (OpImm ALU_ADD 13 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ded0 : bv 32 := 0x00858593.
Lemma F_9ded0 : fetch_word SEGS (0x9e818 : word) = Some W_9ded0.
Proof. vm_refl. Qed.
Lemma D_9ded0 : decode_any W_9ded0 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ded4 : bv 32 := 0x00467713.
Lemma F_9ded4 : fetch_word SEGS (0x9e81c : word) = Some W_9ded4.
Proof. vm_refl. Qed.
Lemma D_9ded4 : decode_any W_9ded4 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ded8 : bv 32 := 0x24070063.
Lemma F_9ded8 : fetch_word SEGS (0x9e820 : word) = Some W_9ded8.
Proof. vm_refl. Qed.
Lemma D_9ded8 : decode_any W_9ded8 = Some (Branch BC_EQ 14 0 576, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dedc : bv 32 := 0x0005a703.
Lemma F_9dedc : fetch_word SEGS (0x9e824 : word) = Some W_9dedc.
Proof. vm_refl. Qed.
Lemma D_9dedc : decode_any W_9dedc = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dee0 : bv 32 := 0x00458593.
Lemma F_9dee0 : fetch_word SEGS (0x9e828 : word) = Some W_9dee0.
Proof. vm_refl. Qed.
Lemma D_9dee0 : decode_any W_9dee0 = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dee4 : bv 32 := 0x00e6a023.
Lemma F_9dee4 : fetch_word SEGS (0x9e82c : word) = Some W_9dee4.
Proof. vm_refl. Qed.
Lemma D_9dee4 : decode_any W_9dee4 = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dee8 : bv 32 := 0x00468693.
Lemma F_9dee8 : fetch_word SEGS (0x9e830 : word) = Some W_9dee8.
Proof. vm_refl. Qed.
Lemma D_9dee8 : decode_any W_9dee8 = Some (OpImm ALU_ADD 13 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9deec : bv 32 := 0x22c0006f.
Lemma F_9deec : fetch_word SEGS (0x9e834 : word) = Some W_9deec.
Proof. vm_refl. Qed.
Lemma D_9deec : decode_any W_9deec = Some (Jal 0 556, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9def0 : bv 32 := 0x00e68023.
Lemma F_9def0 : fetch_word SEGS (0x9e838 : word) = Some W_9def0.
Proof. vm_refl. Qed.
Lemma D_9def0 : decode_any W_9def0 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9def4 : bv 32 := 0x00168693.
Lemma F_9def4 : fetch_word SEGS (0x9e83c : word) = Some W_9def4.
Proof. vm_refl. Qed.
Lemma D_9def4 : decode_any W_9def4 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9def8 : bv 32 := 0xfff60613.
Lemma F_9def8 : fetch_word SEGS (0x9e840 : word) = Some W_9def8.
Proof. vm_refl. Qed.
Lemma D_9def8 : decode_any W_9def8 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9defc : bv 32 := 0x01058593.
Lemma F_9defc : fetch_word SEGS (0x9e844 : word) = Some W_9defc.
Proof. vm_refl. Qed.
Lemma D_9defc : decode_any W_9defc = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df00 : bv 32 := 0x01200793.
Lemma F_9df00 : fetch_word SEGS (0x9e848 : word) = Some W_9df00.
Proof. vm_refl. Qed.
Lemma D_9df00 : decode_any W_9df00 = Some (OpImm ALU_ADD 15 0 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df04 : bv 32 := 0x0087581b.
Lemma F_9df04 : fetch_word SEGS (0x9e84c : word) = Some W_9df04.
Proof. vm_refl. Qed.
Lemma D_9df04 : decode_any W_9df04 = Some (ShiftImm32 ALU_SRL 16 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df08 : bv 32 := 0xff45a883.
Lemma F_9df08 : fetch_word SEGS (0x9e850 : word) = Some W_9df08.
Proof. vm_refl. Qed.
Lemma D_9df08 : decode_any W_9df08 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df0c : bv 32 := 0xff85a283.
Lemma F_9df0c : fetch_word SEGS (0x9e854 : word) = Some W_9df0c.
Proof. vm_refl. Qed.
Lemma D_9df0c : decode_any W_9df0c = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df10 : bv 32 := 0xffc5a303.
Lemma F_9df10 : fetch_word SEGS (0x9e858 : word) = Some W_9df10.
Proof. vm_refl. Qed.
Lemma D_9df10 : decode_any W_9df10 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df14 : bv 32 := 0x0005a703.
Lemma F_9df14 : fetch_word SEGS (0x9e85c : word) = Some W_9df14.
Proof. vm_refl. Qed.
Lemma D_9df14 : decode_any W_9df14 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df18 : bv 32 := 0x01889393.
Lemma F_9df18 : fetch_word SEGS (0x9e860 : word) = Some W_9df18.
Proof. vm_refl. Qed.
Lemma D_9df18 : decode_any W_9df18 = Some (ShiftImm ALU_SLL 7 17 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df1c : bv 32 := 0x0088d89b.
Lemma F_9df1c : fetch_word SEGS (0x9e864 : word) = Some W_9df1c.
Proof. vm_refl. Qed.
Lemma D_9df1c : decode_any W_9df1c = Some (ShiftImm32 ALU_SRL 17 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df20 : bv 32 := 0x0103e833.
Lemma F_9df20 : fetch_word SEGS (0x9e868 : word) = Some W_9df20.
Proof. vm_refl. Qed.
Lemma D_9df20 : decode_any W_9df20 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df24 : bv 32 := 0x01829393.
Lemma F_9df24 : fetch_word SEGS (0x9e86c : word) = Some W_9df24.
Proof. vm_refl. Qed.
Lemma D_9df24 : decode_any W_9df24 = Some (ShiftImm ALU_SLL 7 5 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df28 : bv 32 := 0x0082d29b.
Lemma F_9df28 : fetch_word SEGS (0x9e870 : word) = Some W_9df28.
Proof. vm_refl. Qed.
Lemma D_9df28 : decode_any W_9df28 = Some (ShiftImm32 ALU_SRL 5 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df2c : bv 32 := 0x0113e8b3.
Lemma F_9df2c : fetch_word SEGS (0x9e874 : word) = Some W_9df2c.
Proof. vm_refl. Qed.
Lemma D_9df2c : decode_any W_9df2c = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df30 : bv 32 := 0x01831393.
Lemma F_9df30 : fetch_word SEGS (0x9e878 : word) = Some W_9df30.
Proof. vm_refl. Qed.
Lemma D_9df30 : decode_any W_9df30 = Some (ShiftImm ALU_SLL 7 6 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df34 : bv 32 := 0x0083531b.
Lemma F_9df34 : fetch_word SEGS (0x9e87c : word) = Some W_9df34.
Proof. vm_refl. Qed.
Lemma D_9df34 : decode_any W_9df34 = Some (ShiftImm32 ALU_SRL 6 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df38 : bv 32 := 0x0053e2b3.
Lemma F_9df38 : fetch_word SEGS (0x9e880 : word) = Some W_9df38.
Proof. vm_refl. Qed.
Lemma D_9df38 : decode_any W_9df38 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df3c : bv 32 := 0x01871393.
Lemma F_9df3c : fetch_word SEGS (0x9e884 : word) = Some W_9df3c.
Proof. vm_refl. Qed.
Lemma D_9df3c : decode_any W_9df3c = Some (ShiftImm ALU_SLL 7 14 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df40 : bv 32 := 0x0063e333.
Lemma F_9df40 : fetch_word SEGS (0x9e888 : word) = Some W_9df40.
Proof. vm_refl. Qed.
Lemma D_9df40 : decode_any W_9df40 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df44 : bv 32 := 0xff060613.
Lemma F_9df44 : fetch_word SEGS (0x9e88c : word) = Some W_9df44.
Proof. vm_refl. Qed.
Lemma D_9df44 : decode_any W_9df44 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df48 : bv 32 := 0x0106a023.
Lemma F_9df48 : fetch_word SEGS (0x9e890 : word) = Some W_9df48.
Proof. vm_refl. Qed.
Lemma D_9df48 : decode_any W_9df48 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df4c : bv 32 := 0x0116a223.
Lemma F_9df4c : fetch_word SEGS (0x9e894 : word) = Some W_9df4c.
Proof. vm_refl. Qed.
Lemma D_9df4c : decode_any W_9df4c = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df50 : bv 32 := 0x0056a423.
Lemma F_9df50 : fetch_word SEGS (0x9e898 : word) = Some W_9df50.
Proof. vm_refl. Qed.
Lemma D_9df50 : decode_any W_9df50 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df54 : bv 32 := 0x0066a623.
Lemma F_9df54 : fetch_word SEGS (0x9e89c : word) = Some W_9df54.
Proof. vm_refl. Qed.
Lemma D_9df54 : decode_any W_9df54 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df58 : bv 32 := 0x01068693.
Lemma F_9df58 : fetch_word SEGS (0x9e8a0 : word) = Some W_9df58.
Proof. vm_refl. Qed.
Lemma D_9df58 : decode_any W_9df58 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df5c : bv 32 := 0x01058593.
Lemma F_9df5c : fetch_word SEGS (0x9e8a4 : word) = Some W_9df5c.
Proof. vm_refl. Qed.
Lemma D_9df5c : decode_any W_9df5c = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df60 : bv 32 := 0xfac7e2e3.
Lemma F_9df60 : fetch_word SEGS (0x9e8a8 : word) = Some W_9df60.
Proof. vm_refl. Qed.
Lemma D_9df60 : decode_any W_9df60 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df64 : bv 32 := 0xff158593.
Lemma F_9df64 : fetch_word SEGS (0x9e8ac : word) = Some W_9df64.
Proof. vm_refl. Qed.
Lemma D_9df64 : decode_any W_9df64 = Some (OpImm ALU_ADD 11 11 4081, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df68 : bv 32 := 0x01000713.
Lemma F_9df68 : fetch_word SEGS (0x9e8b0 : word) = Some W_9df68.
Proof. vm_refl. Qed.
Lemma D_9df68 : decode_any W_9df68 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df6c : bv 32 := 0xe4e666e3.
Lemma F_9df6c : fetch_word SEGS (0x9e8b4 : word) = Some W_9df6c.
Proof. vm_refl. Qed.
Lemma D_9df6c : decode_any W_9df6c = Some (Branch BC_LTU 12 14 7756, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df70 : bv 32 := 0x0940006f.
Lemma F_9df70 : fetch_word SEGS (0x9e8b8 : word) = Some W_9df70.
Proof. vm_refl. Qed.
Lemma D_9df70 : decode_any W_9df70 = Some (Jal 0 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df74 : bv 32 := 0x00875793.
Lemma F_9df74 : fetch_word SEGS (0x9e8bc : word) = Some W_9df74.
Proof. vm_refl. Qed.
Lemma D_9df74 : decode_any W_9df74 = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df78 : bv 32 := 0x01075813.
Lemma F_9df78 : fetch_word SEGS (0x9e8c0 : word) = Some W_9df78.
Proof. vm_refl. Qed.
Lemma D_9df78 : decode_any W_9df78 = Some (ShiftImm ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df7c : bv 32 := 0xffd60613.
Lemma F_9df7c : fetch_word SEGS (0x9e8c4 : word) = Some W_9df7c.
Proof. vm_refl. Qed.
Lemma D_9df7c : decode_any W_9df7c = Some (OpImm ALU_ADD 12 12 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df80 : bv 32 := 0x00e68023.
Lemma F_9df80 : fetch_word SEGS (0x9e8c8 : word) = Some W_9df80.
Proof. vm_refl. Qed.
Lemma D_9df80 : decode_any W_9df80 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df84 : bv 32 := 0x00f680a3.
Lemma F_9df84 : fetch_word SEGS (0x9e8cc : word) = Some W_9df84.
Proof. vm_refl. Qed.
Lemma D_9df84 : decode_any W_9df84 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df88 : bv 32 := 0x01068123.
Lemma F_9df88 : fetch_word SEGS (0x9e8d0 : word) = Some W_9df88.
Proof. vm_refl. Qed.
Lemma D_9df88 : decode_any W_9df88 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df8c : bv 32 := 0x00368693.
Lemma F_9df8c : fetch_word SEGS (0x9e8d4 : word) = Some W_9df8c.
Proof. vm_refl. Qed.
Lemma D_9df8c : decode_any W_9df8c = Some (OpImm ALU_ADD 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df90 : bv 32 := 0x01058593.
Lemma F_9df90 : fetch_word SEGS (0x9e8d8 : word) = Some W_9df90.
Proof. vm_refl. Qed.
Lemma D_9df90 : decode_any W_9df90 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df94 : bv 32 := 0x01000793.
Lemma F_9df94 : fetch_word SEGS (0x9e8dc : word) = Some W_9df94.
Proof. vm_refl. Qed.
Lemma D_9df94 : decode_any W_9df94 = Some (OpImm ALU_ADD 15 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df98 : bv 32 := 0x0187581b.
Lemma F_9df98 : fetch_word SEGS (0x9e8e0 : word) = Some W_9df98.
Proof. vm_refl. Qed.
Lemma D_9df98 : decode_any W_9df98 = Some (ShiftImm32 ALU_SRL 16 14 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df9c : bv 32 := 0xff45a883.
Lemma F_9df9c : fetch_word SEGS (0x9e8e4 : word) = Some W_9df9c.
Proof. vm_refl. Qed.
Lemma D_9df9c : decode_any W_9df9c = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dfa0 : bv 32 := 0xff85a283.
Lemma F_9dfa0 : fetch_word SEGS (0x9e8e8 : word) = Some W_9dfa0.
Proof. vm_refl. Qed.
Lemma D_9dfa0 : decode_any W_9dfa0 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dfa4 : bv 32 := 0xffc5a303.
Lemma F_9dfa4 : fetch_word SEGS (0x9e8ec : word) = Some W_9dfa4.
Proof. vm_refl. Qed.
Lemma D_9dfa4 : decode_any W_9dfa4 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dfa8 : bv 32 := 0x0005a703.
Lemma F_9dfa8 : fetch_word SEGS (0x9e8f0 : word) = Some W_9dfa8.
Proof. vm_refl. Qed.
Lemma D_9dfa8 : decode_any W_9dfa8 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dfac : bv 32 := 0x00889393.
Lemma F_9dfac : fetch_word SEGS (0x9e8f4 : word) = Some W_9dfac.
Proof. vm_refl. Qed.
Lemma D_9dfac : decode_any W_9dfac = Some (ShiftImm ALU_SLL 7 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dfb0 : bv 32 := 0x0188d89b.
Lemma F_9dfb0 : fetch_word SEGS (0x9e8f8 : word) = Some W_9dfb0.
Proof. vm_refl. Qed.
Lemma D_9dfb0 : decode_any W_9dfb0 = Some (ShiftImm32 ALU_SRL 17 17 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dfb4 : bv 32 := 0x0103e833.
Lemma F_9dfb4 : fetch_word SEGS (0x9e8fc : word) = Some W_9dfb4.
Proof. vm_refl. Qed.
Lemma D_9dfb4 : decode_any W_9dfb4 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dfb8 : bv 32 := 0x00829393.
Lemma F_9dfb8 : fetch_word SEGS (0x9e900 : word) = Some W_9dfb8.
Proof. vm_refl. Qed.
Lemma D_9dfb8 : decode_any W_9dfb8 = Some (ShiftImm ALU_SLL 7 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dfbc : bv 32 := 0x0182d29b.
Lemma F_9dfbc : fetch_word SEGS (0x9e904 : word) = Some W_9dfbc.
Proof. vm_refl. Qed.
Lemma D_9dfbc : decode_any W_9dfbc = Some (ShiftImm32 ALU_SRL 5 5 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dfc0 : bv 32 := 0x0113e8b3.
Lemma F_9dfc0 : fetch_word SEGS (0x9e908 : word) = Some W_9dfc0.
Proof. vm_refl. Qed.
Lemma D_9dfc0 : decode_any W_9dfc0 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dfc4 : bv 32 := 0x00831393.
Lemma F_9dfc4 : fetch_word SEGS (0x9e90c : word) = Some W_9dfc4.
Proof. vm_refl. Qed.
Lemma D_9dfc4 : decode_any W_9dfc4 = Some (ShiftImm ALU_SLL 7 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dfc8 : bv 32 := 0x0183531b.
Lemma F_9dfc8 : fetch_word SEGS (0x9e910 : word) = Some W_9dfc8.
Proof. vm_refl. Qed.
Lemma D_9dfc8 : decode_any W_9dfc8 = Some (ShiftImm32 ALU_SRL 6 6 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dfcc : bv 32 := 0x0053e2b3.
Lemma F_9dfcc : fetch_word SEGS (0x9e914 : word) = Some W_9dfcc.
Proof. vm_refl. Qed.
Lemma D_9dfcc : decode_any W_9dfcc = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dfd0 : bv 32 := 0x00871393.
Lemma F_9dfd0 : fetch_word SEGS (0x9e918 : word) = Some W_9dfd0.
Proof. vm_refl. Qed.
Lemma D_9dfd0 : decode_any W_9dfd0 = Some (ShiftImm ALU_SLL 7 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dfd4 : bv 32 := 0x0063e333.
Lemma F_9dfd4 : fetch_word SEGS (0x9e91c : word) = Some W_9dfd4.
Proof. vm_refl. Qed.
Lemma D_9dfd4 : decode_any W_9dfd4 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dfd8 : bv 32 := 0xff060613.
Lemma F_9dfd8 : fetch_word SEGS (0x9e920 : word) = Some W_9dfd8.
Proof. vm_refl. Qed.
Lemma D_9dfd8 : decode_any W_9dfd8 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dfdc : bv 32 := 0x0106a023.
Lemma F_9dfdc : fetch_word SEGS (0x9e924 : word) = Some W_9dfdc.
Proof. vm_refl. Qed.
Lemma D_9dfdc : decode_any W_9dfdc = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dfe0 : bv 32 := 0x0116a223.
Lemma F_9dfe0 : fetch_word SEGS (0x9e928 : word) = Some W_9dfe0.
Proof. vm_refl. Qed.
Lemma D_9dfe0 : decode_any W_9dfe0 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dfe4 : bv 32 := 0x0056a423.
Lemma F_9dfe4 : fetch_word SEGS (0x9e92c : word) = Some W_9dfe4.
Proof. vm_refl. Qed.
Lemma D_9dfe4 : decode_any W_9dfe4 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dfe8 : bv 32 := 0x0066a623.
Lemma F_9dfe8 : fetch_word SEGS (0x9e930 : word) = Some W_9dfe8.
Proof. vm_refl. Qed.
Lemma D_9dfe8 : decode_any W_9dfe8 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dfec : bv 32 := 0x01068693.
Lemma F_9dfec : fetch_word SEGS (0x9e934 : word) = Some W_9dfec.
Proof. vm_refl. Qed.
Lemma D_9dfec : decode_any W_9dfec = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dff0 : bv 32 := 0x01058593.
Lemma F_9dff0 : fetch_word SEGS (0x9e938 : word) = Some W_9dff0.
Proof. vm_refl. Qed.
Lemma D_9dff0 : decode_any W_9dff0 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dff4 : bv 32 := 0xfac7e2e3.
Lemma F_9dff4 : fetch_word SEGS (0x9e93c : word) = Some W_9dff4.
Proof. vm_refl. Qed.
Lemma D_9dff4 : decode_any W_9dff4 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dff8 : bv 32 := 0xff358593.
Lemma F_9dff8 : fetch_word SEGS (0x9e940 : word) = Some W_9dff8.
Proof. vm_refl. Qed.
Lemma D_9dff8 : decode_any W_9dff8 = Some (OpImm ALU_ADD 11 11 4083, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dffc : bv 32 := 0x01000713.
Lemma F_9dffc : fetch_word SEGS (0x9e944 : word) = Some W_9dffc.
Proof. vm_refl. Qed.
Lemma D_9dffc : decode_any W_9dffc = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e000 : bv 32 := 0xdae66ce3.
Lemma F_9e000 : fetch_word SEGS (0x9e948 : word) = Some W_9e000.
Proof. vm_refl. Qed.
Lemma D_9e000 : decode_any W_9e000 = Some (Branch BC_LTU 12 14 7608, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e004 : bv 32 := 0x0005c703.
Lemma F_9e004 : fetch_word SEGS (0x9e94c : word) = Some W_9e004.
Proof. vm_refl. Qed.
Lemma D_9e004 : decode_any W_9e004 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e008 : bv 32 := 0x0015c783.
Lemma F_9e008 : fetch_word SEGS (0x9e950 : word) = Some W_9e008.
Proof. vm_refl. Qed.
Lemma D_9e008 : decode_any W_9e008 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e00c : bv 32 := 0x0025c803.
Lemma F_9e00c : fetch_word SEGS (0x9e954 : word) = Some W_9e00c.
Proof. vm_refl. Qed.
Lemma D_9e00c : decode_any W_9e00c = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e010 : bv 32 := 0x0035c883.
Lemma F_9e010 : fetch_word SEGS (0x9e958 : word) = Some W_9e010.
Proof. vm_refl. Qed.
Lemma D_9e010 : decode_any W_9e010 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e014 : bv 32 := 0x0045c283.
Lemma F_9e014 : fetch_word SEGS (0x9e95c : word) = Some W_9e014.
Proof. vm_refl. Qed.
Lemma D_9e014 : decode_any W_9e014 = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e018 : bv 32 := 0x0055c303.
Lemma F_9e018 : fetch_word SEGS (0x9e960 : word) = Some W_9e018.
Proof. vm_refl. Qed.
Lemma D_9e018 : decode_any W_9e018 = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e01c : bv 32 := 0x0065c383.
Lemma F_9e01c : fetch_word SEGS (0x9e964 : word) = Some W_9e01c.
Proof. vm_refl. Qed.
Lemma D_9e01c : decode_any W_9e01c = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e020 : bv 32 := 0x0075ce03.
Lemma F_9e020 : fetch_word SEGS (0x9e968 : word) = Some W_9e020.
Proof. vm_refl. Qed.
Lemma D_9e020 : decode_any W_9e020 = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e024 : bv 32 := 0x00e68023.
Lemma F_9e024 : fetch_word SEGS (0x9e96c : word) = Some W_9e024.
Proof. vm_refl. Qed.
Lemma D_9e024 : decode_any W_9e024 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e028 : bv 32 := 0x00f680a3.
Lemma F_9e028 : fetch_word SEGS (0x9e970 : word) = Some W_9e028.
Proof. vm_refl. Qed.
Lemma D_9e028 : decode_any W_9e028 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e02c : bv 32 := 0x01068123.
Lemma F_9e02c : fetch_word SEGS (0x9e974 : word) = Some W_9e02c.
Proof. vm_refl. Qed.
Lemma D_9e02c : decode_any W_9e02c = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e030 : bv 32 := 0x011681a3.
Lemma F_9e030 : fetch_word SEGS (0x9e978 : word) = Some W_9e030.
Proof. vm_refl. Qed.
Lemma D_9e030 : decode_any W_9e030 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e034 : bv 32 := 0x0085c703.
Lemma F_9e034 : fetch_word SEGS (0x9e97c : word) = Some W_9e034.
Proof. vm_refl. Qed.
Lemma D_9e034 : decode_any W_9e034 = Some (Load SZ1 false 14 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e038 : bv 32 := 0x0095c783.
Lemma F_9e038 : fetch_word SEGS (0x9e980 : word) = Some W_9e038.
Proof. vm_refl. Qed.
Lemma D_9e038 : decode_any W_9e038 = Some (Load SZ1 false 15 11 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e03c : bv 32 := 0x00a5c803.
Lemma F_9e03c : fetch_word SEGS (0x9e984 : word) = Some W_9e03c.
Proof. vm_refl. Qed.
Lemma D_9e03c : decode_any W_9e03c = Some (Load SZ1 false 16 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e040 : bv 32 := 0x00b5c883.
Lemma F_9e040 : fetch_word SEGS (0x9e988 : word) = Some W_9e040.
Proof. vm_refl. Qed.
Lemma D_9e040 : decode_any W_9e040 = Some (Load SZ1 false 17 11 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e044 : bv 32 := 0x00568223.
Lemma F_9e044 : fetch_word SEGS (0x9e98c : word) = Some W_9e044.
Proof. vm_refl. Qed.
Lemma D_9e044 : decode_any W_9e044 = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e048 : bv 32 := 0x006682a3.
Lemma F_9e048 : fetch_word SEGS (0x9e990 : word) = Some W_9e048.
Proof. vm_refl. Qed.
Lemma D_9e048 : decode_any W_9e048 = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e04c : bv 32 := 0x00768323.
Lemma F_9e04c : fetch_word SEGS (0x9e994 : word) = Some W_9e04c.
Proof. vm_refl. Qed.
Lemma D_9e04c : decode_any W_9e04c = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e050 : bv 32 := 0x01c683a3.
Lemma F_9e050 : fetch_word SEGS (0x9e998 : word) = Some W_9e050.
Proof. vm_refl. Qed.
Lemma D_9e050 : decode_any W_9e050 = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e054 : bv 32 := 0x00c5c283.
Lemma F_9e054 : fetch_word SEGS (0x9e99c : word) = Some W_9e054.
Proof. vm_refl. Qed.
Lemma D_9e054 : decode_any W_9e054 = Some (Load SZ1 false 5 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e058 : bv 32 := 0x00d5c303.
Lemma F_9e058 : fetch_word SEGS (0x9e9a0 : word) = Some W_9e058.
Proof. vm_refl. Qed.
Lemma D_9e058 : decode_any W_9e058 = Some (Load SZ1 false 6 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e05c : bv 32 := 0x00e5c383.
Lemma F_9e05c : fetch_word SEGS (0x9e9a4 : word) = Some W_9e05c.
Proof. vm_refl. Qed.
Lemma D_9e05c : decode_any W_9e05c = Some (Load SZ1 false 7 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e060 : bv 32 := 0x00f5ce03.
Lemma F_9e060 : fetch_word SEGS (0x9e9a8 : word) = Some W_9e060.
Proof. vm_refl. Qed.
Lemma D_9e060 : decode_any W_9e060 = Some (Load SZ1 false 28 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e064 : bv 32 := 0x01058593.
Lemma F_9e064 : fetch_word SEGS (0x9e9ac : word) = Some W_9e064.
Proof. vm_refl. Qed.
Lemma D_9e064 : decode_any W_9e064 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e068 : bv 32 := 0x00e68423.
Lemma F_9e068 : fetch_word SEGS (0x9e9b0 : word) = Some W_9e068.
Proof. vm_refl. Qed.
Lemma D_9e068 : decode_any W_9e068 = Some (Store SZ1 13 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e06c : bv 32 := 0x00f684a3.
Lemma F_9e06c : fetch_word SEGS (0x9e9b4 : word) = Some W_9e06c.
Proof. vm_refl. Qed.
Lemma D_9e06c : decode_any W_9e06c = Some (Store SZ1 13 15 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e070 : bv 32 := 0x01068523.
Lemma F_9e070 : fetch_word SEGS (0x9e9b8 : word) = Some W_9e070.
Proof. vm_refl. Qed.
Lemma D_9e070 : decode_any W_9e070 = Some (Store SZ1 13 16 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e074 : bv 32 := 0x011685a3.
Lemma F_9e074 : fetch_word SEGS (0x9e9bc : word) = Some W_9e074.
Proof. vm_refl. Qed.
Lemma D_9e074 : decode_any W_9e074 = Some (Store SZ1 13 17 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e078 : bv 32 := 0x01068713.
Lemma F_9e078 : fetch_word SEGS (0x9e9c0 : word) = Some W_9e078.
Proof. vm_refl. Qed.
Lemma D_9e078 : decode_any W_9e078 = Some (OpImm ALU_ADD 14 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e07c : bv 32 := 0x00568623.
Lemma F_9e07c : fetch_word SEGS (0x9e9c4 : word) = Some W_9e07c.
Proof. vm_refl. Qed.
Lemma D_9e07c : decode_any W_9e07c = Some (Store SZ1 13 5 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e080 : bv 32 := 0x006686a3.
Lemma F_9e080 : fetch_word SEGS (0x9e9c8 : word) = Some W_9e080.
Proof. vm_refl. Qed.
Lemma D_9e080 : decode_any W_9e080 = Some (Store SZ1 13 6 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e084 : bv 32 := 0x00768723.
Lemma F_9e084 : fetch_word SEGS (0x9e9cc : word) = Some W_9e084.
Proof. vm_refl. Qed.
Lemma D_9e084 : decode_any W_9e084 = Some (Store SZ1 13 7 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e088 : bv 32 := 0x01c687a3.
Lemma F_9e088 : fetch_word SEGS (0x9e9d0 : word) = Some W_9e088.
Proof. vm_refl. Qed.
Lemma D_9e088 : decode_any W_9e088 = Some (Store SZ1 13 28 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e08c : bv 32 := 0x00070693.
Lemma F_9e08c : fetch_word SEGS (0x9e9d4 : word) = Some W_9e08c.
Proof. vm_refl. Qed.
Lemma D_9e08c : decode_any W_9e08c = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e090 : bv 32 := 0x00867713.
Lemma F_9e090 : fetch_word SEGS (0x9e9d8 : word) = Some W_9e090.
Proof. vm_refl. Qed.
Lemma D_9e090 : decode_any W_9e090 = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e094 : bv 32 := 0xd20706e3.
Lemma F_9e094 : fetch_word SEGS (0x9e9dc : word) = Some W_9e094.
Proof. vm_refl. Qed.
Lemma D_9e094 : decode_any W_9e094 = Some (Branch BC_EQ 14 0 7468, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e098 : bv 32 := 0x0005c703.
Lemma F_9e098 : fetch_word SEGS (0x9e9e0 : word) = Some W_9e098.
Proof. vm_refl. Qed.
Lemma D_9e098 : decode_any W_9e098 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e09c : bv 32 := 0x0015c783.
Lemma F_9e09c : fetch_word SEGS (0x9e9e4 : word) = Some W_9e09c.
Proof. vm_refl. Qed.
Lemma D_9e09c : decode_any W_9e09c = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e0a0 : bv 32 := 0x0025c803.
Lemma F_9e0a0 : fetch_word SEGS (0x9e9e8 : word) = Some W_9e0a0.
Proof. vm_refl. Qed.
Lemma D_9e0a0 : decode_any W_9e0a0 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e0a4 : bv 32 := 0x0035c883.
Lemma F_9e0a4 : fetch_word SEGS (0x9e9ec : word) = Some W_9e0a4.
Proof. vm_refl. Qed.
Lemma D_9e0a4 : decode_any W_9e0a4 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e0a8 : bv 32 := 0x0045c283.
Lemma F_9e0a8 : fetch_word SEGS (0x9e9f0 : word) = Some W_9e0a8.
Proof. vm_refl. Qed.
Lemma D_9e0a8 : decode_any W_9e0a8 = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e0ac : bv 32 := 0x0055c303.
Lemma F_9e0ac : fetch_word SEGS (0x9e9f4 : word) = Some W_9e0ac.
Proof. vm_refl. Qed.
Lemma D_9e0ac : decode_any W_9e0ac = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e0b0 : bv 32 := 0x0065c383.
Lemma F_9e0b0 : fetch_word SEGS (0x9e9f8 : word) = Some W_9e0b0.
Proof. vm_refl. Qed.
Lemma D_9e0b0 : decode_any W_9e0b0 = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e0b4 : bv 32 := 0x0075ce03.
Lemma F_9e0b4 : fetch_word SEGS (0x9e9fc : word) = Some W_9e0b4.
Proof. vm_refl. Qed.
Lemma D_9e0b4 : decode_any W_9e0b4 = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e0b8 : bv 32 := 0x00858593.
Lemma F_9e0b8 : fetch_word SEGS (0x9ea00 : word) = Some W_9e0b8.
Proof. vm_refl. Qed.
Lemma D_9e0b8 : decode_any W_9e0b8 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e0bc : bv 32 := 0x00e68023.
Lemma F_9e0bc : fetch_word SEGS (0x9ea04 : word) = Some W_9e0bc.
Proof. vm_refl. Qed.
Lemma D_9e0bc : decode_any W_9e0bc = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e0c0 : bv 32 := 0x00f680a3.
Lemma F_9e0c0 : fetch_word SEGS (0x9ea08 : word) = Some W_9e0c0.
Proof. vm_refl. Qed.
Lemma D_9e0c0 : decode_any W_9e0c0 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e0c4 : bv 32 := 0x01068123.
Lemma F_9e0c4 : fetch_word SEGS (0x9ea0c : word) = Some W_9e0c4.
Proof. vm_refl. Qed.
Lemma D_9e0c4 : decode_any W_9e0c4 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e0c8 : bv 32 := 0x011681a3.
Lemma F_9e0c8 : fetch_word SEGS (0x9ea10 : word) = Some W_9e0c8.
Proof. vm_refl. Qed.
Lemma D_9e0c8 : decode_any W_9e0c8 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e0cc : bv 32 := 0x00868713.
Lemma F_9e0cc : fetch_word SEGS (0x9ea14 : word) = Some W_9e0cc.
Proof. vm_refl. Qed.
Lemma D_9e0cc : decode_any W_9e0cc = Some (OpImm ALU_ADD 14 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e0d0 : bv 32 := 0x00568223.
Lemma F_9e0d0 : fetch_word SEGS (0x9ea18 : word) = Some W_9e0d0.
Proof. vm_refl. Qed.
Lemma D_9e0d0 : decode_any W_9e0d0 = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e0d4 : bv 32 := 0x006682a3.
Lemma F_9e0d4 : fetch_word SEGS (0x9ea1c : word) = Some W_9e0d4.
Proof. vm_refl. Qed.
Lemma D_9e0d4 : decode_any W_9e0d4 = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e0d8 : bv 32 := 0x00768323.
Lemma F_9e0d8 : fetch_word SEGS (0x9ea20 : word) = Some W_9e0d8.
Proof. vm_refl. Qed.
Lemma D_9e0d8 : decode_any W_9e0d8 = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e0dc : bv 32 := 0x01c683a3.
Lemma F_9e0dc : fetch_word SEGS (0x9ea24 : word) = Some W_9e0dc.
Proof. vm_refl. Qed.
Lemma D_9e0dc : decode_any W_9e0dc = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e0e0 : bv 32 := 0x00070693.
Lemma F_9e0e0 : fetch_word SEGS (0x9ea28 : word) = Some W_9e0e0.
Proof. vm_refl. Qed.
Lemma D_9e0e0 : decode_any W_9e0e0 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e0e4 : bv 32 := 0x00467713.
Lemma F_9e0e4 : fetch_word SEGS (0x9ea2c : word) = Some W_9e0e4.
Proof. vm_refl. Qed.
Lemma D_9e0e4 : decode_any W_9e0e4 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e0e8 : bv 32 := 0x02070863.
Lemma F_9e0e8 : fetch_word SEGS (0x9ea30 : word) = Some W_9e0e8.
Proof. vm_refl. Qed.
Lemma D_9e0e8 : decode_any W_9e0e8 = Some (Branch BC_EQ 14 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e0ec : bv 32 := 0x0005c703.
Lemma F_9e0ec : fetch_word SEGS (0x9ea34 : word) = Some W_9e0ec.
Proof. vm_refl. Qed.
Lemma D_9e0ec : decode_any W_9e0ec = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e0f0 : bv 32 := 0x0015c783.
Lemma F_9e0f0 : fetch_word SEGS (0x9ea38 : word) = Some W_9e0f0.
Proof. vm_refl. Qed.
Lemma D_9e0f0 : decode_any W_9e0f0 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e0f4 : bv 32 := 0x0025c803.
Lemma F_9e0f4 : fetch_word SEGS (0x9ea3c : word) = Some W_9e0f4.
Proof. vm_refl. Qed.
Lemma D_9e0f4 : decode_any W_9e0f4 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e0f8 : bv 32 := 0x0035c883.
Lemma F_9e0f8 : fetch_word SEGS (0x9ea40 : word) = Some W_9e0f8.
Proof. vm_refl. Qed.
Lemma D_9e0f8 : decode_any W_9e0f8 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e0fc : bv 32 := 0x00458593.
Lemma F_9e0fc : fetch_word SEGS (0x9ea44 : word) = Some W_9e0fc.
Proof. vm_refl. Qed.
Lemma D_9e0fc : decode_any W_9e0fc = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e100 : bv 32 := 0x00468293.
Lemma F_9e100 : fetch_word SEGS (0x9ea48 : word) = Some W_9e100.
Proof. vm_refl. Qed.
Lemma D_9e100 : decode_any W_9e100 = Some (OpImm ALU_ADD 5 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e104 : bv 32 := 0x00e68023.
Lemma F_9e104 : fetch_word SEGS (0x9ea4c : word) = Some W_9e104.
Proof. vm_refl. Qed.
Lemma D_9e104 : decode_any W_9e104 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e108 : bv 32 := 0x00f680a3.
Lemma F_9e108 : fetch_word SEGS (0x9ea50 : word) = Some W_9e108.
Proof. vm_refl. Qed.
Lemma D_9e108 : decode_any W_9e108 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e10c : bv 32 := 0x01068123.
Lemma F_9e10c : fetch_word SEGS (0x9ea54 : word) = Some W_9e10c.
Proof. vm_refl. Qed.
Lemma D_9e10c : decode_any W_9e10c = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e110 : bv 32 := 0x011681a3.
Lemma F_9e110 : fetch_word SEGS (0x9ea58 : word) = Some W_9e110.
Proof. vm_refl. Qed.
Lemma D_9e110 : decode_any W_9e110 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e114 : bv 32 := 0x00028693.
Lemma F_9e114 : fetch_word SEGS (0x9ea5c : word) = Some W_9e114.
Proof. vm_refl. Qed.
Lemma D_9e114 : decode_any W_9e114 = Some (OpImm ALU_ADD 13 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e118 : bv 32 := 0x00267713.
Lemma F_9e118 : fetch_word SEGS (0x9ea60 : word) = Some W_9e118.
Proof. vm_refl. Qed.
Lemma D_9e118 : decode_any W_9e118 = Some (OpImm ALU_AND 14 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e11c : bv 32 := 0x00071863.
Lemma F_9e11c : fetch_word SEGS (0x9ea64 : word) = Some W_9e11c.
Proof. vm_refl. Qed.
Lemma D_9e11c : decode_any W_9e11c = Some (Branch BC_NE 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e120 : bv 32 := 0x00167613.
Lemma F_9e120 : fetch_word SEGS (0x9ea68 : word) = Some W_9e120.
Proof. vm_refl. Qed.
Lemma D_9e120 : decode_any W_9e120 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e124 : bv 32 := 0x02061663.
Lemma F_9e124 : fetch_word SEGS (0x9ea6c : word) = Some W_9e124.
Proof. vm_refl. Qed.
Lemma D_9e124 : decode_any W_9e124 = Some (Branch BC_NE 12 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e128 : bv 32 := 0x00008067.
Lemma F_9e128 : fetch_word SEGS (0x9ea70 : word) = Some W_9e128.
Proof. vm_refl. Qed.
Lemma D_9e128 : decode_any W_9e128 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e12c : bv 32 := 0x0005c703.
Lemma F_9e12c : fetch_word SEGS (0x9ea74 : word) = Some W_9e12c.
Proof. vm_refl. Qed.
Lemma D_9e12c : decode_any W_9e12c = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e130 : bv 32 := 0x0015c783.
Lemma F_9e130 : fetch_word SEGS (0x9ea78 : word) = Some W_9e130.
Proof. vm_refl. Qed.
Lemma D_9e130 : decode_any W_9e130 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e134 : bv 32 := 0x00258593.
Lemma F_9e134 : fetch_word SEGS (0x9ea7c : word) = Some W_9e134.
Proof. vm_refl. Qed.
Lemma D_9e134 : decode_any W_9e134 = Some (OpImm ALU_ADD 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e138 : bv 32 := 0x00268813.
Lemma F_9e138 : fetch_word SEGS (0x9ea80 : word) = Some W_9e138.
Proof. vm_refl. Qed.
Lemma D_9e138 : decode_any W_9e138 = Some (OpImm ALU_ADD 16 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e13c : bv 32 := 0x00e68023.
Lemma F_9e13c : fetch_word SEGS (0x9ea84 : word) = Some W_9e13c.
Proof. vm_refl. Qed.
Lemma D_9e13c : decode_any W_9e13c = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e140 : bv 32 := 0x00f680a3.
Lemma F_9e140 : fetch_word SEGS (0x9ea88 : word) = Some W_9e140.
Proof. vm_refl. Qed.
Lemma D_9e140 : decode_any W_9e140 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e144 : bv 32 := 0x00080693.
Lemma F_9e144 : fetch_word SEGS (0x9ea8c : word) = Some W_9e144.
Proof. vm_refl. Qed.
Lemma D_9e144 : decode_any W_9e144 = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e148 : bv 32 := 0x00167613.
Lemma F_9e148 : fetch_word SEGS (0x9ea90 : word) = Some W_9e148.
Proof. vm_refl. Qed.
Lemma D_9e148 : decode_any W_9e148 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e14c : bv 32 := 0xfc060ee3.
Lemma F_9e14c : fetch_word SEGS (0x9ea94 : word) = Some W_9e14c.
Proof. vm_refl. Qed.
Lemma D_9e14c : decode_any W_9e14c = Some (Branch BC_EQ 12 0 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e150 : bv 32 := 0x0005c583.
Lemma F_9e150 : fetch_word SEGS (0x9ea98 : word) = Some W_9e150.
Proof. vm_refl. Qed.
Lemma D_9e150 : decode_any W_9e150 = Some (Load SZ1 false 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e154 : bv 32 := 0x00b68023.
Lemma F_9e154 : fetch_word SEGS (0x9ea9c : word) = Some W_9e154.
Proof. vm_refl. Qed.
Lemma D_9e154 : decode_any W_9e154 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e158 : bv 32 := 0x00008067.
Lemma F_9e158 : fetch_word SEGS (0x9eaa0 : word) = Some W_9e158.
Proof. vm_refl. Qed.
Lemma D_9e158 : decode_any W_9e158 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Img.TwB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_9dd58 : bv 32 := 0x0035f693.
Lemma F_9dd58 : fetch_word SEGS (0x9ea84 : word) = Some W_9dd58.
Proof. vm_refl. Qed.
Lemma D_9dd58 : decode_any W_9dd58 = Some (OpImm ALU_AND 13 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dd5c : bv 32 := 0x10068863.
Lemma F_9dd5c : fetch_word SEGS (0x9ea88 : word) = Some W_9dd5c.
Proof. vm_refl. Qed.
Lemma D_9dd5c : decode_any W_9dd5c = Some (Branch BC_EQ 13 0 272, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dd60 : bv 32 := 0x02060e63.
Lemma F_9dd60 : fetch_word SEGS (0x9ea8c : word) = Some W_9dd60.
Proof. vm_refl. Qed.
Lemma D_9dd60 : decode_any W_9dd60 = Some (Branch BC_EQ 12 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dd64 : bv 32 := 0x00158713.
Lemma F_9dd64 : fetch_word SEGS (0x9ea90 : word) = Some W_9dd64.
Proof. vm_refl. Qed.
Lemma D_9dd64 : decode_any W_9dd64 = Some (OpImm ALU_ADD 14 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dd68 : bv 32 := 0x00100793.
Lemma F_9dd68 : fetch_word SEGS (0x9ea94 : word) = Some W_9dd68.
Proof. vm_refl. Qed.
Lemma D_9dd68 : decode_any W_9dd68 = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dd6c : bv 32 := 0x00050693.
Lemma F_9dd6c : fetch_word SEGS (0x9ea98 : word) = Some W_9dd6c.
Proof. vm_refl. Qed.
Lemma D_9dd6c : decode_any W_9dd6c = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dd70 : bv 32 := 0x0005c883.
Lemma F_9dd70 : fetch_word SEGS (0x9ea9c : word) = Some W_9dd70.
Proof. vm_refl. Qed.
Lemma D_9dd70 : decode_any W_9dd70 = Some (Load SZ1 false 17 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dd74 : bv 32 := 0x00060813.
Lemma F_9dd74 : fetch_word SEGS (0x9eaa0 : word) = Some W_9dd74.
Proof. vm_refl. Qed.
Lemma D_9dd74 : decode_any W_9dd74 = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dd78 : bv 32 := 0x00158593.
Lemma F_9dd78 : fetch_word SEGS (0x9eaa4 : word) = Some W_9dd78.
Proof. vm_refl. Qed.
Lemma D_9dd78 : decode_any W_9dd78 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dd7c : bv 32 := 0x00377293.
Lemma F_9dd7c : fetch_word SEGS (0x9eaa8 : word) = Some W_9dd7c.
Proof. vm_refl. Qed.
Lemma D_9dd7c : decode_any W_9dd7c = Some (OpImm ALU_AND 5 14 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dd80 : bv 32 := 0x01168023.
Lemma F_9dd80 : fetch_word SEGS (0x9eaac : word) = Some W_9dd80.
Proof. vm_refl. Qed.
Lemma D_9dd80 : decode_any W_9dd80 = Some (Store SZ1 13 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dd84 : bv 32 := 0x00168693.
Lemma F_9dd84 : fetch_word SEGS (0x9eab0 : word) = Some W_9dd84.
Proof. vm_refl. Qed.
Lemma D_9dd84 : decode_any W_9dd84 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dd88 : bv 32 := 0xfff60613.
Lemma F_9dd88 : fetch_word SEGS (0x9eab4 : word) = Some W_9dd88.
Proof. vm_refl. Qed.
Lemma D_9dd88 : decode_any W_9dd88 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dd8c : bv 32 := 0x00028a63.
Lemma F_9dd8c : fetch_word SEGS (0x9eab8 : word) = Some W_9dd8c.
Proof. vm_refl. Qed.
Lemma D_9dd8c : decode_any W_9dd8c = Some (Branch BC_EQ 5 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dd90 : bv 32 := 0x00170713.
Lemma F_9dd90 : fetch_word SEGS (0x9eabc : word) = Some W_9dd90.
Proof. vm_refl. Qed.
Lemma D_9dd90 : decode_any W_9dd90 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dd94 : bv 32 := 0xfcf81ee3.
Lemma F_9dd94 : fetch_word SEGS (0x9eac0 : word) = Some W_9dd94.
Proof. vm_refl. Qed.
Lemma D_9dd94 : decode_any W_9dd94 = Some (Branch BC_NE 16 15 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dd98 : bv 32 := 0x0080006f.
Lemma F_9dd98 : fetch_word SEGS (0x9eac4 : word) = Some W_9dd98.
Proof. vm_refl. Qed.
Lemma D_9dd98 : decode_any W_9dd98 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dd9c : bv 32 := 0x00050693.
Lemma F_9dd9c : fetch_word SEGS (0x9eac8 : word) = Some W_9dd9c.
Proof. vm_refl. Qed.
Lemma D_9dd9c : decode_any W_9dd9c = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dda0 : bv 32 := 0x0036f793.
Lemma F_9dda0 : fetch_word SEGS (0x9eacc : word) = Some W_9dda0.
Proof. vm_refl. Qed.
Lemma D_9dda0 : decode_any W_9dda0 = Some (OpImm ALU_AND 15 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dda4 : bv 32 := 0x0c078a63.
Lemma F_9dda4 : fetch_word SEGS (0x9ead0 : word) = Some W_9dda4.
Proof. vm_refl. Qed.
Lemma D_9dda4 : decode_any W_9dda4 = Some (Branch BC_EQ 15 0 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dda8 : bv 32 := 0x02000713.
Lemma F_9dda8 : fetch_word SEGS (0x9ead4 : word) = Some W_9dda8.
Proof. vm_refl. Qed.
Lemma D_9dda8 : decode_any W_9dda8 = Some (OpImm ALU_ADD 14 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ddac : bv 32 := 0x02e67063.
Lemma F_9ddac : fetch_word SEGS (0x9ead8 : word) = Some W_9ddac.
Proof. vm_refl. Qed.
Lemma D_9ddac : decode_any W_9ddac = Some (Branch BC_GEU 12 14 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ddb0 : bv 32 := 0x01000713.
Lemma F_9ddb0 : fetch_word SEGS (0x9eadc : word) = Some W_9ddb0.
Proof. vm_refl. Qed.
Lemma D_9ddb0 : decode_any W_9ddb0 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ddb4 : bv 32 := 0x24e67863.
Lemma F_9ddb4 : fetch_word SEGS (0x9eae0 : word) = Some W_9ddb4.
Proof. vm_refl. Qed.
Lemma D_9ddb4 : decode_any W_9ddb4 = Some (Branch BC_GEU 12 14 592, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ddb8 : bv 32 := 0x00867713.
Lemma F_9ddb8 : fetch_word SEGS (0x9eae4 : word) = Some W_9ddb8.
Proof. vm_refl. Qed.
Lemma D_9ddb8 : decode_any W_9ddb8 = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ddbc : bv 32 := 0x2c071e63.
Lemma F_9ddbc : fetch_word SEGS (0x9eae8 : word) = Some W_9ddbc.
Proof. vm_refl. Qed.
Lemma D_9ddbc : decode_any W_9ddbc = Some (Branch BC_NE 14 0 732, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ddc0 : bv 32 := 0x00467713.
Lemma F_9ddc0 : fetch_word SEGS (0x9eaec : word) = Some W_9ddc0.
Proof. vm_refl. Qed.
Lemma D_9ddc0 : decode_any W_9ddc0 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ddc4 : bv 32 := 0x32071463.
Lemma F_9ddc4 : fetch_word SEGS (0x9eaf0 : word) = Some W_9ddc4.
Proof. vm_refl. Qed.
Lemma D_9ddc4 : decode_any W_9ddc4 = Some (Branch BC_NE 14 0 808, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ddc8 : bv 32 := 0x3500006f.
Lemma F_9ddc8 : fetch_word SEGS (0x9eaf4 : word) = Some W_9ddc8.
Proof. vm_refl. Qed.
Lemma D_9ddc8 : decode_any W_9ddc8 = Some (Jal 0 848, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ddcc : bv 32 := 0x0005a703.
Lemma F_9ddcc : fetch_word SEGS (0x9eaf8 : word) = Some W_9ddcc.
Proof. vm_refl. Qed.
Lemma D_9ddcc : decode_any W_9ddcc = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ddd0 : bv 32 := 0x00300813.
Lemma F_9ddd0 : fetch_word SEGS (0x9eafc : word) = Some W_9ddd0.
Proof. vm_refl. Qed.
Lemma D_9ddd0 : decode_any W_9ddd0 = Some (OpImm ALU_ADD 16 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ddd4 : bv 32 := 0x11078e63.
Lemma F_9ddd4 : fetch_word SEGS (0x9eb00 : word) = Some W_9ddd4.
Proof. vm_refl. Qed.
Lemma D_9ddd4 : decode_any W_9ddd4 = Some (Branch BC_EQ 15 16 284, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ddd8 : bv 32 := 0x00200813.
Lemma F_9ddd8 : fetch_word SEGS (0x9eb04 : word) = Some W_9ddd8.
Proof. vm_refl. Qed.
Lemma D_9ddd8 : decode_any W_9ddd8 = Some (OpImm ALU_ADD 16 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dddc : bv 32 := 0x19079c63.
Lemma F_9dddc : fetch_word SEGS (0x9eb08 : word) = Some W_9dddc.
Proof. vm_refl. Qed.
Lemma D_9dddc : decode_any W_9dddc = Some (Branch BC_NE 15 16 408, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dde0 : bv 32 := 0x00875793.
Lemma F_9dde0 : fetch_word SEGS (0x9eb0c : word) = Some W_9dde0.
Proof. vm_refl. Qed.
Lemma D_9dde0 : decode_any W_9dde0 = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dde4 : bv 32 := 0xffe60613.
Lemma F_9dde4 : fetch_word SEGS (0x9eb10 : word) = Some W_9dde4.
Proof. vm_refl. Qed.
Lemma D_9dde4 : decode_any W_9dde4 = Some (OpImm ALU_ADD 12 12 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dde8 : bv 32 := 0x00e68023.
Lemma F_9dde8 : fetch_word SEGS (0x9eb14 : word) = Some W_9dde8.
Proof. vm_refl. Qed.
Lemma D_9dde8 : decode_any W_9dde8 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ddec : bv 32 := 0x00f680a3.
Lemma F_9ddec : fetch_word SEGS (0x9eb18 : word) = Some W_9ddec.
Proof. vm_refl. Qed.
Lemma D_9ddec : decode_any W_9ddec = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ddf0 : bv 32 := 0x00268693.
Lemma F_9ddf0 : fetch_word SEGS (0x9eb1c : word) = Some W_9ddf0.
Proof. vm_refl. Qed.
Lemma D_9ddf0 : decode_any W_9ddf0 = Some (OpImm ALU_ADD 13 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ddf4 : bv 32 := 0x01058593.
Lemma F_9ddf4 : fetch_word SEGS (0x9eb20 : word) = Some W_9ddf4.
Proof. vm_refl. Qed.
Lemma D_9ddf4 : decode_any W_9ddf4 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ddf8 : bv 32 := 0x01100793.
Lemma F_9ddf8 : fetch_word SEGS (0x9eb24 : word) = Some W_9ddf8.
Proof. vm_refl. Qed.
Lemma D_9ddf8 : decode_any W_9ddf8 = Some (OpImm ALU_ADD 15 0 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ddfc : bv 32 := 0x0107581b.
Lemma F_9ddfc : fetch_word SEGS (0x9eb28 : word) = Some W_9ddfc.
Proof. vm_refl. Qed.
Lemma D_9ddfc : decode_any W_9ddfc = Some (ShiftImm32 ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9de00 : bv 32 := 0xff45a883.
Lemma F_9de00 : fetch_word SEGS (0x9eb2c : word) = Some W_9de00.
Proof. vm_refl. Qed.
Lemma D_9de00 : decode_any W_9de00 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9de04 : bv 32 := 0xff85a283.
Lemma F_9de04 : fetch_word SEGS (0x9eb30 : word) = Some W_9de04.
Proof. vm_refl. Qed.
Lemma D_9de04 : decode_any W_9de04 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9de08 : bv 32 := 0xffc5a303.
Lemma F_9de08 : fetch_word SEGS (0x9eb34 : word) = Some W_9de08.
Proof. vm_refl. Qed.
Lemma D_9de08 : decode_any W_9de08 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9de0c : bv 32 := 0x0005a703.
Lemma F_9de0c : fetch_word SEGS (0x9eb38 : word) = Some W_9de0c.
Proof. vm_refl. Qed.
Lemma D_9de0c : decode_any W_9de0c = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9de10 : bv 32 := 0x01089393.
Lemma F_9de10 : fetch_word SEGS (0x9eb3c : word) = Some W_9de10.
Proof. vm_refl. Qed.
Lemma D_9de10 : decode_any W_9de10 = Some (ShiftImm ALU_SLL 7 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9de14 : bv 32 := 0x0108d89b.
Lemma F_9de14 : fetch_word SEGS (0x9eb40 : word) = Some W_9de14.
Proof. vm_refl. Qed.
Lemma D_9de14 : decode_any W_9de14 = Some (ShiftImm32 ALU_SRL 17 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9de18 : bv 32 := 0x0103e833.
Lemma F_9de18 : fetch_word SEGS (0x9eb44 : word) = Some W_9de18.
Proof. vm_refl. Qed.
Lemma D_9de18 : decode_any W_9de18 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9de1c : bv 32 := 0x01029393.
Lemma F_9de1c : fetch_word SEGS (0x9eb48 : word) = Some W_9de1c.
Proof. vm_refl. Qed.
Lemma D_9de1c : decode_any W_9de1c = Some (ShiftImm ALU_SLL 7 5 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9de20 : bv 32 := 0x0102d29b.
Lemma F_9de20 : fetch_word SEGS (0x9eb4c : word) = Some W_9de20.
Proof. vm_refl. Qed.
Lemma D_9de20 : decode_any W_9de20 = Some (ShiftImm32 ALU_SRL 5 5 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9de24 : bv 32 := 0x0113e8b3.
Lemma F_9de24 : fetch_word SEGS (0x9eb50 : word) = Some W_9de24.
Proof. vm_refl. Qed.
Lemma D_9de24 : decode_any W_9de24 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9de28 : bv 32 := 0x01031393.
Lemma F_9de28 : fetch_word SEGS (0x9eb54 : word) = Some W_9de28.
Proof. vm_refl. Qed.
Lemma D_9de28 : decode_any W_9de28 = Some (ShiftImm ALU_SLL 7 6 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9de2c : bv 32 := 0x0103531b.
Lemma F_9de2c : fetch_word SEGS (0x9eb58 : word) = Some W_9de2c.
Proof. vm_refl. Qed.
Lemma D_9de2c : decode_any W_9de2c = Some (ShiftImm32 ALU_SRL 6 6 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9de30 : bv 32 := 0x0053e2b3.
Lemma F_9de30 : fetch_word SEGS (0x9eb5c : word) = Some W_9de30.
Proof. vm_refl. Qed.
Lemma D_9de30 : decode_any W_9de30 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9de34 : bv 32 := 0x01071393.
Lemma F_9de34 : fetch_word SEGS (0x9eb60 : word) = Some W_9de34.
Proof. vm_refl. Qed.
Lemma D_9de34 : decode_any W_9de34 = Some (ShiftImm ALU_SLL 7 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9de38 : bv 32 := 0x0063e333.
Lemma F_9de38 : fetch_word SEGS (0x9eb64 : word) = Some W_9de38.
Proof. vm_refl. Qed.
Lemma D_9de38 : decode_any W_9de38 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9de3c : bv 32 := 0xff060613.
Lemma F_9de3c : fetch_word SEGS (0x9eb68 : word) = Some W_9de3c.
Proof. vm_refl. Qed.
Lemma D_9de3c : decode_any W_9de3c = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9de40 : bv 32 := 0x0106a023.
Lemma F_9de40 : fetch_word SEGS (0x9eb6c : word) = Some W_9de40.
Proof. vm_refl. Qed.
Lemma D_9de40 : decode_any W_9de40 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9de44 : bv 32 := 0x0116a223.
Lemma F_9de44 : fetch_word SEGS (0x9eb70 : word) = Some W_9de44.
Proof. vm_refl. Qed.
Lemma D_9de44 : decode_any W_9de44 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9de48 : bv 32 := 0x0056a423.
Lemma F_9de48 : fetch_word SEGS (0x9eb74 : word) = Some W_9de48.
Proof. vm_refl. Qed.
Lemma D_9de48 : decode_any W_9de48 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9de4c : bv 32 := 0x0066a623.
Lemma F_9de4c : fetch_word SEGS (0x9eb78 : word) = Some W_9de4c.
Proof. vm_refl. Qed.
Lemma D_9de4c : decode_any W_9de4c = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9de50 : bv 32 := 0x01068693.
Lemma F_9de50 : fetch_word SEGS (0x9eb7c : word) = Some W_9de50.
Proof. vm_refl. Qed.
Lemma D_9de50 : decode_any W_9de50 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9de54 : bv 32 := 0x01058593.
Lemma F_9de54 : fetch_word SEGS (0x9eb80 : word) = Some W_9de54.
Proof. vm_refl. Qed.
Lemma D_9de54 : decode_any W_9de54 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9de58 : bv 32 := 0xfac7e2e3.
Lemma F_9de58 : fetch_word SEGS (0x9eb84 : word) = Some W_9de58.
Proof. vm_refl. Qed.
Lemma D_9de58 : decode_any W_9de58 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9de5c : bv 32 := 0xff258593.
Lemma F_9de5c : fetch_word SEGS (0x9eb88 : word) = Some W_9de5c.
Proof. vm_refl. Qed.
Lemma D_9de5c : decode_any W_9de5c = Some (OpImm ALU_ADD 11 11 4082, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9de60 : bv 32 := 0x01000713.
Lemma F_9de60 : fetch_word SEGS (0x9eb8c : word) = Some W_9de60.
Proof. vm_refl. Qed.
Lemma D_9de60 : decode_any W_9de60 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9de64 : bv 32 := 0xf4e66ae3.
Lemma F_9de64 : fetch_word SEGS (0x9eb90 : word) = Some W_9de64.
Proof. vm_refl. Qed.
Lemma D_9de64 : decode_any W_9de64 = Some (Branch BC_LTU 12 14 8020, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9de68 : bv 32 := 0x19c0006f.
Lemma F_9de68 : fetch_word SEGS (0x9eb94 : word) = Some W_9de68.
Proof. vm_refl. Qed.
Lemma D_9de68 : decode_any W_9de68 = Some (Jal 0 412, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9de6c : bv 32 := 0x00050693.
Lemma F_9de6c : fetch_word SEGS (0x9eb98 : word) = Some W_9de6c.
Proof. vm_refl. Qed.
Lemma D_9de6c : decode_any W_9de6c = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9de70 : bv 32 := 0x00357793.
Lemma F_9de70 : fetch_word SEGS (0x9eb9c : word) = Some W_9de70.
Proof. vm_refl. Qed.
Lemma D_9de70 : decode_any W_9de70 = Some (OpImm ALU_AND 15 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9de74 : bv 32 := 0xf2079ae3.
Lemma F_9de74 : fetch_word SEGS (0x9eba0 : word) = Some W_9de74.
Proof. vm_refl. Qed.
Lemma D_9de74 : decode_any W_9de74 = Some (Branch BC_NE 15 0 7988, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9de78 : bv 32 := 0x01000713.
Lemma F_9de78 : fetch_word SEGS (0x9eba4 : word) = Some W_9de78.
Proof. vm_refl. Qed.
Lemma D_9de78 : decode_any W_9de78 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9de7c : bv 32 := 0x02e66c63.
Lemma F_9de7c : fetch_word SEGS (0x9eba8 : word) = Some W_9de7c.
Proof. vm_refl. Qed.
Lemma D_9de7c : decode_any W_9de7c = Some (Branch BC_LTU 12 14 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9de80 : bv 32 := 0x00f00713.
Lemma F_9de80 : fetch_word SEGS (0x9ebac : word) = Some W_9de80.
Proof. vm_refl. Qed.
Lemma D_9de80 : decode_any W_9de80 = Some (OpImm ALU_ADD 14 0 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9de84 : bv 32 := 0x0005a783.
Lemma F_9de84 : fetch_word SEGS (0x9ebb0 : word) = Some W_9de84.
Proof. vm_refl. Qed.
Lemma D_9de84 : decode_any W_9de84 = Some (Load SZ4 true 15 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9de88 : bv 32 := 0x0045a803.
Lemma F_9de88 : fetch_word SEGS (0x9ebb4 : word) = Some W_9de88.
Proof. vm_refl. Qed.
Lemma D_9de88 : decode_any W_9de88 = Some (Load SZ4 true 16 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9de8c : bv 32 := 0x0085a883.
Lemma F_9de8c : fetch_word SEGS (0x9ebb8 : word) = Some W_9de8c.
Proof. vm_refl. Qed.
Lemma D_9de8c : decode_any W_9de8c = Some (Load SZ4 true 17 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9de90 : bv 32 := 0x00c5a283.
Lemma F_9de90 : fetch_word SEGS (0x9ebbc : word) = Some W_9de90.
Proof. vm_refl. Qed.
Lemma D_9de90 : decode_any W_9de90 = Some (Load SZ4 true 5 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9de94 : bv 32 := 0x01058593.
Lemma F_9de94 : fetch_word SEGS (0x9ebc0 : word) = Some W_9de94.
Proof. vm_refl. Qed.
Lemma D_9de94 : decode_any W_9de94 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9de98 : bv 32 := 0xff060613.
Lemma F_9de98 : fetch_word SEGS (0x9ebc4 : word) = Some W_9de98.
Proof. vm_refl. Qed.
Lemma D_9de98 : decode_any W_9de98 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9de9c : bv 32 := 0x00f6a023.
Lemma F_9de9c : fetch_word SEGS (0x9ebc8 : word) = Some W_9de9c.
Proof. vm_refl. Qed.
Lemma D_9de9c : decode_any W_9de9c = Some (Store SZ4 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dea0 : bv 32 := 0x0106a223.
Lemma F_9dea0 : fetch_word SEGS (0x9ebcc : word) = Some W_9dea0.
Proof. vm_refl. Qed.
Lemma D_9dea0 : decode_any W_9dea0 = Some (Store SZ4 13 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dea4 : bv 32 := 0x0116a423.
Lemma F_9dea4 : fetch_word SEGS (0x9ebd0 : word) = Some W_9dea4.
Proof. vm_refl. Qed.
Lemma D_9dea4 : decode_any W_9dea4 = Some (Store SZ4 13 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dea8 : bv 32 := 0x0056a623.
Lemma F_9dea8 : fetch_word SEGS (0x9ebd4 : word) = Some W_9dea8.
Proof. vm_refl. Qed.
Lemma D_9dea8 : decode_any W_9dea8 = Some (Store SZ4 13 5 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9deac : bv 32 := 0x01068693.
Lemma F_9deac : fetch_word SEGS (0x9ebd8 : word) = Some W_9deac.
Proof. vm_refl. Qed.
Lemma D_9deac : decode_any W_9deac = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9deb0 : bv 32 := 0xfcc76ae3.
Lemma F_9deb0 : fetch_word SEGS (0x9ebdc : word) = Some W_9deb0.
Proof. vm_refl. Qed.
Lemma D_9deb0 : decode_any W_9deb0 = Some (Branch BC_LTU 14 12 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9deb4 : bv 32 := 0x00800713.
Lemma F_9deb4 : fetch_word SEGS (0x9ebe0 : word) = Some W_9deb4.
Proof. vm_refl. Qed.
Lemma D_9deb4 : decode_any W_9deb4 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9deb8 : bv 32 := 0x00e66e63.
Lemma F_9deb8 : fetch_word SEGS (0x9ebe4 : word) = Some W_9deb8.
Proof. vm_refl. Qed.
Lemma D_9deb8 : decode_any W_9deb8 = Some (Branch BC_LTU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9debc : bv 32 := 0x0005a703.
Lemma F_9debc : fetch_word SEGS (0x9ebe8 : word) = Some W_9debc.
Proof. vm_refl. Qed.
Lemma D_9debc : decode_any W_9debc = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dec0 : bv 32 := 0x0045a783.
Lemma F_9dec0 : fetch_word SEGS (0x9ebec : word) = Some W_9dec0.
Proof. vm_refl. Qed.
Lemma D_9dec0 : decode_any W_9dec0 = Some (Load SZ4 true 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dec4 : bv 32 := 0x00e6a023.
Lemma F_9dec4 : fetch_word SEGS (0x9ebf0 : word) = Some W_9dec4.
Proof. vm_refl. Qed.
Lemma D_9dec4 : decode_any W_9dec4 = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dec8 : bv 32 := 0x00f6a223.
Lemma F_9dec8 : fetch_word SEGS (0x9ebf4 : word) = Some W_9dec8.
Proof. vm_refl. Qed.
Lemma D_9dec8 : decode_any W_9dec8 = Some (Store SZ4 13 15 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9decc : bv 32 := 0x00868693.
Lemma F_9decc : fetch_word SEGS (0x9ebf8 : word) = Some W_9decc.
Proof. vm_refl. Qed.
Lemma D_9decc : decode_any W_9decc = Some (OpImm ALU_ADD 13 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ded0 : bv 32 := 0x00858593.
Lemma F_9ded0 : fetch_word SEGS (0x9ebfc : word) = Some W_9ded0.
Proof. vm_refl. Qed.
Lemma D_9ded0 : decode_any W_9ded0 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ded4 : bv 32 := 0x00467713.
Lemma F_9ded4 : fetch_word SEGS (0x9ec00 : word) = Some W_9ded4.
Proof. vm_refl. Qed.
Lemma D_9ded4 : decode_any W_9ded4 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ded8 : bv 32 := 0x24070063.
Lemma F_9ded8 : fetch_word SEGS (0x9ec04 : word) = Some W_9ded8.
Proof. vm_refl. Qed.
Lemma D_9ded8 : decode_any W_9ded8 = Some (Branch BC_EQ 14 0 576, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dedc : bv 32 := 0x0005a703.
Lemma F_9dedc : fetch_word SEGS (0x9ec08 : word) = Some W_9dedc.
Proof. vm_refl. Qed.
Lemma D_9dedc : decode_any W_9dedc = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dee0 : bv 32 := 0x00458593.
Lemma F_9dee0 : fetch_word SEGS (0x9ec0c : word) = Some W_9dee0.
Proof. vm_refl. Qed.
Lemma D_9dee0 : decode_any W_9dee0 = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dee4 : bv 32 := 0x00e6a023.
Lemma F_9dee4 : fetch_word SEGS (0x9ec10 : word) = Some W_9dee4.
Proof. vm_refl. Qed.
Lemma D_9dee4 : decode_any W_9dee4 = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dee8 : bv 32 := 0x00468693.
Lemma F_9dee8 : fetch_word SEGS (0x9ec14 : word) = Some W_9dee8.
Proof. vm_refl. Qed.
Lemma D_9dee8 : decode_any W_9dee8 = Some (OpImm ALU_ADD 13 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9deec : bv 32 := 0x22c0006f.
Lemma F_9deec : fetch_word SEGS (0x9ec18 : word) = Some W_9deec.
Proof. vm_refl. Qed.
Lemma D_9deec : decode_any W_9deec = Some (Jal 0 556, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9def0 : bv 32 := 0x00e68023.
Lemma F_9def0 : fetch_word SEGS (0x9ec1c : word) = Some W_9def0.
Proof. vm_refl. Qed.
Lemma D_9def0 : decode_any W_9def0 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9def4 : bv 32 := 0x00168693.
Lemma F_9def4 : fetch_word SEGS (0x9ec20 : word) = Some W_9def4.
Proof. vm_refl. Qed.
Lemma D_9def4 : decode_any W_9def4 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9def8 : bv 32 := 0xfff60613.
Lemma F_9def8 : fetch_word SEGS (0x9ec24 : word) = Some W_9def8.
Proof. vm_refl. Qed.
Lemma D_9def8 : decode_any W_9def8 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9defc : bv 32 := 0x01058593.
Lemma F_9defc : fetch_word SEGS (0x9ec28 : word) = Some W_9defc.
Proof. vm_refl. Qed.
Lemma D_9defc : decode_any W_9defc = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df00 : bv 32 := 0x01200793.
Lemma F_9df00 : fetch_word SEGS (0x9ec2c : word) = Some W_9df00.
Proof. vm_refl. Qed.
Lemma D_9df00 : decode_any W_9df00 = Some (OpImm ALU_ADD 15 0 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df04 : bv 32 := 0x0087581b.
Lemma F_9df04 : fetch_word SEGS (0x9ec30 : word) = Some W_9df04.
Proof. vm_refl. Qed.
Lemma D_9df04 : decode_any W_9df04 = Some (ShiftImm32 ALU_SRL 16 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df08 : bv 32 := 0xff45a883.
Lemma F_9df08 : fetch_word SEGS (0x9ec34 : word) = Some W_9df08.
Proof. vm_refl. Qed.
Lemma D_9df08 : decode_any W_9df08 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df0c : bv 32 := 0xff85a283.
Lemma F_9df0c : fetch_word SEGS (0x9ec38 : word) = Some W_9df0c.
Proof. vm_refl. Qed.
Lemma D_9df0c : decode_any W_9df0c = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df10 : bv 32 := 0xffc5a303.
Lemma F_9df10 : fetch_word SEGS (0x9ec3c : word) = Some W_9df10.
Proof. vm_refl. Qed.
Lemma D_9df10 : decode_any W_9df10 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df14 : bv 32 := 0x0005a703.
Lemma F_9df14 : fetch_word SEGS (0x9ec40 : word) = Some W_9df14.
Proof. vm_refl. Qed.
Lemma D_9df14 : decode_any W_9df14 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df18 : bv 32 := 0x01889393.
Lemma F_9df18 : fetch_word SEGS (0x9ec44 : word) = Some W_9df18.
Proof. vm_refl. Qed.
Lemma D_9df18 : decode_any W_9df18 = Some (ShiftImm ALU_SLL 7 17 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df1c : bv 32 := 0x0088d89b.
Lemma F_9df1c : fetch_word SEGS (0x9ec48 : word) = Some W_9df1c.
Proof. vm_refl. Qed.
Lemma D_9df1c : decode_any W_9df1c = Some (ShiftImm32 ALU_SRL 17 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df20 : bv 32 := 0x0103e833.
Lemma F_9df20 : fetch_word SEGS (0x9ec4c : word) = Some W_9df20.
Proof. vm_refl. Qed.
Lemma D_9df20 : decode_any W_9df20 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df24 : bv 32 := 0x01829393.
Lemma F_9df24 : fetch_word SEGS (0x9ec50 : word) = Some W_9df24.
Proof. vm_refl. Qed.
Lemma D_9df24 : decode_any W_9df24 = Some (ShiftImm ALU_SLL 7 5 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df28 : bv 32 := 0x0082d29b.
Lemma F_9df28 : fetch_word SEGS (0x9ec54 : word) = Some W_9df28.
Proof. vm_refl. Qed.
Lemma D_9df28 : decode_any W_9df28 = Some (ShiftImm32 ALU_SRL 5 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df2c : bv 32 := 0x0113e8b3.
Lemma F_9df2c : fetch_word SEGS (0x9ec58 : word) = Some W_9df2c.
Proof. vm_refl. Qed.
Lemma D_9df2c : decode_any W_9df2c = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df30 : bv 32 := 0x01831393.
Lemma F_9df30 : fetch_word SEGS (0x9ec5c : word) = Some W_9df30.
Proof. vm_refl. Qed.
Lemma D_9df30 : decode_any W_9df30 = Some (ShiftImm ALU_SLL 7 6 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df34 : bv 32 := 0x0083531b.
Lemma F_9df34 : fetch_word SEGS (0x9ec60 : word) = Some W_9df34.
Proof. vm_refl. Qed.
Lemma D_9df34 : decode_any W_9df34 = Some (ShiftImm32 ALU_SRL 6 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df38 : bv 32 := 0x0053e2b3.
Lemma F_9df38 : fetch_word SEGS (0x9ec64 : word) = Some W_9df38.
Proof. vm_refl. Qed.
Lemma D_9df38 : decode_any W_9df38 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df3c : bv 32 := 0x01871393.
Lemma F_9df3c : fetch_word SEGS (0x9ec68 : word) = Some W_9df3c.
Proof. vm_refl. Qed.
Lemma D_9df3c : decode_any W_9df3c = Some (ShiftImm ALU_SLL 7 14 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df40 : bv 32 := 0x0063e333.
Lemma F_9df40 : fetch_word SEGS (0x9ec6c : word) = Some W_9df40.
Proof. vm_refl. Qed.
Lemma D_9df40 : decode_any W_9df40 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df44 : bv 32 := 0xff060613.
Lemma F_9df44 : fetch_word SEGS (0x9ec70 : word) = Some W_9df44.
Proof. vm_refl. Qed.
Lemma D_9df44 : decode_any W_9df44 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df48 : bv 32 := 0x0106a023.
Lemma F_9df48 : fetch_word SEGS (0x9ec74 : word) = Some W_9df48.
Proof. vm_refl. Qed.
Lemma D_9df48 : decode_any W_9df48 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df4c : bv 32 := 0x0116a223.
Lemma F_9df4c : fetch_word SEGS (0x9ec78 : word) = Some W_9df4c.
Proof. vm_refl. Qed.
Lemma D_9df4c : decode_any W_9df4c = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df50 : bv 32 := 0x0056a423.
Lemma F_9df50 : fetch_word SEGS (0x9ec7c : word) = Some W_9df50.
Proof. vm_refl. Qed.
Lemma D_9df50 : decode_any W_9df50 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df54 : bv 32 := 0x0066a623.
Lemma F_9df54 : fetch_word SEGS (0x9ec80 : word) = Some W_9df54.
Proof. vm_refl. Qed.
Lemma D_9df54 : decode_any W_9df54 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df58 : bv 32 := 0x01068693.
Lemma F_9df58 : fetch_word SEGS (0x9ec84 : word) = Some W_9df58.
Proof. vm_refl. Qed.
Lemma D_9df58 : decode_any W_9df58 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df5c : bv 32 := 0x01058593.
Lemma F_9df5c : fetch_word SEGS (0x9ec88 : word) = Some W_9df5c.
Proof. vm_refl. Qed.
Lemma D_9df5c : decode_any W_9df5c = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df60 : bv 32 := 0xfac7e2e3.
Lemma F_9df60 : fetch_word SEGS (0x9ec8c : word) = Some W_9df60.
Proof. vm_refl. Qed.
Lemma D_9df60 : decode_any W_9df60 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df64 : bv 32 := 0xff158593.
Lemma F_9df64 : fetch_word SEGS (0x9ec90 : word) = Some W_9df64.
Proof. vm_refl. Qed.
Lemma D_9df64 : decode_any W_9df64 = Some (OpImm ALU_ADD 11 11 4081, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df68 : bv 32 := 0x01000713.
Lemma F_9df68 : fetch_word SEGS (0x9ec94 : word) = Some W_9df68.
Proof. vm_refl. Qed.
Lemma D_9df68 : decode_any W_9df68 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df6c : bv 32 := 0xe4e666e3.
Lemma F_9df6c : fetch_word SEGS (0x9ec98 : word) = Some W_9df6c.
Proof. vm_refl. Qed.
Lemma D_9df6c : decode_any W_9df6c = Some (Branch BC_LTU 12 14 7756, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df70 : bv 32 := 0x0940006f.
Lemma F_9df70 : fetch_word SEGS (0x9ec9c : word) = Some W_9df70.
Proof. vm_refl. Qed.
Lemma D_9df70 : decode_any W_9df70 = Some (Jal 0 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df74 : bv 32 := 0x00875793.
Lemma F_9df74 : fetch_word SEGS (0x9eca0 : word) = Some W_9df74.
Proof. vm_refl. Qed.
Lemma D_9df74 : decode_any W_9df74 = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df78 : bv 32 := 0x01075813.
Lemma F_9df78 : fetch_word SEGS (0x9eca4 : word) = Some W_9df78.
Proof. vm_refl. Qed.
Lemma D_9df78 : decode_any W_9df78 = Some (ShiftImm ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df7c : bv 32 := 0xffd60613.
Lemma F_9df7c : fetch_word SEGS (0x9eca8 : word) = Some W_9df7c.
Proof. vm_refl. Qed.
Lemma D_9df7c : decode_any W_9df7c = Some (OpImm ALU_ADD 12 12 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df80 : bv 32 := 0x00e68023.
Lemma F_9df80 : fetch_word SEGS (0x9ecac : word) = Some W_9df80.
Proof. vm_refl. Qed.
Lemma D_9df80 : decode_any W_9df80 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df84 : bv 32 := 0x00f680a3.
Lemma F_9df84 : fetch_word SEGS (0x9ecb0 : word) = Some W_9df84.
Proof. vm_refl. Qed.
Lemma D_9df84 : decode_any W_9df84 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df88 : bv 32 := 0x01068123.
Lemma F_9df88 : fetch_word SEGS (0x9ecb4 : word) = Some W_9df88.
Proof. vm_refl. Qed.
Lemma D_9df88 : decode_any W_9df88 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df8c : bv 32 := 0x00368693.
Lemma F_9df8c : fetch_word SEGS (0x9ecb8 : word) = Some W_9df8c.
Proof. vm_refl. Qed.
Lemma D_9df8c : decode_any W_9df8c = Some (OpImm ALU_ADD 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df90 : bv 32 := 0x01058593.
Lemma F_9df90 : fetch_word SEGS (0x9ecbc : word) = Some W_9df90.
Proof. vm_refl. Qed.
Lemma D_9df90 : decode_any W_9df90 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df94 : bv 32 := 0x01000793.
Lemma F_9df94 : fetch_word SEGS (0x9ecc0 : word) = Some W_9df94.
Proof. vm_refl. Qed.
Lemma D_9df94 : decode_any W_9df94 = Some (OpImm ALU_ADD 15 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df98 : bv 32 := 0x0187581b.
Lemma F_9df98 : fetch_word SEGS (0x9ecc4 : word) = Some W_9df98.
Proof. vm_refl. Qed.
Lemma D_9df98 : decode_any W_9df98 = Some (ShiftImm32 ALU_SRL 16 14 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9df9c : bv 32 := 0xff45a883.
Lemma F_9df9c : fetch_word SEGS (0x9ecc8 : word) = Some W_9df9c.
Proof. vm_refl. Qed.
Lemma D_9df9c : decode_any W_9df9c = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dfa0 : bv 32 := 0xff85a283.
Lemma F_9dfa0 : fetch_word SEGS (0x9eccc : word) = Some W_9dfa0.
Proof. vm_refl. Qed.
Lemma D_9dfa0 : decode_any W_9dfa0 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dfa4 : bv 32 := 0xffc5a303.
Lemma F_9dfa4 : fetch_word SEGS (0x9ecd0 : word) = Some W_9dfa4.
Proof. vm_refl. Qed.
Lemma D_9dfa4 : decode_any W_9dfa4 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dfa8 : bv 32 := 0x0005a703.
Lemma F_9dfa8 : fetch_word SEGS (0x9ecd4 : word) = Some W_9dfa8.
Proof. vm_refl. Qed.
Lemma D_9dfa8 : decode_any W_9dfa8 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dfac : bv 32 := 0x00889393.
Lemma F_9dfac : fetch_word SEGS (0x9ecd8 : word) = Some W_9dfac.
Proof. vm_refl. Qed.
Lemma D_9dfac : decode_any W_9dfac = Some (ShiftImm ALU_SLL 7 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dfb0 : bv 32 := 0x0188d89b.
Lemma F_9dfb0 : fetch_word SEGS (0x9ecdc : word) = Some W_9dfb0.
Proof. vm_refl. Qed.
Lemma D_9dfb0 : decode_any W_9dfb0 = Some (ShiftImm32 ALU_SRL 17 17 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dfb4 : bv 32 := 0x0103e833.
Lemma F_9dfb4 : fetch_word SEGS (0x9ece0 : word) = Some W_9dfb4.
Proof. vm_refl. Qed.
Lemma D_9dfb4 : decode_any W_9dfb4 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dfb8 : bv 32 := 0x00829393.
Lemma F_9dfb8 : fetch_word SEGS (0x9ece4 : word) = Some W_9dfb8.
Proof. vm_refl. Qed.
Lemma D_9dfb8 : decode_any W_9dfb8 = Some (ShiftImm ALU_SLL 7 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dfbc : bv 32 := 0x0182d29b.
Lemma F_9dfbc : fetch_word SEGS (0x9ece8 : word) = Some W_9dfbc.
Proof. vm_refl. Qed.
Lemma D_9dfbc : decode_any W_9dfbc = Some (ShiftImm32 ALU_SRL 5 5 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dfc0 : bv 32 := 0x0113e8b3.
Lemma F_9dfc0 : fetch_word SEGS (0x9ecec : word) = Some W_9dfc0.
Proof. vm_refl. Qed.
Lemma D_9dfc0 : decode_any W_9dfc0 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dfc4 : bv 32 := 0x00831393.
Lemma F_9dfc4 : fetch_word SEGS (0x9ecf0 : word) = Some W_9dfc4.
Proof. vm_refl. Qed.
Lemma D_9dfc4 : decode_any W_9dfc4 = Some (ShiftImm ALU_SLL 7 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dfc8 : bv 32 := 0x0183531b.
Lemma F_9dfc8 : fetch_word SEGS (0x9ecf4 : word) = Some W_9dfc8.
Proof. vm_refl. Qed.
Lemma D_9dfc8 : decode_any W_9dfc8 = Some (ShiftImm32 ALU_SRL 6 6 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dfcc : bv 32 := 0x0053e2b3.
Lemma F_9dfcc : fetch_word SEGS (0x9ecf8 : word) = Some W_9dfcc.
Proof. vm_refl. Qed.
Lemma D_9dfcc : decode_any W_9dfcc = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dfd0 : bv 32 := 0x00871393.
Lemma F_9dfd0 : fetch_word SEGS (0x9ecfc : word) = Some W_9dfd0.
Proof. vm_refl. Qed.
Lemma D_9dfd0 : decode_any W_9dfd0 = Some (ShiftImm ALU_SLL 7 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dfd4 : bv 32 := 0x0063e333.
Lemma F_9dfd4 : fetch_word SEGS (0x9ed00 : word) = Some W_9dfd4.
Proof. vm_refl. Qed.
Lemma D_9dfd4 : decode_any W_9dfd4 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dfd8 : bv 32 := 0xff060613.
Lemma F_9dfd8 : fetch_word SEGS (0x9ed04 : word) = Some W_9dfd8.
Proof. vm_refl. Qed.
Lemma D_9dfd8 : decode_any W_9dfd8 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dfdc : bv 32 := 0x0106a023.
Lemma F_9dfdc : fetch_word SEGS (0x9ed08 : word) = Some W_9dfdc.
Proof. vm_refl. Qed.
Lemma D_9dfdc : decode_any W_9dfdc = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dfe0 : bv 32 := 0x0116a223.
Lemma F_9dfe0 : fetch_word SEGS (0x9ed0c : word) = Some W_9dfe0.
Proof. vm_refl. Qed.
Lemma D_9dfe0 : decode_any W_9dfe0 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dfe4 : bv 32 := 0x0056a423.
Lemma F_9dfe4 : fetch_word SEGS (0x9ed10 : word) = Some W_9dfe4.
Proof. vm_refl. Qed.
Lemma D_9dfe4 : decode_any W_9dfe4 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dfe8 : bv 32 := 0x0066a623.
Lemma F_9dfe8 : fetch_word SEGS (0x9ed14 : word) = Some W_9dfe8.
Proof. vm_refl. Qed.
Lemma D_9dfe8 : decode_any W_9dfe8 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dfec : bv 32 := 0x01068693.
Lemma F_9dfec : fetch_word SEGS (0x9ed18 : word) = Some W_9dfec.
Proof. vm_refl. Qed.
Lemma D_9dfec : decode_any W_9dfec = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dff0 : bv 32 := 0x01058593.
Lemma F_9dff0 : fetch_word SEGS (0x9ed1c : word) = Some W_9dff0.
Proof. vm_refl. Qed.
Lemma D_9dff0 : decode_any W_9dff0 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dff4 : bv 32 := 0xfac7e2e3.
Lemma F_9dff4 : fetch_word SEGS (0x9ed20 : word) = Some W_9dff4.
Proof. vm_refl. Qed.
Lemma D_9dff4 : decode_any W_9dff4 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dff8 : bv 32 := 0xff358593.
Lemma F_9dff8 : fetch_word SEGS (0x9ed24 : word) = Some W_9dff8.
Proof. vm_refl. Qed.
Lemma D_9dff8 : decode_any W_9dff8 = Some (OpImm ALU_ADD 11 11 4083, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9dffc : bv 32 := 0x01000713.
Lemma F_9dffc : fetch_word SEGS (0x9ed28 : word) = Some W_9dffc.
Proof. vm_refl. Qed.
Lemma D_9dffc : decode_any W_9dffc = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e000 : bv 32 := 0xdae66ce3.
Lemma F_9e000 : fetch_word SEGS (0x9ed2c : word) = Some W_9e000.
Proof. vm_refl. Qed.
Lemma D_9e000 : decode_any W_9e000 = Some (Branch BC_LTU 12 14 7608, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e004 : bv 32 := 0x0005c703.
Lemma F_9e004 : fetch_word SEGS (0x9ed30 : word) = Some W_9e004.
Proof. vm_refl. Qed.
Lemma D_9e004 : decode_any W_9e004 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e008 : bv 32 := 0x0015c783.
Lemma F_9e008 : fetch_word SEGS (0x9ed34 : word) = Some W_9e008.
Proof. vm_refl. Qed.
Lemma D_9e008 : decode_any W_9e008 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e00c : bv 32 := 0x0025c803.
Lemma F_9e00c : fetch_word SEGS (0x9ed38 : word) = Some W_9e00c.
Proof. vm_refl. Qed.
Lemma D_9e00c : decode_any W_9e00c = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e010 : bv 32 := 0x0035c883.
Lemma F_9e010 : fetch_word SEGS (0x9ed3c : word) = Some W_9e010.
Proof. vm_refl. Qed.
Lemma D_9e010 : decode_any W_9e010 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e014 : bv 32 := 0x0045c283.
Lemma F_9e014 : fetch_word SEGS (0x9ed40 : word) = Some W_9e014.
Proof. vm_refl. Qed.
Lemma D_9e014 : decode_any W_9e014 = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e018 : bv 32 := 0x0055c303.
Lemma F_9e018 : fetch_word SEGS (0x9ed44 : word) = Some W_9e018.
Proof. vm_refl. Qed.
Lemma D_9e018 : decode_any W_9e018 = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e01c : bv 32 := 0x0065c383.
Lemma F_9e01c : fetch_word SEGS (0x9ed48 : word) = Some W_9e01c.
Proof. vm_refl. Qed.
Lemma D_9e01c : decode_any W_9e01c = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e020 : bv 32 := 0x0075ce03.
Lemma F_9e020 : fetch_word SEGS (0x9ed4c : word) = Some W_9e020.
Proof. vm_refl. Qed.
Lemma D_9e020 : decode_any W_9e020 = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e024 : bv 32 := 0x00e68023.
Lemma F_9e024 : fetch_word SEGS (0x9ed50 : word) = Some W_9e024.
Proof. vm_refl. Qed.
Lemma D_9e024 : decode_any W_9e024 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e028 : bv 32 := 0x00f680a3.
Lemma F_9e028 : fetch_word SEGS (0x9ed54 : word) = Some W_9e028.
Proof. vm_refl. Qed.
Lemma D_9e028 : decode_any W_9e028 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e02c : bv 32 := 0x01068123.
Lemma F_9e02c : fetch_word SEGS (0x9ed58 : word) = Some W_9e02c.
Proof. vm_refl. Qed.
Lemma D_9e02c : decode_any W_9e02c = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e030 : bv 32 := 0x011681a3.
Lemma F_9e030 : fetch_word SEGS (0x9ed5c : word) = Some W_9e030.
Proof. vm_refl. Qed.
Lemma D_9e030 : decode_any W_9e030 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e034 : bv 32 := 0x0085c703.
Lemma F_9e034 : fetch_word SEGS (0x9ed60 : word) = Some W_9e034.
Proof. vm_refl. Qed.
Lemma D_9e034 : decode_any W_9e034 = Some (Load SZ1 false 14 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e038 : bv 32 := 0x0095c783.
Lemma F_9e038 : fetch_word SEGS (0x9ed64 : word) = Some W_9e038.
Proof. vm_refl. Qed.
Lemma D_9e038 : decode_any W_9e038 = Some (Load SZ1 false 15 11 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e03c : bv 32 := 0x00a5c803.
Lemma F_9e03c : fetch_word SEGS (0x9ed68 : word) = Some W_9e03c.
Proof. vm_refl. Qed.
Lemma D_9e03c : decode_any W_9e03c = Some (Load SZ1 false 16 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e040 : bv 32 := 0x00b5c883.
Lemma F_9e040 : fetch_word SEGS (0x9ed6c : word) = Some W_9e040.
Proof. vm_refl. Qed.
Lemma D_9e040 : decode_any W_9e040 = Some (Load SZ1 false 17 11 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e044 : bv 32 := 0x00568223.
Lemma F_9e044 : fetch_word SEGS (0x9ed70 : word) = Some W_9e044.
Proof. vm_refl. Qed.
Lemma D_9e044 : decode_any W_9e044 = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e048 : bv 32 := 0x006682a3.
Lemma F_9e048 : fetch_word SEGS (0x9ed74 : word) = Some W_9e048.
Proof. vm_refl. Qed.
Lemma D_9e048 : decode_any W_9e048 = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e04c : bv 32 := 0x00768323.
Lemma F_9e04c : fetch_word SEGS (0x9ed78 : word) = Some W_9e04c.
Proof. vm_refl. Qed.
Lemma D_9e04c : decode_any W_9e04c = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e050 : bv 32 := 0x01c683a3.
Lemma F_9e050 : fetch_word SEGS (0x9ed7c : word) = Some W_9e050.
Proof. vm_refl. Qed.
Lemma D_9e050 : decode_any W_9e050 = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e054 : bv 32 := 0x00c5c283.
Lemma F_9e054 : fetch_word SEGS (0x9ed80 : word) = Some W_9e054.
Proof. vm_refl. Qed.
Lemma D_9e054 : decode_any W_9e054 = Some (Load SZ1 false 5 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e058 : bv 32 := 0x00d5c303.
Lemma F_9e058 : fetch_word SEGS (0x9ed84 : word) = Some W_9e058.
Proof. vm_refl. Qed.
Lemma D_9e058 : decode_any W_9e058 = Some (Load SZ1 false 6 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e05c : bv 32 := 0x00e5c383.
Lemma F_9e05c : fetch_word SEGS (0x9ed88 : word) = Some W_9e05c.
Proof. vm_refl. Qed.
Lemma D_9e05c : decode_any W_9e05c = Some (Load SZ1 false 7 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e060 : bv 32 := 0x00f5ce03.
Lemma F_9e060 : fetch_word SEGS (0x9ed8c : word) = Some W_9e060.
Proof. vm_refl. Qed.
Lemma D_9e060 : decode_any W_9e060 = Some (Load SZ1 false 28 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e064 : bv 32 := 0x01058593.
Lemma F_9e064 : fetch_word SEGS (0x9ed90 : word) = Some W_9e064.
Proof. vm_refl. Qed.
Lemma D_9e064 : decode_any W_9e064 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e068 : bv 32 := 0x00e68423.
Lemma F_9e068 : fetch_word SEGS (0x9ed94 : word) = Some W_9e068.
Proof. vm_refl. Qed.
Lemma D_9e068 : decode_any W_9e068 = Some (Store SZ1 13 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e06c : bv 32 := 0x00f684a3.
Lemma F_9e06c : fetch_word SEGS (0x9ed98 : word) = Some W_9e06c.
Proof. vm_refl. Qed.
Lemma D_9e06c : decode_any W_9e06c = Some (Store SZ1 13 15 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e070 : bv 32 := 0x01068523.
Lemma F_9e070 : fetch_word SEGS (0x9ed9c : word) = Some W_9e070.
Proof. vm_refl. Qed.
Lemma D_9e070 : decode_any W_9e070 = Some (Store SZ1 13 16 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e074 : bv 32 := 0x011685a3.
Lemma F_9e074 : fetch_word SEGS (0x9eda0 : word) = Some W_9e074.
Proof. vm_refl. Qed.
Lemma D_9e074 : decode_any W_9e074 = Some (Store SZ1 13 17 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e078 : bv 32 := 0x01068713.
Lemma F_9e078 : fetch_word SEGS (0x9eda4 : word) = Some W_9e078.
Proof. vm_refl. Qed.
Lemma D_9e078 : decode_any W_9e078 = Some (OpImm ALU_ADD 14 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e07c : bv 32 := 0x00568623.
Lemma F_9e07c : fetch_word SEGS (0x9eda8 : word) = Some W_9e07c.
Proof. vm_refl. Qed.
Lemma D_9e07c : decode_any W_9e07c = Some (Store SZ1 13 5 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e080 : bv 32 := 0x006686a3.
Lemma F_9e080 : fetch_word SEGS (0x9edac : word) = Some W_9e080.
Proof. vm_refl. Qed.
Lemma D_9e080 : decode_any W_9e080 = Some (Store SZ1 13 6 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e084 : bv 32 := 0x00768723.
Lemma F_9e084 : fetch_word SEGS (0x9edb0 : word) = Some W_9e084.
Proof. vm_refl. Qed.
Lemma D_9e084 : decode_any W_9e084 = Some (Store SZ1 13 7 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e088 : bv 32 := 0x01c687a3.
Lemma F_9e088 : fetch_word SEGS (0x9edb4 : word) = Some W_9e088.
Proof. vm_refl. Qed.
Lemma D_9e088 : decode_any W_9e088 = Some (Store SZ1 13 28 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e08c : bv 32 := 0x00070693.
Lemma F_9e08c : fetch_word SEGS (0x9edb8 : word) = Some W_9e08c.
Proof. vm_refl. Qed.
Lemma D_9e08c : decode_any W_9e08c = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e090 : bv 32 := 0x00867713.
Lemma F_9e090 : fetch_word SEGS (0x9edbc : word) = Some W_9e090.
Proof. vm_refl. Qed.
Lemma D_9e090 : decode_any W_9e090 = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e094 : bv 32 := 0xd20706e3.
Lemma F_9e094 : fetch_word SEGS (0x9edc0 : word) = Some W_9e094.
Proof. vm_refl. Qed.
Lemma D_9e094 : decode_any W_9e094 = Some (Branch BC_EQ 14 0 7468, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e098 : bv 32 := 0x0005c703.
Lemma F_9e098 : fetch_word SEGS (0x9edc4 : word) = Some W_9e098.
Proof. vm_refl. Qed.
Lemma D_9e098 : decode_any W_9e098 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e09c : bv 32 := 0x0015c783.
Lemma F_9e09c : fetch_word SEGS (0x9edc8 : word) = Some W_9e09c.
Proof. vm_refl. Qed.
Lemma D_9e09c : decode_any W_9e09c = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e0a0 : bv 32 := 0x0025c803.
Lemma F_9e0a0 : fetch_word SEGS (0x9edcc : word) = Some W_9e0a0.
Proof. vm_refl. Qed.
Lemma D_9e0a0 : decode_any W_9e0a0 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e0a4 : bv 32 := 0x0035c883.
Lemma F_9e0a4 : fetch_word SEGS (0x9edd0 : word) = Some W_9e0a4.
Proof. vm_refl. Qed.
Lemma D_9e0a4 : decode_any W_9e0a4 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e0a8 : bv 32 := 0x0045c283.
Lemma F_9e0a8 : fetch_word SEGS (0x9edd4 : word) = Some W_9e0a8.
Proof. vm_refl. Qed.
Lemma D_9e0a8 : decode_any W_9e0a8 = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e0ac : bv 32 := 0x0055c303.
Lemma F_9e0ac : fetch_word SEGS (0x9edd8 : word) = Some W_9e0ac.
Proof. vm_refl. Qed.
Lemma D_9e0ac : decode_any W_9e0ac = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e0b0 : bv 32 := 0x0065c383.
Lemma F_9e0b0 : fetch_word SEGS (0x9eddc : word) = Some W_9e0b0.
Proof. vm_refl. Qed.
Lemma D_9e0b0 : decode_any W_9e0b0 = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e0b4 : bv 32 := 0x0075ce03.
Lemma F_9e0b4 : fetch_word SEGS (0x9ede0 : word) = Some W_9e0b4.
Proof. vm_refl. Qed.
Lemma D_9e0b4 : decode_any W_9e0b4 = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e0b8 : bv 32 := 0x00858593.
Lemma F_9e0b8 : fetch_word SEGS (0x9ede4 : word) = Some W_9e0b8.
Proof. vm_refl. Qed.
Lemma D_9e0b8 : decode_any W_9e0b8 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e0bc : bv 32 := 0x00e68023.
Lemma F_9e0bc : fetch_word SEGS (0x9ede8 : word) = Some W_9e0bc.
Proof. vm_refl. Qed.
Lemma D_9e0bc : decode_any W_9e0bc = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e0c0 : bv 32 := 0x00f680a3.
Lemma F_9e0c0 : fetch_word SEGS (0x9edec : word) = Some W_9e0c0.
Proof. vm_refl. Qed.
Lemma D_9e0c0 : decode_any W_9e0c0 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e0c4 : bv 32 := 0x01068123.
Lemma F_9e0c4 : fetch_word SEGS (0x9edf0 : word) = Some W_9e0c4.
Proof. vm_refl. Qed.
Lemma D_9e0c4 : decode_any W_9e0c4 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e0c8 : bv 32 := 0x011681a3.
Lemma F_9e0c8 : fetch_word SEGS (0x9edf4 : word) = Some W_9e0c8.
Proof. vm_refl. Qed.
Lemma D_9e0c8 : decode_any W_9e0c8 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e0cc : bv 32 := 0x00868713.
Lemma F_9e0cc : fetch_word SEGS (0x9edf8 : word) = Some W_9e0cc.
Proof. vm_refl. Qed.
Lemma D_9e0cc : decode_any W_9e0cc = Some (OpImm ALU_ADD 14 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e0d0 : bv 32 := 0x00568223.
Lemma F_9e0d0 : fetch_word SEGS (0x9edfc : word) = Some W_9e0d0.
Proof. vm_refl. Qed.
Lemma D_9e0d0 : decode_any W_9e0d0 = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e0d4 : bv 32 := 0x006682a3.
Lemma F_9e0d4 : fetch_word SEGS (0x9ee00 : word) = Some W_9e0d4.
Proof. vm_refl. Qed.
Lemma D_9e0d4 : decode_any W_9e0d4 = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e0d8 : bv 32 := 0x00768323.
Lemma F_9e0d8 : fetch_word SEGS (0x9ee04 : word) = Some W_9e0d8.
Proof. vm_refl. Qed.
Lemma D_9e0d8 : decode_any W_9e0d8 = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e0dc : bv 32 := 0x01c683a3.
Lemma F_9e0dc : fetch_word SEGS (0x9ee08 : word) = Some W_9e0dc.
Proof. vm_refl. Qed.
Lemma D_9e0dc : decode_any W_9e0dc = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e0e0 : bv 32 := 0x00070693.
Lemma F_9e0e0 : fetch_word SEGS (0x9ee0c : word) = Some W_9e0e0.
Proof. vm_refl. Qed.
Lemma D_9e0e0 : decode_any W_9e0e0 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e0e4 : bv 32 := 0x00467713.
Lemma F_9e0e4 : fetch_word SEGS (0x9ee10 : word) = Some W_9e0e4.
Proof. vm_refl. Qed.
Lemma D_9e0e4 : decode_any W_9e0e4 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e0e8 : bv 32 := 0x02070863.
Lemma F_9e0e8 : fetch_word SEGS (0x9ee14 : word) = Some W_9e0e8.
Proof. vm_refl. Qed.
Lemma D_9e0e8 : decode_any W_9e0e8 = Some (Branch BC_EQ 14 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e0ec : bv 32 := 0x0005c703.
Lemma F_9e0ec : fetch_word SEGS (0x9ee18 : word) = Some W_9e0ec.
Proof. vm_refl. Qed.
Lemma D_9e0ec : decode_any W_9e0ec = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e0f0 : bv 32 := 0x0015c783.
Lemma F_9e0f0 : fetch_word SEGS (0x9ee1c : word) = Some W_9e0f0.
Proof. vm_refl. Qed.
Lemma D_9e0f0 : decode_any W_9e0f0 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e0f4 : bv 32 := 0x0025c803.
Lemma F_9e0f4 : fetch_word SEGS (0x9ee20 : word) = Some W_9e0f4.
Proof. vm_refl. Qed.
Lemma D_9e0f4 : decode_any W_9e0f4 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e0f8 : bv 32 := 0x0035c883.
Lemma F_9e0f8 : fetch_word SEGS (0x9ee24 : word) = Some W_9e0f8.
Proof. vm_refl. Qed.
Lemma D_9e0f8 : decode_any W_9e0f8 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e0fc : bv 32 := 0x00458593.
Lemma F_9e0fc : fetch_word SEGS (0x9ee28 : word) = Some W_9e0fc.
Proof. vm_refl. Qed.
Lemma D_9e0fc : decode_any W_9e0fc = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e100 : bv 32 := 0x00468293.
Lemma F_9e100 : fetch_word SEGS (0x9ee2c : word) = Some W_9e100.
Proof. vm_refl. Qed.
Lemma D_9e100 : decode_any W_9e100 = Some (OpImm ALU_ADD 5 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e104 : bv 32 := 0x00e68023.
Lemma F_9e104 : fetch_word SEGS (0x9ee30 : word) = Some W_9e104.
Proof. vm_refl. Qed.
Lemma D_9e104 : decode_any W_9e104 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e108 : bv 32 := 0x00f680a3.
Lemma F_9e108 : fetch_word SEGS (0x9ee34 : word) = Some W_9e108.
Proof. vm_refl. Qed.
Lemma D_9e108 : decode_any W_9e108 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e10c : bv 32 := 0x01068123.
Lemma F_9e10c : fetch_word SEGS (0x9ee38 : word) = Some W_9e10c.
Proof. vm_refl. Qed.
Lemma D_9e10c : decode_any W_9e10c = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e110 : bv 32 := 0x011681a3.
Lemma F_9e110 : fetch_word SEGS (0x9ee3c : word) = Some W_9e110.
Proof. vm_refl. Qed.
Lemma D_9e110 : decode_any W_9e110 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e114 : bv 32 := 0x00028693.
Lemma F_9e114 : fetch_word SEGS (0x9ee40 : word) = Some W_9e114.
Proof. vm_refl. Qed.
Lemma D_9e114 : decode_any W_9e114 = Some (OpImm ALU_ADD 13 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e118 : bv 32 := 0x00267713.
Lemma F_9e118 : fetch_word SEGS (0x9ee44 : word) = Some W_9e118.
Proof. vm_refl. Qed.
Lemma D_9e118 : decode_any W_9e118 = Some (OpImm ALU_AND 14 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e11c : bv 32 := 0x00071863.
Lemma F_9e11c : fetch_word SEGS (0x9ee48 : word) = Some W_9e11c.
Proof. vm_refl. Qed.
Lemma D_9e11c : decode_any W_9e11c = Some (Branch BC_NE 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e120 : bv 32 := 0x00167613.
Lemma F_9e120 : fetch_word SEGS (0x9ee4c : word) = Some W_9e120.
Proof. vm_refl. Qed.
Lemma D_9e120 : decode_any W_9e120 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e124 : bv 32 := 0x02061663.
Lemma F_9e124 : fetch_word SEGS (0x9ee50 : word) = Some W_9e124.
Proof. vm_refl. Qed.
Lemma D_9e124 : decode_any W_9e124 = Some (Branch BC_NE 12 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e128 : bv 32 := 0x00008067.
Lemma F_9e128 : fetch_word SEGS (0x9ee54 : word) = Some W_9e128.
Proof. vm_refl. Qed.
Lemma D_9e128 : decode_any W_9e128 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e12c : bv 32 := 0x0005c703.
Lemma F_9e12c : fetch_word SEGS (0x9ee58 : word) = Some W_9e12c.
Proof. vm_refl. Qed.
Lemma D_9e12c : decode_any W_9e12c = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e130 : bv 32 := 0x0015c783.
Lemma F_9e130 : fetch_word SEGS (0x9ee5c : word) = Some W_9e130.
Proof. vm_refl. Qed.
Lemma D_9e130 : decode_any W_9e130 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e134 : bv 32 := 0x00258593.
Lemma F_9e134 : fetch_word SEGS (0x9ee60 : word) = Some W_9e134.
Proof. vm_refl. Qed.
Lemma D_9e134 : decode_any W_9e134 = Some (OpImm ALU_ADD 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e138 : bv 32 := 0x00268813.
Lemma F_9e138 : fetch_word SEGS (0x9ee64 : word) = Some W_9e138.
Proof. vm_refl. Qed.
Lemma D_9e138 : decode_any W_9e138 = Some (OpImm ALU_ADD 16 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e13c : bv 32 := 0x00e68023.
Lemma F_9e13c : fetch_word SEGS (0x9ee68 : word) = Some W_9e13c.
Proof. vm_refl. Qed.
Lemma D_9e13c : decode_any W_9e13c = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e140 : bv 32 := 0x00f680a3.
Lemma F_9e140 : fetch_word SEGS (0x9ee6c : word) = Some W_9e140.
Proof. vm_refl. Qed.
Lemma D_9e140 : decode_any W_9e140 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e144 : bv 32 := 0x00080693.
Lemma F_9e144 : fetch_word SEGS (0x9ee70 : word) = Some W_9e144.
Proof. vm_refl. Qed.
Lemma D_9e144 : decode_any W_9e144 = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e148 : bv 32 := 0x00167613.
Lemma F_9e148 : fetch_word SEGS (0x9ee74 : word) = Some W_9e148.
Proof. vm_refl. Qed.
Lemma D_9e148 : decode_any W_9e148 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e14c : bv 32 := 0xfc060ee3.
Lemma F_9e14c : fetch_word SEGS (0x9ee78 : word) = Some W_9e14c.
Proof. vm_refl. Qed.
Lemma D_9e14c : decode_any W_9e14c = Some (Branch BC_EQ 12 0 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e150 : bv 32 := 0x0005c583.
Lemma F_9e150 : fetch_word SEGS (0x9ee7c : word) = Some W_9e150.
Proof. vm_refl. Qed.
Lemma D_9e150 : decode_any W_9e150 = Some (Load SZ1 false 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e154 : bv 32 := 0x00b68023.
Lemma F_9e154 : fetch_word SEGS (0x9ee80 : word) = Some W_9e154.
Proof. vm_refl. Qed.
Lemma D_9e154 : decode_any W_9e154 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e158 : bv 32 := 0x00008067.
Lemma F_9e158 : fetch_word SEGS (0x9ee84 : word) = Some W_9e158.
Proof. vm_refl. Qed.
Lemma D_9e158 : decode_any W_9e158 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
End TwB.
End MuslMemcpy_code.

(* [comment removed for export] *)
Module MuslMemset_code.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require Import A3Img.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_9e15c : bv 32 := 0x0e060a63.
Lemma F_9e15c : fetch_word SEGS (0x9ead4 : word) = Some W_9e15c.
Proof. vm_refl. Qed.
Lemma D_9e15c : decode_any W_9e15c = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e160 : bv 32 := 0x00b50023.
Lemma F_9e160 : fetch_word SEGS (0x9ead8 : word) = Some W_9e160.
Proof. vm_refl. Qed.
Lemma D_9e160 : decode_any W_9e160 = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e164 : bv 32 := 0x00c506b3.
Lemma F_9e164 : fetch_word SEGS (0x9eadc : word) = Some W_9e164.
Proof. vm_refl. Qed.
Lemma D_9e164 : decode_any W_9e164 = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e168 : bv 32 := 0x00300713.
Lemma F_9e168 : fetch_word SEGS (0x9eae0 : word) = Some W_9e168.
Proof. vm_refl. Qed.
Lemma D_9e168 : decode_any W_9e168 = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e16c : bv 32 := 0xfeb68fa3.
Lemma F_9e16c : fetch_word SEGS (0x9eae4 : word) = Some W_9e16c.
Proof. vm_refl. Qed.
Lemma D_9e16c : decode_any W_9e16c = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e170 : bv 32 := 0x0ee66063.
Lemma F_9e170 : fetch_word SEGS (0x9eae8 : word) = Some W_9e170.
Proof. vm_refl. Qed.
Lemma D_9e170 : decode_any W_9e170 = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e174 : bv 32 := 0x00b500a3.
Lemma F_9e174 : fetch_word SEGS (0x9eaec : word) = Some W_9e174.
Proof. vm_refl. Qed.
Lemma D_9e174 : decode_any W_9e174 = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e178 : bv 32 := 0x00b50123.
Lemma F_9e178 : fetch_word SEGS (0x9eaf0 : word) = Some W_9e178.
Proof. vm_refl. Qed.
Lemma D_9e178 : decode_any W_9e178 = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e17c : bv 32 := 0x00700713.
Lemma F_9e17c : fetch_word SEGS (0x9eaf4 : word) = Some W_9e17c.
Proof. vm_refl. Qed.
Lemma D_9e17c : decode_any W_9e17c = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e180 : bv 32 := 0xfeb68ea3.
Lemma F_9e180 : fetch_word SEGS (0x9eaf8 : word) = Some W_9e180.
Proof. vm_refl. Qed.
Lemma D_9e180 : decode_any W_9e180 = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e184 : bv 32 := 0xfeb68f23.
Lemma F_9e184 : fetch_word SEGS (0x9eafc : word) = Some W_9e184.
Proof. vm_refl. Qed.
Lemma D_9e184 : decode_any W_9e184 = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e188 : bv 32 := 0x0ce66463.
Lemma F_9e188 : fetch_word SEGS (0x9eb00 : word) = Some W_9e188.
Proof. vm_refl. Qed.
Lemma D_9e188 : decode_any W_9e188 = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e18c : bv 32 := 0x00b501a3.
Lemma F_9e18c : fetch_word SEGS (0x9eb04 : word) = Some W_9e18c.
Proof. vm_refl. Qed.
Lemma D_9e18c : decode_any W_9e18c = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e190 : bv 32 := 0x00900793.
Lemma F_9e190 : fetch_word SEGS (0x9eb08 : word) = Some W_9e190.
Proof. vm_refl. Qed.
Lemma D_9e190 : decode_any W_9e190 = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e194 : bv 32 := 0xfeb68e23.
Lemma F_9e194 : fetch_word SEGS (0x9eb0c : word) = Some W_9e194.
Proof. vm_refl. Qed.
Lemma D_9e194 : decode_any W_9e194 = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e198 : bv 32 := 0x0af66c63.
Lemma F_9e198 : fetch_word SEGS (0x9eb10 : word) = Some W_9e198.
Proof. vm_refl. Qed.
Lemma D_9e198 : decode_any W_9e198 = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e19c : bv 32 := 0x40a006bb.
Lemma F_9e19c : fetch_word SEGS (0x9eb14 : word) = Some W_9e19c.
Proof. vm_refl. Qed.
Lemma D_9e19c : decode_any W_9e19c = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e1a0 : bv 32 := 0x03859813.
Lemma F_9e1a0 : fetch_word SEGS (0x9eb18 : word) = Some W_9e1a0.
Proof. vm_refl. Qed.
Lemma D_9e1a0 : decode_any W_9e1a0 = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e1a4 : bv 32 := 0x101015b7.
Lemma F_9e1a4 : fetch_word SEGS (0x9eb1c : word) = Some W_9e1a4.
Proof. vm_refl. Qed.
Lemma D_9e1a4 : decode_any W_9e1a4 = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e1a8 : bv 32 := 0x0036f693.
Lemma F_9e1a8 : fetch_word SEGS (0x9eb20 : word) = Some W_9e1a8.
Proof. vm_refl. Qed.
Lemma D_9e1a8 : decode_any W_9e1a8 = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e1ac : bv 32 := 0x00459713.
Lemma F_9e1ac : fetch_word SEGS (0x9eb24 : word) = Some W_9e1ac.
Proof. vm_refl. Qed.
Lemma D_9e1ac : decode_any W_9e1ac = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e1b0 : bv 32 := 0x40d60633.
Lemma F_9e1b0 : fetch_word SEGS (0x9eb28 : word) = Some W_9e1b0.
Proof. vm_refl. Qed.
Lemma D_9e1b0 : decode_any W_9e1b0 = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e1b4 : bv 32 := 0x00d505b3.
Lemma F_9e1b4 : fetch_word SEGS (0x9eb2c : word) = Some W_9e1b4.
Proof. vm_refl. Qed.
Lemma D_9e1b4 : decode_any W_9e1b4 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e1b8 : bv 32 := 0x10070693.
Lemma F_9e1b8 : fetch_word SEGS (0x9eb30 : word) = Some W_9e1b8.
Proof. vm_refl. Qed.
Lemma D_9e1b8 : decode_any W_9e1b8 = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e1bc : bv 32 := 0xffc67713.
Lemma F_9e1bc : fetch_word SEGS (0x9eb34 : word) = Some W_9e1bc.
Proof. vm_refl. Qed.
Lemma D_9e1bc : decode_any W_9e1bc = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e1c0 : bv 32 := 0x02d83633.
Lemma F_9e1c0 : fetch_word SEGS (0x9eb38 : word) = Some W_9e1c0.
Proof. vm_refl. Qed.
Lemma D_9e1c0 : decode_any W_9e1c0 = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e1c4 : bv 32 := 0x00c5a023.
Lemma F_9e1c4 : fetch_word SEGS (0x9eb3c : word) = Some W_9e1c4.
Proof. vm_refl. Qed.
Lemma D_9e1c4 : decode_any W_9e1c4 = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e1c8 : bv 32 := 0x00e586b3.
Lemma F_9e1c8 : fetch_word SEGS (0x9eb40 : word) = Some W_9e1c8.
Proof. vm_refl. Qed.
Lemma D_9e1c8 : decode_any W_9e1c8 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e1cc : bv 32 := 0xfec6ae23.
Lemma F_9e1cc : fetch_word SEGS (0x9eb44 : word) = Some W_9e1cc.
Proof. vm_refl. Qed.
Lemma D_9e1cc : decode_any W_9e1cc = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e1d0 : bv 32 := 0x08f76063.
Lemma F_9e1d0 : fetch_word SEGS (0x9eb48 : word) = Some W_9e1d0.
Proof. vm_refl. Qed.
Lemma D_9e1d0 : decode_any W_9e1d0 = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e1d4 : bv 32 := 0x00c5a223.
Lemma F_9e1d4 : fetch_word SEGS (0x9eb4c : word) = Some W_9e1d4.
Proof. vm_refl. Qed.
Lemma D_9e1d4 : decode_any W_9e1d4 = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e1d8 : bv 32 := 0x00c5a423.
Lemma F_9e1d8 : fetch_word SEGS (0x9eb50 : word) = Some W_9e1d8.
Proof. vm_refl. Qed.
Lemma D_9e1d8 : decode_any W_9e1d8 = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e1dc : bv 32 := 0x01900793.
Lemma F_9e1dc : fetch_word SEGS (0x9eb54 : word) = Some W_9e1dc.
Proof. vm_refl. Qed.
Lemma D_9e1dc : decode_any W_9e1dc = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e1e0 : bv 32 := 0xfec6aa23.
Lemma F_9e1e0 : fetch_word SEGS (0x9eb58 : word) = Some W_9e1e0.
Proof. vm_refl. Qed.
Lemma D_9e1e0 : decode_any W_9e1e0 = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e1e4 : bv 32 := 0xfec6ac23.
Lemma F_9e1e4 : fetch_word SEGS (0x9eb5c : word) = Some W_9e1e4.
Proof. vm_refl. Qed.
Lemma D_9e1e4 : decode_any W_9e1e4 = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e1e8 : bv 32 := 0x06f76463.
Lemma F_9e1e8 : fetch_word SEGS (0x9eb60 : word) = Some W_9e1e8.
Proof. vm_refl. Qed.
Lemma D_9e1e8 : decode_any W_9e1e8 = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e1ec : bv 32 := 0x00c5a623.
Lemma F_9e1ec : fetch_word SEGS (0x9eb64 : word) = Some W_9e1ec.
Proof. vm_refl. Qed.
Lemma D_9e1ec : decode_any W_9e1ec = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e1f0 : bv 32 := 0x00c5a823.
Lemma F_9e1f0 : fetch_word SEGS (0x9eb68 : word) = Some W_9e1f0.
Proof. vm_refl. Qed.
Lemma D_9e1f0 : decode_any W_9e1f0 = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e1f4 : bv 32 := 0x00c5aa23.
Lemma F_9e1f4 : fetch_word SEGS (0x9eb6c : word) = Some W_9e1f4.
Proof. vm_refl. Qed.
Lemma D_9e1f4 : decode_any W_9e1f4 = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e1f8 : bv 32 := 0x00c5ac23.
Lemma F_9e1f8 : fetch_word SEGS (0x9eb70 : word) = Some W_9e1f8.
Proof. vm_refl. Qed.
Lemma D_9e1f8 : decode_any W_9e1f8 = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e1fc : bv 32 := 0x0045f793.
Lemma F_9e1fc : fetch_word SEGS (0x9eb74 : word) = Some W_9e1fc.
Proof. vm_refl. Qed.
Lemma D_9e1fc : decode_any W_9e1fc = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e200 : bv 32 := 0x02000813.
Lemma F_9e200 : fetch_word SEGS (0x9eb78 : word) = Some W_9e200.
Proof. vm_refl. Qed.
Lemma D_9e200 : decode_any W_9e200 = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e204 : bv 32 := 0x01878793.
Lemma F_9e204 : fetch_word SEGS (0x9eb7c : word) = Some W_9e204.
Proof. vm_refl. Qed.
Lemma D_9e204 : decode_any W_9e204 = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e208 : bv 32 := 0x40f70733.
Lemma F_9e208 : fetch_word SEGS (0x9eb80 : word) = Some W_9e208.
Proof. vm_refl. Qed.
Lemma D_9e208 : decode_any W_9e208 = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e20c : bv 32 := 0xfec6a223.
Lemma F_9e20c : fetch_word SEGS (0x9eb84 : word) = Some W_9e20c.
Proof. vm_refl. Qed.
Lemma D_9e20c : decode_any W_9e20c = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e210 : bv 32 := 0xfec6a423.
Lemma F_9e210 : fetch_word SEGS (0x9eb88 : word) = Some W_9e210.
Proof. vm_refl. Qed.
Lemma D_9e210 : decode_any W_9e210 = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e214 : bv 32 := 0xfec6a623.
Lemma F_9e214 : fetch_word SEGS (0x9eb8c : word) = Some W_9e214.
Proof. vm_refl. Qed.
Lemma D_9e214 : decode_any W_9e214 = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e218 : bv 32 := 0xfec6a823.
Lemma F_9e218 : fetch_word SEGS (0x9eb90 : word) = Some W_9e218.
Proof. vm_refl. Qed.
Lemma D_9e218 : decode_any W_9e218 = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e21c : bv 32 := 0x03076a63.
Lemma F_9e21c : fetch_word SEGS (0x9eb94 : word) = Some W_9e21c.
Proof. vm_refl. Qed.
Lemma D_9e21c : decode_any W_9e21c = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e220 : bv 32 := 0x02061613.
Lemma F_9e220 : fetch_word SEGS (0x9eb98 : word) = Some W_9e220.
Proof. vm_refl. Qed.
Lemma D_9e220 : decode_any W_9e220 = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e224 : bv 32 := 0x00f585b3.
Lemma F_9e224 : fetch_word SEGS (0x9eb9c : word) = Some W_9e224.
Proof. vm_refl. Qed.
Lemma D_9e224 : decode_any W_9e224 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e228 : bv 32 := 0x02065693.
Lemma F_9e228 : fetch_word SEGS (0x9eba0 : word) = Some W_9e228.
Proof. vm_refl. Qed.
Lemma D_9e228 : decode_any W_9e228 = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e22c : bv 32 := 0x00d66633.
Lemma F_9e22c : fetch_word SEGS (0x9eba4 : word) = Some W_9e22c.
Proof. vm_refl. Qed.
Lemma D_9e22c : decode_any W_9e22c = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e230 : bv 32 := 0x01f00693.
Lemma F_9e230 : fetch_word SEGS (0x9eba8 : word) = Some W_9e230.
Proof. vm_refl. Qed.
Lemma D_9e230 : decode_any W_9e230 = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e234 : bv 32 := 0x00c5b023.
Lemma F_9e234 : fetch_word SEGS (0x9ebac : word) = Some W_9e234.
Proof. vm_refl. Qed.
Lemma D_9e234 : decode_any W_9e234 = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e238 : bv 32 := 0x00c5b423.
Lemma F_9e238 : fetch_word SEGS (0x9ebb0 : word) = Some W_9e238.
Proof. vm_refl. Qed.
Lemma D_9e238 : decode_any W_9e238 = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e23c : bv 32 := 0x00c5b823.
Lemma F_9e23c : fetch_word SEGS (0x9ebb4 : word) = Some W_9e23c.
Proof. vm_refl. Qed.
Lemma D_9e23c : decode_any W_9e23c = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e240 : bv 32 := 0x00c5bc23.
Lemma F_9e240 : fetch_word SEGS (0x9ebb8 : word) = Some W_9e240.
Proof. vm_refl. Qed.
Lemma D_9e240 : decode_any W_9e240 = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e244 : bv 32 := 0xfe070713.
Lemma F_9e244 : fetch_word SEGS (0x9ebbc : word) = Some W_9e244.
Proof. vm_refl. Qed.
Lemma D_9e244 : decode_any W_9e244 = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e248 : bv 32 := 0x02058593.
Lemma F_9e248 : fetch_word SEGS (0x9ebc0 : word) = Some W_9e248.
Proof. vm_refl. Qed.
Lemma D_9e248 : decode_any W_9e248 = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e24c : bv 32 := 0xfee6e4e3.
Lemma F_9e24c : fetch_word SEGS (0x9ebc4 : word) = Some W_9e24c.
Proof. vm_refl. Qed.
Lemma D_9e24c : decode_any W_9e24c = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e250 : bv 32 := 0x00008067.
Lemma F_9e250 : fetch_word SEGS (0x9ebc8 : word) = Some W_9e250.
Proof. vm_refl. Qed.
Lemma D_9e250 : decode_any W_9e250 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Abbreviation MSEGS := SEGS.
Definition ms_base : Z := 0x9ead4%Z.   (* [comment removed for export] *)
Definition Fo_000 := F_9e15c.
Definition Do_000 := D_9e15c.
Definition Fo_004 := F_9e160.
Definition Do_004 := D_9e160.
Definition Fo_008 := F_9e164.
Definition Do_008 := D_9e164.
Definition Fo_00c := F_9e168.
Definition Do_00c := D_9e168.
Definition Fo_010 := F_9e16c.
Definition Do_010 := D_9e16c.
Definition Fo_014 := F_9e170.
Definition Do_014 := D_9e170.
Definition Fo_018 := F_9e174.
Definition Do_018 := D_9e174.
Definition Fo_01c := F_9e178.
Definition Do_01c := D_9e178.
Definition Fo_020 := F_9e17c.
Definition Do_020 := D_9e17c.
Definition Fo_024 := F_9e180.
Definition Do_024 := D_9e180.
Definition Fo_028 := F_9e184.
Definition Do_028 := D_9e184.
Definition Fo_02c := F_9e188.
Definition Do_02c := D_9e188.
Definition Fo_030 := F_9e18c.
Definition Do_030 := D_9e18c.
Definition Fo_034 := F_9e190.
Definition Do_034 := D_9e190.
Definition Fo_038 := F_9e194.
Definition Do_038 := D_9e194.
Definition Fo_03c := F_9e198.
Definition Do_03c := D_9e198.
Definition Fo_040 := F_9e19c.
Definition Do_040 := D_9e19c.
Definition Fo_044 := F_9e1a0.
Definition Do_044 := D_9e1a0.
Definition Fo_048 := F_9e1a4.
Definition Do_048 := D_9e1a4.
Definition Fo_04c := F_9e1a8.
Definition Do_04c := D_9e1a8.
Definition Fo_050 := F_9e1ac.
Definition Do_050 := D_9e1ac.
Definition Fo_054 := F_9e1b0.
Definition Do_054 := D_9e1b0.
Definition Fo_058 := F_9e1b4.
Definition Do_058 := D_9e1b4.
Definition Fo_05c := F_9e1b8.
Definition Do_05c := D_9e1b8.
Definition Fo_060 := F_9e1bc.
Definition Do_060 := D_9e1bc.
Definition Fo_064 := F_9e1c0.
Definition Do_064 := D_9e1c0.
Definition Fo_068 := F_9e1c4.
Definition Do_068 := D_9e1c4.
Definition Fo_06c := F_9e1c8.
Definition Do_06c := D_9e1c8.
Definition Fo_070 := F_9e1cc.
Definition Do_070 := D_9e1cc.
Definition Fo_074 := F_9e1d0.
Definition Do_074 := D_9e1d0.
Definition Fo_078 := F_9e1d4.
Definition Do_078 := D_9e1d4.
Definition Fo_07c := F_9e1d8.
Definition Do_07c := D_9e1d8.
Definition Fo_080 := F_9e1dc.
Definition Do_080 := D_9e1dc.
Definition Fo_084 := F_9e1e0.
Definition Do_084 := D_9e1e0.
Definition Fo_088 := F_9e1e4.
Definition Do_088 := D_9e1e4.
Definition Fo_08c := F_9e1e8.
Definition Do_08c := D_9e1e8.
Definition Fo_090 := F_9e1ec.
Definition Do_090 := D_9e1ec.
Definition Fo_094 := F_9e1f0.
Definition Do_094 := D_9e1f0.
Definition Fo_098 := F_9e1f4.
Definition Do_098 := D_9e1f4.
Definition Fo_09c := F_9e1f8.
Definition Do_09c := D_9e1f8.
Definition Fo_0a0 := F_9e1fc.
Definition Do_0a0 := D_9e1fc.
Definition Fo_0a4 := F_9e200.
Definition Do_0a4 := D_9e200.
Definition Fo_0a8 := F_9e204.
Definition Do_0a8 := D_9e204.
Definition Fo_0ac := F_9e208.
Definition Do_0ac := D_9e208.
Definition Fo_0b0 := F_9e20c.
Definition Do_0b0 := D_9e20c.
Definition Fo_0b4 := F_9e210.
Definition Do_0b4 := D_9e210.
Definition Fo_0b8 := F_9e214.
Definition Do_0b8 := D_9e214.
Definition Fo_0bc := F_9e218.
Definition Do_0bc := D_9e218.
Definition Fo_0c0 := F_9e21c.
Definition Do_0c0 := D_9e21c.
Definition Fo_0c4 := F_9e220.
Definition Do_0c4 := D_9e220.
Definition Fo_0c8 := F_9e224.
Definition Do_0c8 := D_9e224.
Definition Fo_0cc := F_9e228.
Definition Do_0cc := D_9e228.
Definition Fo_0d0 := F_9e22c.
Definition Do_0d0 := D_9e22c.
Definition Fo_0d4 := F_9e230.
Definition Do_0d4 := D_9e230.
Definition Fo_0d8 := F_9e234.
Definition Do_0d8 := D_9e234.
Definition Fo_0dc := F_9e238.
Definition Do_0dc := D_9e238.
Definition Fo_0e0 := F_9e23c.
Definition Do_0e0 := D_9e23c.
Definition Fo_0e4 := F_9e240.
Definition Do_0e4 := D_9e240.
Definition Fo_0e8 := F_9e244.
Definition Do_0e8 := D_9e244.
Definition Fo_0ec := F_9e248.
Definition Do_0ec := D_9e248.
Definition Fo_0f0 := F_9e24c.
Definition Do_0f0 := D_9e24c.
Definition Fo_0f4 := F_9e250.
Definition Do_0f4 := D_9e250.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Img.TwB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_9e15c : bv 32 := 0x0e060a63.
Lemma F_9e15c : fetch_word SEGS (0x9eeb8 : word) = Some W_9e15c.
Proof. vm_refl. Qed.
Lemma D_9e15c : decode_any W_9e15c = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e160 : bv 32 := 0x00b50023.
Lemma F_9e160 : fetch_word SEGS (0x9eebc : word) = Some W_9e160.
Proof. vm_refl. Qed.
Lemma D_9e160 : decode_any W_9e160 = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e164 : bv 32 := 0x00c506b3.
Lemma F_9e164 : fetch_word SEGS (0x9eec0 : word) = Some W_9e164.
Proof. vm_refl. Qed.
Lemma D_9e164 : decode_any W_9e164 = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e168 : bv 32 := 0x00300713.
Lemma F_9e168 : fetch_word SEGS (0x9eec4 : word) = Some W_9e168.
Proof. vm_refl. Qed.
Lemma D_9e168 : decode_any W_9e168 = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e16c : bv 32 := 0xfeb68fa3.
Lemma F_9e16c : fetch_word SEGS (0x9eec8 : word) = Some W_9e16c.
Proof. vm_refl. Qed.
Lemma D_9e16c : decode_any W_9e16c = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e170 : bv 32 := 0x0ee66063.
Lemma F_9e170 : fetch_word SEGS (0x9eecc : word) = Some W_9e170.
Proof. vm_refl. Qed.
Lemma D_9e170 : decode_any W_9e170 = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e174 : bv 32 := 0x00b500a3.
Lemma F_9e174 : fetch_word SEGS (0x9eed0 : word) = Some W_9e174.
Proof. vm_refl. Qed.
Lemma D_9e174 : decode_any W_9e174 = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e178 : bv 32 := 0x00b50123.
Lemma F_9e178 : fetch_word SEGS (0x9eed4 : word) = Some W_9e178.
Proof. vm_refl. Qed.
Lemma D_9e178 : decode_any W_9e178 = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e17c : bv 32 := 0x00700713.
Lemma F_9e17c : fetch_word SEGS (0x9eed8 : word) = Some W_9e17c.
Proof. vm_refl. Qed.
Lemma D_9e17c : decode_any W_9e17c = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e180 : bv 32 := 0xfeb68ea3.
Lemma F_9e180 : fetch_word SEGS (0x9eedc : word) = Some W_9e180.
Proof. vm_refl. Qed.
Lemma D_9e180 : decode_any W_9e180 = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e184 : bv 32 := 0xfeb68f23.
Lemma F_9e184 : fetch_word SEGS (0x9eee0 : word) = Some W_9e184.
Proof. vm_refl. Qed.
Lemma D_9e184 : decode_any W_9e184 = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e188 : bv 32 := 0x0ce66463.
Lemma F_9e188 : fetch_word SEGS (0x9eee4 : word) = Some W_9e188.
Proof. vm_refl. Qed.
Lemma D_9e188 : decode_any W_9e188 = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e18c : bv 32 := 0x00b501a3.
Lemma F_9e18c : fetch_word SEGS (0x9eee8 : word) = Some W_9e18c.
Proof. vm_refl. Qed.
Lemma D_9e18c : decode_any W_9e18c = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e190 : bv 32 := 0x00900793.
Lemma F_9e190 : fetch_word SEGS (0x9eeec : word) = Some W_9e190.
Proof. vm_refl. Qed.
Lemma D_9e190 : decode_any W_9e190 = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e194 : bv 32 := 0xfeb68e23.
Lemma F_9e194 : fetch_word SEGS (0x9eef0 : word) = Some W_9e194.
Proof. vm_refl. Qed.
Lemma D_9e194 : decode_any W_9e194 = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e198 : bv 32 := 0x0af66c63.
Lemma F_9e198 : fetch_word SEGS (0x9eef4 : word) = Some W_9e198.
Proof. vm_refl. Qed.
Lemma D_9e198 : decode_any W_9e198 = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e19c : bv 32 := 0x40a006bb.
Lemma F_9e19c : fetch_word SEGS (0x9eef8 : word) = Some W_9e19c.
Proof. vm_refl. Qed.
Lemma D_9e19c : decode_any W_9e19c = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e1a0 : bv 32 := 0x03859813.
Lemma F_9e1a0 : fetch_word SEGS (0x9eefc : word) = Some W_9e1a0.
Proof. vm_refl. Qed.
Lemma D_9e1a0 : decode_any W_9e1a0 = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e1a4 : bv 32 := 0x101015b7.
Lemma F_9e1a4 : fetch_word SEGS (0x9ef00 : word) = Some W_9e1a4.
Proof. vm_refl. Qed.
Lemma D_9e1a4 : decode_any W_9e1a4 = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e1a8 : bv 32 := 0x0036f693.
Lemma F_9e1a8 : fetch_word SEGS (0x9ef04 : word) = Some W_9e1a8.
Proof. vm_refl. Qed.
Lemma D_9e1a8 : decode_any W_9e1a8 = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e1ac : bv 32 := 0x00459713.
Lemma F_9e1ac : fetch_word SEGS (0x9ef08 : word) = Some W_9e1ac.
Proof. vm_refl. Qed.
Lemma D_9e1ac : decode_any W_9e1ac = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e1b0 : bv 32 := 0x40d60633.
Lemma F_9e1b0 : fetch_word SEGS (0x9ef0c : word) = Some W_9e1b0.
Proof. vm_refl. Qed.
Lemma D_9e1b0 : decode_any W_9e1b0 = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e1b4 : bv 32 := 0x00d505b3.
Lemma F_9e1b4 : fetch_word SEGS (0x9ef10 : word) = Some W_9e1b4.
Proof. vm_refl. Qed.
Lemma D_9e1b4 : decode_any W_9e1b4 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e1b8 : bv 32 := 0x10070693.
Lemma F_9e1b8 : fetch_word SEGS (0x9ef14 : word) = Some W_9e1b8.
Proof. vm_refl. Qed.
Lemma D_9e1b8 : decode_any W_9e1b8 = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e1bc : bv 32 := 0xffc67713.
Lemma F_9e1bc : fetch_word SEGS (0x9ef18 : word) = Some W_9e1bc.
Proof. vm_refl. Qed.
Lemma D_9e1bc : decode_any W_9e1bc = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e1c0 : bv 32 := 0x02d83633.
Lemma F_9e1c0 : fetch_word SEGS (0x9ef1c : word) = Some W_9e1c0.
Proof. vm_refl. Qed.
Lemma D_9e1c0 : decode_any W_9e1c0 = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e1c4 : bv 32 := 0x00c5a023.
Lemma F_9e1c4 : fetch_word SEGS (0x9ef20 : word) = Some W_9e1c4.
Proof. vm_refl. Qed.
Lemma D_9e1c4 : decode_any W_9e1c4 = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e1c8 : bv 32 := 0x00e586b3.
Lemma F_9e1c8 : fetch_word SEGS (0x9ef24 : word) = Some W_9e1c8.
Proof. vm_refl. Qed.
Lemma D_9e1c8 : decode_any W_9e1c8 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e1cc : bv 32 := 0xfec6ae23.
Lemma F_9e1cc : fetch_word SEGS (0x9ef28 : word) = Some W_9e1cc.
Proof. vm_refl. Qed.
Lemma D_9e1cc : decode_any W_9e1cc = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e1d0 : bv 32 := 0x08f76063.
Lemma F_9e1d0 : fetch_word SEGS (0x9ef2c : word) = Some W_9e1d0.
Proof. vm_refl. Qed.
Lemma D_9e1d0 : decode_any W_9e1d0 = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e1d4 : bv 32 := 0x00c5a223.
Lemma F_9e1d4 : fetch_word SEGS (0x9ef30 : word) = Some W_9e1d4.
Proof. vm_refl. Qed.
Lemma D_9e1d4 : decode_any W_9e1d4 = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e1d8 : bv 32 := 0x00c5a423.
Lemma F_9e1d8 : fetch_word SEGS (0x9ef34 : word) = Some W_9e1d8.
Proof. vm_refl. Qed.
Lemma D_9e1d8 : decode_any W_9e1d8 = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e1dc : bv 32 := 0x01900793.
Lemma F_9e1dc : fetch_word SEGS (0x9ef38 : word) = Some W_9e1dc.
Proof. vm_refl. Qed.
Lemma D_9e1dc : decode_any W_9e1dc = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e1e0 : bv 32 := 0xfec6aa23.
Lemma F_9e1e0 : fetch_word SEGS (0x9ef3c : word) = Some W_9e1e0.
Proof. vm_refl. Qed.
Lemma D_9e1e0 : decode_any W_9e1e0 = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e1e4 : bv 32 := 0xfec6ac23.
Lemma F_9e1e4 : fetch_word SEGS (0x9ef40 : word) = Some W_9e1e4.
Proof. vm_refl. Qed.
Lemma D_9e1e4 : decode_any W_9e1e4 = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e1e8 : bv 32 := 0x06f76463.
Lemma F_9e1e8 : fetch_word SEGS (0x9ef44 : word) = Some W_9e1e8.
Proof. vm_refl. Qed.
Lemma D_9e1e8 : decode_any W_9e1e8 = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e1ec : bv 32 := 0x00c5a623.
Lemma F_9e1ec : fetch_word SEGS (0x9ef48 : word) = Some W_9e1ec.
Proof. vm_refl. Qed.
Lemma D_9e1ec : decode_any W_9e1ec = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e1f0 : bv 32 := 0x00c5a823.
Lemma F_9e1f0 : fetch_word SEGS (0x9ef4c : word) = Some W_9e1f0.
Proof. vm_refl. Qed.
Lemma D_9e1f0 : decode_any W_9e1f0 = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e1f4 : bv 32 := 0x00c5aa23.
Lemma F_9e1f4 : fetch_word SEGS (0x9ef50 : word) = Some W_9e1f4.
Proof. vm_refl. Qed.
Lemma D_9e1f4 : decode_any W_9e1f4 = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e1f8 : bv 32 := 0x00c5ac23.
Lemma F_9e1f8 : fetch_word SEGS (0x9ef54 : word) = Some W_9e1f8.
Proof. vm_refl. Qed.
Lemma D_9e1f8 : decode_any W_9e1f8 = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e1fc : bv 32 := 0x0045f793.
Lemma F_9e1fc : fetch_word SEGS (0x9ef58 : word) = Some W_9e1fc.
Proof. vm_refl. Qed.
Lemma D_9e1fc : decode_any W_9e1fc = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e200 : bv 32 := 0x02000813.
Lemma F_9e200 : fetch_word SEGS (0x9ef5c : word) = Some W_9e200.
Proof. vm_refl. Qed.
Lemma D_9e200 : decode_any W_9e200 = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e204 : bv 32 := 0x01878793.
Lemma F_9e204 : fetch_word SEGS (0x9ef60 : word) = Some W_9e204.
Proof. vm_refl. Qed.
Lemma D_9e204 : decode_any W_9e204 = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e208 : bv 32 := 0x40f70733.
Lemma F_9e208 : fetch_word SEGS (0x9ef64 : word) = Some W_9e208.
Proof. vm_refl. Qed.
Lemma D_9e208 : decode_any W_9e208 = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e20c : bv 32 := 0xfec6a223.
Lemma F_9e20c : fetch_word SEGS (0x9ef68 : word) = Some W_9e20c.
Proof. vm_refl. Qed.
Lemma D_9e20c : decode_any W_9e20c = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e210 : bv 32 := 0xfec6a423.
Lemma F_9e210 : fetch_word SEGS (0x9ef6c : word) = Some W_9e210.
Proof. vm_refl. Qed.
Lemma D_9e210 : decode_any W_9e210 = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e214 : bv 32 := 0xfec6a623.
Lemma F_9e214 : fetch_word SEGS (0x9ef70 : word) = Some W_9e214.
Proof. vm_refl. Qed.
Lemma D_9e214 : decode_any W_9e214 = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e218 : bv 32 := 0xfec6a823.
Lemma F_9e218 : fetch_word SEGS (0x9ef74 : word) = Some W_9e218.
Proof. vm_refl. Qed.
Lemma D_9e218 : decode_any W_9e218 = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e21c : bv 32 := 0x03076a63.
Lemma F_9e21c : fetch_word SEGS (0x9ef78 : word) = Some W_9e21c.
Proof. vm_refl. Qed.
Lemma D_9e21c : decode_any W_9e21c = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e220 : bv 32 := 0x02061613.
Lemma F_9e220 : fetch_word SEGS (0x9ef7c : word) = Some W_9e220.
Proof. vm_refl. Qed.
Lemma D_9e220 : decode_any W_9e220 = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e224 : bv 32 := 0x00f585b3.
Lemma F_9e224 : fetch_word SEGS (0x9ef80 : word) = Some W_9e224.
Proof. vm_refl. Qed.
Lemma D_9e224 : decode_any W_9e224 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e228 : bv 32 := 0x02065693.
Lemma F_9e228 : fetch_word SEGS (0x9ef84 : word) = Some W_9e228.
Proof. vm_refl. Qed.
Lemma D_9e228 : decode_any W_9e228 = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e22c : bv 32 := 0x00d66633.
Lemma F_9e22c : fetch_word SEGS (0x9ef88 : word) = Some W_9e22c.
Proof. vm_refl. Qed.
Lemma D_9e22c : decode_any W_9e22c = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e230 : bv 32 := 0x01f00693.
Lemma F_9e230 : fetch_word SEGS (0x9ef8c : word) = Some W_9e230.
Proof. vm_refl. Qed.
Lemma D_9e230 : decode_any W_9e230 = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e234 : bv 32 := 0x00c5b023.
Lemma F_9e234 : fetch_word SEGS (0x9ef90 : word) = Some W_9e234.
Proof. vm_refl. Qed.
Lemma D_9e234 : decode_any W_9e234 = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e238 : bv 32 := 0x00c5b423.
Lemma F_9e238 : fetch_word SEGS (0x9ef94 : word) = Some W_9e238.
Proof. vm_refl. Qed.
Lemma D_9e238 : decode_any W_9e238 = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e23c : bv 32 := 0x00c5b823.
Lemma F_9e23c : fetch_word SEGS (0x9ef98 : word) = Some W_9e23c.
Proof. vm_refl. Qed.
Lemma D_9e23c : decode_any W_9e23c = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e240 : bv 32 := 0x00c5bc23.
Lemma F_9e240 : fetch_word SEGS (0x9ef9c : word) = Some W_9e240.
Proof. vm_refl. Qed.
Lemma D_9e240 : decode_any W_9e240 = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e244 : bv 32 := 0xfe070713.
Lemma F_9e244 : fetch_word SEGS (0x9efa0 : word) = Some W_9e244.
Proof. vm_refl. Qed.
Lemma D_9e244 : decode_any W_9e244 = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e248 : bv 32 := 0x02058593.
Lemma F_9e248 : fetch_word SEGS (0x9efa4 : word) = Some W_9e248.
Proof. vm_refl. Qed.
Lemma D_9e248 : decode_any W_9e248 = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e24c : bv 32 := 0xfee6e4e3.
Lemma F_9e24c : fetch_word SEGS (0x9efa8 : word) = Some W_9e24c.
Proof. vm_refl. Qed.
Lemma D_9e24c : decode_any W_9e24c = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e250 : bv 32 := 0x00008067.
Lemma F_9e250 : fetch_word SEGS (0x9efac : word) = Some W_9e250.
Proof. vm_refl. Qed.
Lemma D_9e250 : decode_any W_9e250 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Abbreviation MSEGS := SEGS.
Definition ms_base : Z := 0x9eeb8%Z.   (* [comment removed for export] *)
Definition Fo_000 := F_9e15c.
Definition Do_000 := D_9e15c.
Definition Fo_004 := F_9e160.
Definition Do_004 := D_9e160.
Definition Fo_008 := F_9e164.
Definition Do_008 := D_9e164.
Definition Fo_00c := F_9e168.
Definition Do_00c := D_9e168.
Definition Fo_010 := F_9e16c.
Definition Do_010 := D_9e16c.
Definition Fo_014 := F_9e170.
Definition Do_014 := D_9e170.
Definition Fo_018 := F_9e174.
Definition Do_018 := D_9e174.
Definition Fo_01c := F_9e178.
Definition Do_01c := D_9e178.
Definition Fo_020 := F_9e17c.
Definition Do_020 := D_9e17c.
Definition Fo_024 := F_9e180.
Definition Do_024 := D_9e180.
Definition Fo_028 := F_9e184.
Definition Do_028 := D_9e184.
Definition Fo_02c := F_9e188.
Definition Do_02c := D_9e188.
Definition Fo_030 := F_9e18c.
Definition Do_030 := D_9e18c.
Definition Fo_034 := F_9e190.
Definition Do_034 := D_9e190.
Definition Fo_038 := F_9e194.
Definition Do_038 := D_9e194.
Definition Fo_03c := F_9e198.
Definition Do_03c := D_9e198.
Definition Fo_040 := F_9e19c.
Definition Do_040 := D_9e19c.
Definition Fo_044 := F_9e1a0.
Definition Do_044 := D_9e1a0.
Definition Fo_048 := F_9e1a4.
Definition Do_048 := D_9e1a4.
Definition Fo_04c := F_9e1a8.
Definition Do_04c := D_9e1a8.
Definition Fo_050 := F_9e1ac.
Definition Do_050 := D_9e1ac.
Definition Fo_054 := F_9e1b0.
Definition Do_054 := D_9e1b0.
Definition Fo_058 := F_9e1b4.
Definition Do_058 := D_9e1b4.
Definition Fo_05c := F_9e1b8.
Definition Do_05c := D_9e1b8.
Definition Fo_060 := F_9e1bc.
Definition Do_060 := D_9e1bc.
Definition Fo_064 := F_9e1c0.
Definition Do_064 := D_9e1c0.
Definition Fo_068 := F_9e1c4.
Definition Do_068 := D_9e1c4.
Definition Fo_06c := F_9e1c8.
Definition Do_06c := D_9e1c8.
Definition Fo_070 := F_9e1cc.
Definition Do_070 := D_9e1cc.
Definition Fo_074 := F_9e1d0.
Definition Do_074 := D_9e1d0.
Definition Fo_078 := F_9e1d4.
Definition Do_078 := D_9e1d4.
Definition Fo_07c := F_9e1d8.
Definition Do_07c := D_9e1d8.
Definition Fo_080 := F_9e1dc.
Definition Do_080 := D_9e1dc.
Definition Fo_084 := F_9e1e0.
Definition Do_084 := D_9e1e0.
Definition Fo_088 := F_9e1e4.
Definition Do_088 := D_9e1e4.
Definition Fo_08c := F_9e1e8.
Definition Do_08c := D_9e1e8.
Definition Fo_090 := F_9e1ec.
Definition Do_090 := D_9e1ec.
Definition Fo_094 := F_9e1f0.
Definition Do_094 := D_9e1f0.
Definition Fo_098 := F_9e1f4.
Definition Do_098 := D_9e1f4.
Definition Fo_09c := F_9e1f8.
Definition Do_09c := D_9e1f8.
Definition Fo_0a0 := F_9e1fc.
Definition Do_0a0 := D_9e1fc.
Definition Fo_0a4 := F_9e200.
Definition Do_0a4 := D_9e200.
Definition Fo_0a8 := F_9e204.
Definition Do_0a8 := D_9e204.
Definition Fo_0ac := F_9e208.
Definition Do_0ac := D_9e208.
Definition Fo_0b0 := F_9e20c.
Definition Do_0b0 := D_9e20c.
Definition Fo_0b4 := F_9e210.
Definition Do_0b4 := D_9e210.
Definition Fo_0b8 := F_9e214.
Definition Do_0b8 := D_9e214.
Definition Fo_0bc := F_9e218.
Definition Do_0bc := D_9e218.
Definition Fo_0c0 := F_9e21c.
Definition Do_0c0 := D_9e21c.
Definition Fo_0c4 := F_9e220.
Definition Do_0c4 := D_9e220.
Definition Fo_0c8 := F_9e224.
Definition Do_0c8 := D_9e224.
Definition Fo_0cc := F_9e228.
Definition Do_0cc := D_9e228.
Definition Fo_0d0 := F_9e22c.
Definition Do_0d0 := D_9e22c.
Definition Fo_0d4 := F_9e230.
Definition Do_0d4 := D_9e230.
Definition Fo_0d8 := F_9e234.
Definition Do_0d8 := D_9e234.
Definition Fo_0dc := F_9e238.
Definition Do_0dc := D_9e238.
Definition Fo_0e0 := F_9e23c.
Definition Do_0e0 := D_9e23c.
Definition Fo_0e4 := F_9e240.
Definition Do_0e4 := D_9e240.
Definition Fo_0e8 := F_9e244.
Definition Do_0e8 := D_9e244.
Definition Fo_0ec := F_9e248.
Definition Do_0ec := D_9e248.
Definition Fo_0f0 := F_9e24c.
Definition Do_0f0 := D_9e24c.
Definition Fo_0f4 := F_9e250.
Definition Do_0f4 := D_9e250.
End TwB.
End MuslMemset_code.

(* [comment removed for export] *)
Module BootLedgerA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require Import AsanShadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Img. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Syms__A3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Img OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3Syms.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive guard3 : Type := GuardOk | GuardKept | GuardDestroyed.

(* [comment removed for export] *)
Inductive musl_variant : Type :=
  | MV_grown (g : guard3) (p22 : option word)     (* [comment removed for export] *)
  | MV_refused_nometa                             (* [comment removed for export] *)
  | MV_refused (q : word) (prot_ok : bool) (p22 : option word).
      (* [comment removed for export] *)

Record placements : Type := mkPL {
  pl_space  : word;   (* [comment removed for export] *)
  pl_ptrarr : word;   (* [comment removed for export] *)
  pl_nodes  : word;   (* [comment removed for export] *)
  pl_frames : word;   (* [comment removed for export] *)
  pl_thr    : word;   (* [comment removed for export] *)
  pl_ctx    : word;   (* [comment removed for export] *)
  pl_mv     : musl_variant;
  pl_misc   : list word  (* [comment removed for export] *) }.

(* [comment removed for export] *)
Definition pl_list (p : placements) : list word := [pl_space p; pl_ptrarr p; pl_nodes p; pl_frames p; pl_thr p; pl_ctx p].
Definition NPL : nat := 6.
Lemma pl_list_length : forall p, length (pl_list p) = NPL. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition misc (p : placements) (k : nat) : word := nth k (pl_misc p) (Z_to_bv 64 0).
Definition K_LL1 : nat := 10.  Definition pl_ll1 (p : placements) : word := misc p K_LL1.    (* [comment removed for export] *)
Definition K_META : nat := 11. Definition pl_meta (p : placements) : word := misc p K_META.  (* [comment removed for export] *)
Definition K_V13 : nat := 12.  Definition pl_v13 (p : placements) : word := misc p K_V13.    (* [comment removed for export] *)
Definition K_V14 : nat := 13.  Definition pl_v14 (p : placements) : word := misc p K_V14.    (* [comment removed for export] *)
Definition K_BIG : nat := 14.  Definition pl_big (p : placements) : word := misc p K_BIG.    (* [comment removed for export] *)
Definition K_G25 : nat := 15.  Definition pl_g25 (p : placements) : word := misc p K_G25.    (* [comment removed for export] *)
Definition K_G26 : nat := 16.  Definition pl_g26 (p : placements) : word := misc p K_G26.    (* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition N_SPACE : Z := 0x2000011000.     (* [comment removed for export] *)
Definition N_PTRARR : Z := 0x800000.
Definition N_NODES : Z := 0x100000.
Definition N_FRAMES : Z := 0x800000.
Definition N_THR : Z := 4096.
Definition N_CTX : Z := 0x10000.
Definition N_LL1 : Z := 0x10000.
Definition N_META : Z := 0x38e000.
Definition N_BIG : Z := 0xb09000.

Definition wz (z : Z) : word := Z_to_bv 64 z.
Definition ivz (a n : Z) : word * word := (wz a, wz n).

(* [comment removed for export] *)
Definition round_up (x m : Z) : Z := ((x + m - 1) / m) * m.
Definition SPACE_BEG (p : placements) : Z := bv_unsigned (pl_space p) + 0x10000 - bv_unsigned (pl_space p) mod 0x10000.
Definition REGION_INFO (p : placements) : Z := SPACE_BEG p + 0x2000000000.

(* [comment removed for export] *)
Definition STACK_TOP (sp : word) : Z := ((bv_unsigned sp + 0xf5f) / 4096) * 4096.
Definition STACK_BOT (sp : word) : Z := STACK_TOP sp - 0x800000.
Definition SSH_LO (sp : word) : Z := round_up (sh (STACK_BOT sp)) 4096.
Definition SSH_HI (sp : word) : Z := (sh (STACK_TOP sp) / 4096) * 4096.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition IV_TLS (a : word) : word * word := (a, wz 4096).
Definition IV_LO  : word * word := ivz SH_LO (GAP_LO - SH_LO).
Definition IV_GAP : word * word := ivz GAP_LO (HI_LO - GAP_LO).
Definition IV_HI  : word * word := ivz HI_LO (HI_HI - HI_LO).

(* [comment removed for export] *)
Definition MUSL_MAPS (brk : word) (v : musl_variant) : list (word * word) :=
  match v with
  | MV_grown g p22 =>
      match p22 with Some p => [(p, wz 4096)] | None => [] end
      ++ match g with GuardDestroyed => [ivz (bv_unsigned brk + 4096) 4096] | _ => [(brk, wz 8192)] end
  | MV_refused_nometa => []
  | MV_refused q _ p22 => match p22 with Some p => [(p, wz 4096)] | None => [] end ++ [(q, wz 8192)]
  end.
Definition MUSL_NOACC (brk : word) (v : musl_variant) : list (word * word) :=
  match v with
  | MV_grown GuardOk _ => [(brk, wz 4096)]
  | MV_grown _ _ => []
  | MV_refused_nometa => []
  | MV_refused q true _ => [(q, wz 4096)]
  | MV_refused q false _ => [(q, wz 8192)]
  end.
Definition BRK_MAIN (brk : word) (v : musl_variant) : word :=
  match v with MV_grown _ _ => wz (bv_unsigned brk + 0x2000) | _ => brk end.

Definition MAPS_MAIN (sp brk a : word) (p : placements) : list (word * word) :=
  [(pl_g26 p, wz 4096); (pl_g25 p, wz 4096); (pl_frames p, wz N_FRAMES); (pl_nodes p, wz N_NODES)]
  ++ MUSL_MAPS brk (pl_mv p)
  ++ [(pl_big p, wz N_BIG); (pl_v14 p, wz 4096); (pl_v13 p, wz 4096); (pl_ctx p, wz N_CTX); (pl_thr p, wz N_THR);
      (pl_ptrarr p, wz N_PTRARR); (pl_space p, wz N_SPACE); (pl_meta p, wz N_META); (pl_ll1 p, wz N_LL1);
      IV_HI; IV_GAP; IV_LO; IV_TLS a].

(* [comment removed for export] *)
Definition IV_SPACE_A (p : placements) : word * word := (pl_space p, wz (REGION_INFO p - bv_unsigned (pl_space p))).
Definition IV_SPACE_B (p : placements) : word * word :=
  ivz (REGION_INFO p + 4096) (bv_unsigned (pl_space p) + N_SPACE - (REGION_INFO p + 4096)).
Definition SPACE_TAIL (p : placements) : list (word * word) :=
  if (bv_unsigned (pl_space p) mod 0x10000 =? 0) then [] else [IV_SPACE_B p].

Definition NOACC_MAIN (brk : word) (p : placements) : list (word * word) :=
  MUSL_NOACC brk (pl_mv p) ++ [(pl_ptrarr p, wz N_PTRARR); IV_SPACE_A p] ++ SPACE_TAIL p ++ [IV_GAP].

(* [comment removed for export] *)
Definition IV_SSH (sp : word) : word * word := ivz (SSH_LO sp) (SSH_HI sp - SSH_LO sp).
Definition IV_HI_A (sp : word) : word * word := ivz HI_LO (SSH_LO sp - HI_LO).
Definition IV_HI_B (sp : word) : word * word := ivz (SSH_HI sp) (HI_HI - SSH_HI sp).

Definition LAZY_MAIN (sp : word) (p : placements) : list (word * word) :=
  [(pl_frames p, wz N_FRAMES); IV_SSH sp; (pl_ptrarr p, wz N_PTRARR); IV_SPACE_A p] ++ SPACE_TAIL p ++
  [IV_HI_A sp; IV_HI_B sp; IV_GAP; IV_LO].

(* [comment removed for export] *)
Definition EAGER_MAIN : Z := 2 ^ 24.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition NMISC : nat := 60.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition block_ok (sp : word) (b : word) (n : Z) : Prop :=
  let v := bv_unsigned b in
  v mod 4096 = 0 /\ 4096 <= v /\ v + n <= bv_unsigned sp - stack_max_size
  /\ (v + n <= A_img_lo \/ A_img_hi <= v) /\ (v + n <= SH_LO \/ HI_HI <= v).

Fixpoint apart_all (l : list (word * word)) : Prop :=
  match l with
  | [] => True
  | (b, n) :: r => Forall (fun q => bv_unsigned b + bv_unsigned n <= bv_unsigned (fst q)
                                  \/ bv_unsigned (fst q) + bv_unsigned (snd q) <= bv_unsigned b) r /\ apart_all r
  end.

Record placements_ok (sp brk a : word) (p : placements) : Prop := {
  po_blocks : Forall (fun q => block_ok sp (fst q) (bv_unsigned (snd q)))
                (List.firstn (length (MAPS_MAIN sp brk a p) - 4)%nat (MAPS_MAIN sp brk a p));  (* [comment removed for export] *)
  po_tls    : block_ok sp a 4096;
  po_apart  : apart_all (MAPS_MAIN sp brk a p);
  po_space  : HI_HI <= bv_unsigned (pl_space p);          (* [comment removed for export] *)
  po_brk    : IMG_HI <= bv_unsigned brk <= IMG_HI + brk_aslr_max /\ bv_unsigned brk mod 4096 = 0;
                (* [comment removed for export] *)
  po_misc   : length (pl_misc p) = NMISC }.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.State.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.AsanShadow.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Img.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3Syms.TwB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive guard3 : Type := GuardOk | GuardKept | GuardDestroyed.

(* [comment removed for export] *)
Inductive musl_variant : Type :=
  | MV_grown (g : guard3) (p22 : option word)     (* [comment removed for export] *)
  | MV_refused_nometa                             (* [comment removed for export] *)
  | MV_refused (q : word) (prot_ok : bool) (p22 : option word).
      (* [comment removed for export] *)

Record placements : Type := mkPL {
  pl_space  : word;   (* [comment removed for export] *)
  pl_ptrarr : word;   (* [comment removed for export] *)
  pl_nodes  : word;   (* [comment removed for export] *)
  pl_frames : word;   (* [comment removed for export] *)
  pl_thr    : word;   (* [comment removed for export] *)
  pl_ctx    : word;   (* [comment removed for export] *)
  pl_mv     : musl_variant;
  pl_misc   : list word  (* [comment removed for export] *) }.

(* [comment removed for export] *)
Definition pl_list (p : placements) : list word := [pl_space p; pl_ptrarr p; pl_nodes p; pl_frames p; pl_thr p; pl_ctx p].
Definition NPL : nat := 6.
Lemma pl_list_length : forall p, length (pl_list p) = NPL. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition misc (p : placements) (k : nat) : word := nth k (pl_misc p) (Z_to_bv 64 0).
Definition K_LL1 : nat := 10.  Definition pl_ll1 (p : placements) : word := misc p K_LL1.    (* [comment removed for export] *)
Definition K_META : nat := 11. Definition pl_meta (p : placements) : word := misc p K_META.  (* [comment removed for export] *)
Definition K_V13 : nat := 12.  Definition pl_v13 (p : placements) : word := misc p K_V13.    (* [comment removed for export] *)
Definition K_V14 : nat := 13.  Definition pl_v14 (p : placements) : word := misc p K_V14.    (* [comment removed for export] *)
Definition K_BIG : nat := 14.  Definition pl_big (p : placements) : word := misc p K_BIG.    (* [comment removed for export] *)
Definition K_G25 : nat := 15.  Definition pl_g25 (p : placements) : word := misc p K_G25.    (* [comment removed for export] *)
Definition K_G26 : nat := 16.  Definition pl_g26 (p : placements) : word := misc p K_G26.    (* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition N_SPACE : Z := 0x2000011000.     (* [comment removed for export] *)
Definition N_PTRARR : Z := 0x800000.
Definition N_NODES : Z := 0x100000.
Definition N_FRAMES : Z := 0x800000.
Definition N_THR : Z := 4096.
Definition N_CTX : Z := 0x10000.
Definition N_LL1 : Z := 0x10000.
Definition N_META : Z := 0x38e000.
Definition N_BIG : Z := 0xb09000.

Definition wz (z : Z) : word := Z_to_bv 64 z.
Definition ivz (a n : Z) : word * word := (wz a, wz n).

(* [comment removed for export] *)
Definition round_up (x m : Z) : Z := ((x + m - 1) / m) * m.
Definition SPACE_BEG (p : placements) : Z := bv_unsigned (pl_space p) + 0x10000 - bv_unsigned (pl_space p) mod 0x10000.
Definition REGION_INFO (p : placements) : Z := SPACE_BEG p + 0x2000000000.

(* [comment removed for export] *)
Definition STACK_TOP (sp : word) : Z := ((bv_unsigned sp + 0xf5f) / 4096) * 4096.
Definition STACK_BOT (sp : word) : Z := STACK_TOP sp - 0x800000.
Definition SSH_LO (sp : word) : Z := round_up (sh (STACK_BOT sp)) 4096.
Definition SSH_HI (sp : word) : Z := (sh (STACK_TOP sp) / 4096) * 4096.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition IV_TLS (a : word) : word * word := (a, wz 4096).
Definition IV_LO  : word * word := ivz SH_LO (GAP_LO - SH_LO).
Definition IV_GAP : word * word := ivz GAP_LO (HI_LO - GAP_LO).
Definition IV_HI  : word * word := ivz HI_LO (HI_HI - HI_LO).

(* [comment removed for export] *)
Definition MUSL_MAPS (brk : word) (v : musl_variant) : list (word * word) :=
  match v with
  | MV_grown g p22 =>
      match p22 with Some p => [(p, wz 4096)] | None => [] end
      ++ match g with GuardDestroyed => [ivz (bv_unsigned brk + 4096) 4096] | _ => [(brk, wz 8192)] end
  | MV_refused_nometa => []
  | MV_refused q _ p22 => match p22 with Some p => [(p, wz 4096)] | None => [] end ++ [(q, wz 8192)]
  end.
Definition MUSL_NOACC (brk : word) (v : musl_variant) : list (word * word) :=
  match v with
  | MV_grown GuardOk _ => [(brk, wz 4096)]
  | MV_grown _ _ => []
  | MV_refused_nometa => []
  | MV_refused q true _ => [(q, wz 4096)]
  | MV_refused q false _ => [(q, wz 8192)]
  end.
Definition BRK_MAIN (brk : word) (v : musl_variant) : word :=
  match v with MV_grown _ _ => wz (bv_unsigned brk + 0x2000) | _ => brk end.

Definition MAPS_MAIN (sp brk a : word) (p : placements) : list (word * word) :=
  [(pl_g26 p, wz 4096); (pl_g25 p, wz 4096); (pl_frames p, wz N_FRAMES); (pl_nodes p, wz N_NODES)]
  ++ MUSL_MAPS brk (pl_mv p)
  ++ [(pl_big p, wz N_BIG); (pl_v14 p, wz 4096); (pl_v13 p, wz 4096); (pl_ctx p, wz N_CTX); (pl_thr p, wz N_THR);
      (pl_ptrarr p, wz N_PTRARR); (pl_space p, wz N_SPACE); (pl_meta p, wz N_META); (pl_ll1 p, wz N_LL1);
      IV_HI; IV_GAP; IV_LO; IV_TLS a].

(* [comment removed for export] *)
Definition IV_SPACE_A (p : placements) : word * word := (pl_space p, wz (REGION_INFO p - bv_unsigned (pl_space p))).
Definition IV_SPACE_B (p : placements) : word * word :=
  ivz (REGION_INFO p + 4096) (bv_unsigned (pl_space p) + N_SPACE - (REGION_INFO p + 4096)).
Definition SPACE_TAIL (p : placements) : list (word * word) :=
  if (bv_unsigned (pl_space p) mod 0x10000 =? 0) then [] else [IV_SPACE_B p].

Definition NOACC_MAIN (brk : word) (p : placements) : list (word * word) :=
  MUSL_NOACC brk (pl_mv p) ++ [(pl_ptrarr p, wz N_PTRARR); IV_SPACE_A p] ++ SPACE_TAIL p ++ [IV_GAP].

(* [comment removed for export] *)
Definition IV_SSH (sp : word) : word * word := ivz (SSH_LO sp) (SSH_HI sp - SSH_LO sp).
Definition IV_HI_A (sp : word) : word * word := ivz HI_LO (SSH_LO sp - HI_LO).
Definition IV_HI_B (sp : word) : word * word := ivz (SSH_HI sp) (HI_HI - SSH_HI sp).

Definition LAZY_MAIN (sp : word) (p : placements) : list (word * word) :=
  [(pl_frames p, wz N_FRAMES); IV_SSH sp; (pl_ptrarr p, wz N_PTRARR); IV_SPACE_A p] ++ SPACE_TAIL p ++
  [IV_HI_A sp; IV_HI_B sp; IV_GAP; IV_LO].

(* [comment removed for export] *)
Definition EAGER_MAIN : Z := 2 ^ 24.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition NMISC : nat := 60.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition block_ok (sp : word) (b : word) (n : Z) : Prop :=
  let v := bv_unsigned b in
  v mod 4096 = 0 /\ 4096 <= v /\ v + n <= bv_unsigned sp - stack_max_size
  /\ (v + n <= A_img_lo \/ A_img_hi <= v) /\ (v + n <= SH_LO \/ HI_HI <= v).

Fixpoint apart_all (l : list (word * word)) : Prop :=
  match l with
  | [] => True
  | (b, n) :: r => Forall (fun q => bv_unsigned b + bv_unsigned n <= bv_unsigned (fst q)
                                  \/ bv_unsigned (fst q) + bv_unsigned (snd q) <= bv_unsigned b) r /\ apart_all r
  end.

Record placements_ok (sp brk a : word) (p : placements) : Prop := {
  po_blocks : Forall (fun q => block_ok sp (fst q) (bv_unsigned (snd q)))
                (List.firstn (length (MAPS_MAIN sp brk a p) - 4)%nat (MAPS_MAIN sp brk a p));  (* [comment removed for export] *)
  po_tls    : block_ok sp a 4096;
  po_apart  : apart_all (MAPS_MAIN sp brk a p);
  po_space  : HI_HI <= bv_unsigned (pl_space p);          (* [comment removed for export] *)
  po_brk    : IMG_HI <= bv_unsigned brk <= IMG_HI + brk_aslr_max /\ bv_unsigned brk mod 4096 = 0;
                (* [comment removed for export] *)
  po_misc   : length (pl_misc p) = NMISC }.
End TwB.
End BootLedgerA.
