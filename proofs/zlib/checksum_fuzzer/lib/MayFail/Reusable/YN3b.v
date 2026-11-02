(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN3b.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK0w.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH00.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YH03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN32.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma fetch_lit : forall (p : word) (w : bv 32),
clookup src0tbl (bv_unsigned p) = Some (bv_unsigned w) ->
fetch_word src0segs p = Some w.
Proof.
intros p w H.
rewrite <- (Z_to_bv_bv_unsigned 64 p), <- (Z_to_bv_bv_unsigned 32 w).
apply src0tbl_ok. exact H.
Qed.
End c.
Ltac ftac := apply fetch_lit; vm_compute; reflexivity.
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma F_000 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x0)) = Some (0x0035f693%bv : bv 32).
Proof. ftac. Qed.
Lemma D_000 : decode_any (0x0035f693%bv : bv 32) = Some (OpImm ALU_AND 13 11 3, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_004 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x4)) = Some (0x10068863%bv : bv 32).
Proof. ftac. Qed.
Lemma D_004 : decode_any (0x10068863%bv : bv 32) = Some (Branch BC_EQ 13 0 272, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_008 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x8)) = Some (0x02060e63%bv : bv 32).
Proof. ftac. Qed.
Lemma D_008 : decode_any (0x02060e63%bv : bv 32) = Some (Branch BC_EQ 12 0 60, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_00c : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0xc)) = Some (0x00158713%bv : bv 32).
Proof. ftac. Qed.
Lemma D_00c : decode_any (0x00158713%bv : bv 32) = Some (OpImm ALU_ADD 14 11 1, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_010 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x10)) = Some (0x00100793%bv : bv 32).
Proof. ftac. Qed.
Lemma D_010 : decode_any (0x00100793%bv : bv 32) = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_014 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x14)) = Some (0x00050693%bv : bv 32).
Proof. ftac. Qed.
Lemma D_014 : decode_any (0x00050693%bv : bv 32) = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_018 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x18)) = Some (0x0005c883%bv : bv 32).
Proof. ftac. Qed.
Lemma D_018 : decode_any (0x0005c883%bv : bv 32) = Some (Load SZ1 false 17 11 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_01c : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x1c)) = Some (0x00060813%bv : bv 32).
Proof. ftac. Qed.
Lemma D_01c : decode_any (0x00060813%bv : bv 32) = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_020 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x20)) = Some (0x00158593%bv : bv 32).
Proof. ftac. Qed.
Lemma D_020 : decode_any (0x00158593%bv : bv 32) = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_024 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x24)) = Some (0x00377293%bv : bv 32).
Proof. ftac. Qed.
Lemma D_024 : decode_any (0x00377293%bv : bv 32) = Some (OpImm ALU_AND 5 14 3, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_028 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x28)) = Some (0x01168023%bv : bv 32).
Proof. ftac. Qed.
Lemma D_028 : decode_any (0x01168023%bv : bv 32) = Some (Store SZ1 13 17 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_02c : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x2c)) = Some (0x00168693%bv : bv 32).
Proof. ftac. Qed.
Lemma D_02c : decode_any (0x00168693%bv : bv 32) = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_030 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x30)) = Some (0xfff60613%bv : bv 32).
Proof. ftac. Qed.
Lemma D_030 : decode_any (0xfff60613%bv : bv 32) = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_034 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x34)) = Some (0x00028a63%bv : bv 32).
Proof. ftac. Qed.
Lemma D_034 : decode_any (0x00028a63%bv : bv 32) = Some (Branch BC_EQ 5 0 20, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_038 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x38)) = Some (0x00170713%bv : bv 32).
Proof. ftac. Qed.
Lemma D_038 : decode_any (0x00170713%bv : bv 32) = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_03c : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x3c)) = Some (0xfcf81ee3%bv : bv 32).
Proof. ftac. Qed.
Lemma D_03c : decode_any (0xfcf81ee3%bv : bv 32) = Some (Branch BC_NE 16 15 8156, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_040 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x40)) = Some (0x0080006f%bv : bv 32).
Proof. ftac. Qed.
Lemma D_040 : decode_any (0x0080006f%bv : bv 32) = Some (Jal 0 8, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_044 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x44)) = Some (0x00050693%bv : bv 32).
Proof. ftac. Qed.
Lemma D_044 : decode_any (0x00050693%bv : bv 32) = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_048 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x48)) = Some (0x0036f793%bv : bv 32).
Proof. ftac. Qed.
Lemma D_048 : decode_any (0x0036f793%bv : bv 32) = Some (OpImm ALU_AND 15 13 3, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_04c : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x4c)) = Some (0x0c078a63%bv : bv 32).
Proof. ftac. Qed.
Lemma D_04c : decode_any (0x0c078a63%bv : bv 32) = Some (Branch BC_EQ 15 0 212, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_050 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x50)) = Some (0x02000713%bv : bv 32).
Proof. ftac. Qed.
Lemma D_050 : decode_any (0x02000713%bv : bv 32) = Some (OpImm ALU_ADD 14 0 32, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_054 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x54)) = Some (0x02e67063%bv : bv 32).
Proof. ftac. Qed.
Lemma D_054 : decode_any (0x02e67063%bv : bv 32) = Some (Branch BC_GEU 12 14 32, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_058 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x58)) = Some (0x01000713%bv : bv 32).
Proof. ftac. Qed.
Lemma D_058 : decode_any (0x01000713%bv : bv 32) = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_05c : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x5c)) = Some (0x24e67863%bv : bv 32).
Proof. ftac. Qed.
Lemma D_05c : decode_any (0x24e67863%bv : bv 32) = Some (Branch BC_GEU 12 14 592, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_060 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x60)) = Some (0x00867713%bv : bv 32).
Proof. ftac. Qed.
Lemma D_060 : decode_any (0x00867713%bv : bv 32) = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_064 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x64)) = Some (0x2c071e63%bv : bv 32).
Proof. ftac. Qed.
Lemma D_064 : decode_any (0x2c071e63%bv : bv 32) = Some (Branch BC_NE 14 0 732, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_068 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x68)) = Some (0x00467713%bv : bv 32).
Proof. ftac. Qed.
Lemma D_068 : decode_any (0x00467713%bv : bv 32) = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_06c : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x6c)) = Some (0x32071463%bv : bv 32).
Proof. ftac. Qed.
Lemma D_06c : decode_any (0x32071463%bv : bv 32) = Some (Branch BC_NE 14 0 808, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_070 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x70)) = Some (0x3500006f%bv : bv 32).
Proof. ftac. Qed.
Lemma D_070 : decode_any (0x3500006f%bv : bv 32) = Some (Jal 0 848, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_074 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x74)) = Some (0x0005a703%bv : bv 32).
Proof. ftac. Qed.
Lemma D_074 : decode_any (0x0005a703%bv : bv 32) = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_078 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x78)) = Some (0x00300813%bv : bv 32).
Proof. ftac. Qed.
Lemma D_078 : decode_any (0x00300813%bv : bv 32) = Some (OpImm ALU_ADD 16 0 3, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_07c : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x7c)) = Some (0x11078e63%bv : bv 32).
Proof. ftac. Qed.
Lemma D_07c : decode_any (0x11078e63%bv : bv 32) = Some (Branch BC_EQ 15 16 284, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_080 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x80)) = Some (0x00200813%bv : bv 32).
Proof. ftac. Qed.
Lemma D_080 : decode_any (0x00200813%bv : bv 32) = Some (OpImm ALU_ADD 16 0 2, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_084 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x84)) = Some (0x19079c63%bv : bv 32).
Proof. ftac. Qed.
Lemma D_084 : decode_any (0x19079c63%bv : bv 32) = Some (Branch BC_NE 15 16 408, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_088 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x88)) = Some (0x00875793%bv : bv 32).
Proof. ftac. Qed.
Lemma D_088 : decode_any (0x00875793%bv : bv 32) = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_08c : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x8c)) = Some (0xffe60613%bv : bv 32).
Proof. ftac. Qed.
Lemma D_08c : decode_any (0xffe60613%bv : bv 32) = Some (OpImm ALU_ADD 12 12 4094, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_090 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x90)) = Some (0x00e68023%bv : bv 32).
Proof. ftac. Qed.
Lemma D_090 : decode_any (0x00e68023%bv : bv 32) = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_094 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x94)) = Some (0x00f680a3%bv : bv 32).
Proof. ftac. Qed.
Lemma D_094 : decode_any (0x00f680a3%bv : bv 32) = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_098 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x98)) = Some (0x00268693%bv : bv 32).
Proof. ftac. Qed.
Lemma D_098 : decode_any (0x00268693%bv : bv 32) = Some (OpImm ALU_ADD 13 13 2, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_09c : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x9c)) = Some (0x01058593%bv : bv 32).
Proof. ftac. Qed.
Lemma D_09c : decode_any (0x01058593%bv : bv 32) = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_0a0 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0xa0)) = Some (0x01100793%bv : bv 32).
Proof. ftac. Qed.
Lemma D_0a0 : decode_any (0x01100793%bv : bv 32) = Some (OpImm ALU_ADD 15 0 17, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_0a4 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0xa4)) = Some (0x0107581b%bv : bv 32).
Proof. ftac. Qed.
Lemma D_0a4 : decode_any (0x0107581b%bv : bv 32) = Some (ShiftImm32 ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_0a8 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0xa8)) = Some (0xff45a883%bv : bv 32).
Proof. ftac. Qed.
Lemma D_0a8 : decode_any (0xff45a883%bv : bv 32) = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_0ac : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0xac)) = Some (0xff85a283%bv : bv 32).
Proof. ftac. Qed.
Lemma D_0ac : decode_any (0xff85a283%bv : bv 32) = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_0b0 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0xb0)) = Some (0xffc5a303%bv : bv 32).
Proof. ftac. Qed.
Lemma D_0b0 : decode_any (0xffc5a303%bv : bv 32) = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_0b4 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0xb4)) = Some (0x0005a703%bv : bv 32).
Proof. ftac. Qed.
Lemma D_0b4 : decode_any (0x0005a703%bv : bv 32) = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_0b8 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0xb8)) = Some (0x01089393%bv : bv 32).
Proof. ftac. Qed.
Lemma D_0b8 : decode_any (0x01089393%bv : bv 32) = Some (ShiftImm ALU_SLL 7 17 16, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_0bc : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0xbc)) = Some (0x0108d89b%bv : bv 32).
Proof. ftac. Qed.
Lemma D_0bc : decode_any (0x0108d89b%bv : bv 32) = Some (ShiftImm32 ALU_SRL 17 17 16, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_0c0 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0xc0)) = Some (0x0103e833%bv : bv 32).
Proof. ftac. Qed.
Lemma D_0c0 : decode_any (0x0103e833%bv : bv 32) = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_0c4 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0xc4)) = Some (0x01029393%bv : bv 32).
Proof. ftac. Qed.
Lemma D_0c4 : decode_any (0x01029393%bv : bv 32) = Some (ShiftImm ALU_SLL 7 5 16, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_0c8 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0xc8)) = Some (0x0102d29b%bv : bv 32).
Proof. ftac. Qed.
Lemma D_0c8 : decode_any (0x0102d29b%bv : bv 32) = Some (ShiftImm32 ALU_SRL 5 5 16, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_0cc : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0xcc)) = Some (0x0113e8b3%bv : bv 32).
Proof. ftac. Qed.
Lemma D_0cc : decode_any (0x0113e8b3%bv : bv 32) = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_0d0 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0xd0)) = Some (0x01031393%bv : bv 32).
Proof. ftac. Qed.
Lemma D_0d0 : decode_any (0x01031393%bv : bv 32) = Some (ShiftImm ALU_SLL 7 6 16, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_0d4 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0xd4)) = Some (0x0103531b%bv : bv 32).
Proof. ftac. Qed.
Lemma D_0d4 : decode_any (0x0103531b%bv : bv 32) = Some (ShiftImm32 ALU_SRL 6 6 16, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_0d8 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0xd8)) = Some (0x0053e2b3%bv : bv 32).
Proof. ftac. Qed.
Lemma D_0d8 : decode_any (0x0053e2b3%bv : bv 32) = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_0dc : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0xdc)) = Some (0x01071393%bv : bv 32).
Proof. ftac. Qed.
Lemma D_0dc : decode_any (0x01071393%bv : bv 32) = Some (ShiftImm ALU_SLL 7 14 16, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_0e0 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0xe0)) = Some (0x0063e333%bv : bv 32).
Proof. ftac. Qed.
Lemma D_0e0 : decode_any (0x0063e333%bv : bv 32) = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_0e4 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0xe4)) = Some (0xff060613%bv : bv 32).
Proof. ftac. Qed.
Lemma D_0e4 : decode_any (0xff060613%bv : bv 32) = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_0e8 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0xe8)) = Some (0x0106a023%bv : bv 32).
Proof. ftac. Qed.
Lemma D_0e8 : decode_any (0x0106a023%bv : bv 32) = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_0ec : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0xec)) = Some (0x0116a223%bv : bv 32).
Proof. ftac. Qed.
Lemma D_0ec : decode_any (0x0116a223%bv : bv 32) = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_0f0 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0xf0)) = Some (0x0056a423%bv : bv 32).
Proof. ftac. Qed.
Lemma D_0f0 : decode_any (0x0056a423%bv : bv 32) = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_0f4 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0xf4)) = Some (0x0066a623%bv : bv 32).
Proof. ftac. Qed.
Lemma D_0f4 : decode_any (0x0066a623%bv : bv 32) = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_0f8 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0xf8)) = Some (0x01068693%bv : bv 32).
Proof. ftac. Qed.
Lemma D_0f8 : decode_any (0x01068693%bv : bv 32) = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_0fc : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0xfc)) = Some (0x01058593%bv : bv 32).
Proof. ftac. Qed.
Lemma D_0fc : decode_any (0x01058593%bv : bv 32) = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_100 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x100)) = Some (0xfac7e2e3%bv : bv 32).
Proof. ftac. Qed.
Lemma D_100 : decode_any (0xfac7e2e3%bv : bv 32) = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_104 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x104)) = Some (0xff258593%bv : bv 32).
Proof. ftac. Qed.
Lemma D_104 : decode_any (0xff258593%bv : bv 32) = Some (OpImm ALU_ADD 11 11 4082, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_108 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x108)) = Some (0x01000713%bv : bv 32).
Proof. ftac. Qed.
Lemma D_108 : decode_any (0x01000713%bv : bv 32) = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_10c : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x10c)) = Some (0xf4e66ae3%bv : bv 32).
Proof. ftac. Qed.
Lemma D_10c : decode_any (0xf4e66ae3%bv : bv 32) = Some (Branch BC_LTU 12 14 8020, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_110 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x110)) = Some (0x19c0006f%bv : bv 32).
Proof. ftac. Qed.
Lemma D_110 : decode_any (0x19c0006f%bv : bv 32) = Some (Jal 0 412, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_114 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x114)) = Some (0x00050693%bv : bv 32).
Proof. ftac. Qed.
Lemma D_114 : decode_any (0x00050693%bv : bv 32) = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_118 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x118)) = Some (0x00357793%bv : bv 32).
Proof. ftac. Qed.
Lemma D_118 : decode_any (0x00357793%bv : bv 32) = Some (OpImm ALU_AND 15 10 3, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_11c : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x11c)) = Some (0xf2079ae3%bv : bv 32).
Proof. ftac. Qed.
Lemma D_11c : decode_any (0xf2079ae3%bv : bv 32) = Some (Branch BC_NE 15 0 7988, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_120 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x120)) = Some (0x01000713%bv : bv 32).
Proof. ftac. Qed.
Lemma D_120 : decode_any (0x01000713%bv : bv 32) = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_124 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x124)) = Some (0x02e66c63%bv : bv 32).
Proof. ftac. Qed.
Lemma D_124 : decode_any (0x02e66c63%bv : bv 32) = Some (Branch BC_LTU 12 14 56, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_128 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x128)) = Some (0x00f00713%bv : bv 32).
Proof. ftac. Qed.
Lemma D_128 : decode_any (0x00f00713%bv : bv 32) = Some (OpImm ALU_ADD 14 0 15, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_12c : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x12c)) = Some (0x0005a783%bv : bv 32).
Proof. ftac. Qed.
Lemma D_12c : decode_any (0x0005a783%bv : bv 32) = Some (Load SZ4 true 15 11 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_130 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x130)) = Some (0x0045a803%bv : bv 32).
Proof. ftac. Qed.
Lemma D_130 : decode_any (0x0045a803%bv : bv 32) = Some (Load SZ4 true 16 11 4, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_134 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x134)) = Some (0x0085a883%bv : bv 32).
Proof. ftac. Qed.
Lemma D_134 : decode_any (0x0085a883%bv : bv 32) = Some (Load SZ4 true 17 11 8, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_138 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x138)) = Some (0x00c5a283%bv : bv 32).
Proof. ftac. Qed.
Lemma D_138 : decode_any (0x00c5a283%bv : bv 32) = Some (Load SZ4 true 5 11 12, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_13c : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x13c)) = Some (0x01058593%bv : bv 32).
Proof. ftac. Qed.
Lemma D_13c : decode_any (0x01058593%bv : bv 32) = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_140 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x140)) = Some (0xff060613%bv : bv 32).
Proof. ftac. Qed.
Lemma D_140 : decode_any (0xff060613%bv : bv 32) = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_144 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x144)) = Some (0x00f6a023%bv : bv 32).
Proof. ftac. Qed.
Lemma D_144 : decode_any (0x00f6a023%bv : bv 32) = Some (Store SZ4 13 15 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_148 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x148)) = Some (0x0106a223%bv : bv 32).
Proof. ftac. Qed.
Lemma D_148 : decode_any (0x0106a223%bv : bv 32) = Some (Store SZ4 13 16 4, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_14c : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x14c)) = Some (0x0116a423%bv : bv 32).
Proof. ftac. Qed.
Lemma D_14c : decode_any (0x0116a423%bv : bv 32) = Some (Store SZ4 13 17 8, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_150 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x150)) = Some (0x0056a623%bv : bv 32).
Proof. ftac. Qed.
Lemma D_150 : decode_any (0x0056a623%bv : bv 32) = Some (Store SZ4 13 5 12, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_154 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x154)) = Some (0x01068693%bv : bv 32).
Proof. ftac. Qed.
Lemma D_154 : decode_any (0x01068693%bv : bv 32) = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_158 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x158)) = Some (0xfcc76ae3%bv : bv 32).
Proof. ftac. Qed.
Lemma D_158 : decode_any (0xfcc76ae3%bv : bv 32) = Some (Branch BC_LTU 14 12 8148, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_15c : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x15c)) = Some (0x00800713%bv : bv 32).
Proof. ftac. Qed.
Lemma D_15c : decode_any (0x00800713%bv : bv 32) = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_160 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x160)) = Some (0x00e66e63%bv : bv 32).
Proof. ftac. Qed.
Lemma D_160 : decode_any (0x00e66e63%bv : bv 32) = Some (Branch BC_LTU 12 14 28, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_164 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x164)) = Some (0x0005a703%bv : bv 32).
Proof. ftac. Qed.
Lemma D_164 : decode_any (0x0005a703%bv : bv 32) = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_168 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x168)) = Some (0x0045a783%bv : bv 32).
Proof. ftac. Qed.
Lemma D_168 : decode_any (0x0045a783%bv : bv 32) = Some (Load SZ4 true 15 11 4, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_16c : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x16c)) = Some (0x00e6a023%bv : bv 32).
Proof. ftac. Qed.
Lemma D_16c : decode_any (0x00e6a023%bv : bv 32) = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_170 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x170)) = Some (0x00f6a223%bv : bv 32).
Proof. ftac. Qed.
Lemma D_170 : decode_any (0x00f6a223%bv : bv 32) = Some (Store SZ4 13 15 4, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_174 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x174)) = Some (0x00868693%bv : bv 32).
Proof. ftac. Qed.
Lemma D_174 : decode_any (0x00868693%bv : bv 32) = Some (OpImm ALU_ADD 13 13 8, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_178 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x178)) = Some (0x00858593%bv : bv 32).
Proof. ftac. Qed.
Lemma D_178 : decode_any (0x00858593%bv : bv 32) = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_17c : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x17c)) = Some (0x00467713%bv : bv 32).
Proof. ftac. Qed.
Lemma D_17c : decode_any (0x00467713%bv : bv 32) = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_180 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x180)) = Some (0x24070063%bv : bv 32).
Proof. ftac. Qed.
Lemma D_180 : decode_any (0x24070063%bv : bv 32) = Some (Branch BC_EQ 14 0 576, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_184 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x184)) = Some (0x0005a703%bv : bv 32).
Proof. ftac. Qed.
Lemma D_184 : decode_any (0x0005a703%bv : bv 32) = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_188 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x188)) = Some (0x00458593%bv : bv 32).
Proof. ftac. Qed.
Lemma D_188 : decode_any (0x00458593%bv : bv 32) = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_18c : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x18c)) = Some (0x00e6a023%bv : bv 32).
Proof. ftac. Qed.
Lemma D_18c : decode_any (0x00e6a023%bv : bv 32) = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_190 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x190)) = Some (0x00468693%bv : bv 32).
Proof. ftac. Qed.
Lemma D_190 : decode_any (0x00468693%bv : bv 32) = Some (OpImm ALU_ADD 13 13 4, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_194 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x194)) = Some (0x22c0006f%bv : bv 32).
Proof. ftac. Qed.
Lemma D_194 : decode_any (0x22c0006f%bv : bv 32) = Some (Jal 0 556, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_198 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x198)) = Some (0x00e68023%bv : bv 32).
Proof. ftac. Qed.
Lemma D_198 : decode_any (0x00e68023%bv : bv 32) = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_19c : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x19c)) = Some (0x00168693%bv : bv 32).
Proof. ftac. Qed.
Lemma D_19c : decode_any (0x00168693%bv : bv 32) = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_1a0 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x1a0)) = Some (0xfff60613%bv : bv 32).
Proof. ftac. Qed.
Lemma D_1a0 : decode_any (0xfff60613%bv : bv 32) = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_1a4 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x1a4)) = Some (0x01058593%bv : bv 32).
Proof. ftac. Qed.
Lemma D_1a4 : decode_any (0x01058593%bv : bv 32) = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_1a8 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x1a8)) = Some (0x01200793%bv : bv 32).
Proof. ftac. Qed.
Lemma D_1a8 : decode_any (0x01200793%bv : bv 32) = Some (OpImm ALU_ADD 15 0 18, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_1ac : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x1ac)) = Some (0x0087581b%bv : bv 32).
Proof. ftac. Qed.
Lemma D_1ac : decode_any (0x0087581b%bv : bv 32) = Some (ShiftImm32 ALU_SRL 16 14 8, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_1b0 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x1b0)) = Some (0xff45a883%bv : bv 32).
Proof. ftac. Qed.
Lemma D_1b0 : decode_any (0xff45a883%bv : bv 32) = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_1b4 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x1b4)) = Some (0xff85a283%bv : bv 32).
Proof. ftac. Qed.
Lemma D_1b4 : decode_any (0xff85a283%bv : bv 32) = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_1b8 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x1b8)) = Some (0xffc5a303%bv : bv 32).
Proof. ftac. Qed.
Lemma D_1b8 : decode_any (0xffc5a303%bv : bv 32) = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_1bc : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x1bc)) = Some (0x0005a703%bv : bv 32).
Proof. ftac. Qed.
Lemma D_1bc : decode_any (0x0005a703%bv : bv 32) = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_1c0 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x1c0)) = Some (0x01889393%bv : bv 32).
Proof. ftac. Qed.
Lemma D_1c0 : decode_any (0x01889393%bv : bv 32) = Some (ShiftImm ALU_SLL 7 17 24, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_1c4 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x1c4)) = Some (0x0088d89b%bv : bv 32).
Proof. ftac. Qed.
Lemma D_1c4 : decode_any (0x0088d89b%bv : bv 32) = Some (ShiftImm32 ALU_SRL 17 17 8, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_1c8 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x1c8)) = Some (0x0103e833%bv : bv 32).
Proof. ftac. Qed.
Lemma D_1c8 : decode_any (0x0103e833%bv : bv 32) = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_1cc : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x1cc)) = Some (0x01829393%bv : bv 32).
Proof. ftac. Qed.
Lemma D_1cc : decode_any (0x01829393%bv : bv 32) = Some (ShiftImm ALU_SLL 7 5 24, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_1d0 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x1d0)) = Some (0x0082d29b%bv : bv 32).
Proof. ftac. Qed.
Lemma D_1d0 : decode_any (0x0082d29b%bv : bv 32) = Some (ShiftImm32 ALU_SRL 5 5 8, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_1d4 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x1d4)) = Some (0x0113e8b3%bv : bv 32).
Proof. ftac. Qed.
Lemma D_1d4 : decode_any (0x0113e8b3%bv : bv 32) = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_1d8 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x1d8)) = Some (0x01831393%bv : bv 32).
Proof. ftac. Qed.
Lemma D_1d8 : decode_any (0x01831393%bv : bv 32) = Some (ShiftImm ALU_SLL 7 6 24, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_1dc : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x1dc)) = Some (0x0083531b%bv : bv 32).
Proof. ftac. Qed.
Lemma D_1dc : decode_any (0x0083531b%bv : bv 32) = Some (ShiftImm32 ALU_SRL 6 6 8, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_1e0 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x1e0)) = Some (0x0053e2b3%bv : bv 32).
Proof. ftac. Qed.
Lemma D_1e0 : decode_any (0x0053e2b3%bv : bv 32) = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_1e4 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x1e4)) = Some (0x01871393%bv : bv 32).
Proof. ftac. Qed.
Lemma D_1e4 : decode_any (0x01871393%bv : bv 32) = Some (ShiftImm ALU_SLL 7 14 24, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_1e8 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x1e8)) = Some (0x0063e333%bv : bv 32).
Proof. ftac. Qed.
Lemma D_1e8 : decode_any (0x0063e333%bv : bv 32) = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_1ec : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x1ec)) = Some (0xff060613%bv : bv 32).
Proof. ftac. Qed.
Lemma D_1ec : decode_any (0xff060613%bv : bv 32) = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_1f0 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x1f0)) = Some (0x0106a023%bv : bv 32).
Proof. ftac. Qed.
Lemma D_1f0 : decode_any (0x0106a023%bv : bv 32) = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_1f4 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x1f4)) = Some (0x0116a223%bv : bv 32).
Proof. ftac. Qed.
Lemma D_1f4 : decode_any (0x0116a223%bv : bv 32) = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_1f8 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x1f8)) = Some (0x0056a423%bv : bv 32).
Proof. ftac. Qed.
Lemma D_1f8 : decode_any (0x0056a423%bv : bv 32) = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_1fc : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x1fc)) = Some (0x0066a623%bv : bv 32).
Proof. ftac. Qed.
Lemma D_1fc : decode_any (0x0066a623%bv : bv 32) = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_200 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x200)) = Some (0x01068693%bv : bv 32).
Proof. ftac. Qed.
Lemma D_200 : decode_any (0x01068693%bv : bv 32) = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_204 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x204)) = Some (0x01058593%bv : bv 32).
Proof. ftac. Qed.
Lemma D_204 : decode_any (0x01058593%bv : bv 32) = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_208 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x208)) = Some (0xfac7e2e3%bv : bv 32).
Proof. ftac. Qed.
Lemma D_208 : decode_any (0xfac7e2e3%bv : bv 32) = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_20c : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x20c)) = Some (0xff158593%bv : bv 32).
Proof. ftac. Qed.
Lemma D_20c : decode_any (0xff158593%bv : bv 32) = Some (OpImm ALU_ADD 11 11 4081, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_210 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x210)) = Some (0x01000713%bv : bv 32).
Proof. ftac. Qed.
Lemma D_210 : decode_any (0x01000713%bv : bv 32) = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_214 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x214)) = Some (0xe4e666e3%bv : bv 32).
Proof. ftac. Qed.
Lemma D_214 : decode_any (0xe4e666e3%bv : bv 32) = Some (Branch BC_LTU 12 14 7756, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_218 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x218)) = Some (0x0940006f%bv : bv 32).
Proof. ftac. Qed.
Lemma D_218 : decode_any (0x0940006f%bv : bv 32) = Some (Jal 0 148, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_21c : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x21c)) = Some (0x00875793%bv : bv 32).
Proof. ftac. Qed.
Lemma D_21c : decode_any (0x00875793%bv : bv 32) = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_220 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x220)) = Some (0x01075813%bv : bv 32).
Proof. ftac. Qed.
Lemma D_220 : decode_any (0x01075813%bv : bv 32) = Some (ShiftImm ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_224 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x224)) = Some (0xffd60613%bv : bv 32).
Proof. ftac. Qed.
Lemma D_224 : decode_any (0xffd60613%bv : bv 32) = Some (OpImm ALU_ADD 12 12 4093, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_228 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x228)) = Some (0x00e68023%bv : bv 32).
Proof. ftac. Qed.
Lemma D_228 : decode_any (0x00e68023%bv : bv 32) = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_22c : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x22c)) = Some (0x00f680a3%bv : bv 32).
Proof. ftac. Qed.
Lemma D_22c : decode_any (0x00f680a3%bv : bv 32) = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_230 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x230)) = Some (0x01068123%bv : bv 32).
Proof. ftac. Qed.
Lemma D_230 : decode_any (0x01068123%bv : bv 32) = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_234 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x234)) = Some (0x00368693%bv : bv 32).
Proof. ftac. Qed.
Lemma D_234 : decode_any (0x00368693%bv : bv 32) = Some (OpImm ALU_ADD 13 13 3, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_238 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x238)) = Some (0x01058593%bv : bv 32).
Proof. ftac. Qed.
Lemma D_238 : decode_any (0x01058593%bv : bv 32) = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_23c : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x23c)) = Some (0x01000793%bv : bv 32).
Proof. ftac. Qed.
Lemma D_23c : decode_any (0x01000793%bv : bv 32) = Some (OpImm ALU_ADD 15 0 16, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_240 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x240)) = Some (0x0187581b%bv : bv 32).
Proof. ftac. Qed.
Lemma D_240 : decode_any (0x0187581b%bv : bv 32) = Some (ShiftImm32 ALU_SRL 16 14 24, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_244 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x244)) = Some (0xff45a883%bv : bv 32).
Proof. ftac. Qed.
Lemma D_244 : decode_any (0xff45a883%bv : bv 32) = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_248 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x248)) = Some (0xff85a283%bv : bv 32).
Proof. ftac. Qed.
Lemma D_248 : decode_any (0xff85a283%bv : bv 32) = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_24c : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x24c)) = Some (0xffc5a303%bv : bv 32).
Proof. ftac. Qed.
Lemma D_24c : decode_any (0xffc5a303%bv : bv 32) = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_250 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x250)) = Some (0x0005a703%bv : bv 32).
Proof. ftac. Qed.
Lemma D_250 : decode_any (0x0005a703%bv : bv 32) = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_254 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x254)) = Some (0x00889393%bv : bv 32).
Proof. ftac. Qed.
Lemma D_254 : decode_any (0x00889393%bv : bv 32) = Some (ShiftImm ALU_SLL 7 17 8, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_258 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x258)) = Some (0x0188d89b%bv : bv 32).
Proof. ftac. Qed.
Lemma D_258 : decode_any (0x0188d89b%bv : bv 32) = Some (ShiftImm32 ALU_SRL 17 17 24, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_25c : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x25c)) = Some (0x0103e833%bv : bv 32).
Proof. ftac. Qed.
Lemma D_25c : decode_any (0x0103e833%bv : bv 32) = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_260 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x260)) = Some (0x00829393%bv : bv 32).
Proof. ftac. Qed.
Lemma D_260 : decode_any (0x00829393%bv : bv 32) = Some (ShiftImm ALU_SLL 7 5 8, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_264 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x264)) = Some (0x0182d29b%bv : bv 32).
Proof. ftac. Qed.
Lemma D_264 : decode_any (0x0182d29b%bv : bv 32) = Some (ShiftImm32 ALU_SRL 5 5 24, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_268 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x268)) = Some (0x0113e8b3%bv : bv 32).
Proof. ftac. Qed.
Lemma D_268 : decode_any (0x0113e8b3%bv : bv 32) = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_26c : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x26c)) = Some (0x00831393%bv : bv 32).
Proof. ftac. Qed.
Lemma D_26c : decode_any (0x00831393%bv : bv 32) = Some (ShiftImm ALU_SLL 7 6 8, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_270 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x270)) = Some (0x0183531b%bv : bv 32).
Proof. ftac. Qed.
Lemma D_270 : decode_any (0x0183531b%bv : bv 32) = Some (ShiftImm32 ALU_SRL 6 6 24, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_274 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x274)) = Some (0x0053e2b3%bv : bv 32).
Proof. ftac. Qed.
Lemma D_274 : decode_any (0x0053e2b3%bv : bv 32) = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_278 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x278)) = Some (0x00871393%bv : bv 32).
Proof. ftac. Qed.
Lemma D_278 : decode_any (0x00871393%bv : bv 32) = Some (ShiftImm ALU_SLL 7 14 8, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_27c : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x27c)) = Some (0x0063e333%bv : bv 32).
Proof. ftac. Qed.
Lemma D_27c : decode_any (0x0063e333%bv : bv 32) = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_280 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x280)) = Some (0xff060613%bv : bv 32).
Proof. ftac. Qed.
Lemma D_280 : decode_any (0xff060613%bv : bv 32) = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_284 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x284)) = Some (0x0106a023%bv : bv 32).
Proof. ftac. Qed.
Lemma D_284 : decode_any (0x0106a023%bv : bv 32) = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_288 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x288)) = Some (0x0116a223%bv : bv 32).
Proof. ftac. Qed.
Lemma D_288 : decode_any (0x0116a223%bv : bv 32) = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_28c : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x28c)) = Some (0x0056a423%bv : bv 32).
Proof. ftac. Qed.
Lemma D_28c : decode_any (0x0056a423%bv : bv 32) = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_290 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x290)) = Some (0x0066a623%bv : bv 32).
Proof. ftac. Qed.
Lemma D_290 : decode_any (0x0066a623%bv : bv 32) = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_294 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x294)) = Some (0x01068693%bv : bv 32).
Proof. ftac. Qed.
Lemma D_294 : decode_any (0x01068693%bv : bv 32) = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_298 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x298)) = Some (0x01058593%bv : bv 32).
Proof. ftac. Qed.
Lemma D_298 : decode_any (0x01058593%bv : bv 32) = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_29c : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x29c)) = Some (0xfac7e2e3%bv : bv 32).
Proof. ftac. Qed.
Lemma D_29c : decode_any (0xfac7e2e3%bv : bv 32) = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_2a0 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x2a0)) = Some (0xff358593%bv : bv 32).
Proof. ftac. Qed.
Lemma D_2a0 : decode_any (0xff358593%bv : bv 32) = Some (OpImm ALU_ADD 11 11 4083, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_2a4 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x2a4)) = Some (0x01000713%bv : bv 32).
Proof. ftac. Qed.
Lemma D_2a4 : decode_any (0x01000713%bv : bv 32) = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_2a8 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x2a8)) = Some (0xdae66ce3%bv : bv 32).
Proof. ftac. Qed.
Lemma D_2a8 : decode_any (0xdae66ce3%bv : bv 32) = Some (Branch BC_LTU 12 14 7608, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_2ac : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x2ac)) = Some (0x0005c703%bv : bv 32).
Proof. ftac. Qed.
Lemma D_2ac : decode_any (0x0005c703%bv : bv 32) = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_2b0 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x2b0)) = Some (0x0015c783%bv : bv 32).
Proof. ftac. Qed.
Lemma D_2b0 : decode_any (0x0015c783%bv : bv 32) = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_2b4 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x2b4)) = Some (0x0025c803%bv : bv 32).
Proof. ftac. Qed.
Lemma D_2b4 : decode_any (0x0025c803%bv : bv 32) = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_2b8 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x2b8)) = Some (0x0035c883%bv : bv 32).
Proof. ftac. Qed.
Lemma D_2b8 : decode_any (0x0035c883%bv : bv 32) = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_2bc : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x2bc)) = Some (0x0045c283%bv : bv 32).
Proof. ftac. Qed.
Lemma D_2bc : decode_any (0x0045c283%bv : bv 32) = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_2c0 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x2c0)) = Some (0x0055c303%bv : bv 32).
Proof. ftac. Qed.
Lemma D_2c0 : decode_any (0x0055c303%bv : bv 32) = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_2c4 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x2c4)) = Some (0x0065c383%bv : bv 32).
Proof. ftac. Qed.
Lemma D_2c4 : decode_any (0x0065c383%bv : bv 32) = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_2c8 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x2c8)) = Some (0x0075ce03%bv : bv 32).
Proof. ftac. Qed.
Lemma D_2c8 : decode_any (0x0075ce03%bv : bv 32) = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_2cc : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x2cc)) = Some (0x00e68023%bv : bv 32).
Proof. ftac. Qed.
Lemma D_2cc : decode_any (0x00e68023%bv : bv 32) = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_2d0 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x2d0)) = Some (0x00f680a3%bv : bv 32).
Proof. ftac. Qed.
Lemma D_2d0 : decode_any (0x00f680a3%bv : bv 32) = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_2d4 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x2d4)) = Some (0x01068123%bv : bv 32).
Proof. ftac. Qed.
Lemma D_2d4 : decode_any (0x01068123%bv : bv 32) = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_2d8 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x2d8)) = Some (0x011681a3%bv : bv 32).
Proof. ftac. Qed.
Lemma D_2d8 : decode_any (0x011681a3%bv : bv 32) = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_2dc : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x2dc)) = Some (0x0085c703%bv : bv 32).
Proof. ftac. Qed.
Lemma D_2dc : decode_any (0x0085c703%bv : bv 32) = Some (Load SZ1 false 14 11 8, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_2e0 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x2e0)) = Some (0x0095c783%bv : bv 32).
Proof. ftac. Qed.
Lemma D_2e0 : decode_any (0x0095c783%bv : bv 32) = Some (Load SZ1 false 15 11 9, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_2e4 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x2e4)) = Some (0x00a5c803%bv : bv 32).
Proof. ftac. Qed.
Lemma D_2e4 : decode_any (0x00a5c803%bv : bv 32) = Some (Load SZ1 false 16 11 10, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_2e8 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x2e8)) = Some (0x00b5c883%bv : bv 32).
Proof. ftac. Qed.
Lemma D_2e8 : decode_any (0x00b5c883%bv : bv 32) = Some (Load SZ1 false 17 11 11, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_2ec : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x2ec)) = Some (0x00568223%bv : bv 32).
Proof. ftac. Qed.
Lemma D_2ec : decode_any (0x00568223%bv : bv 32) = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_2f0 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x2f0)) = Some (0x006682a3%bv : bv 32).
Proof. ftac. Qed.
Lemma D_2f0 : decode_any (0x006682a3%bv : bv 32) = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_2f4 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x2f4)) = Some (0x00768323%bv : bv 32).
Proof. ftac. Qed.
Lemma D_2f4 : decode_any (0x00768323%bv : bv 32) = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_2f8 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x2f8)) = Some (0x01c683a3%bv : bv 32).
Proof. ftac. Qed.
Lemma D_2f8 : decode_any (0x01c683a3%bv : bv 32) = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_2fc : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x2fc)) = Some (0x00c5c283%bv : bv 32).
Proof. ftac. Qed.
Lemma D_2fc : decode_any (0x00c5c283%bv : bv 32) = Some (Load SZ1 false 5 11 12, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_300 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x300)) = Some (0x00d5c303%bv : bv 32).
Proof. ftac. Qed.
Lemma D_300 : decode_any (0x00d5c303%bv : bv 32) = Some (Load SZ1 false 6 11 13, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_304 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x304)) = Some (0x00e5c383%bv : bv 32).
Proof. ftac. Qed.
Lemma D_304 : decode_any (0x00e5c383%bv : bv 32) = Some (Load SZ1 false 7 11 14, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_308 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x308)) = Some (0x00f5ce03%bv : bv 32).
Proof. ftac. Qed.
Lemma D_308 : decode_any (0x00f5ce03%bv : bv 32) = Some (Load SZ1 false 28 11 15, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_30c : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x30c)) = Some (0x01058593%bv : bv 32).
Proof. ftac. Qed.
Lemma D_30c : decode_any (0x01058593%bv : bv 32) = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_310 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x310)) = Some (0x00e68423%bv : bv 32).
Proof. ftac. Qed.
Lemma D_310 : decode_any (0x00e68423%bv : bv 32) = Some (Store SZ1 13 14 8, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_314 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x314)) = Some (0x00f684a3%bv : bv 32).
Proof. ftac. Qed.
Lemma D_314 : decode_any (0x00f684a3%bv : bv 32) = Some (Store SZ1 13 15 9, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_318 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x318)) = Some (0x01068523%bv : bv 32).
Proof. ftac. Qed.
Lemma D_318 : decode_any (0x01068523%bv : bv 32) = Some (Store SZ1 13 16 10, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_31c : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x31c)) = Some (0x011685a3%bv : bv 32).
Proof. ftac. Qed.
Lemma D_31c : decode_any (0x011685a3%bv : bv 32) = Some (Store SZ1 13 17 11, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_320 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x320)) = Some (0x01068713%bv : bv 32).
Proof. ftac. Qed.
Lemma D_320 : decode_any (0x01068713%bv : bv 32) = Some (OpImm ALU_ADD 14 13 16, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_324 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x324)) = Some (0x00568623%bv : bv 32).
Proof. ftac. Qed.
Lemma D_324 : decode_any (0x00568623%bv : bv 32) = Some (Store SZ1 13 5 12, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_328 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x328)) = Some (0x006686a3%bv : bv 32).
Proof. ftac. Qed.
Lemma D_328 : decode_any (0x006686a3%bv : bv 32) = Some (Store SZ1 13 6 13, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_32c : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x32c)) = Some (0x00768723%bv : bv 32).
Proof. ftac. Qed.
Lemma D_32c : decode_any (0x00768723%bv : bv 32) = Some (Store SZ1 13 7 14, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_330 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x330)) = Some (0x01c687a3%bv : bv 32).
Proof. ftac. Qed.
Lemma D_330 : decode_any (0x01c687a3%bv : bv 32) = Some (Store SZ1 13 28 15, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_334 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x334)) = Some (0x00070693%bv : bv 32).
Proof. ftac. Qed.
Lemma D_334 : decode_any (0x00070693%bv : bv 32) = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_338 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x338)) = Some (0x00867713%bv : bv 32).
Proof. ftac. Qed.
Lemma D_338 : decode_any (0x00867713%bv : bv 32) = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_33c : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x33c)) = Some (0xd20706e3%bv : bv 32).
Proof. ftac. Qed.
Lemma D_33c : decode_any (0xd20706e3%bv : bv 32) = Some (Branch BC_EQ 14 0 7468, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_340 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x340)) = Some (0x0005c703%bv : bv 32).
Proof. ftac. Qed.
Lemma D_340 : decode_any (0x0005c703%bv : bv 32) = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_344 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x344)) = Some (0x0015c783%bv : bv 32).
Proof. ftac. Qed.
Lemma D_344 : decode_any (0x0015c783%bv : bv 32) = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_348 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x348)) = Some (0x0025c803%bv : bv 32).
Proof. ftac. Qed.
Lemma D_348 : decode_any (0x0025c803%bv : bv 32) = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_34c : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x34c)) = Some (0x0035c883%bv : bv 32).
Proof. ftac. Qed.
Lemma D_34c : decode_any (0x0035c883%bv : bv 32) = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_350 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x350)) = Some (0x0045c283%bv : bv 32).
Proof. ftac. Qed.
Lemma D_350 : decode_any (0x0045c283%bv : bv 32) = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_354 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x354)) = Some (0x0055c303%bv : bv 32).
Proof. ftac. Qed.
Lemma D_354 : decode_any (0x0055c303%bv : bv 32) = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_358 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x358)) = Some (0x0065c383%bv : bv 32).
Proof. ftac. Qed.
Lemma D_358 : decode_any (0x0065c383%bv : bv 32) = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_35c : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x35c)) = Some (0x0075ce03%bv : bv 32).
Proof. ftac. Qed.
Lemma D_35c : decode_any (0x0075ce03%bv : bv 32) = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_360 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x360)) = Some (0x00858593%bv : bv 32).
Proof. ftac. Qed.
Lemma D_360 : decode_any (0x00858593%bv : bv 32) = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_364 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x364)) = Some (0x00e68023%bv : bv 32).
Proof. ftac. Qed.
Lemma D_364 : decode_any (0x00e68023%bv : bv 32) = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_368 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x368)) = Some (0x00f680a3%bv : bv 32).
Proof. ftac. Qed.
Lemma D_368 : decode_any (0x00f680a3%bv : bv 32) = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_36c : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x36c)) = Some (0x01068123%bv : bv 32).
Proof. ftac. Qed.
Lemma D_36c : decode_any (0x01068123%bv : bv 32) = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_370 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x370)) = Some (0x011681a3%bv : bv 32).
Proof. ftac. Qed.
Lemma D_370 : decode_any (0x011681a3%bv : bv 32) = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_374 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x374)) = Some (0x00868713%bv : bv 32).
Proof. ftac. Qed.
Lemma D_374 : decode_any (0x00868713%bv : bv 32) = Some (OpImm ALU_ADD 14 13 8, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_378 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x378)) = Some (0x00568223%bv : bv 32).
Proof. ftac. Qed.
Lemma D_378 : decode_any (0x00568223%bv : bv 32) = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_37c : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x37c)) = Some (0x006682a3%bv : bv 32).
Proof. ftac. Qed.
Lemma D_37c : decode_any (0x006682a3%bv : bv 32) = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_380 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x380)) = Some (0x00768323%bv : bv 32).
Proof. ftac. Qed.
Lemma D_380 : decode_any (0x00768323%bv : bv 32) = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_384 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x384)) = Some (0x01c683a3%bv : bv 32).
Proof. ftac. Qed.
Lemma D_384 : decode_any (0x01c683a3%bv : bv 32) = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_388 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x388)) = Some (0x00070693%bv : bv 32).
Proof. ftac. Qed.
Lemma D_388 : decode_any (0x00070693%bv : bv 32) = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_38c : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x38c)) = Some (0x00467713%bv : bv 32).
Proof. ftac. Qed.
Lemma D_38c : decode_any (0x00467713%bv : bv 32) = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_390 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x390)) = Some (0x02070863%bv : bv 32).
Proof. ftac. Qed.
Lemma D_390 : decode_any (0x02070863%bv : bv 32) = Some (Branch BC_EQ 14 0 48, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_394 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x394)) = Some (0x0005c703%bv : bv 32).
Proof. ftac. Qed.
Lemma D_394 : decode_any (0x0005c703%bv : bv 32) = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_398 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x398)) = Some (0x0015c783%bv : bv 32).
Proof. ftac. Qed.
Lemma D_398 : decode_any (0x0015c783%bv : bv 32) = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_39c : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x39c)) = Some (0x0025c803%bv : bv 32).
Proof. ftac. Qed.
Lemma D_39c : decode_any (0x0025c803%bv : bv 32) = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_3a0 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x3a0)) = Some (0x0035c883%bv : bv 32).
Proof. ftac. Qed.
Lemma D_3a0 : decode_any (0x0035c883%bv : bv 32) = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_3a4 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x3a4)) = Some (0x00458593%bv : bv 32).
Proof. ftac. Qed.
Lemma D_3a4 : decode_any (0x00458593%bv : bv 32) = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_3a8 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x3a8)) = Some (0x00468293%bv : bv 32).
Proof. ftac. Qed.
Lemma D_3a8 : decode_any (0x00468293%bv : bv 32) = Some (OpImm ALU_ADD 5 13 4, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_3ac : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x3ac)) = Some (0x00e68023%bv : bv 32).
Proof. ftac. Qed.
Lemma D_3ac : decode_any (0x00e68023%bv : bv 32) = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_3b0 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x3b0)) = Some (0x00f680a3%bv : bv 32).
Proof. ftac. Qed.
Lemma D_3b0 : decode_any (0x00f680a3%bv : bv 32) = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_3b4 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x3b4)) = Some (0x01068123%bv : bv 32).
Proof. ftac. Qed.
Lemma D_3b4 : decode_any (0x01068123%bv : bv 32) = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_3b8 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x3b8)) = Some (0x011681a3%bv : bv 32).
Proof. ftac. Qed.
Lemma D_3b8 : decode_any (0x011681a3%bv : bv 32) = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_3bc : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x3bc)) = Some (0x00028693%bv : bv 32).
Proof. ftac. Qed.
Lemma D_3bc : decode_any (0x00028693%bv : bv 32) = Some (OpImm ALU_ADD 13 5 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_3c0 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x3c0)) = Some (0x00267713%bv : bv 32).
Proof. ftac. Qed.
Lemma D_3c0 : decode_any (0x00267713%bv : bv 32) = Some (OpImm ALU_AND 14 12 2, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_3c4 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x3c4)) = Some (0x00071863%bv : bv 32).
Proof. ftac. Qed.
Lemma D_3c4 : decode_any (0x00071863%bv : bv 32) = Some (Branch BC_NE 14 0 16, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_3c8 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x3c8)) = Some (0x00167613%bv : bv 32).
Proof. ftac. Qed.
Lemma D_3c8 : decode_any (0x00167613%bv : bv 32) = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_3cc : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x3cc)) = Some (0x02061663%bv : bv 32).
Proof. ftac. Qed.
Lemma D_3cc : decode_any (0x02061663%bv : bv 32) = Some (Branch BC_NE 12 0 44, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_3d0 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x3d0)) = Some (0x00008067%bv : bv 32).
Proof. ftac. Qed.
Lemma D_3d0 : decode_any (0x00008067%bv : bv 32) = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_3d4 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x3d4)) = Some (0x0005c703%bv : bv 32).
Proof. ftac. Qed.
Lemma D_3d4 : decode_any (0x0005c703%bv : bv 32) = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_3d8 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x3d8)) = Some (0x0015c783%bv : bv 32).
Proof. ftac. Qed.
Lemma D_3d8 : decode_any (0x0015c783%bv : bv 32) = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_3dc : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x3dc)) = Some (0x00258593%bv : bv 32).
Proof. ftac. Qed.
Lemma D_3dc : decode_any (0x00258593%bv : bv 32) = Some (OpImm ALU_ADD 11 11 2, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_3e0 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x3e0)) = Some (0x00268813%bv : bv 32).
Proof. ftac. Qed.
Lemma D_3e0 : decode_any (0x00268813%bv : bv 32) = Some (OpImm ALU_ADD 16 13 2, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_3e4 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x3e4)) = Some (0x00e68023%bv : bv 32).
Proof. ftac. Qed.
Lemma D_3e4 : decode_any (0x00e68023%bv : bv 32) = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_3e8 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x3e8)) = Some (0x00f680a3%bv : bv 32).
Proof. ftac. Qed.
Lemma D_3e8 : decode_any (0x00f680a3%bv : bv 32) = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_3ec : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x3ec)) = Some (0x00080693%bv : bv 32).
Proof. ftac. Qed.
Lemma D_3ec : decode_any (0x00080693%bv : bv 32) = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_3f0 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x3f0)) = Some (0x00167613%bv : bv 32).
Proof. ftac. Qed.
Lemma D_3f0 : decode_any (0x00167613%bv : bv 32) = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_3f4 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x3f4)) = Some (0xfc060ee3%bv : bv 32).
Proof. ftac. Qed.
Lemma D_3f4 : decode_any (0xfc060ee3%bv : bv 32) = Some (Branch BC_EQ 12 0 8156, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_3f8 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x3f8)) = Some (0x0005c583%bv : bv 32).
Proof. ftac. Qed.
Lemma D_3f8 : decode_any (0x0005c583%bv : bv 32) = Some (Load SZ1 false 11 11 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_3fc : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x3fc)) = Some (0x00b68023%bv : bv 32).
Proof. ftac. Qed.
Lemma D_3fc : decode_any (0x00b68023%bv : bv 32) = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_400 : fetch_word src0segs (Z_to_bv 64 (src0_A_memcpy + 0x400)) = Some (0x00008067%bv : bv 32).
Proof. ftac. Qed.
Lemma D_400 : decode_any (0x00008067%bv : bv 32) = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl_bv. Qed.
Section f.
Variable bs : list byte.
Variables d s : word.
Variables mem rom : word -> option byte.
Definition D : Z := bv_unsigned d.
Definition S : Z := bv_unsigned s.
Hypothesis Hsrc : rdn src0segs mem s (length bs) = Some bs.
Hypothesis Hdst : store_ok src0segs mem d (length bs) = true.
Hypothesis Hnd : bv_unsigned d + Z.of_nat (length bs) <= 2^64.
Hypothesis Hns : bv_unsigned s + Z.of_nat (length bs) <= 2^64.
Hypothesis Hdisj : bv_unsigned d + Z.of_nat (length bs) <= bv_unsigned s
\/ bv_unsigned s + Z.of_nat (length bs) <= bv_unsigned d.
Definition M (i : nat) : word -> option byte := wbytes mem d (firstn i bs).
Definition chunk (i k : nat) : list byte := firstn k (skipn i bs).
Lemma DS_facts : D = bv_unsigned d /\ S = bv_unsigned s /\ 0 <= bv_unsigned d < 2^64 /\ 0 <= bv_unsigned s < 2^64.
Proof. pose proof (u64_range d). pose proof (u64_range s). unfold D, S. lia. Qed.
Ltac dsl := pose proof DS_facts as HDS; destruct HDS as (HD_ & HS_ & HDr & HSr).
Lemma chunk_len : forall i k, (i + k <= length bs)%nat -> length (chunk i k) = k.
Proof. intros i k H. unfold chunk. rewrite length_firstn, length_skipn. lia. Qed.
Lemma chunk1 : forall i, (i < length bs)%nat -> chunk i 1 = [nth i bs NUL].
Proof. intros i Hi. unfold chunk. rewrite (skipn_nth bs i NUL Hi). reflexivity. Qed.
Lemma nth_firstn' : forall {A} (l : list A) k j (x : A), (j < k)%nat -> nth j (firstn k l) x = nth j l x.
Proof.
intros A l k; revert l. induction k as [|k IH]; intros l j x Hj; [lia|].
destruct l as [|a l]; [destruct j; reflexivity|].
destruct j as [|j]; [reflexivity|]. cbn. apply IH. lia.
Qed.
Lemma nth_chunk : forall i k j, (j < k)%nat ->
nth j (chunk i k) NUL = nth (i + j) bs NUL.
Proof.
intros i k j Hj. unfold chunk. rewrite nth_firstn' by exact Hj.
rewrite nth_skipn. reflexivity.
Qed.
Lemma chunk_shift : forall i p, (p <= 4)%nat ->
chunk (i + p) 4 = skipn p (chunk i 4) ++ firstn p (chunk (i + 4) 4).
Proof.
intros i p Hp. unfold chunk.
rewrite skipn_firstn_comm, skipn_skipn, firstn_firstn.
replace (Init.Nat.min p 4) with p by lia.
rewrite (Nat.add_comm p i).
replace (firstn 4 (skipn (i + p) bs)) with (firstn (4 - p + p) (skipn (i + p) bs)) by (f_equal; lia).
rewrite <- (firstn_app_firstn_skipn (skipn (i + p) bs) (4 - p) p).
rewrite skipn_skipn. replace (4 - p + (i + p))%nat with (i + 4)%nat by lia.
reflexivity.
Qed.
Lemma src_read : forall j i k, (0 < k)%nat -> (i + k <= length bs)%nat ->
rdn src0segs (M j) (Z_to_bv 64 (S + Z.of_nat i)) k = Some (chunk i k).
Proof.
intros j i k Hk Hik. dsl. unfold M.
pose proof (length_firstn j bs) as Hl'.
rewrite rdn_wbytes_out.
- replace (Z_to_bv 64 (S + Z.of_nat i)) with (s + nat_to_word i)%bv
by (rewrite word_add_nat; f_equal; lia).
unfold chunk. eapply rdn_sub; [exact Hsrc | exact Hik].
- rewrite u_Z2bv by lia. rewrite length_firstn. lia.
- rewrite u_Z2bv by lia. lia.
- rewrite length_firstn. lia.
Qed.
Lemma src_read1 : forall j a i, a = S + Z.of_nat i -> (i < length bs)%nat ->
rdn src0segs (M j) (Z_to_bv 64 a) 1 = Some [nth i bs NUL].
Proof. intros j a i -> Hi. rewrite <- chunk1 by exact Hi. apply src_read; lia. Qed.
Lemma src_read4 : forall j a i, a = S + Z.of_nat i -> (i + 4 <= length bs)%nat ->
rdn src0segs (M j) (Z_to_bv 64 a) 4 = Some (chunk i 4).
Proof. intros j a i -> Hi. apply src_read; lia. Qed.
Lemma dst_ok : forall j a i k, a = D + Z.of_nat i -> (0 < k)%nat -> (i + k <= length bs)%nat ->
store_ok src0segs (M j) (Z_to_bv 64 a) k = true.
Proof.
intros j a i k -> Hk Hik. dsl. unfold M.
eapply store_ok_mono; [apply wbytes_grows|].
eapply (store_ok_sub src0segs mem d _ (length bs)); [exact Hnd | exact Hdst | |];
rewrite u_Z2bv by lia; lia.
Qed.
Lemma M_app : forall i k, (i + k <= length bs)%nat ->
wbytes (M i) (Z_to_bv 64 (D + Z.of_nat i)) (chunk i k) = M (i + k).
Proof.
intros i k Hik. dsl. unfold M, chunk.
rewrite <- firstn_app_firstn_skipn, wbytes_app. f_equal.
rewrite word_add_nat, length_firstn. f_equal. lia.
Qed.
Lemma M_app1 : forall j a b, a = D + Z.of_nat j -> b = nth j bs NUL -> (j < length bs)%nat ->
wbytes (M j) (Z_to_bv 64 a) [b] = M (Datatypes.S j).
Proof.
intros j a b -> -> Hj. rewrite <- chunk1, M_app by lia. f_equal. lia.
Qed.
Lemma M_app4 : forall j a l, a = D + Z.of_nat j -> l = chunk j 4 -> (j + 4 <= length bs)%nat ->
wbytes (M j) (Z_to_bv 64 a) l = M (j + 4).
Proof. intros j a l -> -> Hj. apply M_app. exact Hj. Qed.
Lemma M_full : forall i, (length bs <= i)%nat -> M i = wbytes mem d bs.
Proof. intros i Hi. unfold M. rewrite firstn_all2 by exact Hi. reflexivity. Qed.
Definition keep (r : reg) : Prop :=
r <> 5%bv /\ r <> 6%bv /\ r <> 7%bv /\ r <> 11%bv /\ r <> 12%bv /\ r <> 13%bv /\ r <> 14%bv
/\ r <> 15%bv /\ r <> 16%bv /\ r <> 17%bv /\ r <> 28%bv.
Definition fin (regs : bvmap 5 word) (pc : word) (m : word -> option byte) : Prop :=
exists regs',
msteps src0segs (mkst regs pc m rom) (mkst regs' (v_jalr (getr regs 1) 0) (wbytes mem d bs) rom)
/\ forall r, keep r -> getr regs' r = getr regs r.
Lemma keep_1 : keep 1.
Proof. unfold keep. repeat split; reg_neq_tac. Qed.
Lemma fin_steps : forall regs pc m regs2 pc2 m2,
msteps src0segs (mkst regs pc m rom) (mkst regs2 pc2 m2 rom) ->
(forall r, keep r -> getr regs2 r = getr regs r) ->
fin regs2 pc2 m2 -> fin regs pc m.
Proof.
intros regs pc m regs2 pc2 m2 Hms Hfr (regs' & Hms' & Hfr').
exists regs'. split.
- eapply msteps_trans; [exact Hms|]. rewrite <- (Hfr 1%bv keep_1). exact Hms'.
- intros r Hr. rewrite (Hfr' r Hr). apply Hfr. exact Hr.
Qed.
Lemma fin_done : forall regs t m,
t = v_jalr (getr regs 1) 0 -> m = wbytes mem d bs -> fin regs t m.
Proof. intros regs t m -> ->. exists regs. split; [apply mst_refl| intros; reflexivity]. Qed.
Lemma fin_pc : forall regs (pc pc' : word) m,
bv_unsigned pc = bv_unsigned pc' -> fin regs pc' m -> fin regs pc m.
Proof. intros regs pc pc' m H Hf. replace pc with pc' by (apply bv_eq; symmetry; exact H). exact Hf. Qed.
Ltac frame :=
let r := fresh "r" in let Hr := fresh "Hkeep" in
intros r Hr; unfold keep in Hr;
destruct Hr as (?&?&?&?&?&?&?&?&?&?&?);
rewrite ?getr_other by assumption; reflexivity.
Ltac fin_apply L :=
eapply fin_pc; [ | eapply L ]; [ vm_compute; reflexivity | .. ].
Ltac rg := gr; rwH; first [ reflexivity | f_equal; lia ].
Ltac steplbu F0 D idx := let F := litF F0 in
chain_step;
[ reflexivity
| eapply step_lbu; [ exact F | reflexivity | exact D
| gr; rwH; imm_norm; rewrite ?v_addi_lit; apply (src_read1 _ _ idx); lia ]
| step_simpl ].
Ltac steplw F0 D idx := let F := litF F0 in
chain_step;
[ reflexivity
| eapply step_lw_l; [ exact F | reflexivity | exact D
| gr; rwH; imm_norm; rewrite ?v_addi_lit; apply (src_read4 _ _ idx); lia ]
| step_simpl ].
Ltac sbval :=
gr; rwH;
first [ apply sb_lbu
| rewrite sb_lwv_l by (apply chunk_len; lia); rewrite nth_chunk by lia; reflexivity
| rewrite sb_lwv_sr8_l by (apply chunk_len; lia); rewrite nth_chunk by lia; reflexivity
| rewrite sb_lwv_sr16_l by (apply chunk_len; lia); rewrite nth_chunk by lia; reflexivity ].
Ltac swval :=
gr; rwH;
first [ rewrite sw_lwv_l by (apply chunk_len; lia); first [reflexivity | f_equal; lia]
| rewrite ?sw_merge8_l, ?sw_merge16_l, ?sw_merge24_l by (apply chunk_len; lia);
lazymatch goal with
| |- skipn ?p (chunk ?o 4) ++ firstn _ (chunk ?o4 4) = chunk ?j 4 =>
replace j with (o + p)%nat by lia; replace o4 with (o + 4)%nat by lia;
symmetry; apply chunk_shift; lia
end ].
Ltac stepsb HF0 HD := let HF := litF HF0 in
lazymatch goal with
| |- msteps _ (mkst _ _ (M ?j) _) _ =>
chain_step;
[ reflexivity
| eapply step_sb_l with (a := D + Z.of_nat j);
[ exact HF | reflexivity | exact HD | val | sbval | apply (dst_ok j _ j 1); [lia|lia|lia] ]
| step_simpl; rewrite M_app1 by first [lia | f_equal; lia] ]
end.
Ltac stepsw HF0 HD := let HF := litF HF0 in
lazymatch goal with
| |- msteps _ (mkst _ _ (M ?j) _) _ =>
chain_step;
[ reflexivity
| eapply step_sw_l with (a := D + Z.of_nat j) (l := chunk j 4);
[ exact HF | reflexivity | exact HD | val | swval | apply (dst_ok j _ j 4); [lia|lia|lia] ]
| step_simpl; rewrite M_app4 by first [lia | f_equal; lia] ]
end.
Ltac finish_ret :=
lazymatch goal with
| |- msteps _ _ _ => apply mst_refl
end.
Lemma tail_3f0 : forall regs i m,
getr regs 11 = Z_to_bv 64 (S + Z.of_nat i) ->
getr regs 13 = Z_to_bv 64 (D + Z.of_nat i) ->
getr regs 12 = Z_to_bv 64 m -> 0 <= m < 2^64 ->
Z.of_nat i + m mod 4 = Z.of_nat (length bs) ->
fin regs (Z_to_bv 64 (src0_A_memcpy + 0x3c0)) (M i).
Proof.
intros regs i m H11 H13 H12 Hm Hi. dsl.
pose proof (mod4_split m) as E4. pose proof (mod2_split m) as E2.
assert (Hm2 : 0 <= m mod 2 < 2) by (apply Z.mod_pos_bound; lia).
destruct (land2_cases m) as [L2|L2]; destruct (land1_cases m) as [L1|L1].
-
eapply fin_steps.
+ norm_pc.
sv F_3c0 D_3c0 (Z_to_bv 64 0); [rewrite v_andi_lit by lia; rewrite L2; reflexivity|].
stepbf F_3c4 D_3c4.
sv F_3c8 D_3c8 (Z_to_bv 64 0); [rewrite v_andi_lit by lia; rewrite L1; reflexivity|].
stepbf F_3cc D_3cc.
stepret F_3d0 D_3d0.
finish_ret.
+ frame.
+ apply fin_done; [gr; reflexivity | apply M_full; lia].
-
eapply fin_steps.
+ norm_pc.
sv F_3c0 D_3c0 (Z_to_bv 64 0); [rewrite v_andi_lit by lia; rewrite L2; reflexivity|].
stepbf F_3c4 D_3c4.
sv F_3c8 D_3c8 (Z_to_bv 64 1); [rewrite v_andi_lit by lia; rewrite L1; reflexivity|].
stepbt F_3cc D_3cc.
steplbu F_3f8 D_3f8 i.
stepsb F_3fc D_3fc.
stepret F_400 D_400.
finish_ret.
+ frame.
+ apply fin_done; [gr; reflexivity | apply M_full; lia].
-
eapply fin_steps.
+ norm_pc.
sv F_3c0 D_3c0 (Z_to_bv 64 2); [rewrite v_andi_lit by lia; rewrite L2; reflexivity|].
stepbt F_3c4 D_3c4.
steplbu F_3d4 D_3d4 i.
steplbu F_3d8 D_3d8 (i + 1)%nat.
sv F_3dc D_3dc (Z_to_bv 64 (S + Z.of_nat i + 2)).
sv F_3e0 D_3e0 (Z_to_bv 64 (D + Z.of_nat i + 2)).
stepsb F_3e4 D_3e4.
stepsb F_3e8 D_3e8.
sv F_3ec D_3ec (Z_to_bv 64 (D + Z.of_nat i + 2)).
sv F_3f0 D_3f0 (Z_to_bv 64 0); [rewrite v_andi_lit by lia; rewrite L1; reflexivity|].
stepbt F_3f4 D_3f4.
stepret F_3d0 D_3d0.
finish_ret.
+ frame.
+ apply fin_done; [gr; reflexivity | apply M_full; lia].
-
eapply fin_steps.
+ norm_pc.
sv F_3c0 D_3c0 (Z_to_bv 64 2); [rewrite v_andi_lit by lia; rewrite L2; reflexivity|].
stepbt F_3c4 D_3c4.
steplbu F_3d4 D_3d4 i.
steplbu F_3d8 D_3d8 (i + 1)%nat.
sv F_3dc D_3dc (Z_to_bv 64 (S + Z.of_nat i + 2)).
sv F_3e0 D_3e0 (Z_to_bv 64 (D + Z.of_nat i + 2)).
stepsb F_3e4 D_3e4.
stepsb F_3e8 D_3e8.
sv F_3ec D_3ec (Z_to_bv 64 (D + Z.of_nat i + 2)).
sv F_3f0 D_3f0 (Z_to_bv 64 1); [rewrite v_andi_lit by lia; rewrite L1; reflexivity|].
stepbf F_3f4 D_3f4.
steplbu F_3f8 D_3f8 (i + 2)%nat.
stepsb F_3fc D_3fc.
stepret F_400 D_400.
finish_ret.
+ frame.
+ apply fin_done; [gr; reflexivity | apply M_full; lia].
Qed.
Lemma tail_3c4 : forall regs i m,
getr regs 11 = Z_to_bv 64 (S + Z.of_nat i) ->
getr regs 13 = Z_to_bv 64 (D + Z.of_nat i) ->
getr regs 12 = Z_to_bv 64 m -> 0 <= m < 2^64 ->
Z.of_nat i + 4 + m mod 4 = Z.of_nat (length bs) ->
fin regs (Z_to_bv 64 (src0_A_memcpy + 0x394)) (M i).
Proof.
intros regs i m H11 H13 H12 Hm Hi. dsl.
assert (Hm4 : 0 <= m mod 4 < 4) by (apply Z.mod_pos_bound; lia).
eapply fin_steps.
- norm_pc.
steplbu F_394 D_394 i.
steplbu F_398 D_398 (i + 1)%nat.
steplbu F_39c D_39c (i + 2)%nat.
steplbu F_3a0 D_3a0 (i + 3)%nat.
sv F_3a4 D_3a4 (Z_to_bv 64 (S + Z.of_nat i + 4)).
sv F_3a8 D_3a8 (Z_to_bv 64 (D + Z.of_nat i + 4)).
stepsb F_3ac D_3ac.
stepsb F_3b0 D_3b0.
stepsb F_3b4 D_3b4.
stepsb F_3b8 D_3b8.
sv F_3bc D_3bc (Z_to_bv 64 (D + Z.of_nat i + 4)).
apply mst_refl.
- frame.
- fin_apply tail_3f0; [gr; f_equal; lia | gr; f_equal; lia | gr; rwH; reflexivity | lia | lia].
Qed.
Lemma test_098 : forall regs i m,
getr regs 11 = Z_to_bv 64 (S + Z.of_nat i) ->
getr regs 13 = Z_to_bv 64 (D + Z.of_nat i) ->
getr regs 12 = Z_to_bv 64 m -> 0 <= m < 2^64 ->
Z.of_nat i + m mod 8 = Z.of_nat (length bs) ->
fin regs (Z_to_bv 64 (src0_A_memcpy + 0x68)) (M i).
Proof.
intros regs i m H11 H13 H12 Hm Hi. dsl.
pose proof (mod8_split m) as E8.
destruct (land4_cases m) as [L4|L4].
- eapply fin_steps.
+ norm_pc.
sv F_068 D_068 (Z_to_bv 64 0); [rewrite v_andi_lit by lia; rewrite L4; reflexivity|].
stepbf F_06c D_06c.
stepj' F_070 D_070.
apply mst_refl.
+ frame.
+ fin_apply tail_3f0; [gr; exact H11 | gr; exact H13 | gr; exact H12 | lia | lia].
- eapply fin_steps.
+ norm_pc.
sv F_068 D_068 (Z_to_bv 64 4); [rewrite v_andi_lit by lia; rewrite L4; reflexivity|].
stepbt F_06c D_06c.
apply mst_refl.
+ frame.
+ fin_apply tail_3c4; [gr; exact H11 | gr; exact H13 | gr; exact H12 | lia | lia].
Qed.
Lemma tail_370 : forall regs i m,
getr regs 11 = Z_to_bv 64 (S + Z.of_nat i) ->
getr regs 13 = Z_to_bv 64 (D + Z.of_nat i) ->
getr regs 12 = Z_to_bv 64 m -> 0 <= m < 2^64 ->
Z.of_nat i + 8 + m mod 8 = Z.of_nat (length bs) ->
fin regs (Z_to_bv 64 (src0_A_memcpy + 0x340)) (M i).
Proof.
intros regs i m H11 H13 H12 Hm Hi. dsl.
assert (Hm8 : 0 <= m mod 8 < 8) by (apply Z.mod_pos_bound; lia).
pose proof (mod8_split m) as E8.
eapply fin_steps.
- norm_pc.
steplbu F_340 D_340 i.
steplbu F_344 D_344 (i + 1)%nat.
steplbu F_348 D_348 (i + 2)%nat.
steplbu F_34c D_34c (i + 3)%nat.
steplbu F_350 D_350 (i + 4)%nat.
steplbu F_354 D_354 (i + 5)%nat.
steplbu F_358 D_358 (i + 6)%nat.
steplbu F_35c D_35c (i + 7)%nat.
sv F_360 D_360 (Z_to_bv 64 (S + Z.of_nat i + 8)).
stepsb F_364 D_364.
stepsb F_368 D_368.
stepsb F_36c D_36c.
stepsb F_370 D_370.
sv F_374 D_374 (Z_to_bv 64 (D + Z.of_nat i + 8)).
stepsb F_378 D_378.
stepsb F_37c D_37c.
stepsb F_380 D_380.
stepsb F_384 D_384.
sv F_388 D_388 (Z_to_bv 64 (D + Z.of_nat i + 8)).
apply mst_refl.
- frame.
- destruct (land4_cases m) as [L4|L4].
+ eapply fin_steps.
* norm_pc.
sv F_38c D_38c (Z_to_bv 64 0); [rewrite v_andi_lit by lia; rewrite L4; reflexivity|].
stepbt F_390 D_390.
apply mst_refl.
* frame.
* fin_apply tail_3f0; [gr; f_equal; lia | gr; f_equal; lia | gr; rwH; reflexivity | lia | lia].
+ eapply fin_steps.
* norm_pc.
sv F_38c D_38c (Z_to_bv 64 4); [rewrite v_andi_lit by lia; rewrite L4; reflexivity|].
stepbf F_390 D_390.
apply mst_refl.
* frame.
* fin_apply tail_3c4; [gr; f_equal; lia | gr; f_equal; lia | gr; rwH; reflexivity | lia | lia].
Qed.
Lemma test_090 : forall regs i m,
getr regs 11 = Z_to_bv 64 (S + Z.of_nat i) ->
getr regs 13 = Z_to_bv 64 (D + Z.of_nat i) ->
getr regs 12 = Z_to_bv 64 m -> 0 <= m < 2^64 ->
Z.of_nat i + m mod 16 = Z.of_nat (length bs) ->
fin regs (Z_to_bv 64 (src0_A_memcpy + 0x60)) (M i).
Proof.
intros regs i m H11 H13 H12 Hm Hi. dsl.
pose proof (mod16_split m) as E16.
destruct (land8_cases m) as [L8|L8].
- eapply fin_steps.
+ norm_pc.
sv F_060 D_060 (Z_to_bv 64 0); [rewrite v_andi_lit by lia; rewrite L8; reflexivity|].
stepbf F_064 D_064.
apply mst_refl.
+ frame.
+ fin_apply test_098; [gr; exact H11 | gr; exact H13 | gr; exact H12 | lia | lia].
- eapply fin_steps.
+ norm_pc.
sv F_060 D_060 (Z_to_bv 64 8); [rewrite v_andi_lit by lia; rewrite L8; reflexivity|].
stepbt F_064 D_064.
apply mst_refl.
+ frame.
+ fin_apply tail_370; [gr; exact H11 | gr; exact H13 | gr; exact H12 | lia | lia].
Qed.
Lemma tail_2dc : forall regs i m,
getr regs 11 = Z_to_bv 64 (S + Z.of_nat i) ->
getr regs 13 = Z_to_bv 64 (D + Z.of_nat i) ->
getr regs 12 = Z_to_bv 64 m -> 0 <= m < 2^64 ->
Z.of_nat i + 16 + m mod 16 = Z.of_nat (length bs) ->
fin regs (Z_to_bv 64 (src0_A_memcpy + 0x2ac)) (M i).
Proof.
intros regs i m H11 H13 H12 Hm Hi. dsl.
assert (Hm16 : 0 <= m mod 16 < 16) by (apply Z.mod_pos_bound; lia).
pose proof (mod16_split m) as E16.
eapply fin_steps.
- norm_pc.
steplbu F_2ac D_2ac i.
steplbu F_2b0 D_2b0 (i + 1)%nat.
steplbu F_2b4 D_2b4 (i + 2)%nat.
steplbu F_2b8 D_2b8 (i + 3)%nat.
steplbu F_2bc D_2bc (i + 4)%nat.
steplbu F_2c0 D_2c0 (i + 5)%nat.
steplbu F_2c4 D_2c4 (i + 6)%nat.
steplbu F_2c8 D_2c8 (i + 7)%nat.
stepsb F_2cc D_2cc.
stepsb F_2d0 D_2d0.
stepsb F_2d4 D_2d4.
stepsb F_2d8 D_2d8.
steplbu F_2dc D_2dc (i + 8)%nat.
steplbu F_2e0 D_2e0 (i + 9)%nat.
steplbu F_2e4 D_2e4 (i + 10)%nat.
steplbu F_2e8 D_2e8 (i + 11)%nat.
stepsb F_2ec D_2ec.
stepsb F_2f0 D_2f0.
stepsb F_2f4 D_2f4.
stepsb F_2f8 D_2f8.
steplbu F_2fc D_2fc (i + 12)%nat.
steplbu F_300 D_300 (i + 13)%nat.
steplbu F_304 D_304 (i + 14)%nat.
steplbu F_308 D_308 (i + 15)%nat.
sv F_30c D_30c (Z_to_bv 64 (S + Z.of_nat i + 16)).
stepsb F_310 D_310.
stepsb F_314 D_314.
stepsb F_318 D_318.
stepsb F_31c D_31c.
sv F_320 D_320 (Z_to_bv 64 (D + Z.of_nat i + 16)).
stepsb F_324 D_324.
stepsb F_328 D_328.
stepsb F_32c D_32c.
stepsb F_330 D_330.
sv F_334 D_334 (Z_to_bv 64 (D + Z.of_nat i + 16)).
apply mst_refl.
- frame.
- destruct (land8_cases m) as [L8|L8].
+ eapply fin_steps.
* norm_pc.
sv F_338 D_338 (Z_to_bv 64 0); [rewrite v_andi_lit by lia; rewrite L8; reflexivity|].
stepbt F_33c D_33c.
apply mst_refl.
* frame.
* fin_apply test_098; [gr; f_equal; lia | gr; f_equal; lia | gr; rwH; reflexivity | lia | lia].
+ eapply fin_steps.
* norm_pc.
sv F_338 D_338 (Z_to_bv 64 8); [rewrite v_andi_lit by lia; rewrite L8; reflexivity|].
stepbf F_33c D_33c.
apply mst_refl.
* frame.
* fin_apply tail_370; [gr; f_equal; lia | gr; f_equal; lia | gr; rwH; reflexivity | lia | lia].
Qed.
Lemma test_088 : forall regs i m,
getr regs 11 = Z_to_bv 64 (S + Z.of_nat i) ->
getr regs 13 = Z_to_bv 64 (D + Z.of_nat i) ->
getr regs 12 = Z_to_bv 64 m -> 0 <= m < 32 ->
Z.of_nat i + m = Z.of_nat (length bs) ->
fin regs (Z_to_bv 64 (src0_A_memcpy + 0x58)) (M i).
Proof.
intros regs i m H11 H13 H12 Hm Hi. dsl.
destruct (Z_lt_le_dec m 16) as [Hl|Hh].
- eapply fin_steps.
+ norm_pc.
sv F_058 D_058 (Z_to_bv 64 16).
stepbf F_05c D_05c.
apply mst_refl.
+ frame.
+ fin_apply test_090; [gr; exact H11 | gr; exact H13 | gr; exact H12 | lia |].
rewrite Z.mod_small by lia. lia.
- eapply fin_steps.
+ norm_pc.
sv F_058 D_058 (Z_to_bv 64 16).
stepbt F_05c D_05c.
apply mst_refl.
+ frame.
+ fin_apply tail_2dc; [gr; exact H11 | gr; exact H13 | gr; exact H12 | lia |].
replace (m mod 16) with (m - 16); [lia|].
apply Z.mod_unique_pos with (q := 1); lia.
Qed.
Lemma al_1ac : forall regs i m,
getr regs 11 = Z_to_bv 64 (S + Z.of_nat i) ->
getr regs 13 = Z_to_bv 64 (D + Z.of_nat i) ->
getr regs 12 = Z_to_bv 64 m -> 0 <= m < 2^64 ->
Z.of_nat i + m mod 8 = Z.of_nat (length bs) ->
fin regs (Z_to_bv 64 (src0_A_memcpy + 0x17c)) (M i).
Proof.
intros regs i m H11 H13 H12 Hm Hi. dsl.
pose proof (mod8_split m) as E8.
assert (Hm4 : 0 <= m mod 4 < 4) by (apply Z.mod_pos_bound; lia).
destruct (land4_cases m) as [L4|L4].
- eapply fin_steps.
+ norm_pc.
sv F_17c D_17c (Z_to_bv 64 0); [rewrite v_andi_lit by lia; rewrite L4; reflexivity|].
stepbt F_180 D_180.
apply mst_refl.
+ frame.
+ fin_apply tail_3f0; [gr; exact H11 | gr; exact H13 | gr; exact H12 | lia | lia].
- eapply fin_steps.
+ norm_pc.
sv F_17c D_17c (Z_to_bv 64 4); [rewrite v_andi_lit by lia; rewrite L4; reflexivity|].
stepbf F_180 D_180.
steplw F_184 D_184 i.
sv F_188 D_188 (Z_to_bv 64 (S + Z.of_nat i + 4)).
stepsw F_18c D_18c.
sv F_190 D_190 (Z_to_bv 64 (D + Z.of_nat i + 4)).
stepj' F_194 D_194.
apply mst_refl.
+ frame.
+ fin_apply tail_3f0; [gr; f_equal; lia | gr; f_equal; lia | gr; rwH; reflexivity | lia | lia].
Qed.
Lemma al_18c : forall regs i m,
getr regs 11 = Z_to_bv 64 (S + Z.of_nat i) ->
getr regs 13 = Z_to_bv 64 (D + Z.of_nat i) ->
getr regs 12 = Z_to_bv 64 m -> 0 <= m < 16 ->
Z.of_nat i + m = Z.of_nat (length bs) ->
fin regs (Z_to_bv 64 (src0_A_memcpy + 0x15c)) (M i).
Proof.
intros regs i m H11 H13 H12 Hm Hi. dsl.
destruct (Z_lt_le_dec m 8) as [Hl|Hh].
- eapply fin_steps.
+ norm_pc.
sv F_15c D_15c (Z_to_bv 64 8).
stepbt F_160 D_160.
apply mst_refl.
+ frame.
+ fin_apply al_1ac; [gr; exact H11 | gr; exact H13 | gr; exact H12 | lia |].
rewrite Z.mod_small by lia. lia.
- eapply fin_steps.
+ norm_pc.
sv F_15c D_15c (Z_to_bv 64 8).
stepbf F_160 D_160.
steplw F_164 D_164 i.
steplw F_168 D_168 (i + 4)%nat.
stepsw F_16c D_16c.
stepsw F_170 D_170.
sv F_174 D_174 (Z_to_bv 64 (D + Z.of_nat i + 8)).
sv F_178 D_178 (Z_to_bv 64 (S + Z.of_nat i + 8)).
apply mst_refl.
+ frame.
+ fin_apply al_1ac; [gr; f_equal; lia | gr; f_equal; lia | gr; rwH; reflexivity | lia |].
replace (m mod 8) with (m - 8); [lia|].
apply Z.mod_unique_pos with (q := 1); lia.
Qed.
Lemma al_loop : forall k regs i m,
getr regs 11 = Z_to_bv 64 (S + Z.of_nat i) ->
getr regs 13 = Z_to_bv 64 (D + Z.of_nat i) ->
getr regs 12 = Z_to_bv 64 m ->
getr regs 14 = Z_to_bv 64 15 ->
16 <= m -> m <= 16 * Z.of_nat k ->
Z.of_nat i + m = Z.of_nat (length bs) ->
fin regs (Z_to_bv 64 (src0_A_memcpy + 0x12c)) (M i).
Proof.
induction k as [|k IH]; intros regs i m H11 H13 H12 H14 Hm Hk Hi; [lia|]. dsl.
eapply fin_steps.
- norm_pc.
steplw F_12c D_12c i.
steplw F_130 D_130 (i + 4)%nat.
steplw F_134 D_134 (i + 8)%nat.
steplw F_138 D_138 (i + 12)%nat.
sv F_13c D_13c (Z_to_bv 64 (S + Z.of_nat i + 16)).
sv F_140 D_140 (Z_to_bv 64 (m - 16)).
stepsw F_144 D_144.
stepsw F_148 D_148.
stepsw F_14c D_14c.
stepsw F_150 D_150.
sv F_154 D_154 (Z_to_bv 64 (D + Z.of_nat i + 16)).
apply mst_refl.
- frame.
- destruct (Z_lt_le_dec 15 (m - 16)) as [Hmore|Hlast].
+ eapply fin_steps.
* norm_pc. stepbt F_158 D_158. apply mst_refl.
* frame.
* fin_apply IH; [rg | rg | rg | rg | lia | lia | lia].
+ eapply fin_steps.
* norm_pc. stepbf F_158 D_158. apply mst_refl.
* frame.
* fin_apply al_18c; [gr; f_equal; lia | gr; f_equal; lia | gr; reflexivity | lia | lia].
Qed.
Lemma al_150 : forall regs i m,
getr regs 11 = Z_to_bv 64 (S + Z.of_nat i) ->
getr regs 13 = Z_to_bv 64 (D + Z.of_nat i) ->
getr regs 12 = Z_to_bv 64 m -> 0 <= m < 2^64 ->
Z.of_nat i + m = Z.of_nat (length bs) ->
fin regs (Z_to_bv 64 (src0_A_memcpy + 0x120)) (M i).
Proof.
intros regs i m H11 H13 H12 Hm Hi. dsl.
destruct (Z_lt_le_dec m 16) as [Hl|Hh].
- eapply fin_steps.
+ norm_pc.
sv F_120 D_120 (Z_to_bv 64 16).
stepbt F_124 D_124.
apply mst_refl.
+ frame.
+ fin_apply al_18c; [gr; exact H11 | gr; exact H13 | gr; exact H12 | lia | lia].
- eapply fin_steps.
+ norm_pc.
sv F_120 D_120 (Z_to_bv 64 16).
stepbf F_124 D_124.
sv F_128 D_128 (Z_to_bv 64 15).
apply mst_refl.
+ frame.
+ fin_apply (al_loop (Z.to_nat m)); [gr; exact H11 | gr; exact H13 | gr; exact H12 | gr; reflexivity | lia | lia | lia].
Qed.
Lemma sh_loop2 : forall k regs o j m,
getr regs 14 = lwv (chunk o 4) ->
getr regs 11 = Z_to_bv 64 (S + Z.of_nat o + 16) ->
getr regs 13 = Z_to_bv 64 (D + Z.of_nat j) ->
getr regs 12 = Z_to_bv 64 m ->
getr regs 15 = Z_to_bv 64 17 ->
(j = o + 2)%nat -> 18 <= m -> m <= 16 * Z.of_nat k ->
Z.of_nat j + m = Z.of_nat (length bs) ->
fin regs (Z_to_bv 64 (src0_A_memcpy + 0xa4)) (M j).
Proof.
induction k as [|k IH]; intros regs o j m H14 H11 H13 H12 H15 Hj Hm Hk Hi; [lia|]. dsl. subst j.
eapply fin_steps.
- norm_pc.
svsrw F_0a4 D_0a4 (v_srliw (lwv (chunk o 4)) 16).
steplw F_0a8 D_0a8 (o + 4)%nat.
steplw F_0ac D_0ac (o + 8)%nat.
steplw F_0b0 D_0b0 (o + 12)%nat.
steplw F_0b4 D_0b4 (o + 16)%nat.
sv F_0b8 D_0b8 (v_slli (lwv (chunk (o + 4) 4)) 16).
svsrw F_0bc D_0bc (v_srliw (lwv (chunk (o + 4) 4)) 16).
svor F_0c0 D_0c0 (v_or (v_slli (lwv (chunk (o + 4) 4)) 16) (v_srliw (lwv (chunk o 4)) 16)).
sv F_0c4 D_0c4 (v_slli (lwv (chunk (o + 8) 4)) 16).
svsrw F_0c8 D_0c8 (v_srliw (lwv (chunk (o + 8) 4)) 16).
svor F_0cc D_0cc (v_or (v_slli (lwv (chunk (o + 8) 4)) 16) (v_srliw (lwv (chunk (o + 4) 4)) 16)).
sv F_0d0 D_0d0 (v_slli (lwv (chunk (o + 12) 4)) 16).
svsrw F_0d4 D_0d4 (v_srliw (lwv (chunk (o + 12) 4)) 16).
svor F_0d8 D_0d8 (v_or (v_slli (lwv (chunk (o + 12) 4)) 16) (v_srliw (lwv (chunk (o + 8) 4)) 16)).
sv F_0dc D_0dc (v_slli (lwv (chunk (o + 16) 4)) 16).
svor F_0e0 D_0e0 (v_or (v_slli (lwv (chunk (o + 16) 4)) 16) (v_srliw (lwv (chunk (o + 12) 4)) 16)).
sv F_0e4 D_0e4 (Z_to_bv 64 (m - 16)).
stepsw F_0e8 D_0e8.
stepsw F_0ec D_0ec.
stepsw F_0f0 D_0f0.
stepsw F_0f4 D_0f4.
sv F_0f8 D_0f8 (Z_to_bv 64 (D + Z.of_nat o + 18)).
sv F_0fc D_0fc (Z_to_bv 64 (S + Z.of_nat o + 32)).
apply mst_refl.
- frame.
- destruct (Z_lt_le_dec 17 (m - 16)) as [Hmore|Hlast].
+ eapply fin_steps.
* norm_pc. stepbt F_100 D_100. apply mst_refl.
* frame.
* fin_apply IH; [rg | rg | rg | rg | rg | lia | lia | lia | lia].
+ destruct (Z_lt_le_dec (m - 16) 16) as [Hl|Hh].
* eapply fin_steps.
-- norm_pc. stepbf F_100 D_100.
sv F_104 D_104 (Z_to_bv 64 (S + Z.of_nat o + 18)).
sv F_108 D_108 (Z_to_bv 64 16).
stepbt F_10c D_10c. apply mst_refl.
-- frame.
-- fin_apply test_090; [rg | rg | rg | lia | rewrite Z.mod_small by lia; lia].
* eapply fin_steps.
-- norm_pc. stepbf F_100 D_100.
sv F_104 D_104 (Z_to_bv 64 (S + Z.of_nat o + 18)).
sv F_108 D_108 (Z_to_bv 64 16).
stepbf F_10c D_10c.
stepj' F_110 D_110. apply mst_refl.
-- frame.
-- fin_apply tail_2dc; [rg | rg | rg | lia | ].
replace ((m - 16) mod 16) with (m - 32); [lia|].
apply Z.mod_unique_pos with (q := 1); lia.
Qed.
Lemma sh_loop3 : forall k regs o j m,
getr regs 14 = lwv (chunk o 4) ->
getr regs 11 = Z_to_bv 64 (S + Z.of_nat o + 16) ->
getr regs 13 = Z_to_bv 64 (D + Z.of_nat j) ->
getr regs 12 = Z_to_bv 64 m ->
getr regs 15 = Z_to_bv 64 18 ->
(j = o + 1)%nat -> 19 <= m -> m <= 16 * Z.of_nat k ->
Z.of_nat j + m = Z.of_nat (length bs) ->
fin regs (Z_to_bv 64 (src0_A_memcpy + 0x1ac)) (M j).
Proof.
induction k as [|k IH]; intros regs o j m H14 H11 H13 H12 H15 Hj Hm Hk Hi; [lia|]. dsl. subst j.
eapply fin_steps.
- norm_pc.
svsrw F_1ac D_1ac (v_srliw (lwv (chunk o 4)) 8).
steplw F_1b0 D_1b0 (o + 4)%nat.
steplw F_1b4 D_1b4 (o + 8)%nat.
steplw F_1b8 D_1b8 (o + 12)%nat.
steplw F_1bc D_1bc (o + 16)%nat.
sv F_1c0 D_1c0 (v_slli (lwv (chunk (o + 4) 4)) 24).
svsrw F_1c4 D_1c4 (v_srliw (lwv (chunk (o + 4) 4)) 8).
svor F_1c8 D_1c8 (v_or (v_slli (lwv (chunk (o + 4) 4)) 24) (v_srliw (lwv (chunk o 4)) 8)).
sv F_1cc D_1cc (v_slli (lwv (chunk (o + 8) 4)) 24).
svsrw F_1d0 D_1d0 (v_srliw (lwv (chunk (o + 8) 4)) 8).
svor F_1d4 D_1d4 (v_or (v_slli (lwv (chunk (o + 8) 4)) 24) (v_srliw (lwv (chunk (o + 4) 4)) 8)).
sv F_1d8 D_1d8 (v_slli (lwv (chunk (o + 12) 4)) 24).
svsrw F_1dc D_1dc (v_srliw (lwv (chunk (o + 12) 4)) 8).
svor F_1e0 D_1e0 (v_or (v_slli (lwv (chunk (o + 12) 4)) 24) (v_srliw (lwv (chunk (o + 8) 4)) 8)).
sv F_1e4 D_1e4 (v_slli (lwv (chunk (o + 16) 4)) 24).
svor F_1e8 D_1e8 (v_or (v_slli (lwv (chunk (o + 16) 4)) 24) (v_srliw (lwv (chunk (o + 12) 4)) 8)).
sv F_1ec D_1ec (Z_to_bv 64 (m - 16)).
stepsw F_1f0 D_1f0.
stepsw F_1f4 D_1f4.
stepsw F_1f8 D_1f8.
stepsw F_1fc D_1fc.
sv F_200 D_200 (Z_to_bv 64 (D + Z.of_nat o + 1 + 16)).
sv F_204 D_204 (Z_to_bv 64 (S + Z.of_nat o + 32)).
apply mst_refl.
- frame.
- destruct (Z_lt_le_dec 18 (m - 16)) as [Hmore|Hlast].
+ eapply fin_steps.
* norm_pc. stepbt F_208 D_208. apply mst_refl.
* frame.
* fin_apply IH; [rg | rg | rg | rg | rg | lia | lia | lia | lia].
+ destruct (Z_lt_le_dec (m - 16) 16) as [Hl|Hh].
* eapply fin_steps.
-- norm_pc. stepbf F_208 D_208.
sv F_20c D_20c (Z_to_bv 64 (S + Z.of_nat o + 17)).
sv F_210 D_210 (Z_to_bv 64 16).
stepbt F_214 D_214. apply mst_refl.
-- frame.
-- fin_apply test_090; [rg | rg | rg | lia | rewrite Z.mod_small by lia; lia].
* eapply fin_steps.
-- norm_pc. stepbf F_208 D_208.
sv F_20c D_20c (Z_to_bv 64 (S + Z.of_nat o + 17)).
sv F_210 D_210 (Z_to_bv 64 16).
stepbf F_214 D_214.
stepj' F_218 D_218. apply mst_refl.
-- frame.
-- fin_apply tail_2dc; [rg | rg | rg | lia | ].
replace ((m - 16) mod 16) with (m - 32); [lia|].
apply Z.mod_unique_pos with (q := 1); lia.
Qed.
Lemma sh_loop1 : forall k regs o j m,
getr regs 14 = lwv (chunk o 4) ->
getr regs 11 = Z_to_bv 64 (S + Z.of_nat o + 16) ->
getr regs 13 = Z_to_bv 64 (D + Z.of_nat j) ->
getr regs 12 = Z_to_bv 64 m ->
getr regs 15 = Z_to_bv 64 16 ->
(j = o + 3)%nat -> 17 <= m -> m <= 16 * Z.of_nat k ->
Z.of_nat j + m = Z.of_nat (length bs) ->
fin regs (Z_to_bv 64 (src0_A_memcpy + 0x240)) (M j).
Proof.
induction k as [|k IH]; intros regs o j m H14 H11 H13 H12 H15 Hj Hm Hk Hi; [lia|]. dsl. subst j.
eapply fin_steps.
- norm_pc.
svsrw F_240 D_240 (v_srliw (lwv (chunk o 4)) 24).
steplw F_244 D_244 (o + 4)%nat.
steplw F_248 D_248 (o + 8)%nat.
steplw F_24c D_24c (o + 12)%nat.
steplw F_250 D_250 (o + 16)%nat.
sv F_254 D_254 (v_slli (lwv (chunk (o + 4) 4)) 8).
svsrw F_258 D_258 (v_srliw (lwv (chunk (o + 4) 4)) 24).
svor F_25c D_25c (v_or (v_slli (lwv (chunk (o + 4) 4)) 8) (v_srliw (lwv (chunk o 4)) 24)).
sv F_260 D_260 (v_slli (lwv (chunk (o + 8) 4)) 8).
svsrw F_264 D_264 (v_srliw (lwv (chunk (o + 8) 4)) 24).
svor F_268 D_268 (v_or (v_slli (lwv (chunk (o + 8) 4)) 8) (v_srliw (lwv (chunk (o + 4) 4)) 24)).
sv F_26c D_26c (v_slli (lwv (chunk (o + 12) 4)) 8).
svsrw F_270 D_270 (v_srliw (lwv (chunk (o + 12) 4)) 24).
svor F_274 D_274 (v_or (v_slli (lwv (chunk (o + 12) 4)) 8) (v_srliw (lwv (chunk (o + 8) 4)) 24)).
sv F_278 D_278 (v_slli (lwv (chunk (o + 16) 4)) 8).
svor F_27c D_27c (v_or (v_slli (lwv (chunk (o + 16) 4)) 8) (v_srliw (lwv (chunk (o + 12) 4)) 24)).
sv F_280 D_280 (Z_to_bv 64 (m - 16)).
stepsw F_284 D_284.
stepsw F_288 D_288.
stepsw F_28c D_28c.
stepsw F_290 D_290.
sv F_294 D_294 (Z_to_bv 64 (D + Z.of_nat o + 3 + 16)).
sv F_298 D_298 (Z_to_bv 64 (S + Z.of_nat o + 32)).
apply mst_refl.
- frame.
- destruct (Z_lt_le_dec 16 (m - 16)) as [Hmore|Hlast].
+ eapply fin_steps.
* norm_pc. stepbt F_29c D_29c. apply mst_refl.
* frame.
* fin_apply IH; [rg | rg | rg | rg | rg | lia | lia | lia | lia].
+ destruct (Z_lt_le_dec (m - 16) 16) as [Hl|Hh].
* eapply fin_steps.
-- norm_pc. stepbf F_29c D_29c.
sv F_2a0 D_2a0 (Z_to_bv 64 (S + Z.of_nat o + 19)).
sv F_2a4 D_2a4 (Z_to_bv 64 16).
stepbt F_2a8 D_2a8. apply mst_refl.
-- frame.
-- fin_apply test_090; [rg | rg | rg | lia | rewrite Z.mod_small by lia; lia].
* eapply fin_steps.
-- norm_pc. stepbf F_29c D_29c.
sv F_2a0 D_2a0 (Z_to_bv 64 (S + Z.of_nat o + 19)).
sv F_2a4 D_2a4 (Z_to_bv 64 16).
stepbf F_2a8 D_2a8.
apply mst_refl.
-- frame.
-- fin_apply tail_2dc; [rg | rg | rg | lia | ].
replace ((m - 16) mod 16) with (m - 32); [lia|].
apply Z.mod_unique_pos with (q := 1); lia.
Qed.
Lemma sh_0a4 : forall regs i m r,
getr regs 11 = Z_to_bv 64 (S + Z.of_nat i) ->
getr regs 13 = Z_to_bv 64 (D + Z.of_nat i) ->
getr regs 12 = Z_to_bv 64 m ->
getr regs 15 = Z_to_bv 64 r ->
0 < r < 4 -> 32 <= m < 2^64 ->
Z.of_nat i + m = Z.of_nat (length bs) ->
fin regs (Z_to_bv 64 (src0_A_memcpy + 0x74)) (M i).
Proof.
intros regs i m r H11 H13 H12 H15 Hr Hm Hi. dsl.
assert (Hr3 : r = 1 \/ r = 2 \/ r = 3) by lia.
destruct Hr3 as [Hr1|[Hr2|Hr3]]; subst r.
-
eapply fin_steps.
+ norm_pc.
steplw F_074 D_074 i.
sv F_078 D_078 (Z_to_bv 64 3).
stepbf F_07c D_07c.
sv F_080 D_080 (Z_to_bv 64 2).
stepbt F_084 D_084.
sv F_21c D_21c (v_srli (lwv (chunk i 4)) 8).
sv F_220 D_220 (v_srli (lwv (chunk i 4)) 16).
sv F_224 D_224 (Z_to_bv 64 (m - 3)).
stepsb F_228 D_228.
stepsb F_22c D_22c.
stepsb F_230 D_230.
sv F_234 D_234 (Z_to_bv 64 (D + Z.of_nat i + 3)).
sv F_238 D_238 (Z_to_bv 64 (S + Z.of_nat i + 16)).
sv F_23c D_23c (Z_to_bv 64 16).
apply mst_refl.
+ frame.
+ fin_apply (sh_loop1 (Z.to_nat m)); [rg | rg | rg | rg | rg | lia | lia | lia | lia].
-
eapply fin_steps.
+ norm_pc.
steplw F_074 D_074 i.
sv F_078 D_078 (Z_to_bv 64 3).
stepbf F_07c D_07c.
sv F_080 D_080 (Z_to_bv 64 2).
stepbf F_084 D_084.
sv F_088 D_088 (v_srli (lwv (chunk i 4)) 8).
sv F_08c D_08c (Z_to_bv 64 (m - 2)).
stepsb F_090 D_090.
stepsb F_094 D_094.
sv F_098 D_098 (Z_to_bv 64 (D + Z.of_nat i + 2)).
sv F_09c D_09c (Z_to_bv 64 (S + Z.of_nat i + 16)).
sv F_0a0 D_0a0 (Z_to_bv 64 17).
apply mst_refl.
+ frame.
+ fin_apply (sh_loop2 (Z.to_nat m)); [rg | rg | rg | rg | rg | lia | lia | lia | lia].
-
eapply fin_steps.
+ norm_pc.
steplw F_074 D_074 i.
sv F_078 D_078 (Z_to_bv 64 3).
stepbt F_07c D_07c.
stepsb F_198 D_198.
sv F_19c D_19c (Z_to_bv 64 (D + Z.of_nat i + 1)).
sv F_1a0 D_1a0 (Z_to_bv 64 (m - 1)).
sv F_1a4 D_1a4 (Z_to_bv 64 (S + Z.of_nat i + 16)).
sv F_1a8 D_1a8 (Z_to_bv 64 18).
apply mst_refl.
+ frame.
+ fin_apply (sh_loop3 (Z.to_nat m)); [rg | rg | rg | rg | rg | lia | lia | lia | lia].
Qed.
Lemma mid_080 : forall regs i m r,
getr regs 11 = Z_to_bv 64 (S + Z.of_nat i) ->
getr regs 13 = Z_to_bv 64 (D + Z.of_nat i) ->
getr regs 12 = Z_to_bv 64 m ->
getr regs 15 = Z_to_bv 64 r ->
0 < r < 4 -> 0 <= m < 2^64 ->
Z.of_nat i + m = Z.of_nat (length bs) ->
fin regs (Z_to_bv 64 (src0_A_memcpy + 0x50)) (M i).
Proof.
intros regs i m r H11 H13 H12 H15 Hr Hm Hi. dsl.
destruct (Z_lt_le_dec m 32) as [Hl|Hh].
- eapply fin_steps.
+ norm_pc. sv F_050 D_050 (Z_to_bv 64 32). stepbf F_054 D_054. apply mst_refl.
+ frame.
+ fin_apply test_088; [rg | rg | rg | lia | lia].
- eapply fin_steps.
+ norm_pc. sv F_050 D_050 (Z_to_bv 64 32). stepbt F_054 D_054. apply mst_refl.
+ frame.
+ fin_apply sh_0a4; [rg | rg | rg | rg | lia | lia | lia].
Qed.
Lemma mid_078 : forall regs i m,
getr regs 11 = Z_to_bv 64 (S + Z.of_nat i) ->
getr regs 13 = Z_to_bv 64 (D + Z.of_nat i) ->
getr regs 12 = Z_to_bv 64 m ->
0 <= m < 2^64 ->
Z.of_nat i + m = Z.of_nat (length bs) ->
fin regs (Z_to_bv 64 (src0_A_memcpy + 0x48)) (M i).
Proof.
intros regs i m H11 H13 H12 Hm Hi. dsl.
assert (Hr : 0 <= (D + Z.of_nat i) mod 4 < 4) by (apply Z.mod_pos_bound; lia).
destruct (Z.eq_dec ((D + Z.of_nat i) mod 4) 0) as [Hz|Hnz].
- eapply fin_steps.
+ norm_pc.
sv F_048 D_048 (Z_to_bv 64 0); [rewrite and3_mod4, Hz; reflexivity|].
stepbt F_04c D_04c. apply mst_refl.
+ frame.
+ fin_apply al_150; [rg | rg | rg | lia | lia].
- eapply fin_steps.
+ norm_pc.
sv F_048 D_048 (Z_to_bv 64 ((D + Z.of_nat i) mod 4)); [rewrite and3_mod4; reflexivity|].
stepbf F_04c D_04c. apply mst_refl.
+ frame.
+ fin_apply mid_080; [rg | rg | rg | rg | lia | lia | lia].
Qed.
Lemma ph1_loop : forall k regs i m,
getr regs 11 = Z_to_bv 64 (S + Z.of_nat i) ->
getr regs 13 = Z_to_bv 64 (D + Z.of_nat i) ->
getr regs 12 = Z_to_bv 64 m ->
getr regs 14 = Z_to_bv 64 (S + Z.of_nat i + 1) ->
getr regs 15 = Z_to_bv 64 1 ->
1 <= m -> m <= Z.of_nat k ->
Z.of_nat i + m = Z.of_nat (length bs) ->
fin regs (Z_to_bv 64 (src0_A_memcpy + 0x18)) (M i).
Proof.
induction k as [|k IH]; intros regs i m H11 H13 H12 H14 H15 Hm Hk Hi; [lia|]. dsl.
assert (Hr : 0 <= (S + Z.of_nat i + 1) mod 4 < 4) by (apply Z.mod_pos_bound; lia).
eapply fin_steps.
- norm_pc.
steplbu F_018 D_018 i.
sv F_01c D_01c (Z_to_bv 64 m).
sv F_020 D_020 (Z_to_bv 64 (S + Z.of_nat i + 1)).
sv F_024 D_024 (Z_to_bv 64 ((S + Z.of_nat i + 1) mod 4)); [rewrite and3_mod4; reflexivity|].
stepsb F_028 D_028.
sv F_02c D_02c (Z_to_bv 64 (D + Z.of_nat i + 1)).
sv F_030 D_030 (Z_to_bv 64 (m - 1)).
apply mst_refl.
- frame.
- destruct (Z.eq_dec ((S + Z.of_nat i + 1) mod 4) 0) as [Hz|Hnz].
+
eapply fin_steps.
* norm_pc. stepbt F_034 D_034. apply mst_refl.
* frame.
* fin_apply mid_078; [rg | rg | rg | lia | lia].
+ destruct (Z.eq_dec m 1) as [H1|Hn1].
*
eapply fin_steps.
-- norm_pc. stepbf F_034 D_034.
sv F_038 D_038 (Z_to_bv 64 (S + Z.of_nat i + 2)).
stepbf F_03c D_03c.
stepj' F_040 D_040. apply mst_refl.
-- frame.
-- fin_apply mid_078; [rg | rg | rg | lia | lia].
* eapply fin_steps.
-- norm_pc. stepbf F_034 D_034.
sv F_038 D_038 (Z_to_bv 64 (S + Z.of_nat i + 2)).
stepbt F_03c D_03c. apply mst_refl.
-- frame.
-- fin_apply IH; [rg | rg | rg | rg | rg | lia | lia | lia].
Qed.
Lemma entry_030 : forall regs,
getr regs 10 = d -> getr regs 11 = s ->
getr regs 12 = Z_to_bv 64 (Z.of_nat (length bs)) ->
fin regs (Z_to_bv 64 (src0_A_memcpy + 0x0)) (M 0).
Proof.
intros regs H10' H11' H12. dsl.
assert (H10 : getr regs 10 = Z_to_bv 64 (D + Z.of_nat 0))
by (rewrite H10', HD_, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
assert (H11 : getr regs 11 = Z_to_bv 64 (S + Z.of_nat 0))
by (rewrite H11', HS_, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
clear H10' H11'.
assert (HSm : 0 <= S mod 4 < 4) by (apply Z.mod_pos_bound; lia).
assert (HDm : 0 <= D mod 4 < 4) by (apply Z.mod_pos_bound; lia).
destruct (Z.eq_dec (S mod 4) 0) as [HSz|HSnz].
-
destruct (Z.eq_dec (D mod 4) 0) as [HDz|HDnz].
+ eapply fin_steps.
* norm_pc.
sv F_000 D_000 (Z_to_bv 64 0); [rewrite and3_mod4; rewrite <- HSz; f_equal; f_equal; lia|].
stepbt F_004 D_004.
sv F_114 D_114 (Z_to_bv 64 (D + Z.of_nat 0)).
sv F_118 D_118 (Z_to_bv 64 0); [rewrite and3_mod4; rewrite <- HDz; f_equal; f_equal; lia|].
stepbf F_11c D_11c. apply mst_refl.
* frame.
* fin_apply al_150; [rg | rg | rg | lia | lia].
+ eapply fin_steps.
* norm_pc.
sv F_000 D_000 (Z_to_bv 64 0); [rewrite and3_mod4; rewrite <- HSz; f_equal; f_equal; lia|].
stepbt F_004 D_004.
sv F_114 D_114 (Z_to_bv 64 (D + Z.of_nat 0)).
sv F_118 D_118 (Z_to_bv 64 (D mod 4)); [rewrite and3_mod4; f_equal; f_equal; lia|].
stepbt F_11c D_11c. apply mst_refl.
* frame.
* fin_apply mid_080; [rg | rg | rg | rg | lia | lia | lia].
- destruct (Nat.eq_dec (length bs) 0) as [HL0|HLnz].
+
eapply fin_steps.
* norm_pc.
sv F_000 D_000 (Z_to_bv 64 (S mod 4)); [rewrite and3_mod4; f_equal; f_equal; lia|].
stepbf F_004 D_004.
stepbt F_008 D_008.
sv F_044 D_044 (Z_to_bv 64 (D + Z.of_nat 0)).
apply mst_refl.
* frame.
* fin_apply mid_078; [rg | rg | rg | lia | lia].
+ eapply fin_steps.
* norm_pc.
sv F_000 D_000 (Z_to_bv 64 (S mod 4)); [rewrite and3_mod4; f_equal; f_equal; lia|].
stepbf F_004 D_004.
stepbf F_008 D_008.
sv F_00c D_00c (Z_to_bv 64 (S + Z.of_nat 0 + 1)).
sv F_010 D_010 (Z_to_bv 64 1).
sv F_014 D_014 (Z_to_bv 64 (D + Z.of_nat 0)).
apply mst_refl.
* frame.
* fin_apply (ph1_loop (length bs)); [rg | rg | rg | rg | rg | lia | lia | lia].
Qed.
End f.
Theorem src0_memcpy :
forall (bs : list byte) (d s n : word) (mem rom : word -> option byte) (regs : bvmap 5 word),
getr regs 10 = d -> getr regs 11 = s -> getr regs 12 = n ->
bv_unsigned n = Z.of_nat (length bs) ->
rdn src0segs mem s (length bs) = Some bs ->
store_ok src0segs mem d (length bs) = true ->
bv_unsigned d + Z.of_nat (length bs) <= 2^64 ->
bv_unsigned s + Z.of_nat (length bs) <= 2^64 ->
(bv_unsigned d + Z.of_nat (length bs) <= bv_unsigned s
\/ bv_unsigned s + Z.of_nat (length bs) <= bv_unsigned d) ->
exists regs',
msteps src0segs (mkst regs (Z_to_bv 64 src0_A_memcpy) mem rom)
(mkst regs' (v_jalr (getr regs 1) 0) (wbytes mem d bs) rom)
/\ getr regs' 10 = d
/\ (forall r : reg, r <> 5%bv -> r <> 6%bv -> r <> 7%bv -> r <> 11%bv -> r <> 12%bv ->
r <> 13%bv -> r <> 14%bv -> r <> 15%bv -> r <> 16%bv -> r <> 17%bv -> r <> 28%bv ->
getr regs' r = getr regs r).
Proof.
intros bs d s n mem rom regs H10 H11 H12 Hn Hsrc Hdst Hnd Hns Hdisj.
change (Z_to_bv 64 src0_A_memcpy) with (Z_to_bv 64 (src0_A_memcpy + 0x0)).
assert (H12' : getr regs 12 = Z_to_bv 64 (Z.of_nat (length bs)))
by (rewrite H12, <- Hn, Z_to_bv_bv_unsigned; reflexivity).
destruct (entry_030 bs d s mem rom Hsrc Hdst Hnd Hns Hdisj regs H10 H11 H12') as (regs' & Hms & Hfr).
exists regs'. split; [exact Hms|]. split.
- rewrite Hfr; [exact H10|]. unfold keep. repeat split; reg_neq_tac.
- intros. apply Hfr. unfold keep. repeat split; assumption.
Qed.
End e.
