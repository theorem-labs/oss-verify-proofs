(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK0w.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP02.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AB1w.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN32.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0f YO0g YO0a YO0c.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma fetch_lit : forall (p : word) (w : bv 32),
clookup tfibmusl_tbl (bv_unsigned p) = Some (bv_unsigned w) ->
fetch_word tfibsegs p = Some w.
Proof.
intros p w H.
rewrite <- (Z_to_bv_bv_unsigned 64 p), <- (Z_to_bv_bv_unsigned 32 w).
apply tfibmusl_tbl_ok. exact H.
Qed.
End e.
Ltac ftac := apply fetch_lit; vm_compute; reflexivity.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma F_000 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_memset + 0x0)) = Some (0x0e060a63%bv : bv 32).
Proof. ftac. Qed.
Lemma D_000 : decode_any (0x0e060a63%bv : bv 32) = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_004 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_memset + 0x4)) = Some (0x00b50023%bv : bv 32).
Proof. ftac. Qed.
Lemma D_004 : decode_any (0x00b50023%bv : bv 32) = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_008 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_memset + 0x8)) = Some (0x00c506b3%bv : bv 32).
Proof. ftac. Qed.
Lemma D_008 : decode_any (0x00c506b3%bv : bv 32) = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_00c : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_memset + 0xc)) = Some (0x00300713%bv : bv 32).
Proof. ftac. Qed.
Lemma D_00c : decode_any (0x00300713%bv : bv 32) = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_010 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_memset + 0x10)) = Some (0xfeb68fa3%bv : bv 32).
Proof. ftac. Qed.
Lemma D_010 : decode_any (0xfeb68fa3%bv : bv 32) = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_014 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_memset + 0x14)) = Some (0x0ee66063%bv : bv 32).
Proof. ftac. Qed.
Lemma D_014 : decode_any (0x0ee66063%bv : bv 32) = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_018 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_memset + 0x18)) = Some (0x00b500a3%bv : bv 32).
Proof. ftac. Qed.
Lemma D_018 : decode_any (0x00b500a3%bv : bv 32) = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_01c : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_memset + 0x1c)) = Some (0x00b50123%bv : bv 32).
Proof. ftac. Qed.
Lemma D_01c : decode_any (0x00b50123%bv : bv 32) = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_020 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_memset + 0x20)) = Some (0x00700713%bv : bv 32).
Proof. ftac. Qed.
Lemma D_020 : decode_any (0x00700713%bv : bv 32) = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_024 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_memset + 0x24)) = Some (0xfeb68ea3%bv : bv 32).
Proof. ftac. Qed.
Lemma D_024 : decode_any (0xfeb68ea3%bv : bv 32) = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_028 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_memset + 0x28)) = Some (0xfeb68f23%bv : bv 32).
Proof. ftac. Qed.
Lemma D_028 : decode_any (0xfeb68f23%bv : bv 32) = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_02c : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_memset + 0x2c)) = Some (0x0ce66463%bv : bv 32).
Proof. ftac. Qed.
Lemma D_02c : decode_any (0x0ce66463%bv : bv 32) = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_030 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_memset + 0x30)) = Some (0x00b501a3%bv : bv 32).
Proof. ftac. Qed.
Lemma D_030 : decode_any (0x00b501a3%bv : bv 32) = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_034 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_memset + 0x34)) = Some (0x00900793%bv : bv 32).
Proof. ftac. Qed.
Lemma D_034 : decode_any (0x00900793%bv : bv 32) = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_038 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_memset + 0x38)) = Some (0xfeb68e23%bv : bv 32).
Proof. ftac. Qed.
Lemma D_038 : decode_any (0xfeb68e23%bv : bv 32) = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_03c : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_memset + 0x3c)) = Some (0x0af66c63%bv : bv 32).
Proof. ftac. Qed.
Lemma D_03c : decode_any (0x0af66c63%bv : bv 32) = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_040 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_memset + 0x40)) = Some (0x40a006bb%bv : bv 32).
Proof. ftac. Qed.
Lemma D_040 : decode_any (0x40a006bb%bv : bv 32) = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_044 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_memset + 0x44)) = Some (0x03859813%bv : bv 32).
Proof. ftac. Qed.
Lemma D_044 : decode_any (0x03859813%bv : bv 32) = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_048 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_memset + 0x48)) = Some (0x101015b7%bv : bv 32).
Proof. ftac. Qed.
Lemma D_048 : decode_any (0x101015b7%bv : bv 32) = Some (Lui 11 65793, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_04c : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_memset + 0x4c)) = Some (0x0036f693%bv : bv 32).
Proof. ftac. Qed.
Lemma D_04c : decode_any (0x0036f693%bv : bv 32) = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_050 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_memset + 0x50)) = Some (0x00459713%bv : bv 32).
Proof. ftac. Qed.
Lemma D_050 : decode_any (0x00459713%bv : bv 32) = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_054 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_memset + 0x54)) = Some (0x40d60633%bv : bv 32).
Proof. ftac. Qed.
Lemma D_054 : decode_any (0x40d60633%bv : bv 32) = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_058 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_memset + 0x58)) = Some (0x00d505b3%bv : bv 32).
Proof. ftac. Qed.
Lemma D_058 : decode_any (0x00d505b3%bv : bv 32) = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_05c : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_memset + 0x5c)) = Some (0x10070693%bv : bv 32).
Proof. ftac. Qed.
Lemma D_05c : decode_any (0x10070693%bv : bv 32) = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_060 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_memset + 0x60)) = Some (0xffc67713%bv : bv 32).
Proof. ftac. Qed.
Lemma D_060 : decode_any (0xffc67713%bv : bv 32) = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_064 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_memset + 0x64)) = Some (0x02d83633%bv : bv 32).
Proof. ftac. Qed.
Lemma D_064 : decode_any (0x02d83633%bv : bv 32) = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_068 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_memset + 0x68)) = Some (0x00c5a023%bv : bv 32).
Proof. ftac. Qed.
Lemma D_068 : decode_any (0x00c5a023%bv : bv 32) = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_06c : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_memset + 0x6c)) = Some (0x00e586b3%bv : bv 32).
Proof. ftac. Qed.
Lemma D_06c : decode_any (0x00e586b3%bv : bv 32) = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_070 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_memset + 0x70)) = Some (0xfec6ae23%bv : bv 32).
Proof. ftac. Qed.
Lemma D_070 : decode_any (0xfec6ae23%bv : bv 32) = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_074 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_memset + 0x74)) = Some (0x08f76063%bv : bv 32).
Proof. ftac. Qed.
Lemma D_074 : decode_any (0x08f76063%bv : bv 32) = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_078 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_memset + 0x78)) = Some (0x00c5a223%bv : bv 32).
Proof. ftac. Qed.
Lemma D_078 : decode_any (0x00c5a223%bv : bv 32) = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_07c : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_memset + 0x7c)) = Some (0x00c5a423%bv : bv 32).
Proof. ftac. Qed.
Lemma D_07c : decode_any (0x00c5a423%bv : bv 32) = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_080 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_memset + 0x80)) = Some (0x01900793%bv : bv 32).
Proof. ftac. Qed.
Lemma D_080 : decode_any (0x01900793%bv : bv 32) = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_084 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_memset + 0x84)) = Some (0xfec6aa23%bv : bv 32).
Proof. ftac. Qed.
Lemma D_084 : decode_any (0xfec6aa23%bv : bv 32) = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_088 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_memset + 0x88)) = Some (0xfec6ac23%bv : bv 32).
Proof. ftac. Qed.
Lemma D_088 : decode_any (0xfec6ac23%bv : bv 32) = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_08c : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_memset + 0x8c)) = Some (0x06f76463%bv : bv 32).
Proof. ftac. Qed.
Lemma D_08c : decode_any (0x06f76463%bv : bv 32) = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_090 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_memset + 0x90)) = Some (0x00c5a623%bv : bv 32).
Proof. ftac. Qed.
Lemma D_090 : decode_any (0x00c5a623%bv : bv 32) = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_094 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_memset + 0x94)) = Some (0x00c5a823%bv : bv 32).
Proof. ftac. Qed.
Lemma D_094 : decode_any (0x00c5a823%bv : bv 32) = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_098 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_memset + 0x98)) = Some (0x00c5aa23%bv : bv 32).
Proof. ftac. Qed.
Lemma D_098 : decode_any (0x00c5aa23%bv : bv 32) = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_09c : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_memset + 0x9c)) = Some (0x00c5ac23%bv : bv 32).
Proof. ftac. Qed.
Lemma D_09c : decode_any (0x00c5ac23%bv : bv 32) = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_0a0 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_memset + 0xa0)) = Some (0x0045f793%bv : bv 32).
Proof. ftac. Qed.
Lemma D_0a0 : decode_any (0x0045f793%bv : bv 32) = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_0a4 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_memset + 0xa4)) = Some (0x02000813%bv : bv 32).
Proof. ftac. Qed.
Lemma D_0a4 : decode_any (0x02000813%bv : bv 32) = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_0a8 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_memset + 0xa8)) = Some (0x01878793%bv : bv 32).
Proof. ftac. Qed.
Lemma D_0a8 : decode_any (0x01878793%bv : bv 32) = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_0ac : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_memset + 0xac)) = Some (0x40f70733%bv : bv 32).
Proof. ftac. Qed.
Lemma D_0ac : decode_any (0x40f70733%bv : bv 32) = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_0b0 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_memset + 0xb0)) = Some (0xfec6a223%bv : bv 32).
Proof. ftac. Qed.
Lemma D_0b0 : decode_any (0xfec6a223%bv : bv 32) = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_0b4 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_memset + 0xb4)) = Some (0xfec6a423%bv : bv 32).
Proof. ftac. Qed.
Lemma D_0b4 : decode_any (0xfec6a423%bv : bv 32) = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_0b8 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_memset + 0xb8)) = Some (0xfec6a623%bv : bv 32).
Proof. ftac. Qed.
Lemma D_0b8 : decode_any (0xfec6a623%bv : bv 32) = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_0bc : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_memset + 0xbc)) = Some (0xfec6a823%bv : bv 32).
Proof. ftac. Qed.
Lemma D_0bc : decode_any (0xfec6a823%bv : bv 32) = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_0c0 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_memset + 0xc0)) = Some (0x03076a63%bv : bv 32).
Proof. ftac. Qed.
Lemma D_0c0 : decode_any (0x03076a63%bv : bv 32) = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_0c4 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_memset + 0xc4)) = Some (0x02061613%bv : bv 32).
Proof. ftac. Qed.
Lemma D_0c4 : decode_any (0x02061613%bv : bv 32) = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_0c8 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_memset + 0xc8)) = Some (0x00f585b3%bv : bv 32).
Proof. ftac. Qed.
Lemma D_0c8 : decode_any (0x00f585b3%bv : bv 32) = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_0cc : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_memset + 0xcc)) = Some (0x02065693%bv : bv 32).
Proof. ftac. Qed.
Lemma D_0cc : decode_any (0x02065693%bv : bv 32) = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_0d0 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_memset + 0xd0)) = Some (0x00d66633%bv : bv 32).
Proof. ftac. Qed.
Lemma D_0d0 : decode_any (0x00d66633%bv : bv 32) = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_0d4 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_memset + 0xd4)) = Some (0x01f00693%bv : bv 32).
Proof. ftac. Qed.
Lemma D_0d4 : decode_any (0x01f00693%bv : bv 32) = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_0d8 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_memset + 0xd8)) = Some (0x00c5b023%bv : bv 32).
Proof. ftac. Qed.
Lemma D_0d8 : decode_any (0x00c5b023%bv : bv 32) = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_0dc : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_memset + 0xdc)) = Some (0x00c5b423%bv : bv 32).
Proof. ftac. Qed.
Lemma D_0dc : decode_any (0x00c5b423%bv : bv 32) = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_0e0 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_memset + 0xe0)) = Some (0x00c5b823%bv : bv 32).
Proof. ftac. Qed.
Lemma D_0e0 : decode_any (0x00c5b823%bv : bv 32) = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_0e4 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_memset + 0xe4)) = Some (0x00c5bc23%bv : bv 32).
Proof. ftac. Qed.
Lemma D_0e4 : decode_any (0x00c5bc23%bv : bv 32) = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_0e8 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_memset + 0xe8)) = Some (0xfe070713%bv : bv 32).
Proof. ftac. Qed.
Lemma D_0e8 : decode_any (0xfe070713%bv : bv 32) = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_0ec : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_memset + 0xec)) = Some (0x02058593%bv : bv 32).
Proof. ftac. Qed.
Lemma D_0ec : decode_any (0x02058593%bv : bv 32) = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_0f0 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_memset + 0xf0)) = Some (0xfee6e4e3%bv : bv 32).
Proof. ftac. Qed.
Lemma D_0f0 : decode_any (0xfee6e4e3%bv : bv 32) = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_0f4 : fetch_word tfibsegs (Z_to_bv 64 (tfib_A_musl_memset + 0xf4)) = Some (0x00008067%bv : bv 32).
Proof. ftac. Qed.
Lemma D_0f4 : decode_any (0x00008067%bv : bv 32) = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma wbytes_repeat_spec : forall k (c : byte) m (a x : word),
bv_unsigned a + Z.of_nat k <= 2^64 ->
wbytes m a (repeat c k) x =
if (bv_unsigned a <=? bv_unsigned x) && (bv_unsigned x <? bv_unsigned a + Z.of_nat k)
then Some c else m x.
Proof.
induction k as [|k IH]; intros c m a x Hnw.
- cbn [repeat wbytes]. destruct (_ && _) eqn:E; [|reflexivity].
apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. cbn in E2. lia.
- cbn [repeat wbytes]. pose proof (u64_range a) as Ha. pose proof (u64_range x) as Hx.
destruct k as [|k'].
+ cbn [repeat wbytes]. unfold bv_eqb.
destruct (Z.eqb_spec (bv_unsigned x) (bv_unsigned a)) as [E|E].
* replace (_ && _) with true; [reflexivity|]. symmetry. apply andb_true_intro.
split; [apply Z.leb_le|apply Z.ltb_lt]; cbn; lia.
* destruct (_ && _) eqn:E2; [|reflexivity].
apply andb_prop in E2 as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. cbn in E2. lia.
+ assert (Hu1 : bv_unsigned (a + 1) = bv_unsigned a + 1) by (apply u_add1; cbn [length] in Hnw; lia).
rewrite IH by (cbn [repeat length] in *; lia). rewrite Hu1. unfold bv_eqb.
destruct (Z.eqb_spec (bv_unsigned x) (bv_unsigned a)) as [E|E].
* rewrite E. replace (bv_unsigned a + 1 <=? bv_unsigned a) with false by (symmetry; apply Z.leb_gt; lia).
cbn [andb]. replace (_ && _) with true; [reflexivity|]. symmetry. apply andb_true_intro.
split; [apply Z.leb_le|apply Z.ltb_lt]; lia.
* destruct ((bv_unsigned a + 1 <=? bv_unsigned x) && _) eqn:E1;
destruct ((bv_unsigned a <=? bv_unsigned x) && _) eqn:E2; try reflexivity.
-- apply andb_prop in E1 as [E1 E3]. apply Z.leb_le in E1. apply Z.ltb_lt in E3.
apply andb_false_iff in E2. destruct E2 as [E2|E2]; [apply Z.leb_gt in E2|apply Z.ltb_ge in E2]; lia.
-- apply andb_prop in E2 as [E2 E3]. apply Z.leb_le in E2. apply Z.ltb_lt in E3.
apply andb_false_iff in E1. destruct E1 as [E1|E1]; [apply Z.leb_gt in E1|apply Z.ltb_ge in E1]; lia.
Qed.
Lemma length_repeat_Z : forall {A} (c : A) k, Z.of_nat (length (repeat c k)) = Z.of_nat k.
Proof. intros. rewrite repeat_length. reflexivity. Qed.
Fixpoint bytes_eqb (l1 l2 : list byte) : bool :=
match l1, l2 with
| [], [] => true
| b1 :: t1, b2 :: t2 => Z.eqb (bv_unsigned b1) (bv_unsigned b2) && bytes_eqb t1 t2
| _, _ => false
end.
Lemma bytes_eqb_eq : forall l1 l2, bytes_eqb l1 l2 = true -> l1 = l2.
Proof.
induction l1 as [|b1 t1 IH]; intros [|b2 t2] H; cbn in H; try discriminate; [reflexivity|].
apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. f_equal; [apply bv_eq; exact H1|apply IH; exact H2].
Qed.
Definition c32_of (C : Z) : Z := C * 0x01010101.
Definition c64_of (C : Z) : Z := C * 0x0101010101010101.
Lemma fill_tab :
forallb (fun C =>
bytes_eqb (word_to_le_bytes 1 (Z_to_bv 64 C)) (repeat (Z_to_bv 8 C) 1) &&
bytes_eqb (word_to_le_bytes 4 (Z_to_bv 64 (c32_of C))) (repeat (Z_to_bv 8 C) 4) &&
bytes_eqb (word_to_le_bytes 8 (Z_to_bv 64 (c64_of C))) (repeat (Z_to_bv 8 C) 8) &&
(Z.shiftr ((C * 2^56) * 0x101010100) 64 =? c32_of C) &&
(Z.lor (c32_of C * 2^32) (Z.shiftr (c32_of C * 2^32) 32) =? c64_of C))
(zseq 0 256) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma fill_facts : forall C, 0 <= C < 256 ->
word_to_le_bytes 1 (Z_to_bv 64 C) = repeat (Z_to_bv 8 C) 1 /\
word_to_le_bytes 4 (Z_to_bv 64 (c32_of C)) = repeat (Z_to_bv 8 C) 4 /\
word_to_le_bytes 8 (Z_to_bv 64 (c64_of C)) = repeat (Z_to_bv 8 C) 8 /\
Z.shiftr ((C * 2^56) * 0x101010100) 64 = c32_of C /\
Z.lor (c32_of C * 2^32) (Z.shiftr (c32_of C * 2^32) 32) = c64_of C.
Proof.
intros C HC. pose proof fill_tab as T. rewrite forallb_forall in T.
specialize (T C (proj2 (In_zseq 0 256 C) ltac:(lia))). cbn beta in T.
apply andb_prop in T as [T H5]. apply andb_prop in T as [T H4].
apply andb_prop in T as [T H3]. apply andb_prop in T as [H1 H2].
apply bytes_eqb_eq in H1. apply bytes_eqb_eq in H2. apply bytes_eqb_eq in H3.
apply Z.eqb_eq in H4. apply Z.eqb_eq in H5.
repeat split; assumption.
Qed.
Section g.
Variables d cw : word.
Variable n : nat.
Variables mem rom : word -> option byte.
Definition D : Z := bv_unsigned d.
Definition N : Z := Z.of_nat n.
Definition C : Z := bv_unsigned cw mod 256.
Definition cb : byte := Z_to_bv 8 C.
Definition c32w : word := Z_to_bv 64 (c32_of C).
Definition c64w : word := Z_to_bv 64 (c64_of C).
Hypothesis Hdst : store_ok tfibsegs mem d n = true.
Hypothesis Hnd : bv_unsigned d + Z.of_nat n <= 2^64.
Hypothesis HN64 : Z.of_nat n < 2^64.
Lemma D_facts : D = bv_unsigned d /\ N = Z.of_nat n /\ 0 <= D < 2^64 /\ 0 <= N < 2^64 /\ D + N <= 2^64 /\ 0 <= C < 256.
Proof.
pose proof (u64_range d). unfold D, N, C.
pose proof (Z.mod_pos_bound (bv_unsigned cw) 256 ltac:(lia)). lia.
Qed.
Ltac dfacts := pose proof D_facts as HDF; destruct HDF as (HD_ & HN_ & HDr & HNr & HDN & HCr).
Definition inv (m : word -> option byte) : Prop :=
mem_grows mem m /\
forall x, m x = mem x \/ (D <= bv_unsigned x < D + N /\ m x = Some cb).
Definition cov (m : word -> option byte) (a k : Z) : Prop :=
forall x : word, a <= bv_unsigned x < a + k -> m x = Some cb.
Definition fill (m : word -> option byte) (a : Z) (k : nat) : word -> option byte :=
wbytes m (Z_to_bv 64 a) (repeat cb k).
Lemma inv_mem : inv mem.
Proof. split; [apply mem_grows_refl|]. intros x. left. reflexivity. Qed.
Lemma fill_spec : forall m a k x, 0 <= a -> (0 < k)%nat -> a + Z.of_nat k <= 2^64 ->
fill m a k x = if (a <=? bv_unsigned x) && (bv_unsigned x <? a + Z.of_nat k) then Some cb else m x.
Proof.
intros m a k x Ha Hk0 Hk. unfold fill. rewrite wbytes_repeat_spec by (rewrite u_Z2bv by lia; lia).
rewrite u_Z2bv by lia. reflexivity.
Qed.
Lemma inv_fill : forall m a k, inv m -> (0 < k)%nat -> D <= a -> a + Z.of_nat k <= D + N -> inv (fill m a k).
Proof.
intros m a k [Hg Hi] Hk0 Ha Hk. dfacts. split.
- eapply mem_grows_trans; [exact Hg|]. unfold fill. apply wbytes_grows.
- intros x. rewrite fill_spec by lia.
destruct (_ && _) eqn:E.
+ apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. right. split; [lia|reflexivity].
+ apply Hi.
Qed.
Lemma cov_fill_new : forall m a k, 0 <= a -> (0 < k)%nat -> a + Z.of_nat k <= 2^64 -> cov (fill m a k) a (Z.of_nat k).
Proof.
intros m a k Ha Hk0 Hk x Hx. rewrite fill_spec by lia.
replace (_ && _) with true; [reflexivity|].
symmetry. apply andb_true_intro. split; [apply Z.leb_le|apply Z.ltb_lt]; lia.
Qed.
Lemma cov_fill_keep : forall m a k a' k', 0 <= a -> (0 < k)%nat -> a + Z.of_nat k <= 2^64 ->
cov m a' k' -> cov (fill m a k) a' k'.
Proof.
intros m a k a' k' Ha Hk0 Hk Hc x Hx. rewrite fill_spec by lia.
destruct (_ && _); [reflexivity|]. apply Hc. exact Hx.
Qed.
Definition covP (m : word -> option byte) (P : Z -> Prop) : Prop :=
forall x : word, D <= bv_unsigned x < D + N -> P (bv_unsigned x) -> m x = Some cb.
Lemma covP_fill : forall m a k (P Q : Z -> Prop), 0 <= a -> (0 < k)%nat -> a + Z.of_nat k <= 2^64 ->
covP m P ->
(forall z, D <= z < D + N -> Q z -> P z \/ a <= z < a + Z.of_nat k) ->
covP (fill m a k) Q.
Proof.
intros m a k P Q Ha Hk0 Hk Hc HQ x Hx HQx. rewrite fill_spec by lia.
destruct (_ && _) eqn:E; [reflexivity|].
destruct (HQ _ Hx HQx) as [HP|Hin]; [apply Hc; assumption|].
exfalso. apply andb_false_iff in E. destruct E as [E|E]; [apply Z.leb_gt in E|apply Z.ltb_ge in E]; lia.
Qed.
Lemma covP_weaken : forall m (P Q : Z -> Prop),
covP m P -> (forall z, D <= z < D + N -> Q z -> P z) -> covP m Q.
Proof. intros m P Q Hc HQ x Hx HQx. apply Hc; [exact Hx|]. apply HQ; assumption. Qed.
Definition post (m' : word -> option byte) : Prop :=
(forall x : word, D <= bv_unsigned x < D + N -> m' x = Some cb) /\
(forall x : word, ~ (D <= bv_unsigned x < D + N) -> m' x = mem x).
Lemma post_of_inv : forall m, inv m -> covP m (fun _ => True) -> post m.
Proof.
intros m [Hg Hi] Hc. split.
- intros x Hx. apply Hc; [exact Hx|exact I].
- intros x Hx. destruct (Hi x) as [E|[Hr E]]; [exact E|]. exfalso. apply Hx. exact Hr.
Qed.
Lemma fill_ok : forall m a k, inv m -> (0 < k)%nat -> D <= a -> a + Z.of_nat k <= D + N ->
store_ok tfibsegs m (Z_to_bv 64 a) k = true.
Proof.
intros m a k [Hg _] Hk0 Ha Hk. dfacts.
eapply store_ok_mono; [exact Hg|].
eapply (store_ok_sub tfibsegs mem d _ n); [lia | exact Hdst | |]; rewrite u_Z2bv by lia; lia.
Qed.
Lemma cb_of_cw : Z_to_bv 8 (bv_unsigned cw) = cb.
Proof.
unfold cb, C. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 8) with 256. rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma sb_bytes : word_to_le_bytes 1 cw = repeat cb 1.
Proof. unfold word_to_le_bytes. cbn [Z_to_le_bytes repeat]. rewrite cb_of_cw. reflexivity. Qed.
Lemma sb_bytes1 : word_to_le_bytes 1 cw = [cb].
Proof. exact sb_bytes. Qed.
Lemma sw_bytes : word_to_le_bytes 4 c32w = repeat cb 4.
Proof. dfacts. unfold c32w, cb. apply (proj1 (proj2 (fill_facts C ltac:(lia)))). Qed.
Lemma sd_bytes : word_to_le_bytes 8 c64w = repeat cb 8.
Proof. dfacts. unfold c64w, cb. apply (proj1 (proj2 (proj2 (fill_facts C ltac:(lia))))). Qed.
Lemma c32_range : 0 <= c32_of C < 2^32.
Proof. dfacts. unfold c32_of. lia. Qed.
Lemma c64_range : 0 <= c64_of C < 2^64.
Proof. dfacts. unfold c64_of. lia. Qed.
Lemma slli56_val : v_slli cw 56 = Z_to_bv 64 (C * 2^56).
Proof.
dfacts. unfold v_slli, C. apply bv_eq. rewrite !Z_to_bv_unsigned. rewrite Z.shiftl_mul_pow2 by lia.
unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64).
pose proof (u64_range cw). rewrite (Z.div_mod (bv_unsigned cw) 256) at 1 by lia.
replace ((256 * (bv_unsigned cw / 256) + bv_unsigned cw mod 256) * 2^56)
with (bv_unsigned cw mod 256 * 2^56 + (bv_unsigned cw / 256) * 2^64) by lia.
rewrite Z.mod_add by lia.
pose proof (Z.mod_pos_bound (bv_unsigned cw) 256 ltac:(lia)).
rewrite !Z.mod_small by lia. reflexivity.
Qed.
Lemma mulhu_val : v_mulhu (Z_to_bv 64 (C * 2^56)) (Z_to_bv 64 0x101010100) = c32w.
Proof.
dfacts. unfold v_mulhu, c32w. f_equal. rewrite !u_Z2bv by lia.
apply (fill_facts C). lia.
Qed.
Lemma c64_val : v_or (v_slli c32w 32) (v_srli (v_slli c32w 32) 32) = c64w.
Proof.
dfacts. pose proof c32_range. pose proof c64_range.
unfold v_or, v_slli, v_srli, c32w, c64w. f_equal.
rewrite !Z.shiftl_mul_pow2 by lia. rewrite (u_Z2bv (c32_of C)) by lia.
rewrite (u_Z2bv (c32_of C * 2^32)) by lia.
assert (Hs : 0 <= Z.shiftr (c32_of C * 2^32) 32 < 2^64).
{ rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; lia]. }
rewrite u_Z2bv by lia.
apply (fill_facts C). lia.
Qed.
Lemma negand3_val : v_andi (v_subw (Z_to_bv 64 0) d) 3 = Z_to_bv 64 ((- D) mod 4).
Proof.
dfacts. unfold v_andi, v_subw. f_equal.
rewrite Z_to_bv_unsigned, wrap64_swrap32.
change (bv_wrap 64 3) with (Z.ones 2). rewrite land_sx32_small by (split; [easy|reflexivity]).
rewrite Z.land_ones by lia. change (bv_unsigned (Z_to_bv 64 0)) with 0. unfold D. f_equal.
Qed.
Lemma andm4_val : forall z, 0 <= z < 2^64 -> v_andi (Z_to_bv 64 z) (-4) = Z_to_bv 64 (z - z mod 4).
Proof.
intros z Hz. unfold v_andi. f_equal. rewrite u_Z2bv by lia.
change (bv_wrap 64 (-4)) with (2^64 - 2^2). rewrite land_neg_pow2_u64 by lia. reflexivity.
Qed.
Lemma and4_val : forall z, 0 <= z < 2^64 -> v_andi (Z_to_bv 64 z) 4 = Z_to_bv 64 (Z.land z 4).
Proof. intros z Hz. unfold v_andi. f_equal. rewrite u_Z2bv by lia. reflexivity. Qed.
Definition keep (r : reg) : Prop :=
r <> 11%bv /\ r <> 12%bv /\ r <> 13%bv /\ r <> 14%bv /\ r <> 15%bv /\ r <> 16%bv.
Definition fin (regs : bvmap 5 word) (pc : word) (m : word -> option byte) : Prop :=
exists regs' m',
msteps tfibsegs (mkst regs pc m rom) (mkst regs' (v_jalr (getr regs 1) 0) m' rom)
/\ post m'
/\ forall r, keep r -> getr regs' r = getr regs r.
Lemma keep_1 : keep 1.
Proof. unfold keep. repeat split; reg_neq_tac. Qed.
Lemma fin_steps : forall regs pc m regs2 pc2 m2,
msteps tfibsegs (mkst regs pc m rom) (mkst regs2 pc2 m2 rom) ->
(forall r, keep r -> getr regs2 r = getr regs r) ->
fin regs2 pc2 m2 -> fin regs pc m.
Proof.
intros regs pc m regs2 pc2 m2 Hms Hfr (regs' & m' & Hms' & Hp & Hfr').
exists regs', m'. split; [|split; [exact Hp|]].
- eapply msteps_trans; [exact Hms|]. rewrite <- (Hfr 1%bv keep_1). exact Hms'.
- intros r Hr. rewrite (Hfr' r Hr). apply Hfr. exact Hr.
Qed.
Lemma fin_pc : forall regs (pc pc' : word) m,
bv_unsigned pc = bv_unsigned pc' -> fin regs pc' m -> fin regs pc m.
Proof. intros regs pc pc' m H Hf. replace pc with pc' by (apply bv_eq; symmetry; exact H). exact Hf. Qed.
Ltac frame :=
let r := fresh "r" in let Hr := fresh "Hkeep" in
intros r Hr; unfold keep in Hr;
destruct Hr as (?&?&?&?&?&?);
rewrite ?getr_other by assumption; reflexivity.
Ltac fin_apply L :=
eapply fin_pc; [ | eapply L ]; [ vm_compute; reflexivity | .. ].
Lemma ret_0f4 : forall regs m, inv m -> covP m (fun _ => True) ->
fin regs (Z_to_bv 64 (tfib_A_musl_memset + 0xf4)) m.
Proof.
intros regs m Hi Hc. exists regs, m. split; [|split; [apply post_of_inv; assumption|intros; reflexivity]].
norm_pc. stepret F_0f4 D_0f4. apply mst_refl.
Qed.
Lemma store_ok_fill : forall m a' k' a k,
store_ok tfibsegs m a k = true -> store_ok tfibsegs (fill m a' k') a k = true.
Proof. intros. eapply store_ok_mono; [|eassumption]. unfold fill. apply wbytes_grows. Qed.
Lemma covP_fill' : forall m a k (P : Z -> Prop), 0 <= a -> (0 < k)%nat -> a + Z.of_nat k <= 2^64 ->
covP m P -> covP (fill m a k) (fun z => P z \/ a <= z < a + Z.of_nat k).
Proof. intros m a k P Ha Hk0 Hk Hc. eapply covP_fill; [exact Ha|exact Hk0|exact Hk|exact Hc|]. intros z _ Hz. exact Hz. Qed.
Ltac solve_ok := repeat apply store_ok_fill; apply fill_ok; [assumption | cbv; lia | lia | lia].
Ltac fold_fill k :=
lazymatch goal with
| |- context [wbytes ?m' (Z_to_bv 64 ?a') (repeat cb k)] =>
change (wbytes m' (Z_to_bv 64 a') (repeat cb k)) with (fill m' a' k)
end.
Ltac stepsd F0 D0 addr :=
let F := litF F0 in
chain_step;
[ reflexivity
| eapply step_sd_at with (a := Z_to_bv 64 addr) (v := c64w);
[ exact F | reflexivity | exact D0 | val | gr; rwH; reflexivity | solve_ok ]
| step_simpl; rewrite sd_bytes; fold_fill 8%nat ].
Ltac stepsw F0 D0 addr :=
let F := litF F0 in
chain_step;
[ reflexivity
| eapply step_sw_at with (a := Z_to_bv 64 addr) (v := c32w);
[ exact F | reflexivity | exact D0 | val | gr; rwH; reflexivity | solve_ok ]
| step_simpl; rewrite sw_bytes; fold_fill 4%nat ].
Ltac stepsb F0 D0 addr :=
let F := litF F0 in
chain_step;
[ reflexivity
| eapply step_sb_l with (a := addr) (b := cb);
[ exact F | reflexivity | exact D0 | val | gr; rwH; apply sb_bytes1 | solve_ok ]
| step_simpl;
lazymatch goal with
| |- context [wbytes ?m' (Z_to_bv 64 ?a') [cb]] =>
change (wbytes m' (Z_to_bv 64 a') [cb]) with (fill m' a' 1)
end ].
Ltac inv_tac := repeat (apply inv_fill; [|cbv; lia|lia|lia]); assumption.
Lemma loop_0d8 : forall (q : nat) regs m (s r : Z),
inv m ->
getr regs 11 = Z_to_bv 64 s ->
getr regs 12 = c64w ->
getr regs 13 = Z_to_bv 64 31 ->
getr regs 14 = Z_to_bv 64 r ->
32 * (Z.of_nat q + 1) <= r < 32 * (Z.of_nat q + 2) ->
D <= s -> s + 32 * (Z.of_nat q + 1) <= D + N ->
covP m (fun z => z < s \/ s + 32 * (Z.of_nat q + 1) <= z) ->
fin regs (Z_to_bv 64 (tfib_A_musl_memset + 0xd8)) m.
Proof.
induction q as [|q IH]; intros regs m s r Hinv H11 H12 H13 H14 Hr Hs HsN Hcov; dfacts.
-
eapply fin_steps.
+ norm_pc.
stepsd F_0d8 D_0d8 s.
stepsd F_0dc D_0dc (s + 8).
stepsd F_0e0 D_0e0 (s + 16).
stepsd F_0e4 D_0e4 (s + 24).
sv F_0e8 D_0e8 (Z_to_bv 64 (r - 32)).
sv F_0ec D_0ec (Z_to_bv 64 (s + 32)).
stepbf F_0f0 D_0f0.
apply mst_refl.
+ frame.
+ fin_apply ret_0f4.
* inv_tac.
* eapply covP_weaken.
-- repeat (apply covP_fill'; [lia|cbv; lia|lia|]). exact Hcov.
-- cbn beta. intros z Hz _. lia.
- eapply fin_steps.
+ norm_pc.
stepsd F_0d8 D_0d8 s.
stepsd F_0dc D_0dc (s + 8).
stepsd F_0e0 D_0e0 (s + 16).
stepsd F_0e4 D_0e4 (s + 24).
sv F_0e8 D_0e8 (Z_to_bv 64 (r - 32)).
sv F_0ec D_0ec (Z_to_bv 64 (s + 32)).
stepbt F_0f0 D_0f0.
apply mst_refl.
+ frame.
+ fin_apply (fun regs m => IH regs m (s + 32) (r - 32)).
* inv_tac.
* gr. reflexivity.
* gr. exact H12.
* gr. exact H13.
* gr. reflexivity.
* lia.
* lia.
* lia.
* eapply covP_weaken.
-- repeat (apply covP_fill'; [lia|cbv; lia|lia|]). exact Hcov.
-- cbn beta. intros z Hz HH. lia.
Qed.
Lemma step_subw_at : forall segs regs pc mm rr w rd rs1 rs2 v,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Op32 ALU_SUB rd rs1 rs2, 4%Z) ->
bv_eqb rd 0 = false ->
v_subw (getr regs rs1) (getr regs rs2) = v ->
RiscvSemantics.step segs (mkst regs pc mm rr) =
MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mm rr).
Proof.
intros * Hf He Hd Hrd Hv.
rewrite (step_subw segs regs pc mm rr w rd rs1 rs2 Hf He Hd), Hrd, Hv. reflexivity.
Qed.
Lemma step_mulhu_at : forall segs regs pc mm rr w rd rs1 rs2 v,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Mul M_MULHU rd rs1 rs2, 4%Z) ->
bv_eqb rd 0 = false ->
v_mulhu (getr regs rs1) (getr regs rs2) = v ->
RiscvSemantics.step segs (mkst regs pc mm rr) =
MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mm rr).
Proof.
intros * Hf He Hd Hrd Hv.
rewrite (step_mulhu segs regs pc mm rr w rd rs1 rs2 Hf He Hd), Hrd, Hv. reflexivity.
Qed.
Ltac svt F D vv tac := let F' := litF F in stepiv F' D vv tac.
Ltac svat L F0 D vv tac :=
let F := litF F0 in
chain_step;
[ reflexivity
| eapply L with (v := vv); [ exact F | reflexivity | exact D | reflexivity | tac ]
| step_simpl ].
Lemma blk_0c4 : forall regs m (s1 n2 k2 e1 j2 : Z),
inv m ->
getr regs 11 = Z_to_bv 64 s1 ->
getr regs 12 = c32w ->
getr regs 14 = Z_to_bv 64 n2 ->
getr regs 15 = Z_to_bv 64 k2 ->
32 <= n2 -> n2 = 4 * j2 -> 0 <= k2 ->
D <= s1 -> s1 + k2 + n2 = e1 -> e1 <= D + N ->
covP m (fun z => z < s1 + k2 \/ e1 - 28 <= z) ->
fin regs (Z_to_bv 64 (tfib_A_musl_memset + 0xc4)) m.
Proof.
intros regs m s1 n2 k2 e1 j2 Hinv H11 H12 H14 H15 Hn2 Hj2 Hk2 Hs1 He1 He1N Hcov. dfacts.
pose proof c32_range as Hc32.
pose proof (Z.div_mod n2 32 ltac:(lia)) as Hqr. pose proof (Z.mod_pos_bound n2 32 ltac:(lia)) as Hrr.
set (qq := n2 / 32) in *. set (rr := n2 mod 32) in *.
eapply fin_steps.
- norm_pc.
svt F_0c4 D_0c4 (v_slli c32w 32) ltac:(gr; rwH; reflexivity).
svt F_0c8 D_0c8 (Z_to_bv 64 (s1 + k2)) val.
svt F_0cc D_0cc (v_srli (v_slli c32w 32) 32) ltac:(gr; rwH; reflexivity).
svor F_0d0 D_0d0 c64w. { apply c64_val. }
svt F_0d4 D_0d4 (Z_to_bv 64 31) val.
apply mst_refl.
- frame.
- fin_apply (fun regs m => loop_0d8 (Z.to_nat (qq - 1)) regs m (s1 + k2) n2).
+ exact Hinv.
+ gr. reflexivity.
+ gr. reflexivity.
+ gr. reflexivity.
+ gr. exact H14.
+ rewrite Z2Nat.id by lia. lia.
+ lia.
+ rewrite Z2Nat.id by lia. lia.
+ rewrite Z2Nat.id by lia. eapply covP_weaken; [exact Hcov|]. cbn beta. intros z Hz HH. lia.
Qed.
Lemma blk_090 : forall regs m (s1 n1 e1 j1 : Z),
inv m ->
getr regs 11 = Z_to_bv 64 s1 ->
getr regs 12 = c32w ->
getr regs 13 = Z_to_bv 64 e1 ->
getr regs 14 = Z_to_bv 64 n1 ->
25 <= n1 -> n1 = 4 * j1 ->
D <= s1 -> s1 + n1 = e1 -> e1 <= D + N ->
covP m (fun z => z < s1 + 12 \/ e1 - 12 <= z) ->
fin regs (Z_to_bv 64 (tfib_A_musl_memset + 0x90)) m.
Proof.
intros regs m s1 n1 e1 j1 Hinv H11 H12 H13 H14 Hn1 Hj1 Hs1 He1 He1N Hcov. dfacts.
destruct (land4_cases s1) as [Ht|Ht].
all: destruct (Z_lt_le_dec (n1 - (24 + Z.land s1 4)) 32) as [Hsmall|Hbig].
-
eapply fin_steps.
+ norm_pc.
stepsw F_090 D_090 (s1 + 12).
stepsw F_094 D_094 (s1 + 16).
stepsw F_098 D_098 (s1 + 20).
stepsw F_09c D_09c (s1 + 24).
svt F_0a0 D_0a0 (Z_to_bv 64 (Z.land s1 4)) ltac:(gr; rwH; apply and4_val; lia).
svt F_0a4 D_0a4 (Z_to_bv 64 32) val.
svt F_0a8 D_0a8 (Z_to_bv 64 (24 + Z.land s1 4)) val.
svt F_0ac D_0ac (Z_to_bv 64 (n1 - (24 + Z.land s1 4))) val.
stepsw F_0b0 D_0b0 (e1 - 28).
stepsw F_0b4 D_0b4 (e1 - 24).
stepsw F_0b8 D_0b8 (e1 - 20).
stepsw F_0bc D_0bc (e1 - 16).
stepbt F_0c0 D_0c0.
apply mst_refl.
+ frame.
+ fin_apply ret_0f4.
* inv_tac.
* eapply covP_weaken.
-- repeat (apply covP_fill'; [lia|cbv; lia|lia|]). exact Hcov.
-- cbn beta. intros z Hz _. lia.
-
eapply fin_steps.
+ norm_pc.
stepsw F_090 D_090 (s1 + 12).
stepsw F_094 D_094 (s1 + 16).
stepsw F_098 D_098 (s1 + 20).
stepsw F_09c D_09c (s1 + 24).
svt F_0a0 D_0a0 (Z_to_bv 64 (Z.land s1 4)) ltac:(gr; rwH; apply and4_val; lia).
svt F_0a4 D_0a4 (Z_to_bv 64 32) val.
svt F_0a8 D_0a8 (Z_to_bv 64 (24 + Z.land s1 4)) val.
svt F_0ac D_0ac (Z_to_bv 64 (n1 - (24 + Z.land s1 4))) val.
stepsw F_0b0 D_0b0 (e1 - 28).
stepsw F_0b4 D_0b4 (e1 - 24).
stepsw F_0b8 D_0b8 (e1 - 20).
stepsw F_0bc D_0bc (e1 - 16).
stepbf F_0c0 D_0c0.
apply mst_refl.
+ frame.
+ fin_apply (fun regs m => blk_0c4 regs m s1 (n1 - (24 + Z.land s1 4)) (24 + Z.land s1 4) e1 (j1 - 6)).
* inv_tac.
* gr. exact H11.
* gr. exact H12.
* gr. reflexivity.
* gr. reflexivity.
* lia.
* lia.
* lia.
* lia.
* lia.
* lia.
* eapply covP_weaken.
-- repeat (apply covP_fill'; [lia|cbv; lia|lia|]). exact Hcov.
-- cbn beta. intros z Hz HH. lia.
-
eapply fin_steps.
+ norm_pc.
stepsw F_090 D_090 (s1 + 12).
stepsw F_094 D_094 (s1 + 16).
stepsw F_098 D_098 (s1 + 20).
stepsw F_09c D_09c (s1 + 24).
svt F_0a0 D_0a0 (Z_to_bv 64 (Z.land s1 4)) ltac:(gr; rwH; apply and4_val; lia).
svt F_0a4 D_0a4 (Z_to_bv 64 32) val.
svt F_0a8 D_0a8 (Z_to_bv 64 (24 + Z.land s1 4)) val.
svt F_0ac D_0ac (Z_to_bv 64 (n1 - (24 + Z.land s1 4))) val.
stepsw F_0b0 D_0b0 (e1 - 28).
stepsw F_0b4 D_0b4 (e1 - 24).
stepsw F_0b8 D_0b8 (e1 - 20).
stepsw F_0bc D_0bc (e1 - 16).
stepbt F_0c0 D_0c0.
apply mst_refl.
+ frame.
+ fin_apply ret_0f4.
* inv_tac.
* eapply covP_weaken.
-- repeat (apply covP_fill'; [lia|cbv; lia|lia|]). exact Hcov.
-- cbn beta. intros z Hz _. lia.
-
eapply fin_steps.
+ norm_pc.
stepsw F_090 D_090 (s1 + 12).
stepsw F_094 D_094 (s1 + 16).
stepsw F_098 D_098 (s1 + 20).
stepsw F_09c D_09c (s1 + 24).
svt F_0a0 D_0a0 (Z_to_bv 64 (Z.land s1 4)) ltac:(gr; rwH; apply and4_val; lia).
svt F_0a4 D_0a4 (Z_to_bv 64 32) val.
svt F_0a8 D_0a8 (Z_to_bv 64 (24 + Z.land s1 4)) val.
svt F_0ac D_0ac (Z_to_bv 64 (n1 - (24 + Z.land s1 4))) val.
stepsw F_0b0 D_0b0 (e1 - 28).
stepsw F_0b4 D_0b4 (e1 - 24).
stepsw F_0b8 D_0b8 (e1 - 20).
stepsw F_0bc D_0bc (e1 - 16).
stepbf F_0c0 D_0c0.
apply mst_refl.
+ frame.
+ fin_apply (fun regs m => blk_0c4 regs m s1 (n1 - (24 + Z.land s1 4)) (24 + Z.land s1 4) e1 (j1 - 7)).
* inv_tac.
* gr. exact H11.
* gr. exact H12.
* gr. reflexivity.
* gr. reflexivity.
* lia.
* lia.
* lia.
* lia.
* lia.
* lia.
* eapply covP_weaken.
-- repeat (apply covP_fill'; [lia|cbv; lia|lia|]). exact Hcov.
-- cbn beta. intros z Hz HH. lia.
Qed.
Lemma blk_078 : forall regs m (s1 n1 e1 j1 : Z),
inv m ->
getr regs 11 = Z_to_bv 64 s1 ->
getr regs 12 = c32w ->
getr regs 13 = Z_to_bv 64 e1 ->
getr regs 14 = Z_to_bv 64 n1 ->
9 <= n1 -> n1 = 4 * j1 ->
D <= s1 -> s1 + n1 = e1 -> e1 <= D + N ->
covP m (fun z => z < s1 + 4 \/ e1 - 4 <= z) ->
fin regs (Z_to_bv 64 (tfib_A_musl_memset + 0x78)) m.
Proof.
intros regs m s1 n1 e1 j1 Hinv H11 H12 H13 H14 Hn1 Hj1 Hs1 He1 He1N Hcov. dfacts.
destruct (Z_lt_le_dec n1 25) as [Hsmall|Hbig].
- eapply fin_steps.
+ norm_pc.
stepsw F_078 D_078 (s1 + 4).
stepsw F_07c D_07c (s1 + 8).
svt F_080 D_080 (Z_to_bv 64 25) val.
stepsw F_084 D_084 (e1 - 12).
stepsw F_088 D_088 (e1 - 8).
stepbt F_08c D_08c.
apply mst_refl.
+ frame.
+ fin_apply ret_0f4.
* inv_tac.
* eapply covP_weaken.
-- repeat (apply covP_fill'; [lia|cbv; lia|lia|]). exact Hcov.
-- cbn beta. intros z Hz _. lia.
- eapply fin_steps.
+ norm_pc.
stepsw F_078 D_078 (s1 + 4).
stepsw F_07c D_07c (s1 + 8).
svt F_080 D_080 (Z_to_bv 64 25) val.
stepsw F_084 D_084 (e1 - 12).
stepsw F_088 D_088 (e1 - 8).
stepbf F_08c D_08c.
apply mst_refl.
+ frame.
+ fin_apply (fun regs m => blk_090 regs m s1 n1 e1 j1).
* inv_tac.
* gr. exact H11.
* gr. exact H12.
* gr. exact H13.
* gr. exact H14.
* lia.
* lia.
* lia.
* lia.
* lia.
* eapply covP_weaken.
-- repeat (apply covP_fill'; [lia|cbv; lia|lia|]). exact Hcov.
-- cbn beta. intros z Hz HH. lia.
Qed.
Lemma blk_040 : forall regs m,
inv m ->
getr regs 10 = Z_to_bv 64 D ->
getr regs 11 = cw ->
getr regs 12 = Z_to_bv 64 N ->
getr regs 15 = Z_to_bv 64 9 ->
9 <= N ->
covP m (fun z => z < D + 4 \/ D + N - 4 <= z) ->
fin regs (Z_to_bv 64 (tfib_A_musl_memset + 0x40)) m.
Proof.
intros regs m Hinv H10 H11 H12 H15 HN9 Hcov. dfacts.
pose proof (Z.mod_pos_bound (- D) 4 ltac:(lia)) as Hk.
set (k := (- D) mod 4) in *.
assert (Hk4 : (D + k) mod 4 = 0).
{ subst k. rewrite Zplus_mod_idemp_r. replace (D + - D) with 0 by lia. reflexivity. }
pose proof (Z.mod_pos_bound (N - k) 4 ltac:(lia)) as Hr1.
pose proof (Z.div_mod (N - k) 4 ltac:(lia)) as Hq1.
set (r1 := (N - k) mod 4) in *. set (j1 := (N - k) / 4) in *.
set (s1 := D + k). set (n1 := N - k - r1). set (e1 := s1 + n1).
destruct (Z_lt_le_dec n1 9) as [Hsmall|Hbig].
- eapply fin_steps.
+ norm_pc.
svat step_subw_at F_040 D_040 (v_subw (Z_to_bv 64 0) d) ltac:(gr; rwH; rewrite HD_, Z_to_bv_bv_unsigned; reflexivity).
svt F_044 D_044 (Z_to_bv 64 (C * 2^56)) ltac:(gr; rwH; apply slli56_val).
svt F_048 D_048 (Z_to_bv 64 0x10101000) val.
svt F_04c D_04c (Z_to_bv 64 k) ltac:(gr; apply negand3_val).
svt F_050 D_050 (Z_to_bv 64 0x101010000) ltac:(gr; apply bv_eq; vm_compute; reflexivity).
svt F_054 D_054 (Z_to_bv 64 (N - k)) val.
svt F_058 D_058 (Z_to_bv 64 s1) val.
svt F_05c D_05c (Z_to_bv 64 0x101010100) val.
svt F_060 D_060 (Z_to_bv 64 n1) ltac:(gr; rewrite andm4_val by lia; subst n1 r1; reflexivity).
svat step_mulhu_at F_064 D_064 c32w ltac:(gr; apply mulhu_val).
stepsw F_068 D_068 s1.
svt F_06c D_06c (Z_to_bv 64 e1) val.
stepsw F_070 D_070 (e1 - 4).
stepbt F_074 D_074.
apply mst_refl.
+ frame.
+ fin_apply ret_0f4.
* inv_tac.
* eapply covP_weaken.
-- repeat (apply covP_fill'; [lia|cbv; lia|lia|]). exact Hcov.
-- cbn beta. intros z Hz _. lia.
- eapply fin_steps.
+ norm_pc.
svat step_subw_at F_040 D_040 (v_subw (Z_to_bv 64 0) d) ltac:(gr; rwH; rewrite HD_, Z_to_bv_bv_unsigned; reflexivity).
svt F_044 D_044 (Z_to_bv 64 (C * 2^56)) ltac:(gr; rwH; apply slli56_val).
svt F_048 D_048 (Z_to_bv 64 0x10101000) val.
svt F_04c D_04c (Z_to_bv 64 k) ltac:(gr; apply negand3_val).
svt F_050 D_050 (Z_to_bv 64 0x101010000) ltac:(gr; apply bv_eq; vm_compute; reflexivity).
svt F_054 D_054 (Z_to_bv 64 (N - k)) val.
svt F_058 D_058 (Z_to_bv 64 s1) val.
svt F_05c D_05c (Z_to_bv 64 0x101010100) val.
svt F_060 D_060 (Z_to_bv 64 n1) ltac:(gr; rewrite andm4_val by lia; subst n1 r1; reflexivity).
svat step_mulhu_at F_064 D_064 c32w ltac:(gr; apply mulhu_val).
stepsw F_068 D_068 s1.
svt F_06c D_06c (Z_to_bv 64 e1) val.
stepsw F_070 D_070 (e1 - 4).
stepbf F_074 D_074.
apply mst_refl.
+ frame.
+ fin_apply (fun regs m => blk_078 regs m s1 n1 e1 j1).
* inv_tac.
* gr. reflexivity.
* gr. reflexivity.
* gr. reflexivity.
* gr. reflexivity.
* lia.
* lia.
* lia.
* lia.
* lia.
* eapply covP_weaken.
-- repeat (apply covP_fill'; [lia|cbv; lia|lia|]). exact Hcov.
-- cbn beta. intros z Hz HH. lia.
Qed.
Lemma entry_000 : forall regs,
getr regs 10 = Z_to_bv 64 D -> getr regs 11 = cw -> getr regs 12 = Z_to_bv 64 N ->
fin regs (Z_to_bv 64 (tfib_A_musl_memset + 0x0)) mem.
Proof.
intros regs H10 H11 H12. dfacts. pose proof inv_mem as Hinv.
assert (Hcov0 : covP mem (fun z => False)) by (intros x _ HF; destruct HF).
destruct (Z.eq_dec N 0) as [HN0|HN0].
{
eapply fin_steps.
+ norm_pc. stepbt F_000 D_000. apply mst_refl.
+ intros; reflexivity.
+ fin_apply ret_0f4; [exact Hinv|]. intros x Hx _. exfalso. lia. }
destruct (Z_lt_le_dec N 3) as [HN3|HN3].
{
eapply fin_steps.
+ norm_pc. stepbf F_000 D_000.
stepsb F_004 D_004 D.
svt F_008 D_008 (Z_to_bv 64 (D + N)) val.
svt F_00c D_00c (Z_to_bv 64 3) val.
stepsb F_010 D_010 (D + N - 1).
stepbt F_014 D_014. apply mst_refl.
+ frame.
+ fin_apply ret_0f4.
* inv_tac.
* eapply covP_weaken.
-- repeat (apply covP_fill'; [lia|cbv; lia|lia|]). exact Hcov0.
-- cbn beta. intros z Hz _. lia. }
destruct (Z_lt_le_dec N 7) as [HN7|HN7].
{
eapply fin_steps.
+ norm_pc. stepbf F_000 D_000.
stepsb F_004 D_004 D.
svt F_008 D_008 (Z_to_bv 64 (D + N)) val.
svt F_00c D_00c (Z_to_bv 64 3) val.
stepsb F_010 D_010 (D + N - 1).
stepbf F_014 D_014.
stepsb F_018 D_018 (D + 1).
stepsb F_01c D_01c (D + 2).
svt F_020 D_020 (Z_to_bv 64 7) val.
stepsb F_024 D_024 (D + N - 3).
stepsb F_028 D_028 (D + N - 2).
stepbt F_02c D_02c. apply mst_refl.
+ frame.
+ fin_apply ret_0f4.
* inv_tac.
* eapply covP_weaken.
-- repeat (apply covP_fill'; [lia|cbv; lia|lia|]). exact Hcov0.
-- cbn beta. intros z Hz _. lia. }
destruct (Z_lt_le_dec N 9) as [HN9|HN9].
{
eapply fin_steps.
+ norm_pc. stepbf F_000 D_000.
stepsb F_004 D_004 D.
svt F_008 D_008 (Z_to_bv 64 (D + N)) val.
svt F_00c D_00c (Z_to_bv 64 3) val.
stepsb F_010 D_010 (D + N - 1).
stepbf F_014 D_014.
stepsb F_018 D_018 (D + 1).
stepsb F_01c D_01c (D + 2).
svt F_020 D_020 (Z_to_bv 64 7) val.
stepsb F_024 D_024 (D + N - 3).
stepsb F_028 D_028 (D + N - 2).
stepbf F_02c D_02c.
stepsb F_030 D_030 (D + 3).
svt F_034 D_034 (Z_to_bv 64 9) val.
stepsb F_038 D_038 (D + N - 4).
stepbt F_03c D_03c. apply mst_refl.
+ frame.
+ fin_apply ret_0f4.
* inv_tac.
* eapply covP_weaken.
-- repeat (apply covP_fill'; [lia|cbv; lia|lia|]). exact Hcov0.
-- cbn beta. intros z Hz _. lia. }
eapply fin_steps.
+ norm_pc. stepbf F_000 D_000.
stepsb F_004 D_004 D.
svt F_008 D_008 (Z_to_bv 64 (D + N)) val.
svt F_00c D_00c (Z_to_bv 64 3) val.
stepsb F_010 D_010 (D + N - 1).
stepbf F_014 D_014.
stepsb F_018 D_018 (D + 1).
stepsb F_01c D_01c (D + 2).
svt F_020 D_020 (Z_to_bv 64 7) val.
stepsb F_024 D_024 (D + N - 3).
stepsb F_028 D_028 (D + N - 2).
stepbf F_02c D_02c.
stepsb F_030 D_030 (D + 3).
svt F_034 D_034 (Z_to_bv 64 9) val.
stepsb F_038 D_038 (D + N - 4).
stepbf F_03c D_03c. apply mst_refl.
+ frame.
+ fin_apply blk_040.
* inv_tac.
* gr. exact H10.
* gr. exact H11.
* gr. exact H12.
* gr. reflexivity.
* lia.
* eapply covP_weaken.
-- repeat (apply covP_fill'; [lia|cbv; lia|lia|]). exact Hcov0.
-- cbn beta. intros z Hz HH. lia.
Qed.
Lemma post_wbytes : forall m', post m' -> m' = wbytes mem d (repeat cb n).
Proof.
intros m' [Hin Hout]. dfacts. apply functional_extensionality. intros x.
rewrite wbytes_repeat_spec by lia. rewrite <- HD_, <- HN_.
destruct (_ && _) eqn:E.
- apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. apply Hin. lia.
- apply Hout. intros Hx. apply andb_false_iff in E. destruct E as [E|E]; [apply Z.leb_gt in E|apply Z.ltb_ge in E]; lia.
Qed.
End g.
Theorem tfib_memset :
forall (d c nw : word) (n : nat) (mem rom : word -> option byte) (regs : bvmap 5 word),
getr regs 10 = d -> getr regs 11 = c -> getr regs 12 = nw ->
bv_unsigned nw = Z.of_nat n ->
store_ok tfibsegs mem d n = true ->
bv_unsigned d + Z.of_nat n <= 2^64 ->
exists regs',
msteps tfibsegs (mkst regs (Z_to_bv 64 tfib_A_musl_memset) mem rom)
(mkst regs' (v_jalr (getr regs 1) 0)
(wbytes mem d (repeat (Z_to_bv 8 (bv_unsigned c mod 256)) n)) rom)
/\ getr regs' 10 = d
/\ (forall r : reg, r <> 11%bv -> r <> 12%bv -> r <> 13%bv -> r <> 14%bv -> r <> 15%bv ->
r <> 16%bv -> getr regs' r = getr regs r).
Proof.
intros d c nw n mem rom regs H10 H11 H12 Hn Hdst Hnd.
pose proof (u64_range nw) as Hnw.
assert (H10' : getr regs 10 = Z_to_bv 64 (D d)) by (rewrite H10; unfold D; rewrite Z_to_bv_bv_unsigned; reflexivity).
assert (H12' : getr regs 12 = Z_to_bv 64 (N n)) by (rewrite H12; unfold N; rewrite <- Hn, Z_to_bv_bv_unsigned; reflexivity).
destruct (entry_000 d c n mem rom Hdst Hnd ltac:(lia) regs H10' H11 H12') as (regs' & m' & Hms & Hpost & Hfr).
pose proof (post_wbytes d c n mem rom Hnd ltac:(lia) m' Hpost) as Em. subst m'.
exists regs'. split; [|split].
- change (Z_to_bv 64 tfib_A_musl_memset) with (Z_to_bv 64 (tfib_A_musl_memset + 0x0)). exact Hms.
- rewrite Hfr; [exact H10|]. unfold keep. repeat split; reg_neq_tac.
- intros. apply Hfr. unfold keep. repeat split; assumption.
Qed.
Corollary tfib_memset_pointwise :
forall (d c nw : word) (n : nat) (mem rom : word -> option byte) (regs : bvmap 5 word),
getr regs 10 = d -> getr regs 11 = c -> getr regs 12 = nw ->
bv_unsigned nw = Z.of_nat n ->
store_ok tfibsegs mem d n = true ->
bv_unsigned d + Z.of_nat n <= 2^64 ->
exists regs' mem',
msteps tfibsegs (mkst regs (Z_to_bv 64 tfib_A_musl_memset) mem rom)
(mkst regs' (v_jalr (getr regs 1) 0) mem' rom)
/\ (forall x : word, bv_unsigned d <= bv_unsigned x < bv_unsigned d + Z.of_nat n ->
mem' x = Some (Z_to_bv 8 (bv_unsigned c mod 256)))
/\ (forall x : word, ~ (bv_unsigned d <= bv_unsigned x < bv_unsigned d + Z.of_nat n) -> mem' x = mem x)
/\ getr regs' 10 = d
/\ (forall r : reg, r <> 11%bv -> r <> 12%bv -> r <> 13%bv -> r <> 14%bv -> r <> 15%bv ->
r <> 16%bv -> getr regs' r = getr regs r).
Proof.
intros d c nw n mem rom regs H10 H11 H12 Hn Hdst Hnd.
destruct (tfib_memset d c nw n mem rom regs H10 H11 H12 Hn Hdst Hnd) as (regs' & Hms & Ha0 & Hfr).
exists regs', (wbytes mem d (repeat (Z_to_bv 8 (bv_unsigned c mod 256)) n)).
split; [exact Hms|]. split; [|split; [|split; [exact Ha0|exact Hfr]]].
- intros x Hx. rewrite wbytes_repeat_spec by lia.
replace (_ && _) with true; [reflexivity|].
symmetry. apply andb_true_intro. split; [apply Z.leb_le|apply Z.ltb_lt]; lia.
- intros x Hx. rewrite wbytes_repeat_spec by lia.
destruct (_ && _) eqn:E; [|reflexivity].
exfalso. apply Hx. apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. lia.
Qed.
End f.
