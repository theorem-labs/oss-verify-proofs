(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN05.v, with its module paths changed. *)
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
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma fetch_lit : forall (p : word) (w : bv 32),
clookup src0tbl (bv_unsigned p) = Some (bv_unsigned w) ->
fetch_word src0segs p = Some w.
Proof.
intros p w H.
rewrite <- (Z_to_bv_bv_unsigned 64 p), <- (Z_to_bv_bv_unsigned 32 w).
apply src0tbl_ok. exact H.
Qed.
End a.
Ltac ftac := apply fetch_lit; vm_compute; reflexivity.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma FN_000 : fetch_word src0segs (Z_to_bv 64 (src0_A_enframe + 0x0)) = Some (0x02053703%bv : bv 32).
Proof. ftac. Qed.
Lemma DN_000 : decode_any (0x02053703%bv : bv 32) = Some (Load SZ8 true 14 10 32, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FN_004 : fetch_word src0segs (Z_to_bv 64 (src0_A_enframe + 0x4)) = Some (0x00c75793%bv : bv 32).
Proof. ftac. Qed.
Lemma DN_004 : decode_any (0x00c75793%bv : bv 32) = Some (ShiftImm ALU_SRL 15 14 12, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FN_008 : fetch_word src0segs (Z_to_bv 64 (src0_A_enframe + 0x8)) = Some (0x00078e63%bv : bv 32).
Proof. ftac. Qed.
Lemma DN_008 : decode_any (0x00078e63%bv : bv 32) = Some (Branch BC_EQ 15 0 28, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FN_00c : fetch_word src0segs (Z_to_bv 64 (src0_A_enframe + 0xc)) = Some (0x01f77793%bv : bv 32).
Proof. ftac. Qed.
Lemma DN_00c : decode_any (0x01f77793%bv : bv 32) = Some (OpImm ALU_AND 15 14 31, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FN_010 : fetch_word src0segs (Z_to_bv 64 (src0_A_enframe + 0x10)) = Some (0x00079a63%bv : bv 32).
Proof. ftac. Qed.
Lemma DN_010 : decode_any (0x00079a63%bv : bv 32) = Some (Branch BC_NE 15 0 20, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FN_014 : fetch_word src0segs (Z_to_bv 64 (src0_A_enframe + 0x14)) = Some (0xfffff7b7%bv : bv 32).
Proof. ftac. Qed.
Lemma DN_014 : decode_any (0xfffff7b7%bv : bv 32) = Some (Lui 15 1048575, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FN_018 : fetch_word src0segs (Z_to_bv 64 (src0_A_enframe + 0x18)) = Some (0x00f77733%bv : bv 32).
Proof. ftac. Qed.
Lemma DN_018 : decode_any (0x00f77733%bv : bv 32) = Some (Op ALU_AND 14 14 15, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FN_01c : fetch_word src0segs (Z_to_bv 64 (src0_A_enframe + 0x1c)) = Some (0xff070713%bv : bv 32).
Proof. ftac. Qed.
Lemma DN_01c : decode_any (0xff070713%bv : bv 32) = Some (OpImm ALU_ADD 14 14 4080, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FN_020 : fetch_word src0segs (Z_to_bv 64 (src0_A_enframe + 0x20)) = Some (0x0200006f%bv : bv 32).
Proof. ftac. Qed.
Lemma DN_020 : decode_any (0x0200006f%bv : bv 32) = Some (Jal 0 32, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FN_024 : fetch_word src0segs (Z_to_bv 64 (src0_A_enframe + 0x24)) = Some (0x00575713%bv : bv 32).
Proof. ftac. Qed.
Lemma DN_024 : decode_any (0x00575713%bv : bv 32) = Some (ShiftImm ALU_SRL 14 14 5, 4%Z).
Proof. vm_refl_bv. Qed.
Definition src0_enframe_w028 : Z := Eval vm_compute in tblw src0tbl (src0_A_enframe + 0x28).
Definition src0_enframe_i028 : Z := Eval vm_compute in instr_imm src0_enframe_w028.
Lemma FN_028 : fetch_word src0segs (Z_to_bv 64 (src0_A_enframe + 0x28)) = Some (Z_to_bv 32 src0_enframe_w028).
Proof. ftac. Qed.
Lemma DN_028 : decode_any (Z_to_bv 32 src0_enframe_w028) = Some (Auipc 15 (Z_to_bv 20 src0_enframe_i028), 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FN_02c : fetch_word src0segs (Z_to_bv 64 (src0_A_enframe + 0x2c)) = Some (0x07e77713%bv : bv 32).
Proof. ftac. Qed.
Lemma DN_02c : decode_any (0x07e77713%bv : bv 32) = Some (OpImm ALU_AND 14 14 126, 4%Z).
Proof. vm_refl_bv. Qed.
Definition src0_enframe_w030 : Z := Eval vm_compute in tblw src0tbl (src0_A_enframe + 0x30).
Definition src0_enframe_i030 : Z := Eval vm_compute in instr_imm src0_enframe_w030.
Lemma FN_030 : fetch_word src0segs (Z_to_bv 64 (src0_A_enframe + 0x30)) = Some (Z_to_bv 32 src0_enframe_w030).
Proof. ftac. Qed.
Lemma DN_030 : decode_any (Z_to_bv 32 src0_enframe_w030) = Some (OpImm ALU_ADD 15 15 (Z_to_bv 12 src0_enframe_i030), 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FN_034 : fetch_word src0segs (Z_to_bv 64 (src0_A_enframe + 0x34)) = Some (0x00e78733%bv : bv 32).
Proof. ftac. Qed.
Lemma DN_034 : decode_any (0x00e78733%bv : bv 32) = Some (Op ALU_ADD 14 15 14, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FN_038 : fetch_word src0segs (Z_to_bv 64 (src0_A_enframe + 0x38)) = Some (0x00075703%bv : bv 32).
Proof. ftac. Qed.
Lemma DN_038 : decode_any (0x00075703%bv : bv 32) = Some (Load SZ2 false 14 14 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FN_03c : fetch_word src0segs (Z_to_bv 64 (src0_A_enframe + 0x3c)) = Some (0x00471713%bv : bv 32).
Proof. ftac. Qed.
Lemma DN_03c : decode_any (0x00471713%bv : bv 32) = Some (ShiftImm ALU_SLL 14 14 4, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FN_040 : fetch_word src0segs (Z_to_bv 64 (src0_A_enframe + 0x40)) = Some (0x01053803%bv : bv 32).
Proof. ftac. Qed.
Lemma DN_040 : decode_any (0x01053803%bv : bv 32) = Some (Load SZ8 true 16 10 16, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FN_044 : fetch_word src0segs (Z_to_bv 64 (src0_A_enframe + 0x44)) = Some (0x02b707b3%bv : bv 32).
Proof. ftac. Qed.
Lemma DN_044 : decode_any (0x02b707b3%bv : bv 32) = Some (Mul M_MUL 15 14 11, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FN_048 : fetch_word src0segs (Z_to_bv 64 (src0_A_enframe + 0x48)) = Some (0x00f807b3%bv : bv 32).
Proof. ftac. Qed.
Lemma DN_048 : decode_any (0x00f807b3%bv : bv 32) = Some (Op ALU_ADD 15 16 15, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FN_04c : fetch_word src0segs (Z_to_bv 64 (src0_A_enframe + 0x4c)) = Some (0x00d7c883%bv : bv 32).
Proof. ftac. Qed.
Lemma DN_04c : decode_any (0x00d7c883%bv : bv 32) = Some (Load SZ1 false 17 15 13, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FN_050 : fetch_word src0segs (Z_to_bv 64 (src0_A_enframe + 0x50)) = Some (0x40c702b3%bv : bv 32).
Proof. ftac. Qed.
Lemma DN_050 : decode_any (0x40c702b3%bv : bv 32) = Some (Op ALU_SUB 5 14 12, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FN_054 : fetch_word src0segs (Z_to_bv 64 (src0_A_enframe + 0x54)) = Some (0xffc28293%bv : bv 32).
Proof. ftac. Qed.
Lemma DN_054 : decode_any (0xffc28293%bv : bv 32) = Some (OpImm ALU_ADD 5 5 4092, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FN_058 : fetch_word src0segs (Z_to_bv 64 (src0_A_enframe + 0x58)) = Some (0x01078793%bv : bv 32).
Proof. ftac. Qed.
Lemma DN_058 : decode_any (0x01078793%bv : bv 32) = Some (OpImm ALU_ADD 15 15 16, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FN_05c : fetch_word src0segs (Z_to_bv 64 (src0_A_enframe + 0x5c)) = Some (0x00088663%bv : bv 32).
Proof. ftac. Qed.
Lemma DN_05c : decode_any (0x00088663%bv : bv 32) = Some (Branch BC_EQ 17 0 12, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FN_060 : fetch_word src0segs (Z_to_bv 64 (src0_A_enframe + 0x60)) = Some (0xffe7d683%bv : bv 32).
Proof. ftac. Qed.
Lemma DN_060 : decode_any (0xffe7d683%bv : bv 32) = Some (Load SZ2 false 13 15 4094, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FN_064 : fetch_word src0segs (Z_to_bv 64 (src0_A_enframe + 0x64)) = Some (0x00168693%bv : bv 32).
Proof. ftac. Qed.
Lemma DN_064 : decode_any (0x00168693%bv : bv 32) = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FN_068 : fetch_word src0segs (Z_to_bv 64 (src0_A_enframe + 0x68)) = Some (0xffc7c383%bv : bv 32).
Proof. ftac. Qed.
Lemma DN_068 : decode_any (0xffc7c383%bv : bv 32) = Some (Load SZ1 false 7 15 4092, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FN_06c : fetch_word src0segs (Z_to_bv 64 (src0_A_enframe + 0x6c)) = Some (0x0042d313%bv : bv 32).
Proof. ftac. Qed.
Lemma DN_06c : decode_any (0x0042d313%bv : bv 32) = Some (ShiftImm ALU_SRL 6 5 4, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FN_070 : fetch_word src0segs (Z_to_bv 64 (src0_A_enframe + 0x70)) = Some (0x0ff6f893%bv : bv 32).
Proof. ftac. Qed.
Lemma DN_070 : decode_any (0x0ff6f893%bv : bv 32) = Some (OpImm ALU_AND 17 13 255, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FN_074 : fetch_word src0segs (Z_to_bv 64 (src0_A_enframe + 0x74)) = Some (0x00038463%bv : bv 32).
Proof. ftac. Qed.
Lemma DN_074 : decode_any (0x00038463%bv : bv 32) = Some (Branch BC_EQ 7 0 8, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FN_078 : fetch_word src0segs (Z_to_bv 64 (src0_A_enframe + 0x78)) = Some (0x00000023%bv : bv 32).
Proof. ftac. Qed.
Lemma DN_078 : decode_any (0x00000023%bv : bv 32) = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FN_07c : fetch_word src0segs (Z_to_bv 64 (src0_A_enframe + 0x7c)) = Some (0x03137e63%bv : bv 32).
Proof. ftac. Qed.
Lemma DN_07c : decode_any (0x03137e63%bv : bv 32) = Some (Branch BC_GEU 6 17 60, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FN_080 : fetch_word src0segs (Z_to_bv 64 (src0_A_enframe + 0x80)) = Some (0x0052d693%bv : bv 32).
Proof. ftac. Qed.
Lemma DN_080 : decode_any (0x0052d693%bv : bv 32) = Some (ShiftImm ALU_SRL 13 5 5, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FN_084 : fetch_word src0segs (Z_to_bv 64 (src0_A_enframe + 0x84)) = Some (0x00d366b3%bv : bv 32).
Proof. ftac. Qed.
Lemma DN_084 : decode_any (0x00d366b3%bv : bv 32) = Some (Op ALU_OR 13 6 13, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FN_088 : fetch_word src0segs (Z_to_bv 64 (src0_A_enframe + 0x88)) = Some (0x0026d293%bv : bv 32).
Proof. ftac. Qed.
Lemma DN_088 : decode_any (0x0026d293%bv : bv 32) = Some (ShiftImm ALU_SRL 5 13 2, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FN_08c : fetch_word src0segs (Z_to_bv 64 (src0_A_enframe + 0x8c)) = Some (0x00d2e6b3%bv : bv 32).
Proof. ftac. Qed.
Lemma DN_08c : decode_any (0x00d2e6b3%bv : bv 32) = Some (Op ALU_OR 13 5 13, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FN_090 : fetch_word src0segs (Z_to_bv 64 (src0_A_enframe + 0x90)) = Some (0x0046d293%bv : bv 32).
Proof. ftac. Qed.
Lemma DN_090 : decode_any (0x0046d293%bv : bv 32) = Some (ShiftImm ALU_SRL 5 13 4, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FN_094 : fetch_word src0segs (Z_to_bv 64 (src0_A_enframe + 0x94)) = Some (0x00d2e6b3%bv : bv 32).
Proof. ftac. Qed.
Lemma DN_094 : decode_any (0x00d2e6b3%bv : bv 32) = Some (Op ALU_OR 13 5 13, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FN_098 : fetch_word src0segs (Z_to_bv 64 (src0_A_enframe + 0x98)) = Some (0x00d8f6b3%bv : bv 32).
Proof. ftac. Qed.
Lemma DN_098 : decode_any (0x00d8f6b3%bv : bv 32) = Some (Op ALU_AND 13 17 13, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FN_09c : fetch_word src0segs (Z_to_bv 64 (src0_A_enframe + 0x9c)) = Some (0x00d338b3%bv : bv 32).
Proof. ftac. Qed.
Lemma DN_09c : decode_any (0x00d338b3%bv : bv 32) = Some (Op ALU_SLTU 17 6 13, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FN_0a0 : fetch_word src0segs (Z_to_bv 64 (src0_A_enframe + 0xa0)) = Some (0xfff34293%bv : bv 32).
Proof. ftac. Qed.
Lemma DN_0a0 : decode_any (0xfff34293%bv : bv 32) = Some (OpImm ALU_XOR 5 6 4095, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FN_0a4 : fetch_word src0segs (Z_to_bv 64 (src0_A_enframe + 0xa4)) = Some (0x411008bb%bv : bv 32).
Proof. ftac. Qed.
Lemma DN_0a4 : decode_any (0x411008bb%bv : bv 32) = Some (Op32 ALU_SUB 17 0 17, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FN_0a8 : fetch_word src0segs (Z_to_bv 64 (src0_A_enframe + 0xa8)) = Some (0x0058f8b3%bv : bv 32).
Proof. ftac. Qed.
Lemma DN_0a8 : decode_any (0x0058f8b3%bv : bv 32) = Some (Op ALU_AND 17 17 5, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FN_0ac : fetch_word src0segs (Z_to_bv 64 (src0_A_enframe + 0xac)) = Some (0x00d888bb%bv : bv 32).
Proof. ftac. Qed.
Lemma DN_0ac : decode_any (0x00d888bb%bv : bv 32) = Some (Op32 ALU_ADD 17 17 13, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FN_0b0 : fetch_word src0segs (Z_to_bv 64 (src0_A_enframe + 0xb0)) = Some (0x01137463%bv : bv 32).
Proof. ftac. Qed.
Lemma DN_0b0 : decode_any (0x01137463%bv : bv 32) = Some (Branch BC_GEU 6 17 8, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FN_0b4 : fetch_word src0segs (Z_to_bv 64 (src0_A_enframe + 0xb4)) = Some (0x00000023%bv : bv 32).
Proof. ftac. Qed.
Lemma DN_0b4 : decode_any (0x00000023%bv : bv 32) = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FN_0b8 : fetch_word src0segs (Z_to_bv 64 (src0_A_enframe + 0xb8)) = Some (0x00078693%bv : bv 32).
Proof. ftac. Qed.
Lemma DN_0b8 : decode_any (0x00078693%bv : bv 32) = Some (OpImm ALU_ADD 13 15 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FN_0bc : fetch_word src0segs (Z_to_bv 64 (src0_A_enframe + 0xbc)) = Some (0x02088063%bv : bv 32).
Proof. ftac. Qed.
Lemma DN_0bc : decode_any (0x02088063%bv : bv 32) = Some (Branch BC_EQ 17 0 32, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FN_0c0 : fetch_word src0segs (Z_to_bv 64 (src0_A_enframe + 0xc0)) = Some (0xfe000813%bv : bv 32).
Proof. ftac. Qed.
Lemma DN_0c0 : decode_any (0xfe000813%bv : bv 32) = Some (OpImm ALU_ADD 16 0 4064, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FN_0c4 : fetch_word src0segs (Z_to_bv 64 (src0_A_enframe + 0xc4)) = Some (0x0048969b%bv : bv 32).
Proof. ftac. Qed.
Lemma DN_0c4 : decode_any (0x0048969b%bv : bv 32) = Some (ShiftImm32 ALU_SLL 13 17 4, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FN_0c8 : fetch_word src0segs (Z_to_bv 64 (src0_A_enframe + 0xc8)) = Some (0x00d786b3%bv : bv 32).
Proof. ftac. Qed.
Lemma DN_0c8 : decode_any (0x00d786b3%bv : bv 32) = Some (Op ALU_ADD 13 15 13, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FN_0cc : fetch_word src0segs (Z_to_bv 64 (src0_A_enframe + 0xcc)) = Some (0xff078ea3%bv : bv 32).
Proof. ftac. Qed.
Lemma DN_0cc : decode_any (0xff078ea3%bv : bv 32) = Some (Store SZ1 15 16 4093, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FN_0d0 : fetch_word src0segs (Z_to_bv 64 (src0_A_enframe + 0xd0)) = Some (0xff179f23%bv : bv 32).
Proof. ftac. Qed.
Lemma DN_0d0 : decode_any (0xff179f23%bv : bv 32) = Some (Store SZ2 15 17 4094, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FN_0d4 : fetch_word src0segs (Z_to_bv 64 (src0_A_enframe + 0xd4)) = Some (0xfe068e23%bv : bv 32).
Proof. ftac. Qed.
Lemma DN_0d4 : decode_any (0xfe068e23%bv : bv 32) = Some (Store SZ1 13 0 4092, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FN_0d8 : fetch_word src0segs (Z_to_bv 64 (src0_A_enframe + 0xd8)) = Some (0x01053803%bv : bv 32).
Proof. ftac. Qed.
Lemma DN_0d8 : decode_any (0x01053803%bv : bv 32) = Some (Load SZ8 true 16 10 16, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FN_0dc : fetch_word src0segs (Z_to_bv 64 (src0_A_enframe + 0xdc)) = Some (0x00e78733%bv : bv 32).
Proof. ftac. Qed.
Lemma DN_0dc : decode_any (0x00e78733%bv : bv 32) = Some (Op ALU_ADD 14 15 14, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FN_0e0 : fetch_word src0segs (Z_to_bv 64 (src0_A_enframe + 0xe0)) = Some (0x410687bb%bv : bv 32).
Proof. ftac. Qed.
Lemma DN_0e0 : decode_any (0x410687bb%bv : bv 32) = Some (Op32 ALU_SUB 15 13 16, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FN_0e4 : fetch_word src0segs (Z_to_bv 64 (src0_A_enframe + 0xe4)) = Some (0x00d60633%bv : bv 32).
Proof. ftac. Qed.
Lemma DN_0e4 : decode_any (0x00d60633%bv : bv 32) = Some (Op ALU_ADD 12 12 13, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FN_0e8 : fetch_word src0segs (Z_to_bv 64 (src0_A_enframe + 0xe8)) = Some (0xffc70513%bv : bv 32).
Proof. ftac. Qed.
Lemma DN_0e8 : decode_any (0xffc70513%bv : bv 32) = Some (OpImm ALU_ADD 10 14 4092, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FN_0ec : fetch_word src0segs (Z_to_bv 64 (src0_A_enframe + 0xec)) = Some (0xff078793%bv : bv 32).
Proof. ftac. Qed.
Lemma DN_0ec : decode_any (0xff078793%bv : bv 32) = Some (OpImm ALU_ADD 15 15 4080, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FN_0f0 : fetch_word src0segs (Z_to_bv 64 (src0_A_enframe + 0xf0)) = Some (0x0047d793%bv : bv 32).
Proof. ftac. Qed.
Lemma DN_0f0 : decode_any (0x0047d793%bv : bv 32) = Some (ShiftImm ALU_SRL 15 15 4, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FN_0f4 : fetch_word src0segs (Z_to_bv 64 (src0_A_enframe + 0xf4)) = Some (0x40c5083b%bv : bv 32).
Proof. ftac. Qed.
Lemma DN_0f4 : decode_any (0x40c5083b%bv : bv 32) = Some (Op32 ALU_SUB 16 10 12, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FN_0f8 : fetch_word src0segs (Z_to_bv 64 (src0_A_enframe + 0xf8)) = Some (0xfeb68ea3%bv : bv 32).
Proof. ftac. Qed.
Lemma DN_0f8 : decode_any (0xfeb68ea3%bv : bv 32) = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FN_0fc : fetch_word src0segs (Z_to_bv 64 (src0_A_enframe + 0xfc)) = Some (0xfef69f23%bv : bv 32).
Proof. ftac. Qed.
Lemma DN_0fc : decode_any (0xfef69f23%bv : bv 32) = Some (Store SZ2 13 15 4094, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FN_100 : fetch_word src0segs (Z_to_bv 64 (src0_A_enframe + 0x100)) = Some (0x02080463%bv : bv 32).
Proof. ftac. Qed.
Lemma DN_100 : decode_any (0x02080463%bv : bv 32) = Some (Branch BC_EQ 16 0 40, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FN_104 : fetch_word src0segs (Z_to_bv 64 (src0_A_enframe + 0x104)) = Some (0x40c505bb%bv : bv 32).
Proof. ftac. Qed.
Lemma DN_104 : decode_any (0x40c505bb%bv : bv 32) = Some (Op32 ALU_SUB 11 10 12, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FN_108 : fetch_word src0segs (Z_to_bv 64 (src0_A_enframe + 0x108)) = Some (0x40b0063b%bv : bv 32).
Proof. ftac. Qed.
Lemma DN_108 : decode_any (0x40b0063b%bv : bv 32) = Some (Op32 ALU_SUB 12 0 11, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FN_10c : fetch_word src0segs (Z_to_bv 64 (src0_A_enframe + 0x10c)) = Some (0x00c50633%bv : bv 32).
Proof. ftac. Qed.
Lemma DN_10c : decode_any (0x00c50633%bv : bv 32) = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FN_110 : fetch_word src0segs (Z_to_bv 64 (src0_A_enframe + 0x110)) = Some (0x00500513%bv : bv 32).
Proof. ftac. Qed.
Lemma DN_110 : decode_any (0x00500513%bv : bv 32) = Some (OpImm ALU_ADD 10 0 5, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FN_114 : fetch_word src0segs (Z_to_bv 64 (src0_A_enframe + 0x114)) = Some (0x00060023%bv : bv 32).
Proof. ftac. Qed.
Lemma DN_114 : decode_any (0x00060023%bv : bv 32) = Some (Store SZ1 12 0 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FN_118 : fetch_word src0segs (Z_to_bv 64 (src0_A_enframe + 0x118)) = Some (0x00a5cc63%bv : bv 32).
Proof. ftac. Qed.
Lemma DN_118 : decode_any (0x00a5cc63%bv : bv 32) = Some (Branch BC_LT 11 10 24, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FN_11c : fetch_word src0segs (Z_to_bv 64 (src0_A_enframe + 0x11c)) = Some (0xfe070ba3%bv : bv 32).
Proof. ftac. Qed.
Lemma DN_11c : decode_any (0xfe070ba3%bv : bv 32) = Some (Store SZ1 14 0 4087, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FN_120 : fetch_word src0segs (Z_to_bv 64 (src0_A_enframe + 0x120)) = Some (0xfeb72c23%bv : bv 32).
Proof. ftac. Qed.
Lemma DN_120 : decode_any (0xfeb72c23%bv : bv 32) = Some (Store SZ4 14 11 4088, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FN_124 : fetch_word src0segs (Z_to_bv 64 (src0_A_enframe + 0x124)) = Some (0x0100006f%bv : bv 32).
Proof. ftac. Qed.
Lemma DN_124 : decode_any (0x0100006f%bv : bv 32) = Some (Jal 0 16, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FN_128 : fetch_word src0segs (Z_to_bv 64 (src0_A_enframe + 0x128)) = Some (0x00000513%bv : bv 32).
Proof. ftac. Qed.
Lemma DN_128 : decode_any (0x00000513%bv : bv 32) = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FN_12c : fetch_word src0segs (Z_to_bv 64 (src0_A_enframe + 0x12c)) = Some (0x0080006f%bv : bv 32).
Proof. ftac. Qed.
Lemma DN_12c : decode_any (0x0080006f%bv : bv 32) = Some (Jal 0 8, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FN_130 : fetch_word src0segs (Z_to_bv 64 (src0_A_enframe + 0x130)) = Some (0x00058513%bv : bv 32).
Proof. ftac. Qed.
Lemma DN_130 : decode_any (0x00058513%bv : bv 32) = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FN_134 : fetch_word src0segs (Z_to_bv 64 (src0_A_enframe + 0x134)) = Some (0xffd6c583%bv : bv 32).
Proof. ftac. Qed.
Lemma DN_134 : decode_any (0xffd6c583%bv : bv 32) = Some (Load SZ1 false 11 13 4093, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FN_138 : fetch_word src0segs (Z_to_bv 64 (src0_A_enframe + 0x138)) = Some (0x01f5f593%bv : bv 32).
Proof. ftac. Qed.
Lemma DN_138 : decode_any (0x01f5f593%bv : bv 32) = Some (OpImm ALU_AND 11 11 31, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FN_13c : fetch_word src0segs (Z_to_bv 64 (src0_A_enframe + 0x13c)) = Some (0x00551513%bv : bv 32).
Proof. ftac. Qed.
Lemma DN_13c : decode_any (0x00551513%bv : bv 32) = Some (ShiftImm ALU_SLL 10 10 5, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FN_140 : fetch_word src0segs (Z_to_bv 64 (src0_A_enframe + 0x140)) = Some (0x00b56533%bv : bv 32).
Proof. ftac. Qed.
Lemma DN_140 : decode_any (0x00b56533%bv : bv 32) = Some (Op ALU_OR 10 10 11, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FN_144 : fetch_word src0segs (Z_to_bv 64 (src0_A_enframe + 0x144)) = Some (0xfea68ea3%bv : bv 32).
Proof. ftac. Qed.
Lemma DN_144 : decode_any (0xfea68ea3%bv : bv 32) = Some (Store SZ1 13 10 4093, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FN_148 : fetch_word src0segs (Z_to_bv 64 (src0_A_enframe + 0x148)) = Some (0x00068513%bv : bv 32).
Proof. ftac. Qed.
Lemma DN_148 : decode_any (0x00068513%bv : bv 32) = Some (OpImm ALU_ADD 10 13 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma FN_14c : fetch_word src0segs (Z_to_bv 64 (src0_A_enframe + 0x14c)) = Some (0x00008067%bv : bv 32).
Proof. ftac. Qed.
Lemma DN_14c : decode_any (0x00008067%bv : bv 32) = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl_bv. Qed.
End b.
