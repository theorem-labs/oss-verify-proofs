(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_12fff0 : bv 32 := 0x0e060a63.
Lemma F_12fff0 : fetch_word AsanUbsan.M.loaded_segments (0x130034 : word) = Some W_12fff0.
Proof. vm_refl. Qed.
Lemma D_12fff0 : decode_any W_12fff0 = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12fff4 : bv 32 := 0x00b50023.
Lemma F_12fff4 : fetch_word AsanUbsan.M.loaded_segments (0x130038 : word) = Some W_12fff4.
Proof. vm_refl. Qed.
Lemma D_12fff4 : decode_any W_12fff4 = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12fff8 : bv 32 := 0x00c506b3.
Lemma F_12fff8 : fetch_word AsanUbsan.M.loaded_segments (0x13003c : word) = Some W_12fff8.
Proof. vm_refl. Qed.
Lemma D_12fff8 : decode_any W_12fff8 = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12fffc : bv 32 := 0x00300713.
Lemma F_12fffc : fetch_word AsanUbsan.M.loaded_segments (0x130040 : word) = Some W_12fffc.
Proof. vm_refl. Qed.
Lemma D_12fffc : decode_any W_12fffc = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_130000 : bv 32 := 0xfeb68fa3.
Lemma F_130000 : fetch_word AsanUbsan.M.loaded_segments (0x130044 : word) = Some W_130000.
Proof. vm_refl. Qed.
Lemma D_130000 : decode_any W_130000 = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_130004 : bv 32 := 0x0ee66063.
Lemma F_130004 : fetch_word AsanUbsan.M.loaded_segments (0x130048 : word) = Some W_130004.
Proof. vm_refl. Qed.
Lemma D_130004 : decode_any W_130004 = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_130008 : bv 32 := 0x00b500a3.
Lemma F_130008 : fetch_word AsanUbsan.M.loaded_segments (0x13004c : word) = Some W_130008.
Proof. vm_refl. Qed.
Lemma D_130008 : decode_any W_130008 = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13000c : bv 32 := 0x00b50123.
Lemma F_13000c : fetch_word AsanUbsan.M.loaded_segments (0x130050 : word) = Some W_13000c.
Proof. vm_refl. Qed.
Lemma D_13000c : decode_any W_13000c = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_130010 : bv 32 := 0x00700713.
Lemma F_130010 : fetch_word AsanUbsan.M.loaded_segments (0x130054 : word) = Some W_130010.
Proof. vm_refl. Qed.
Lemma D_130010 : decode_any W_130010 = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_130014 : bv 32 := 0xfeb68ea3.
Lemma F_130014 : fetch_word AsanUbsan.M.loaded_segments (0x130058 : word) = Some W_130014.
Proof. vm_refl. Qed.
Lemma D_130014 : decode_any W_130014 = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_130018 : bv 32 := 0xfeb68f23.
Lemma F_130018 : fetch_word AsanUbsan.M.loaded_segments (0x13005c : word) = Some W_130018.
Proof. vm_refl. Qed.
Lemma D_130018 : decode_any W_130018 = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13001c : bv 32 := 0x0ce66463.
Lemma F_13001c : fetch_word AsanUbsan.M.loaded_segments (0x130060 : word) = Some W_13001c.
Proof. vm_refl. Qed.
Lemma D_13001c : decode_any W_13001c = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_130020 : bv 32 := 0x00b501a3.
Lemma F_130020 : fetch_word AsanUbsan.M.loaded_segments (0x130064 : word) = Some W_130020.
Proof. vm_refl. Qed.
Lemma D_130020 : decode_any W_130020 = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_130024 : bv 32 := 0x00900793.
Lemma F_130024 : fetch_word AsanUbsan.M.loaded_segments (0x130068 : word) = Some W_130024.
Proof. vm_refl. Qed.
Lemma D_130024 : decode_any W_130024 = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_130028 : bv 32 := 0xfeb68e23.
Lemma F_130028 : fetch_word AsanUbsan.M.loaded_segments (0x13006c : word) = Some W_130028.
Proof. vm_refl. Qed.
Lemma D_130028 : decode_any W_130028 = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13002c : bv 32 := 0x0af66c63.
Lemma F_13002c : fetch_word AsanUbsan.M.loaded_segments (0x130070 : word) = Some W_13002c.
Proof. vm_refl. Qed.
Lemma D_13002c : decode_any W_13002c = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_130030 : bv 32 := 0x40a006bb.
Lemma F_130030 : fetch_word AsanUbsan.M.loaded_segments (0x130074 : word) = Some W_130030.
Proof. vm_refl. Qed.
Lemma D_130030 : decode_any W_130030 = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_130034 : bv 32 := 0x03859813.
Lemma F_130034 : fetch_word AsanUbsan.M.loaded_segments (0x130078 : word) = Some W_130034.
Proof. vm_refl. Qed.
Lemma D_130034 : decode_any W_130034 = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_130038 : bv 32 := 0x101015b7.
Lemma F_130038 : fetch_word AsanUbsan.M.loaded_segments (0x13007c : word) = Some W_130038.
Proof. vm_refl. Qed.
Lemma D_130038 : decode_any W_130038 = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13003c : bv 32 := 0x0036f693.
Lemma F_13003c : fetch_word AsanUbsan.M.loaded_segments (0x130080 : word) = Some W_13003c.
Proof. vm_refl. Qed.
Lemma D_13003c : decode_any W_13003c = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_130040 : bv 32 := 0x00459713.
Lemma F_130040 : fetch_word AsanUbsan.M.loaded_segments (0x130084 : word) = Some W_130040.
Proof. vm_refl. Qed.
Lemma D_130040 : decode_any W_130040 = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_130044 : bv 32 := 0x40d60633.
Lemma F_130044 : fetch_word AsanUbsan.M.loaded_segments (0x130088 : word) = Some W_130044.
Proof. vm_refl. Qed.
Lemma D_130044 : decode_any W_130044 = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_130048 : bv 32 := 0x00d505b3.
Lemma F_130048 : fetch_word AsanUbsan.M.loaded_segments (0x13008c : word) = Some W_130048.
Proof. vm_refl. Qed.
Lemma D_130048 : decode_any W_130048 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13004c : bv 32 := 0x10070693.
Lemma F_13004c : fetch_word AsanUbsan.M.loaded_segments (0x130090 : word) = Some W_13004c.
Proof. vm_refl. Qed.
Lemma D_13004c : decode_any W_13004c = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_130050 : bv 32 := 0xffc67713.
Lemma F_130050 : fetch_word AsanUbsan.M.loaded_segments (0x130094 : word) = Some W_130050.
Proof. vm_refl. Qed.
Lemma D_130050 : decode_any W_130050 = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_130054 : bv 32 := 0x02d83633.
Lemma F_130054 : fetch_word AsanUbsan.M.loaded_segments (0x130098 : word) = Some W_130054.
Proof. vm_refl. Qed.
Lemma D_130054 : decode_any W_130054 = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_130058 : bv 32 := 0x00c5a023.
Lemma F_130058 : fetch_word AsanUbsan.M.loaded_segments (0x13009c : word) = Some W_130058.
Proof. vm_refl. Qed.
Lemma D_130058 : decode_any W_130058 = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13005c : bv 32 := 0x00e586b3.
Lemma F_13005c : fetch_word AsanUbsan.M.loaded_segments (0x1300a0 : word) = Some W_13005c.
Proof. vm_refl. Qed.
Lemma D_13005c : decode_any W_13005c = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_130060 : bv 32 := 0xfec6ae23.
Lemma F_130060 : fetch_word AsanUbsan.M.loaded_segments (0x1300a4 : word) = Some W_130060.
Proof. vm_refl. Qed.
Lemma D_130060 : decode_any W_130060 = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_130064 : bv 32 := 0x08f76063.
Lemma F_130064 : fetch_word AsanUbsan.M.loaded_segments (0x1300a8 : word) = Some W_130064.
Proof. vm_refl. Qed.
Lemma D_130064 : decode_any W_130064 = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_130068 : bv 32 := 0x00c5a223.
Lemma F_130068 : fetch_word AsanUbsan.M.loaded_segments (0x1300ac : word) = Some W_130068.
Proof. vm_refl. Qed.
Lemma D_130068 : decode_any W_130068 = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13006c : bv 32 := 0x00c5a423.
Lemma F_13006c : fetch_word AsanUbsan.M.loaded_segments (0x1300b0 : word) = Some W_13006c.
Proof. vm_refl. Qed.
Lemma D_13006c : decode_any W_13006c = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_130070 : bv 32 := 0x01900793.
Lemma F_130070 : fetch_word AsanUbsan.M.loaded_segments (0x1300b4 : word) = Some W_130070.
Proof. vm_refl. Qed.
Lemma D_130070 : decode_any W_130070 = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_130074 : bv 32 := 0xfec6aa23.
Lemma F_130074 : fetch_word AsanUbsan.M.loaded_segments (0x1300b8 : word) = Some W_130074.
Proof. vm_refl. Qed.
Lemma D_130074 : decode_any W_130074 = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_130078 : bv 32 := 0xfec6ac23.
Lemma F_130078 : fetch_word AsanUbsan.M.loaded_segments (0x1300bc : word) = Some W_130078.
Proof. vm_refl. Qed.
Lemma D_130078 : decode_any W_130078 = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13007c : bv 32 := 0x06f76463.
Lemma F_13007c : fetch_word AsanUbsan.M.loaded_segments (0x1300c0 : word) = Some W_13007c.
Proof. vm_refl. Qed.
Lemma D_13007c : decode_any W_13007c = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_130080 : bv 32 := 0x00c5a623.
Lemma F_130080 : fetch_word AsanUbsan.M.loaded_segments (0x1300c4 : word) = Some W_130080.
Proof. vm_refl. Qed.
Lemma D_130080 : decode_any W_130080 = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_130084 : bv 32 := 0x00c5a823.
Lemma F_130084 : fetch_word AsanUbsan.M.loaded_segments (0x1300c8 : word) = Some W_130084.
Proof. vm_refl. Qed.
Lemma D_130084 : decode_any W_130084 = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_130088 : bv 32 := 0x00c5aa23.
Lemma F_130088 : fetch_word AsanUbsan.M.loaded_segments (0x1300cc : word) = Some W_130088.
Proof. vm_refl. Qed.
Lemma D_130088 : decode_any W_130088 = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13008c : bv 32 := 0x00c5ac23.
Lemma F_13008c : fetch_word AsanUbsan.M.loaded_segments (0x1300d0 : word) = Some W_13008c.
Proof. vm_refl. Qed.
Lemma D_13008c : decode_any W_13008c = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_130090 : bv 32 := 0x0045f793.
Lemma F_130090 : fetch_word AsanUbsan.M.loaded_segments (0x1300d4 : word) = Some W_130090.
Proof. vm_refl. Qed.
Lemma D_130090 : decode_any W_130090 = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_130094 : bv 32 := 0x02000813.
Lemma F_130094 : fetch_word AsanUbsan.M.loaded_segments (0x1300d8 : word) = Some W_130094.
Proof. vm_refl. Qed.
Lemma D_130094 : decode_any W_130094 = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_130098 : bv 32 := 0x01878793.
Lemma F_130098 : fetch_word AsanUbsan.M.loaded_segments (0x1300dc : word) = Some W_130098.
Proof. vm_refl. Qed.
Lemma D_130098 : decode_any W_130098 = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13009c : bv 32 := 0x40f70733.
Lemma F_13009c : fetch_word AsanUbsan.M.loaded_segments (0x1300e0 : word) = Some W_13009c.
Proof. vm_refl. Qed.
Lemma D_13009c : decode_any W_13009c = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1300a0 : bv 32 := 0xfec6a223.
Lemma F_1300a0 : fetch_word AsanUbsan.M.loaded_segments (0x1300e4 : word) = Some W_1300a0.
Proof. vm_refl. Qed.
Lemma D_1300a0 : decode_any W_1300a0 = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1300a4 : bv 32 := 0xfec6a423.
Lemma F_1300a4 : fetch_word AsanUbsan.M.loaded_segments (0x1300e8 : word) = Some W_1300a4.
Proof. vm_refl. Qed.
Lemma D_1300a4 : decode_any W_1300a4 = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1300a8 : bv 32 := 0xfec6a623.
Lemma F_1300a8 : fetch_word AsanUbsan.M.loaded_segments (0x1300ec : word) = Some W_1300a8.
Proof. vm_refl. Qed.
Lemma D_1300a8 : decode_any W_1300a8 = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1300ac : bv 32 := 0xfec6a823.
Lemma F_1300ac : fetch_word AsanUbsan.M.loaded_segments (0x1300f0 : word) = Some W_1300ac.
Proof. vm_refl. Qed.
Lemma D_1300ac : decode_any W_1300ac = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1300b0 : bv 32 := 0x03076a63.
Lemma F_1300b0 : fetch_word AsanUbsan.M.loaded_segments (0x1300f4 : word) = Some W_1300b0.
Proof. vm_refl. Qed.
Lemma D_1300b0 : decode_any W_1300b0 = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1300b4 : bv 32 := 0x02061613.
Lemma F_1300b4 : fetch_word AsanUbsan.M.loaded_segments (0x1300f8 : word) = Some W_1300b4.
Proof. vm_refl. Qed.
Lemma D_1300b4 : decode_any W_1300b4 = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1300b8 : bv 32 := 0x00f585b3.
Lemma F_1300b8 : fetch_word AsanUbsan.M.loaded_segments (0x1300fc : word) = Some W_1300b8.
Proof. vm_refl. Qed.
Lemma D_1300b8 : decode_any W_1300b8 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1300bc : bv 32 := 0x02065693.
Lemma F_1300bc : fetch_word AsanUbsan.M.loaded_segments (0x130100 : word) = Some W_1300bc.
Proof. vm_refl. Qed.
Lemma D_1300bc : decode_any W_1300bc = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1300c0 : bv 32 := 0x00d66633.
Lemma F_1300c0 : fetch_word AsanUbsan.M.loaded_segments (0x130104 : word) = Some W_1300c0.
Proof. vm_refl. Qed.
Lemma D_1300c0 : decode_any W_1300c0 = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1300c4 : bv 32 := 0x01f00693.
Lemma F_1300c4 : fetch_word AsanUbsan.M.loaded_segments (0x130108 : word) = Some W_1300c4.
Proof. vm_refl. Qed.
Lemma D_1300c4 : decode_any W_1300c4 = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1300c8 : bv 32 := 0x00c5b023.
Lemma F_1300c8 : fetch_word AsanUbsan.M.loaded_segments (0x13010c : word) = Some W_1300c8.
Proof. vm_refl. Qed.
Lemma D_1300c8 : decode_any W_1300c8 = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1300cc : bv 32 := 0x00c5b423.
Lemma F_1300cc : fetch_word AsanUbsan.M.loaded_segments (0x130110 : word) = Some W_1300cc.
Proof. vm_refl. Qed.
Lemma D_1300cc : decode_any W_1300cc = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1300d0 : bv 32 := 0x00c5b823.
Lemma F_1300d0 : fetch_word AsanUbsan.M.loaded_segments (0x130114 : word) = Some W_1300d0.
Proof. vm_refl. Qed.
Lemma D_1300d0 : decode_any W_1300d0 = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1300d4 : bv 32 := 0x00c5bc23.
Lemma F_1300d4 : fetch_word AsanUbsan.M.loaded_segments (0x130118 : word) = Some W_1300d4.
Proof. vm_refl. Qed.
Lemma D_1300d4 : decode_any W_1300d4 = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1300d8 : bv 32 := 0xfe070713.
Lemma F_1300d8 : fetch_word AsanUbsan.M.loaded_segments (0x13011c : word) = Some W_1300d8.
Proof. vm_refl. Qed.
Lemma D_1300d8 : decode_any W_1300d8 = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1300dc : bv 32 := 0x02058593.
Lemma F_1300dc : fetch_word AsanUbsan.M.loaded_segments (0x130120 : word) = Some W_1300dc.
Proof. vm_refl. Qed.
Lemma D_1300dc : decode_any W_1300dc = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1300e0 : bv 32 := 0xfee6e4e3.
Lemma F_1300e0 : fetch_word AsanUbsan.M.loaded_segments (0x130124 : word) = Some W_1300e0.
Proof. vm_refl. Qed.
Lemma D_1300e0 : decode_any W_1300e0 = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1300e4 : bv 32 := 0x00008067.
Lemma F_1300e4 : fetch_word AsanUbsan.M.loaded_segments (0x130128 : word) = Some W_1300e4.
Proof. vm_refl. Qed.
Lemma D_1300e4 : decode_any W_1300e4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Abbreviation MSEGS := AsanUbsan.M.loaded_segments.
Definition ms_base : Z := 0x130034%Z.
Definition Fo_000 := F_12fff0.
Definition Do_000 := D_12fff0.
Definition Fo_004 := F_12fff4.
Definition Do_004 := D_12fff4.
Definition Fo_008 := F_12fff8.
Definition Do_008 := D_12fff8.
Definition Fo_00c := F_12fffc.
Definition Do_00c := D_12fffc.
Definition Fo_010 := F_130000.
Definition Do_010 := D_130000.
Definition Fo_014 := F_130004.
Definition Do_014 := D_130004.
Definition Fo_018 := F_130008.
Definition Do_018 := D_130008.
Definition Fo_01c := F_13000c.
Definition Do_01c := D_13000c.
Definition Fo_020 := F_130010.
Definition Do_020 := D_130010.
Definition Fo_024 := F_130014.
Definition Do_024 := D_130014.
Definition Fo_028 := F_130018.
Definition Do_028 := D_130018.
Definition Fo_02c := F_13001c.
Definition Do_02c := D_13001c.
Definition Fo_030 := F_130020.
Definition Do_030 := D_130020.
Definition Fo_034 := F_130024.
Definition Do_034 := D_130024.
Definition Fo_038 := F_130028.
Definition Do_038 := D_130028.
Definition Fo_03c := F_13002c.
Definition Do_03c := D_13002c.
Definition Fo_040 := F_130030.
Definition Do_040 := D_130030.
Definition Fo_044 := F_130034.
Definition Do_044 := D_130034.
Definition Fo_048 := F_130038.
Definition Do_048 := D_130038.
Definition Fo_04c := F_13003c.
Definition Do_04c := D_13003c.
Definition Fo_050 := F_130040.
Definition Do_050 := D_130040.
Definition Fo_054 := F_130044.
Definition Do_054 := D_130044.
Definition Fo_058 := F_130048.
Definition Do_058 := D_130048.
Definition Fo_05c := F_13004c.
Definition Do_05c := D_13004c.
Definition Fo_060 := F_130050.
Definition Do_060 := D_130050.
Definition Fo_064 := F_130054.
Definition Do_064 := D_130054.
Definition Fo_068 := F_130058.
Definition Do_068 := D_130058.
Definition Fo_06c := F_13005c.
Definition Do_06c := D_13005c.
Definition Fo_070 := F_130060.
Definition Do_070 := D_130060.
Definition Fo_074 := F_130064.
Definition Do_074 := D_130064.
Definition Fo_078 := F_130068.
Definition Do_078 := D_130068.
Definition Fo_07c := F_13006c.
Definition Do_07c := D_13006c.
Definition Fo_080 := F_130070.
Definition Do_080 := D_130070.
Definition Fo_084 := F_130074.
Definition Do_084 := D_130074.
Definition Fo_088 := F_130078.
Definition Do_088 := D_130078.
Definition Fo_08c := F_13007c.
Definition Do_08c := D_13007c.
Definition Fo_090 := F_130080.
Definition Do_090 := D_130080.
Definition Fo_094 := F_130084.
Definition Do_094 := D_130084.
Definition Fo_098 := F_130088.
Definition Do_098 := D_130088.
Definition Fo_09c := F_13008c.
Definition Do_09c := D_13008c.
Definition Fo_0a0 := F_130090.
Definition Do_0a0 := D_130090.
Definition Fo_0a4 := F_130094.
Definition Do_0a4 := D_130094.
Definition Fo_0a8 := F_130098.
Definition Do_0a8 := D_130098.
Definition Fo_0ac := F_13009c.
Definition Do_0ac := D_13009c.
Definition Fo_0b0 := F_1300a0.
Definition Do_0b0 := D_1300a0.
Definition Fo_0b4 := F_1300a4.
Definition Do_0b4 := D_1300a4.
Definition Fo_0b8 := F_1300a8.
Definition Do_0b8 := D_1300a8.
Definition Fo_0bc := F_1300ac.
Definition Do_0bc := D_1300ac.
Definition Fo_0c0 := F_1300b0.
Definition Do_0c0 := D_1300b0.
Definition Fo_0c4 := F_1300b4.
Definition Do_0c4 := D_1300b4.
Definition Fo_0c8 := F_1300b8.
Definition Do_0c8 := D_1300b8.
Definition Fo_0cc := F_1300bc.
Definition Do_0cc := D_1300bc.
Definition Fo_0d0 := F_1300c0.
Definition Do_0d0 := D_1300c0.
Definition Fo_0d4 := F_1300c4.
Definition Do_0d4 := D_1300c4.
Definition Fo_0d8 := F_1300c8.
Definition Do_0d8 := D_1300c8.
Definition Fo_0dc := F_1300cc.
Definition Do_0dc := D_1300cc.
Definition Fo_0e0 := F_1300d0.
Definition Do_0e0 := D_1300d0.
Definition Fo_0e4 := F_1300d4.
Definition Do_0e4 := D_1300d4.
Definition Fo_0e8 := F_1300d8.
Definition Do_0e8 := D_1300d8.
Definition Fo_0ec := F_1300dc.
Definition Do_0ec := D_1300dc.
Definition Fo_0f0 := F_1300e0.
Definition Do_0f0 := D_1300e0.
Definition Fo_0f4 := F_1300e4.
Definition Do_0f4 := D_1300e4.
