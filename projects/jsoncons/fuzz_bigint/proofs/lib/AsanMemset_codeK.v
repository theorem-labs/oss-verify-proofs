(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_cbb2c : bv 32 := 0x0e060a63.
Lemma F_cbb2c : fetch_word Asan.M.loaded_segments (0xcbb2c : word) = Some W_cbb2c.
Proof. vm_refl. Qed.
Lemma D_cbb2c : decode_any W_cbb2c = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbb30 : bv 32 := 0x00b50023.
Lemma F_cbb30 : fetch_word Asan.M.loaded_segments (0xcbb30 : word) = Some W_cbb30.
Proof. vm_refl. Qed.
Lemma D_cbb30 : decode_any W_cbb30 = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbb34 : bv 32 := 0x00c506b3.
Lemma F_cbb34 : fetch_word Asan.M.loaded_segments (0xcbb34 : word) = Some W_cbb34.
Proof. vm_refl. Qed.
Lemma D_cbb34 : decode_any W_cbb34 = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbb38 : bv 32 := 0x00300713.
Lemma F_cbb38 : fetch_word Asan.M.loaded_segments (0xcbb38 : word) = Some W_cbb38.
Proof. vm_refl. Qed.
Lemma D_cbb38 : decode_any W_cbb38 = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbb3c : bv 32 := 0xfeb68fa3.
Lemma F_cbb3c : fetch_word Asan.M.loaded_segments (0xcbb3c : word) = Some W_cbb3c.
Proof. vm_refl. Qed.
Lemma D_cbb3c : decode_any W_cbb3c = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbb40 : bv 32 := 0x0ee66063.
Lemma F_cbb40 : fetch_word Asan.M.loaded_segments (0xcbb40 : word) = Some W_cbb40.
Proof. vm_refl. Qed.
Lemma D_cbb40 : decode_any W_cbb40 = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbb44 : bv 32 := 0x00b500a3.
Lemma F_cbb44 : fetch_word Asan.M.loaded_segments (0xcbb44 : word) = Some W_cbb44.
Proof. vm_refl. Qed.
Lemma D_cbb44 : decode_any W_cbb44 = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbb48 : bv 32 := 0x00b50123.
Lemma F_cbb48 : fetch_word Asan.M.loaded_segments (0xcbb48 : word) = Some W_cbb48.
Proof. vm_refl. Qed.
Lemma D_cbb48 : decode_any W_cbb48 = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbb4c : bv 32 := 0x00700713.
Lemma F_cbb4c : fetch_word Asan.M.loaded_segments (0xcbb4c : word) = Some W_cbb4c.
Proof. vm_refl. Qed.
Lemma D_cbb4c : decode_any W_cbb4c = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbb50 : bv 32 := 0xfeb68ea3.
Lemma F_cbb50 : fetch_word Asan.M.loaded_segments (0xcbb50 : word) = Some W_cbb50.
Proof. vm_refl. Qed.
Lemma D_cbb50 : decode_any W_cbb50 = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbb54 : bv 32 := 0xfeb68f23.
Lemma F_cbb54 : fetch_word Asan.M.loaded_segments (0xcbb54 : word) = Some W_cbb54.
Proof. vm_refl. Qed.
Lemma D_cbb54 : decode_any W_cbb54 = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbb58 : bv 32 := 0x0ce66463.
Lemma F_cbb58 : fetch_word Asan.M.loaded_segments (0xcbb58 : word) = Some W_cbb58.
Proof. vm_refl. Qed.
Lemma D_cbb58 : decode_any W_cbb58 = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbb5c : bv 32 := 0x00b501a3.
Lemma F_cbb5c : fetch_word Asan.M.loaded_segments (0xcbb5c : word) = Some W_cbb5c.
Proof. vm_refl. Qed.
Lemma D_cbb5c : decode_any W_cbb5c = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbb60 : bv 32 := 0x00900793.
Lemma F_cbb60 : fetch_word Asan.M.loaded_segments (0xcbb60 : word) = Some W_cbb60.
Proof. vm_refl. Qed.
Lemma D_cbb60 : decode_any W_cbb60 = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbb64 : bv 32 := 0xfeb68e23.
Lemma F_cbb64 : fetch_word Asan.M.loaded_segments (0xcbb64 : word) = Some W_cbb64.
Proof. vm_refl. Qed.
Lemma D_cbb64 : decode_any W_cbb64 = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbb68 : bv 32 := 0x0af66c63.
Lemma F_cbb68 : fetch_word Asan.M.loaded_segments (0xcbb68 : word) = Some W_cbb68.
Proof. vm_refl. Qed.
Lemma D_cbb68 : decode_any W_cbb68 = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbb6c : bv 32 := 0x40a006bb.
Lemma F_cbb6c : fetch_word Asan.M.loaded_segments (0xcbb6c : word) = Some W_cbb6c.
Proof. vm_refl. Qed.
Lemma D_cbb6c : decode_any W_cbb6c = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbb70 : bv 32 := 0x03859813.
Lemma F_cbb70 : fetch_word Asan.M.loaded_segments (0xcbb70 : word) = Some W_cbb70.
Proof. vm_refl. Qed.
Lemma D_cbb70 : decode_any W_cbb70 = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbb74 : bv 32 := 0x101015b7.
Lemma F_cbb74 : fetch_word Asan.M.loaded_segments (0xcbb74 : word) = Some W_cbb74.
Proof. vm_refl. Qed.
Lemma D_cbb74 : decode_any W_cbb74 = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbb78 : bv 32 := 0x0036f693.
Lemma F_cbb78 : fetch_word Asan.M.loaded_segments (0xcbb78 : word) = Some W_cbb78.
Proof. vm_refl. Qed.
Lemma D_cbb78 : decode_any W_cbb78 = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbb7c : bv 32 := 0x00459713.
Lemma F_cbb7c : fetch_word Asan.M.loaded_segments (0xcbb7c : word) = Some W_cbb7c.
Proof. vm_refl. Qed.
Lemma D_cbb7c : decode_any W_cbb7c = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbb80 : bv 32 := 0x40d60633.
Lemma F_cbb80 : fetch_word Asan.M.loaded_segments (0xcbb80 : word) = Some W_cbb80.
Proof. vm_refl. Qed.
Lemma D_cbb80 : decode_any W_cbb80 = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbb84 : bv 32 := 0x00d505b3.
Lemma F_cbb84 : fetch_word Asan.M.loaded_segments (0xcbb84 : word) = Some W_cbb84.
Proof. vm_refl. Qed.
Lemma D_cbb84 : decode_any W_cbb84 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbb88 : bv 32 := 0x10070693.
Lemma F_cbb88 : fetch_word Asan.M.loaded_segments (0xcbb88 : word) = Some W_cbb88.
Proof. vm_refl. Qed.
Lemma D_cbb88 : decode_any W_cbb88 = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbb8c : bv 32 := 0xffc67713.
Lemma F_cbb8c : fetch_word Asan.M.loaded_segments (0xcbb8c : word) = Some W_cbb8c.
Proof. vm_refl. Qed.
Lemma D_cbb8c : decode_any W_cbb8c = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbb90 : bv 32 := 0x02d83633.
Lemma F_cbb90 : fetch_word Asan.M.loaded_segments (0xcbb90 : word) = Some W_cbb90.
Proof. vm_refl. Qed.
Lemma D_cbb90 : decode_any W_cbb90 = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbb94 : bv 32 := 0x00c5a023.
Lemma F_cbb94 : fetch_word Asan.M.loaded_segments (0xcbb94 : word) = Some W_cbb94.
Proof. vm_refl. Qed.
Lemma D_cbb94 : decode_any W_cbb94 = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbb98 : bv 32 := 0x00e586b3.
Lemma F_cbb98 : fetch_word Asan.M.loaded_segments (0xcbb98 : word) = Some W_cbb98.
Proof. vm_refl. Qed.
Lemma D_cbb98 : decode_any W_cbb98 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbb9c : bv 32 := 0xfec6ae23.
Lemma F_cbb9c : fetch_word Asan.M.loaded_segments (0xcbb9c : word) = Some W_cbb9c.
Proof. vm_refl. Qed.
Lemma D_cbb9c : decode_any W_cbb9c = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbba0 : bv 32 := 0x08f76063.
Lemma F_cbba0 : fetch_word Asan.M.loaded_segments (0xcbba0 : word) = Some W_cbba0.
Proof. vm_refl. Qed.
Lemma D_cbba0 : decode_any W_cbba0 = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbba4 : bv 32 := 0x00c5a223.
Lemma F_cbba4 : fetch_word Asan.M.loaded_segments (0xcbba4 : word) = Some W_cbba4.
Proof. vm_refl. Qed.
Lemma D_cbba4 : decode_any W_cbba4 = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbba8 : bv 32 := 0x00c5a423.
Lemma F_cbba8 : fetch_word Asan.M.loaded_segments (0xcbba8 : word) = Some W_cbba8.
Proof. vm_refl. Qed.
Lemma D_cbba8 : decode_any W_cbba8 = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbbac : bv 32 := 0x01900793.
Lemma F_cbbac : fetch_word Asan.M.loaded_segments (0xcbbac : word) = Some W_cbbac.
Proof. vm_refl. Qed.
Lemma D_cbbac : decode_any W_cbbac = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbbb0 : bv 32 := 0xfec6aa23.
Lemma F_cbbb0 : fetch_word Asan.M.loaded_segments (0xcbbb0 : word) = Some W_cbbb0.
Proof. vm_refl. Qed.
Lemma D_cbbb0 : decode_any W_cbbb0 = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbbb4 : bv 32 := 0xfec6ac23.
Lemma F_cbbb4 : fetch_word Asan.M.loaded_segments (0xcbbb4 : word) = Some W_cbbb4.
Proof. vm_refl. Qed.
Lemma D_cbbb4 : decode_any W_cbbb4 = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbbb8 : bv 32 := 0x06f76463.
Lemma F_cbbb8 : fetch_word Asan.M.loaded_segments (0xcbbb8 : word) = Some W_cbbb8.
Proof. vm_refl. Qed.
Lemma D_cbbb8 : decode_any W_cbbb8 = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbbbc : bv 32 := 0x00c5a623.
Lemma F_cbbbc : fetch_word Asan.M.loaded_segments (0xcbbbc : word) = Some W_cbbbc.
Proof. vm_refl. Qed.
Lemma D_cbbbc : decode_any W_cbbbc = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbbc0 : bv 32 := 0x00c5a823.
Lemma F_cbbc0 : fetch_word Asan.M.loaded_segments (0xcbbc0 : word) = Some W_cbbc0.
Proof. vm_refl. Qed.
Lemma D_cbbc0 : decode_any W_cbbc0 = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbbc4 : bv 32 := 0x00c5aa23.
Lemma F_cbbc4 : fetch_word Asan.M.loaded_segments (0xcbbc4 : word) = Some W_cbbc4.
Proof. vm_refl. Qed.
Lemma D_cbbc4 : decode_any W_cbbc4 = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbbc8 : bv 32 := 0x00c5ac23.
Lemma F_cbbc8 : fetch_word Asan.M.loaded_segments (0xcbbc8 : word) = Some W_cbbc8.
Proof. vm_refl. Qed.
Lemma D_cbbc8 : decode_any W_cbbc8 = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbbcc : bv 32 := 0x0045f793.
Lemma F_cbbcc : fetch_word Asan.M.loaded_segments (0xcbbcc : word) = Some W_cbbcc.
Proof. vm_refl. Qed.
Lemma D_cbbcc : decode_any W_cbbcc = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbbd0 : bv 32 := 0x02000813.
Lemma F_cbbd0 : fetch_word Asan.M.loaded_segments (0xcbbd0 : word) = Some W_cbbd0.
Proof. vm_refl. Qed.
Lemma D_cbbd0 : decode_any W_cbbd0 = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbbd4 : bv 32 := 0x01878793.
Lemma F_cbbd4 : fetch_word Asan.M.loaded_segments (0xcbbd4 : word) = Some W_cbbd4.
Proof. vm_refl. Qed.
Lemma D_cbbd4 : decode_any W_cbbd4 = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbbd8 : bv 32 := 0x40f70733.
Lemma F_cbbd8 : fetch_word Asan.M.loaded_segments (0xcbbd8 : word) = Some W_cbbd8.
Proof. vm_refl. Qed.
Lemma D_cbbd8 : decode_any W_cbbd8 = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbbdc : bv 32 := 0xfec6a223.
Lemma F_cbbdc : fetch_word Asan.M.loaded_segments (0xcbbdc : word) = Some W_cbbdc.
Proof. vm_refl. Qed.
Lemma D_cbbdc : decode_any W_cbbdc = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbbe0 : bv 32 := 0xfec6a423.
Lemma F_cbbe0 : fetch_word Asan.M.loaded_segments (0xcbbe0 : word) = Some W_cbbe0.
Proof. vm_refl. Qed.
Lemma D_cbbe0 : decode_any W_cbbe0 = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbbe4 : bv 32 := 0xfec6a623.
Lemma F_cbbe4 : fetch_word Asan.M.loaded_segments (0xcbbe4 : word) = Some W_cbbe4.
Proof. vm_refl. Qed.
Lemma D_cbbe4 : decode_any W_cbbe4 = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbbe8 : bv 32 := 0xfec6a823.
Lemma F_cbbe8 : fetch_word Asan.M.loaded_segments (0xcbbe8 : word) = Some W_cbbe8.
Proof. vm_refl. Qed.
Lemma D_cbbe8 : decode_any W_cbbe8 = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbbec : bv 32 := 0x03076a63.
Lemma F_cbbec : fetch_word Asan.M.loaded_segments (0xcbbec : word) = Some W_cbbec.
Proof. vm_refl. Qed.
Lemma D_cbbec : decode_any W_cbbec = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbbf0 : bv 32 := 0x02061613.
Lemma F_cbbf0 : fetch_word Asan.M.loaded_segments (0xcbbf0 : word) = Some W_cbbf0.
Proof. vm_refl. Qed.
Lemma D_cbbf0 : decode_any W_cbbf0 = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbbf4 : bv 32 := 0x00f585b3.
Lemma F_cbbf4 : fetch_word Asan.M.loaded_segments (0xcbbf4 : word) = Some W_cbbf4.
Proof. vm_refl. Qed.
Lemma D_cbbf4 : decode_any W_cbbf4 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbbf8 : bv 32 := 0x02065693.
Lemma F_cbbf8 : fetch_word Asan.M.loaded_segments (0xcbbf8 : word) = Some W_cbbf8.
Proof. vm_refl. Qed.
Lemma D_cbbf8 : decode_any W_cbbf8 = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbbfc : bv 32 := 0x00d66633.
Lemma F_cbbfc : fetch_word Asan.M.loaded_segments (0xcbbfc : word) = Some W_cbbfc.
Proof. vm_refl. Qed.
Lemma D_cbbfc : decode_any W_cbbfc = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbc00 : bv 32 := 0x01f00693.
Lemma F_cbc00 : fetch_word Asan.M.loaded_segments (0xcbc00 : word) = Some W_cbc00.
Proof. vm_refl. Qed.
Lemma D_cbc00 : decode_any W_cbc00 = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbc04 : bv 32 := 0x00c5b023.
Lemma F_cbc04 : fetch_word Asan.M.loaded_segments (0xcbc04 : word) = Some W_cbc04.
Proof. vm_refl. Qed.
Lemma D_cbc04 : decode_any W_cbc04 = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbc08 : bv 32 := 0x00c5b423.
Lemma F_cbc08 : fetch_word Asan.M.loaded_segments (0xcbc08 : word) = Some W_cbc08.
Proof. vm_refl. Qed.
Lemma D_cbc08 : decode_any W_cbc08 = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbc0c : bv 32 := 0x00c5b823.
Lemma F_cbc0c : fetch_word Asan.M.loaded_segments (0xcbc0c : word) = Some W_cbc0c.
Proof. vm_refl. Qed.
Lemma D_cbc0c : decode_any W_cbc0c = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbc10 : bv 32 := 0x00c5bc23.
Lemma F_cbc10 : fetch_word Asan.M.loaded_segments (0xcbc10 : word) = Some W_cbc10.
Proof. vm_refl. Qed.
Lemma D_cbc10 : decode_any W_cbc10 = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbc14 : bv 32 := 0xfe070713.
Lemma F_cbc14 : fetch_word Asan.M.loaded_segments (0xcbc14 : word) = Some W_cbc14.
Proof. vm_refl. Qed.
Lemma D_cbc14 : decode_any W_cbc14 = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbc18 : bv 32 := 0x02058593.
Lemma F_cbc18 : fetch_word Asan.M.loaded_segments (0xcbc18 : word) = Some W_cbc18.
Proof. vm_refl. Qed.
Lemma D_cbc18 : decode_any W_cbc18 = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbc1c : bv 32 := 0xfee6e4e3.
Lemma F_cbc1c : fetch_word Asan.M.loaded_segments (0xcbc1c : word) = Some W_cbc1c.
Proof. vm_refl. Qed.
Lemma D_cbc1c : decode_any W_cbc1c = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cbc20 : bv 32 := 0x00008067.
Lemma F_cbc20 : fetch_word Asan.M.loaded_segments (0xcbc20 : word) = Some W_cbc20.
Proof. vm_refl. Qed.
Lemma D_cbc20 : decode_any W_cbc20 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Abbreviation MSEGS := Asan.M.loaded_segments.
Definition ms_base : Z := 0xcbb2c%Z.
Definition Fo_000 := F_cbb2c.
Definition Do_000 := D_cbb2c.
Definition Fo_004 := F_cbb30.
Definition Do_004 := D_cbb30.
Definition Fo_008 := F_cbb34.
Definition Do_008 := D_cbb34.
Definition Fo_00c := F_cbb38.
Definition Do_00c := D_cbb38.
Definition Fo_010 := F_cbb3c.
Definition Do_010 := D_cbb3c.
Definition Fo_014 := F_cbb40.
Definition Do_014 := D_cbb40.
Definition Fo_018 := F_cbb44.
Definition Do_018 := D_cbb44.
Definition Fo_01c := F_cbb48.
Definition Do_01c := D_cbb48.
Definition Fo_020 := F_cbb4c.
Definition Do_020 := D_cbb4c.
Definition Fo_024 := F_cbb50.
Definition Do_024 := D_cbb50.
Definition Fo_028 := F_cbb54.
Definition Do_028 := D_cbb54.
Definition Fo_02c := F_cbb58.
Definition Do_02c := D_cbb58.
Definition Fo_030 := F_cbb5c.
Definition Do_030 := D_cbb5c.
Definition Fo_034 := F_cbb60.
Definition Do_034 := D_cbb60.
Definition Fo_038 := F_cbb64.
Definition Do_038 := D_cbb64.
Definition Fo_03c := F_cbb68.
Definition Do_03c := D_cbb68.
Definition Fo_040 := F_cbb6c.
Definition Do_040 := D_cbb6c.
Definition Fo_044 := F_cbb70.
Definition Do_044 := D_cbb70.
Definition Fo_048 := F_cbb74.
Definition Do_048 := D_cbb74.
Definition Fo_04c := F_cbb78.
Definition Do_04c := D_cbb78.
Definition Fo_050 := F_cbb7c.
Definition Do_050 := D_cbb7c.
Definition Fo_054 := F_cbb80.
Definition Do_054 := D_cbb80.
Definition Fo_058 := F_cbb84.
Definition Do_058 := D_cbb84.
Definition Fo_05c := F_cbb88.
Definition Do_05c := D_cbb88.
Definition Fo_060 := F_cbb8c.
Definition Do_060 := D_cbb8c.
Definition Fo_064 := F_cbb90.
Definition Do_064 := D_cbb90.
Definition Fo_068 := F_cbb94.
Definition Do_068 := D_cbb94.
Definition Fo_06c := F_cbb98.
Definition Do_06c := D_cbb98.
Definition Fo_070 := F_cbb9c.
Definition Do_070 := D_cbb9c.
Definition Fo_074 := F_cbba0.
Definition Do_074 := D_cbba0.
Definition Fo_078 := F_cbba4.
Definition Do_078 := D_cbba4.
Definition Fo_07c := F_cbba8.
Definition Do_07c := D_cbba8.
Definition Fo_080 := F_cbbac.
Definition Do_080 := D_cbbac.
Definition Fo_084 := F_cbbb0.
Definition Do_084 := D_cbbb0.
Definition Fo_088 := F_cbbb4.
Definition Do_088 := D_cbbb4.
Definition Fo_08c := F_cbbb8.
Definition Do_08c := D_cbbb8.
Definition Fo_090 := F_cbbbc.
Definition Do_090 := D_cbbbc.
Definition Fo_094 := F_cbbc0.
Definition Do_094 := D_cbbc0.
Definition Fo_098 := F_cbbc4.
Definition Do_098 := D_cbbc4.
Definition Fo_09c := F_cbbc8.
Definition Do_09c := D_cbbc8.
Definition Fo_0a0 := F_cbbcc.
Definition Do_0a0 := D_cbbcc.
Definition Fo_0a4 := F_cbbd0.
Definition Do_0a4 := D_cbbd0.
Definition Fo_0a8 := F_cbbd4.
Definition Do_0a8 := D_cbbd4.
Definition Fo_0ac := F_cbbd8.
Definition Do_0ac := D_cbbd8.
Definition Fo_0b0 := F_cbbdc.
Definition Do_0b0 := D_cbbdc.
Definition Fo_0b4 := F_cbbe0.
Definition Do_0b4 := D_cbbe0.
Definition Fo_0b8 := F_cbbe4.
Definition Do_0b8 := D_cbbe4.
Definition Fo_0bc := F_cbbe8.
Definition Do_0bc := D_cbbe8.
Definition Fo_0c0 := F_cbbec.
Definition Do_0c0 := D_cbbec.
Definition Fo_0c4 := F_cbbf0.
Definition Do_0c4 := D_cbbf0.
Definition Fo_0c8 := F_cbbf4.
Definition Do_0c8 := D_cbbf4.
Definition Fo_0cc := F_cbbf8.
Definition Do_0cc := D_cbbf8.
Definition Fo_0d0 := F_cbbfc.
Definition Do_0d0 := D_cbbfc.
Definition Fo_0d4 := F_cbc00.
Definition Do_0d4 := D_cbc00.
Definition Fo_0d8 := F_cbc04.
Definition Do_0d8 := D_cbc04.
Definition Fo_0dc := F_cbc08.
Definition Do_0dc := D_cbc08.
Definition Fo_0e0 := F_cbc0c.
Definition Do_0e0 := D_cbc0c.
Definition Fo_0e4 := F_cbc10.
Definition Do_0e4 := D_cbc10.
Definition Fo_0e8 := F_cbc14.
Definition Do_0e8 := D_cbc14.
Definition Fo_0ec := F_cbc18.
Definition Do_0ec := D_cbc18.
Definition Fo_0f0 := F_cbc1c.
Definition Do_0f0 := D_cbc1c.
Definition Fo_0f4 := F_cbc20.
Definition Do_0f4 := D_cbc20.
