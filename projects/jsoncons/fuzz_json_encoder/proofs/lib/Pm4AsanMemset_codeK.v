(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_152e60 : bv 32 := 0x0e060a63.
Lemma F_152e60 : fetch_word Asan.M.loaded_segments (0x152ea4 : word) = Some W_152e60.
Proof. vm_refl. Qed.
Lemma D_152e60 : decode_any W_152e60 = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152e64 : bv 32 := 0x00b50023.
Lemma F_152e64 : fetch_word Asan.M.loaded_segments (0x152ea8 : word) = Some W_152e64.
Proof. vm_refl. Qed.
Lemma D_152e64 : decode_any W_152e64 = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152e68 : bv 32 := 0x00c506b3.
Lemma F_152e68 : fetch_word Asan.M.loaded_segments (0x152eac : word) = Some W_152e68.
Proof. vm_refl. Qed.
Lemma D_152e68 : decode_any W_152e68 = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152e6c : bv 32 := 0x00300713.
Lemma F_152e6c : fetch_word Asan.M.loaded_segments (0x152eb0 : word) = Some W_152e6c.
Proof. vm_refl. Qed.
Lemma D_152e6c : decode_any W_152e6c = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152e70 : bv 32 := 0xfeb68fa3.
Lemma F_152e70 : fetch_word Asan.M.loaded_segments (0x152eb4 : word) = Some W_152e70.
Proof. vm_refl. Qed.
Lemma D_152e70 : decode_any W_152e70 = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152e74 : bv 32 := 0x0ee66063.
Lemma F_152e74 : fetch_word Asan.M.loaded_segments (0x152eb8 : word) = Some W_152e74.
Proof. vm_refl. Qed.
Lemma D_152e74 : decode_any W_152e74 = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152e78 : bv 32 := 0x00b500a3.
Lemma F_152e78 : fetch_word Asan.M.loaded_segments (0x152ebc : word) = Some W_152e78.
Proof. vm_refl. Qed.
Lemma D_152e78 : decode_any W_152e78 = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152e7c : bv 32 := 0x00b50123.
Lemma F_152e7c : fetch_word Asan.M.loaded_segments (0x152ec0 : word) = Some W_152e7c.
Proof. vm_refl. Qed.
Lemma D_152e7c : decode_any W_152e7c = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152e80 : bv 32 := 0x00700713.
Lemma F_152e80 : fetch_word Asan.M.loaded_segments (0x152ec4 : word) = Some W_152e80.
Proof. vm_refl. Qed.
Lemma D_152e80 : decode_any W_152e80 = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152e84 : bv 32 := 0xfeb68ea3.
Lemma F_152e84 : fetch_word Asan.M.loaded_segments (0x152ec8 : word) = Some W_152e84.
Proof. vm_refl. Qed.
Lemma D_152e84 : decode_any W_152e84 = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152e88 : bv 32 := 0xfeb68f23.
Lemma F_152e88 : fetch_word Asan.M.loaded_segments (0x152ecc : word) = Some W_152e88.
Proof. vm_refl. Qed.
Lemma D_152e88 : decode_any W_152e88 = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152e8c : bv 32 := 0x0ce66463.
Lemma F_152e8c : fetch_word Asan.M.loaded_segments (0x152ed0 : word) = Some W_152e8c.
Proof. vm_refl. Qed.
Lemma D_152e8c : decode_any W_152e8c = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152e90 : bv 32 := 0x00b501a3.
Lemma F_152e90 : fetch_word Asan.M.loaded_segments (0x152ed4 : word) = Some W_152e90.
Proof. vm_refl. Qed.
Lemma D_152e90 : decode_any W_152e90 = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152e94 : bv 32 := 0x00900793.
Lemma F_152e94 : fetch_word Asan.M.loaded_segments (0x152ed8 : word) = Some W_152e94.
Proof. vm_refl. Qed.
Lemma D_152e94 : decode_any W_152e94 = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152e98 : bv 32 := 0xfeb68e23.
Lemma F_152e98 : fetch_word Asan.M.loaded_segments (0x152edc : word) = Some W_152e98.
Proof. vm_refl. Qed.
Lemma D_152e98 : decode_any W_152e98 = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152e9c : bv 32 := 0x0af66c63.
Lemma F_152e9c : fetch_word Asan.M.loaded_segments (0x152ee0 : word) = Some W_152e9c.
Proof. vm_refl. Qed.
Lemma D_152e9c : decode_any W_152e9c = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152ea0 : bv 32 := 0x40a006bb.
Lemma F_152ea0 : fetch_word Asan.M.loaded_segments (0x152ee4 : word) = Some W_152ea0.
Proof. vm_refl. Qed.
Lemma D_152ea0 : decode_any W_152ea0 = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152ea4 : bv 32 := 0x03859813.
Lemma F_152ea4 : fetch_word Asan.M.loaded_segments (0x152ee8 : word) = Some W_152ea4.
Proof. vm_refl. Qed.
Lemma D_152ea4 : decode_any W_152ea4 = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152ea8 : bv 32 := 0x101015b7.
Lemma F_152ea8 : fetch_word Asan.M.loaded_segments (0x152eec : word) = Some W_152ea8.
Proof. vm_refl. Qed.
Lemma D_152ea8 : decode_any W_152ea8 = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152eac : bv 32 := 0x0036f693.
Lemma F_152eac : fetch_word Asan.M.loaded_segments (0x152ef0 : word) = Some W_152eac.
Proof. vm_refl. Qed.
Lemma D_152eac : decode_any W_152eac = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152eb0 : bv 32 := 0x00459713.
Lemma F_152eb0 : fetch_word Asan.M.loaded_segments (0x152ef4 : word) = Some W_152eb0.
Proof. vm_refl. Qed.
Lemma D_152eb0 : decode_any W_152eb0 = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152eb4 : bv 32 := 0x40d60633.
Lemma F_152eb4 : fetch_word Asan.M.loaded_segments (0x152ef8 : word) = Some W_152eb4.
Proof. vm_refl. Qed.
Lemma D_152eb4 : decode_any W_152eb4 = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152eb8 : bv 32 := 0x00d505b3.
Lemma F_152eb8 : fetch_word Asan.M.loaded_segments (0x152efc : word) = Some W_152eb8.
Proof. vm_refl. Qed.
Lemma D_152eb8 : decode_any W_152eb8 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152ebc : bv 32 := 0x10070693.
Lemma F_152ebc : fetch_word Asan.M.loaded_segments (0x152f00 : word) = Some W_152ebc.
Proof. vm_refl. Qed.
Lemma D_152ebc : decode_any W_152ebc = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152ec0 : bv 32 := 0xffc67713.
Lemma F_152ec0 : fetch_word Asan.M.loaded_segments (0x152f04 : word) = Some W_152ec0.
Proof. vm_refl. Qed.
Lemma D_152ec0 : decode_any W_152ec0 = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152ec4 : bv 32 := 0x02d83633.
Lemma F_152ec4 : fetch_word Asan.M.loaded_segments (0x152f08 : word) = Some W_152ec4.
Proof. vm_refl. Qed.
Lemma D_152ec4 : decode_any W_152ec4 = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152ec8 : bv 32 := 0x00c5a023.
Lemma F_152ec8 : fetch_word Asan.M.loaded_segments (0x152f0c : word) = Some W_152ec8.
Proof. vm_refl. Qed.
Lemma D_152ec8 : decode_any W_152ec8 = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152ecc : bv 32 := 0x00e586b3.
Lemma F_152ecc : fetch_word Asan.M.loaded_segments (0x152f10 : word) = Some W_152ecc.
Proof. vm_refl. Qed.
Lemma D_152ecc : decode_any W_152ecc = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152ed0 : bv 32 := 0xfec6ae23.
Lemma F_152ed0 : fetch_word Asan.M.loaded_segments (0x152f14 : word) = Some W_152ed0.
Proof. vm_refl. Qed.
Lemma D_152ed0 : decode_any W_152ed0 = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152ed4 : bv 32 := 0x08f76063.
Lemma F_152ed4 : fetch_word Asan.M.loaded_segments (0x152f18 : word) = Some W_152ed4.
Proof. vm_refl. Qed.
Lemma D_152ed4 : decode_any W_152ed4 = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152ed8 : bv 32 := 0x00c5a223.
Lemma F_152ed8 : fetch_word Asan.M.loaded_segments (0x152f1c : word) = Some W_152ed8.
Proof. vm_refl. Qed.
Lemma D_152ed8 : decode_any W_152ed8 = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152edc : bv 32 := 0x00c5a423.
Lemma F_152edc : fetch_word Asan.M.loaded_segments (0x152f20 : word) = Some W_152edc.
Proof. vm_refl. Qed.
Lemma D_152edc : decode_any W_152edc = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152ee0 : bv 32 := 0x01900793.
Lemma F_152ee0 : fetch_word Asan.M.loaded_segments (0x152f24 : word) = Some W_152ee0.
Proof. vm_refl. Qed.
Lemma D_152ee0 : decode_any W_152ee0 = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152ee4 : bv 32 := 0xfec6aa23.
Lemma F_152ee4 : fetch_word Asan.M.loaded_segments (0x152f28 : word) = Some W_152ee4.
Proof. vm_refl. Qed.
Lemma D_152ee4 : decode_any W_152ee4 = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152ee8 : bv 32 := 0xfec6ac23.
Lemma F_152ee8 : fetch_word Asan.M.loaded_segments (0x152f2c : word) = Some W_152ee8.
Proof. vm_refl. Qed.
Lemma D_152ee8 : decode_any W_152ee8 = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152eec : bv 32 := 0x06f76463.
Lemma F_152eec : fetch_word Asan.M.loaded_segments (0x152f30 : word) = Some W_152eec.
Proof. vm_refl. Qed.
Lemma D_152eec : decode_any W_152eec = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152ef0 : bv 32 := 0x00c5a623.
Lemma F_152ef0 : fetch_word Asan.M.loaded_segments (0x152f34 : word) = Some W_152ef0.
Proof. vm_refl. Qed.
Lemma D_152ef0 : decode_any W_152ef0 = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152ef4 : bv 32 := 0x00c5a823.
Lemma F_152ef4 : fetch_word Asan.M.loaded_segments (0x152f38 : word) = Some W_152ef4.
Proof. vm_refl. Qed.
Lemma D_152ef4 : decode_any W_152ef4 = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152ef8 : bv 32 := 0x00c5aa23.
Lemma F_152ef8 : fetch_word Asan.M.loaded_segments (0x152f3c : word) = Some W_152ef8.
Proof. vm_refl. Qed.
Lemma D_152ef8 : decode_any W_152ef8 = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152efc : bv 32 := 0x00c5ac23.
Lemma F_152efc : fetch_word Asan.M.loaded_segments (0x152f40 : word) = Some W_152efc.
Proof. vm_refl. Qed.
Lemma D_152efc : decode_any W_152efc = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152f00 : bv 32 := 0x0045f793.
Lemma F_152f00 : fetch_word Asan.M.loaded_segments (0x152f44 : word) = Some W_152f00.
Proof. vm_refl. Qed.
Lemma D_152f00 : decode_any W_152f00 = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152f04 : bv 32 := 0x02000813.
Lemma F_152f04 : fetch_word Asan.M.loaded_segments (0x152f48 : word) = Some W_152f04.
Proof. vm_refl. Qed.
Lemma D_152f04 : decode_any W_152f04 = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152f08 : bv 32 := 0x01878793.
Lemma F_152f08 : fetch_word Asan.M.loaded_segments (0x152f4c : word) = Some W_152f08.
Proof. vm_refl. Qed.
Lemma D_152f08 : decode_any W_152f08 = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152f0c : bv 32 := 0x40f70733.
Lemma F_152f0c : fetch_word Asan.M.loaded_segments (0x152f50 : word) = Some W_152f0c.
Proof. vm_refl. Qed.
Lemma D_152f0c : decode_any W_152f0c = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152f10 : bv 32 := 0xfec6a223.
Lemma F_152f10 : fetch_word Asan.M.loaded_segments (0x152f54 : word) = Some W_152f10.
Proof. vm_refl. Qed.
Lemma D_152f10 : decode_any W_152f10 = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152f14 : bv 32 := 0xfec6a423.
Lemma F_152f14 : fetch_word Asan.M.loaded_segments (0x152f58 : word) = Some W_152f14.
Proof. vm_refl. Qed.
Lemma D_152f14 : decode_any W_152f14 = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152f18 : bv 32 := 0xfec6a623.
Lemma F_152f18 : fetch_word Asan.M.loaded_segments (0x152f5c : word) = Some W_152f18.
Proof. vm_refl. Qed.
Lemma D_152f18 : decode_any W_152f18 = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152f1c : bv 32 := 0xfec6a823.
Lemma F_152f1c : fetch_word Asan.M.loaded_segments (0x152f60 : word) = Some W_152f1c.
Proof. vm_refl. Qed.
Lemma D_152f1c : decode_any W_152f1c = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152f20 : bv 32 := 0x03076a63.
Lemma F_152f20 : fetch_word Asan.M.loaded_segments (0x152f64 : word) = Some W_152f20.
Proof. vm_refl. Qed.
Lemma D_152f20 : decode_any W_152f20 = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152f24 : bv 32 := 0x02061613.
Lemma F_152f24 : fetch_word Asan.M.loaded_segments (0x152f68 : word) = Some W_152f24.
Proof. vm_refl. Qed.
Lemma D_152f24 : decode_any W_152f24 = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152f28 : bv 32 := 0x00f585b3.
Lemma F_152f28 : fetch_word Asan.M.loaded_segments (0x152f6c : word) = Some W_152f28.
Proof. vm_refl. Qed.
Lemma D_152f28 : decode_any W_152f28 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152f2c : bv 32 := 0x02065693.
Lemma F_152f2c : fetch_word Asan.M.loaded_segments (0x152f70 : word) = Some W_152f2c.
Proof. vm_refl. Qed.
Lemma D_152f2c : decode_any W_152f2c = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152f30 : bv 32 := 0x00d66633.
Lemma F_152f30 : fetch_word Asan.M.loaded_segments (0x152f74 : word) = Some W_152f30.
Proof. vm_refl. Qed.
Lemma D_152f30 : decode_any W_152f30 = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152f34 : bv 32 := 0x01f00693.
Lemma F_152f34 : fetch_word Asan.M.loaded_segments (0x152f78 : word) = Some W_152f34.
Proof. vm_refl. Qed.
Lemma D_152f34 : decode_any W_152f34 = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152f38 : bv 32 := 0x00c5b023.
Lemma F_152f38 : fetch_word Asan.M.loaded_segments (0x152f7c : word) = Some W_152f38.
Proof. vm_refl. Qed.
Lemma D_152f38 : decode_any W_152f38 = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152f3c : bv 32 := 0x00c5b423.
Lemma F_152f3c : fetch_word Asan.M.loaded_segments (0x152f80 : word) = Some W_152f3c.
Proof. vm_refl. Qed.
Lemma D_152f3c : decode_any W_152f3c = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152f40 : bv 32 := 0x00c5b823.
Lemma F_152f40 : fetch_word Asan.M.loaded_segments (0x152f84 : word) = Some W_152f40.
Proof. vm_refl. Qed.
Lemma D_152f40 : decode_any W_152f40 = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152f44 : bv 32 := 0x00c5bc23.
Lemma F_152f44 : fetch_word Asan.M.loaded_segments (0x152f88 : word) = Some W_152f44.
Proof. vm_refl. Qed.
Lemma D_152f44 : decode_any W_152f44 = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152f48 : bv 32 := 0xfe070713.
Lemma F_152f48 : fetch_word Asan.M.loaded_segments (0x152f8c : word) = Some W_152f48.
Proof. vm_refl. Qed.
Lemma D_152f48 : decode_any W_152f48 = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152f4c : bv 32 := 0x02058593.
Lemma F_152f4c : fetch_word Asan.M.loaded_segments (0x152f90 : word) = Some W_152f4c.
Proof. vm_refl. Qed.
Lemma D_152f4c : decode_any W_152f4c = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152f50 : bv 32 := 0xfee6e4e3.
Lemma F_152f50 : fetch_word Asan.M.loaded_segments (0x152f94 : word) = Some W_152f50.
Proof. vm_refl. Qed.
Lemma D_152f50 : decode_any W_152f50 = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152f54 : bv 32 := 0x00008067.
Lemma F_152f54 : fetch_word Asan.M.loaded_segments (0x152f98 : word) = Some W_152f54.
Proof. vm_refl. Qed.
Lemma D_152f54 : decode_any W_152f54 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Abbreviation MSEGS := Asan.M.loaded_segments.
Definition ms_base : Z := 0x152ea4%Z.
Definition Fo_000 := F_152e60.
Definition Do_000 := D_152e60.
Definition Fo_004 := F_152e64.
Definition Do_004 := D_152e64.
Definition Fo_008 := F_152e68.
Definition Do_008 := D_152e68.
Definition Fo_00c := F_152e6c.
Definition Do_00c := D_152e6c.
Definition Fo_010 := F_152e70.
Definition Do_010 := D_152e70.
Definition Fo_014 := F_152e74.
Definition Do_014 := D_152e74.
Definition Fo_018 := F_152e78.
Definition Do_018 := D_152e78.
Definition Fo_01c := F_152e7c.
Definition Do_01c := D_152e7c.
Definition Fo_020 := F_152e80.
Definition Do_020 := D_152e80.
Definition Fo_024 := F_152e84.
Definition Do_024 := D_152e84.
Definition Fo_028 := F_152e88.
Definition Do_028 := D_152e88.
Definition Fo_02c := F_152e8c.
Definition Do_02c := D_152e8c.
Definition Fo_030 := F_152e90.
Definition Do_030 := D_152e90.
Definition Fo_034 := F_152e94.
Definition Do_034 := D_152e94.
Definition Fo_038 := F_152e98.
Definition Do_038 := D_152e98.
Definition Fo_03c := F_152e9c.
Definition Do_03c := D_152e9c.
Definition Fo_040 := F_152ea0.
Definition Do_040 := D_152ea0.
Definition Fo_044 := F_152ea4.
Definition Do_044 := D_152ea4.
Definition Fo_048 := F_152ea8.
Definition Do_048 := D_152ea8.
Definition Fo_04c := F_152eac.
Definition Do_04c := D_152eac.
Definition Fo_050 := F_152eb0.
Definition Do_050 := D_152eb0.
Definition Fo_054 := F_152eb4.
Definition Do_054 := D_152eb4.
Definition Fo_058 := F_152eb8.
Definition Do_058 := D_152eb8.
Definition Fo_05c := F_152ebc.
Definition Do_05c := D_152ebc.
Definition Fo_060 := F_152ec0.
Definition Do_060 := D_152ec0.
Definition Fo_064 := F_152ec4.
Definition Do_064 := D_152ec4.
Definition Fo_068 := F_152ec8.
Definition Do_068 := D_152ec8.
Definition Fo_06c := F_152ecc.
Definition Do_06c := D_152ecc.
Definition Fo_070 := F_152ed0.
Definition Do_070 := D_152ed0.
Definition Fo_074 := F_152ed4.
Definition Do_074 := D_152ed4.
Definition Fo_078 := F_152ed8.
Definition Do_078 := D_152ed8.
Definition Fo_07c := F_152edc.
Definition Do_07c := D_152edc.
Definition Fo_080 := F_152ee0.
Definition Do_080 := D_152ee0.
Definition Fo_084 := F_152ee4.
Definition Do_084 := D_152ee4.
Definition Fo_088 := F_152ee8.
Definition Do_088 := D_152ee8.
Definition Fo_08c := F_152eec.
Definition Do_08c := D_152eec.
Definition Fo_090 := F_152ef0.
Definition Do_090 := D_152ef0.
Definition Fo_094 := F_152ef4.
Definition Do_094 := D_152ef4.
Definition Fo_098 := F_152ef8.
Definition Do_098 := D_152ef8.
Definition Fo_09c := F_152efc.
Definition Do_09c := D_152efc.
Definition Fo_0a0 := F_152f00.
Definition Do_0a0 := D_152f00.
Definition Fo_0a4 := F_152f04.
Definition Do_0a4 := D_152f04.
Definition Fo_0a8 := F_152f08.
Definition Do_0a8 := D_152f08.
Definition Fo_0ac := F_152f0c.
Definition Do_0ac := D_152f0c.
Definition Fo_0b0 := F_152f10.
Definition Do_0b0 := D_152f10.
Definition Fo_0b4 := F_152f14.
Definition Do_0b4 := D_152f14.
Definition Fo_0b8 := F_152f18.
Definition Do_0b8 := D_152f18.
Definition Fo_0bc := F_152f1c.
Definition Do_0bc := D_152f1c.
Definition Fo_0c0 := F_152f20.
Definition Do_0c0 := D_152f20.
Definition Fo_0c4 := F_152f24.
Definition Do_0c4 := D_152f24.
Definition Fo_0c8 := F_152f28.
Definition Do_0c8 := D_152f28.
Definition Fo_0cc := F_152f2c.
Definition Do_0cc := D_152f2c.
Definition Fo_0d0 := F_152f30.
Definition Do_0d0 := D_152f30.
Definition Fo_0d4 := F_152f34.
Definition Do_0d4 := D_152f34.
Definition Fo_0d8 := F_152f38.
Definition Do_0d8 := D_152f38.
Definition Fo_0dc := F_152f3c.
Definition Do_0dc := D_152f3c.
Definition Fo_0e0 := F_152f40.
Definition Do_0e0 := D_152f40.
Definition Fo_0e4 := F_152f44.
Definition Do_0e4 := D_152f44.
Definition Fo_0e8 := F_152f48.
Definition Do_0e8 := D_152f48.
Definition Fo_0ec := F_152f4c.
Definition Do_0ec := D_152f4c.
Definition Fo_0f0 := F_152f50.
Definition Do_0f0 := D_152f50.
Definition Fo_0f4 := F_152f54.
Definition Do_0f4 := D_152f54.
