(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.yajl_ruby.json_fuzzer.images Require Import Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)


(* [comment removed for export] *)
Definition W_9d45c : bv 32 := 0x0e060a63.
Lemma F_9d45c : fetch_word Asan.M.loaded_segments (0x9e0e0 : word) = Some W_9d45c.
Proof. vm_refl. Qed.
Lemma D_9d45c : decode_any W_9d45c = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d460 : bv 32 := 0x00b50023.
Lemma F_9d460 : fetch_word Asan.M.loaded_segments (0x9e0e4 : word) = Some W_9d460.
Proof. vm_refl. Qed.
Lemma D_9d460 : decode_any W_9d460 = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d464 : bv 32 := 0x00c506b3.
Lemma F_9d464 : fetch_word Asan.M.loaded_segments (0x9e0e8 : word) = Some W_9d464.
Proof. vm_refl. Qed.
Lemma D_9d464 : decode_any W_9d464 = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d468 : bv 32 := 0x00300713.
Lemma F_9d468 : fetch_word Asan.M.loaded_segments (0x9e0ec : word) = Some W_9d468.
Proof. vm_refl. Qed.
Lemma D_9d468 : decode_any W_9d468 = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d46c : bv 32 := 0xfeb68fa3.
Lemma F_9d46c : fetch_word Asan.M.loaded_segments (0x9e0f0 : word) = Some W_9d46c.
Proof. vm_refl. Qed.
Lemma D_9d46c : decode_any W_9d46c = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d470 : bv 32 := 0x0ee66063.
Lemma F_9d470 : fetch_word Asan.M.loaded_segments (0x9e0f4 : word) = Some W_9d470.
Proof. vm_refl. Qed.
Lemma D_9d470 : decode_any W_9d470 = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d474 : bv 32 := 0x00b500a3.
Lemma F_9d474 : fetch_word Asan.M.loaded_segments (0x9e0f8 : word) = Some W_9d474.
Proof. vm_refl. Qed.
Lemma D_9d474 : decode_any W_9d474 = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d478 : bv 32 := 0x00b50123.
Lemma F_9d478 : fetch_word Asan.M.loaded_segments (0x9e0fc : word) = Some W_9d478.
Proof. vm_refl. Qed.
Lemma D_9d478 : decode_any W_9d478 = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d47c : bv 32 := 0x00700713.
Lemma F_9d47c : fetch_word Asan.M.loaded_segments (0x9e100 : word) = Some W_9d47c.
Proof. vm_refl. Qed.
Lemma D_9d47c : decode_any W_9d47c = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d480 : bv 32 := 0xfeb68ea3.
Lemma F_9d480 : fetch_word Asan.M.loaded_segments (0x9e104 : word) = Some W_9d480.
Proof. vm_refl. Qed.
Lemma D_9d480 : decode_any W_9d480 = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d484 : bv 32 := 0xfeb68f23.
Lemma F_9d484 : fetch_word Asan.M.loaded_segments (0x9e108 : word) = Some W_9d484.
Proof. vm_refl. Qed.
Lemma D_9d484 : decode_any W_9d484 = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d488 : bv 32 := 0x0ce66463.
Lemma F_9d488 : fetch_word Asan.M.loaded_segments (0x9e10c : word) = Some W_9d488.
Proof. vm_refl. Qed.
Lemma D_9d488 : decode_any W_9d488 = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d48c : bv 32 := 0x00b501a3.
Lemma F_9d48c : fetch_word Asan.M.loaded_segments (0x9e110 : word) = Some W_9d48c.
Proof. vm_refl. Qed.
Lemma D_9d48c : decode_any W_9d48c = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d490 : bv 32 := 0x00900793.
Lemma F_9d490 : fetch_word Asan.M.loaded_segments (0x9e114 : word) = Some W_9d490.
Proof. vm_refl. Qed.
Lemma D_9d490 : decode_any W_9d490 = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d494 : bv 32 := 0xfeb68e23.
Lemma F_9d494 : fetch_word Asan.M.loaded_segments (0x9e118 : word) = Some W_9d494.
Proof. vm_refl. Qed.
Lemma D_9d494 : decode_any W_9d494 = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d498 : bv 32 := 0x0af66c63.
Lemma F_9d498 : fetch_word Asan.M.loaded_segments (0x9e11c : word) = Some W_9d498.
Proof. vm_refl. Qed.
Lemma D_9d498 : decode_any W_9d498 = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d49c : bv 32 := 0x40a006bb.
Lemma F_9d49c : fetch_word Asan.M.loaded_segments (0x9e120 : word) = Some W_9d49c.
Proof. vm_refl. Qed.
Lemma D_9d49c : decode_any W_9d49c = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d4a0 : bv 32 := 0x03859813.
Lemma F_9d4a0 : fetch_word Asan.M.loaded_segments (0x9e124 : word) = Some W_9d4a0.
Proof. vm_refl. Qed.
Lemma D_9d4a0 : decode_any W_9d4a0 = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d4a4 : bv 32 := 0x101015b7.
Lemma F_9d4a4 : fetch_word Asan.M.loaded_segments (0x9e128 : word) = Some W_9d4a4.
Proof. vm_refl. Qed.
Lemma D_9d4a4 : decode_any W_9d4a4 = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d4a8 : bv 32 := 0x0036f693.
Lemma F_9d4a8 : fetch_word Asan.M.loaded_segments (0x9e12c : word) = Some W_9d4a8.
Proof. vm_refl. Qed.
Lemma D_9d4a8 : decode_any W_9d4a8 = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d4ac : bv 32 := 0x00459713.
Lemma F_9d4ac : fetch_word Asan.M.loaded_segments (0x9e130 : word) = Some W_9d4ac.
Proof. vm_refl. Qed.
Lemma D_9d4ac : decode_any W_9d4ac = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d4b0 : bv 32 := 0x40d60633.
Lemma F_9d4b0 : fetch_word Asan.M.loaded_segments (0x9e134 : word) = Some W_9d4b0.
Proof. vm_refl. Qed.
Lemma D_9d4b0 : decode_any W_9d4b0 = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d4b4 : bv 32 := 0x00d505b3.
Lemma F_9d4b4 : fetch_word Asan.M.loaded_segments (0x9e138 : word) = Some W_9d4b4.
Proof. vm_refl. Qed.
Lemma D_9d4b4 : decode_any W_9d4b4 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d4b8 : bv 32 := 0x10070693.
Lemma F_9d4b8 : fetch_word Asan.M.loaded_segments (0x9e13c : word) = Some W_9d4b8.
Proof. vm_refl. Qed.
Lemma D_9d4b8 : decode_any W_9d4b8 = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d4bc : bv 32 := 0xffc67713.
Lemma F_9d4bc : fetch_word Asan.M.loaded_segments (0x9e140 : word) = Some W_9d4bc.
Proof. vm_refl. Qed.
Lemma D_9d4bc : decode_any W_9d4bc = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d4c0 : bv 32 := 0x02d83633.
Lemma F_9d4c0 : fetch_word Asan.M.loaded_segments (0x9e144 : word) = Some W_9d4c0.
Proof. vm_refl. Qed.
Lemma D_9d4c0 : decode_any W_9d4c0 = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d4c4 : bv 32 := 0x00c5a023.
Lemma F_9d4c4 : fetch_word Asan.M.loaded_segments (0x9e148 : word) = Some W_9d4c4.
Proof. vm_refl. Qed.
Lemma D_9d4c4 : decode_any W_9d4c4 = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d4c8 : bv 32 := 0x00e586b3.
Lemma F_9d4c8 : fetch_word Asan.M.loaded_segments (0x9e14c : word) = Some W_9d4c8.
Proof. vm_refl. Qed.
Lemma D_9d4c8 : decode_any W_9d4c8 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d4cc : bv 32 := 0xfec6ae23.
Lemma F_9d4cc : fetch_word Asan.M.loaded_segments (0x9e150 : word) = Some W_9d4cc.
Proof. vm_refl. Qed.
Lemma D_9d4cc : decode_any W_9d4cc = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d4d0 : bv 32 := 0x08f76063.
Lemma F_9d4d0 : fetch_word Asan.M.loaded_segments (0x9e154 : word) = Some W_9d4d0.
Proof. vm_refl. Qed.
Lemma D_9d4d0 : decode_any W_9d4d0 = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d4d4 : bv 32 := 0x00c5a223.
Lemma F_9d4d4 : fetch_word Asan.M.loaded_segments (0x9e158 : word) = Some W_9d4d4.
Proof. vm_refl. Qed.
Lemma D_9d4d4 : decode_any W_9d4d4 = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d4d8 : bv 32 := 0x00c5a423.
Lemma F_9d4d8 : fetch_word Asan.M.loaded_segments (0x9e15c : word) = Some W_9d4d8.
Proof. vm_refl. Qed.
Lemma D_9d4d8 : decode_any W_9d4d8 = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d4dc : bv 32 := 0x01900793.
Lemma F_9d4dc : fetch_word Asan.M.loaded_segments (0x9e160 : word) = Some W_9d4dc.
Proof. vm_refl. Qed.
Lemma D_9d4dc : decode_any W_9d4dc = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d4e0 : bv 32 := 0xfec6aa23.
Lemma F_9d4e0 : fetch_word Asan.M.loaded_segments (0x9e164 : word) = Some W_9d4e0.
Proof. vm_refl. Qed.
Lemma D_9d4e0 : decode_any W_9d4e0 = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d4e4 : bv 32 := 0xfec6ac23.
Lemma F_9d4e4 : fetch_word Asan.M.loaded_segments (0x9e168 : word) = Some W_9d4e4.
Proof. vm_refl. Qed.
Lemma D_9d4e4 : decode_any W_9d4e4 = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d4e8 : bv 32 := 0x06f76463.
Lemma F_9d4e8 : fetch_word Asan.M.loaded_segments (0x9e16c : word) = Some W_9d4e8.
Proof. vm_refl. Qed.
Lemma D_9d4e8 : decode_any W_9d4e8 = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d4ec : bv 32 := 0x00c5a623.
Lemma F_9d4ec : fetch_word Asan.M.loaded_segments (0x9e170 : word) = Some W_9d4ec.
Proof. vm_refl. Qed.
Lemma D_9d4ec : decode_any W_9d4ec = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d4f0 : bv 32 := 0x00c5a823.
Lemma F_9d4f0 : fetch_word Asan.M.loaded_segments (0x9e174 : word) = Some W_9d4f0.
Proof. vm_refl. Qed.
Lemma D_9d4f0 : decode_any W_9d4f0 = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d4f4 : bv 32 := 0x00c5aa23.
Lemma F_9d4f4 : fetch_word Asan.M.loaded_segments (0x9e178 : word) = Some W_9d4f4.
Proof. vm_refl. Qed.
Lemma D_9d4f4 : decode_any W_9d4f4 = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d4f8 : bv 32 := 0x00c5ac23.
Lemma F_9d4f8 : fetch_word Asan.M.loaded_segments (0x9e17c : word) = Some W_9d4f8.
Proof. vm_refl. Qed.
Lemma D_9d4f8 : decode_any W_9d4f8 = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d4fc : bv 32 := 0x0045f793.
Lemma F_9d4fc : fetch_word Asan.M.loaded_segments (0x9e180 : word) = Some W_9d4fc.
Proof. vm_refl. Qed.
Lemma D_9d4fc : decode_any W_9d4fc = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d500 : bv 32 := 0x02000813.
Lemma F_9d500 : fetch_word Asan.M.loaded_segments (0x9e184 : word) = Some W_9d500.
Proof. vm_refl. Qed.
Lemma D_9d500 : decode_any W_9d500 = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d504 : bv 32 := 0x01878793.
Lemma F_9d504 : fetch_word Asan.M.loaded_segments (0x9e188 : word) = Some W_9d504.
Proof. vm_refl. Qed.
Lemma D_9d504 : decode_any W_9d504 = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d508 : bv 32 := 0x40f70733.
Lemma F_9d508 : fetch_word Asan.M.loaded_segments (0x9e18c : word) = Some W_9d508.
Proof. vm_refl. Qed.
Lemma D_9d508 : decode_any W_9d508 = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d50c : bv 32 := 0xfec6a223.
Lemma F_9d50c : fetch_word Asan.M.loaded_segments (0x9e190 : word) = Some W_9d50c.
Proof. vm_refl. Qed.
Lemma D_9d50c : decode_any W_9d50c = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d510 : bv 32 := 0xfec6a423.
Lemma F_9d510 : fetch_word Asan.M.loaded_segments (0x9e194 : word) = Some W_9d510.
Proof. vm_refl. Qed.
Lemma D_9d510 : decode_any W_9d510 = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d514 : bv 32 := 0xfec6a623.
Lemma F_9d514 : fetch_word Asan.M.loaded_segments (0x9e198 : word) = Some W_9d514.
Proof. vm_refl. Qed.
Lemma D_9d514 : decode_any W_9d514 = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d518 : bv 32 := 0xfec6a823.
Lemma F_9d518 : fetch_word Asan.M.loaded_segments (0x9e19c : word) = Some W_9d518.
Proof. vm_refl. Qed.
Lemma D_9d518 : decode_any W_9d518 = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d51c : bv 32 := 0x03076a63.
Lemma F_9d51c : fetch_word Asan.M.loaded_segments (0x9e1a0 : word) = Some W_9d51c.
Proof. vm_refl. Qed.
Lemma D_9d51c : decode_any W_9d51c = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d520 : bv 32 := 0x02061613.
Lemma F_9d520 : fetch_word Asan.M.loaded_segments (0x9e1a4 : word) = Some W_9d520.
Proof. vm_refl. Qed.
Lemma D_9d520 : decode_any W_9d520 = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d524 : bv 32 := 0x00f585b3.
Lemma F_9d524 : fetch_word Asan.M.loaded_segments (0x9e1a8 : word) = Some W_9d524.
Proof. vm_refl. Qed.
Lemma D_9d524 : decode_any W_9d524 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d528 : bv 32 := 0x02065693.
Lemma F_9d528 : fetch_word Asan.M.loaded_segments (0x9e1ac : word) = Some W_9d528.
Proof. vm_refl. Qed.
Lemma D_9d528 : decode_any W_9d528 = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d52c : bv 32 := 0x00d66633.
Lemma F_9d52c : fetch_word Asan.M.loaded_segments (0x9e1b0 : word) = Some W_9d52c.
Proof. vm_refl. Qed.
Lemma D_9d52c : decode_any W_9d52c = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d530 : bv 32 := 0x01f00693.
Lemma F_9d530 : fetch_word Asan.M.loaded_segments (0x9e1b4 : word) = Some W_9d530.
Proof. vm_refl. Qed.
Lemma D_9d530 : decode_any W_9d530 = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d534 : bv 32 := 0x00c5b023.
Lemma F_9d534 : fetch_word Asan.M.loaded_segments (0x9e1b8 : word) = Some W_9d534.
Proof. vm_refl. Qed.
Lemma D_9d534 : decode_any W_9d534 = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d538 : bv 32 := 0x00c5b423.
Lemma F_9d538 : fetch_word Asan.M.loaded_segments (0x9e1bc : word) = Some W_9d538.
Proof. vm_refl. Qed.
Lemma D_9d538 : decode_any W_9d538 = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d53c : bv 32 := 0x00c5b823.
Lemma F_9d53c : fetch_word Asan.M.loaded_segments (0x9e1c0 : word) = Some W_9d53c.
Proof. vm_refl. Qed.
Lemma D_9d53c : decode_any W_9d53c = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d540 : bv 32 := 0x00c5bc23.
Lemma F_9d540 : fetch_word Asan.M.loaded_segments (0x9e1c4 : word) = Some W_9d540.
Proof. vm_refl. Qed.
Lemma D_9d540 : decode_any W_9d540 = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d544 : bv 32 := 0xfe070713.
Lemma F_9d544 : fetch_word Asan.M.loaded_segments (0x9e1c8 : word) = Some W_9d544.
Proof. vm_refl. Qed.
Lemma D_9d544 : decode_any W_9d544 = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d548 : bv 32 := 0x02058593.
Lemma F_9d548 : fetch_word Asan.M.loaded_segments (0x9e1cc : word) = Some W_9d548.
Proof. vm_refl. Qed.
Lemma D_9d548 : decode_any W_9d548 = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d54c : bv 32 := 0xfee6e4e3.
Lemma F_9d54c : fetch_word Asan.M.loaded_segments (0x9e1d0 : word) = Some W_9d54c.
Proof. vm_refl. Qed.
Lemma D_9d54c : decode_any W_9d54c = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9d550 : bv 32 := 0x00008067.
Lemma F_9d550 : fetch_word Asan.M.loaded_segments (0x9e1d4 : word) = Some W_9d550.
Proof. vm_refl. Qed.
Lemma D_9d550 : decode_any W_9d550 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.


(* [comment removed for export] *)
Abbreviation MSEGS := Asan.M.loaded_segments.
Definition ms_base : Z := 0x9e0e0%Z.
Definition Fo_000 := F_9d45c.
Definition Do_000 := D_9d45c.
Definition Fo_004 := F_9d460.
Definition Do_004 := D_9d460.
Definition Fo_008 := F_9d464.
Definition Do_008 := D_9d464.
Definition Fo_00c := F_9d468.
Definition Do_00c := D_9d468.
Definition Fo_010 := F_9d46c.
Definition Do_010 := D_9d46c.
Definition Fo_014 := F_9d470.
Definition Do_014 := D_9d470.
Definition Fo_018 := F_9d474.
Definition Do_018 := D_9d474.
Definition Fo_01c := F_9d478.
Definition Do_01c := D_9d478.
Definition Fo_020 := F_9d47c.
Definition Do_020 := D_9d47c.
Definition Fo_024 := F_9d480.
Definition Do_024 := D_9d480.
Definition Fo_028 := F_9d484.
Definition Do_028 := D_9d484.
Definition Fo_02c := F_9d488.
Definition Do_02c := D_9d488.
Definition Fo_030 := F_9d48c.
Definition Do_030 := D_9d48c.
Definition Fo_034 := F_9d490.
Definition Do_034 := D_9d490.
Definition Fo_038 := F_9d494.
Definition Do_038 := D_9d494.
Definition Fo_03c := F_9d498.
Definition Do_03c := D_9d498.
Definition Fo_040 := F_9d49c.
Definition Do_040 := D_9d49c.
Definition Fo_044 := F_9d4a0.
Definition Do_044 := D_9d4a0.
Definition Fo_048 := F_9d4a4.
Definition Do_048 := D_9d4a4.
Definition Fo_04c := F_9d4a8.
Definition Do_04c := D_9d4a8.
Definition Fo_050 := F_9d4ac.
Definition Do_050 := D_9d4ac.
Definition Fo_054 := F_9d4b0.
Definition Do_054 := D_9d4b0.
Definition Fo_058 := F_9d4b4.
Definition Do_058 := D_9d4b4.
Definition Fo_05c := F_9d4b8.
Definition Do_05c := D_9d4b8.
Definition Fo_060 := F_9d4bc.
Definition Do_060 := D_9d4bc.
Definition Fo_064 := F_9d4c0.
Definition Do_064 := D_9d4c0.
Definition Fo_068 := F_9d4c4.
Definition Do_068 := D_9d4c4.
Definition Fo_06c := F_9d4c8.
Definition Do_06c := D_9d4c8.
Definition Fo_070 := F_9d4cc.
Definition Do_070 := D_9d4cc.
Definition Fo_074 := F_9d4d0.
Definition Do_074 := D_9d4d0.
Definition Fo_078 := F_9d4d4.
Definition Do_078 := D_9d4d4.
Definition Fo_07c := F_9d4d8.
Definition Do_07c := D_9d4d8.
Definition Fo_080 := F_9d4dc.
Definition Do_080 := D_9d4dc.
Definition Fo_084 := F_9d4e0.
Definition Do_084 := D_9d4e0.
Definition Fo_088 := F_9d4e4.
Definition Do_088 := D_9d4e4.
Definition Fo_08c := F_9d4e8.
Definition Do_08c := D_9d4e8.
Definition Fo_090 := F_9d4ec.
Definition Do_090 := D_9d4ec.
Definition Fo_094 := F_9d4f0.
Definition Do_094 := D_9d4f0.
Definition Fo_098 := F_9d4f4.
Definition Do_098 := D_9d4f4.
Definition Fo_09c := F_9d4f8.
Definition Do_09c := D_9d4f8.
Definition Fo_0a0 := F_9d4fc.
Definition Do_0a0 := D_9d4fc.
Definition Fo_0a4 := F_9d500.
Definition Do_0a4 := D_9d500.
Definition Fo_0a8 := F_9d504.
Definition Do_0a8 := D_9d504.
Definition Fo_0ac := F_9d508.
Definition Do_0ac := D_9d508.
Definition Fo_0b0 := F_9d50c.
Definition Do_0b0 := D_9d50c.
Definition Fo_0b4 := F_9d510.
Definition Do_0b4 := D_9d510.
Definition Fo_0b8 := F_9d514.
Definition Do_0b8 := D_9d514.
Definition Fo_0bc := F_9d518.
Definition Do_0bc := D_9d518.
Definition Fo_0c0 := F_9d51c.
Definition Do_0c0 := D_9d51c.
Definition Fo_0c4 := F_9d520.
Definition Do_0c4 := D_9d520.
Definition Fo_0c8 := F_9d524.
Definition Do_0c8 := D_9d524.
Definition Fo_0cc := F_9d528.
Definition Do_0cc := D_9d528.
Definition Fo_0d0 := F_9d52c.
Definition Do_0d0 := D_9d52c.
Definition Fo_0d4 := F_9d530.
Definition Do_0d4 := D_9d530.
Definition Fo_0d8 := F_9d534.
Definition Do_0d8 := D_9d534.
Definition Fo_0dc := F_9d538.
Definition Do_0dc := D_9d538.
Definition Fo_0e0 := F_9d53c.
Definition Do_0e0 := D_9d53c.
Definition Fo_0e4 := F_9d540.
Definition Do_0e4 := D_9d540.
Definition Fo_0e8 := F_9d544.
Definition Do_0e8 := D_9d544.
Definition Fo_0ec := F_9d548.
Definition Do_0ec := D_9d548.
Definition Fo_0f0 := F_9d54c.
Definition Do_0f0 := D_9d54c.
Definition Fo_0f4 := F_9d550.
Definition Do_0f4 := D_9d550.
