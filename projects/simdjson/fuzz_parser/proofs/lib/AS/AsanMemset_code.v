(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.simdjson.fuzz_parser.images Require Import Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_fd360 : bv 32 := 0x0e060a63.
Lemma F_fd360 : fetch_word Asan.M.loaded_segments (0xfd51c : word) = Some W_fd360.
Proof. vm_refl. Qed.
Lemma D_fd360 : decode_any W_fd360 = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd364 : bv 32 := 0x00b50023.
Lemma F_fd364 : fetch_word Asan.M.loaded_segments (0xfd520 : word) = Some W_fd364.
Proof. vm_refl. Qed.
Lemma D_fd364 : decode_any W_fd364 = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd368 : bv 32 := 0x00c506b3.
Lemma F_fd368 : fetch_word Asan.M.loaded_segments (0xfd524 : word) = Some W_fd368.
Proof. vm_refl. Qed.
Lemma D_fd368 : decode_any W_fd368 = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd36c : bv 32 := 0x00300713.
Lemma F_fd36c : fetch_word Asan.M.loaded_segments (0xfd528 : word) = Some W_fd36c.
Proof. vm_refl. Qed.
Lemma D_fd36c : decode_any W_fd36c = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd370 : bv 32 := 0xfeb68fa3.
Lemma F_fd370 : fetch_word Asan.M.loaded_segments (0xfd52c : word) = Some W_fd370.
Proof. vm_refl. Qed.
Lemma D_fd370 : decode_any W_fd370 = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd374 : bv 32 := 0x0ee66063.
Lemma F_fd374 : fetch_word Asan.M.loaded_segments (0xfd530 : word) = Some W_fd374.
Proof. vm_refl. Qed.
Lemma D_fd374 : decode_any W_fd374 = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd378 : bv 32 := 0x00b500a3.
Lemma F_fd378 : fetch_word Asan.M.loaded_segments (0xfd534 : word) = Some W_fd378.
Proof. vm_refl. Qed.
Lemma D_fd378 : decode_any W_fd378 = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd37c : bv 32 := 0x00b50123.
Lemma F_fd37c : fetch_word Asan.M.loaded_segments (0xfd538 : word) = Some W_fd37c.
Proof. vm_refl. Qed.
Lemma D_fd37c : decode_any W_fd37c = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd380 : bv 32 := 0x00700713.
Lemma F_fd380 : fetch_word Asan.M.loaded_segments (0xfd53c : word) = Some W_fd380.
Proof. vm_refl. Qed.
Lemma D_fd380 : decode_any W_fd380 = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd384 : bv 32 := 0xfeb68ea3.
Lemma F_fd384 : fetch_word Asan.M.loaded_segments (0xfd540 : word) = Some W_fd384.
Proof. vm_refl. Qed.
Lemma D_fd384 : decode_any W_fd384 = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd388 : bv 32 := 0xfeb68f23.
Lemma F_fd388 : fetch_word Asan.M.loaded_segments (0xfd544 : word) = Some W_fd388.
Proof. vm_refl. Qed.
Lemma D_fd388 : decode_any W_fd388 = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd38c : bv 32 := 0x0ce66463.
Lemma F_fd38c : fetch_word Asan.M.loaded_segments (0xfd548 : word) = Some W_fd38c.
Proof. vm_refl. Qed.
Lemma D_fd38c : decode_any W_fd38c = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd390 : bv 32 := 0x00b501a3.
Lemma F_fd390 : fetch_word Asan.M.loaded_segments (0xfd54c : word) = Some W_fd390.
Proof. vm_refl. Qed.
Lemma D_fd390 : decode_any W_fd390 = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd394 : bv 32 := 0x00900793.
Lemma F_fd394 : fetch_word Asan.M.loaded_segments (0xfd550 : word) = Some W_fd394.
Proof. vm_refl. Qed.
Lemma D_fd394 : decode_any W_fd394 = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd398 : bv 32 := 0xfeb68e23.
Lemma F_fd398 : fetch_word Asan.M.loaded_segments (0xfd554 : word) = Some W_fd398.
Proof. vm_refl. Qed.
Lemma D_fd398 : decode_any W_fd398 = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd39c : bv 32 := 0x0af66c63.
Lemma F_fd39c : fetch_word Asan.M.loaded_segments (0xfd558 : word) = Some W_fd39c.
Proof. vm_refl. Qed.
Lemma D_fd39c : decode_any W_fd39c = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd3a0 : bv 32 := 0x40a006bb.
Lemma F_fd3a0 : fetch_word Asan.M.loaded_segments (0xfd55c : word) = Some W_fd3a0.
Proof. vm_refl. Qed.
Lemma D_fd3a0 : decode_any W_fd3a0 = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd3a4 : bv 32 := 0x03859813.
Lemma F_fd3a4 : fetch_word Asan.M.loaded_segments (0xfd560 : word) = Some W_fd3a4.
Proof. vm_refl. Qed.
Lemma D_fd3a4 : decode_any W_fd3a4 = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd3a8 : bv 32 := 0x101015b7.
Lemma F_fd3a8 : fetch_word Asan.M.loaded_segments (0xfd564 : word) = Some W_fd3a8.
Proof. vm_refl. Qed.
Lemma D_fd3a8 : decode_any W_fd3a8 = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd3ac : bv 32 := 0x0036f693.
Lemma F_fd3ac : fetch_word Asan.M.loaded_segments (0xfd568 : word) = Some W_fd3ac.
Proof. vm_refl. Qed.
Lemma D_fd3ac : decode_any W_fd3ac = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd3b0 : bv 32 := 0x00459713.
Lemma F_fd3b0 : fetch_word Asan.M.loaded_segments (0xfd56c : word) = Some W_fd3b0.
Proof. vm_refl. Qed.
Lemma D_fd3b0 : decode_any W_fd3b0 = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd3b4 : bv 32 := 0x40d60633.
Lemma F_fd3b4 : fetch_word Asan.M.loaded_segments (0xfd570 : word) = Some W_fd3b4.
Proof. vm_refl. Qed.
Lemma D_fd3b4 : decode_any W_fd3b4 = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd3b8 : bv 32 := 0x00d505b3.
Lemma F_fd3b8 : fetch_word Asan.M.loaded_segments (0xfd574 : word) = Some W_fd3b8.
Proof. vm_refl. Qed.
Lemma D_fd3b8 : decode_any W_fd3b8 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd3bc : bv 32 := 0x10070693.
Lemma F_fd3bc : fetch_word Asan.M.loaded_segments (0xfd578 : word) = Some W_fd3bc.
Proof. vm_refl. Qed.
Lemma D_fd3bc : decode_any W_fd3bc = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd3c0 : bv 32 := 0xffc67713.
Lemma F_fd3c0 : fetch_word Asan.M.loaded_segments (0xfd57c : word) = Some W_fd3c0.
Proof. vm_refl. Qed.
Lemma D_fd3c0 : decode_any W_fd3c0 = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd3c4 : bv 32 := 0x02d83633.
Lemma F_fd3c4 : fetch_word Asan.M.loaded_segments (0xfd580 : word) = Some W_fd3c4.
Proof. vm_refl. Qed.
Lemma D_fd3c4 : decode_any W_fd3c4 = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd3c8 : bv 32 := 0x00c5a023.
Lemma F_fd3c8 : fetch_word Asan.M.loaded_segments (0xfd584 : word) = Some W_fd3c8.
Proof. vm_refl. Qed.
Lemma D_fd3c8 : decode_any W_fd3c8 = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd3cc : bv 32 := 0x00e586b3.
Lemma F_fd3cc : fetch_word Asan.M.loaded_segments (0xfd588 : word) = Some W_fd3cc.
Proof. vm_refl. Qed.
Lemma D_fd3cc : decode_any W_fd3cc = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd3d0 : bv 32 := 0xfec6ae23.
Lemma F_fd3d0 : fetch_word Asan.M.loaded_segments (0xfd58c : word) = Some W_fd3d0.
Proof. vm_refl. Qed.
Lemma D_fd3d0 : decode_any W_fd3d0 = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd3d4 : bv 32 := 0x08f76063.
Lemma F_fd3d4 : fetch_word Asan.M.loaded_segments (0xfd590 : word) = Some W_fd3d4.
Proof. vm_refl. Qed.
Lemma D_fd3d4 : decode_any W_fd3d4 = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd3d8 : bv 32 := 0x00c5a223.
Lemma F_fd3d8 : fetch_word Asan.M.loaded_segments (0xfd594 : word) = Some W_fd3d8.
Proof. vm_refl. Qed.
Lemma D_fd3d8 : decode_any W_fd3d8 = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd3dc : bv 32 := 0x00c5a423.
Lemma F_fd3dc : fetch_word Asan.M.loaded_segments (0xfd598 : word) = Some W_fd3dc.
Proof. vm_refl. Qed.
Lemma D_fd3dc : decode_any W_fd3dc = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd3e0 : bv 32 := 0x01900793.
Lemma F_fd3e0 : fetch_word Asan.M.loaded_segments (0xfd59c : word) = Some W_fd3e0.
Proof. vm_refl. Qed.
Lemma D_fd3e0 : decode_any W_fd3e0 = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd3e4 : bv 32 := 0xfec6aa23.
Lemma F_fd3e4 : fetch_word Asan.M.loaded_segments (0xfd5a0 : word) = Some W_fd3e4.
Proof. vm_refl. Qed.
Lemma D_fd3e4 : decode_any W_fd3e4 = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd3e8 : bv 32 := 0xfec6ac23.
Lemma F_fd3e8 : fetch_word Asan.M.loaded_segments (0xfd5a4 : word) = Some W_fd3e8.
Proof. vm_refl. Qed.
Lemma D_fd3e8 : decode_any W_fd3e8 = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd3ec : bv 32 := 0x06f76463.
Lemma F_fd3ec : fetch_word Asan.M.loaded_segments (0xfd5a8 : word) = Some W_fd3ec.
Proof. vm_refl. Qed.
Lemma D_fd3ec : decode_any W_fd3ec = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd3f0 : bv 32 := 0x00c5a623.
Lemma F_fd3f0 : fetch_word Asan.M.loaded_segments (0xfd5ac : word) = Some W_fd3f0.
Proof. vm_refl. Qed.
Lemma D_fd3f0 : decode_any W_fd3f0 = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd3f4 : bv 32 := 0x00c5a823.
Lemma F_fd3f4 : fetch_word Asan.M.loaded_segments (0xfd5b0 : word) = Some W_fd3f4.
Proof. vm_refl. Qed.
Lemma D_fd3f4 : decode_any W_fd3f4 = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd3f8 : bv 32 := 0x00c5aa23.
Lemma F_fd3f8 : fetch_word Asan.M.loaded_segments (0xfd5b4 : word) = Some W_fd3f8.
Proof. vm_refl. Qed.
Lemma D_fd3f8 : decode_any W_fd3f8 = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd3fc : bv 32 := 0x00c5ac23.
Lemma F_fd3fc : fetch_word Asan.M.loaded_segments (0xfd5b8 : word) = Some W_fd3fc.
Proof. vm_refl. Qed.
Lemma D_fd3fc : decode_any W_fd3fc = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd400 : bv 32 := 0x0045f793.
Lemma F_fd400 : fetch_word Asan.M.loaded_segments (0xfd5bc : word) = Some W_fd400.
Proof. vm_refl. Qed.
Lemma D_fd400 : decode_any W_fd400 = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd404 : bv 32 := 0x02000813.
Lemma F_fd404 : fetch_word Asan.M.loaded_segments (0xfd5c0 : word) = Some W_fd404.
Proof. vm_refl. Qed.
Lemma D_fd404 : decode_any W_fd404 = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd408 : bv 32 := 0x01878793.
Lemma F_fd408 : fetch_word Asan.M.loaded_segments (0xfd5c4 : word) = Some W_fd408.
Proof. vm_refl. Qed.
Lemma D_fd408 : decode_any W_fd408 = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd40c : bv 32 := 0x40f70733.
Lemma F_fd40c : fetch_word Asan.M.loaded_segments (0xfd5c8 : word) = Some W_fd40c.
Proof. vm_refl. Qed.
Lemma D_fd40c : decode_any W_fd40c = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd410 : bv 32 := 0xfec6a223.
Lemma F_fd410 : fetch_word Asan.M.loaded_segments (0xfd5cc : word) = Some W_fd410.
Proof. vm_refl. Qed.
Lemma D_fd410 : decode_any W_fd410 = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd414 : bv 32 := 0xfec6a423.
Lemma F_fd414 : fetch_word Asan.M.loaded_segments (0xfd5d0 : word) = Some W_fd414.
Proof. vm_refl. Qed.
Lemma D_fd414 : decode_any W_fd414 = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd418 : bv 32 := 0xfec6a623.
Lemma F_fd418 : fetch_word Asan.M.loaded_segments (0xfd5d4 : word) = Some W_fd418.
Proof. vm_refl. Qed.
Lemma D_fd418 : decode_any W_fd418 = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd41c : bv 32 := 0xfec6a823.
Lemma F_fd41c : fetch_word Asan.M.loaded_segments (0xfd5d8 : word) = Some W_fd41c.
Proof. vm_refl. Qed.
Lemma D_fd41c : decode_any W_fd41c = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd420 : bv 32 := 0x03076a63.
Lemma F_fd420 : fetch_word Asan.M.loaded_segments (0xfd5dc : word) = Some W_fd420.
Proof. vm_refl. Qed.
Lemma D_fd420 : decode_any W_fd420 = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd424 : bv 32 := 0x02061613.
Lemma F_fd424 : fetch_word Asan.M.loaded_segments (0xfd5e0 : word) = Some W_fd424.
Proof. vm_refl. Qed.
Lemma D_fd424 : decode_any W_fd424 = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd428 : bv 32 := 0x00f585b3.
Lemma F_fd428 : fetch_word Asan.M.loaded_segments (0xfd5e4 : word) = Some W_fd428.
Proof. vm_refl. Qed.
Lemma D_fd428 : decode_any W_fd428 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd42c : bv 32 := 0x02065693.
Lemma F_fd42c : fetch_word Asan.M.loaded_segments (0xfd5e8 : word) = Some W_fd42c.
Proof. vm_refl. Qed.
Lemma D_fd42c : decode_any W_fd42c = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd430 : bv 32 := 0x00d66633.
Lemma F_fd430 : fetch_word Asan.M.loaded_segments (0xfd5ec : word) = Some W_fd430.
Proof. vm_refl. Qed.
Lemma D_fd430 : decode_any W_fd430 = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd434 : bv 32 := 0x01f00693.
Lemma F_fd434 : fetch_word Asan.M.loaded_segments (0xfd5f0 : word) = Some W_fd434.
Proof. vm_refl. Qed.
Lemma D_fd434 : decode_any W_fd434 = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd438 : bv 32 := 0x00c5b023.
Lemma F_fd438 : fetch_word Asan.M.loaded_segments (0xfd5f4 : word) = Some W_fd438.
Proof. vm_refl. Qed.
Lemma D_fd438 : decode_any W_fd438 = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd43c : bv 32 := 0x00c5b423.
Lemma F_fd43c : fetch_word Asan.M.loaded_segments (0xfd5f8 : word) = Some W_fd43c.
Proof. vm_refl. Qed.
Lemma D_fd43c : decode_any W_fd43c = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd440 : bv 32 := 0x00c5b823.
Lemma F_fd440 : fetch_word Asan.M.loaded_segments (0xfd5fc : word) = Some W_fd440.
Proof. vm_refl. Qed.
Lemma D_fd440 : decode_any W_fd440 = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd444 : bv 32 := 0x00c5bc23.
Lemma F_fd444 : fetch_word Asan.M.loaded_segments (0xfd600 : word) = Some W_fd444.
Proof. vm_refl. Qed.
Lemma D_fd444 : decode_any W_fd444 = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd448 : bv 32 := 0xfe070713.
Lemma F_fd448 : fetch_word Asan.M.loaded_segments (0xfd604 : word) = Some W_fd448.
Proof. vm_refl. Qed.
Lemma D_fd448 : decode_any W_fd448 = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd44c : bv 32 := 0x02058593.
Lemma F_fd44c : fetch_word Asan.M.loaded_segments (0xfd608 : word) = Some W_fd44c.
Proof. vm_refl. Qed.
Lemma D_fd44c : decode_any W_fd44c = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd450 : bv 32 := 0xfee6e4e3.
Lemma F_fd450 : fetch_word Asan.M.loaded_segments (0xfd60c : word) = Some W_fd450.
Proof. vm_refl. Qed.
Lemma D_fd450 : decode_any W_fd450 = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fd454 : bv 32 := 0x00008067.
Lemma F_fd454 : fetch_word Asan.M.loaded_segments (0xfd610 : word) = Some W_fd454.
Proof. vm_refl. Qed.
Lemma D_fd454 : decode_any W_fd454 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Abbreviation MSEGS := Asan.M.loaded_segments.
Definition ms_base : Z := 0xfd51c%Z.
Definition Fo_000 := F_fd360.
Definition Do_000 := D_fd360.
Definition Fo_004 := F_fd364.
Definition Do_004 := D_fd364.
Definition Fo_008 := F_fd368.
Definition Do_008 := D_fd368.
Definition Fo_00c := F_fd36c.
Definition Do_00c := D_fd36c.
Definition Fo_010 := F_fd370.
Definition Do_010 := D_fd370.
Definition Fo_014 := F_fd374.
Definition Do_014 := D_fd374.
Definition Fo_018 := F_fd378.
Definition Do_018 := D_fd378.
Definition Fo_01c := F_fd37c.
Definition Do_01c := D_fd37c.
Definition Fo_020 := F_fd380.
Definition Do_020 := D_fd380.
Definition Fo_024 := F_fd384.
Definition Do_024 := D_fd384.
Definition Fo_028 := F_fd388.
Definition Do_028 := D_fd388.
Definition Fo_02c := F_fd38c.
Definition Do_02c := D_fd38c.
Definition Fo_030 := F_fd390.
Definition Do_030 := D_fd390.
Definition Fo_034 := F_fd394.
Definition Do_034 := D_fd394.
Definition Fo_038 := F_fd398.
Definition Do_038 := D_fd398.
Definition Fo_03c := F_fd39c.
Definition Do_03c := D_fd39c.
Definition Fo_040 := F_fd3a0.
Definition Do_040 := D_fd3a0.
Definition Fo_044 := F_fd3a4.
Definition Do_044 := D_fd3a4.
Definition Fo_048 := F_fd3a8.
Definition Do_048 := D_fd3a8.
Definition Fo_04c := F_fd3ac.
Definition Do_04c := D_fd3ac.
Definition Fo_050 := F_fd3b0.
Definition Do_050 := D_fd3b0.
Definition Fo_054 := F_fd3b4.
Definition Do_054 := D_fd3b4.
Definition Fo_058 := F_fd3b8.
Definition Do_058 := D_fd3b8.
Definition Fo_05c := F_fd3bc.
Definition Do_05c := D_fd3bc.
Definition Fo_060 := F_fd3c0.
Definition Do_060 := D_fd3c0.
Definition Fo_064 := F_fd3c4.
Definition Do_064 := D_fd3c4.
Definition Fo_068 := F_fd3c8.
Definition Do_068 := D_fd3c8.
Definition Fo_06c := F_fd3cc.
Definition Do_06c := D_fd3cc.
Definition Fo_070 := F_fd3d0.
Definition Do_070 := D_fd3d0.
Definition Fo_074 := F_fd3d4.
Definition Do_074 := D_fd3d4.
Definition Fo_078 := F_fd3d8.
Definition Do_078 := D_fd3d8.
Definition Fo_07c := F_fd3dc.
Definition Do_07c := D_fd3dc.
Definition Fo_080 := F_fd3e0.
Definition Do_080 := D_fd3e0.
Definition Fo_084 := F_fd3e4.
Definition Do_084 := D_fd3e4.
Definition Fo_088 := F_fd3e8.
Definition Do_088 := D_fd3e8.
Definition Fo_08c := F_fd3ec.
Definition Do_08c := D_fd3ec.
Definition Fo_090 := F_fd3f0.
Definition Do_090 := D_fd3f0.
Definition Fo_094 := F_fd3f4.
Definition Do_094 := D_fd3f4.
Definition Fo_098 := F_fd3f8.
Definition Do_098 := D_fd3f8.
Definition Fo_09c := F_fd3fc.
Definition Do_09c := D_fd3fc.
Definition Fo_0a0 := F_fd400.
Definition Do_0a0 := D_fd400.
Definition Fo_0a4 := F_fd404.
Definition Do_0a4 := D_fd404.
Definition Fo_0a8 := F_fd408.
Definition Do_0a8 := D_fd408.
Definition Fo_0ac := F_fd40c.
Definition Do_0ac := D_fd40c.
Definition Fo_0b0 := F_fd410.
Definition Do_0b0 := D_fd410.
Definition Fo_0b4 := F_fd414.
Definition Do_0b4 := D_fd414.
Definition Fo_0b8 := F_fd418.
Definition Do_0b8 := D_fd418.
Definition Fo_0bc := F_fd41c.
Definition Do_0bc := D_fd41c.
Definition Fo_0c0 := F_fd420.
Definition Do_0c0 := D_fd420.
Definition Fo_0c4 := F_fd424.
Definition Do_0c4 := D_fd424.
Definition Fo_0c8 := F_fd428.
Definition Do_0c8 := D_fd428.
Definition Fo_0cc := F_fd42c.
Definition Do_0cc := D_fd42c.
Definition Fo_0d0 := F_fd430.
Definition Do_0d0 := D_fd430.
Definition Fo_0d4 := F_fd434.
Definition Do_0d4 := D_fd434.
Definition Fo_0d8 := F_fd438.
Definition Do_0d8 := D_fd438.
Definition Fo_0dc := F_fd43c.
Definition Do_0dc := D_fd43c.
Definition Fo_0e0 := F_fd440.
Definition Do_0e0 := D_fd440.
Definition Fo_0e4 := F_fd444.
Definition Do_0e4 := D_fd444.
Definition Fo_0e8 := F_fd448.
Definition Do_0e8 := D_fd448.
Definition Fo_0ec := F_fd44c.
Definition Do_0ec := D_fd44c.
Definition Fo_0f0 := F_fd450.
Definition Do_0f0 := D_fd450.
Definition Fo_0f4 := F_fd454.
Definition Do_0f4 := D_fd454.
