(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
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
From OssFuzzTheorems.zstd.simple_decompress.images Require Import Asan.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_c52cc : bv 32 := 0x0e060a63.
Lemma F_c52cc : fetch_word Asan.M.loaded_segments (0xc0a3c : word) = Some W_c52cc.
Proof. vm_refl. Qed.
Lemma D_c52cc : decode_any W_c52cc = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c52d0 : bv 32 := 0x00b50023.
Lemma F_c52d0 : fetch_word Asan.M.loaded_segments (0xc0a40 : word) = Some W_c52d0.
Proof. vm_refl. Qed.
Lemma D_c52d0 : decode_any W_c52d0 = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c52d4 : bv 32 := 0x00c506b3.
Lemma F_c52d4 : fetch_word Asan.M.loaded_segments (0xc0a44 : word) = Some W_c52d4.
Proof. vm_refl. Qed.
Lemma D_c52d4 : decode_any W_c52d4 = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c52d8 : bv 32 := 0x00300713.
Lemma F_c52d8 : fetch_word Asan.M.loaded_segments (0xc0a48 : word) = Some W_c52d8.
Proof. vm_refl. Qed.
Lemma D_c52d8 : decode_any W_c52d8 = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c52dc : bv 32 := 0xfeb68fa3.
Lemma F_c52dc : fetch_word Asan.M.loaded_segments (0xc0a4c : word) = Some W_c52dc.
Proof. vm_refl. Qed.
Lemma D_c52dc : decode_any W_c52dc = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c52e0 : bv 32 := 0x0ee66063.
Lemma F_c52e0 : fetch_word Asan.M.loaded_segments (0xc0a50 : word) = Some W_c52e0.
Proof. vm_refl. Qed.
Lemma D_c52e0 : decode_any W_c52e0 = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c52e4 : bv 32 := 0x00b500a3.
Lemma F_c52e4 : fetch_word Asan.M.loaded_segments (0xc0a54 : word) = Some W_c52e4.
Proof. vm_refl. Qed.
Lemma D_c52e4 : decode_any W_c52e4 = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c52e8 : bv 32 := 0x00b50123.
Lemma F_c52e8 : fetch_word Asan.M.loaded_segments (0xc0a58 : word) = Some W_c52e8.
Proof. vm_refl. Qed.
Lemma D_c52e8 : decode_any W_c52e8 = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c52ec : bv 32 := 0x00700713.
Lemma F_c52ec : fetch_word Asan.M.loaded_segments (0xc0a5c : word) = Some W_c52ec.
Proof. vm_refl. Qed.
Lemma D_c52ec : decode_any W_c52ec = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c52f0 : bv 32 := 0xfeb68ea3.
Lemma F_c52f0 : fetch_word Asan.M.loaded_segments (0xc0a60 : word) = Some W_c52f0.
Proof. vm_refl. Qed.
Lemma D_c52f0 : decode_any W_c52f0 = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c52f4 : bv 32 := 0xfeb68f23.
Lemma F_c52f4 : fetch_word Asan.M.loaded_segments (0xc0a64 : word) = Some W_c52f4.
Proof. vm_refl. Qed.
Lemma D_c52f4 : decode_any W_c52f4 = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c52f8 : bv 32 := 0x0ce66463.
Lemma F_c52f8 : fetch_word Asan.M.loaded_segments (0xc0a68 : word) = Some W_c52f8.
Proof. vm_refl. Qed.
Lemma D_c52f8 : decode_any W_c52f8 = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c52fc : bv 32 := 0x00b501a3.
Lemma F_c52fc : fetch_word Asan.M.loaded_segments (0xc0a6c : word) = Some W_c52fc.
Proof. vm_refl. Qed.
Lemma D_c52fc : decode_any W_c52fc = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5300 : bv 32 := 0x00900793.
Lemma F_c5300 : fetch_word Asan.M.loaded_segments (0xc0a70 : word) = Some W_c5300.
Proof. vm_refl. Qed.
Lemma D_c5300 : decode_any W_c5300 = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5304 : bv 32 := 0xfeb68e23.
Lemma F_c5304 : fetch_word Asan.M.loaded_segments (0xc0a74 : word) = Some W_c5304.
Proof. vm_refl. Qed.
Lemma D_c5304 : decode_any W_c5304 = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5308 : bv 32 := 0x0af66c63.
Lemma F_c5308 : fetch_word Asan.M.loaded_segments (0xc0a78 : word) = Some W_c5308.
Proof. vm_refl. Qed.
Lemma D_c5308 : decode_any W_c5308 = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c530c : bv 32 := 0x40a006bb.
Lemma F_c530c : fetch_word Asan.M.loaded_segments (0xc0a7c : word) = Some W_c530c.
Proof. vm_refl. Qed.
Lemma D_c530c : decode_any W_c530c = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5310 : bv 32 := 0x03859813.
Lemma F_c5310 : fetch_word Asan.M.loaded_segments (0xc0a80 : word) = Some W_c5310.
Proof. vm_refl. Qed.
Lemma D_c5310 : decode_any W_c5310 = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5314 : bv 32 := 0x101015b7.
Lemma F_c5314 : fetch_word Asan.M.loaded_segments (0xc0a84 : word) = Some W_c5314.
Proof. vm_refl. Qed.
Lemma D_c5314 : decode_any W_c5314 = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5318 : bv 32 := 0x0036f693.
Lemma F_c5318 : fetch_word Asan.M.loaded_segments (0xc0a88 : word) = Some W_c5318.
Proof. vm_refl. Qed.
Lemma D_c5318 : decode_any W_c5318 = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c531c : bv 32 := 0x00459713.
Lemma F_c531c : fetch_word Asan.M.loaded_segments (0xc0a8c : word) = Some W_c531c.
Proof. vm_refl. Qed.
Lemma D_c531c : decode_any W_c531c = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5320 : bv 32 := 0x40d60633.
Lemma F_c5320 : fetch_word Asan.M.loaded_segments (0xc0a90 : word) = Some W_c5320.
Proof. vm_refl. Qed.
Lemma D_c5320 : decode_any W_c5320 = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5324 : bv 32 := 0x00d505b3.
Lemma F_c5324 : fetch_word Asan.M.loaded_segments (0xc0a94 : word) = Some W_c5324.
Proof. vm_refl. Qed.
Lemma D_c5324 : decode_any W_c5324 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5328 : bv 32 := 0x10070693.
Lemma F_c5328 : fetch_word Asan.M.loaded_segments (0xc0a98 : word) = Some W_c5328.
Proof. vm_refl. Qed.
Lemma D_c5328 : decode_any W_c5328 = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c532c : bv 32 := 0xffc67713.
Lemma F_c532c : fetch_word Asan.M.loaded_segments (0xc0a9c : word) = Some W_c532c.
Proof. vm_refl. Qed.
Lemma D_c532c : decode_any W_c532c = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5330 : bv 32 := 0x02d83633.
Lemma F_c5330 : fetch_word Asan.M.loaded_segments (0xc0aa0 : word) = Some W_c5330.
Proof. vm_refl. Qed.
Lemma D_c5330 : decode_any W_c5330 = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5334 : bv 32 := 0x00c5a023.
Lemma F_c5334 : fetch_word Asan.M.loaded_segments (0xc0aa4 : word) = Some W_c5334.
Proof. vm_refl. Qed.
Lemma D_c5334 : decode_any W_c5334 = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5338 : bv 32 := 0x00e586b3.
Lemma F_c5338 : fetch_word Asan.M.loaded_segments (0xc0aa8 : word) = Some W_c5338.
Proof. vm_refl. Qed.
Lemma D_c5338 : decode_any W_c5338 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c533c : bv 32 := 0xfec6ae23.
Lemma F_c533c : fetch_word Asan.M.loaded_segments (0xc0aac : word) = Some W_c533c.
Proof. vm_refl. Qed.
Lemma D_c533c : decode_any W_c533c = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5340 : bv 32 := 0x08f76063.
Lemma F_c5340 : fetch_word Asan.M.loaded_segments (0xc0ab0 : word) = Some W_c5340.
Proof. vm_refl. Qed.
Lemma D_c5340 : decode_any W_c5340 = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5344 : bv 32 := 0x00c5a223.
Lemma F_c5344 : fetch_word Asan.M.loaded_segments (0xc0ab4 : word) = Some W_c5344.
Proof. vm_refl. Qed.
Lemma D_c5344 : decode_any W_c5344 = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5348 : bv 32 := 0x00c5a423.
Lemma F_c5348 : fetch_word Asan.M.loaded_segments (0xc0ab8 : word) = Some W_c5348.
Proof. vm_refl. Qed.
Lemma D_c5348 : decode_any W_c5348 = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c534c : bv 32 := 0x01900793.
Lemma F_c534c : fetch_word Asan.M.loaded_segments (0xc0abc : word) = Some W_c534c.
Proof. vm_refl. Qed.
Lemma D_c534c : decode_any W_c534c = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5350 : bv 32 := 0xfec6aa23.
Lemma F_c5350 : fetch_word Asan.M.loaded_segments (0xc0ac0 : word) = Some W_c5350.
Proof. vm_refl. Qed.
Lemma D_c5350 : decode_any W_c5350 = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5354 : bv 32 := 0xfec6ac23.
Lemma F_c5354 : fetch_word Asan.M.loaded_segments (0xc0ac4 : word) = Some W_c5354.
Proof. vm_refl. Qed.
Lemma D_c5354 : decode_any W_c5354 = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5358 : bv 32 := 0x06f76463.
Lemma F_c5358 : fetch_word Asan.M.loaded_segments (0xc0ac8 : word) = Some W_c5358.
Proof. vm_refl. Qed.
Lemma D_c5358 : decode_any W_c5358 = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c535c : bv 32 := 0x00c5a623.
Lemma F_c535c : fetch_word Asan.M.loaded_segments (0xc0acc : word) = Some W_c535c.
Proof. vm_refl. Qed.
Lemma D_c535c : decode_any W_c535c = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5360 : bv 32 := 0x00c5a823.
Lemma F_c5360 : fetch_word Asan.M.loaded_segments (0xc0ad0 : word) = Some W_c5360.
Proof. vm_refl. Qed.
Lemma D_c5360 : decode_any W_c5360 = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5364 : bv 32 := 0x00c5aa23.
Lemma F_c5364 : fetch_word Asan.M.loaded_segments (0xc0ad4 : word) = Some W_c5364.
Proof. vm_refl. Qed.
Lemma D_c5364 : decode_any W_c5364 = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5368 : bv 32 := 0x00c5ac23.
Lemma F_c5368 : fetch_word Asan.M.loaded_segments (0xc0ad8 : word) = Some W_c5368.
Proof. vm_refl. Qed.
Lemma D_c5368 : decode_any W_c5368 = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c536c : bv 32 := 0x0045f793.
Lemma F_c536c : fetch_word Asan.M.loaded_segments (0xc0adc : word) = Some W_c536c.
Proof. vm_refl. Qed.
Lemma D_c536c : decode_any W_c536c = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5370 : bv 32 := 0x02000813.
Lemma F_c5370 : fetch_word Asan.M.loaded_segments (0xc0ae0 : word) = Some W_c5370.
Proof. vm_refl. Qed.
Lemma D_c5370 : decode_any W_c5370 = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5374 : bv 32 := 0x01878793.
Lemma F_c5374 : fetch_word Asan.M.loaded_segments (0xc0ae4 : word) = Some W_c5374.
Proof. vm_refl. Qed.
Lemma D_c5374 : decode_any W_c5374 = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5378 : bv 32 := 0x40f70733.
Lemma F_c5378 : fetch_word Asan.M.loaded_segments (0xc0ae8 : word) = Some W_c5378.
Proof. vm_refl. Qed.
Lemma D_c5378 : decode_any W_c5378 = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c537c : bv 32 := 0xfec6a223.
Lemma F_c537c : fetch_word Asan.M.loaded_segments (0xc0aec : word) = Some W_c537c.
Proof. vm_refl. Qed.
Lemma D_c537c : decode_any W_c537c = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5380 : bv 32 := 0xfec6a423.
Lemma F_c5380 : fetch_word Asan.M.loaded_segments (0xc0af0 : word) = Some W_c5380.
Proof. vm_refl. Qed.
Lemma D_c5380 : decode_any W_c5380 = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5384 : bv 32 := 0xfec6a623.
Lemma F_c5384 : fetch_word Asan.M.loaded_segments (0xc0af4 : word) = Some W_c5384.
Proof. vm_refl. Qed.
Lemma D_c5384 : decode_any W_c5384 = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5388 : bv 32 := 0xfec6a823.
Lemma F_c5388 : fetch_word Asan.M.loaded_segments (0xc0af8 : word) = Some W_c5388.
Proof. vm_refl. Qed.
Lemma D_c5388 : decode_any W_c5388 = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c538c : bv 32 := 0x03076a63.
Lemma F_c538c : fetch_word Asan.M.loaded_segments (0xc0afc : word) = Some W_c538c.
Proof. vm_refl. Qed.
Lemma D_c538c : decode_any W_c538c = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5390 : bv 32 := 0x02061613.
Lemma F_c5390 : fetch_word Asan.M.loaded_segments (0xc0b00 : word) = Some W_c5390.
Proof. vm_refl. Qed.
Lemma D_c5390 : decode_any W_c5390 = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5394 : bv 32 := 0x00f585b3.
Lemma F_c5394 : fetch_word Asan.M.loaded_segments (0xc0b04 : word) = Some W_c5394.
Proof. vm_refl. Qed.
Lemma D_c5394 : decode_any W_c5394 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c5398 : bv 32 := 0x02065693.
Lemma F_c5398 : fetch_word Asan.M.loaded_segments (0xc0b08 : word) = Some W_c5398.
Proof. vm_refl. Qed.
Lemma D_c5398 : decode_any W_c5398 = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c539c : bv 32 := 0x00d66633.
Lemma F_c539c : fetch_word Asan.M.loaded_segments (0xc0b0c : word) = Some W_c539c.
Proof. vm_refl. Qed.
Lemma D_c539c : decode_any W_c539c = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c53a0 : bv 32 := 0x01f00693.
Lemma F_c53a0 : fetch_word Asan.M.loaded_segments (0xc0b10 : word) = Some W_c53a0.
Proof. vm_refl. Qed.
Lemma D_c53a0 : decode_any W_c53a0 = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c53a4 : bv 32 := 0x00c5b023.
Lemma F_c53a4 : fetch_word Asan.M.loaded_segments (0xc0b14 : word) = Some W_c53a4.
Proof. vm_refl. Qed.
Lemma D_c53a4 : decode_any W_c53a4 = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c53a8 : bv 32 := 0x00c5b423.
Lemma F_c53a8 : fetch_word Asan.M.loaded_segments (0xc0b18 : word) = Some W_c53a8.
Proof. vm_refl. Qed.
Lemma D_c53a8 : decode_any W_c53a8 = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c53ac : bv 32 := 0x00c5b823.
Lemma F_c53ac : fetch_word Asan.M.loaded_segments (0xc0b1c : word) = Some W_c53ac.
Proof. vm_refl. Qed.
Lemma D_c53ac : decode_any W_c53ac = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c53b0 : bv 32 := 0x00c5bc23.
Lemma F_c53b0 : fetch_word Asan.M.loaded_segments (0xc0b20 : word) = Some W_c53b0.
Proof. vm_refl. Qed.
Lemma D_c53b0 : decode_any W_c53b0 = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c53b4 : bv 32 := 0xfe070713.
Lemma F_c53b4 : fetch_word Asan.M.loaded_segments (0xc0b24 : word) = Some W_c53b4.
Proof. vm_refl. Qed.
Lemma D_c53b4 : decode_any W_c53b4 = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c53b8 : bv 32 := 0x02058593.
Lemma F_c53b8 : fetch_word Asan.M.loaded_segments (0xc0b28 : word) = Some W_c53b8.
Proof. vm_refl. Qed.
Lemma D_c53b8 : decode_any W_c53b8 = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c53bc : bv 32 := 0xfee6e4e3.
Lemma F_c53bc : fetch_word Asan.M.loaded_segments (0xc0b2c : word) = Some W_c53bc.
Proof. vm_refl. Qed.
Lemma D_c53bc : decode_any W_c53bc = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c53c0 : bv 32 := 0x00008067.
Lemma F_c53c0 : fetch_word Asan.M.loaded_segments (0xc0b30 : word) = Some W_c53c0.
Proof. vm_refl. Qed.
Lemma D_c53c0 : decode_any W_c53c0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Abbreviation MSEGS := Asan.M.loaded_segments.
Definition ms_base : Z := 0xc0a3c%Z.
Definition Fo_000 := F_c52cc.
Definition Do_000 := D_c52cc.
Definition Fo_004 := F_c52d0.
Definition Do_004 := D_c52d0.
Definition Fo_008 := F_c52d4.
Definition Do_008 := D_c52d4.
Definition Fo_00c := F_c52d8.
Definition Do_00c := D_c52d8.
Definition Fo_010 := F_c52dc.
Definition Do_010 := D_c52dc.
Definition Fo_014 := F_c52e0.
Definition Do_014 := D_c52e0.
Definition Fo_018 := F_c52e4.
Definition Do_018 := D_c52e4.
Definition Fo_01c := F_c52e8.
Definition Do_01c := D_c52e8.
Definition Fo_020 := F_c52ec.
Definition Do_020 := D_c52ec.
Definition Fo_024 := F_c52f0.
Definition Do_024 := D_c52f0.
Definition Fo_028 := F_c52f4.
Definition Do_028 := D_c52f4.
Definition Fo_02c := F_c52f8.
Definition Do_02c := D_c52f8.
Definition Fo_030 := F_c52fc.
Definition Do_030 := D_c52fc.
Definition Fo_034 := F_c5300.
Definition Do_034 := D_c5300.
Definition Fo_038 := F_c5304.
Definition Do_038 := D_c5304.
Definition Fo_03c := F_c5308.
Definition Do_03c := D_c5308.
Definition Fo_040 := F_c530c.
Definition Do_040 := D_c530c.
Definition Fo_044 := F_c5310.
Definition Do_044 := D_c5310.
Definition Fo_048 := F_c5314.
Definition Do_048 := D_c5314.
Definition Fo_04c := F_c5318.
Definition Do_04c := D_c5318.
Definition Fo_050 := F_c531c.
Definition Do_050 := D_c531c.
Definition Fo_054 := F_c5320.
Definition Do_054 := D_c5320.
Definition Fo_058 := F_c5324.
Definition Do_058 := D_c5324.
Definition Fo_05c := F_c5328.
Definition Do_05c := D_c5328.
Definition Fo_060 := F_c532c.
Definition Do_060 := D_c532c.
Definition Fo_064 := F_c5330.
Definition Do_064 := D_c5330.
Definition Fo_068 := F_c5334.
Definition Do_068 := D_c5334.
Definition Fo_06c := F_c5338.
Definition Do_06c := D_c5338.
Definition Fo_070 := F_c533c.
Definition Do_070 := D_c533c.
Definition Fo_074 := F_c5340.
Definition Do_074 := D_c5340.
Definition Fo_078 := F_c5344.
Definition Do_078 := D_c5344.
Definition Fo_07c := F_c5348.
Definition Do_07c := D_c5348.
Definition Fo_080 := F_c534c.
Definition Do_080 := D_c534c.
Definition Fo_084 := F_c5350.
Definition Do_084 := D_c5350.
Definition Fo_088 := F_c5354.
Definition Do_088 := D_c5354.
Definition Fo_08c := F_c5358.
Definition Do_08c := D_c5358.
Definition Fo_090 := F_c535c.
Definition Do_090 := D_c535c.
Definition Fo_094 := F_c5360.
Definition Do_094 := D_c5360.
Definition Fo_098 := F_c5364.
Definition Do_098 := D_c5364.
Definition Fo_09c := F_c5368.
Definition Do_09c := D_c5368.
Definition Fo_0a0 := F_c536c.
Definition Do_0a0 := D_c536c.
Definition Fo_0a4 := F_c5370.
Definition Do_0a4 := D_c5370.
Definition Fo_0a8 := F_c5374.
Definition Do_0a8 := D_c5374.
Definition Fo_0ac := F_c5378.
Definition Do_0ac := D_c5378.
Definition Fo_0b0 := F_c537c.
Definition Do_0b0 := D_c537c.
Definition Fo_0b4 := F_c5380.
Definition Do_0b4 := D_c5380.
Definition Fo_0b8 := F_c5384.
Definition Do_0b8 := D_c5384.
Definition Fo_0bc := F_c5388.
Definition Do_0bc := D_c5388.
Definition Fo_0c0 := F_c538c.
Definition Do_0c0 := D_c538c.
Definition Fo_0c4 := F_c5390.
Definition Do_0c4 := D_c5390.
Definition Fo_0c8 := F_c5394.
Definition Do_0c8 := D_c5394.
Definition Fo_0cc := F_c5398.
Definition Do_0cc := D_c5398.
Definition Fo_0d0 := F_c539c.
Definition Do_0d0 := D_c539c.
Definition Fo_0d4 := F_c53a0.
Definition Do_0d4 := D_c53a0.
Definition Fo_0d8 := F_c53a4.
Definition Do_0d8 := D_c53a4.
Definition Fo_0dc := F_c53a8.
Definition Do_0dc := D_c53a8.
Definition Fo_0e0 := F_c53ac.
Definition Do_0e0 := D_c53ac.
Definition Fo_0e4 := F_c53b0.
Definition Do_0e4 := D_c53b0.
Definition Fo_0e8 := F_c53b4.
Definition Do_0e8 := D_c53b4.
Definition Fo_0ec := F_c53b8.
Definition Do_0ec := D_c53b8.
Definition Fo_0f0 := F_c53bc.
Definition Do_0f0 := D_c53bc.
Definition Fo_0f4 := F_c53c0.
Definition Do_0f4 := D_c53c0.
