(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.skcms.iccprofile_info.images Require Import Asan.
Unset Lia Cache. Unset Nia Cache.  (* [comment removed for export] *)
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_8e960 : bv 32 := 0xfffff5b7.
Lemma F_8e960 : fetch_word Asan.M.loaded_segments (0x8e960 : word) = Some W_8e960.
Proof. vm_refl. Qed.
Lemma D_8e960 : decode_any W_8e960 = Some (Lui 11 1048575, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e964 : bv 32 := 0x0015859b.
Lemma F_8e964 : fetch_word Asan.M.loaded_segments (0x8e964 : word) = Some W_8e964.
Proof. vm_refl. Qed.
Lemma D_8e964 : decode_any W_8e964 = Some (OpImm32 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e968 : bv 32 := 0x02b56663.
Lemma F_8e968 : fetch_word Asan.M.loaded_segments (0x8e968 : word) = Some W_8e968.
Proof. vm_refl. Qed.
Lemma D_8e968 : decode_any W_8e968 = Some (Branch BC_LTU 10 11 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e96c : bv 32 := 0xff010113.
Lemma F_8e96c : fetch_word Asan.M.loaded_segments (0x8e96c : word) = Some W_8e96c.
Proof. vm_refl. Qed.
Lemma D_8e96c : decode_any W_8e96c = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e970 : bv 32 := 0x00113423.
Lemma F_8e970 : fetch_word Asan.M.loaded_segments (0x8e970 : word) = Some W_8e970.
Proof. vm_refl. Qed.
Lemma D_8e970 : decode_any W_8e970 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e974 : bv 32 := 0x00813023.
Lemma F_8e974 : fetch_word Asan.M.loaded_segments (0x8e974 : word) = Some W_8e974.
Proof. vm_refl. Qed.
Lemma D_8e974 : decode_any W_8e974 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e978 : bv 32 := 0x40a0043b.
Lemma F_8e978 : fetch_word Asan.M.loaded_segments (0x8e978 : word) = Some W_8e978.
Proof. vm_refl. Qed.
Lemma D_8e978 : decode_any W_8e978 = Some (Op32 ALU_SUB 8 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e97c : bv 32 := 0x981ff0ef.
Lemma F_8e97c : fetch_word Asan.M.loaded_segments (0x8e97c : word) = Some W_8e97c.
Proof. vm_refl. Qed.
Lemma D_8e97c : decode_any W_8e97c = Some (Jal 1 2095488, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e980 : bv 32 := 0x00852023.
Lemma F_8e980 : fetch_word Asan.M.loaded_segments (0x8e980 : word) = Some W_8e980.
Proof. vm_refl. Qed.
Lemma D_8e980 : decode_any W_8e980 = Some (Store SZ4 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e984 : bv 32 := 0xfff00513.
Lemma F_8e984 : fetch_word Asan.M.loaded_segments (0x8e984 : word) = Some W_8e984.
Proof. vm_refl. Qed.
Lemma D_8e984 : decode_any W_8e984 = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e988 : bv 32 := 0x00813083.
Lemma F_8e988 : fetch_word Asan.M.loaded_segments (0x8e988 : word) = Some W_8e988.
Proof. vm_refl. Qed.
Lemma D_8e988 : decode_any W_8e988 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e98c : bv 32 := 0x00013403.
Lemma F_8e98c : fetch_word Asan.M.loaded_segments (0x8e98c : word) = Some W_8e98c.
Proof. vm_refl. Qed.
Lemma D_8e98c : decode_any W_8e98c = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e990 : bv 32 := 0x01010113.
Lemma F_8e990 : fetch_word Asan.M.loaded_segments (0x8e990 : word) = Some W_8e990.
Proof. vm_refl. Qed.
Lemma D_8e990 : decode_any W_8e990 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8e994 : bv 32 := 0x00008067.
Lemma F_8e994 : fetch_word Asan.M.loaded_segments (0x8e994 : word) = Some W_8e994.
Proof. vm_refl. Qed.
Lemma D_8e994 : decode_any W_8e994 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93b18 : bv 32 := 0xf9010113.
Lemma F_93b18 : fetch_word Asan.M.loaded_segments (0x93b18 : word) = Some W_93b18.
Proof. vm_refl. Qed.
Lemma D_93b18 : decode_any W_93b18 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93b1c : bv 32 := 0x06113423.
Lemma F_93b1c : fetch_word Asan.M.loaded_segments (0x93b1c : word) = Some W_93b1c.
Proof. vm_refl. Qed.
Lemma D_93b1c : decode_any W_93b1c = Some (Store SZ8 2 1 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93b20 : bv 32 := 0x06813023.
Lemma F_93b20 : fetch_word Asan.M.loaded_segments (0x93b20 : word) = Some W_93b20.
Proof. vm_refl. Qed.
Lemma D_93b20 : decode_any W_93b20 = Some (Store SZ8 2 8 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93b24 : bv 32 := 0x04913c23.
Lemma F_93b24 : fetch_word Asan.M.loaded_segments (0x93b24 : word) = Some W_93b24.
Proof. vm_refl. Qed.
Lemma D_93b24 : decode_any W_93b24 = Some (Store SZ8 2 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93b28 : bv 32 := 0x05213823.
Lemma F_93b28 : fetch_word Asan.M.loaded_segments (0x93b28 : word) = Some W_93b28.
Proof. vm_refl. Qed.
Lemma D_93b28 : decode_any W_93b28 = Some (Store SZ8 2 18 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93b2c : bv 32 := 0x05313423.
Lemma F_93b2c : fetch_word Asan.M.loaded_segments (0x93b2c : word) = Some W_93b2c.
Proof. vm_refl. Qed.
Lemma D_93b2c : decode_any W_93b2c = Some (Store SZ8 2 19 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93b30 : bv 32 := 0x05413023.
Lemma F_93b30 : fetch_word Asan.M.loaded_segments (0x93b30 : word) = Some W_93b30.
Proof. vm_refl. Qed.
Lemma D_93b30 : decode_any W_93b30 = Some (Store SZ8 2 20 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93b34 : bv 32 := 0x03513c23.
Lemma F_93b34 : fetch_word Asan.M.loaded_segments (0x93b34 : word) = Some W_93b34.
Proof. vm_refl. Qed.
Lemma D_93b34 : decode_any W_93b34 = Some (Store SZ8 2 21 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93b38 : bv 32 := 0x03613823.
Lemma F_93b38 : fetch_word Asan.M.loaded_segments (0x93b38 : word) = Some W_93b38.
Proof. vm_refl. Qed.
Lemma D_93b38 : decode_any W_93b38 = Some (Store SZ8 2 22 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93b3c : bv 32 := 0x00060413.
Lemma F_93b3c : fetch_word Asan.M.loaded_segments (0x93b3c : word) = Some W_93b3c.
Proof. vm_refl. Qed.
Lemma D_93b3c : decode_any W_93b3c = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93b40 : bv 32 := 0x00050493.
Lemma F_93b40 : fetch_word Asan.M.loaded_segments (0x93b40 : word) = Some W_93b40.
Proof. vm_refl. Qed.
Lemma D_93b40 : decode_any W_93b40 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93b44 : bv 32 := 0x0000c517.
Lemma F_93b44 : fetch_word Asan.M.loaded_segments (0x93b44 : word) = Some W_93b44.
Proof. vm_refl. Qed.
Lemma D_93b44 : decode_any W_93b44 = Some (Auipc 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93b48 : bv 32 := 0xc3453a83.
Lemma F_93b48 : fetch_word Asan.M.loaded_segments (0x93b48 : word) = Some W_93b48.
Proof. vm_refl. Qed.
Lemma D_93b48 : decode_any W_93b48 = Some (Load SZ8 true 21 10 3124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93b4c : bv 32 := 0x000ab503.
Lemma F_93b4c : fetch_word Asan.M.loaded_segments (0x93b4c : word) = Some W_93b4c.
Proof. vm_refl. Qed.
Lemma D_93b4c : decode_any W_93b4c = Some (Load SZ8 true 10 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93b50 : bv 32 := 0x02a13423.
Lemma F_93b50 : fetch_word Asan.M.loaded_segments (0x93b50 : word) = Some W_93b50.
Proof. vm_refl. Qed.
Lemma D_93b50 : decode_any W_93b50 = Some (Store SZ8 2 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93b54 : bv 32 := 0x0284b503.
Lemma F_93b54 : fetch_word Asan.M.loaded_segments (0x93b54 : word) = Some W_93b54.
Proof. vm_refl. Qed.
Lemma D_93b54 : decode_any W_93b54 = Some (Load SZ8 true 10 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93b58 : bv 32 := 0x0384b603.
Lemma F_93b58 : fetch_word Asan.M.loaded_segments (0x93b58 : word) = Some W_93b58.
Proof. vm_refl. Qed.
Lemma D_93b58 : decode_any W_93b58 = Some (Load SZ8 true 12 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93b5c : bv 32 := 0x40c50b33.
Lemma F_93b5c : fetch_word Asan.M.loaded_segments (0x93b5c : word) = Some W_93b5c.
Proof. vm_refl. Qed.
Lemma D_93b5c : decode_any W_93b5c = Some (Op ALU_SUB 22 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93b60 : bv 32 := 0x00c546b3.
Lemma F_93b60 : fetch_word Asan.M.loaded_segments (0x93b60 : word) = Some W_93b60.
Proof. vm_refl. Qed.
Lemma D_93b60 : decode_any W_93b60 = Some (Op ALU_XOR 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93b64 : bv 32 := 0x00c13423.
Lemma F_93b64 : fetch_word Asan.M.loaded_segments (0x93b64 : word) = Some W_93b64.
Proof. vm_refl. Qed.
Lemma D_93b64 : decode_any W_93b64 = Some (Store SZ8 2 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93b68 : bv 32 := 0x01613823.
Lemma F_93b68 : fetch_word Asan.M.loaded_segments (0x93b68 : word) = Some W_93b68.
Proof. vm_refl. Qed.
Lemma D_93b68 : decode_any W_93b68 = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93b6c : bv 32 := 0x00b13c23.
Lemma F_93b6c : fetch_word Asan.M.loaded_segments (0x93b6c : word) = Some W_93b6c.
Proof. vm_refl. Qed.
Lemma D_93b6c : decode_any W_93b6c = Some (Store SZ8 2 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93b70 : bv 32 := 0x02813023.
Lemma F_93b70 : fetch_word Asan.M.loaded_segments (0x93b70 : word) = Some W_93b70.
Proof. vm_refl. Qed.
Lemma D_93b70 : decode_any W_93b70 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93b74 : bv 32 := 0x008b0b33.
Lemma F_93b74 : fetch_word Asan.M.loaded_segments (0x93b74 : word) = Some W_93b74.
Proof. vm_refl. Qed.
Lemma D_93b74 : decode_any W_93b74 = Some (Op ALU_ADD 22 22 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93b78 : bv 32 := 0x00d03933.
Lemma F_93b78 : fetch_word Asan.M.loaded_segments (0x93b78 : word) = Some W_93b78.
Proof. vm_refl. Qed.
Lemma D_93b78 : decode_any W_93b78 = Some (Op ALU_SLTU 18 0 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93b7c : bv 32 := 0x00c50663.
Lemma F_93b7c : fetch_word Asan.M.loaded_segments (0x93b7c : word) = Some W_93b7c.
Proof. vm_refl. Qed.
Lemma D_93b7c : decode_any W_93b7c = Some (Branch BC_EQ 10 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93b80 : bv 32 := 0x00810993.
Lemma F_93b80 : fetch_word Asan.M.loaded_segments (0x93b80 : word) = Some W_93b80.
Proof. vm_refl. Qed.
Lemma D_93b80 : decode_any W_93b80 = Some (OpImm ALU_ADD 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93b84 : bv 32 := 0x0080006f.
Lemma F_93b84 : fetch_word Asan.M.loaded_segments (0x93b84 : word) = Some W_93b84.
Proof. vm_refl. Qed.
Lemma D_93b84 : decode_any W_93b84 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93b88 : bv 32 := 0x01810993.
Lemma F_93b88 : fetch_word Asan.M.loaded_segments (0x93b88 : word) = Some W_93b88.
Proof. vm_refl. Qed.
Lemma D_93b88 : decode_any W_93b88 = Some (OpImm ALU_ADD 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93b8c : bv 32 := 0x0784a503.
Lemma F_93b8c : fetch_word Asan.M.loaded_segments (0x93b8c : word) = Some W_93b8c.
Proof. vm_refl. Qed.
Lemma D_93b8c : decode_any W_93b8c = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93b90 : bv 32 := 0x00190913.
Lemma F_93b90 : fetch_word Asan.M.loaded_segments (0x93b90 : word) = Some W_93b90.
Proof. vm_refl. Qed.
Lemma D_93b90 : decode_any W_93b90 = Some (OpImm ALU_ADD 18 18 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93b94 : bv 32 := 0x04200893.
Lemma F_93b94 : fetch_word Asan.M.loaded_segments (0x93b94 : word) = Some W_93b94.
Proof. vm_refl. Qed.
Lemma D_93b94 : decode_any W_93b94 = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93b98 : bv 32 := 0x00098593.
Lemma F_93b98 : fetch_word Asan.M.loaded_segments (0x93b98 : word) = Some W_93b98.
Proof. vm_refl. Qed.
Lemma D_93b98 : decode_any W_93b98 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93b9c : bv 32 := 0x00090613.
Lemma F_93b9c : fetch_word Asan.M.loaded_segments (0x93b9c : word) = Some W_93b9c.
Proof. vm_refl. Qed.
Lemma D_93b9c : decode_any W_93b9c = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93ba0 : bv 32 := 0x00000073.
Lemma F_93ba0 : fetch_word Asan.M.loaded_segments (0x93ba0 : word) = Some W_93ba0.
Proof. vm_refl. Qed.
Lemma D_93ba0 : decode_any W_93ba0 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_93ba0 : is_ecall W_93ba0 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_93ba4 : bv 32 := 0xdbdfa0ef.
Lemma F_93ba4 : fetch_word Asan.M.loaded_segments (0x93ba4 : word) = Some W_93ba4.
Proof. vm_refl. Qed.
Lemma D_93ba4 : decode_any W_93ba4 = Some (Jal 1 2076092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93ba8 : bv 32 := 0x09651863.
Lemma F_93ba8 : fetch_word Asan.M.loaded_segments (0x93ba8 : word) = Some W_93ba8.
Proof. vm_refl. Qed.
Lemma D_93ba8 : decode_any W_93ba8 = Some (Branch BC_NE 10 22 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93bac : bv 32 := 0x0584b503.
Lemma F_93bac : fetch_word Asan.M.loaded_segments (0x93bac : word) = Some W_93bac.
Proof. vm_refl. Qed.
Lemma D_93bac : decode_any W_93bac = Some (Load SZ8 true 10 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93bb0 : bv 32 := 0x0604b583.
Lemma F_93bb0 : fetch_word Asan.M.loaded_segments (0x93bb0 : word) = Some W_93bb0.
Proof. vm_refl. Qed.
Lemma D_93bb0 : decode_any W_93bb0 = Some (Load SZ8 true 11 9 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93bb4 : bv 32 := 0x00b505b3.
Lemma F_93bb4 : fetch_word Asan.M.loaded_segments (0x93bb4 : word) = Some W_93bb4.
Proof. vm_refl. Qed.
Lemma D_93bb4 : decode_any W_93bb4 = Some (Op ALU_ADD 11 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93bb8 : bv 32 := 0x02b4b023.
Lemma F_93bb8 : fetch_word Asan.M.loaded_segments (0x93bb8 : word) = Some W_93bb8.
Proof. vm_refl. Qed.
Lemma D_93bb8 : decode_any W_93bb8 = Some (Store SZ8 9 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93bbc : bv 32 := 0x02a4b423.
Lemma F_93bbc : fetch_word Asan.M.loaded_segments (0x93bbc : word) = Some W_93bbc.
Proof. vm_refl. Qed.
Lemma D_93bbc : decode_any W_93bbc = Some (Store SZ8 9 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93bc0 : bv 32 := 0x02a4bc23.
Lemma F_93bc0 : fetch_word Asan.M.loaded_segments (0x93bc0 : word) = Some W_93bc0.
Proof. vm_refl. Qed.
Lemma D_93bc0 : decode_any W_93bc0 = Some (Store SZ8 9 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93bc4 : bv 32 := 0x00040513.
Lemma F_93bc4 : fetch_word Asan.M.loaded_segments (0x93bc4 : word) = Some W_93bc4.
Proof. vm_refl. Qed.
Lemma D_93bc4 : decode_any W_93bc4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93bc8 : bv 32 := 0x000ab583.
Lemma F_93bc8 : fetch_word Asan.M.loaded_segments (0x93bc8 : word) = Some W_93bc8.
Proof. vm_refl. Qed.
Lemma D_93bc8 : decode_any W_93bc8 = Some (Load SZ8 true 11 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93bcc : bv 32 := 0x02813603.
Lemma F_93bcc : fetch_word Asan.M.loaded_segments (0x93bcc : word) = Some W_93bcc.
Proof. vm_refl. Qed.
Lemma D_93bcc : decode_any W_93bcc = Some (Load SZ8 true 12 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93bd0 : bv 32 := 0x0cc59a63.
Lemma F_93bd0 : fetch_word Asan.M.loaded_segments (0x93bd0 : word) = Some W_93bd0.
Proof. vm_refl. Qed.
Lemma D_93bd0 : decode_any W_93bd0 = Some (Branch BC_NE 11 12 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93bd4 : bv 32 := 0x06813083.
Lemma F_93bd4 : fetch_word Asan.M.loaded_segments (0x93bd4 : word) = Some W_93bd4.
Proof. vm_refl. Qed.
Lemma D_93bd4 : decode_any W_93bd4 = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93bd8 : bv 32 := 0x06013403.
Lemma F_93bd8 : fetch_word Asan.M.loaded_segments (0x93bd8 : word) = Some W_93bd8.
Proof. vm_refl. Qed.
Lemma D_93bd8 : decode_any W_93bd8 = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93bdc : bv 32 := 0x05813483.
Lemma F_93bdc : fetch_word Asan.M.loaded_segments (0x93bdc : word) = Some W_93bdc.
Proof. vm_refl. Qed.
Lemma D_93bdc : decode_any W_93bdc = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93be0 : bv 32 := 0x05013903.
Lemma F_93be0 : fetch_word Asan.M.loaded_segments (0x93be0 : word) = Some W_93be0.
Proof. vm_refl. Qed.
Lemma D_93be0 : decode_any W_93be0 = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93be4 : bv 32 := 0x04813983.
Lemma F_93be4 : fetch_word Asan.M.loaded_segments (0x93be4 : word) = Some W_93be4.
Proof. vm_refl. Qed.
Lemma D_93be4 : decode_any W_93be4 = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93be8 : bv 32 := 0x04013a03.
Lemma F_93be8 : fetch_word Asan.M.loaded_segments (0x93be8 : word) = Some W_93be8.
Proof. vm_refl. Qed.
Lemma D_93be8 : decode_any W_93be8 = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93bec : bv 32 := 0x03813a83.
Lemma F_93bec : fetch_word Asan.M.loaded_segments (0x93bec : word) = Some W_93bec.
Proof. vm_refl. Qed.
Lemma D_93bec : decode_any W_93bec = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93bf0 : bv 32 := 0x03013b03.
Lemma F_93bf0 : fetch_word Asan.M.loaded_segments (0x93bf0 : word) = Some W_93bf0.
Proof. vm_refl. Qed.
Lemma D_93bf0 : decode_any W_93bf0 = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93bf4 : bv 32 := 0x07010113.
Lemma F_93bf4 : fetch_word Asan.M.loaded_segments (0x93bf4 : word) = Some W_93bf4.
Proof. vm_refl. Qed.
Lemma D_93bf4 : decode_any W_93bf4 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93bf8 : bv 32 := 0x00008067.
Lemma F_93bf8 : fetch_word Asan.M.loaded_segments (0x93bf8 : word) = Some W_93bf8.
Proof. vm_refl. Qed.
Lemma D_93bf8 : decode_any W_93bf8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93bfc : bv 32 := 0x00800713.
Lemma F_93bfc : fetch_word Asan.M.loaded_segments (0x93bfc : word) = Some W_93bfc.
Proof. vm_refl. Qed.
Lemma D_93bfc : decode_any W_93bfc = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93c00 : bv 32 := 0x000a0593.
Lemma F_93c00 : fetch_word Asan.M.loaded_segments (0x93c00 : word) = Some W_93c00.
Proof. vm_refl. Qed.
Lemma D_93c00 : decode_any W_93c00 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93c04 : bv 32 := 0x00e98733.
Lemma F_93c04 : fetch_word Asan.M.loaded_segments (0x93c04 : word) = Some W_93c04.
Proof. vm_refl. Qed.
Lemma D_93c04 : decode_any W_93c04 = Some (Op ALU_ADD 14 19 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93c08 : bv 32 := 0x00073783.
Lemma F_93c08 : fetch_word Asan.M.loaded_segments (0x93c08 : word) = Some W_93c08.
Proof. vm_refl. Qed.
Lemma D_93c08 : decode_any W_93c08 = Some (Load SZ8 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93c0c : bv 32 := 0x40ab0b33.
Lemma F_93c0c : fetch_word Asan.M.loaded_segments (0x93c0c : word) = Some W_93c0c.
Proof. vm_refl. Qed.
Lemma D_93c0c : decode_any W_93c0c = Some (Op ALU_SUB 22 22 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93c10 : bv 32 := 0x0784a503.
Lemma F_93c10 : fetch_word Asan.M.loaded_segments (0x93c10 : word) = Some W_93c10.
Proof. vm_refl. Qed.
Lemma D_93c10 : decode_any W_93c10 = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93c14 : bv 32 := 0x40c9093b.
Lemma F_93c14 : fetch_word Asan.M.loaded_segments (0x93c14 : word) = Some W_93c14.
Proof. vm_refl. Qed.
Lemma D_93c14 : decode_any W_93c14 = Some (Op32 ALU_SUB 18 18 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93c18 : bv 32 := 0x40d787b3.
Lemma F_93c18 : fetch_word Asan.M.loaded_segments (0x93c18 : word) = Some W_93c18.
Proof. vm_refl. Qed.
Lemma D_93c18 : decode_any W_93c18 = Some (Op ALU_SUB 15 15 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93c1c : bv 32 := 0x00f73023.
Lemma F_93c1c : fetch_word Asan.M.loaded_segments (0x93c1c : word) = Some W_93c1c.
Proof. vm_refl. Qed.
Lemma D_93c1c : decode_any W_93c1c = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93c20 : bv 32 := 0x04200893.
Lemma F_93c20 : fetch_word Asan.M.loaded_segments (0x93c20 : word) = Some W_93c20.
Proof. vm_refl. Qed.
Lemma D_93c20 : decode_any W_93c20 = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93c24 : bv 32 := 0x00090613.
Lemma F_93c24 : fetch_word Asan.M.loaded_segments (0x93c24 : word) = Some W_93c24.
Proof. vm_refl. Qed.
Lemma D_93c24 : decode_any W_93c24 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93c28 : bv 32 := 0x00000073.
Lemma F_93c28 : fetch_word Asan.M.loaded_segments (0x93c28 : word) = Some W_93c28.
Proof. vm_refl. Qed.
Lemma D_93c28 : decode_any W_93c28 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_93c28 : is_ecall W_93c28 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_93c2c : bv 32 := 0xd35fa0ef.
Lemma F_93c2c : fetch_word Asan.M.loaded_segments (0x93c2c : word) = Some W_93c2c.
Proof. vm_refl. Qed.
Lemma D_93c2c : decode_any W_93c2c = Some (Jal 1 2075956, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93c30 : bv 32 := 0x000a0993.
Lemma F_93c30 : fetch_word Asan.M.loaded_segments (0x93c30 : word) = Some W_93c30.
Proof. vm_refl. Qed.
Lemma D_93c30 : decode_any W_93c30 = Some (OpImm ALU_ADD 19 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93c34 : bv 32 := 0xf7650ce3.
Lemma F_93c34 : fetch_word Asan.M.loaded_segments (0x93c34 : word) = Some W_93c34.
Proof. vm_refl. Qed.
Lemma D_93c34 : decode_any W_93c34 = Some (Branch BC_EQ 10 22 8056, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93c38 : bv 32 := 0x02054c63.
Lemma F_93c38 : fetch_word Asan.M.loaded_segments (0x93c38 : word) = Some W_93c38.
Proof. vm_refl. Qed.
Lemma D_93c38 : decode_any W_93c38 = Some (Branch BC_LT 10 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93c3c : bv 32 := 0x0089b583.
Lemma F_93c3c : fetch_word Asan.M.loaded_segments (0x93c3c : word) = Some W_93c3c.
Proof. vm_refl. Qed.
Lemma D_93c3c : decode_any W_93c3c = Some (Load SZ8 true 11 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93c40 : bv 32 := 0x00a5b633.
Lemma F_93c40 : fetch_word Asan.M.loaded_segments (0x93c40 : word) = Some W_93c40.
Proof. vm_refl. Qed.
Lemma D_93c40 : decode_any W_93c40 = Some (Op ALU_SLTU 12 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93c44 : bv 32 := 0x00461a13.
Lemma F_93c44 : fetch_word Asan.M.loaded_segments (0x93c44 : word) = Some W_93c44.
Proof. vm_refl. Qed.
Lemma D_93c44 : decode_any W_93c44 = Some (ShiftImm ALU_SLL 20 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93c48 : bv 32 := 0x01498a33.
Lemma F_93c48 : fetch_word Asan.M.loaded_segments (0x93c48 : word) = Some W_93c48.
Proof. vm_refl. Qed.
Lemma D_93c48 : decode_any W_93c48 = Some (Op ALU_ADD 20 19 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93c4c : bv 32 := 0x000a3703.
Lemma F_93c4c : fetch_word Asan.M.loaded_segments (0x93c4c : word) = Some W_93c4c.
Proof. vm_refl. Qed.
Lemma D_93c4c : decode_any W_93c4c = Some (Load SZ8 true 14 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93c50 : bv 32 := 0x40c006b3.
Lemma F_93c50 : fetch_word Asan.M.loaded_segments (0x93c50 : word) = Some W_93c50.
Proof. vm_refl. Qed.
Lemma D_93c50 : decode_any W_93c50 = Some (Op ALU_SUB 13 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93c54 : bv 32 := 0x00b6f6b3.
Lemma F_93c54 : fetch_word Asan.M.loaded_segments (0x93c54 : word) = Some W_93c54.
Proof. vm_refl. Qed.
Lemma D_93c54 : decode_any W_93c54 = Some (Op ALU_AND 13 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93c58 : bv 32 := 0x40d506b3.
Lemma F_93c58 : fetch_word Asan.M.loaded_segments (0x93c58 : word) = Some W_93c58.
Proof. vm_refl. Qed.
Lemma D_93c58 : decode_any W_93c58 = Some (Op ALU_SUB 13 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93c5c : bv 32 := 0x00d70733.
Lemma F_93c5c : fetch_word Asan.M.loaded_segments (0x93c5c : word) = Some W_93c5c.
Proof. vm_refl. Qed.
Lemma D_93c5c : decode_any W_93c5c = Some (Op ALU_ADD 14 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93c60 : bv 32 := 0x00ea3023.
Lemma F_93c60 : fetch_word Asan.M.loaded_segments (0x93c60 : word) = Some W_93c60.
Proof. vm_refl. Qed.
Lemma D_93c60 : decode_any W_93c60 = Some (Store SZ8 20 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93c64 : bv 32 := 0xf8a5fce3.
Lemma F_93c64 : fetch_word Asan.M.loaded_segments (0x93c64 : word) = Some W_93c64.
Proof. vm_refl. Qed.
Lemma D_93c64 : decode_any W_93c64 = Some (Branch BC_GEU 11 10 8088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93c68 : bv 32 := 0x01800713.
Lemma F_93c68 : fetch_word Asan.M.loaded_segments (0x93c68 : word) = Some W_93c68.
Proof. vm_refl. Qed.
Lemma D_93c68 : decode_any W_93c68 = Some (OpImm ALU_ADD 14 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93c6c : bv 32 := 0xf95ff06f.
Lemma F_93c6c : fetch_word Asan.M.loaded_segments (0x93c6c : word) = Some W_93c6c.
Proof. vm_refl. Qed.
Lemma D_93c6c : decode_any W_93c6c = Some (Jal 0 2097044, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93c70 : bv 32 := 0x00000513.
Lemma F_93c70 : fetch_word Asan.M.loaded_segments (0x93c70 : word) = Some W_93c70.
Proof. vm_refl. Qed.
Lemma D_93c70 : decode_any W_93c70 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93c74 : bv 32 := 0x0004a583.
Lemma F_93c74 : fetch_word Asan.M.loaded_segments (0x93c74 : word) = Some W_93c74.
Proof. vm_refl. Qed.
Lemma D_93c74 : decode_any W_93c74 = Some (Load SZ4 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93c78 : bv 32 := 0x0009091b.
Lemma F_93c78 : fetch_word Asan.M.loaded_segments (0x93c78 : word) = Some W_93c78.
Proof. vm_refl. Qed.
Lemma D_93c78 : decode_any W_93c78 = Some (OpImm32 18 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93c7c : bv 32 := 0x00200613.
Lemma F_93c7c : fetch_word Asan.M.loaded_segments (0x93c7c : word) = Some W_93c7c.
Proof. vm_refl. Qed.
Lemma D_93c7c : decode_any W_93c7c = Some (OpImm ALU_ADD 12 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93c80 : bv 32 := 0x0205e593.
Lemma F_93c80 : fetch_word Asan.M.loaded_segments (0x93c80 : word) = Some W_93c80.
Proof. vm_refl. Qed.
Lemma D_93c80 : decode_any W_93c80 = Some (OpImm ALU_OR 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93c84 : bv 32 := 0x00b4a023.
Lemma F_93c84 : fetch_word Asan.M.loaded_segments (0x93c84 : word) = Some W_93c84.
Proof. vm_refl. Qed.
Lemma D_93c84 : decode_any W_93c84 = Some (Store SZ4 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93c88 : bv 32 := 0x0204b023.
Lemma F_93c88 : fetch_word Asan.M.loaded_segments (0x93c88 : word) = Some W_93c88.
Proof. vm_refl. Qed.
Lemma D_93c88 : decode_any W_93c88 = Some (Store SZ8 9 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93c8c : bv 32 := 0x0204b423.
Lemma F_93c8c : fetch_word Asan.M.loaded_segments (0x93c8c : word) = Some W_93c8c.
Proof. vm_refl. Qed.
Lemma D_93c8c : decode_any W_93c8c = Some (Store SZ8 9 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93c90 : bv 32 := 0x0204bc23.
Lemma F_93c90 : fetch_word Asan.M.loaded_segments (0x93c90 : word) = Some W_93c90.
Proof. vm_refl. Qed.
Lemma D_93c90 : decode_any W_93c90 = Some (Store SZ8 9 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93c94 : bv 32 := 0xf2c90ae3.
Lemma F_93c94 : fetch_word Asan.M.loaded_segments (0x93c94 : word) = Some W_93c94.
Proof. vm_refl. Qed.
Lemma D_93c94 : decode_any W_93c94 = Some (Branch BC_EQ 18 12 7988, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93c98 : bv 32 := 0x0089b503.
Lemma F_93c98 : fetch_word Asan.M.loaded_segments (0x93c98 : word) = Some W_93c98.
Proof. vm_refl. Qed.
Lemma D_93c98 : decode_any W_93c98 = Some (Load SZ8 true 10 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93c9c : bv 32 := 0x40a40533.
Lemma F_93c9c : fetch_word Asan.M.loaded_segments (0x93c9c : word) = Some W_93c9c.
Proof. vm_refl. Qed.
Lemma D_93c9c : decode_any W_93c9c = Some (Op ALU_SUB 10 8 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93ca0 : bv 32 := 0xf29ff06f.
Lemma F_93ca0 : fetch_word Asan.M.loaded_segments (0x93ca0 : word) = Some W_93ca0.
Proof. vm_refl. Qed.
Lemma D_93ca0 : decode_any W_93ca0 = Some (Jal 0 2096936, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93ca4 : bv 32 := 0xe50fa0ef.
Lemma F_93ca4 : fetch_word Asan.M.loaded_segments (0x93ca4 : word) = Some W_93ca4.
Proof. vm_refl. Qed.
Lemma D_93ca4 : decode_any W_93ca4 = Some (Jal 1 2074192, 4%Z).
Proof. vm_refl. Qed.
