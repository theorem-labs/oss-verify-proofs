(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_9ac5c : bv 32 := 0xfffff5b7.
Lemma F_9ac5c : fetch_word Asan.M.loaded_segments (0x9ac5c : word) = Some W_9ac5c.
Proof. vm_refl. Qed.
Lemma D_9ac5c : decode_any W_9ac5c = Some (Lui 11 1048575, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ac60 : bv 32 := 0x0015859b.
Lemma F_9ac60 : fetch_word Asan.M.loaded_segments (0x9ac60 : word) = Some W_9ac60.
Proof. vm_refl. Qed.
Lemma D_9ac60 : decode_any W_9ac60 = Some (OpImm32 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ac64 : bv 32 := 0x02b56663.
Lemma F_9ac64 : fetch_word Asan.M.loaded_segments (0x9ac64 : word) = Some W_9ac64.
Proof. vm_refl. Qed.
Lemma D_9ac64 : decode_any W_9ac64 = Some (Branch BC_LTU 10 11 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ac68 : bv 32 := 0xff010113.
Lemma F_9ac68 : fetch_word Asan.M.loaded_segments (0x9ac68 : word) = Some W_9ac68.
Proof. vm_refl. Qed.
Lemma D_9ac68 : decode_any W_9ac68 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ac6c : bv 32 := 0x00113423.
Lemma F_9ac6c : fetch_word Asan.M.loaded_segments (0x9ac6c : word) = Some W_9ac6c.
Proof. vm_refl. Qed.
Lemma D_9ac6c : decode_any W_9ac6c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ac70 : bv 32 := 0x00813023.
Lemma F_9ac70 : fetch_word Asan.M.loaded_segments (0x9ac70 : word) = Some W_9ac70.
Proof. vm_refl. Qed.
Lemma D_9ac70 : decode_any W_9ac70 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ac74 : bv 32 := 0x40a0043b.
Lemma F_9ac74 : fetch_word Asan.M.loaded_segments (0x9ac74 : word) = Some W_9ac74.
Proof. vm_refl. Qed.
Lemma D_9ac74 : decode_any W_9ac74 = Some (Op32 ALU_SUB 8 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ac78 : bv 32 := 0x981ff0ef.
Lemma F_9ac78 : fetch_word Asan.M.loaded_segments (0x9ac78 : word) = Some W_9ac78.
Proof. vm_refl. Qed.
Lemma D_9ac78 : decode_any W_9ac78 = Some (Jal 1 2095488, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ac7c : bv 32 := 0x00852023.
Lemma F_9ac7c : fetch_word Asan.M.loaded_segments (0x9ac7c : word) = Some W_9ac7c.
Proof. vm_refl. Qed.
Lemma D_9ac7c : decode_any W_9ac7c = Some (Store SZ4 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ac80 : bv 32 := 0xfff00513.
Lemma F_9ac80 : fetch_word Asan.M.loaded_segments (0x9ac80 : word) = Some W_9ac80.
Proof. vm_refl. Qed.
Lemma D_9ac80 : decode_any W_9ac80 = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ac84 : bv 32 := 0x00813083.
Lemma F_9ac84 : fetch_word Asan.M.loaded_segments (0x9ac84 : word) = Some W_9ac84.
Proof. vm_refl. Qed.
Lemma D_9ac84 : decode_any W_9ac84 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ac88 : bv 32 := 0x00013403.
Lemma F_9ac88 : fetch_word Asan.M.loaded_segments (0x9ac88 : word) = Some W_9ac88.
Proof. vm_refl. Qed.
Lemma D_9ac88 : decode_any W_9ac88 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ac8c : bv 32 := 0x01010113.
Lemma F_9ac8c : fetch_word Asan.M.loaded_segments (0x9ac8c : word) = Some W_9ac8c.
Proof. vm_refl. Qed.
Lemma D_9ac8c : decode_any W_9ac8c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ac90 : bv 32 := 0x00008067.
Lemma F_9ac90 : fetch_word Asan.M.loaded_segments (0x9ac90 : word) = Some W_9ac90.
Proof. vm_refl. Qed.
Lemma D_9ac90 : decode_any W_9ac90 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9fea4 : bv 32 := 0xf9010113.
Lemma F_9fea4 : fetch_word Asan.M.loaded_segments (0x9fea4 : word) = Some W_9fea4.
Proof. vm_refl. Qed.
Lemma D_9fea4 : decode_any W_9fea4 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9fea8 : bv 32 := 0x06113423.
Lemma F_9fea8 : fetch_word Asan.M.loaded_segments (0x9fea8 : word) = Some W_9fea8.
Proof. vm_refl. Qed.
Lemma D_9fea8 : decode_any W_9fea8 = Some (Store SZ8 2 1 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9feac : bv 32 := 0x06813023.
Lemma F_9feac : fetch_word Asan.M.loaded_segments (0x9feac : word) = Some W_9feac.
Proof. vm_refl. Qed.
Lemma D_9feac : decode_any W_9feac = Some (Store SZ8 2 8 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9feb0 : bv 32 := 0x04913c23.
Lemma F_9feb0 : fetch_word Asan.M.loaded_segments (0x9feb0 : word) = Some W_9feb0.
Proof. vm_refl. Qed.
Lemma D_9feb0 : decode_any W_9feb0 = Some (Store SZ8 2 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9feb4 : bv 32 := 0x05213823.
Lemma F_9feb4 : fetch_word Asan.M.loaded_segments (0x9feb4 : word) = Some W_9feb4.
Proof. vm_refl. Qed.
Lemma D_9feb4 : decode_any W_9feb4 = Some (Store SZ8 2 18 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9feb8 : bv 32 := 0x05313423.
Lemma F_9feb8 : fetch_word Asan.M.loaded_segments (0x9feb8 : word) = Some W_9feb8.
Proof. vm_refl. Qed.
Lemma D_9feb8 : decode_any W_9feb8 = Some (Store SZ8 2 19 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9febc : bv 32 := 0x05413023.
Lemma F_9febc : fetch_word Asan.M.loaded_segments (0x9febc : word) = Some W_9febc.
Proof. vm_refl. Qed.
Lemma D_9febc : decode_any W_9febc = Some (Store SZ8 2 20 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9fec0 : bv 32 := 0x03513c23.
Lemma F_9fec0 : fetch_word Asan.M.loaded_segments (0x9fec0 : word) = Some W_9fec0.
Proof. vm_refl. Qed.
Lemma D_9fec0 : decode_any W_9fec0 = Some (Store SZ8 2 21 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9fec4 : bv 32 := 0x03613823.
Lemma F_9fec4 : fetch_word Asan.M.loaded_segments (0x9fec4 : word) = Some W_9fec4.
Proof. vm_refl. Qed.
Lemma D_9fec4 : decode_any W_9fec4 = Some (Store SZ8 2 22 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9fec8 : bv 32 := 0x00060413.
Lemma F_9fec8 : fetch_word Asan.M.loaded_segments (0x9fec8 : word) = Some W_9fec8.
Proof. vm_refl. Qed.
Lemma D_9fec8 : decode_any W_9fec8 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9fecc : bv 32 := 0x00050493.
Lemma F_9fecc : fetch_word Asan.M.loaded_segments (0x9fecc : word) = Some W_9fecc.
Proof. vm_refl. Qed.
Lemma D_9fecc : decode_any W_9fecc = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9fed0 : bv 32 := 0x0000c517.
Lemma F_9fed0 : fetch_word Asan.M.loaded_segments (0x9fed0 : word) = Some W_9fed0.
Proof. vm_refl. Qed.
Lemma D_9fed0 : decode_any W_9fed0 = Some (Auipc 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9fed4 : bv 32 := 0xc3853a83.
Lemma F_9fed4 : fetch_word Asan.M.loaded_segments (0x9fed4 : word) = Some W_9fed4.
Proof. vm_refl. Qed.
Lemma D_9fed4 : decode_any W_9fed4 = Some (Load SZ8 true 21 10 3128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9fed8 : bv 32 := 0x000ab503.
Lemma F_9fed8 : fetch_word Asan.M.loaded_segments (0x9fed8 : word) = Some W_9fed8.
Proof. vm_refl. Qed.
Lemma D_9fed8 : decode_any W_9fed8 = Some (Load SZ8 true 10 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9fedc : bv 32 := 0x02a13423.
Lemma F_9fedc : fetch_word Asan.M.loaded_segments (0x9fedc : word) = Some W_9fedc.
Proof. vm_refl. Qed.
Lemma D_9fedc : decode_any W_9fedc = Some (Store SZ8 2 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9fee0 : bv 32 := 0x0284b503.
Lemma F_9fee0 : fetch_word Asan.M.loaded_segments (0x9fee0 : word) = Some W_9fee0.
Proof. vm_refl. Qed.
Lemma D_9fee0 : decode_any W_9fee0 = Some (Load SZ8 true 10 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9fee4 : bv 32 := 0x0384b603.
Lemma F_9fee4 : fetch_word Asan.M.loaded_segments (0x9fee4 : word) = Some W_9fee4.
Proof. vm_refl. Qed.
Lemma D_9fee4 : decode_any W_9fee4 = Some (Load SZ8 true 12 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9fee8 : bv 32 := 0x40c50b33.
Lemma F_9fee8 : fetch_word Asan.M.loaded_segments (0x9fee8 : word) = Some W_9fee8.
Proof. vm_refl. Qed.
Lemma D_9fee8 : decode_any W_9fee8 = Some (Op ALU_SUB 22 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9feec : bv 32 := 0x00c546b3.
Lemma F_9feec : fetch_word Asan.M.loaded_segments (0x9feec : word) = Some W_9feec.
Proof. vm_refl. Qed.
Lemma D_9feec : decode_any W_9feec = Some (Op ALU_XOR 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9fef0 : bv 32 := 0x00c13423.
Lemma F_9fef0 : fetch_word Asan.M.loaded_segments (0x9fef0 : word) = Some W_9fef0.
Proof. vm_refl. Qed.
Lemma D_9fef0 : decode_any W_9fef0 = Some (Store SZ8 2 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9fef4 : bv 32 := 0x01613823.
Lemma F_9fef4 : fetch_word Asan.M.loaded_segments (0x9fef4 : word) = Some W_9fef4.
Proof. vm_refl. Qed.
Lemma D_9fef4 : decode_any W_9fef4 = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9fef8 : bv 32 := 0x00b13c23.
Lemma F_9fef8 : fetch_word Asan.M.loaded_segments (0x9fef8 : word) = Some W_9fef8.
Proof. vm_refl. Qed.
Lemma D_9fef8 : decode_any W_9fef8 = Some (Store SZ8 2 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9fefc : bv 32 := 0x02813023.
Lemma F_9fefc : fetch_word Asan.M.loaded_segments (0x9fefc : word) = Some W_9fefc.
Proof. vm_refl. Qed.
Lemma D_9fefc : decode_any W_9fefc = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ff00 : bv 32 := 0x008b0b33.
Lemma F_9ff00 : fetch_word Asan.M.loaded_segments (0x9ff00 : word) = Some W_9ff00.
Proof. vm_refl. Qed.
Lemma D_9ff00 : decode_any W_9ff00 = Some (Op ALU_ADD 22 22 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ff04 : bv 32 := 0x00d03933.
Lemma F_9ff04 : fetch_word Asan.M.loaded_segments (0x9ff04 : word) = Some W_9ff04.
Proof. vm_refl. Qed.
Lemma D_9ff04 : decode_any W_9ff04 = Some (Op ALU_SLTU 18 0 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ff08 : bv 32 := 0x00c50663.
Lemma F_9ff08 : fetch_word Asan.M.loaded_segments (0x9ff08 : word) = Some W_9ff08.
Proof. vm_refl. Qed.
Lemma D_9ff08 : decode_any W_9ff08 = Some (Branch BC_EQ 10 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ff0c : bv 32 := 0x00810993.
Lemma F_9ff0c : fetch_word Asan.M.loaded_segments (0x9ff0c : word) = Some W_9ff0c.
Proof. vm_refl. Qed.
Lemma D_9ff0c : decode_any W_9ff0c = Some (OpImm ALU_ADD 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ff10 : bv 32 := 0x0080006f.
Lemma F_9ff10 : fetch_word Asan.M.loaded_segments (0x9ff10 : word) = Some W_9ff10.
Proof. vm_refl. Qed.
Lemma D_9ff10 : decode_any W_9ff10 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ff14 : bv 32 := 0x01810993.
Lemma F_9ff14 : fetch_word Asan.M.loaded_segments (0x9ff14 : word) = Some W_9ff14.
Proof. vm_refl. Qed.
Lemma D_9ff14 : decode_any W_9ff14 = Some (OpImm ALU_ADD 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ff18 : bv 32 := 0x0784a503.
Lemma F_9ff18 : fetch_word Asan.M.loaded_segments (0x9ff18 : word) = Some W_9ff18.
Proof. vm_refl. Qed.
Lemma D_9ff18 : decode_any W_9ff18 = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ff1c : bv 32 := 0x00190913.
Lemma F_9ff1c : fetch_word Asan.M.loaded_segments (0x9ff1c : word) = Some W_9ff1c.
Proof. vm_refl. Qed.
Lemma D_9ff1c : decode_any W_9ff1c = Some (OpImm ALU_ADD 18 18 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ff20 : bv 32 := 0x04200893.
Lemma F_9ff20 : fetch_word Asan.M.loaded_segments (0x9ff20 : word) = Some W_9ff20.
Proof. vm_refl. Qed.
Lemma D_9ff20 : decode_any W_9ff20 = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ff24 : bv 32 := 0x00098593.
Lemma F_9ff24 : fetch_word Asan.M.loaded_segments (0x9ff24 : word) = Some W_9ff24.
Proof. vm_refl. Qed.
Lemma D_9ff24 : decode_any W_9ff24 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ff28 : bv 32 := 0x00090613.
Lemma F_9ff28 : fetch_word Asan.M.loaded_segments (0x9ff28 : word) = Some W_9ff28.
Proof. vm_refl. Qed.
Lemma D_9ff28 : decode_any W_9ff28 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ff2c : bv 32 := 0x00000073.
Lemma F_9ff2c : fetch_word Asan.M.loaded_segments (0x9ff2c : word) = Some W_9ff2c.
Proof. vm_refl. Qed.
Lemma D_9ff2c : decode_any W_9ff2c = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_9ff2c : is_ecall W_9ff2c = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_9ff30 : bv 32 := 0xd2dfa0ef.
Lemma F_9ff30 : fetch_word Asan.M.loaded_segments (0x9ff30 : word) = Some W_9ff30.
Proof. vm_refl. Qed.
Lemma D_9ff30 : decode_any W_9ff30 = Some (Jal 1 2075948, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ff34 : bv 32 := 0x09651863.
Lemma F_9ff34 : fetch_word Asan.M.loaded_segments (0x9ff34 : word) = Some W_9ff34.
Proof. vm_refl. Qed.
Lemma D_9ff34 : decode_any W_9ff34 = Some (Branch BC_NE 10 22 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ff38 : bv 32 := 0x0584b503.
Lemma F_9ff38 : fetch_word Asan.M.loaded_segments (0x9ff38 : word) = Some W_9ff38.
Proof. vm_refl. Qed.
Lemma D_9ff38 : decode_any W_9ff38 = Some (Load SZ8 true 10 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ff3c : bv 32 := 0x0604b583.
Lemma F_9ff3c : fetch_word Asan.M.loaded_segments (0x9ff3c : word) = Some W_9ff3c.
Proof. vm_refl. Qed.
Lemma D_9ff3c : decode_any W_9ff3c = Some (Load SZ8 true 11 9 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ff40 : bv 32 := 0x00b505b3.
Lemma F_9ff40 : fetch_word Asan.M.loaded_segments (0x9ff40 : word) = Some W_9ff40.
Proof. vm_refl. Qed.
Lemma D_9ff40 : decode_any W_9ff40 = Some (Op ALU_ADD 11 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ff44 : bv 32 := 0x02b4b023.
Lemma F_9ff44 : fetch_word Asan.M.loaded_segments (0x9ff44 : word) = Some W_9ff44.
Proof. vm_refl. Qed.
Lemma D_9ff44 : decode_any W_9ff44 = Some (Store SZ8 9 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ff48 : bv 32 := 0x02a4b423.
Lemma F_9ff48 : fetch_word Asan.M.loaded_segments (0x9ff48 : word) = Some W_9ff48.
Proof. vm_refl. Qed.
Lemma D_9ff48 : decode_any W_9ff48 = Some (Store SZ8 9 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ff4c : bv 32 := 0x02a4bc23.
Lemma F_9ff4c : fetch_word Asan.M.loaded_segments (0x9ff4c : word) = Some W_9ff4c.
Proof. vm_refl. Qed.
Lemma D_9ff4c : decode_any W_9ff4c = Some (Store SZ8 9 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ff50 : bv 32 := 0x00040513.
Lemma F_9ff50 : fetch_word Asan.M.loaded_segments (0x9ff50 : word) = Some W_9ff50.
Proof. vm_refl. Qed.
Lemma D_9ff50 : decode_any W_9ff50 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ff54 : bv 32 := 0x000ab583.
Lemma F_9ff54 : fetch_word Asan.M.loaded_segments (0x9ff54 : word) = Some W_9ff54.
Proof. vm_refl. Qed.
Lemma D_9ff54 : decode_any W_9ff54 = Some (Load SZ8 true 11 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ff58 : bv 32 := 0x02813603.
Lemma F_9ff58 : fetch_word Asan.M.loaded_segments (0x9ff58 : word) = Some W_9ff58.
Proof. vm_refl. Qed.
Lemma D_9ff58 : decode_any W_9ff58 = Some (Load SZ8 true 12 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ff5c : bv 32 := 0x0cc59a63.
Lemma F_9ff5c : fetch_word Asan.M.loaded_segments (0x9ff5c : word) = Some W_9ff5c.
Proof. vm_refl. Qed.
Lemma D_9ff5c : decode_any W_9ff5c = Some (Branch BC_NE 11 12 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ff60 : bv 32 := 0x06813083.
Lemma F_9ff60 : fetch_word Asan.M.loaded_segments (0x9ff60 : word) = Some W_9ff60.
Proof. vm_refl. Qed.
Lemma D_9ff60 : decode_any W_9ff60 = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ff64 : bv 32 := 0x06013403.
Lemma F_9ff64 : fetch_word Asan.M.loaded_segments (0x9ff64 : word) = Some W_9ff64.
Proof. vm_refl. Qed.
Lemma D_9ff64 : decode_any W_9ff64 = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ff68 : bv 32 := 0x05813483.
Lemma F_9ff68 : fetch_word Asan.M.loaded_segments (0x9ff68 : word) = Some W_9ff68.
Proof. vm_refl. Qed.
Lemma D_9ff68 : decode_any W_9ff68 = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ff6c : bv 32 := 0x05013903.
Lemma F_9ff6c : fetch_word Asan.M.loaded_segments (0x9ff6c : word) = Some W_9ff6c.
Proof. vm_refl. Qed.
Lemma D_9ff6c : decode_any W_9ff6c = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ff70 : bv 32 := 0x04813983.
Lemma F_9ff70 : fetch_word Asan.M.loaded_segments (0x9ff70 : word) = Some W_9ff70.
Proof. vm_refl. Qed.
Lemma D_9ff70 : decode_any W_9ff70 = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ff74 : bv 32 := 0x04013a03.
Lemma F_9ff74 : fetch_word Asan.M.loaded_segments (0x9ff74 : word) = Some W_9ff74.
Proof. vm_refl. Qed.
Lemma D_9ff74 : decode_any W_9ff74 = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ff78 : bv 32 := 0x03813a83.
Lemma F_9ff78 : fetch_word Asan.M.loaded_segments (0x9ff78 : word) = Some W_9ff78.
Proof. vm_refl. Qed.
Lemma D_9ff78 : decode_any W_9ff78 = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ff7c : bv 32 := 0x03013b03.
Lemma F_9ff7c : fetch_word Asan.M.loaded_segments (0x9ff7c : word) = Some W_9ff7c.
Proof. vm_refl. Qed.
Lemma D_9ff7c : decode_any W_9ff7c = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ff80 : bv 32 := 0x07010113.
Lemma F_9ff80 : fetch_word Asan.M.loaded_segments (0x9ff80 : word) = Some W_9ff80.
Proof. vm_refl. Qed.
Lemma D_9ff80 : decode_any W_9ff80 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ff84 : bv 32 := 0x00008067.
Lemma F_9ff84 : fetch_word Asan.M.loaded_segments (0x9ff84 : word) = Some W_9ff84.
Proof. vm_refl. Qed.
Lemma D_9ff84 : decode_any W_9ff84 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ff88 : bv 32 := 0x00800713.
Lemma F_9ff88 : fetch_word Asan.M.loaded_segments (0x9ff88 : word) = Some W_9ff88.
Proof. vm_refl. Qed.
Lemma D_9ff88 : decode_any W_9ff88 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ff8c : bv 32 := 0x000a0593.
Lemma F_9ff8c : fetch_word Asan.M.loaded_segments (0x9ff8c : word) = Some W_9ff8c.
Proof. vm_refl. Qed.
Lemma D_9ff8c : decode_any W_9ff8c = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ff90 : bv 32 := 0x00e98733.
Lemma F_9ff90 : fetch_word Asan.M.loaded_segments (0x9ff90 : word) = Some W_9ff90.
Proof. vm_refl. Qed.
Lemma D_9ff90 : decode_any W_9ff90 = Some (Op ALU_ADD 14 19 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ff94 : bv 32 := 0x00073783.
Lemma F_9ff94 : fetch_word Asan.M.loaded_segments (0x9ff94 : word) = Some W_9ff94.
Proof. vm_refl. Qed.
Lemma D_9ff94 : decode_any W_9ff94 = Some (Load SZ8 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ff98 : bv 32 := 0x40ab0b33.
Lemma F_9ff98 : fetch_word Asan.M.loaded_segments (0x9ff98 : word) = Some W_9ff98.
Proof. vm_refl. Qed.
Lemma D_9ff98 : decode_any W_9ff98 = Some (Op ALU_SUB 22 22 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ff9c : bv 32 := 0x0784a503.
Lemma F_9ff9c : fetch_word Asan.M.loaded_segments (0x9ff9c : word) = Some W_9ff9c.
Proof. vm_refl. Qed.
Lemma D_9ff9c : decode_any W_9ff9c = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ffa0 : bv 32 := 0x40c9093b.
Lemma F_9ffa0 : fetch_word Asan.M.loaded_segments (0x9ffa0 : word) = Some W_9ffa0.
Proof. vm_refl. Qed.
Lemma D_9ffa0 : decode_any W_9ffa0 = Some (Op32 ALU_SUB 18 18 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ffa4 : bv 32 := 0x40d787b3.
Lemma F_9ffa4 : fetch_word Asan.M.loaded_segments (0x9ffa4 : word) = Some W_9ffa4.
Proof. vm_refl. Qed.
Lemma D_9ffa4 : decode_any W_9ffa4 = Some (Op ALU_SUB 15 15 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ffa8 : bv 32 := 0x00f73023.
Lemma F_9ffa8 : fetch_word Asan.M.loaded_segments (0x9ffa8 : word) = Some W_9ffa8.
Proof. vm_refl. Qed.
Lemma D_9ffa8 : decode_any W_9ffa8 = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ffac : bv 32 := 0x04200893.
Lemma F_9ffac : fetch_word Asan.M.loaded_segments (0x9ffac : word) = Some W_9ffac.
Proof. vm_refl. Qed.
Lemma D_9ffac : decode_any W_9ffac = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ffb0 : bv 32 := 0x00090613.
Lemma F_9ffb0 : fetch_word Asan.M.loaded_segments (0x9ffb0 : word) = Some W_9ffb0.
Proof. vm_refl. Qed.
Lemma D_9ffb0 : decode_any W_9ffb0 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ffb4 : bv 32 := 0x00000073.
Lemma F_9ffb4 : fetch_word Asan.M.loaded_segments (0x9ffb4 : word) = Some W_9ffb4.
Proof. vm_refl. Qed.
Lemma D_9ffb4 : decode_any W_9ffb4 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_9ffb4 : is_ecall W_9ffb4 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_9ffb8 : bv 32 := 0xca5fa0ef.
Lemma F_9ffb8 : fetch_word Asan.M.loaded_segments (0x9ffb8 : word) = Some W_9ffb8.
Proof. vm_refl. Qed.
Lemma D_9ffb8 : decode_any W_9ffb8 = Some (Jal 1 2075812, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ffbc : bv 32 := 0x000a0993.
Lemma F_9ffbc : fetch_word Asan.M.loaded_segments (0x9ffbc : word) = Some W_9ffbc.
Proof. vm_refl. Qed.
Lemma D_9ffbc : decode_any W_9ffbc = Some (OpImm ALU_ADD 19 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ffc0 : bv 32 := 0xf7650ce3.
Lemma F_9ffc0 : fetch_word Asan.M.loaded_segments (0x9ffc0 : word) = Some W_9ffc0.
Proof. vm_refl. Qed.
Lemma D_9ffc0 : decode_any W_9ffc0 = Some (Branch BC_EQ 10 22 8056, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ffc4 : bv 32 := 0x02054c63.
Lemma F_9ffc4 : fetch_word Asan.M.loaded_segments (0x9ffc4 : word) = Some W_9ffc4.
Proof. vm_refl. Qed.
Lemma D_9ffc4 : decode_any W_9ffc4 = Some (Branch BC_LT 10 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ffc8 : bv 32 := 0x0089b583.
Lemma F_9ffc8 : fetch_word Asan.M.loaded_segments (0x9ffc8 : word) = Some W_9ffc8.
Proof. vm_refl. Qed.
Lemma D_9ffc8 : decode_any W_9ffc8 = Some (Load SZ8 true 11 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ffcc : bv 32 := 0x00a5b633.
Lemma F_9ffcc : fetch_word Asan.M.loaded_segments (0x9ffcc : word) = Some W_9ffcc.
Proof. vm_refl. Qed.
Lemma D_9ffcc : decode_any W_9ffcc = Some (Op ALU_SLTU 12 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ffd0 : bv 32 := 0x00461a13.
Lemma F_9ffd0 : fetch_word Asan.M.loaded_segments (0x9ffd0 : word) = Some W_9ffd0.
Proof. vm_refl. Qed.
Lemma D_9ffd0 : decode_any W_9ffd0 = Some (ShiftImm ALU_SLL 20 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ffd4 : bv 32 := 0x01498a33.
Lemma F_9ffd4 : fetch_word Asan.M.loaded_segments (0x9ffd4 : word) = Some W_9ffd4.
Proof. vm_refl. Qed.
Lemma D_9ffd4 : decode_any W_9ffd4 = Some (Op ALU_ADD 20 19 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ffd8 : bv 32 := 0x000a3703.
Lemma F_9ffd8 : fetch_word Asan.M.loaded_segments (0x9ffd8 : word) = Some W_9ffd8.
Proof. vm_refl. Qed.
Lemma D_9ffd8 : decode_any W_9ffd8 = Some (Load SZ8 true 14 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ffdc : bv 32 := 0x40c006b3.
Lemma F_9ffdc : fetch_word Asan.M.loaded_segments (0x9ffdc : word) = Some W_9ffdc.
Proof. vm_refl. Qed.
Lemma D_9ffdc : decode_any W_9ffdc = Some (Op ALU_SUB 13 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ffe0 : bv 32 := 0x00b6f6b3.
Lemma F_9ffe0 : fetch_word Asan.M.loaded_segments (0x9ffe0 : word) = Some W_9ffe0.
Proof. vm_refl. Qed.
Lemma D_9ffe0 : decode_any W_9ffe0 = Some (Op ALU_AND 13 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ffe4 : bv 32 := 0x40d506b3.
Lemma F_9ffe4 : fetch_word Asan.M.loaded_segments (0x9ffe4 : word) = Some W_9ffe4.
Proof. vm_refl. Qed.
Lemma D_9ffe4 : decode_any W_9ffe4 = Some (Op ALU_SUB 13 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ffe8 : bv 32 := 0x00d70733.
Lemma F_9ffe8 : fetch_word Asan.M.loaded_segments (0x9ffe8 : word) = Some W_9ffe8.
Proof. vm_refl. Qed.
Lemma D_9ffe8 : decode_any W_9ffe8 = Some (Op ALU_ADD 14 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ffec : bv 32 := 0x00ea3023.
Lemma F_9ffec : fetch_word Asan.M.loaded_segments (0x9ffec : word) = Some W_9ffec.
Proof. vm_refl. Qed.
Lemma D_9ffec : decode_any W_9ffec = Some (Store SZ8 20 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9fff0 : bv 32 := 0xf8a5fce3.
Lemma F_9fff0 : fetch_word Asan.M.loaded_segments (0x9fff0 : word) = Some W_9fff0.
Proof. vm_refl. Qed.
Lemma D_9fff0 : decode_any W_9fff0 = Some (Branch BC_GEU 11 10 8088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9fff4 : bv 32 := 0x01800713.
Lemma F_9fff4 : fetch_word Asan.M.loaded_segments (0x9fff4 : word) = Some W_9fff4.
Proof. vm_refl. Qed.
Lemma D_9fff4 : decode_any W_9fff4 = Some (OpImm ALU_ADD 14 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9fff8 : bv 32 := 0xf95ff06f.
Lemma F_9fff8 : fetch_word Asan.M.loaded_segments (0x9fff8 : word) = Some W_9fff8.
Proof. vm_refl. Qed.
Lemma D_9fff8 : decode_any W_9fff8 = Some (Jal 0 2097044, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9fffc : bv 32 := 0x00000513.
Lemma F_9fffc : fetch_word Asan.M.loaded_segments (0x9fffc : word) = Some W_9fffc.
Proof. vm_refl. Qed.
Lemma D_9fffc : decode_any W_9fffc = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a0000 : bv 32 := 0x0004a583.
Lemma F_a0000 : fetch_word Asan.M.loaded_segments (0xa0000 : word) = Some W_a0000.
Proof. vm_refl. Qed.
Lemma D_a0000 : decode_any W_a0000 = Some (Load SZ4 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a0004 : bv 32 := 0x0009091b.
Lemma F_a0004 : fetch_word Asan.M.loaded_segments (0xa0004 : word) = Some W_a0004.
Proof. vm_refl. Qed.
Lemma D_a0004 : decode_any W_a0004 = Some (OpImm32 18 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a0008 : bv 32 := 0x00200613.
Lemma F_a0008 : fetch_word Asan.M.loaded_segments (0xa0008 : word) = Some W_a0008.
Proof. vm_refl. Qed.
Lemma D_a0008 : decode_any W_a0008 = Some (OpImm ALU_ADD 12 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a000c : bv 32 := 0x0205e593.
Lemma F_a000c : fetch_word Asan.M.loaded_segments (0xa000c : word) = Some W_a000c.
Proof. vm_refl. Qed.
Lemma D_a000c : decode_any W_a000c = Some (OpImm ALU_OR 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a0010 : bv 32 := 0x00b4a023.
Lemma F_a0010 : fetch_word Asan.M.loaded_segments (0xa0010 : word) = Some W_a0010.
Proof. vm_refl. Qed.
Lemma D_a0010 : decode_any W_a0010 = Some (Store SZ4 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a0014 : bv 32 := 0x0204b023.
Lemma F_a0014 : fetch_word Asan.M.loaded_segments (0xa0014 : word) = Some W_a0014.
Proof. vm_refl. Qed.
Lemma D_a0014 : decode_any W_a0014 = Some (Store SZ8 9 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a0018 : bv 32 := 0x0204b423.
Lemma F_a0018 : fetch_word Asan.M.loaded_segments (0xa0018 : word) = Some W_a0018.
Proof. vm_refl. Qed.
Lemma D_a0018 : decode_any W_a0018 = Some (Store SZ8 9 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a001c : bv 32 := 0x0204bc23.
Lemma F_a001c : fetch_word Asan.M.loaded_segments (0xa001c : word) = Some W_a001c.
Proof. vm_refl. Qed.
Lemma D_a001c : decode_any W_a001c = Some (Store SZ8 9 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a0020 : bv 32 := 0xf2c90ae3.
Lemma F_a0020 : fetch_word Asan.M.loaded_segments (0xa0020 : word) = Some W_a0020.
Proof. vm_refl. Qed.
Lemma D_a0020 : decode_any W_a0020 = Some (Branch BC_EQ 18 12 7988, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a0024 : bv 32 := 0x0089b503.
Lemma F_a0024 : fetch_word Asan.M.loaded_segments (0xa0024 : word) = Some W_a0024.
Proof. vm_refl. Qed.
Lemma D_a0024 : decode_any W_a0024 = Some (Load SZ8 true 10 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a0028 : bv 32 := 0x40a40533.
Lemma F_a0028 : fetch_word Asan.M.loaded_segments (0xa0028 : word) = Some W_a0028.
Proof. vm_refl. Qed.
Lemma D_a0028 : decode_any W_a0028 = Some (Op ALU_SUB 10 8 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a002c : bv 32 := 0xf29ff06f.
Lemma F_a002c : fetch_word Asan.M.loaded_segments (0xa002c : word) = Some W_a002c.
Proof. vm_refl. Qed.
Lemma D_a002c : decode_any W_a002c = Some (Jal 0 2096936, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a0030 : bv 32 := 0xdc0fa0ef.
Lemma F_a0030 : fetch_word Asan.M.loaded_segments (0xa0030 : word) = Some W_a0030.
Proof. vm_refl. Qed.
Lemma D_a0030 : decode_any W_a0030 = Some (Jal 1 2074048, 4%Z).
Proof. vm_refl. Qed.
