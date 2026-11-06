(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_13b7cc : bv 32 := 0x0284b503.
Lemma F_13b7cc : fetch_word Asan.M.loaded_segments (0x13b810 : word) = Some W_13b7cc.
Proof. vm_refl. Qed.
Lemma D_13b7cc : decode_any W_13b7cc = Some (Load SZ8 true 10 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_13b7d0 : bv 32 := 0x0384b603.
Lemma F_13b7d0 : fetch_word Asan.M.loaded_segments (0x13b814 : word) = Some W_13b7d0.
Proof. vm_refl. Qed.
Lemma D_13b7d0 : decode_any W_13b7d0 = Some (Load SZ8 true 12 9 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_13b7d4 : bv 32 := 0x40c50b33.
Lemma F_13b7d4 : fetch_word Asan.M.loaded_segments (0x13b818 : word) = Some W_13b7d4.
Proof. vm_refl. Qed.
Lemma D_13b7d4 : decode_any W_13b7d4 = Some (Op ALU_SUB 22 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_13b7d8 : bv 32 := 0x00c546b3.
Lemma F_13b7d8 : fetch_word Asan.M.loaded_segments (0x13b81c : word) = Some W_13b7d8.
Proof. vm_refl. Qed.
Lemma D_13b7d8 : decode_any W_13b7d8 = Some (Op ALU_XOR 13 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_13b7dc : bv 32 := 0x00c13423.
Lemma F_13b7dc : fetch_word Asan.M.loaded_segments (0x13b820 : word) = Some W_13b7dc.
Proof. vm_refl. Qed.
Lemma D_13b7dc : decode_any W_13b7dc = Some (Store SZ8 2 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_13b7e0 : bv 32 := 0x01613823.
Lemma F_13b7e0 : fetch_word Asan.M.loaded_segments (0x13b824 : word) = Some W_13b7e0.
Proof. vm_refl. Qed.
Lemma D_13b7e0 : decode_any W_13b7e0 = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_13b7e4 : bv 32 := 0x00b13c23.
Lemma F_13b7e4 : fetch_word Asan.M.loaded_segments (0x13b828 : word) = Some W_13b7e4.
Proof. vm_refl. Qed.
Lemma D_13b7e4 : decode_any W_13b7e4 = Some (Store SZ8 2 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_13b7e8 : bv 32 := 0x02813023.
Lemma F_13b7e8 : fetch_word Asan.M.loaded_segments (0x13b82c : word) = Some W_13b7e8.
Proof. vm_refl. Qed.
Lemma D_13b7e8 : decode_any W_13b7e8 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_13b7ec : bv 32 := 0x008b0b33.
Lemma F_13b7ec : fetch_word Asan.M.loaded_segments (0x13b830 : word) = Some W_13b7ec.
Proof. vm_refl. Qed.
Lemma D_13b7ec : decode_any W_13b7ec = Some (Op ALU_ADD 22 22 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_13b7f0 : bv 32 := 0x00d03933.
Lemma F_13b7f0 : fetch_word Asan.M.loaded_segments (0x13b834 : word) = Some W_13b7f0.
Proof. vm_refl. Qed.
Lemma D_13b7f0 : decode_any W_13b7f0 = Some (Op ALU_SLTU 18 0 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_13b7f4 : bv 32 := 0x00c50663.
Lemma F_13b7f4 : fetch_word Asan.M.loaded_segments (0x13b838 : word) = Some W_13b7f4.
Proof. vm_refl. Qed.
Lemma D_13b7f4 : decode_any W_13b7f4 = Some (Branch BC_EQ 10 12 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_13b7f8 : bv 32 := 0x00810993.
Lemma F_13b7f8 : fetch_word Asan.M.loaded_segments (0x13b83c : word) = Some W_13b7f8.
Proof. vm_refl. Qed.
Lemma D_13b7f8 : decode_any W_13b7f8 = Some (OpImm ALU_ADD 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_13b7fc : bv 32 := 0x0080006f.
Lemma F_13b7fc : fetch_word Asan.M.loaded_segments (0x13b840 : word) = Some W_13b7fc.
Proof. vm_refl. Qed.
Lemma D_13b7fc : decode_any W_13b7fc = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_13b800 : bv 32 := 0x01810993.
Lemma F_13b800 : fetch_word Asan.M.loaded_segments (0x13b844 : word) = Some W_13b800.
Proof. vm_refl. Qed.
Lemma D_13b800 : decode_any W_13b800 = Some (OpImm ALU_ADD 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_13b804 : bv 32 := 0x0784a503.
Lemma F_13b804 : fetch_word Asan.M.loaded_segments (0x13b848 : word) = Some W_13b804.
Proof. vm_refl. Qed.
Lemma D_13b804 : decode_any W_13b804 = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_13b808 : bv 32 := 0x00190913.
Lemma F_13b808 : fetch_word Asan.M.loaded_segments (0x13b84c : word) = Some W_13b808.
Proof. vm_refl. Qed.
Lemma D_13b808 : decode_any W_13b808 = Some (OpImm ALU_ADD 18 18 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_13b80c : bv 32 := 0x04200893.
Lemma F_13b80c : fetch_word Asan.M.loaded_segments (0x13b850 : word) = Some W_13b80c.
Proof. vm_refl. Qed.
Lemma D_13b80c : decode_any W_13b80c = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

Definition W_13b810 : bv 32 := 0x00098593.
Lemma F_13b810 : fetch_word Asan.M.loaded_segments (0x13b854 : word) = Some W_13b810.
Proof. vm_refl. Qed.
Lemma D_13b810 : decode_any W_13b810 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13b814 : bv 32 := 0x00090613.
Lemma F_13b814 : fetch_word Asan.M.loaded_segments (0x13b858 : word) = Some W_13b814.
Proof. vm_refl. Qed.
Lemma D_13b814 : decode_any W_13b814 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13b81c : bv 32 := 0x971f80ef.
Lemma F_13b81c : fetch_word Asan.M.loaded_segments (0x13b860 : word) = Some W_13b81c.
Proof. vm_refl. Qed.
Lemma D_13b81c : decode_any W_13b81c = Some (Jal 1 2066800, 4%Z).
Proof. vm_refl. Qed.

Definition W_13b820 : bv 32 := 0x09651863.
Lemma F_13b820 : fetch_word Asan.M.loaded_segments (0x13b864 : word) = Some W_13b820.
Proof. vm_refl. Qed.
Lemma D_13b820 : decode_any W_13b820 = Some (Branch BC_NE 10 22 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_13b874 : bv 32 := 0x00800713.
Lemma F_13b874 : fetch_word Asan.M.loaded_segments (0x13b8b8 : word) = Some W_13b874.
Proof. vm_refl. Qed.
Lemma D_13b874 : decode_any W_13b874 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_13b878 : bv 32 := 0x000a0593.
Lemma F_13b878 : fetch_word Asan.M.loaded_segments (0x13b8bc : word) = Some W_13b878.
Proof. vm_refl. Qed.
Lemma D_13b878 : decode_any W_13b878 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13b87c : bv 32 := 0x00e98733.
Lemma F_13b87c : fetch_word Asan.M.loaded_segments (0x13b8c0 : word) = Some W_13b87c.
Proof. vm_refl. Qed.
Lemma D_13b87c : decode_any W_13b87c = Some (Op ALU_ADD 14 19 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_13b880 : bv 32 := 0x00073783.
Lemma F_13b880 : fetch_word Asan.M.loaded_segments (0x13b8c4 : word) = Some W_13b880.
Proof. vm_refl. Qed.
Lemma D_13b880 : decode_any W_13b880 = Some (Load SZ8 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13b884 : bv 32 := 0x40ab0b33.
Lemma F_13b884 : fetch_word Asan.M.loaded_segments (0x13b8c8 : word) = Some W_13b884.
Proof. vm_refl. Qed.
Lemma D_13b884 : decode_any W_13b884 = Some (Op ALU_SUB 22 22 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_13b888 : bv 32 := 0x0784a503.
Lemma F_13b888 : fetch_word Asan.M.loaded_segments (0x13b8cc : word) = Some W_13b888.
Proof. vm_refl. Qed.
Lemma D_13b888 : decode_any W_13b888 = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_13b88c : bv 32 := 0x40c9093b.
Lemma F_13b88c : fetch_word Asan.M.loaded_segments (0x13b8d0 : word) = Some W_13b88c.
Proof. vm_refl. Qed.
Lemma D_13b88c : decode_any W_13b88c = Some (Op32 ALU_SUB 18 18 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_13b890 : bv 32 := 0x40d787b3.
Lemma F_13b890 : fetch_word Asan.M.loaded_segments (0x13b8d4 : word) = Some W_13b890.
Proof. vm_refl. Qed.
Lemma D_13b890 : decode_any W_13b890 = Some (Op ALU_SUB 15 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_13b894 : bv 32 := 0x00f73023.
Lemma F_13b894 : fetch_word Asan.M.loaded_segments (0x13b8d8 : word) = Some W_13b894.
Proof. vm_refl. Qed.
Lemma D_13b894 : decode_any W_13b894 = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13b898 : bv 32 := 0x04200893.
Lemma F_13b898 : fetch_word Asan.M.loaded_segments (0x13b8dc : word) = Some W_13b898.
Proof. vm_refl. Qed.
Lemma D_13b898 : decode_any W_13b898 = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

Definition W_13b89c : bv 32 := 0x00090613.
Lemma F_13b89c : fetch_word Asan.M.loaded_segments (0x13b8e0 : word) = Some W_13b89c.
Proof. vm_refl. Qed.
Lemma D_13b89c : decode_any W_13b89c = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13b8a4 : bv 32 := 0x8e9f80ef.
Lemma F_13b8a4 : fetch_word Asan.M.loaded_segments (0x13b8e8 : word) = Some W_13b8a4.
Proof. vm_refl. Qed.
Lemma D_13b8a4 : decode_any W_13b8a4 = Some (Jal 1 2066664, 4%Z).
Proof. vm_refl. Qed.

Definition W_13b8a8 : bv 32 := 0x000a0993.
Lemma F_13b8a8 : fetch_word Asan.M.loaded_segments (0x13b8ec : word) = Some W_13b8a8.
Proof. vm_refl. Qed.
Lemma D_13b8a8 : decode_any W_13b8a8 = Some (OpImm ALU_ADD 19 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13b8ac : bv 32 := 0xf7650ce3.
Lemma F_13b8ac : fetch_word Asan.M.loaded_segments (0x13b8f0 : word) = Some W_13b8ac.
Proof. vm_refl. Qed.
Lemma D_13b8ac : decode_any W_13b8ac = Some (Branch BC_EQ 10 22 8056, 4%Z).
Proof. vm_refl. Qed.

Definition W_13b8b0 : bv 32 := 0x02054c63.
Lemma F_13b8b0 : fetch_word Asan.M.loaded_segments (0x13b8f4 : word) = Some W_13b8b0.
Proof. vm_refl. Qed.
Lemma D_13b8b0 : decode_any W_13b8b0 = Some (Branch BC_LT 10 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_13b8b4 : bv 32 := 0x0089b583.
Lemma F_13b8b4 : fetch_word Asan.M.loaded_segments (0x13b8f8 : word) = Some W_13b8b4.
Proof. vm_refl. Qed.
Lemma D_13b8b4 : decode_any W_13b8b4 = Some (Load SZ8 true 11 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_13b8b8 : bv 32 := 0x00a5b633.
Lemma F_13b8b8 : fetch_word Asan.M.loaded_segments (0x13b8fc : word) = Some W_13b8b8.
Proof. vm_refl. Qed.
Lemma D_13b8b8 : decode_any W_13b8b8 = Some (Op ALU_SLTU 12 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_13b8bc : bv 32 := 0x00461a13.
Lemma F_13b8bc : fetch_word Asan.M.loaded_segments (0x13b900 : word) = Some W_13b8bc.
Proof. vm_refl. Qed.
Lemma D_13b8bc : decode_any W_13b8bc = Some (ShiftImm ALU_SLL 20 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_13b8c0 : bv 32 := 0x01498a33.
Lemma F_13b8c0 : fetch_word Asan.M.loaded_segments (0x13b904 : word) = Some W_13b8c0.
Proof. vm_refl. Qed.
Lemma D_13b8c0 : decode_any W_13b8c0 = Some (Op ALU_ADD 20 19 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_13b8c4 : bv 32 := 0x000a3703.
Lemma F_13b8c4 : fetch_word Asan.M.loaded_segments (0x13b908 : word) = Some W_13b8c4.
Proof. vm_refl. Qed.
Lemma D_13b8c4 : decode_any W_13b8c4 = Some (Load SZ8 true 14 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13b8c8 : bv 32 := 0x40c006b3.
Lemma F_13b8c8 : fetch_word Asan.M.loaded_segments (0x13b90c : word) = Some W_13b8c8.
Proof. vm_refl. Qed.
Lemma D_13b8c8 : decode_any W_13b8c8 = Some (Op ALU_SUB 13 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_13b8cc : bv 32 := 0x00b6f6b3.
Lemma F_13b8cc : fetch_word Asan.M.loaded_segments (0x13b910 : word) = Some W_13b8cc.
Proof. vm_refl. Qed.
Lemma D_13b8cc : decode_any W_13b8cc = Some (Op ALU_AND 13 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_13b8d0 : bv 32 := 0x40d506b3.
Lemma F_13b8d0 : fetch_word Asan.M.loaded_segments (0x13b914 : word) = Some W_13b8d0.
Proof. vm_refl. Qed.
Lemma D_13b8d0 : decode_any W_13b8d0 = Some (Op ALU_SUB 13 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_13b8d4 : bv 32 := 0x00d70733.
Lemma F_13b8d4 : fetch_word Asan.M.loaded_segments (0x13b918 : word) = Some W_13b8d4.
Proof. vm_refl. Qed.
Lemma D_13b8d4 : decode_any W_13b8d4 = Some (Op ALU_ADD 14 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_13b8d8 : bv 32 := 0x00ea3023.
Lemma F_13b8d8 : fetch_word Asan.M.loaded_segments (0x13b91c : word) = Some W_13b8d8.
Proof. vm_refl. Qed.
Lemma D_13b8d8 : decode_any W_13b8d8 = Some (Store SZ8 20 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13b8dc : bv 32 := 0xf8a5fce3.
Lemma F_13b8dc : fetch_word Asan.M.loaded_segments (0x13b920 : word) = Some W_13b8dc.
Proof. vm_refl. Qed.
Lemma D_13b8dc : decode_any W_13b8dc = Some (Branch BC_GEU 11 10 8088, 4%Z).
Proof. vm_refl. Qed.

Definition W_13b8e0 : bv 32 := 0x01800713.
Lemma F_13b8e0 : fetch_word Asan.M.loaded_segments (0x13b924 : word) = Some W_13b8e0.
Proof. vm_refl. Qed.
Lemma D_13b8e0 : decode_any W_13b8e0 = Some (OpImm ALU_ADD 14 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_13b8e4 : bv 32 := 0xf95ff06f.
Lemma F_13b8e4 : fetch_word Asan.M.loaded_segments (0x13b928 : word) = Some W_13b8e4.
Proof. vm_refl. Qed.
Lemma D_13b8e4 : decode_any W_13b8e4 = Some (Jal 0 2097044, 4%Z).
Proof. vm_refl. Qed.

