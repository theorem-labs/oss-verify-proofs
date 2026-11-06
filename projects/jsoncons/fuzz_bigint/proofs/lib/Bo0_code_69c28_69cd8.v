(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_69c28 : bv 32 := 0x02850583.
Lemma F_69c28 : fetch_word AsanUbsan.M.loaded_segments (0x69c28 : word) = Some W_69c28.
Proof. vm_refl. Qed.
Lemma D_69c28 : decode_any W_69c28 = Some (Load SZ1 true 11 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_69c2c : bv 32 := 0x0230000f.
Lemma F_69c2c : fetch_word AsanUbsan.M.loaded_segments (0x69c2c : word) = Some W_69c2c.
Proof. vm_refl. Qed.
Lemma D_69c2c : decode_any W_69c2c = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_69c30 : bv 32 := 0x02058c63.
Lemma F_69c30 : fetch_word AsanUbsan.M.loaded_segments (0x69c30 : word) = Some W_69c30.
Proof. vm_refl. Qed.
Lemma D_69c30 : decode_any W_69c30 = Some (Branch BC_EQ 11 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_69c34 : bv 32 := 0xff010113.
Lemma F_69c34 : fetch_word AsanUbsan.M.loaded_segments (0x69c34 : word) = Some W_69c34.
Proof. vm_refl. Qed.
Lemma D_69c34 : decode_any W_69c34 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_69c38 : bv 32 := 0x02053603.
Lemma F_69c38 : fetch_word AsanUbsan.M.loaded_segments (0x69c38 : word) = Some W_69c38.
Proof. vm_refl. Qed.
Lemma D_69c38 : decode_any W_69c38 = Some (Load SZ8 true 12 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_69c3c : bv 32 := 0x01853583.
Lemma F_69c3c : fetch_word AsanUbsan.M.loaded_segments (0x69c3c : word) = Some W_69c3c.
Proof. vm_refl. Qed.
Lemma D_69c3c : decode_any W_69c3c = Some (Load SZ8 true 11 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_69c40 : bv 32 := 0x00f10693.
Lemma F_69c40 : fetch_word AsanUbsan.M.loaded_segments (0x69c40 : word) = Some W_69c40.
Proof. vm_refl. Qed.
Lemma D_69c40 : decode_any W_69c40 = Some (OpImm ALU_ADD 13 2 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_69c44 : bv 32 := 0x00c6b633.
Lemma F_69c44 : fetch_word AsanUbsan.M.loaded_segments (0x69c44 : word) = Some W_69c44.
Proof. vm_refl. Qed.
Lemma D_69c44 : decode_any W_69c44 = Some (Op ALU_SLTU 12 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_69c48 : bv 32 := 0xfff64613.
Lemma F_69c48 : fetch_word AsanUbsan.M.loaded_segments (0x69c48 : word) = Some W_69c48.
Proof. vm_refl. Qed.
Lemma D_69c48 : decode_any W_69c48 = Some (OpImm ALU_XOR 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_69c4c : bv 32 := 0x00b6b6b3.
Lemma F_69c4c : fetch_word AsanUbsan.M.loaded_segments (0x69c4c : word) = Some W_69c4c.
Proof. vm_refl. Qed.
Lemma D_69c4c : decode_any W_69c4c = Some (Op ALU_SLTU 13 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_69c50 : bv 32 := 0x00d67633.
Lemma F_69c50 : fetch_word AsanUbsan.M.loaded_segments (0x69c50 : word) = Some W_69c50.
Proof. vm_refl. Qed.
Lemma D_69c50 : decode_any W_69c50 = Some (Op ALU_AND 12 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_69c54 : bv 32 := 0x01010113.
Lemma F_69c54 : fetch_word AsanUbsan.M.loaded_segments (0x69c54 : word) = Some W_69c54.
Proof. vm_refl. Qed.
Lemma D_69c54 : decode_any W_69c54 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_69c58 : bv 32 := 0x00061463.
Lemma F_69c58 : fetch_word AsanUbsan.M.loaded_segments (0x69c58 : word) = Some W_69c58.
Proof. vm_refl. Qed.
Lemma D_69c58 : decode_any W_69c58 = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_69c5c : bv 32 := 0x00853583.
Lemma F_69c5c : fetch_word AsanUbsan.M.loaded_segments (0x69c5c : word) = Some W_69c5c.
Proof. vm_refl. Qed.
Lemma D_69c5c : decode_any W_69c5c = Some (Load SZ8 true 11 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_69c60 : bv 32 := 0x00058513.
Lemma F_69c60 : fetch_word AsanUbsan.M.loaded_segments (0x69c60 : word) = Some W_69c60.
Proof. vm_refl. Qed.
Lemma D_69c60 : decode_any W_69c60 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_69c64 : bv 32 := 0x00008067.
Lemma F_69c64 : fetch_word AsanUbsan.M.loaded_segments (0x69c64 : word) = Some W_69c64.
Proof. vm_refl. Qed.
Lemma D_69c64 : decode_any W_69c64 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_69c68 : bv 32 := 0x00853583.
Lemma F_69c68 : fetch_word AsanUbsan.M.loaded_segments (0x69c68 : word) = Some W_69c68.
Proof. vm_refl. Qed.
Lemma D_69c68 : decode_any W_69c68 = Some (Load SZ8 true 11 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_69c6c : bv 32 := 0x01053503.
Lemma F_69c6c : fetch_word AsanUbsan.M.loaded_segments (0x69c6c : word) = Some W_69c6c.
Proof. vm_refl. Qed.
Lemma D_69c6c : decode_any W_69c6c = Some (Load SZ8 true 10 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_69c70 : bv 32 := 0x00b53533.
Lemma F_69c70 : fetch_word AsanUbsan.M.loaded_segments (0x69c70 : word) = Some W_69c70.
Proof. vm_refl. Qed.
Lemma D_69c70 : decode_any W_69c70 = Some (Op ALU_SLTU 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_69c74 : bv 32 := 0x40a00533.
Lemma F_69c74 : fetch_word AsanUbsan.M.loaded_segments (0x69c74 : word) = Some W_69c74.
Proof. vm_refl. Qed.
Lemma D_69c74 : decode_any W_69c74 = Some (Op ALU_SUB 10 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_69c78 : bv 32 := 0x00b57533.
Lemma F_69c78 : fetch_word AsanUbsan.M.loaded_segments (0x69c78 : word) = Some W_69c78.
Proof. vm_refl. Qed.
Lemma D_69c78 : decode_any W_69c78 = Some (Op ALU_AND 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_69c7c : bv 32 := 0x00008067.
Lemma F_69c7c : fetch_word AsanUbsan.M.loaded_segments (0x69c7c : word) = Some W_69c7c.
Proof. vm_refl. Qed.
Lemma D_69c7c : decode_any W_69c7c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_69c80 : bv 32 := 0x02850583.
Lemma F_69c80 : fetch_word AsanUbsan.M.loaded_segments (0x69c80 : word) = Some W_69c80.
Proof. vm_refl. Qed.
Lemma D_69c80 : decode_any W_69c80 = Some (Load SZ1 true 11 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_69c84 : bv 32 := 0x0230000f.
Lemma F_69c84 : fetch_word AsanUbsan.M.loaded_segments (0x69c84 : word) = Some W_69c84.
Proof. vm_refl. Qed.
Lemma D_69c84 : decode_any W_69c84 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_69c88 : bv 32 := 0x02058c63.
Lemma F_69c88 : fetch_word AsanUbsan.M.loaded_segments (0x69c88 : word) = Some W_69c88.
Proof. vm_refl. Qed.
Lemma D_69c88 : decode_any W_69c88 = Some (Branch BC_EQ 11 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_69c8c : bv 32 := 0xff010113.
Lemma F_69c8c : fetch_word AsanUbsan.M.loaded_segments (0x69c8c : word) = Some W_69c8c.
Proof. vm_refl. Qed.
Lemma D_69c8c : decode_any W_69c8c = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_69c90 : bv 32 := 0x02053583.
Lemma F_69c90 : fetch_word AsanUbsan.M.loaded_segments (0x69c90 : word) = Some W_69c90.
Proof. vm_refl. Qed.
Lemma D_69c90 : decode_any W_69c90 = Some (Load SZ8 true 11 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_69c94 : bv 32 := 0x01853603.
Lemma F_69c94 : fetch_word AsanUbsan.M.loaded_segments (0x69c94 : word) = Some W_69c94.
Proof. vm_refl. Qed.
Lemma D_69c94 : decode_any W_69c94 = Some (Load SZ8 true 12 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_69c98 : bv 32 := 0x00f10693.
Lemma F_69c98 : fetch_word AsanUbsan.M.loaded_segments (0x69c98 : word) = Some W_69c98.
Proof. vm_refl. Qed.
Lemma D_69c98 : decode_any W_69c98 = Some (OpImm ALU_ADD 13 2 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_69c9c : bv 32 := 0x00b6b733.
Lemma F_69c9c : fetch_word AsanUbsan.M.loaded_segments (0x69c9c : word) = Some W_69c9c.
Proof. vm_refl. Qed.
Lemma D_69c9c : decode_any W_69c9c = Some (Op ALU_SLTU 14 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_69ca0 : bv 32 := 0xfff74713.
Lemma F_69ca0 : fetch_word AsanUbsan.M.loaded_segments (0x69ca0 : word) = Some W_69ca0.
Proof. vm_refl. Qed.
Lemma D_69ca0 : decode_any W_69ca0 = Some (OpImm ALU_XOR 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_69ca4 : bv 32 := 0x00c6b633.
Lemma F_69ca4 : fetch_word AsanUbsan.M.loaded_segments (0x69ca4 : word) = Some W_69ca4.
Proof. vm_refl. Qed.
Lemma D_69ca4 : decode_any W_69ca4 = Some (Op ALU_SLTU 12 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_69ca8 : bv 32 := 0x00c77633.
Lemma F_69ca8 : fetch_word AsanUbsan.M.loaded_segments (0x69ca8 : word) = Some W_69ca8.
Proof. vm_refl. Qed.
Lemma D_69ca8 : decode_any W_69ca8 = Some (Op ALU_AND 12 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_69cac : bv 32 := 0x01010113.
Lemma F_69cac : fetch_word AsanUbsan.M.loaded_segments (0x69cac : word) = Some W_69cac.
Proof. vm_refl. Qed.
Lemma D_69cac : decode_any W_69cac = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_69cb0 : bv 32 := 0x00061463.
Lemma F_69cb0 : fetch_word AsanUbsan.M.loaded_segments (0x69cb0 : word) = Some W_69cb0.
Proof. vm_refl. Qed.
Lemma D_69cb0 : decode_any W_69cb0 = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_69cb4 : bv 32 := 0x01053583.
Lemma F_69cb4 : fetch_word AsanUbsan.M.loaded_segments (0x69cb4 : word) = Some W_69cb4.
Proof. vm_refl. Qed.
Lemma D_69cb4 : decode_any W_69cb4 = Some (Load SZ8 true 11 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_69cb8 : bv 32 := 0x00058513.
Lemma F_69cb8 : fetch_word AsanUbsan.M.loaded_segments (0x69cb8 : word) = Some W_69cb8.
Proof. vm_refl. Qed.
Lemma D_69cb8 : decode_any W_69cb8 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_69cbc : bv 32 := 0x00008067.
Lemma F_69cbc : fetch_word AsanUbsan.M.loaded_segments (0x69cbc : word) = Some W_69cbc.
Proof. vm_refl. Qed.
Lemma D_69cbc : decode_any W_69cbc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_69cc0 : bv 32 := 0x00853583.
Lemma F_69cc0 : fetch_word AsanUbsan.M.loaded_segments (0x69cc0 : word) = Some W_69cc0.
Proof. vm_refl. Qed.
Lemma D_69cc0 : decode_any W_69cc0 = Some (Load SZ8 true 11 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_69cc4 : bv 32 := 0x01053503.
Lemma F_69cc4 : fetch_word AsanUbsan.M.loaded_segments (0x69cc4 : word) = Some W_69cc4.
Proof. vm_refl. Qed.
Lemma D_69cc4 : decode_any W_69cc4 = Some (Load SZ8 true 10 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_69cc8 : bv 32 := 0x00b535b3.
Lemma F_69cc8 : fetch_word AsanUbsan.M.loaded_segments (0x69cc8 : word) = Some W_69cc8.
Proof. vm_refl. Qed.
Lemma D_69cc8 : decode_any W_69cc8 = Some (Op ALU_SLTU 11 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_69ccc : bv 32 := 0x40b005b3.
Lemma F_69ccc : fetch_word AsanUbsan.M.loaded_segments (0x69ccc : word) = Some W_69ccc.
Proof. vm_refl. Qed.
Lemma D_69ccc : decode_any W_69ccc = Some (Op ALU_SUB 11 0 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_69cd0 : bv 32 := 0x00a5f533.
Lemma F_69cd0 : fetch_word AsanUbsan.M.loaded_segments (0x69cd0 : word) = Some W_69cd0.
Proof. vm_refl. Qed.
Lemma D_69cd0 : decode_any W_69cd0 = Some (Op ALU_AND 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_69cd4 : bv 32 := 0x00008067.
Lemma F_69cd4 : fetch_word AsanUbsan.M.loaded_segments (0x69cd4 : word) = Some W_69cd4.
Proof. vm_refl. Qed.
Lemma D_69cd4 : decode_any W_69cd4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
