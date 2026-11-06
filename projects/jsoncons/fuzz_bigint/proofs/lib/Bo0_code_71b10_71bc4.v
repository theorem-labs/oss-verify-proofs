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

Definition W_71b10 : bv 32 := 0xff010113.
Lemma F_71b10 : fetch_word AsanUbsan.M.loaded_segments (0x71b10 : word) = Some W_71b10.
Proof. vm_refl. Qed.
Lemma D_71b10 : decode_any W_71b10 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_71b14 : bv 32 := 0x00113423.
Lemma F_71b14 : fetch_word AsanUbsan.M.loaded_segments (0x71b14 : word) = Some W_71b14.
Proof. vm_refl. Qed.
Lemma D_71b14 : decode_any W_71b14 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_71b18 : bv 32 := 0x00058693.
Lemma F_71b18 : fetch_word AsanUbsan.M.loaded_segments (0x71b18 : word) = Some W_71b18.
Proof. vm_refl. Qed.
Lemma D_71b18 : decode_any W_71b18 = Some (OpImm ALU_ADD 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71b1c : bv 32 := 0x00100713.
Lemma F_71b1c : fetch_word AsanUbsan.M.loaded_segments (0x71b1c : word) = Some W_71b1c.
Proof. vm_refl. Qed.
Lemma D_71b1c : decode_any W_71b1c = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_71b20 : bv 32 := 0x02871713.
Lemma F_71b20 : fetch_word AsanUbsan.M.loaded_segments (0x71b20 : word) = Some W_71b20.
Proof. vm_refl. Qed.
Lemma D_71b20 : decode_any W_71b20 = Some (ShiftImm ALU_SLL 14 14 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_71b24 : bv 32 := 0x00170593.
Lemma F_71b24 : fetch_word AsanUbsan.M.loaded_segments (0x71b24 : word) = Some W_71b24.
Proof. vm_refl. Qed.
Lemma D_71b24 : decode_any W_71b24 = Some (OpImm ALU_ADD 11 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_71b28 : bv 32 := 0x08b6f263.
Lemma F_71b28 : fetch_word AsanUbsan.M.loaded_segments (0x71b28 : word) = Some W_71b28.
Proof. vm_refl. Qed.
Lemma D_71b28 : decode_any W_71b28 = Some (Branch BC_GEU 13 11 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_71b2c : bv 32 := 0x00000593.
Lemma F_71b2c : fetch_word AsanUbsan.M.loaded_segments (0x71b2c : word) = Some W_71b2c.
Proof. vm_refl. Qed.
Lemma D_71b2c : decode_any W_71b2c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71b30 : bv 32 := 0x00d50733.
Lemma F_71b30 : fetch_word AsanUbsan.M.loaded_segments (0x71b30 : word) = Some W_71b30.
Proof. vm_refl. Qed.
Lemma D_71b30 : decode_any W_71b30 = Some (Op ALU_ADD 14 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_71b34 : bv 32 := 0x00750793.
Lemma F_71b34 : fetch_word AsanUbsan.M.loaded_segments (0x71b34 : word) = Some W_71b34.
Proof. vm_refl. Qed.
Lemma D_71b34 : decode_any W_71b34 = Some (OpImm ALU_ADD 15 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_71b38 : bv 32 := 0xff87f793.
Lemma F_71b38 : fetch_word AsanUbsan.M.loaded_segments (0x71b38 : word) = Some W_71b38.
Proof. vm_refl. Qed.
Lemma D_71b38 : decode_any W_71b38 = Some (OpImm ALU_AND 15 15 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_71b3c : bv 32 := 0xff877613.
Lemma F_71b3c : fetch_word AsanUbsan.M.loaded_segments (0x71b3c : word) = Some W_71b3c.
Proof. vm_refl. Qed.
Lemma D_71b3c : decode_any W_71b3c = Some (OpImm ALU_AND 12 14 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_71b40 : bv 32 := 0x02f57463.
Lemma F_71b40 : fetch_word AsanUbsan.M.loaded_segments (0x71b40 : word) = Some W_71b40.
Proof. vm_refl. Qed.
Lemma D_71b40 : decode_any W_71b40 = Some (Branch BC_GEU 10 15 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_71b44 : bv 32 := 0x02068263.
Lemma F_71b44 : fetch_word AsanUbsan.M.loaded_segments (0x71b44 : word) = Some W_71b44.
Proof. vm_refl. Qed.
Lemma D_71b44 : decode_any W_71b44 = Some (Branch BC_EQ 13 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_71b48 : bv 32 := 0x00000593.
Lemma F_71b48 : fetch_word AsanUbsan.M.loaded_segments (0x71b48 : word) = Some W_71b48.
Proof. vm_refl. Qed.
Lemma D_71b48 : decode_any W_71b48 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71b4c : bv 32 := 0x00150693.
Lemma F_71b4c : fetch_word AsanUbsan.M.loaded_segments (0x71b4c : word) = Some W_71b4c.
Proof. vm_refl. Qed.
Lemma D_71b4c : decode_any W_71b4c = Some (OpImm ALU_ADD 13 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_71b50 : bv 32 := 0x00068813.
Lemma F_71b50 : fetch_word AsanUbsan.M.loaded_segments (0x71b50 : word) = Some W_71b50.
Proof. vm_refl. Qed.
Lemma D_71b50 : decode_any W_71b50 = Some (OpImm ALU_ADD 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71b54 : bv 32 := 0xfff6c683.
Lemma F_71b54 : fetch_word AsanUbsan.M.loaded_segments (0x71b54 : word) = Some W_71b54.
Proof. vm_refl. Qed.
Lemma D_71b54 : decode_any W_71b54 = Some (Load SZ1 false 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_71b58 : bv 32 := 0x00d5e5b3.
Lemma F_71b58 : fetch_word AsanUbsan.M.loaded_segments (0x71b58 : word) = Some W_71b58.
Proof. vm_refl. Qed.
Lemma D_71b58 : decode_any W_71b58 = Some (Op ALU_OR 11 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_71b5c : bv 32 := 0x00f87663.
Lemma F_71b5c : fetch_word AsanUbsan.M.loaded_segments (0x71b5c : word) = Some W_71b5c.
Proof. vm_refl. Qed.
Lemma D_71b5c : decode_any W_71b5c = Some (Branch BC_GEU 16 15 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_71b60 : bv 32 := 0x00180693.
Lemma F_71b60 : fetch_word AsanUbsan.M.loaded_segments (0x71b60 : word) = Some W_71b60.
Proof. vm_refl. Qed.
Lemma D_71b60 : decode_any W_71b60 = Some (OpImm ALU_ADD 13 16 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_71b64 : bv 32 := 0xfee866e3.
Lemma F_71b64 : fetch_word AsanUbsan.M.loaded_segments (0x71b64 : word) = Some W_71b64.
Proof. vm_refl. Qed.
Lemma D_71b64 : decode_any W_71b64 = Some (Branch BC_LTU 16 14 8172, 4%Z).
Proof. vm_refl. Qed.

Definition W_71b68 : bv 32 := 0x00c7fa63.
Lemma F_71b68 : fetch_word AsanUbsan.M.loaded_segments (0x71b68 : word) = Some W_71b68.
Proof. vm_refl. Qed.
Lemma D_71b68 : decode_any W_71b68 = Some (Branch BC_GEU 15 12 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_71b6c : bv 32 := 0x0007b683.
Lemma F_71b6c : fetch_word AsanUbsan.M.loaded_segments (0x71b6c : word) = Some W_71b6c.
Proof. vm_refl. Qed.
Lemma D_71b6c : decode_any W_71b6c = Some (Load SZ8 true 13 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71b70 : bv 32 := 0x00878793.
Lemma F_71b70 : fetch_word AsanUbsan.M.loaded_segments (0x71b70 : word) = Some W_71b70.
Proof. vm_refl. Qed.
Lemma D_71b70 : decode_any W_71b70 = Some (OpImm ALU_ADD 15 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_71b74 : bv 32 := 0x00b6e5b3.
Lemma F_71b74 : fetch_word AsanUbsan.M.loaded_segments (0x71b74 : word) = Some W_71b74.
Proof. vm_refl. Qed.
Lemma D_71b74 : decode_any W_71b74 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_71b78 : bv 32 := 0xfec7eae3.
Lemma F_71b78 : fetch_word AsanUbsan.M.loaded_segments (0x71b78 : word) = Some W_71b78.
Proof. vm_refl. Qed.
Lemma D_71b78 : decode_any W_71b78 = Some (Branch BC_LTU 15 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_71b7c : bv 32 := 0x02a66063.
Lemma F_71b7c : fetch_word AsanUbsan.M.loaded_segments (0x71b7c : word) = Some W_71b7c.
Proof. vm_refl. Qed.
Lemma D_71b7c : decode_any W_71b7c = Some (Branch BC_LTU 12 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_71b80 : bv 32 := 0x00e67e63.
Lemma F_71b80 : fetch_word AsanUbsan.M.loaded_segments (0x71b80 : word) = Some W_71b80.
Proof. vm_refl. Qed.
Lemma D_71b80 : decode_any W_71b80 = Some (Branch BC_GEU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_71b84 : bv 32 := 0x40c70733.
Lemma F_71b84 : fetch_word AsanUbsan.M.loaded_segments (0x71b84 : word) = Some W_71b84.
Proof. vm_refl. Qed.
Lemma D_71b84 : decode_any W_71b84 = Some (Op ALU_SUB 14 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_71b88 : bv 32 := 0x00064503.
Lemma F_71b88 : fetch_word AsanUbsan.M.loaded_segments (0x71b88 : word) = Some W_71b88.
Proof. vm_refl. Qed.
Lemma D_71b88 : decode_any W_71b88 = Some (Load SZ1 false 10 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71b8c : bv 32 := 0xfff70713.
Lemma F_71b8c : fetch_word AsanUbsan.M.loaded_segments (0x71b8c : word) = Some W_71b8c.
Proof. vm_refl. Qed.
Lemma D_71b8c : decode_any W_71b8c = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_71b90 : bv 32 := 0x00a5e5b3.
Lemma F_71b90 : fetch_word AsanUbsan.M.loaded_segments (0x71b90 : word) = Some W_71b90.
Proof. vm_refl. Qed.
Lemma D_71b90 : decode_any W_71b90 = Some (Op ALU_OR 11 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_71b94 : bv 32 := 0x00160613.
Lemma F_71b94 : fetch_word AsanUbsan.M.loaded_segments (0x71b94 : word) = Some W_71b94.
Proof. vm_refl. Qed.
Lemma D_71b94 : decode_any W_71b94 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_71b98 : bv 32 := 0xfe0718e3.
Lemma F_71b98 : fetch_word AsanUbsan.M.loaded_segments (0x71b98 : word) = Some W_71b98.
Proof. vm_refl. Qed.
Lemma D_71b98 : decode_any W_71b98 = Some (Branch BC_NE 14 0 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_71b9c : bv 32 := 0x0015b513.
Lemma F_71b9c : fetch_word AsanUbsan.M.loaded_segments (0x71b9c : word) = Some W_71b9c.
Proof. vm_refl. Qed.
Lemma D_71b9c : decode_any W_71b9c = Some (OpImm ALU_SLTU 10 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_71ba0 : bv 32 := 0x00813083.
Lemma F_71ba0 : fetch_word AsanUbsan.M.loaded_segments (0x71ba0 : word) = Some W_71ba0.
Proof. vm_refl. Qed.
Lemma D_71ba0 : decode_any W_71ba0 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_71ba4 : bv 32 := 0x01010113.
Lemma F_71ba4 : fetch_word AsanUbsan.M.loaded_segments (0x71ba4 : word) = Some W_71ba4.
Proof. vm_refl. Qed.
Lemma D_71ba4 : decode_any W_71ba4 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_71ba8 : bv 32 := 0x00008067.
Lemma F_71ba8 : fetch_word AsanUbsan.M.loaded_segments (0x71ba8 : word) = Some W_71ba8.
Proof. vm_refl. Qed.
Lemma D_71ba8 : decode_any W_71ba8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71bac : bv 32 := 0xfffa2517.
Lemma F_71bac : fetch_word AsanUbsan.M.loaded_segments (0x71bac : word) = Some W_71bac.
Proof. vm_refl. Qed.
Lemma D_71bac : decode_any W_71bac = Some (Auipc 10 1048482, 4%Z).
Proof. vm_refl. Qed.

Definition W_71bb0 : bv 32 := 0xfffa7597.
Lemma F_71bb0 : fetch_word AsanUbsan.M.loaded_segments (0x71bb0 : word) = Some W_71bb0.
Proof. vm_refl. Qed.
Lemma D_71bb0 : decode_any W_71bb0 = Some (Auipc 11 1048487, 4%Z).
Proof. vm_refl. Qed.

Definition W_71bb4 : bv 32 := 0xd0250513.
Lemma F_71bb4 : fetch_word AsanUbsan.M.loaded_segments (0x71bb4 : word) = Some W_71bb4.
Proof. vm_refl. Qed.
Lemma D_71bb4 : decode_any W_71bb4 = Some (OpImm ALU_ADD 10 10 3330, 4%Z).
Proof. vm_refl. Qed.

Definition W_71bb8 : bv 32 := 0x57058613.
Lemma F_71bb8 : fetch_word AsanUbsan.M.loaded_segments (0x71bb8 : word) = Some W_71bb8.
Proof. vm_refl. Qed.
Lemma D_71bb8 : decode_any W_71bb8 = Some (OpImm ALU_ADD 12 11 1392, 4%Z).
Proof. vm_refl. Qed.

Definition W_71bbc : bv 32 := 0x12b00593.
Lemma F_71bbc : fetch_word AsanUbsan.M.loaded_segments (0x71bbc : word) = Some W_71bbc.
Proof. vm_refl. Qed.
Lemma D_71bbc : decode_any W_71bbc = Some (OpImm ALU_ADD 11 0 299, 4%Z).
Proof. vm_refl. Qed.

Definition W_71bc0 : bv 32 := 0x728070ef.
Lemma F_71bc0 : fetch_word AsanUbsan.M.loaded_segments (0x71bc0 : word) = Some W_71bc0.
Proof. vm_refl. Qed.
Lemma D_71bc0 : decode_any W_71bc0 = Some (Jal 1 30504, 4%Z).
Proof. vm_refl. Qed.
