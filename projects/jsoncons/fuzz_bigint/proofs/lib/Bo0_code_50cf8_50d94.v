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

Definition W_50cf8 : bv 32 := 0x23d200ef.
Lemma F_50cf8 : fetch_word AsanUbsan.M.loaded_segments (0x50cf8 : word) = Some W_50cf8.
Proof. vm_refl. Qed.
Lemma D_50cf8 : decode_any W_50cf8 = Some (Jal 1 133692, 4%Z).
Proof. vm_refl. Qed.

Definition W_50cfc : bv 32 := 0x00150b93.
Lemma F_50cfc : fetch_word AsanUbsan.M.loaded_segments (0x50cfc : word) = Some W_50cfc.
Proof. vm_refl. Qed.
Lemma D_50cfc : decode_any W_50cfc = Some (OpImm ALU_ADD 23 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_50d00 : bv 32 := 0xfffb4513.
Lemma F_50d00 : fetch_word AsanUbsan.M.loaded_segments (0x50d00 : word) = Some W_50d00.
Proof. vm_refl. Qed.
Lemma D_50d00 : decode_any W_50d00 = Some (OpImm ALU_XOR 10 22 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_50d04 : bv 32 := 0x25756e63.
Lemma F_50d04 : fetch_word AsanUbsan.M.loaded_segments (0x50d04 : word) = Some W_50d04.
Proof. vm_refl. Qed.
Lemma D_50d04 : decode_any W_50d04 = Some (Branch BC_LTU 10 23 604, 4%Z).
Proof. vm_refl. Qed.

Definition W_50d08 : bv 32 := 0xfbfb8513.
Lemma F_50d08 : fetch_word AsanUbsan.M.loaded_segments (0x50d08 : word) = Some W_50d08.
Proof. vm_refl. Qed.
Lemma D_50d08 : decode_any W_50d08 = Some (OpImm ALU_ADD 10 23 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_50d0c : bv 32 := 0xfbf00593.
Lemma F_50d0c : fetch_word AsanUbsan.M.loaded_segments (0x50d0c : word) = Some W_50d0c.
Proof. vm_refl. Qed.
Lemma D_50d0c : decode_any W_50d0c = Some (OpImm ALU_ADD 11 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_50d10 : bv 32 := 0x2ca5f063.
Lemma F_50d10 : fetch_word AsanUbsan.M.loaded_segments (0x50d10 : word) = Some W_50d10.
Proof. vm_refl. Qed.
Lemma D_50d10 : decode_any W_50d10 = Some (Branch BC_GEU 11 10 704, 4%Z).
Proof. vm_refl. Qed.

Definition W_50d14 : bv 32 := 0x00085517.
Lemma F_50d14 : fetch_word AsanUbsan.M.loaded_segments (0x50d14 : word) = Some W_50d14.
Proof. vm_refl. Qed.
Lemma D_50d14 : decode_any W_50d14 = Some (Auipc 10 133, 4%Z).
Proof. vm_refl. Qed.

Definition W_50d18 : bv 32 := 0x7b453503.
Lemma F_50d18 : fetch_word AsanUbsan.M.loaded_segments (0x50d18 : word) = Some W_50d18.
Proof. vm_refl. Qed.
Lemma D_50d18 : decode_any W_50d18 = Some (Load SZ8 true 10 10 1972, 4%Z).
Proof. vm_refl. Qed.

Definition W_50d1c : bv 32 := 0x017b0633.
Lemma F_50d1c : fetch_word AsanUbsan.M.loaded_segments (0x50d1c : word) = Some W_50d1c.
Proof. vm_refl. Qed.
Lemma D_50d1c : decode_any W_50d1c = Some (Op ALU_ADD 12 22 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_50d20 : bv 32 := 0x00053583.
Lemma F_50d20 : fetch_word AsanUbsan.M.loaded_segments (0x50d20 : word) = Some W_50d20.
Proof. vm_refl. Qed.
Lemma D_50d20 : decode_any W_50d20 = Some (Load SZ8 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_50d24 : bv 32 := 0x003b5513.
Lemma F_50d24 : fetch_word AsanUbsan.M.loaded_segments (0x50d24 : word) = Some W_50d24.
Proof. vm_refl. Qed.
Lemma D_50d24 : decode_any W_50d24 = Some (ShiftImm ALU_SRL 10 22 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_50d28 : bv 32 := 0xfff60613.
Lemma F_50d28 : fetch_word AsanUbsan.M.loaded_segments (0x50d28 : word) = Some W_50d28.
Proof. vm_refl. Qed.
Lemma D_50d28 : decode_any W_50d28 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_50d2c : bv 32 := 0x00365693.
Lemma F_50d2c : fetch_word AsanUbsan.M.loaded_segments (0x50d2c : word) = Some W_50d2c.
Proof. vm_refl. Qed.
Lemma D_50d2c : decode_any W_50d2c = Some (ShiftImm ALU_SRL 13 12 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_50d30 : bv 32 := 0x00a58533.
Lemma F_50d30 : fetch_word AsanUbsan.M.loaded_segments (0x50d30 : word) = Some W_50d30.
Proof. vm_refl. Qed.
Lemma D_50d30 : decode_any W_50d30 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_50d34 : bv 32 := 0x00d585b3.
Lemma F_50d34 : fetch_word AsanUbsan.M.loaded_segments (0x50d34 : word) = Some W_50d34.
Proof. vm_refl. Qed.
Lemma D_50d34 : decode_any W_50d34 = Some (Op ALU_ADD 11 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_50d38 : bv 32 := 0xff857693.
Lemma F_50d38 : fetch_word AsanUbsan.M.loaded_segments (0x50d38 : word) = Some W_50d38.
Proof. vm_refl. Qed.
Lemma D_50d38 : decode_any W_50d38 = Some (OpImm ALU_AND 13 10 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_50d3c : bv 32 := 0xff85f713.
Lemma F_50d3c : fetch_word AsanUbsan.M.loaded_segments (0x50d3c : word) = Some W_50d3c.
Proof. vm_refl. Qed.
Lemma D_50d3c : decode_any W_50d3c = Some (OpImm ALU_AND 14 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_50d40 : bv 32 := 0x0006b683.
Lemma F_50d40 : fetch_word AsanUbsan.M.loaded_segments (0x50d40 : word) = Some W_50d40.
Proof. vm_refl. Qed.
Lemma D_50d40 : decode_any W_50d40 = Some (Load SZ8 true 13 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_50d44 : bv 32 := 0x00073703.
Lemma F_50d44 : fetch_word AsanUbsan.M.loaded_segments (0x50d44 : word) = Some W_50d44.
Proof. vm_refl. Qed.
Lemma D_50d44 : decode_any W_50d44 = Some (Load SZ8 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_50d48 : bv 32 := 0x00d766b3.
Lemma F_50d48 : fetch_word AsanUbsan.M.loaded_segments (0x50d48 : word) = Some W_50d48.
Proof. vm_refl. Qed.
Lemma D_50d48 : decode_any W_50d48 = Some (Op ALU_OR 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_50d4c : bv 32 := 0xf00688e3.
Lemma F_50d4c : fetch_word AsanUbsan.M.loaded_segments (0x50d4c : word) = Some W_50d4c.
Proof. vm_refl. Qed.
Lemma D_50d4c : decode_any W_50d4c = Some (Branch BC_EQ 13 0 7952, 4%Z).
Proof. vm_refl. Qed.

Definition W_50d50 : bv 32 := 0x00058683.
Lemma F_50d50 : fetch_word AsanUbsan.M.loaded_segments (0x50d50 : word) = Some W_50d50.
Proof. vm_refl. Qed.
Lemma D_50d50 : decode_any W_50d50 = Some (Load SZ1 true 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_50d54 : bv 32 := 0x00767613.
Lemma F_50d54 : fetch_word AsanUbsan.M.loaded_segments (0x50d54 : word) = Some W_50d54.
Proof. vm_refl. Qed.
Lemma D_50d54 : decode_any W_50d54 = Some (OpImm ALU_AND 12 12 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_50d58 : bv 32 := 0x00d03733.
Lemma F_50d58 : fetch_word AsanUbsan.M.loaded_segments (0x50d58 : word) = Some W_50d58.
Proof. vm_refl. Qed.
Lemma D_50d58 : decode_any W_50d58 = Some (Op ALU_SLTU 14 0 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_50d5c : bv 32 := 0x00d62633.
Lemma F_50d5c : fetch_word AsanUbsan.M.loaded_segments (0x50d5c : word) = Some W_50d5c.
Proof. vm_refl. Qed.
Lemma D_50d5c : decode_any W_50d5c = Some (Op ALU_SLT 12 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_50d60 : bv 32 := 0x00164613.
Lemma F_50d60 : fetch_word AsanUbsan.M.loaded_segments (0x50d60 : word) = Some W_50d60.
Proof. vm_refl. Qed.
Lemma D_50d60 : decode_any W_50d60 = Some (OpImm ALU_XOR 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_50d64 : bv 32 := 0x00c77633.
Lemma F_50d64 : fetch_word AsanUbsan.M.loaded_segments (0x50d64 : word) = Some W_50d64.
Proof. vm_refl. Qed.
Lemma D_50d64 : decode_any W_50d64 = Some (Op ALU_AND 12 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_50d68 : bv 32 := 0x00b57a63.
Lemma F_50d68 : fetch_word AsanUbsan.M.loaded_segments (0x50d68 : word) = Some W_50d68.
Proof. vm_refl. Qed.
Lemma D_50d68 : decode_any W_50d68 = Some (Branch BC_GEU 10 11 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_50d6c : bv 32 := 0x00054683.
Lemma F_50d6c : fetch_word AsanUbsan.M.loaded_segments (0x50d6c : word) = Some W_50d6c.
Proof. vm_refl. Qed.
Lemma D_50d6c : decode_any W_50d6c = Some (Load SZ1 false 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_50d70 : bv 32 := 0x00150513.
Lemma F_50d70 : fetch_word AsanUbsan.M.loaded_segments (0x50d70 : word) = Some W_50d70.
Proof. vm_refl. Qed.
Lemma D_50d70 : decode_any W_50d70 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_50d74 : bv 32 := 0x00c6e633.
Lemma F_50d74 : fetch_word AsanUbsan.M.loaded_segments (0x50d74 : word) = Some W_50d74.
Proof. vm_refl. Qed.
Lemma D_50d74 : decode_any W_50d74 = Some (Op ALU_OR 12 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_50d78 : bv 32 := 0xfeb51ae3.
Lemma F_50d78 : fetch_word AsanUbsan.M.loaded_segments (0x50d78 : word) = Some W_50d78.
Proof. vm_refl. Qed.
Lemma D_50d78 : decode_any W_50d78 = Some (Branch BC_NE 10 11 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_50d7c : bv 32 := 0x0ff67513.
Lemma F_50d7c : fetch_word AsanUbsan.M.loaded_segments (0x50d7c : word) = Some W_50d7c.
Proof. vm_refl. Qed.
Lemma D_50d7c : decode_any W_50d7c = Some (OpImm ALU_AND 10 12 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_50d80 : bv 32 := 0xec050ee3.
Lemma F_50d80 : fetch_word AsanUbsan.M.loaded_segments (0x50d80 : word) = Some W_50d80.
Proof. vm_refl. Qed.
Lemma D_50d80 : decode_any W_50d80 = Some (Branch BC_EQ 10 0 7900, 4%Z).
Proof. vm_refl. Qed.

Definition W_50d84 : bv 32 := 0x000b0513.
Lemma F_50d84 : fetch_word AsanUbsan.M.loaded_segments (0x50d84 : word) = Some W_50d84.
Proof. vm_refl. Qed.
Lemma D_50d84 : decode_any W_50d84 = Some (OpImm ALU_ADD 10 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_50d88 : bv 32 := 0x000b8593.
Lemma F_50d88 : fetch_word AsanUbsan.M.loaded_segments (0x50d88 : word) = Some W_50d88.
Proof. vm_refl. Qed.
Lemma D_50d88 : decode_any W_50d88 = Some (OpImm ALU_ADD 11 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_50d8c : bv 32 := 0x5f5100ef.
Lemma F_50d8c : fetch_word AsanUbsan.M.loaded_segments (0x50d8c : word) = Some W_50d8c.
Proof. vm_refl. Qed.
Lemma D_50d8c : decode_any W_50d8c = Some (Jal 1 69108, 4%Z).
Proof. vm_refl. Qed.

Definition W_50d90 : bv 32 := 0xec0506e3.
Lemma F_50d90 : fetch_word AsanUbsan.M.loaded_segments (0x50d90 : word) = Some W_50d90.
Proof. vm_refl. Qed.
Lemma D_50d90 : decode_any W_50d90 = Some (Branch BC_EQ 10 0 7884, 4%Z).
Proof. vm_refl. Qed.
