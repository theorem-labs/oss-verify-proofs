(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_69c58 : bv 32 := 0xfc010113.
Lemma F_69c58 : fetch_word Plain.M.loaded_segments (0x69c98 : word) = Some W_69c58.
Proof. vm_refl. Qed.
Lemma D_69c58 : decode_any W_69c58 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_69c5c : bv 32 := 0x02113c23.
Lemma F_69c5c : fetch_word Plain.M.loaded_segments (0x69c9c : word) = Some W_69c5c.
Proof. vm_refl. Qed.
Lemma D_69c5c : decode_any W_69c5c = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_69c60 : bv 32 := 0x02813823.
Lemma F_69c60 : fetch_word Plain.M.loaded_segments (0x69ca0 : word) = Some W_69c60.
Proof. vm_refl. Qed.
Lemma D_69c60 : decode_any W_69c60 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_69c64 : bv 32 := 0x02913423.
Lemma F_69c64 : fetch_word Plain.M.loaded_segments (0x69ca4 : word) = Some W_69c64.
Proof. vm_refl. Qed.
Lemma D_69c64 : decode_any W_69c64 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_69c68 : bv 32 := 0x03213023.
Lemma F_69c68 : fetch_word Plain.M.loaded_segments (0x69ca8 : word) = Some W_69c68.
Proof. vm_refl. Qed.
Lemma D_69c68 : decode_any W_69c68 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_69c6c : bv 32 := 0x01313c23.
Lemma F_69c6c : fetch_word Plain.M.loaded_segments (0x69cac : word) = Some W_69c6c.
Proof. vm_refl. Qed.
Lemma D_69c6c : decode_any W_69c6c = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_69c70 : bv 32 := 0x01413823.
Lemma F_69c70 : fetch_word Plain.M.loaded_segments (0x69cb0 : word) = Some W_69c70.
Proof. vm_refl. Qed.
Lemma D_69c70 : decode_any W_69c70 = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_69c74 : bv 32 := 0x01513423.
Lemma F_69c74 : fetch_word Plain.M.loaded_segments (0x69cb4 : word) = Some W_69c74.
Proof. vm_refl. Qed.
Lemma D_69c74 : decode_any W_69c74 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_69c78 : bv 32 := 0x01613023.
Lemma F_69c78 : fetch_word Plain.M.loaded_segments (0x69cb8 : word) = Some W_69c78.
Proof. vm_refl. Qed.
Lemma D_69c78 : decode_any W_69c78 = Some (Store SZ8 2 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_69c7c : bv 32 := 0x00050413.
Lemma F_69c7c : fetch_word Plain.M.loaded_segments (0x69cbc : word) = Some W_69c7c.
Proof. vm_refl. Qed.
Lemma D_69c7c : decode_any W_69c7c = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_69c80 : bv 32 := 0x00853503.
Lemma F_69c80 : fetch_word Plain.M.loaded_segments (0x69cc0 : word) = Some W_69c80.
Proof. vm_refl. Qed.
Lemma D_69c80 : decode_any W_69c80 = Some (Load SZ8 true 10 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_69c84 : bv 32 := 0x01043603.
Lemma F_69c84 : fetch_word Plain.M.loaded_segments (0x69cc4 : word) = Some W_69c84.
Proof. vm_refl. Qed.
Lemma D_69c84 : decode_any W_69c84 = Some (Load SZ8 true 12 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_69c88 : bv 32 := 0x02c57a63.
Lemma F_69c88 : fetch_word Plain.M.loaded_segments (0x69cc8 : word) = Some W_69c88.
Proof. vm_refl. Qed.
Lemma D_69c88 : decode_any W_69c88 = Some (Branch BC_GEU 10 12 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_69c8c : bv 32 := 0x0105a603.
Lemma F_69c8c : fetch_word Plain.M.loaded_segments (0x69ccc : word) = Some W_69c8c.
Proof. vm_refl. Qed.
Lemma D_69c8c : decode_any W_69c8c = Some (Load SZ4 true 12 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_69c90 : bv 32 := 0x00c52823.
Lemma F_69c90 : fetch_word Plain.M.loaded_segments (0x69cd0 : word) = Some W_69c90.
Proof. vm_refl. Qed.
Lemma D_69c90 : decode_any W_69c90 = Some (Store SZ4 10 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_69c94 : bv 32 := 0x00c5a603.
Lemma F_69c94 : fetch_word Plain.M.loaded_segments (0x69cd4 : word) = Some W_69c94.
Proof. vm_refl. Qed.
Lemma D_69c94 : decode_any W_69c94 = Some (Load SZ4 true 12 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_69c98 : bv 32 := 0x00c52623.
Lemma F_69c98 : fetch_word Plain.M.loaded_segments (0x69cd8 : word) = Some W_69c98.
Proof. vm_refl. Qed.
Lemma D_69c98 : decode_any W_69c98 = Some (Store SZ4 10 12 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_69c9c : bv 32 := 0x0085a603.
Lemma F_69c9c : fetch_word Plain.M.loaded_segments (0x69cdc : word) = Some W_69c9c.
Proof. vm_refl. Qed.
Lemma D_69c9c : decode_any W_69c9c = Some (Load SZ4 true 12 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_69ca0 : bv 32 := 0x00c52423.
Lemma F_69ca0 : fetch_word Plain.M.loaded_segments (0x69ce0 : word) = Some W_69ca0.
Proof. vm_refl. Qed.
Lemma D_69ca0 : decode_any W_69ca0 = Some (Store SZ4 10 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_69ca4 : bv 32 := 0x0045a603.
Lemma F_69ca4 : fetch_word Plain.M.loaded_segments (0x69ce4 : word) = Some W_69ca4.
Proof. vm_refl. Qed.
Lemma D_69ca4 : decode_any W_69ca4 = Some (Load SZ4 true 12 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_69ca8 : bv 32 := 0x00c52223.
Lemma F_69ca8 : fetch_word Plain.M.loaded_segments (0x69ce8 : word) = Some W_69ca8.
Proof. vm_refl. Qed.
Lemma D_69ca8 : decode_any W_69ca8 = Some (Store SZ4 10 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_69cac : bv 32 := 0x0005a583.
Lemma F_69cac : fetch_word Plain.M.loaded_segments (0x69cec : word) = Some W_69cac.
Proof. vm_refl. Qed.
Lemma D_69cac : decode_any W_69cac = Some (Load SZ4 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_69cb0 : bv 32 := 0x00b52023.
Lemma F_69cb0 : fetch_word Plain.M.loaded_segments (0x69cf0 : word) = Some W_69cb0.
Proof. vm_refl. Qed.
Lemma D_69cb0 : decode_any W_69cb0 = Some (Store SZ4 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_69cb4 : bv 32 := 0x01450a93.
Lemma F_69cb4 : fetch_word Plain.M.loaded_segments (0x69cf4 : word) = Some W_69cb4.
Proof. vm_refl. Qed.
Lemma D_69cb4 : decode_any W_69cb4 = Some (OpImm ALU_ADD 21 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_69cb8 : bv 32 := 0x0f00006f.
Lemma F_69cb8 : fetch_word Plain.M.loaded_segments (0x69cf8 : word) = Some W_69cb8.
Proof. vm_refl. Qed.
Lemma D_69cb8 : decode_any W_69cb8 = Some (Jal 0 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_69cbc : bv 32 := 0x00043483.
Lemma F_69cbc : fetch_word Plain.M.loaded_segments (0x69cfc : word) = Some W_69cbc.
Proof. vm_refl. Qed.
Lemma D_69cbc : decode_any W_69cbc = Some (Load SZ8 true 9 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_69cc0 : bv 32 := 0xccccd6b7.
Lemma F_69cc0 : fetch_word Plain.M.loaded_segments (0x69d00 : word) = Some W_69cc0.
Proof. vm_refl. Qed.
Lemma D_69cc0 : decode_any W_69cc0 = Some (Lui 13 838861, 4%Z).
Proof. vm_refl. Qed.

Definition W_69cc4 : bv 32 := 0xfffab797.
Lemma F_69cc4 : fetch_word Plain.M.loaded_segments (0x69d04 : word) = Some W_69cc4.
Proof. vm_refl. Qed.
Lemma D_69cc4 : decode_any W_69cc4 = Some (Auipc 15 1048491, 4%Z).
Proof. vm_refl. Qed.

Definition W_69cc8 : bv 32 := 0xccd6871b.
Lemma F_69cc8 : fetch_word Plain.M.loaded_segments (0x69d08 : word) = Some W_69cc8.
Proof. vm_refl. Qed.
Lemma D_69cc8 : decode_any W_69cc8 = Some (OpImm32 14 13 3277, 4%Z).
Proof. vm_refl. Qed.

Definition W_69ccc : bv 32 := 0x02071693.
Lemma F_69ccc : fetch_word Plain.M.loaded_segments (0x69d0c : word) = Some W_69ccc.
Proof. vm_refl. Qed.
Lemma D_69ccc : decode_any W_69ccc = Some (ShiftImm ALU_SLL 13 14 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_69cd0 : bv 32 := 0x00d70733.
Lemma F_69cd0 : fetch_word Plain.M.loaded_segments (0x69d10 : word) = Some W_69cd0.
Proof. vm_refl. Qed.
Lemma D_69cd0 : decode_any W_69cd0 = Some (Op ALU_ADD 14 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_69cd4 : bv 32 := 0x409509b3.
Lemma F_69cd4 : fetch_word Plain.M.loaded_segments (0x69d14 : word) = Some W_69cd4.
Proof. vm_refl. Qed.
Lemma D_69cd4 : decode_any W_69cd4 = Some (Op ALU_SUB 19 10 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_69cd8 : bv 32 := 0xc547b503.
Lemma F_69cd8 : fetch_word Plain.M.loaded_segments (0x69d18 : word) = Some W_69cd8.
Proof. vm_refl. Qed.
Lemma D_69cd8 : decode_any W_69cd8 = Some (Load SZ8 true 10 15 3156, 4%Z).
Proof. vm_refl. Qed.

Definition W_69cdc : bv 32 := 0x4029d693.
Lemma F_69cdc : fetch_word Plain.M.loaded_segments (0x69d1c : word) = Some W_69cdc.
Proof. vm_refl. Qed.
Lemma D_69cdc : decode_any W_69cdc = Some (ShiftImm ALU_SRA 13 19 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_69ce0 : bv 32 := 0x02e686b3.
Lemma F_69ce0 : fetch_word Plain.M.loaded_segments (0x69d20 : word) = Some W_69ce0.
Proof. vm_refl. Qed.
Lemma D_69ce0 : decode_any W_69ce0 = Some (Mul M_MUL 13 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_69ce4 : bv 32 := 0x00168693.
Lemma F_69ce4 : fetch_word Plain.M.loaded_segments (0x69d24 : word) = Some W_69ce4.
Proof. vm_refl. Qed.
Lemma D_69ce4 : decode_any W_69ce4 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_69ce8 : bv 32 := 0x0ea6f663.
Lemma F_69ce8 : fetch_word Plain.M.loaded_segments (0x69d28 : word) = Some W_69ce8.
Proof. vm_refl. Qed.
Lemma D_69ce8 : decode_any W_69ce8 = Some (Branch BC_GEU 13 10 236, 4%Z).
Proof. vm_refl. Qed.

Definition W_69cec : bv 32 := 0x40960933.
Lemma F_69cec : fetch_word Plain.M.loaded_segments (0x69d2c : word) = Some W_69cec.
Proof. vm_refl. Qed.
Lemma D_69cec : decode_any W_69cec = Some (Op ALU_SUB 18 12 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_69cf0 : bv 32 := 0x40295613.
Lemma F_69cf0 : fetch_word Plain.M.loaded_segments (0x69d30 : word) = Some W_69cf0.
Proof. vm_refl. Qed.
Lemma D_69cf0 : decode_any W_69cf0 = Some (ShiftImm ALU_SRA 12 18 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_69cf4 : bv 32 := 0x02e60633.
Lemma F_69cf4 : fetch_word Plain.M.loaded_segments (0x69d34 : word) = Some W_69cf4.
Proof. vm_refl. Qed.
Lemma D_69cf4 : decode_any W_69cf4 = Some (Mul M_MUL 12 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_69cf8 : bv 32 := 0x00161a93.
Lemma F_69cf8 : fetch_word Plain.M.loaded_segments (0x69d38 : word) = Some W_69cf8.
Proof. vm_refl. Qed.
Lemma D_69cf8 : decode_any W_69cf8 = Some (ShiftImm ALU_SLL 21 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_69cfc : bv 32 := 0x0156e463.
Lemma F_69cfc : fetch_word Plain.M.loaded_segments (0x69d3c : word) = Some W_69cfc.
Proof. vm_refl. Qed.
Lemma D_69cfc : decode_any W_69cfc = Some (Branch BC_LTU 13 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_69d00 : bv 32 := 0x00068a93.
Lemma F_69d00 : fetch_word Plain.M.loaded_segments (0x69d40 : word) = Some W_69d00.
Proof. vm_refl. Qed.
Lemma D_69d00 : decode_any W_69d00 = Some (OpImm ALU_ADD 21 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_69d04 : bv 32 := 0xfffab697.
Lemma F_69d04 : fetch_word Plain.M.loaded_segments (0x69d44 : word) = Some W_69d04.
Proof. vm_refl. Qed.
Lemma D_69d04 : decode_any W_69d04 = Some (Auipc 13 1048491, 4%Z).
Proof. vm_refl. Qed.

Definition W_69d08 : bv 32 := 0xc646b683.
Lemma F_69d08 : fetch_word Plain.M.loaded_segments (0x69d48 : word) = Some W_69d08.
Proof. vm_refl. Qed.
Lemma D_69d08 : decode_any W_69d08 = Some (Load SZ8 true 13 13 3172, 4%Z).
Proof. vm_refl. Qed.

Definition W_69d0c : bv 32 := 0x00d66663.
Lemma F_69d0c : fetch_word Plain.M.loaded_segments (0x69d4c : word) = Some W_69d0c.
Proof. vm_refl. Qed.
Lemma D_69d0c : decode_any W_69d0c = Some (Branch BC_LTU 12 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_69d18 : bv 32 := 0x020a8263.
Lemma F_69d18 : fetch_word Plain.M.loaded_segments (0x69d58 : word) = Some W_69d18.
Proof. vm_refl. Qed.
Lemma D_69d18 : decode_any W_69d18 = Some (Branch BC_EQ 21 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_69d1c : bv 32 := 0x0aaafe63.
Lemma F_69d1c : fetch_word Plain.M.loaded_segments (0x69d5c : word) = Some W_69d1c.
Proof. vm_refl. Qed.
Lemma D_69d1c : decode_any W_69d1c = Some (Branch BC_GEU 21 10 188, 4%Z).
Proof. vm_refl. Qed.

Definition W_69d20 : bv 32 := 0x00058b13.
Lemma F_69d20 : fetch_word Plain.M.loaded_segments (0x69d60 : word) = Some W_69d20.
Proof. vm_refl. Qed.
Lemma D_69d20 : decode_any W_69d20 = Some (OpImm ALU_ADD 22 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_69d24 : bv 32 := 0x01400513.
Lemma F_69d24 : fetch_word Plain.M.loaded_segments (0x69d64 : word) = Some W_69d24.
Proof. vm_refl. Qed.
Lemma D_69d24 : decode_any W_69d24 = Some (OpImm ALU_ADD 10 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_69d28 : bv 32 := 0x02aa8533.
Lemma F_69d28 : fetch_word Plain.M.loaded_segments (0x69d68 : word) = Some W_69d28.
Proof. vm_refl. Qed.
Lemma D_69d28 : decode_any W_69d28 = Some (Mul M_MUL 10 21 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_69d2c : bv 32 := 0x0707c0ef.
Lemma F_69d2c : fetch_word Plain.M.loaded_segments (0x69d6c : word) = Some W_69d2c.
Proof. vm_refl. Qed.
Lemma D_69d2c : decode_any W_69d2c = Some (Jal 1 508016, 4%Z).
Proof. vm_refl. Qed.

Definition W_69d30 : bv 32 := 0x00050a13.
Lemma F_69d30 : fetch_word Plain.M.loaded_segments (0x69d70 : word) = Some W_69d30.
Proof. vm_refl. Qed.
Lemma D_69d30 : decode_any W_69d30 = Some (OpImm ALU_ADD 20 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_69d34 : bv 32 := 0x000b0593.
Lemma F_69d34 : fetch_word Plain.M.loaded_segments (0x69d74 : word) = Some W_69d34.
Proof. vm_refl. Qed.
Lemma D_69d34 : decode_any W_69d34 = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_69d38 : bv 32 := 0x0080006f.
Lemma F_69d38 : fetch_word Plain.M.loaded_segments (0x69d78 : word) = Some W_69d38.
Proof. vm_refl. Qed.
Lemma D_69d38 : decode_any W_69d38 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_69d40 : bv 32 := 0x0105a503.
Lemma F_69d40 : fetch_word Plain.M.loaded_segments (0x69d80 : word) = Some W_69d40.
Proof. vm_refl. Qed.
Lemma D_69d40 : decode_any W_69d40 = Some (Load SZ4 true 10 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_69d44 : bv 32 := 0x013a0633.
Lemma F_69d44 : fetch_word Plain.M.loaded_segments (0x69d84 : word) = Some W_69d44.
Proof. vm_refl. Qed.
Lemma D_69d44 : decode_any W_69d44 = Some (Op ALU_ADD 12 20 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_69d48 : bv 32 := 0x01400693.
Lemma F_69d48 : fetch_word Plain.M.loaded_segments (0x69d88 : word) = Some W_69d48.
Proof. vm_refl. Qed.
Lemma D_69d48 : decode_any W_69d48 = Some (OpImm ALU_ADD 13 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_69d4c : bv 32 := 0x02da86b3.
Lemma F_69d4c : fetch_word Plain.M.loaded_segments (0x69d8c : word) = Some W_69d4c.
Proof. vm_refl. Qed.
Lemma D_69d4c : decode_any W_69d4c = Some (Mul M_MUL 13 21 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_69d50 : bv 32 := 0x00a62823.
Lemma F_69d50 : fetch_word Plain.M.loaded_segments (0x69d90 : word) = Some W_69d50.
Proof. vm_refl. Qed.
Lemma D_69d50 : decode_any W_69d50 = Some (Store SZ4 12 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_69d54 : bv 32 := 0x0005a503.
Lemma F_69d54 : fetch_word Plain.M.loaded_segments (0x69d94 : word) = Some W_69d54.
Proof. vm_refl. Qed.
Lemma D_69d54 : decode_any W_69d54 = Some (Load SZ4 true 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_69d58 : bv 32 := 0x0045a703.
Lemma F_69d58 : fetch_word Plain.M.loaded_segments (0x69d98 : word) = Some W_69d58.
Proof. vm_refl. Qed.
Lemma D_69d58 : decode_any W_69d58 = Some (Load SZ4 true 14 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_69d5c : bv 32 := 0x0085a783.
Lemma F_69d5c : fetch_word Plain.M.loaded_segments (0x69d9c : word) = Some W_69d5c.
Proof. vm_refl. Qed.
Lemma D_69d5c : decode_any W_69d5c = Some (Load SZ4 true 15 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_69d60 : bv 32 := 0x00c5a583.
Lemma F_69d60 : fetch_word Plain.M.loaded_segments (0x69da0 : word) = Some W_69d60.
Proof. vm_refl. Qed.
Lemma D_69d60 : decode_any W_69d60 = Some (Load SZ4 true 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_69d64 : bv 32 := 0x00da0b33.
Lemma F_69d64 : fetch_word Plain.M.loaded_segments (0x69da4 : word) = Some W_69d64.
Proof. vm_refl. Qed.
Lemma D_69d64 : decode_any W_69d64 = Some (Op ALU_ADD 22 20 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_69d68 : bv 32 := 0x00a62023.
Lemma F_69d68 : fetch_word Plain.M.loaded_segments (0x69da8 : word) = Some W_69d68.
Proof. vm_refl. Qed.
Lemma D_69d68 : decode_any W_69d68 = Some (Store SZ4 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_69d6c : bv 32 := 0x00e62223.
Lemma F_69d6c : fetch_word Plain.M.loaded_segments (0x69dac : word) = Some W_69d6c.
Proof. vm_refl. Qed.
Lemma D_69d6c : decode_any W_69d6c = Some (Store SZ4 12 14 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_69d70 : bv 32 := 0x00f62423.
Lemma F_69d70 : fetch_word Plain.M.loaded_segments (0x69db0 : word) = Some W_69d70.
Proof. vm_refl. Qed.
Lemma D_69d70 : decode_any W_69d70 = Some (Store SZ4 12 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_69d74 : bv 32 := 0x00b62623.
Lemma F_69d74 : fetch_word Plain.M.loaded_segments (0x69db4 : word) = Some W_69d74.
Proof. vm_refl. Qed.
Lemma D_69d74 : decode_any W_69d74 = Some (Store SZ4 12 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_69d78 : bv 32 := 0x01460a93.
Lemma F_69d78 : fetch_word Plain.M.loaded_segments (0x69db8 : word) = Some W_69d78.
Proof. vm_refl. Qed.
Lemma D_69d78 : decode_any W_69d78 = Some (OpImm ALU_ADD 21 12 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_69d7c : bv 32 := 0x000a0513.
Lemma F_69d7c : fetch_word Plain.M.loaded_segments (0x69dbc : word) = Some W_69d7c.
Proof. vm_refl. Qed.
Lemma D_69d7c : decode_any W_69d7c = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_69d80 : bv 32 := 0x00048593.
Lemma F_69d80 : fetch_word Plain.M.loaded_segments (0x69dc0 : word) = Some W_69d80.
Proof. vm_refl. Qed.
Lemma D_69d80 : decode_any W_69d80 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_69d84 : bv 32 := 0x00098613.
Lemma F_69d84 : fetch_word Plain.M.loaded_segments (0x69dc4 : word) = Some W_69d84.
Proof. vm_refl. Qed.
Lemma D_69d84 : decode_any W_69d84 = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_69d88 : bv 32 := 0x07c770ef.
Lemma F_69d88 : fetch_word Plain.M.loaded_segments (0x69dc8 : word) = Some W_69d88.
Proof. vm_refl. Qed.
Lemma D_69d88 : decode_any W_69d88 = Some (Jal 1 487548, 4%Z).
Proof. vm_refl. Qed.

Definition W_69d8c : bv 32 := 0x01443023.
Lemma F_69d8c : fetch_word Plain.M.loaded_segments (0x69dcc : word) = Some W_69d8c.
Proof. vm_refl. Qed.
Lemma D_69d8c : decode_any W_69d8c = Some (Store SZ8 8 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_69d90 : bv 32 := 0x01543423.
Lemma F_69d90 : fetch_word Plain.M.loaded_segments (0x69dd0 : word) = Some W_69d90.
Proof. vm_refl. Qed.
Lemma D_69d90 : decode_any W_69d90 = Some (Store SZ8 8 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_69d94 : bv 32 := 0x01643823.
Lemma F_69d94 : fetch_word Plain.M.loaded_segments (0x69dd4 : word) = Some W_69d94.
Proof. vm_refl. Qed.
Lemma D_69d94 : decode_any W_69d94 = Some (Store SZ8 8 22 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_69d98 : bv 32 := 0x00048863.
Lemma F_69d98 : fetch_word Plain.M.loaded_segments (0x69dd8 : word) = Some W_69d98.
Proof. vm_refl. Qed.
Lemma D_69d98 : decode_any W_69d98 = Some (Branch BC_EQ 9 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_69d9c : bv 32 := 0x00048513.
Lemma F_69d9c : fetch_word Plain.M.loaded_segments (0x69ddc : word) = Some W_69d9c.
Proof. vm_refl. Qed.
Lemma D_69d9c : decode_any W_69d9c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_69da0 : bv 32 := 0x00090593.
Lemma F_69da0 : fetch_word Plain.M.loaded_segments (0x69de0 : word) = Some W_69da0.
Proof. vm_refl. Qed.
Lemma D_69da0 : decode_any W_69da0 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_69da4 : bv 32 := 0x591030ef.
Lemma F_69da4 : fetch_word Plain.M.loaded_segments (0x69de4 : word) = Some W_69da4.
Proof. vm_refl. Qed.
Lemma D_69da4 : decode_any W_69da4 = Some (Jal 1 15760, 4%Z).
Proof. vm_refl. Qed.

Definition W_69da8 : bv 32 := 0x01543423.
Lemma F_69da8 : fetch_word Plain.M.loaded_segments (0x69de8 : word) = Some W_69da8.
Proof. vm_refl. Qed.
Lemma D_69da8 : decode_any W_69da8 = Some (Store SZ8 8 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_69dac : bv 32 := 0x03813083.
Lemma F_69dac : fetch_word Plain.M.loaded_segments (0x69dec : word) = Some W_69dac.
Proof. vm_refl. Qed.
Lemma D_69dac : decode_any W_69dac = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_69db0 : bv 32 := 0x03013403.
Lemma F_69db0 : fetch_word Plain.M.loaded_segments (0x69df0 : word) = Some W_69db0.
Proof. vm_refl. Qed.
Lemma D_69db0 : decode_any W_69db0 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_69db4 : bv 32 := 0x02813483.
Lemma F_69db4 : fetch_word Plain.M.loaded_segments (0x69df4 : word) = Some W_69db4.
Proof. vm_refl. Qed.
Lemma D_69db4 : decode_any W_69db4 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_69db8 : bv 32 := 0x02013903.
Lemma F_69db8 : fetch_word Plain.M.loaded_segments (0x69df8 : word) = Some W_69db8.
Proof. vm_refl. Qed.
Lemma D_69db8 : decode_any W_69db8 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_69dbc : bv 32 := 0x01813983.
Lemma F_69dbc : fetch_word Plain.M.loaded_segments (0x69dfc : word) = Some W_69dbc.
Proof. vm_refl. Qed.
Lemma D_69dbc : decode_any W_69dbc = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_69dc0 : bv 32 := 0x01013a03.
Lemma F_69dc0 : fetch_word Plain.M.loaded_segments (0x69e00 : word) = Some W_69dc0.
Proof. vm_refl. Qed.
Lemma D_69dc0 : decode_any W_69dc0 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_69dc4 : bv 32 := 0x00813a83.
Lemma F_69dc4 : fetch_word Plain.M.loaded_segments (0x69e04 : word) = Some W_69dc4.
Proof. vm_refl. Qed.
Lemma D_69dc4 : decode_any W_69dc4 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_69dc8 : bv 32 := 0x00013b03.
Lemma F_69dc8 : fetch_word Plain.M.loaded_segments (0x69e08 : word) = Some W_69dc8.
Proof. vm_refl. Qed.
Lemma D_69dc8 : decode_any W_69dc8 = Some (Load SZ8 true 22 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_69dcc : bv 32 := 0x04010113.
Lemma F_69dcc : fetch_word Plain.M.loaded_segments (0x69e0c : word) = Some W_69dcc.
Proof. vm_refl. Qed.
Lemma D_69dcc : decode_any W_69dcc = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_69dd0 : bv 32 := 0x00008067.
Lemma F_69dd0 : fetch_word Plain.M.loaded_segments (0x69e10 : word) = Some W_69dd0.
Proof. vm_refl. Qed.
Lemma D_69dd0 : decode_any W_69dd0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
