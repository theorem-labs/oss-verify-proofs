(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_e2a6c : bv 32 := 0x0ff5f593.
Lemma F_e2a6c : fetch_word Ubsan.M.loaded_segments (0xe2aa0 : word) = Some W_e2a6c.
Proof. vm_refl. Qed.
Lemma D_e2a6c : decode_any W_e2a6c = Some (OpImm ALU_AND 11 11 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_e2a70 : bv 32 := 0x00757693.
Lemma F_e2a70 : fetch_word Ubsan.M.loaded_segments (0xe2aa4 : word) = Some W_e2a70.
Proof. vm_refl. Qed.
Lemma D_e2a70 : decode_any W_e2a70 = Some (OpImm ALU_AND 13 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_e2a74 : bv 32 := 0x00c03733.
Lemma F_e2a74 : fetch_word Ubsan.M.loaded_segments (0xe2aa8 : word) = Some W_e2a74.
Proof. vm_refl. Qed.
Lemma D_e2a74 : decode_any W_e2a74 = Some (Op ALU_SLTU 14 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_e2a78 : bv 32 := 0x02068c63.
Lemma F_e2a78 : fetch_word Ubsan.M.loaded_segments (0xe2aac : word) = Some W_e2a78.
Proof. vm_refl. Qed.
Lemma D_e2a78 : decode_any W_e2a78 = Some (Branch BC_EQ 13 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_e2a7c : bv 32 := 0x02060a63.
Lemma F_e2a7c : fetch_word Ubsan.M.loaded_segments (0xe2ab0 : word) = Some W_e2a7c.
Proof. vm_refl. Qed.
Lemma D_e2a7c : decode_any W_e2a7c = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_e2a80 : bv 32 := 0x00150793.
Lemma F_e2a80 : fetch_word Ubsan.M.loaded_segments (0xe2ab4 : word) = Some W_e2a80.
Proof. vm_refl. Qed.
Lemma D_e2a80 : decode_any W_e2a80 = Some (OpImm ALU_ADD 15 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_e2a84 : bv 32 := 0x00100813.
Lemma F_e2a84 : fetch_word Ubsan.M.loaded_segments (0xe2ab8 : word) = Some W_e2a84.
Proof. vm_refl. Qed.
Lemma D_e2a84 : decode_any W_e2a84 = Some (OpImm ALU_ADD 16 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_e2a88 : bv 32 := 0x00054703.
Lemma F_e2a88 : fetch_word Ubsan.M.loaded_segments (0xe2abc : word) = Some W_e2a88.
Proof. vm_refl. Qed.
Lemma D_e2a88 : decode_any W_e2a88 = Some (Load SZ1 false 14 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e2a8c : bv 32 := 0x00060693.
Lemma F_e2a8c : fetch_word Ubsan.M.loaded_segments (0xe2ac0 : word) = Some W_e2a8c.
Proof. vm_refl. Qed.
Lemma D_e2a8c : decode_any W_e2a8c = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e2a90 : bv 32 := 0x06b70e63.
Lemma F_e2a90 : fetch_word Ubsan.M.loaded_segments (0xe2ac4 : word) = Some W_e2a90.
Proof. vm_refl. Qed.
Lemma D_e2a90 : decode_any W_e2a90 = Some (Branch BC_EQ 14 11 124, 4%Z).
Proof. vm_refl. Qed.

Definition W_e2a94 : bv 32 := 0x00150513.
Lemma F_e2a94 : fetch_word Ubsan.M.loaded_segments (0xe2ac8 : word) = Some W_e2a94.
Proof. vm_refl. Qed.
Lemma D_e2a94 : decode_any W_e2a94 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_e2a98 : bv 32 := 0xfff68613.
Lemma F_e2a98 : fetch_word Ubsan.M.loaded_segments (0xe2acc : word) = Some W_e2a98.
Proof. vm_refl. Qed.
Lemma D_e2a98 : decode_any W_e2a98 = Some (OpImm ALU_ADD 12 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_e2a9c : bv 32 := 0x0077f893.
Lemma F_e2a9c : fetch_word Ubsan.M.loaded_segments (0xe2ad0 : word) = Some W_e2a9c.
Proof. vm_refl. Qed.
Lemma D_e2a9c : decode_any W_e2a9c = Some (OpImm ALU_AND 17 15 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_e2aa0 : bv 32 := 0x00c03733.
Lemma F_e2aa0 : fetch_word Ubsan.M.loaded_segments (0xe2ad4 : word) = Some W_e2aa0.
Proof. vm_refl. Qed.
Lemma D_e2aa0 : decode_any W_e2aa0 = Some (Op ALU_SLTU 14 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_e2aa4 : bv 32 := 0x00088663.
Lemma F_e2aa4 : fetch_word Ubsan.M.loaded_segments (0xe2ad8 : word) = Some W_e2aa4.
Proof. vm_refl. Qed.
Lemma D_e2aa4 : decode_any W_e2aa4 = Some (Branch BC_EQ 17 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_e2aa8 : bv 32 := 0x00178793.
Lemma F_e2aa8 : fetch_word Ubsan.M.loaded_segments (0xe2adc : word) = Some W_e2aa8.
Proof. vm_refl. Qed.
Lemma D_e2aa8 : decode_any W_e2aa8 = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_e2aac : bv 32 := 0xfd069ee3.
Lemma F_e2aac : fetch_word Ubsan.M.loaded_segments (0xe2ae0 : word) = Some W_e2aac.
Proof. vm_refl. Qed.
Lemma D_e2aac : decode_any W_e2aac = Some (Branch BC_NE 13 16 8156, 4%Z).
Proof. vm_refl. Qed.

Definition W_e2ab0 : bv 32 := 0x06070863.
Lemma F_e2ab0 : fetch_word Ubsan.M.loaded_segments (0xe2ae4 : word) = Some W_e2ab0.
Proof. vm_refl. Qed.
Lemma D_e2ab0 : decode_any W_e2ab0 = Some (Branch BC_EQ 14 0 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_e2ab4 : bv 32 := 0x00054683.
Lemma F_e2ab4 : fetch_word Ubsan.M.loaded_segments (0xe2ae8 : word) = Some W_e2ab4.
Proof. vm_refl. Qed.
Lemma D_e2ab4 : decode_any W_e2ab4 = Some (Load SZ1 false 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e2ab8 : bv 32 := 0x04b68663.
Lemma F_e2ab8 : fetch_word Ubsan.M.loaded_segments (0xe2aec : word) = Some W_e2ab8.
Proof. vm_refl. Qed.
Lemma D_e2ab8 : decode_any W_e2ab8 = Some (Branch BC_EQ 13 11 76, 4%Z).
Proof. vm_refl. Qed.

Definition W_e2abc : bv 32 := 0x00800693.
Lemma F_e2abc : fetch_word Ubsan.M.loaded_segments (0xe2af0 : word) = Some W_e2abc.
Proof. vm_refl. Qed.
Lemma D_e2abc : decode_any W_e2abc = Some (OpImm ALU_ADD 13 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_e2ac0 : bv 32 := 0x04d66263.
Lemma F_e2ac0 : fetch_word Ubsan.M.loaded_segments (0xe2af4 : word) = Some W_e2ac0.
Proof. vm_refl. Qed.
Lemma D_e2ac0 : decode_any W_e2ac0 = Some (Branch BC_LTU 12 13 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_e2ac4 : bv 32 := 0xfff32697.
Lemma F_e2ac4 : fetch_word Ubsan.M.loaded_segments (0xe2af8 : word) = Some W_e2ac4.
Proof. vm_refl. Qed.
Lemma D_e2ac4 : decode_any W_e2ac4 = Some (Auipc 13 1048370, 4%Z).
Proof. vm_refl. Qed.

Definition W_e2ac8 : bv 32 := 0xed86b683.
Lemma F_e2ac8 : fetch_word Ubsan.M.loaded_segments (0xe2afc : word) = Some W_e2ac8.
Proof. vm_refl. Qed.
Lemma D_e2ac8 : decode_any W_e2ac8 = Some (Load SZ8 true 13 13 3800, 4%Z).
Proof. vm_refl. Qed.

Definition W_e2acc : bv 32 := 0xfff32717.
Lemma F_e2acc : fetch_word Ubsan.M.loaded_segments (0xe2b00 : word) = Some W_e2acc.
Proof. vm_refl. Qed.
Lemma D_e2acc : decode_any W_e2acc = Some (Auipc 14 1048370, 4%Z).
Proof. vm_refl. Qed.

Definition W_e2ad0 : bv 32 := 0xec073703.
Lemma F_e2ad0 : fetch_word Ubsan.M.loaded_segments (0xe2b04 : word) = Some W_e2ad0.
Proof. vm_refl. Qed.
Lemma D_e2ad0 : decode_any W_e2ad0 = Some (Load SZ8 true 14 14 3776, 4%Z).
Proof. vm_refl. Qed.

Definition W_e2ad4 : bv 32 := 0x00168793.
Lemma F_e2ad4 : fetch_word Ubsan.M.loaded_segments (0xe2b08 : word) = Some W_e2ad4.
Proof. vm_refl. Qed.
Lemma D_e2ad4 : decode_any W_e2ad4 = Some (OpImm ALU_ADD 15 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_e2ad8 : bv 32 := 0x02f587b3.
Lemma F_e2ad8 : fetch_word Ubsan.M.loaded_segments (0xe2b0c : word) = Some W_e2ad8.
Proof. vm_refl. Qed.
Lemma D_e2ad8 : decode_any W_e2ad8 = Some (Mul M_MUL 15 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_e2adc : bv 32 := 0x00700813.
Lemma F_e2adc : fetch_word Ubsan.M.loaded_segments (0xe2b10 : word) = Some W_e2adc.
Proof. vm_refl. Qed.
Lemma D_e2adc : decode_any W_e2adc = Some (OpImm ALU_ADD 16 0 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_e2ae0 : bv 32 := 0x00053883.
Lemma F_e2ae0 : fetch_word Ubsan.M.loaded_segments (0xe2b14 : word) = Some W_e2ae0.
Proof. vm_refl. Qed.
Lemma D_e2ae0 : decode_any W_e2ae0 = Some (Load SZ8 true 17 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e2ae4 : bv 32 := 0x00f8c8b3.
Lemma F_e2ae4 : fetch_word Ubsan.M.loaded_segments (0xe2b18 : word) = Some W_e2ae4.
Proof. vm_refl. Qed.
Lemma D_e2ae4 : decode_any W_e2ae4 = Some (Op ALU_XOR 17 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_e2ae8 : bv 32 := 0x411682b3.
Lemma F_e2ae8 : fetch_word Ubsan.M.loaded_segments (0xe2b1c : word) = Some W_e2ae8.
Proof. vm_refl. Qed.
Lemma D_e2ae8 : decode_any W_e2ae8 = Some (Op ALU_SUB 5 13 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_e2aec : bv 32 := 0x0112e8b3.
Lemma F_e2aec : fetch_word Ubsan.M.loaded_segments (0xe2b20 : word) = Some W_e2aec.
Proof. vm_refl. Qed.
Lemma D_e2aec : decode_any W_e2aec = Some (Op ALU_OR 17 5 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_e2af0 : bv 32 := 0x00e8f8b3.
Lemma F_e2af0 : fetch_word Ubsan.M.loaded_segments (0xe2b24 : word) = Some W_e2af0.
Proof. vm_refl. Qed.
Lemma D_e2af0 : decode_any W_e2af0 = Some (Op ALU_AND 17 17 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_e2af4 : bv 32 := 0x02e89a63.
Lemma F_e2af4 : fetch_word Ubsan.M.loaded_segments (0xe2b28 : word) = Some W_e2af4.
Proof. vm_refl. Qed.
Lemma D_e2af4 : decode_any W_e2af4 = Some (Branch BC_NE 17 14 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_e2af8 : bv 32 := 0xff860613.
Lemma F_e2af8 : fetch_word Ubsan.M.loaded_segments (0xe2b2c : word) = Some W_e2af8.
Proof. vm_refl. Qed.
Lemma D_e2af8 : decode_any W_e2af8 = Some (OpImm ALU_ADD 12 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_e2afc : bv 32 := 0x00850513.
Lemma F_e2afc : fetch_word Ubsan.M.loaded_segments (0xe2b30 : word) = Some W_e2afc.
Proof. vm_refl. Qed.
Lemma D_e2afc : decode_any W_e2afc = Some (OpImm ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_e2b00 : bv 32 := 0xfec860e3.
Lemma F_e2b00 : fetch_word Ubsan.M.loaded_segments (0xe2b34 : word) = Some W_e2b00.
Proof. vm_refl. Qed.
Lemma D_e2b00 : decode_any W_e2b00 = Some (Branch BC_LTU 16 12 8160, 4%Z).
Proof. vm_refl. Qed.

Definition W_e2b04 : bv 32 := 0x00060693.
Lemma F_e2b04 : fetch_word Ubsan.M.loaded_segments (0xe2b38 : word) = Some W_e2b04.
Proof. vm_refl. Qed.
Lemma D_e2b04 : decode_any W_e2b04 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e2b08 : bv 32 := 0x00060c63.
Lemma F_e2b08 : fetch_word Ubsan.M.loaded_segments (0xe2b3c : word) = Some W_e2b08.
Proof. vm_refl. Qed.
Lemma D_e2b08 : decode_any W_e2b08 = Some (Branch BC_EQ 12 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_e2b0c : bv 32 := 0x00054603.
Lemma F_e2b0c : fetch_word Ubsan.M.loaded_segments (0xe2b40 : word) = Some W_e2b0c.
Proof. vm_refl. Qed.
Lemma D_e2b0c : decode_any W_e2b0c = Some (Load SZ1 false 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e2b10 : bv 32 := 0x00b60a63.
Lemma F_e2b10 : fetch_word Ubsan.M.loaded_segments (0xe2b44 : word) = Some W_e2b10.
Proof. vm_refl. Qed.
Lemma D_e2b10 : decode_any W_e2b10 = Some (Branch BC_EQ 12 11 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_e2b14 : bv 32 := 0xfff68693.
Lemma F_e2b14 : fetch_word Ubsan.M.loaded_segments (0xe2b48 : word) = Some W_e2b14.
Proof. vm_refl. Qed.
Lemma D_e2b14 : decode_any W_e2b14 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_e2b18 : bv 32 := 0x00150513.
Lemma F_e2b18 : fetch_word Ubsan.M.loaded_segments (0xe2b4c : word) = Some W_e2b18.
Proof. vm_refl. Qed.
Lemma D_e2b18 : decode_any W_e2b18 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_e2b1c : bv 32 := 0xfe0698e3.
Lemma F_e2b1c : fetch_word Ubsan.M.loaded_segments (0xe2b50 : word) = Some W_e2b1c.
Proof. vm_refl. Qed.
Lemma D_e2b1c : decode_any W_e2b1c = Some (Branch BC_NE 13 0 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_e2b20 : bv 32 := 0x00000513.

Definition W_e2b24 : bv 32 := 0x00008067.
Lemma F_e2b24 : fetch_word Ubsan.M.loaded_segments (0xe2b58 : word) = Some W_e2b24.
Proof. vm_refl. Qed.
Lemma D_e2b24 : decode_any W_e2b24 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e2b28 : bv 32 := 0x00060693.
Lemma F_e2b28 : fetch_word Ubsan.M.loaded_segments (0xe2b5c : word) = Some W_e2b28.
Proof. vm_refl. Qed.
Lemma D_e2b28 : decode_any W_e2b28 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e2b2c : bv 32 := 0x00054603.
Lemma F_e2b2c : fetch_word Ubsan.M.loaded_segments (0xe2b60 : word) = Some W_e2b2c.
Proof. vm_refl. Qed.
Lemma D_e2b2c : decode_any W_e2b2c = Some (Load SZ1 false 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e2b30 : bv 32 := 0xfeb612e3.
Lemma F_e2b30 : fetch_word Ubsan.M.loaded_segments (0xe2b64 : word) = Some W_e2b30.
Proof. vm_refl. Qed.
Lemma D_e2b30 : decode_any W_e2b30 = Some (Branch BC_NE 12 11 8164, 4%Z).
Proof. vm_refl. Qed.

Definition W_e2b34 : bv 32 := 0xff1ff06f.
Lemma F_e2b34 : fetch_word Ubsan.M.loaded_segments (0xe2b68 : word) = Some W_e2b34.
Proof. vm_refl. Qed.
Lemma D_e2b34 : decode_any W_e2b34 = Some (Jal 0 2097136, 4%Z).
Proof. vm_refl. Qed.

Definition W_e2b38 : bv 32 := 0x02060063.

Definition W_e2b3c : bv 32 := 0x00054683.

Definition W_e2b40 : bv 32 := 0x0005c703.

Definition W_e2b44 : bv 32 := 0x00e69e63.

Definition W_e2b48 : bv 32 := 0xfff60613.

Definition W_e2b4c : bv 32 := 0x00150513.

Definition W_e2b50 : bv 32 := 0x00158593.

Definition W_e2b54 : bv 32 := 0xfe0614e3.

Definition W_e2b58 : bv 32 := 0x00000513.

Definition W_e2b5c : bv 32 := 0x00008067.

Definition W_e2b60 : bv 32 := 0x40e68533.

Definition W_e2b64 : bv 32 := 0x00008067.

