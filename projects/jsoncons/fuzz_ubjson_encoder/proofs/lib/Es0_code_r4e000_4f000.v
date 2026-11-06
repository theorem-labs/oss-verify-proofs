(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Plain.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_a0fb0 : bv 32 := 0xf9010113.
Lemma F_a0fb0 : fetch_word Plain.M.loaded_segments (0xa0ffc : word) = Some W_a0fb0.
Proof. vm_refl. Qed.
Lemma D_a0fb0 : decode_any W_a0fb0 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0fb4 : bv 32 := 0x06113423.
Lemma F_a0fb4 : fetch_word Plain.M.loaded_segments (0xa1000 : word) = Some W_a0fb4.
Proof. vm_refl. Qed.
Lemma D_a0fb4 : decode_any W_a0fb4 = Some (Store SZ8 2 1 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0fb8 : bv 32 := 0x06813023.
Lemma F_a0fb8 : fetch_word Plain.M.loaded_segments (0xa1004 : word) = Some W_a0fb8.
Proof. vm_refl. Qed.
Lemma D_a0fb8 : decode_any W_a0fb8 = Some (Store SZ8 2 8 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0fbc : bv 32 := 0x04913c23.
Lemma F_a0fbc : fetch_word Plain.M.loaded_segments (0xa1008 : word) = Some W_a0fbc.
Proof. vm_refl. Qed.
Lemma D_a0fbc : decode_any W_a0fbc = Some (Store SZ8 2 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0fc0 : bv 32 := 0x05213823.
Lemma F_a0fc0 : fetch_word Plain.M.loaded_segments (0xa100c : word) = Some W_a0fc0.
Proof. vm_refl. Qed.
Lemma D_a0fc0 : decode_any W_a0fc0 = Some (Store SZ8 2 18 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0fc4 : bv 32 := 0x05313423.
Lemma F_a0fc4 : fetch_word Plain.M.loaded_segments (0xa1010 : word) = Some W_a0fc4.
Proof. vm_refl. Qed.
Lemma D_a0fc4 : decode_any W_a0fc4 = Some (Store SZ8 2 19 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0fc8 : bv 32 := 0x05413023.
Lemma F_a0fc8 : fetch_word Plain.M.loaded_segments (0xa1014 : word) = Some W_a0fc8.
Proof. vm_refl. Qed.
Lemma D_a0fc8 : decode_any W_a0fc8 = Some (Store SZ8 2 20 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0fcc : bv 32 := 0x03513c23.
Lemma F_a0fcc : fetch_word Plain.M.loaded_segments (0xa1018 : word) = Some W_a0fcc.
Proof. vm_refl. Qed.
Lemma D_a0fcc : decode_any W_a0fcc = Some (Store SZ8 2 21 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0fd0 : bv 32 := 0x03613823.
Lemma F_a0fd0 : fetch_word Plain.M.loaded_segments (0xa101c : word) = Some W_a0fd0.
Proof. vm_refl. Qed.
Lemma D_a0fd0 : decode_any W_a0fd0 = Some (Store SZ8 2 22 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0fd4 : bv 32 := 0x00060413.
Lemma F_a0fd4 : fetch_word Plain.M.loaded_segments (0xa1020 : word) = Some W_a0fd4.
Proof. vm_refl. Qed.
Lemma D_a0fd4 : decode_any W_a0fd4 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0fd8 : bv 32 := 0x00050493.
Lemma F_a0fd8 : fetch_word Plain.M.loaded_segments (0xa1024 : word) = Some W_a0fd8.
Proof. vm_refl. Qed.
Lemma D_a0fd8 : decode_any W_a0fd8 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0fdc : bv 32 := 0x00017517.
Lemma F_a0fdc : fetch_word Plain.M.loaded_segments (0xa1028 : word) = Some W_a0fdc.
Proof. vm_refl. Qed.
Lemma D_a0fdc : decode_any W_a0fdc = Some (Auipc 10 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0fe0 : bv 32 := 0x27853a83.
Lemma F_a0fe0 : fetch_word Plain.M.loaded_segments (0xa102c : word) = Some W_a0fe0.
Proof. vm_refl. Qed.
Lemma D_a0fe0 : decode_any W_a0fe0 = Some (Load SZ8 true 21 10 632, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0fe4 : bv 32 := 0x000ab503.
Lemma F_a0fe4 : fetch_word Plain.M.loaded_segments (0xa1030 : word) = Some W_a0fe4.
Proof. vm_refl. Qed.
Lemma D_a0fe4 : decode_any W_a0fe4 = Some (Load SZ8 true 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0fe8 : bv 32 := 0x02a13423.
Lemma F_a0fe8 : fetch_word Plain.M.loaded_segments (0xa1034 : word) = Some W_a0fe8.
Proof. vm_refl. Qed.
Lemma D_a0fe8 : decode_any W_a0fe8 = Some (Store SZ8 2 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0fec : bv 32 := 0x0284b503.
Lemma F_a0fec : fetch_word Plain.M.loaded_segments (0xa1038 : word) = Some W_a0fec.
Proof. vm_refl. Qed.
Lemma D_a0fec : decode_any W_a0fec = Some (Load SZ8 true 10 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0ff0 : bv 32 := 0x0384b603.
Lemma F_a0ff0 : fetch_word Plain.M.loaded_segments (0xa103c : word) = Some W_a0ff0.
Proof. vm_refl. Qed.
Lemma D_a0ff0 : decode_any W_a0ff0 = Some (Load SZ8 true 12 9 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0ff4 : bv 32 := 0x40c50b33.
Lemma F_a0ff4 : fetch_word Plain.M.loaded_segments (0xa1040 : word) = Some W_a0ff4.
Proof. vm_refl. Qed.
Lemma D_a0ff4 : decode_any W_a0ff4 = Some (Op ALU_SUB 22 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0ff8 : bv 32 := 0x00c546b3.
Lemma F_a0ff8 : fetch_word Plain.M.loaded_segments (0xa1044 : word) = Some W_a0ff8.
Proof. vm_refl. Qed.
Lemma D_a0ff8 : decode_any W_a0ff8 = Some (Op ALU_XOR 13 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a0ffc : bv 32 := 0x00c13423.
Lemma F_a0ffc : fetch_word Plain.M.loaded_segments (0xa1048 : word) = Some W_a0ffc.
Proof. vm_refl. Qed.
Lemma D_a0ffc : decode_any W_a0ffc = Some (Store SZ8 2 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1000 : bv 32 := 0x01613823.
Lemma F_a1000 : fetch_word Plain.M.loaded_segments (0xa104c : word) = Some W_a1000.
Proof. vm_refl. Qed.
Lemma D_a1000 : decode_any W_a1000 = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1004 : bv 32 := 0x00b13c23.
Lemma F_a1004 : fetch_word Plain.M.loaded_segments (0xa1050 : word) = Some W_a1004.
Proof. vm_refl. Qed.
Lemma D_a1004 : decode_any W_a1004 = Some (Store SZ8 2 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1008 : bv 32 := 0x02813023.
Lemma F_a1008 : fetch_word Plain.M.loaded_segments (0xa1054 : word) = Some W_a1008.
Proof. vm_refl. Qed.
Lemma D_a1008 : decode_any W_a1008 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a100c : bv 32 := 0x008b0b33.
Lemma F_a100c : fetch_word Plain.M.loaded_segments (0xa1058 : word) = Some W_a100c.
Proof. vm_refl. Qed.
Lemma D_a100c : decode_any W_a100c = Some (Op ALU_ADD 22 22 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1010 : bv 32 := 0x00d03933.
Lemma F_a1010 : fetch_word Plain.M.loaded_segments (0xa105c : word) = Some W_a1010.
Proof. vm_refl. Qed.
Lemma D_a1010 : decode_any W_a1010 = Some (Op ALU_SLTU 18 0 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1014 : bv 32 := 0x00c50663.
Lemma F_a1014 : fetch_word Plain.M.loaded_segments (0xa1060 : word) = Some W_a1014.
Proof. vm_refl. Qed.
Lemma D_a1014 : decode_any W_a1014 = Some (Branch BC_EQ 10 12 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1018 : bv 32 := 0x00810993.
Lemma F_a1018 : fetch_word Plain.M.loaded_segments (0xa1064 : word) = Some W_a1018.
Proof. vm_refl. Qed.
Lemma D_a1018 : decode_any W_a1018 = Some (OpImm ALU_ADD 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a101c : bv 32 := 0x0080006f.
Lemma F_a101c : fetch_word Plain.M.loaded_segments (0xa1068 : word) = Some W_a101c.
Proof. vm_refl. Qed.
Lemma D_a101c : decode_any W_a101c = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1020 : bv 32 := 0x01810993.
Lemma F_a1020 : fetch_word Plain.M.loaded_segments (0xa106c : word) = Some W_a1020.
Proof. vm_refl. Qed.
Lemma D_a1020 : decode_any W_a1020 = Some (OpImm ALU_ADD 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1024 : bv 32 := 0x0784a503.
Lemma F_a1024 : fetch_word Plain.M.loaded_segments (0xa1070 : word) = Some W_a1024.
Proof. vm_refl. Qed.
Lemma D_a1024 : decode_any W_a1024 = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1028 : bv 32 := 0x00190913.
Lemma F_a1028 : fetch_word Plain.M.loaded_segments (0xa1074 : word) = Some W_a1028.
Proof. vm_refl. Qed.
Lemma D_a1028 : decode_any W_a1028 = Some (OpImm ALU_ADD 18 18 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a102c : bv 32 := 0x04200893.
Lemma F_a102c : fetch_word Plain.M.loaded_segments (0xa1078 : word) = Some W_a102c.
Proof. vm_refl. Qed.
Lemma D_a102c : decode_any W_a102c = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1030 : bv 32 := 0x00098593.
Lemma F_a1030 : fetch_word Plain.M.loaded_segments (0xa107c : word) = Some W_a1030.
Proof. vm_refl. Qed.
Lemma D_a1030 : decode_any W_a1030 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1034 : bv 32 := 0x00090613.
Lemma F_a1034 : fetch_word Plain.M.loaded_segments (0xa1080 : word) = Some W_a1034.
Proof. vm_refl. Qed.
Lemma D_a1034 : decode_any W_a1034 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1038 : bv 32 := 0x00000073.
Lemma F_a1038 : fetch_word Plain.M.loaded_segments (0xa1084 : word) = Some W_a1038.
Proof. vm_refl. Qed.
Lemma D_a1038 : decode_any W_a1038 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_a1038 : is_ecall W_a1038 = true.
Proof. reflexivity. Qed.

Definition W_a103c : bv 32 := 0xf31fa0ef.
Lemma F_a103c : fetch_word Plain.M.loaded_segments (0xa1088 : word) = Some W_a103c.
Proof. vm_refl. Qed.
Lemma D_a103c : decode_any W_a103c = Some (Jal 1 2076464, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1040 : bv 32 := 0x09651863.
Lemma F_a1040 : fetch_word Plain.M.loaded_segments (0xa108c : word) = Some W_a1040.
Proof. vm_refl. Qed.
Lemma D_a1040 : decode_any W_a1040 = Some (Branch BC_NE 10 22 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1044 : bv 32 := 0x0584b503.
Lemma F_a1044 : fetch_word Plain.M.loaded_segments (0xa1090 : word) = Some W_a1044.
Proof. vm_refl. Qed.
Lemma D_a1044 : decode_any W_a1044 = Some (Load SZ8 true 10 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1048 : bv 32 := 0x0604b583.
Lemma F_a1048 : fetch_word Plain.M.loaded_segments (0xa1094 : word) = Some W_a1048.
Proof. vm_refl. Qed.
Lemma D_a1048 : decode_any W_a1048 = Some (Load SZ8 true 11 9 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_a104c : bv 32 := 0x00b505b3.
Lemma F_a104c : fetch_word Plain.M.loaded_segments (0xa1098 : word) = Some W_a104c.
Proof. vm_refl. Qed.
Lemma D_a104c : decode_any W_a104c = Some (Op ALU_ADD 11 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1050 : bv 32 := 0x02b4b023.
Lemma F_a1050 : fetch_word Plain.M.loaded_segments (0xa109c : word) = Some W_a1050.
Proof. vm_refl. Qed.
Lemma D_a1050 : decode_any W_a1050 = Some (Store SZ8 9 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1054 : bv 32 := 0x02a4b423.
Lemma F_a1054 : fetch_word Plain.M.loaded_segments (0xa10a0 : word) = Some W_a1054.
Proof. vm_refl. Qed.
Lemma D_a1054 : decode_any W_a1054 = Some (Store SZ8 9 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1058 : bv 32 := 0x02a4bc23.
Lemma F_a1058 : fetch_word Plain.M.loaded_segments (0xa10a4 : word) = Some W_a1058.
Proof. vm_refl. Qed.
Lemma D_a1058 : decode_any W_a1058 = Some (Store SZ8 9 10 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_a105c : bv 32 := 0x00040513.
Lemma F_a105c : fetch_word Plain.M.loaded_segments (0xa10a8 : word) = Some W_a105c.
Proof. vm_refl. Qed.
Lemma D_a105c : decode_any W_a105c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1060 : bv 32 := 0x000ab583.
Lemma F_a1060 : fetch_word Plain.M.loaded_segments (0xa10ac : word) = Some W_a1060.
Proof. vm_refl. Qed.
Lemma D_a1060 : decode_any W_a1060 = Some (Load SZ8 true 11 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1064 : bv 32 := 0x02813603.
Lemma F_a1064 : fetch_word Plain.M.loaded_segments (0xa10b0 : word) = Some W_a1064.
Proof. vm_refl. Qed.
Lemma D_a1064 : decode_any W_a1064 = Some (Load SZ8 true 12 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1068 : bv 32 := 0x0cc59a63.
Lemma F_a1068 : fetch_word Plain.M.loaded_segments (0xa10b4 : word) = Some W_a1068.
Proof. vm_refl. Qed.
Lemma D_a1068 : decode_any W_a1068 = Some (Branch BC_NE 11 12 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_a106c : bv 32 := 0x06813083.
Lemma F_a106c : fetch_word Plain.M.loaded_segments (0xa10b8 : word) = Some W_a106c.
Proof. vm_refl. Qed.
Lemma D_a106c : decode_any W_a106c = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1070 : bv 32 := 0x06013403.
Lemma F_a1070 : fetch_word Plain.M.loaded_segments (0xa10bc : word) = Some W_a1070.
Proof. vm_refl. Qed.
Lemma D_a1070 : decode_any W_a1070 = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1074 : bv 32 := 0x05813483.
Lemma F_a1074 : fetch_word Plain.M.loaded_segments (0xa10c0 : word) = Some W_a1074.
Proof. vm_refl. Qed.
Lemma D_a1074 : decode_any W_a1074 = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1078 : bv 32 := 0x05013903.
Lemma F_a1078 : fetch_word Plain.M.loaded_segments (0xa10c4 : word) = Some W_a1078.
Proof. vm_refl. Qed.
Lemma D_a1078 : decode_any W_a1078 = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_a107c : bv 32 := 0x04813983.
Lemma F_a107c : fetch_word Plain.M.loaded_segments (0xa10c8 : word) = Some W_a107c.
Proof. vm_refl. Qed.
Lemma D_a107c : decode_any W_a107c = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1080 : bv 32 := 0x04013a03.
Lemma F_a1080 : fetch_word Plain.M.loaded_segments (0xa10cc : word) = Some W_a1080.
Proof. vm_refl. Qed.
Lemma D_a1080 : decode_any W_a1080 = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1084 : bv 32 := 0x03813a83.
Lemma F_a1084 : fetch_word Plain.M.loaded_segments (0xa10d0 : word) = Some W_a1084.
Proof. vm_refl. Qed.
Lemma D_a1084 : decode_any W_a1084 = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1088 : bv 32 := 0x03013b03.
Lemma F_a1088 : fetch_word Plain.M.loaded_segments (0xa10d4 : word) = Some W_a1088.
Proof. vm_refl. Qed.
Lemma D_a1088 : decode_any W_a1088 = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_a108c : bv 32 := 0x07010113.
Lemma F_a108c : fetch_word Plain.M.loaded_segments (0xa10d8 : word) = Some W_a108c.
Proof. vm_refl. Qed.
Lemma D_a108c : decode_any W_a108c = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1090 : bv 32 := 0x00008067.
Lemma F_a1090 : fetch_word Plain.M.loaded_segments (0xa10dc : word) = Some W_a1090.
Proof. vm_refl. Qed.
Lemma D_a1090 : decode_any W_a1090 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1094 : bv 32 := 0x00800713.
Lemma F_a1094 : fetch_word Plain.M.loaded_segments (0xa10e0 : word) = Some W_a1094.
Proof. vm_refl. Qed.
Lemma D_a1094 : decode_any W_a1094 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1098 : bv 32 := 0x000a0593.
Lemma F_a1098 : fetch_word Plain.M.loaded_segments (0xa10e4 : word) = Some W_a1098.
Proof. vm_refl. Qed.
Lemma D_a1098 : decode_any W_a1098 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a109c : bv 32 := 0x00e98733.
Lemma F_a109c : fetch_word Plain.M.loaded_segments (0xa10e8 : word) = Some W_a109c.
Proof. vm_refl. Qed.
Lemma D_a109c : decode_any W_a109c = Some (Op ALU_ADD 14 19 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_a10a0 : bv 32 := 0x00073783.
Lemma F_a10a0 : fetch_word Plain.M.loaded_segments (0xa10ec : word) = Some W_a10a0.
Proof. vm_refl. Qed.
Lemma D_a10a0 : decode_any W_a10a0 = Some (Load SZ8 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a10a4 : bv 32 := 0x40ab0b33.
Lemma F_a10a4 : fetch_word Plain.M.loaded_segments (0xa10f0 : word) = Some W_a10a4.
Proof. vm_refl. Qed.
Lemma D_a10a4 : decode_any W_a10a4 = Some (Op ALU_SUB 22 22 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_a10a8 : bv 32 := 0x0784a503.
Lemma F_a10a8 : fetch_word Plain.M.loaded_segments (0xa10f4 : word) = Some W_a10a8.
Proof. vm_refl. Qed.
Lemma D_a10a8 : decode_any W_a10a8 = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_a10ac : bv 32 := 0x40c9093b.
Lemma F_a10ac : fetch_word Plain.M.loaded_segments (0xa10f8 : word) = Some W_a10ac.
Proof. vm_refl. Qed.
Lemma D_a10ac : decode_any W_a10ac = Some (Op32 ALU_SUB 18 18 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a10b0 : bv 32 := 0x40d787b3.
Lemma F_a10b0 : fetch_word Plain.M.loaded_segments (0xa10fc : word) = Some W_a10b0.
Proof. vm_refl. Qed.
Lemma D_a10b0 : decode_any W_a10b0 = Some (Op ALU_SUB 15 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_a10b4 : bv 32 := 0x00f73023.
Lemma F_a10b4 : fetch_word Plain.M.loaded_segments (0xa1100 : word) = Some W_a10b4.
Proof. vm_refl. Qed.
Lemma D_a10b4 : decode_any W_a10b4 = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a10b8 : bv 32 := 0x04200893.
Lemma F_a10b8 : fetch_word Plain.M.loaded_segments (0xa1104 : word) = Some W_a10b8.
Proof. vm_refl. Qed.
Lemma D_a10b8 : decode_any W_a10b8 = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

Definition W_a10bc : bv 32 := 0x00090613.
Lemma F_a10bc : fetch_word Plain.M.loaded_segments (0xa1108 : word) = Some W_a10bc.
Proof. vm_refl. Qed.
Lemma D_a10bc : decode_any W_a10bc = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a10c0 : bv 32 := 0x00000073.
Lemma F_a10c0 : fetch_word Plain.M.loaded_segments (0xa110c : word) = Some W_a10c0.
Proof. vm_refl. Qed.
Lemma D_a10c0 : decode_any W_a10c0 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_a10c0 : is_ecall W_a10c0 = true.
Proof. reflexivity. Qed.

Definition W_a10c4 : bv 32 := 0xea9fa0ef.
Lemma F_a10c4 : fetch_word Plain.M.loaded_segments (0xa1110 : word) = Some W_a10c4.
Proof. vm_refl. Qed.
Lemma D_a10c4 : decode_any W_a10c4 = Some (Jal 1 2076328, 4%Z).
Proof. vm_refl. Qed.

Definition W_a10c8 : bv 32 := 0x000a0993.
Lemma F_a10c8 : fetch_word Plain.M.loaded_segments (0xa1114 : word) = Some W_a10c8.
Proof. vm_refl. Qed.
Lemma D_a10c8 : decode_any W_a10c8 = Some (OpImm ALU_ADD 19 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a10cc : bv 32 := 0xf7650ce3.
Lemma F_a10cc : fetch_word Plain.M.loaded_segments (0xa1118 : word) = Some W_a10cc.
Proof. vm_refl. Qed.
Lemma D_a10cc : decode_any W_a10cc = Some (Branch BC_EQ 10 22 8056, 4%Z).
Proof. vm_refl. Qed.

Definition W_a10d0 : bv 32 := 0x02054c63.
Lemma F_a10d0 : fetch_word Plain.M.loaded_segments (0xa111c : word) = Some W_a10d0.
Proof. vm_refl. Qed.
Lemma D_a10d0 : decode_any W_a10d0 = Some (Branch BC_LT 10 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_a10d4 : bv 32 := 0x0089b583.
Lemma F_a10d4 : fetch_word Plain.M.loaded_segments (0xa1120 : word) = Some W_a10d4.
Proof. vm_refl. Qed.
Lemma D_a10d4 : decode_any W_a10d4 = Some (Load SZ8 true 11 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a10d8 : bv 32 := 0x00a5b633.
Lemma F_a10d8 : fetch_word Plain.M.loaded_segments (0xa1124 : word) = Some W_a10d8.
Proof. vm_refl. Qed.
Lemma D_a10d8 : decode_any W_a10d8 = Some (Op ALU_SLTU 12 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_a10dc : bv 32 := 0x00461a13.
Lemma F_a10dc : fetch_word Plain.M.loaded_segments (0xa1128 : word) = Some W_a10dc.
Proof. vm_refl. Qed.
Lemma D_a10dc : decode_any W_a10dc = Some (ShiftImm ALU_SLL 20 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_a10e0 : bv 32 := 0x01498a33.
Lemma F_a10e0 : fetch_word Plain.M.loaded_segments (0xa112c : word) = Some W_a10e0.
Proof. vm_refl. Qed.
Lemma D_a10e0 : decode_any W_a10e0 = Some (Op ALU_ADD 20 19 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_a10e4 : bv 32 := 0x000a3703.
Lemma F_a10e4 : fetch_word Plain.M.loaded_segments (0xa1130 : word) = Some W_a10e4.
Proof. vm_refl. Qed.
Lemma D_a10e4 : decode_any W_a10e4 = Some (Load SZ8 true 14 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a10e8 : bv 32 := 0x40c006b3.
Lemma F_a10e8 : fetch_word Plain.M.loaded_segments (0xa1134 : word) = Some W_a10e8.
Proof. vm_refl. Qed.
Lemma D_a10e8 : decode_any W_a10e8 = Some (Op ALU_SUB 13 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_a10ec : bv 32 := 0x00b6f6b3.
Lemma F_a10ec : fetch_word Plain.M.loaded_segments (0xa1138 : word) = Some W_a10ec.
Proof. vm_refl. Qed.
Lemma D_a10ec : decode_any W_a10ec = Some (Op ALU_AND 13 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_a10f0 : bv 32 := 0x40d506b3.
Lemma F_a10f0 : fetch_word Plain.M.loaded_segments (0xa113c : word) = Some W_a10f0.
Proof. vm_refl. Qed.
Lemma D_a10f0 : decode_any W_a10f0 = Some (Op ALU_SUB 13 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_a10f4 : bv 32 := 0x00d70733.
Lemma F_a10f4 : fetch_word Plain.M.loaded_segments (0xa1140 : word) = Some W_a10f4.
Proof. vm_refl. Qed.
Lemma D_a10f4 : decode_any W_a10f4 = Some (Op ALU_ADD 14 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_a10f8 : bv 32 := 0x00ea3023.
Lemma F_a10f8 : fetch_word Plain.M.loaded_segments (0xa1144 : word) = Some W_a10f8.
Proof. vm_refl. Qed.
Lemma D_a10f8 : decode_any W_a10f8 = Some (Store SZ8 20 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a10fc : bv 32 := 0xf8a5fce3.
Lemma F_a10fc : fetch_word Plain.M.loaded_segments (0xa1148 : word) = Some W_a10fc.
Proof. vm_refl. Qed.
Lemma D_a10fc : decode_any W_a10fc = Some (Branch BC_GEU 11 10 8088, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1100 : bv 32 := 0x01800713.
Lemma F_a1100 : fetch_word Plain.M.loaded_segments (0xa114c : word) = Some W_a1100.
Proof. vm_refl. Qed.
Lemma D_a1100 : decode_any W_a1100 = Some (OpImm ALU_ADD 14 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1104 : bv 32 := 0xf95ff06f.
Lemma F_a1104 : fetch_word Plain.M.loaded_segments (0xa1150 : word) = Some W_a1104.
Proof. vm_refl. Qed.
Lemma D_a1104 : decode_any W_a1104 = Some (Jal 0 2097044, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1148 : bv 32 := 0x00008067.
Lemma F_a1148 : fetch_word Plain.M.loaded_segments (0xa1194 : word) = Some W_a1148.
Proof. vm_refl. Qed.
Lemma D_a1148 : decode_any W_a1148 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1878 : bv 32 := 0xff010113.
Lemma F_a1878 : fetch_word Plain.M.loaded_segments (0xa18c4 : word) = Some W_a1878.
Proof. vm_refl. Qed.
Lemma D_a1878 : decode_any W_a1878 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_a187c : bv 32 := 0x00113423.
Lemma F_a187c : fetch_word Plain.M.loaded_segments (0xa18c8 : word) = Some W_a187c.
Proof. vm_refl. Qed.
Lemma D_a187c : decode_any W_a187c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1880 : bv 32 := 0x00813023.
Lemma F_a1880 : fetch_word Plain.M.loaded_segments (0xa18cc : word) = Some W_a1880.
Proof. vm_refl. Qed.
Lemma D_a1880 : decode_any W_a1880 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1884 : bv 32 := 0x0004a517.
Lemma F_a1884 : fetch_word Plain.M.loaded_segments (0xa18d0 : word) = Some W_a1884.
Proof. vm_refl. Qed.
Lemma D_a1884 : decode_any W_a1884 = Some (Auipc 10 74, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1888 : bv 32 := 0xf4050413.
Lemma F_a1888 : fetch_word Plain.M.loaded_segments (0xa18d4 : word) = Some W_a1888.
Proof. vm_refl. Qed.
Lemma D_a1888 : decode_any W_a1888 = Some (OpImm ALU_ADD 8 10 3904, 4%Z).
Proof. vm_refl. Qed.

Definition W_a188c : bv 32 := 0x00040513.
Lemma F_a188c : fetch_word Plain.M.loaded_segments (0xa18d8 : word) = Some W_a188c.
Proof. vm_refl. Qed.
Lemma D_a188c : decode_any W_a188c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1890 : bv 32 := 0x0410b0ef.
Lemma F_a1890 : fetch_word Plain.M.loaded_segments (0xa18dc : word) = Some W_a1890.
Proof. vm_refl. Qed.
Lemma D_a1890 : decode_any W_a1890 = Some (Jal 1 47168, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1894 : bv 32 := 0x00840513.
Lemma F_a1894 : fetch_word Plain.M.loaded_segments (0xa18e0 : word) = Some W_a1894.
Proof. vm_refl. Qed.
Lemma D_a1894 : decode_any W_a1894 = Some (OpImm ALU_ADD 10 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1898 : bv 32 := 0x00813083.
Lemma F_a1898 : fetch_word Plain.M.loaded_segments (0xa18e4 : word) = Some W_a1898.
Proof. vm_refl. Qed.
Lemma D_a1898 : decode_any W_a1898 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a189c : bv 32 := 0x00013403.
Lemma F_a189c : fetch_word Plain.M.loaded_segments (0xa18e8 : word) = Some W_a189c.
Proof. vm_refl. Qed.
Lemma D_a189c : decode_any W_a189c = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a18a0 : bv 32 := 0x01010113.
Lemma F_a18a0 : fetch_word Plain.M.loaded_segments (0xa18ec : word) = Some W_a18a0.
Proof. vm_refl. Qed.
Lemma D_a18a0 : decode_any W_a18a0 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a18a4 : bv 32 := 0x00008067.
Lemma F_a18a4 : fetch_word Plain.M.loaded_segments (0xa18f0 : word) = Some W_a18a4.
Proof. vm_refl. Qed.
Lemma D_a18a4 : decode_any W_a18a4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
