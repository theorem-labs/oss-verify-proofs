(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Ubsan.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StepTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.WalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StartupTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SumWalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MemSplit OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ShapeAlg OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SRealizes OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefReadLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibEff OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MmapSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SumMemcpyBase OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SumMemcpy OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibMaskBits OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.U1Layout.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.CRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.U1Facts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.U1Lib_Cxx_OperatorDelete.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Module U1_code_6a07c_6a21c.

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Ubsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_6a07c : bv 32 := 0xfb010113.
Lemma F_6a07c : fetch_word Ubsan.M.loaded_segments (0x6a0bc : word) = Some W_6a07c.
Proof. vm_refl. Qed.
Lemma D_6a07c : decode_any W_6a07c = Some (OpImm ALU_ADD 2 2 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a080 : bv 32 := 0x04113423.
Lemma F_6a080 : fetch_word Ubsan.M.loaded_segments (0x6a0c0 : word) = Some W_6a080.
Proof. vm_refl. Qed.
Lemma D_6a080 : decode_any W_6a080 = Some (Store SZ8 2 1 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a084 : bv 32 := 0x04813023.
Lemma F_6a084 : fetch_word Ubsan.M.loaded_segments (0x6a0c4 : word) = Some W_6a084.
Proof. vm_refl. Qed.
Lemma D_6a084 : decode_any W_6a084 = Some (Store SZ8 2 8 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a088 : bv 32 := 0x02913c23.
Lemma F_6a088 : fetch_word Ubsan.M.loaded_segments (0x6a0c8 : word) = Some W_6a088.
Proof. vm_refl. Qed.
Lemma D_6a088 : decode_any W_6a088 = Some (Store SZ8 2 9 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a08c : bv 32 := 0x03213823.
Lemma F_6a08c : fetch_word Ubsan.M.loaded_segments (0x6a0cc : word) = Some W_6a08c.
Proof. vm_refl. Qed.
Lemma D_6a08c : decode_any W_6a08c = Some (Store SZ8 2 18 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a090 : bv 32 := 0x03313423.
Lemma F_6a090 : fetch_word Ubsan.M.loaded_segments (0x6a0d0 : word) = Some W_6a090.
Proof. vm_refl. Qed.
Lemma D_6a090 : decode_any W_6a090 = Some (Store SZ8 2 19 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a094 : bv 32 := 0x03413023.
Lemma F_6a094 : fetch_word Ubsan.M.loaded_segments (0x6a0d4 : word) = Some W_6a094.
Proof. vm_refl. Qed.
Lemma D_6a094 : decode_any W_6a094 = Some (Store SZ8 2 20 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a098 : bv 32 := 0x01513c23.
Lemma F_6a098 : fetch_word Ubsan.M.loaded_segments (0x6a0d8 : word) = Some W_6a098.
Proof. vm_refl. Qed.
Lemma D_6a098 : decode_any W_6a098 = Some (Store SZ8 2 21 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a09c : bv 32 := 0x01613823.
Lemma F_6a09c : fetch_word Ubsan.M.loaded_segments (0x6a0dc : word) = Some W_6a09c.
Proof. vm_refl. Qed.
Lemma D_6a09c : decode_any W_6a09c = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a0a0 : bv 32 := 0x01713423.
Lemma F_6a0a0 : fetch_word Ubsan.M.loaded_segments (0x6a0e0 : word) = Some W_6a0a0.
Proof. vm_refl. Qed.
Lemma D_6a0a0 : decode_any W_6a0a0 = Some (Store SZ8 2 23 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a0a4 : bv 32 := 0x01813023.
Lemma F_6a0a4 : fetch_word Ubsan.M.loaded_segments (0x6a0e4 : word) = Some W_6a0a4.
Proof. vm_refl. Qed.
Lemma D_6a0a4 : decode_any W_6a0a4 = Some (Store SZ8 2 24 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a0a8 : bv 32 := 0x00050493.
Lemma F_6a0a8 : fetch_word Ubsan.M.loaded_segments (0x6a0e8 : word) = Some W_6a0a8.
Proof. vm_refl. Qed.
Lemma D_6a0a8 : decode_any W_6a0a8 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a0ac : bv 32 := 0x00053403.
Lemma F_6a0ac : fetch_word Ubsan.M.loaded_segments (0x6a0ec : word) = Some W_6a0ac.
Proof. vm_refl. Qed.
Lemma D_6a0ac : decode_any W_6a0ac = Some (Load SZ8 true 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a0b0 : bv 32 := 0x00853503.
Lemma F_6a0b0 : fetch_word Ubsan.M.loaded_segments (0x6a0f0 : word) = Some W_6a0b0.
Proof. vm_refl. Qed.
Lemma D_6a0b0 : decode_any W_6a0b0 = Some (Load SZ8 true 10 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a0b4 : bv 32 := 0x408509b3.
Lemma F_6a0b4 : fetch_word Ubsan.M.loaded_segments (0x6a0f4 : word) = Some W_6a0b4.
Proof. vm_refl. Qed.
Lemma D_6a0b4 : decode_any W_6a0b4 = Some (Op ALU_SUB 19 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a0b8 : bv 32 := 0x4029db13.
Lemma F_6a0b8 : fetch_word Ubsan.M.loaded_segments (0x6a0f8 : word) = Some W_6a0b8.
Proof. vm_refl. Qed.
Lemma D_6a0b8 : decode_any W_6a0b8 = Some (ShiftImm ALU_SRA 22 19 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a0bc : bv 32 := 0x001b0513.
Lemma F_6a0bc : fetch_word Ubsan.M.loaded_segments (0x6a0fc : word) = Some W_6a0bc.
Proof. vm_refl. Qed.
Lemma D_6a0bc : decode_any W_6a0bc = Some (OpImm ALU_ADD 10 22 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a0c0 : bv 32 := 0x03e55613.
Lemma F_6a0c0 : fetch_word Ubsan.M.loaded_segments (0x6a100 : word) = Some W_6a0c0.
Proof. vm_refl. Qed.
Lemma D_6a0c0 : decode_any W_6a0c0 = Some (ShiftImm ALU_SRL 12 10 62, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a0c4 : bv 32 := 0x14061463.
Lemma F_6a0c4 : fetch_word Ubsan.M.loaded_segments (0x6a104 : word) = Some W_6a0c4.
Proof. vm_refl. Qed.
Lemma D_6a0c4 : decode_any W_6a0c4 = Some (Branch BC_NE 12 0 328, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a0c8 : bv 32 := 0x00058a13.
Lemma F_6a0c8 : fetch_word Ubsan.M.loaded_segments (0x6a108 : word) = Some W_6a0c8.
Proof. vm_refl. Qed.
Lemma D_6a0c8 : decode_any W_6a0c8 = Some (OpImm ALU_ADD 20 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a0cc : bv 32 := 0x0104b583.
Lemma F_6a0cc : fetch_word Ubsan.M.loaded_segments (0x6a10c : word) = Some W_6a0cc.
Proof. vm_refl. Qed.
Lemma D_6a0cc : decode_any W_6a0cc = Some (Load SZ8 true 11 9 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a0d0 : bv 32 := 0x40858933.
Lemma F_6a0d0 : fetch_word Ubsan.M.loaded_segments (0x6a110 : word) = Some W_6a0d0.
Proof. vm_refl. Qed.
Lemma D_6a0d0 : decode_any W_6a0d0 = Some (Op ALU_SUB 18 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a0d4 : bv 32 := 0x00195c13.
Lemma F_6a0d4 : fetch_word Ubsan.M.loaded_segments (0x6a114 : word) = Some W_6a0d4.
Proof. vm_refl. Qed.
Lemma D_6a0d4 : decode_any W_6a0d4 = Some (ShiftImm ALU_SRL 24 18 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a0d8 : bv 32 := 0x03857a63.
Lemma F_6a0d8 : fetch_word Ubsan.M.loaded_segments (0x6a118 : word) = Some W_6a0d8.
Proof. vm_refl. Qed.
Lemma D_6a0d8 : decode_any W_6a0d8 = Some (Branch BC_GEU 10 24 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a0dc : bv 32 := 0xff900513.
Lemma F_6a0dc : fetch_word Ubsan.M.loaded_segments (0x6a11c : word) = Some W_6a0dc.
Proof. vm_refl. Qed.
Lemma D_6a0dc : decode_any W_6a0dc = Some (OpImm ALU_ADD 10 0 4089, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a0e0 : bv 32 := 0x00155513.
Lemma F_6a0e0 : fetch_word Ubsan.M.loaded_segments (0x6a120 : word) = Some W_6a0e0.
Proof. vm_refl. Qed.
Lemma D_6a0e0 : decode_any W_6a0e0 = Some (ShiftImm ALU_SRL 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a0e4 : bv 32 := 0x02a97c63.
Lemma F_6a0e4 : fetch_word Ubsan.M.loaded_segments (0x6a124 : word) = Some W_6a0e4.
Proof. vm_refl. Qed.
Lemma D_6a0e4 : decode_any W_6a0e4 = Some (Branch BC_GEU 18 10 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a0e8 : bv 32 := 0x002c1a93.
Lemma F_6a0e8 : fetch_word Ubsan.M.loaded_segments (0x6a128 : word) = Some W_6a0e8.
Proof. vm_refl. Qed.
Lemma D_6a0e8 : decode_any W_6a0e8 = Some (ShiftImm ALU_SLL 21 24 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a0ec : bv 32 := 0x040c0063.
Lemma F_6a0ec : fetch_word Ubsan.M.loaded_segments (0x6a12c : word) = Some W_6a0ec.
Proof. vm_refl. Qed.
Lemma D_6a0ec : decode_any W_6a0ec = Some (Branch BC_EQ 24 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a0f0 : bv 32 := 0x03ec5513.
Lemma F_6a0f0 : fetch_word Ubsan.M.loaded_segments (0x6a130 : word) = Some W_6a0f0.
Proof. vm_refl. Qed.
Lemma D_6a0f0 : decode_any W_6a0f0 = Some (ShiftImm ALU_SRL 10 24 62, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a0f4 : bv 32 := 0x12051063.
Lemma F_6a0f4 : fetch_word Ubsan.M.loaded_segments (0x6a134 : word) = Some W_6a0f4.
Proof. vm_refl. Qed.
Lemma D_6a0f4 : decode_any W_6a0f4 = Some (Branch BC_NE 10 0 288, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a0f8 : bv 32 := 0x000a8513.
Lemma F_6a0f8 : fetch_word Ubsan.M.loaded_segments (0x6a138 : word) = Some W_6a0f8.
Proof. vm_refl. Qed.
Lemma D_6a0f8 : decode_any W_6a0f8 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a0fc : bv 32 := 0x1f97d0ef.
Lemma F_6a0fc : fetch_word Ubsan.M.loaded_segments (0x6a13c : word) = Some W_6a0fc.
Proof. vm_refl. Qed.
Lemma D_6a0fc : decode_any W_6a0fc = Some (Jal 1 514552, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a100 : bv 32 := 0x013505b3.
Lemma F_6a100 : fetch_word Ubsan.M.loaded_segments (0x6a140 : word) = Some W_6a100.
Proof. vm_refl. Qed.
Lemma D_6a100 : decode_any W_6a100 = Some (Op ALU_ADD 11 10 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a104 : bv 32 := 0x02a5fa63.
Lemma F_6a104 : fetch_word Ubsan.M.loaded_segments (0x6a144 : word) = Some W_6a104.
Proof. vm_refl. Qed.
Lemma D_6a104 : decode_any W_6a104 = Some (Branch BC_GEU 11 10 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a10c : bv 32 := 0x00050c13.
Lemma F_6a10c : fetch_word Ubsan.M.loaded_segments (0x6a14c : word) = Some W_6a10c.
Proof. vm_refl. Qed.
Lemma D_6a10c : decode_any W_6a10c = Some (OpImm ALU_ADD 24 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a110 : bv 32 := 0xff900513.
Lemma F_6a110 : fetch_word Ubsan.M.loaded_segments (0x6a150 : word) = Some W_6a110.
Proof. vm_refl. Qed.
Lemma D_6a110 : decode_any W_6a110 = Some (OpImm ALU_ADD 10 0 4089, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a114 : bv 32 := 0x00155513.
Lemma F_6a114 : fetch_word Ubsan.M.loaded_segments (0x6a154 : word) = Some W_6a114.
Proof. vm_refl. Qed.
Lemma D_6a114 : decode_any W_6a114 = Some (ShiftImm ALU_SRL 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a118 : bv 32 := 0xfca968e3.
Lemma F_6a118 : fetch_word Ubsan.M.loaded_segments (0x6a158 : word) = Some W_6a118.
Proof. vm_refl. Qed.
Lemma D_6a118 : decode_any W_6a118 = Some (Branch BC_LTU 18 10 8144, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a138 : bv 32 := 0x00a03633.
Lemma F_6a138 : fetch_word Ubsan.M.loaded_segments (0x6a178 : word) = Some W_6a138.
Proof. vm_refl. Qed.
Lemma D_6a138 : decode_any W_6a138 = Some (Op ALU_SLTU 12 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a13c : bv 32 := 0x0015b693.
Lemma F_6a13c : fetch_word Ubsan.M.loaded_segments (0x6a17c : word) = Some W_6a13c.
Proof. vm_refl. Qed.
Lemma D_6a13c : decode_any W_6a13c = Some (OpImm ALU_SLTU 13 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a140 : bv 32 := 0x00d646b3.
Lemma F_6a140 : fetch_word Ubsan.M.loaded_segments (0x6a180 : word) = Some W_6a140.
Proof. vm_refl. Qed.
Lemma D_6a140 : decode_any W_6a140 = Some (Op ALU_XOR 13 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a144 : bv 32 := 0x0c068a63.
Lemma F_6a144 : fetch_word Ubsan.M.loaded_segments (0x6a184 : word) = Some W_6a144.
Proof. vm_refl. Qed.
Lemma D_6a144 : decode_any W_6a144 = Some (Branch BC_EQ 13 0 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a148 : bv 32 := 0x00aa8bb3.
Lemma F_6a148 : fetch_word Ubsan.M.loaded_segments (0x6a188 : word) = Some W_6a148.
Proof. vm_refl. Qed.
Lemma D_6a148 : decode_any W_6a148 = Some (Op ALU_ADD 23 21 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a14c : bv 32 := 0x001bb693.
Lemma F_6a14c : fetch_word Ubsan.M.loaded_segments (0x6a18c : word) = Some W_6a14c.
Proof. vm_refl. Qed.
Lemma D_6a14c : decode_any W_6a14c = Some (OpImm ALU_SLTU 13 23 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a150 : bv 32 := 0x0cd60463.
Lemma F_6a150 : fetch_word Ubsan.M.loaded_segments (0x6a190 : word) = Some W_6a150.
Proof. vm_refl. Qed.
Lemma D_6a150 : decode_any W_6a150 = Some (Branch BC_EQ 12 13 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a154 : bv 32 := 0x03dc5613.
Lemma F_6a154 : fetch_word Ubsan.M.loaded_segments (0x6a194 : word) = Some W_6a154.
Proof. vm_refl. Qed.
Lemma D_6a154 : decode_any W_6a154 = Some (ShiftImm ALU_SRL 12 24 61, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a158 : bv 32 := 0x0c061063.
Lemma F_6a158 : fetch_word Ubsan.M.loaded_segments (0x6a198 : word) = Some W_6a158.
Proof. vm_refl. Qed.
Lemma D_6a158 : decode_any W_6a158 = Some (Branch BC_NE 12 0 192, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a15c : bv 32 := 0x0aabee63.
Lemma F_6a15c : fetch_word Ubsan.M.loaded_segments (0x6a19c : word) = Some W_6a15c.
Proof. vm_refl. Qed.
Lemma D_6a15c : decode_any W_6a15c = Some (Branch BC_LTU 23 10 188, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a160 : bv 32 := 0x0035f613.
Lemma F_6a160 : fetch_word Ubsan.M.loaded_segments (0x6a1a0 : word) = Some W_6a160.
Proof. vm_refl. Qed.
Lemma D_6a160 : decode_any W_6a160 = Some (OpImm ALU_AND 12 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a164 : bv 32 := 0x0a061a63.
Lemma F_6a164 : fetch_word Ubsan.M.loaded_segments (0x6a1a4 : word) = Some W_6a164.
Proof. vm_refl. Qed.
Lemma D_6a164 : decode_any W_6a164 = Some (Branch BC_NE 12 0 180, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a168 : bv 32 := 0x0a050863.
Lemma F_6a168 : fetch_word Ubsan.M.loaded_segments (0x6a1a8 : word) = Some W_6a168.
Proof. vm_refl. Qed.
Lemma D_6a168 : decode_any W_6a168 = Some (Branch BC_EQ 10 0 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a16c : bv 32 := 0x000a2503.
Lemma F_6a16c : fetch_word Ubsan.M.loaded_segments (0x6a1ac : word) = Some W_6a16c.
Proof. vm_refl. Qed.
Lemma D_6a16c : decode_any W_6a16c = Some (Load SZ4 true 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a170 : bv 32 := 0x00a5a023.
Lemma F_6a170 : fetch_word Ubsan.M.loaded_segments (0x6a1b0 : word) = Some W_6a170.
Proof. vm_refl. Qed.
Lemma D_6a170 : decode_any W_6a170 = Some (Store SZ4 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a174 : bv 32 := 0x0a058263.
Lemma F_6a174 : fetch_word Ubsan.M.loaded_segments (0x6a1b4 : word) = Some W_6a174.
Proof. vm_refl. Qed.
Lemma D_6a174 : decode_any W_6a174 = Some (Branch BC_EQ 11 0 164, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a178 : bv 32 := 0xffc00513.
Lemma F_6a178 : fetch_word Ubsan.M.loaded_segments (0x6a1b8 : word) = Some W_6a178.
Proof. vm_refl. Qed.
Lemma D_6a178 : decode_any W_6a178 = Some (OpImm ALU_ADD 10 0 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a17c : bv 32 := 0x08a58e63.
Lemma F_6a17c : fetch_word Ubsan.M.loaded_segments (0x6a1bc : word) = Some W_6a17c.
Proof. vm_refl. Qed.
Lemma D_6a17c : decode_any W_6a17c = Some (Branch BC_EQ 11 10 156, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a180 : bv 32 := 0x002b1513.
Lemma F_6a180 : fetch_word Ubsan.M.loaded_segments (0x6a1c0 : word) = Some W_6a180.
Proof. vm_refl. Qed.
Lemma D_6a180 : decode_any W_6a180 = Some (ShiftImm ALU_SLL 10 22 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a184 : bv 32 := 0x40a58a33.
Lemma F_6a184 : fetch_word Ubsan.M.loaded_segments (0x6a1c4 : word) = Some W_6a184.
Proof. vm_refl. Qed.
Lemma D_6a184 : decode_any W_6a184 = Some (Op ALU_SUB 20 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a188 : bv 32 := 0x080a0863.
Lemma F_6a188 : fetch_word Ubsan.M.loaded_segments (0x6a1c8 : word) = Some W_6a188.
Proof. vm_refl. Qed.
Lemma D_6a188 : decode_any W_6a188 = Some (Branch BC_EQ 20 0 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a18c : bv 32 := 0x00ba3533.
Lemma F_6a18c : fetch_word Ubsan.M.loaded_segments (0x6a1cc : word) = Some W_6a18c.
Proof. vm_refl. Qed.
Lemma D_6a18c : decode_any W_6a18c = Some (Op ALU_SLTU 10 20 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a190 : bv 32 := 0x01602633.
Lemma F_6a190 : fetch_word Ubsan.M.loaded_segments (0x6a1d0 : word) = Some W_6a190.
Proof. vm_refl. Qed.
Lemma D_6a190 : decode_any W_6a190 = Some (Op ALU_SLT 12 0 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a194 : bv 32 := 0x00c54533.
Lemma F_6a194 : fetch_word Ubsan.M.loaded_segments (0x6a1d4 : word) = Some W_6a194.
Proof. vm_refl. Qed.
Lemma D_6a194 : decode_any W_6a194 = Some (Op ALU_XOR 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a198 : bv 32 := 0x00154513.
Lemma F_6a198 : fetch_word Ubsan.M.loaded_segments (0x6a1d8 : word) = Some W_6a198.
Proof. vm_refl. Qed.
Lemma D_6a198 : decode_any W_6a198 = Some (OpImm ALU_XOR 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a19c : bv 32 := 0x06050e63.
Lemma F_6a19c : fetch_word Ubsan.M.loaded_segments (0x6a1dc : word) = Some W_6a19c.
Proof. vm_refl. Qed.
Lemma D_6a19c : decode_any W_6a19c = Some (Branch BC_EQ 10 0 124, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a1a0 : bv 32 := 0x00347513.
Lemma F_6a1a0 : fetch_word Ubsan.M.loaded_segments (0x6a1e0 : word) = Some W_6a1a0.
Proof. vm_refl. Qed.
Lemma D_6a1a0 : decode_any W_6a1a0 = Some (OpImm ALU_AND 10 8 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a1a4 : bv 32 := 0x06051a63.
Lemma F_6a1a4 : fetch_word Ubsan.M.loaded_segments (0x6a1e4 : word) = Some W_6a1a4.
Proof. vm_refl. Qed.
Lemma D_6a1a4 : decode_any W_6a1a4 = Some (Branch BC_NE 10 0 116, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a1a8 : bv 32 := 0x00458a93.
Lemma F_6a1a8 : fetch_word Ubsan.M.loaded_segments (0x6a1e8 : word) = Some W_6a1a8.
Proof. vm_refl. Qed.
Lemma D_6a1a8 : decode_any W_6a1a8 = Some (OpImm ALU_ADD 21 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a1ac : bv 32 := 0x000a0513.
Lemma F_6a1ac : fetch_word Ubsan.M.loaded_segments (0x6a1ec : word) = Some W_6a1ac.
Proof. vm_refl. Qed.
Lemma D_6a1ac : decode_any W_6a1ac = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a1b0 : bv 32 := 0x00040593.
Lemma F_6a1b0 : fetch_word Ubsan.M.loaded_segments (0x6a1f0 : word) = Some W_6a1b0.
Proof. vm_refl. Qed.
Lemma D_6a1b0 : decode_any W_6a1b0 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a1b4 : bv 32 := 0x00098613.
Lemma F_6a1b4 : fetch_word Ubsan.M.loaded_segments (0x6a1f4 : word) = Some W_6a1b4.
Proof. vm_refl. Qed.
Lemma D_6a1b4 : decode_any W_6a1b4 = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a1b8 : bv 32 := 0x1a5780ef.
Lemma F_6a1b8 : fetch_word Ubsan.M.loaded_segments (0x6a1f8 : word) = Some W_6a1b8.
Proof. vm_refl. Qed.
Lemma D_6a1b8 : decode_any W_6a1b8 = Some (Jal 1 493988, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a1bc : bv 32 := 0x0144b023.
Lemma F_6a1bc : fetch_word Ubsan.M.loaded_segments (0x6a1fc : word) = Some W_6a1bc.
Proof. vm_refl. Qed.
Lemma D_6a1bc : decode_any W_6a1bc = Some (Store SZ8 9 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a1c0 : bv 32 := 0x0154b423.
Lemma F_6a1c0 : fetch_word Ubsan.M.loaded_segments (0x6a200 : word) = Some W_6a1c0.
Proof. vm_refl. Qed.
Lemma D_6a1c0 : decode_any W_6a1c0 = Some (Store SZ8 9 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a1c4 : bv 32 := 0x0174b823.
Lemma F_6a1c4 : fetch_word Ubsan.M.loaded_segments (0x6a204 : word) = Some W_6a1c4.
Proof. vm_refl. Qed.
Lemma D_6a1c4 : decode_any W_6a1c4 = Some (Store SZ8 9 23 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a1c8 : bv 32 := 0x00040863.
Lemma F_6a1c8 : fetch_word Ubsan.M.loaded_segments (0x6a208 : word) = Some W_6a1c8.
Proof. vm_refl. Qed.
Lemma D_6a1c8 : decode_any W_6a1c8 = Some (Branch BC_EQ 8 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a1cc : bv 32 := 0x00040513.
Lemma F_6a1cc : fetch_word Ubsan.M.loaded_segments (0x6a20c : word) = Some W_6a1cc.
Proof. vm_refl. Qed.
Lemma D_6a1cc : decode_any W_6a1cc = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a1d0 : bv 32 := 0x00090593.
Lemma F_6a1d0 : fetch_word Ubsan.M.loaded_segments (0x6a210 : word) = Some W_6a1d0.
Proof. vm_refl. Qed.
Lemma D_6a1d0 : decode_any W_6a1d0 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a1d4 : bv 32 := 0x6b8050ef.
Lemma F_6a1d4 : fetch_word Ubsan.M.loaded_segments (0x6a214 : word) = Some W_6a1d4.
Proof. vm_refl. Qed.
Lemma D_6a1d4 : decode_any W_6a1d4 = Some (Jal 1 22200, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a1d8 : bv 32 := 0x000a8513.
Lemma F_6a1d8 : fetch_word Ubsan.M.loaded_segments (0x6a218 : word) = Some W_6a1d8.
Proof. vm_refl. Qed.
Lemma D_6a1d8 : decode_any W_6a1d8 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a1dc : bv 32 := 0x04813083.
Lemma F_6a1dc : fetch_word Ubsan.M.loaded_segments (0x6a21c : word) = Some W_6a1dc.
Proof. vm_refl. Qed.
Lemma D_6a1dc : decode_any W_6a1dc = Some (Load SZ8 true 1 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a1e0 : bv 32 := 0x04013403.
Lemma F_6a1e0 : fetch_word Ubsan.M.loaded_segments (0x6a220 : word) = Some W_6a1e0.
Proof. vm_refl. Qed.
Lemma D_6a1e0 : decode_any W_6a1e0 = Some (Load SZ8 true 8 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a1e4 : bv 32 := 0x03813483.
Lemma F_6a1e4 : fetch_word Ubsan.M.loaded_segments (0x6a224 : word) = Some W_6a1e4.
Proof. vm_refl. Qed.
Lemma D_6a1e4 : decode_any W_6a1e4 = Some (Load SZ8 true 9 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a1e8 : bv 32 := 0x03013903.
Lemma F_6a1e8 : fetch_word Ubsan.M.loaded_segments (0x6a228 : word) = Some W_6a1e8.
Proof. vm_refl. Qed.
Lemma D_6a1e8 : decode_any W_6a1e8 = Some (Load SZ8 true 18 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a1ec : bv 32 := 0x02813983.
Lemma F_6a1ec : fetch_word Ubsan.M.loaded_segments (0x6a22c : word) = Some W_6a1ec.
Proof. vm_refl. Qed.
Lemma D_6a1ec : decode_any W_6a1ec = Some (Load SZ8 true 19 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a1f0 : bv 32 := 0x02013a03.
Lemma F_6a1f0 : fetch_word Ubsan.M.loaded_segments (0x6a230 : word) = Some W_6a1f0.
Proof. vm_refl. Qed.
Lemma D_6a1f0 : decode_any W_6a1f0 = Some (Load SZ8 true 20 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a1f4 : bv 32 := 0x01813a83.
Lemma F_6a1f4 : fetch_word Ubsan.M.loaded_segments (0x6a234 : word) = Some W_6a1f4.
Proof. vm_refl. Qed.
Lemma D_6a1f4 : decode_any W_6a1f4 = Some (Load SZ8 true 21 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a1f8 : bv 32 := 0x01013b03.
Lemma F_6a1f8 : fetch_word Ubsan.M.loaded_segments (0x6a238 : word) = Some W_6a1f8.
Proof. vm_refl. Qed.
Lemma D_6a1f8 : decode_any W_6a1f8 = Some (Load SZ8 true 22 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a1fc : bv 32 := 0x00813b83.
Lemma F_6a1fc : fetch_word Ubsan.M.loaded_segments (0x6a23c : word) = Some W_6a1fc.
Proof. vm_refl. Qed.
Lemma D_6a1fc : decode_any W_6a1fc = Some (Load SZ8 true 23 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a200 : bv 32 := 0x00013c03.
Lemma F_6a200 : fetch_word Ubsan.M.loaded_segments (0x6a240 : word) = Some W_6a200.
Proof. vm_refl. Qed.
Lemma D_6a200 : decode_any W_6a200 = Some (Load SZ8 true 24 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a204 : bv 32 := 0x05010113.
Lemma F_6a204 : fetch_word Ubsan.M.loaded_segments (0x6a244 : word) = Some W_6a204.
Proof. vm_refl. Qed.
Lemma D_6a204 : decode_any W_6a204 = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a208 : bv 32 := 0x00008067.
Lemma F_6a208 : fetch_word Ubsan.M.loaded_segments (0x6a248 : word) = Some W_6a208.
Proof. vm_refl. Qed.
Lemma D_6a208 : decode_any W_6a208 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
End U1_code_6a07c_6a21c.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablStmts.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PeLia.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac WalkTac StartupTac SumWalkTac StoreOk MemSplit Hoare ShapeAlg
  SRealizes RefMemcpyLib RefReadLib LibIface LibEff MmapSim SumMemcpyBase SumMemcpy LibMaskBits U1Layout.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContLib ContStmts U1Facts U1Lib_Cxx_OperatorDelete.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.U1Lib_Vec32_PbSlow.U1_code_6a07c_6a21c.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablStmts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PeLia.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Local Ltac lia ::= pe_lia.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Abbreviation SEGS := Ubsan.M.loaded_segments.
Module Ly := U1Layout.

Ltac rdn_fix H :=
  first [ exact H
        | lazymatch goal with |- rdn _ _ (Z_to_bv 64 ?a) _ = _ =>
            lazymatch type of H with rdn _ _ (Z_to_bv 64 ?a') _ = _ =>
              replace a with a' by lia; exact H end end ].
Ltac rdA H := peel; rdn_fix H.
Ltac b2z8 := apply bytes_le_to_Z_8.
Ltac close_pc := lazymatch goal with |- msteps _ ?a ?bb => replace bb with a; [apply mst_refl|] end; f_equal; apply bv_eq; vm_compute; reflexivity.
Ltac wl := lazymatch goal with |- msteps _ (mkst (regupd _ _ ?v) _ _ _) _ => wlit v | |- _ => idtac end.
Ltac snl F D := stepn F D; pin; wl.
Ltac cmpz := pin; unfold c_ltu, c_eq, c_lts, bv_ltu, bv_lts, bv_eqb; imm_norm; rewrite ?u64_of_Z by lia; rewrite ?bv_signed_small64 by lia;
  first [apply Z.ltb_lt; lia | apply Z.ltb_ge; lia | apply Z.eqb_eq; lia | apply Z.eqb_neq; lia | reflexivity].
Ltac slotv SL k H :=
  pose proof (SL k ltac:(lia)) as H;
  lazymatch type of H with rdn _ _ _ _ = Some (word_to_le_bytes 8 ?v) =>
    let v' := eval simpl in v in change v with v' in H end.

Lemma step_sltu_at {fx : FPState} : forall segs regs pc mem rom w rd rs1 rs2 v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op ALU_SLTU rd rs1 rs2, 4%Z) -> bv_eqb rd 0 = false ->
  v_sltu (getr regs rs1) (getr regs rs2) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) = MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof. intros segs regs pc mem rom w rd rs1 rs2 v Hf He Hd Hrd Hv. rewrite (step_sltu segs regs pc mem rom w rd rs1 rs2 Hf He Hd). rewrite Hrd, Hv. reflexivity. Qed.
Lemma step_slt_at {fx : FPState} : forall segs regs pc mem rom w rd rs1 rs2 v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op ALU_SLT rd rs1 rs2, 4%Z) -> bv_eqb rd 0 = false ->
  v_slt (getr regs rs1) (getr regs rs2) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) = MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof. intros segs regs pc mem rom w rd rs1 rs2 v Hf He Hd Hrd Hv. rewrite (step_slt segs regs pc mem rom w rd rs1 rs2 Hf He Hd). rewrite Hrd, Hv. reflexivity. Qed.
Lemma step_xor_at {fx : FPState} : forall segs regs pc mem rom w rd rs1 rs2 v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op ALU_XOR rd rs1 rs2, 4%Z) -> bv_eqb rd 0 = false ->
  v_xor (getr regs rs1) (getr regs rs2) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) = MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof. intros segs regs pc mem rom w rd rs1 rs2 v Hf He Hd Hrd Hv. rewrite (step_xor segs regs pc mem rom w rd rs1 rs2 Hf He Hd). rewrite Hrd, Hv. reflexivity. Qed.
Ltac steprr L F D vv tac :=
  chain_step;
  [ reflexivity
  | eapply L with (v := vv); [ exact F | reflexivity | exact D | reflexivity | tac ]
  | step_simpl ].
Lemma snez_Z : forall b, 0 < b < 2 ^ 64 -> v_sltu (Z_to_bv 64 0) (Z_to_bv 64 b) = Z_to_bv 64 1.
Proof. intros b Hb. unfold v_sltu. rewrite c_ltu_Z by lia. destruct (Z.ltb_spec 0 b); [reflexivity|lia]. Qed.
Lemma sltiu_1_Z : forall a, 0 <= a < 2 ^ 64 -> v_sltiu (Z_to_bv 64 a) 1 = Z_to_bv 64 (if a =? 0 then 1 else 0).
Proof.
  intros a Ha. unfold v_sltiu. rewrite u64_of_Z by lia. change (bv_wrap 64 1) with 1.
  destruct (Z.eqb_spec a 0); [subst; reflexivity|]. destruct (Z.ltb_spec a 1); [lia|reflexivity].
Qed.
Lemma sltu_pp : forall p k, 0 <= p -> 0 <= k -> p + k < 2 ^ 64 -> v_sltu (Z_to_bv 64 p) (Z_to_bv 64 (p + k)) = Z_to_bv 64 (if k =? 0 then 0 else 1).
Proof.
  intros p k Hp Hk Hpk. unfold v_sltu. rewrite c_ltu_Z by lia.
  destruct (Z.eqb_spec k 0); destruct (Z.ltb_spec p (p + k)); first [reflexivity | lia].
Qed.
Lemma sgtz_Z : forall c, 0 <= c < 2 ^ 63 -> v_slt (Z_to_bv 64 0) (Z_to_bv 64 c) = Z_to_bv 64 (if c =? 0 then 0 else 1).
Proof.
  intros c Hc. unfold v_slt, c_lts, bv_lts. rewrite !bv_signed_small64 by lia. rewrite ?u64_of_Z by lia.
  destruct (Z.eqb_spec c 0); destruct (Z.ltb_spec 0 c); first [reflexivity | lia].
Qed.
Lemma xor_same : forall w : word, v_xor w w = Z_to_bv 64 0.
Proof. intros w. unfold v_xor. rewrite Z.lxor_nilpotent. reflexivity. Qed.

Section PbSlow.
Context {AC : AllocCeiling}.
  Variable MI : MallocIface SEGS Ly.L.
  Variable ST : StaticsIface SEGS Ly.L.
  Hypothesis MALLOC_STACK_pos : (0 <= MALLOC_STACK MI)%Z.
  Hypothesis NEW : new_rule_stmt SEGS Ly.L MI ST (NEW_STACK SEGS Ly.L MI).

  #[local] Notation placed_sep := (placed_sep SEGS Ly.L MI ly_img_low ly_rw_img).
  #[local] Notation stack_sep := (stack_sep SEGS Ly.L MI ly_img_low ly_rw_img).
  #[local] Notation offimg_sep := (offimg_sep SEGS Ly.L ST ly_rw_img ly_relro_img ly_errno_img).

  Definition u1c6a018 : vec_consts := {| vc_entry := 0x6a0bc; vc_stack := 80 |}.

  Definition PRO_vals (R : bvmap 5 word) (ret : Z) : list word :=
    [getr R 24%bv; getr R 23%bv; getr R 22%bv; getr R 21%bv; getr R 20%bv; getr R 19%bv; getr R 18%bv; getr R 9%bv; getr R 8%bv; Z_to_bv 64 ret].

  Lemma LA : forall (fx : FPState) R M (sp ret v b cap src : Z),
    getr R 1%bv = Z_to_bv 64 ret -> getr R 2%bv = Z_to_bv 64 sp -> getr R 10%bv = Z_to_bv 64 v -> getr R 11%bv = Z_to_bv 64 src ->
    0 <= cap < 2 ^ 40 -> 0 <= b -> b + 4 * cap <= 2 ^ 63 -> 2 ^ 20 <= sp - 80 -> sp < 2 ^ 47 -> 0 <= v -> v + 24 <= 2 ^ 63 ->
    (v + 24 <= sp - 80 \/ sp <= v) ->
    store_ok SEGS M (Z_to_bv 64 (sp - 80)) 80 = true ->
    rdn SEGS M (Z_to_bv 64 v) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 b)) ->
    rdn SEGS M (Z_to_bv 64 (v + 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (b + 4 * cap))) ->
    rdn SEGS M (Z_to_bv 64 (v + 16)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (b + 4 * cap))) ->
    exists Rn,
      msteps SEGS (@mkst fx R (Z_to_bv 64 0x6a0bc) M (seg_rom SEGS)) (@mkst fx Rn (Z_to_bv 64 (ly_new Ly.L)) (wslots M sp (PRO_vals R ret)) (seg_rom SEGS))
      /\ getr Rn 10%bv = Z_to_bv 64 (4 * vgrow cap) /\ getr Rn 1%bv = Z_to_bv 64 0x6a140 /\ getr Rn 2%bv = Z_to_bv 64 (sp - 80)
      /\ getr Rn 8%bv = Z_to_bv 64 b /\ getr Rn 9%bv = Z_to_bv 64 v /\ getr Rn 18%bv = Z_to_bv 64 (4 * cap) /\ getr Rn 19%bv = Z_to_bv 64 (4 * cap)
      /\ getr Rn 20%bv = Z_to_bv 64 src /\ getr Rn 21%bv = Z_to_bv 64 (4 * vgrow cap) /\ getr Rn 22%bv = Z_to_bv 64 cap /\ getr Rn 24%bv = Z_to_bv 64 (vgrow cap)
      /\ getr Rn 3%bv = getr R 3%bv /\ getr Rn 4%bv = getr R 4%bv
      /\ (forall r, In r [23; 25; 26; 27]%bv -> getr Rn r = getr R r).
  Proof using.
    intros fx R M sp ret v b cap src Hra Hsp Ha0 Ha1 Hcap Hb0 Hbc Hspr Hsphi Hv0 Hv1 WINv HOK F0 F1 F2.
    assert (PRO : forall Rx, Rx = regupd (regupd R 2%bv (Z_to_bv 64 (sp - 80))) 9%bv (Z_to_bv 64 v) ->
      msteps SEGS (@mkst fx R (Z_to_bv 64 0x6a0bc) M (seg_rom SEGS)) (@mkst fx Rx (Z_to_bv 64 0x6a0ec) (wslots M sp (PRO_vals R ret)) (seg_rom SEGS))).
    { intros Rx ->. norm_pc.
      sv F_6a07c D_6a07c (Z_to_bv 64 (sp - 80)).
      stw F_6a080 D_6a080 (Z_to_bv 64 (sp - 8)) (Z_to_bv 64 ret) ltac:(ok_sub HOK).
      stw F_6a084 D_6a084 (Z_to_bv 64 (sp - 16)) (getr R 8%bv) ltac:(ok_sub HOK).
      stw F_6a088 D_6a088 (Z_to_bv 64 (sp - 24)) (getr R 9%bv) ltac:(ok_sub HOK).
      stw F_6a08c D_6a08c (Z_to_bv 64 (sp - 32)) (getr R 18%bv) ltac:(ok_sub HOK).
      stw F_6a090 D_6a090 (Z_to_bv 64 (sp - 40)) (getr R 19%bv) ltac:(ok_sub HOK).
      stw F_6a094 D_6a094 (Z_to_bv 64 (sp - 48)) (getr R 20%bv) ltac:(ok_sub HOK).
      stw F_6a098 D_6a098 (Z_to_bv 64 (sp - 56)) (getr R 21%bv) ltac:(ok_sub HOK).
      stw F_6a09c D_6a09c (Z_to_bv 64 (sp - 64)) (getr R 22%bv) ltac:(ok_sub HOK).
      stw F_6a0a0 D_6a0a0 (Z_to_bv 64 (sp - 72)) (getr R 23%bv) ltac:(ok_sub HOK).
      stw F_6a0a4 D_6a0a4 (Z_to_bv 64 (sp - 80)) (getr R 24%bv) ltac:(ok_sub HOK).
      sv F_6a0a8 D_6a0a8 (Z_to_bv 64 v).
      lazymatch goal with |- msteps _ ?a ?bb => replace bb with a; [apply mst_refl|] end.
      f_equal. apply bv_eq; reflexivity. }
    assert (F0' : rdn SEGS (wslots M sp (PRO_vals R ret)) (Z_to_bv 64 v) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 b))).
    { rewrite wslots_out; [exact F0 | unfold Zlen; cbn; lia | lia | lia | cbn; lia | unfold Zlen; cbn; lia]. }
    assert (F1' : rdn SEGS (wslots M sp (PRO_vals R ret)) (Z_to_bv 64 (v + 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (b + 4 * cap)))).
    { rewrite wslots_out; [exact F1 | unfold Zlen; cbn; lia | lia | lia | cbn; lia | unfold Zlen; cbn; lia]. }
    assert (F2' : rdn SEGS (wslots M sp (PRO_vals R ret)) (Z_to_bv 64 (v + 16)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (b + 4 * cap)))).
    { rewrite wslots_out; [exact F2 | unfold Zlen; cbn; lia | lia | lia | cbn; lia | unfold Zlen; cbn; lia]. }
    destruct (Z.lt_ge_cases 1 cap) as [Hc1 | Hc1].
    -
      replace (vgrow cap) with (2 * cap) by (unfold vgrow; lia).
      eexists. split.
      + eapply msteps_trans; [apply PRO; reflexivity|]. norm_pc.
        ld_step F_6a0ac D_6a0ac (word_to_le_bytes 8 (Z_to_bv 64 b)) (Z_to_bv 64 b) ltac:(rdn_fix F0') ltac:(b2z8).
        ld_step F_6a0b0 D_6a0b0 (word_to_le_bytes 8 (Z_to_bv 64 (b + 4 * cap))) (Z_to_bv 64 (b + 4 * cap)) ltac:(rdn_fix F1') ltac:(b2z8).
        stepiv F_6a0b4 D_6a0b4 (Z_to_bv 64 (4 * cap)) ltac:(gres; rewrite v_sub_Z by lia; f_equal; lia).
        stepiv F_6a0b8 D_6a0b8 (Z_to_bv 64 cap) ltac:(gres; imm_norm; rewrite v_srai_Z by lia; f_equal; change (2^2) with 4; rewrite Z.mul_comm; apply Z.div_mul; lia).
        stepiv F_6a0bc D_6a0bc (Z_to_bv 64 (cap + 1)) ltac:(gres; imm_norm; rewrite v_addi_Z by lia; reflexivity).
        stepiv F_6a0c0 D_6a0c0 (Z_to_bv 64 0) ltac:(gres; imm_norm; rewrite v_srli_Z by lia; f_equal; rewrite Z.div_small by lia; reflexivity).
        stepb_ft F_6a0c4 D_6a0c4 ltac:(apply c_eq_refl).
        sv F_6a0c8 D_6a0c8 (Z_to_bv 64 src).
        ld_step F_6a0cc D_6a0cc (word_to_le_bytes 8 (Z_to_bv 64 (b + 4 * cap))) (Z_to_bv 64 (b + 4 * cap)) ltac:(rdn_fix F2') ltac:(b2z8).
        stepiv F_6a0d0 D_6a0d0 (Z_to_bv 64 (4 * cap)) ltac:(gres; rewrite v_sub_Z by lia; f_equal; lia).
        stepiv F_6a0d4 D_6a0d4 (Z_to_bv 64 (2 * cap)) ltac:(gres; imm_norm; rewrite v_srli_Z by lia; f_equal; change (2^1) with 2; replace (4 * cap) with (2 * cap * 2) by lia; apply Z.div_mul; lia).
        stepb_ft F_6a0d8 D_6a0d8 ltac:(cmpz).
        stepiv F_6a0dc D_6a0dc (Z_to_bv 64 (2 ^ 64 - 7)) ltac:(gres; imm_norm; apply bv_eq; vm_compute; reflexivity).
        stepiv F_6a0e0 D_6a0e0 (Z_to_bv 64 0x7ffffffffffffffc) ltac:(gres; imm_norm; apply bv_eq; vm_compute; reflexivity).
        stepb_ft F_6a0e4 D_6a0e4 ltac:(cmpz).
        stepiv F_6a0e8 D_6a0e8 (Z_to_bv 64 (4 * (2 * cap))) ltac:(gres; imm_norm; rewrite v_slli_Z by lia; f_equal; change (2^2) with 4; lia).
        stepb_ft F_6a0ec D_6a0ec ltac:(cmpz).
        stepiv F_6a0f0 D_6a0f0 (Z_to_bv 64 0) ltac:(gres; imm_norm; rewrite v_srli_Z by lia; f_equal; rewrite Z.div_small by lia; reflexivity).
        stepb_ft F_6a0f4 D_6a0f4 ltac:(apply c_eq_refl).
        sv F_6a0f8 D_6a0f8 (Z_to_bv 64 (4 * (2 * cap))).
        stepj F_6a0fc D_6a0fc.
        close_pc.
      + gres. repeat split; try reflexivity; try (f_equal; lia).
        intros r Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
    -
      replace (vgrow cap) with (cap + 1) by (unfold vgrow; lia).
      eexists. split.
      + eapply msteps_trans; [apply PRO; reflexivity|]. norm_pc.
        ld_step F_6a0ac D_6a0ac (word_to_le_bytes 8 (Z_to_bv 64 b)) (Z_to_bv 64 b) ltac:(rdn_fix F0') ltac:(b2z8).
        ld_step F_6a0b0 D_6a0b0 (word_to_le_bytes 8 (Z_to_bv 64 (b + 4 * cap))) (Z_to_bv 64 (b + 4 * cap)) ltac:(rdn_fix F1') ltac:(b2z8).
        stepiv F_6a0b4 D_6a0b4 (Z_to_bv 64 (4 * cap)) ltac:(gres; rewrite v_sub_Z by lia; f_equal; lia).
        stepiv F_6a0b8 D_6a0b8 (Z_to_bv 64 cap) ltac:(gres; imm_norm; rewrite v_srai_Z by lia; f_equal; change (2^2) with 4; rewrite Z.mul_comm; apply Z.div_mul; lia).
        stepiv F_6a0bc D_6a0bc (Z_to_bv 64 (cap + 1)) ltac:(gres; imm_norm; rewrite v_addi_Z by lia; reflexivity).
        stepiv F_6a0c0 D_6a0c0 (Z_to_bv 64 0) ltac:(gres; imm_norm; rewrite v_srli_Z by lia; f_equal; rewrite Z.div_small by lia; reflexivity).
        stepb_ft F_6a0c4 D_6a0c4 ltac:(apply c_eq_refl).
        sv F_6a0c8 D_6a0c8 (Z_to_bv 64 src).
        ld_step F_6a0cc D_6a0cc (word_to_le_bytes 8 (Z_to_bv 64 (b + 4 * cap))) (Z_to_bv 64 (b + 4 * cap)) ltac:(rdn_fix F2') ltac:(b2z8).
        stepiv F_6a0d0 D_6a0d0 (Z_to_bv 64 (4 * cap)) ltac:(gres; rewrite v_sub_Z by lia; f_equal; lia).
        stepiv F_6a0d4 D_6a0d4 (Z_to_bv 64 (2 * cap)) ltac:(gres; imm_norm; rewrite v_srli_Z by lia; f_equal; change (2^1) with 2; replace (4 * cap) with (2 * cap * 2) by lia; apply Z.div_mul; lia).
        stepb_tk F_6a0d8 D_6a0d8 ltac:(cmpz).
        sv F_6a10c D_6a10c (Z_to_bv 64 (cap + 1)).
        stepiv F_6a110 D_6a110 (Z_to_bv 64 (2 ^ 64 - 7)) ltac:(gres; imm_norm; apply bv_eq; vm_compute; reflexivity).
        stepiv F_6a114 D_6a114 (Z_to_bv 64 0x7ffffffffffffffc) ltac:(gres; imm_norm; apply bv_eq; vm_compute; reflexivity).
        stepb_tk F_6a118 D_6a118 ltac:(cmpz).
        stepiv F_6a0e8 D_6a0e8 (Z_to_bv 64 (4 * (cap + 1))) ltac:(gres; imm_norm; rewrite v_slli_Z by lia; f_equal; change (2^2) with 4; lia).
        stepb_ft F_6a0ec D_6a0ec ltac:(cmpz).
        stepiv F_6a0f0 D_6a0f0 (Z_to_bv 64 0) ltac:(gres; imm_norm; rewrite v_srli_Z by lia; f_equal; rewrite Z.div_small by lia; reflexivity).
        stepb_ft F_6a0f4 D_6a0f4 ltac:(apply c_eq_refl).
        sv F_6a0f8 D_6a0f8 (Z_to_bv 64 (4 * (cap + 1))).
        stepj F_6a0fc D_6a0fc.
        close_pc.
      + gres. repeat split; try reflexivity; try (f_equal; lia).
        intros r Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
  Qed.

  Lemma LB : forall (fx : FPState) R2 Mb (sp v b cap src x p : Z),
    getr R2 10%bv = Z_to_bv 64 p -> getr R2 2%bv = Z_to_bv 64 (sp - 80) ->
    getr R2 8%bv = Z_to_bv 64 b -> getr R2 9%bv = Z_to_bv 64 v -> getr R2 18%bv = Z_to_bv 64 (4 * cap) -> getr R2 19%bv = Z_to_bv 64 (4 * cap) ->
    getr R2 20%bv = Z_to_bv 64 src -> getr R2 21%bv = Z_to_bv 64 (4 * vgrow cap) -> getr R2 22%bv = Z_to_bv 64 cap -> getr R2 24%bv = Z_to_bv 64 (vgrow cap) ->
    0 <= cap < 2 ^ 40 -> 0 <= b -> b + 4 * cap <= 2 ^ 63 -> b mod 4 = 0 -> 16 <= p -> p mod 16 = 0 -> p + 4 * vgrow cap <= 2 ^ 47 -> 0 <= x < 2 ^ 32 -> 0 <= src -> src + 4 <= 2 ^ 63 ->
    (src + 4 <= p \/ p + 4 * vgrow cap <= src) ->
    mdef Mb p (4 * vgrow cap) ->
    rdn SEGS Mb (Z_to_bv 64 src) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 x)) ->
    exists R3,
      msteps SEGS (@mkst fx R2 (Z_to_bv 64 0x6a140) Mb (seg_rom SEGS))
                  (@mkst fx R3 (Z_to_bv 64 0xe2b9c) (wbytes Mb (Z_to_bv 64 (p + 4 * cap)) (word_to_le_bytes 4 (v_lw (Z_to_bv 64 x)))) (seg_rom SEGS))
      /\ getr R3 10%bv = Z_to_bv 64 p /\ getr R3 11%bv = Z_to_bv 64 b /\ getr R3 12%bv = Z_to_bv 64 (4 * cap) /\ getr R3 1%bv = Z_to_bv 64 0x6a1fc
      /\ getr R3 2%bv = Z_to_bv 64 (sp - 80) /\ getr R3 8%bv = Z_to_bv 64 b /\ getr R3 9%bv = Z_to_bv 64 v /\ getr R3 18%bv = Z_to_bv 64 (4 * cap)
      /\ getr R3 20%bv = Z_to_bv 64 p /\ getr R3 21%bv = Z_to_bv 64 (p + 4 * cap + 4) /\ getr R3 23%bv = Z_to_bv 64 (p + 4 * vgrow cap)
      /\ getr R3 3%bv = getr R2 3%bv /\ getr R3 4%bv = getr R2 4%bv
      /\ (forall r, In r [19; 22; 24; 25; 26; 27]%bv -> getr R3 r = getr R2 r).
  Proof using.
    intros fx R2 Mb sp v b cap src x p G10 G2 G8 G9 G18 G19 G20 G21 G22 G24 Hcap Hb0 Hbc Hb4 Hp16 Hpal Hpv Hx Hs0 Hs1 Hsp HDp SRC.
    assert (Hvg : cap + 1 <= vgrow cap /\ vgrow cap <= 2 * cap + 1) by (unfold vgrow; lia).
    assert (Hp4 : (p + 4 * cap) mod 4 = 0).
    { pose proof (Z_div_mod_eq_full p 16) as E. rewrite Hpal in E. replace (p + 4 * cap) with ((4 * (p / 16) + cap) * 4) by lia. apply Z_mod_mult. }
    eexists. split.
    - norm_pc.
      stepiv F_6a100 D_6a100 (Z_to_bv 64 (p + 4 * cap)) ltac:(gres; pin; rewrite v_add_Z by lia; reflexivity).
      stepb_tk F_6a104 D_6a104 ltac:(cmpz).
      steprr (@step_sltu_at fx) F_6a138 D_6a138 (Z_to_bv 64 1) ltac:(gres; pin; rewrite ?getr_zero; apply snez_Z; lia).
      stepiv F_6a13c D_6a13c (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite sltiu_1_Z by lia; destruct (Z.eqb_spec (p + 4 * cap) 0); [lia|reflexivity]).
      steprr (@step_xor_at fx) F_6a140 D_6a140 (Z_to_bv 64 1) ltac:(gres; pin; apply bv_eq; vm_compute; reflexivity).
      stepb_ft F_6a144 D_6a144 ltac:(cmpz).
      stepiv F_6a148 D_6a148 (Z_to_bv 64 (p + 4 * vgrow cap)) ltac:(gres; pin; rewrite v_add_Z by lia; f_equal; lia).
      stepiv F_6a14c D_6a14c (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite sltiu_1_Z by lia; destruct (Z.eqb_spec (p + 4 * vgrow cap) 0); [lia|reflexivity]).
      stepb_ft F_6a150 D_6a150 ltac:(cmpz).
      stepiv F_6a154 D_6a154 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite v_srli_Z by lia; f_equal; rewrite Z.div_small by lia; reflexivity).
      stepb_ft F_6a158 D_6a158 ltac:(apply c_eq_refl).
      stepb_ft F_6a15c D_6a15c ltac:(cmpz).
      stepiv F_6a160 D_6a160 (Z_to_bv 64 0)
        ltac:(gres; pin; imm_norm; rewrite v_andi_Z by lia; f_equal; change 3 with (2 ^ 2 - 1); rewrite land_ones_mod by lia; change (2 ^ 2) with 4; exact Hp4).
      stepb_ft F_6a164 D_6a164 ltac:(apply c_eq_refl).
      stepb_ft F_6a168 D_6a168 ltac:(cmpz).
      ld_step F_6a16c D_6a16c (word_to_le_bytes 4 (Z_to_bv 64 x)) (Z_to_bv 64 x) ltac:(rdn_fix SRC) ltac:(apply lwu_val; lia).
      stw F_6a170 D_6a170 (Z_to_bv 64 (p + 4 * cap)) (v_lw (Z_to_bv 64 x)) ltac:(apply (mdef_store_ok_off SEGS Mb p (4 * vgrow cap) (4 * cap) 4 HDp); lia).
      stepb_ft F_6a174 D_6a174 ltac:(cmpz).
      stepiv F_6a178 D_6a178 (Z_to_bv 64 (2 ^ 64 - 4)) ltac:(gres; pin; imm_norm; apply bv_eq; vm_compute; reflexivity).
      stepb_ft F_6a17c D_6a17c ltac:(cmpz).
      stepiv F_6a180 D_6a180 (Z_to_bv 64 (4 * cap)) ltac:(gres; pin; imm_norm; rewrite v_slli_Z by lia; f_equal; change (2 ^ 2) with 4; lia).
      stepiv F_6a184 D_6a184 (Z_to_bv 64 p) ltac:(gres; pin; rewrite v_sub_Z by lia; f_equal; lia).
      stepb_ft F_6a188 D_6a188 ltac:(cmpz).
      steprr (@step_sltu_at fx) F_6a18c D_6a18c (Z_to_bv 64 (if 4 * cap =? 0 then 0 else 1)) ltac:(gres; pin; apply sltu_pp; lia).
      steprr (@step_slt_at fx) F_6a190 D_6a190 (Z_to_bv 64 (if 4 * cap =? 0 then 0 else 1))
        ltac:(gres; pin; rewrite ?getr_zero; rewrite sgtz_Z by lia; f_equal; destruct (Z.eqb_spec cap 0); destruct (Z.eqb_spec (4 * cap) 0); lia).
      steprr (@step_xor_at fx) F_6a194 D_6a194 (Z_to_bv 64 0) ltac:(gres; pin; apply xor_same).
      stepiv F_6a198 D_6a198 (Z_to_bv 64 1) ltac:(gres; pin; imm_norm; reflexivity).
      stepb_ft F_6a19c D_6a19c ltac:(cmpz).
      stepiv F_6a1a0 D_6a1a0 (Z_to_bv 64 0)
        ltac:(gres; pin; imm_norm; rewrite v_andi_Z by lia; f_equal; change 3 with (2 ^ 2 - 1); rewrite land_ones_mod by lia; change (2 ^ 2) with 4; exact Hb4).
      stepb_ft F_6a1a4 D_6a1a4 ltac:(apply c_eq_refl).
      stepiv F_6a1a8 D_6a1a8 (Z_to_bv 64 (p + 4 * cap + 4)) ltac:(gres; pin; imm_norm; rewrite v_addi_Z by lia; reflexivity).
      sv F_6a1ac D_6a1ac (Z_to_bv 64 p).
      sv F_6a1b0 D_6a1b0 (Z_to_bv 64 b).
      sv F_6a1b4 D_6a1b4 (Z_to_bv 64 (4 * cap)).
      stepj F_6a1b8 D_6a1b8.
      close_pc.
    - gres. repeat split; first [reflexivity | assumption | f_equal; lia | intros r Hr; repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]); destruct Hr].
  Qed.

  Lemma epilogue : forall (fx : FPState) R M sp ret (a0v v8 v9 v18 v19 v20 v21 v22 v23 v24 : word),
    getr R 2%bv = Z_to_bv 64 (sp - 80) -> getr R 21%bv = a0v -> 80 <= sp < 2 ^ 63 ->
    rdn SEGS M (Z_to_bv 64 (sp - 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 ret)) ->
    rdn SEGS M (Z_to_bv 64 (sp - 16)) 8 = Some (word_to_le_bytes 8 v8) ->
    rdn SEGS M (Z_to_bv 64 (sp - 24)) 8 = Some (word_to_le_bytes 8 v9) ->
    rdn SEGS M (Z_to_bv 64 (sp - 32)) 8 = Some (word_to_le_bytes 8 v18) ->
    rdn SEGS M (Z_to_bv 64 (sp - 40)) 8 = Some (word_to_le_bytes 8 v19) ->
    rdn SEGS M (Z_to_bv 64 (sp - 48)) 8 = Some (word_to_le_bytes 8 v20) ->
    rdn SEGS M (Z_to_bv 64 (sp - 56)) 8 = Some (word_to_le_bytes 8 v21) ->
    rdn SEGS M (Z_to_bv 64 (sp - 64)) 8 = Some (word_to_le_bytes 8 v22) ->
    rdn SEGS M (Z_to_bv 64 (sp - 72)) 8 = Some (word_to_le_bytes 8 v23) ->
    rdn SEGS M (Z_to_bv 64 (sp - 80)) 8 = Some (word_to_le_bytes 8 v24) ->
    ret_ok (Z_to_bv 64 ret) ->
    msteps SEGS (@mkst fx R (Z_to_bv 64 0x6a218) M (seg_rom SEGS))
                (@mkst fx (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd R
                             10%bv a0v) 1%bv (Z_to_bv 64 ret)) 8%bv v8) 9%bv v9) 18%bv v18) 19%bv v19) 20%bv v20) 21%bv v21) 22%bv v22) 23%bv v23) 24%bv v24)
                             2%bv (Z_to_bv 64 sp))
                          (Z_to_bv 64 ret) M (seg_rom SEGS)).
  Proof using.
    intros fx R M sp ret a0v v8 v9 v18 v19 v20 v21 v22 v23 v24 Hsp Hs5 Hsp' L1 L8 L9 L18 L19 L20 L21 L22 L23 L24 Hret.
    norm_pc.
    sv F_6a1d8 D_6a1d8 a0v.
    ld_step F_6a1dc D_6a1dc (word_to_le_bytes 8 (Z_to_bv 64 ret)) (Z_to_bv 64 ret) ltac:(rdA L1) ltac:(b2z8).
    ld_step F_6a1e0 D_6a1e0 (word_to_le_bytes 8 v8) v8 ltac:(rdA L8) ltac:(b2z8).
    ld_step F_6a1e4 D_6a1e4 (word_to_le_bytes 8 v9) v9 ltac:(rdA L9) ltac:(b2z8).
    ld_step F_6a1e8 D_6a1e8 (word_to_le_bytes 8 v18) v18 ltac:(rdA L18) ltac:(b2z8).
    ld_step F_6a1ec D_6a1ec (word_to_le_bytes 8 v19) v19 ltac:(rdA L19) ltac:(b2z8).
    ld_step F_6a1f0 D_6a1f0 (word_to_le_bytes 8 v20) v20 ltac:(rdA L20) ltac:(b2z8).
    ld_step F_6a1f4 D_6a1f4 (word_to_le_bytes 8 v21) v21 ltac:(rdA L21) ltac:(b2z8).
    ld_step F_6a1f8 D_6a1f8 (word_to_le_bytes 8 v22) v22 ltac:(rdA L22) ltac:(b2z8).
    ld_step F_6a1fc D_6a1fc (word_to_le_bytes 8 v23) v23 ltac:(rdA L23) ltac:(b2z8).
    ld_step F_6a200 D_6a200 (word_to_le_bytes 8 v24) v24 ltac:(rdA L24) ltac:(b2z8).
    sv F_6a204 D_6a204 (Z_to_bv 64 sp).
    stepjr F_6a208 D_6a208 (Z_to_bv 64 ret) ltac:(gres; reflexivity).
    lazymatch goal with |- msteps _ ?a ?b => replace b with a; [apply mst_refl|] end.
    f_equal. exact Hret.
  Qed.

  Theorem vec32_pbslow_6a018_spec : vec32_pbslow_stmt SEGS Ly.L MI ST (2 ^ 32) u1c6a018.
  Proof using AC MI ST MALLOC_STACK_pos NEW.
    intros fx A s R M model sp ret v b cap src x xs K.
    cbn [vc_entry vc_stack u1c6a018]. lazy zeta.
    intros CB Ha0 Ha1 VEC LEN OBJ Hv8 SRC Hx SOBJ Hs0 Hs1 Hs4 SRCV HNMAX ROOM CONT.
    destruct CB as [AI MS ROC SXI SXH CR Hceil HROOM Hwin Hown_sx Herr_sx].
    destruct CR as [Hra Hret Hretr Hsp Hsp16 Hsphi Hgp Htp].
    cbn [ly_gp ly_tp ly_errno_off ly_img ly_relro ly_rw Ly.L] in *.
    unfold NEW_STACK in *.
    pose proof ac_bounds_lit as Hceilv.
    destruct VEC as (Hv0 & Hv1 & HDv & Hlen & Hb & F0 & F1 & F2 & FE).
    pose proof HROOM as HOK. unfold stack_room in HOK.
    assert (Hspr : 2 ^ 20 <= sp - (80 + (16 + MALLOC_STACK MI))) by (lia).
    pose proof (ai_nmax_bound MI) as HNM. pose proof (ai_big_pos MI) as HBIG.
    assert (Hcap : 0 <= cap < 2 ^ 40) by (unfold vgrow in HNMAX; lia).
    destruct OBJ as [PLv WINv]. destruct SOBJ as [PLs WINs].
    assert (WINv' : v + 24 <= sp - (80 + (16 + MALLOC_STACK MI)) \/ sp <= v).
    { destruct (Z.lt_ge_cases v sp); [left|right; lia].
      destruct (Z.lt_ge_cases (v + 24) (sp - (80 + (16 + MALLOC_STACK MI)) + 1)); [lia|].
      exfalso. destruct (Z.lt_ge_cases v (sp - (80 + (16 + MALLOC_STACK MI)))).
      - apply (WINv (sp - (80 + (16 + MALLOC_STACK MI)))); unfold zwin; lia.
      - apply (WINv v); unfold zwin; lia. }
    assert (WINs' : src + 4 <= sp - (80 + (16 + MALLOC_STACK MI)) \/ sp <= src).
    { destruct (Z.lt_ge_cases src sp); [left|right; lia].
      destruct (Z.lt_ge_cases (src + 4) (sp - (80 + (16 + MALLOC_STACK MI)) + 1)); [lia|].
      exfalso. destruct (Z.lt_ge_cases src (sp - (80 + (16 + MALLOC_STACK MI)))).
      - apply (WINs (sp - (80 + (16 + MALLOC_STACK MI)))); unfold zwin; lia.
      - apply (WINs src); unfold zwin; lia. }
    hide WINv'. hide WINs'.

    assert (BUF : b <> 0 -> mdef M b (4 * cap) /\ b + 4 * cap <= alloc_ceiling /\
                  (forall a, b <= a < b + 4 * cap -> ~ owned MI A a /\ ~ in_ranges [(0x10000, 0x124000)] a)).
    { intros Hbnz. destruct Hb as [[Hb0 _]|(Hbp & Hal & Hcp & Hbc & HIn & Hdj)]; [lia|].
      split; [eapply (live_mdef SEGS Ly.L MI); eassumption|].
      split; [eapply (live_range SEGS Ly.L MI); eassumption|].
      intros a Ha. split; [eapply (live_unowned SEGS Ly.L MI); eassumption|].
      eapply (live_offimg SEGS Ly.L MI); eassumption. }
    hide Hb.
    assert (Hb0 : 0 <= b) by (unhide Hb; destruct Hb as [[-> _]|(Hbp & _)]; lia).
    assert (Hbc4 : b + 4 * cap <= 2 ^ 63) by (unhide Hb; destruct Hb as [[-> ->]|(Hbp & Hal & Hcp & Hbc & _)]; lia).
    assert (Hbal4 : b mod 4 = 0).
    { unhide Hb. destruct Hb as [[-> _]|(Hbp & Hal & _)]; [reflexivity|].
      pose proof (Z_div_mod_eq_full b 16) as E. rewrite Hal in E. replace b with ((4 * (b / 16)) * 4) by lia. apply Z_mod_mult. }
    assert (HDR : forall a, v <= a < v + 24 -> ~ owned MI A a /\ ~ in_ranges [(0x10000, 0x124000)] a).
    { intros a Ha. exact (placed_sep A M model v 24 a AI PLv Ha). }
    assert (WIN : forall a, sp - (80 + (16 + MALLOC_STACK MI)) <= a < sp -> ~ owned MI A a /\ ~ in_ranges [(0x10000, 0x124000)] a).
    { intros a Ha. apply (stack_sep A M model a AI). lia. }
    assert (HDW : mdef M (sp - (80 + (16 + MALLOC_STACK MI))) (80 + (16 + MALLOC_STACK MI))).
    { eapply store_ok_mdef_offimg; [exact HOK | lia | lia | lia |]. intros w Hw. apply ly_noseg. lia. }

    set (M1 := wslots M sp (PRO_vals R ret)).
    assert (ST1 : stores_in (zwin (sp - 80) sp) M M1).
    { unfold M1. apply (wslots_stores_in M sp (PRO_vals R ret)); unfold Zlen; cbn; lia. }
    assert (AG1 : forall lo hi, (hi <= sp - 80 \/ sp <= lo) -> 0 <= lo -> hi < 2 ^ 64 -> agree_on (zwin lo hi) M M1).
    { intros lo hi Hd Hlo Hhi. eapply stores_in_agree; [exact ST1|]. intros a Ha. unfold zwin in *. lia. }
    assert (SRC' : fld SEGS M1 src 4 x).
    { eapply fld_agree; [lia| cbn; lia | exact SRC |]. apply AG1; cbn; unhide WINs'; lia. }
    assert (SL : forall k, 1 <= k <= 10 ->
              rdn SEGS M1 (Z_to_bv 64 (sp - 8 * k)) 8
              = Some (word_to_le_bytes 8 (nth (Z.to_nat (10 - k)) (PRO_vals R ret) (Z_to_bv 64 0)))).
    { intros k Hk. unfold M1. apply wslots_read; unfold Zlen; cbn; lia. }
    slotv SL 1 SL1. slotv SL 2 SL2. slotv SL 3 SL3. slotv SL 4 SL4. slotv SL 5 SL5.
    slotv SL 6 SL6. slotv SL 7 SL7. slotv SL 8 SL8. slotv SL 9 SL9. slotv SL 10 SL10. clear SL.
    unfold fld in SRC'.

    destruct (LA fx R M sp ret v b cap src Hra Hsp Ha0 Ha1 Hcap Hb0 Hbc4 ltac:(lia) ltac:(lia) Hv0 Hv1 ltac:(unhide WINv'; lia)
                 ltac:(ok_sub HOK) F0 ltac:(rewrite <- LEN; exact F1) F2)
      as (Rn & RUNA & Rn10 & Rn1 & Rn2 & Rn8 & Rn9 & Rn18 & Rn19 & Rn20 & Rn21 & Rn22 & Rn24 & Rn3 & Rn4 & RnS).
    fold M1 in RUNA.
    eapply srz_msteps; [exact (ms_halt _ MS) | exact (ms_lazy _ MS) | exact RUNA | ].
    assert (Hng : 4 <= 4 * vgrow cap) by (unfold vgrow; lia).
    eapply (NEW fx A s Rn M1 model (4 * vgrow cap) (sp - 80) 0x6a140 K).
    + eapply (stores_in_ainv SEGS Ly.L MI); [exact AI | exact ST1 |]. intros a Ha. apply WIN. unfold zwin in Ha. lia.
    + exact MS.
    + eapply (roc_stores Ly.L); [exact ROC | exact ST1 |]. intros a Ha. cbn [ly_img Ly.L]. apply (proj2 (WIN a ltac:(unfold zwin in Ha; lia))).
    + eapply (stores_in_sx SEGS Ly.L ST); [exact SXI | exact ST1 |].
      intros a Ha. destruct (offimg_sep a (proj2 (WIN a ltac:(unfold zwin in Ha; lia)))) as (X1 & X2 & _). split; assumption.
    + exact SXH.
    + constructor.
      * exact Rn1.
      * unfold ret_ok. apply bv_eq. vm_compute. reflexivity.
      * lia.
      * exact Rn2.
      * replace (sp - 80) with (sp - 16 * 5) by lia. apply mod16_sub. exact Hsp16.
      * lia.
      * rewrite Rn3. exact Hgp.
      * rewrite Rn4. exact Htp.
    + exact Rn10.
    + lia.
    + lia.
    + unfold stack_room. eapply stores_in_store_ok; [exact ST1|]. ok_sub HOK.
    + intros a Ha. apply Hwin. unfold zwin in *. lia.
    + exact Hown_sx.
    + exact Herr_sx.
    + rewrite new_size_id by lia. eapply (roomL_room_for SEGS Ly.L MI); [exact AI | lia | exact ROOM].
    +
      intros A1 R2 M2 model1 p AI1 MS1 Hfs1 Hfds1 SX1 KEPT2 R2a0 Hp LADD CAPS1 BIGC1 NEWT1 FR1 DEF1.
      rewrite new_size_id in LADD, FR1 by lia.
      assert (ROC1 : img_ro_clear Ly.L M1).
      { eapply (roc_stores Ly.L); [exact ROC | exact ST1 |]. intros a Ha. cbn [ly_img Ly.L]. apply (proj2 (WIN a ltac:(unfold zwin in Ha; lia))). }
      assert (ROC2 : img_ro_clear Ly.L M2).
      { eapply (roc_frame Ly.L); [exact ROC1 | exact FR1 |]. intros a [Ho|[Hblk|[Hw|He]]].
        - exact (roc_owned SEGS Ly.L MI A1 M2 model1 a AI1 Ho).
        - right. eapply (live_offimg SEGS Ly.L MI); [exact AI1 | apply (live_add_new _ _ _ _ LADD) | exact Hblk].
        - right. apply (proj2 (stack_sep A1 M2 model1 a AI1 ltac:(unfold zwin in Hw; lia))).
        - left. apply ly_errno_rw. exact He. }
      set (n4 := 4 * vgrow cap) in *.
      assert (Hn4 : n4 = Z.max (2 * cap) (cap + 1) * 4) by (unfold n4, vgrow; lia).
      assert (HinP : In (p, n4) (live MI A1)) by (apply (live_add_new _ _ _ _ LADD)).
      destruct (live_range SEGS Ly.L MI A1 M2 model1 p n4 AI1 HinP) as (_ & Hpal & _ & Hpce).
      assert (HDp : mdef M2 p n4) by (eapply (live_mdef SEGS Ly.L MI); eassumption).
      assert (Hpown : forall a, p <= a < p + n4 -> ~ owned MI A1 a /\ ~ in_ranges [(0x10000, 0x124000)] a).
      { intros a Ha. split; [eapply (live_unowned SEGS Ly.L MI); eassumption | eapply (live_offimg SEGS Ly.L MI); eassumption]. }
      assert (LIVE1 : forall blk, In blk (live MI A) -> In blk (live MI A1)) by (intros blk Hblk; eapply live_add_keeps; eassumption).
      assert (PLv1 : placed MI A1 v 24) by (eapply (placed_mono SEGS Ly.L MI); eassumption).
      assert (PLs1 : placed MI A1 src 4) by (eapply (placed_mono SEGS Ly.L MI); eassumption).
      assert (HDRp : v + 24 <= p \/ p + n4 <= v).
      { destruct (placed_new_block_disjoint SEGS Ly.L MI A A1 M M2 model model1 v 24 p n4 AI AI1 PLv LADD ltac:(lia)) as [H|[H|H]]; [left|right|]; lia. }
      hide HDRp.
      assert (SRCp : src + 4 <= p \/ p + n4 <= src).
      { destruct (placed_new_block_disjoint SEGS Ly.L MI A A1 M M2 model model1 src 4 p n4 AI AI1 PLs LADD ltac:(lia)) as [H|[H|H]]; [left|right|]; lia. }
      hide SRCp.
      assert (BUFp : b <> 0 -> b + 4 * cap <= p \/ p + n4 <= b).
      { intros Hbnz. unhide Hb. destruct Hb as [[Hb00 _]|(Hbp & Hal & Hcp & Hbc & HIn & Hdj)]; [lia|].
        assert (Hne : p <> b).
        { intros ->. destruct LADD as [_ Hnin]. apply Hnin. apply in_map_iff. exists (b, 4 * cap). split; [reflexivity|exact HIn]. }
        destruct (ai_live_disjoint MI A1 M2 model1 p n4 b (4 * cap) AI1 HinP (LIVE1 _ HIn) Hne); [right|left]; lia. }
      assert (WIN1 : forall a, sp - (80 + (16 + MALLOC_STACK MI)) <= a < sp -> ~ owned MI A1 a /\ ~ in_ranges [(0x10000, 0x124000)] a).
      { intros a Ha. apply (stack_sep A1 M2 model1 a AI1). lia. }
      assert (HDR1 : forall a, v <= a < v + 24 -> ~ owned MI A1 a /\ ~ in_ranges [(0x10000, 0x124000)] a).
      { intros a Ha. exact (placed_sep A1 M2 model1 v 24 a AI1 PLv1 Ha). }
      assert (SRC1 : forall a, src <= a < src + 4 -> ~ owned MI A1 a /\ ~ in_ranges [(0x10000, 0x124000)] a).
      { intros a Ha. exact (placed_sep A1 M2 model1 src 4 a AI1 PLs1 Ha). }

      assert (PRES2 : forall a, (sp - 80 <= a < sp) \/ (v <= a < v + 24) \/ (src <= a < src + 4)
                                \/ (b <> 0 /\ b <= a < b + 4 * cap) -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
      { intros a Ha.
        assert (Hr : 0 <= a < 2 ^ 64) by (destruct Ha as [H|[H|[H|[Hnz H]]]]; lia).
        apply FR1. rewrite u64_of_Z by lia. intros [Ho|[Hblk|[Hw|He]]].
        - destruct Ha as [H|[H|[H|[Hnz H]]]].
          + exact (proj1 (WIN1 a ltac:(lia)) Ho).
          + exact (proj1 (HDR1 a H) Ho).
          + exact (proj1 (SRC1 a H) Ho).
          + unhide Hb. destruct Hb as [[Hb00 _]|(Hbp & Hal & Hcp & Hbc & HIn & Hdj)]; [lia|].
            exact (live_unowned SEGS Ly.L MI A1 M2 model1 b (4 * cap) a AI1 (LIVE1 _ HIn) H Ho).
        - destruct Ha as [H|[H|[H|[Hnz H]]]].
          + lia. + unhide HDRp; lia. + unhide SRCp; lia. + destruct (BUFp Hnz); lia.
        - unfold zwin in Hw. destruct Ha as [H|[H|[H|[Hnz H]]]].
          + lia. + unhide WINv'; lia. + unhide WINs'; lia.
          + unhide Hb. destruct Hb as [[Hb00 _]|(Hbp & Hal & Hcp & Hbc & HIn & Hdj)]; [lia|].
            destruct (live_range SEGS Ly.L MI A M model b (4 * cap) AI HIn) as (_ & _ & _ & Hbce). lia.
        - pose proof (ly_errno_img a He) as Hi. rewrite ly_img_iff in Hi.
          destruct Ha as [H|[H|[H|[Hnz H]]]].
          + pose proof (proj2 (WIN1 a ltac:(lia))) as X. rewrite in_ranges_1 in X. lia.
          + pose proof (proj2 (HDR1 a H)) as X. rewrite in_ranges_1 in X. lia.
          + pose proof (proj2 (SRC1 a H)) as X. rewrite in_ranges_1 in X. lia.
          + unhide Hb. destruct Hb as [[Hb00 _]|(Hbp & Hal & Hcp & Hbc & HIn & Hdj)]; [lia|].
            pose proof (live_offimg SEGS Ly.L MI A1 M2 model1 b (4 * cap) a AI1 (LIVE1 _ HIn) H) as X. rewrite ly_img_iff in X. lia. }
      assert (AG2 : forall lo hi, 0 <= lo -> hi < 2 ^ 64 ->
               ((sp - 80 <= lo /\ hi <= sp) \/ (v <= lo /\ hi <= v + 24) \/ (src <= lo /\ hi <= src + 4)
                \/ (b <> 0 /\ b <= lo /\ hi <= b + 4 * cap)) -> agree_on (zwin lo hi) M1 M2).
      { intros lo hi Hlo Hhi Hc a Ha. apply PRES2. unfold zwin in Ha. clear -Hc Ha.
        destruct Hc as [H|[H|[H|H]]]; [left|right;left|right;right;left|right;right;right]; lia. }

      assert (R2_2 : getr R2 2%bv = Z_to_bv 64 (sp - 80)) by (rewrite (KEPT2 2%bv) by in_cs; exact Rn2).
      assert (R2_8 : getr R2 8%bv = Z_to_bv 64 b) by (rewrite (KEPT2 8%bv) by in_cs; exact Rn8).
      assert (R2_9 : getr R2 9%bv = Z_to_bv 64 v) by (rewrite (KEPT2 9%bv) by in_cs; exact Rn9).
      assert (R2_18 : getr R2 18%bv = Z_to_bv 64 (4 * cap)) by (rewrite (KEPT2 18%bv) by in_cs; exact Rn18).
      assert (R2_19 : getr R2 19%bv = Z_to_bv 64 (4 * cap)) by (rewrite (KEPT2 19%bv) by in_cs; exact Rn19).
      assert (R2_20 : getr R2 20%bv = Z_to_bv 64 src) by (rewrite (KEPT2 20%bv) by in_cs; exact Rn20).
      assert (R2_21 : getr R2 21%bv = Z_to_bv 64 n4) by (rewrite (KEPT2 21%bv) by in_cs; exact Rn21).
      assert (R2_22 : getr R2 22%bv = Z_to_bv 64 cap) by (rewrite (KEPT2 22%bv) by in_cs; exact Rn22).
      assert (R2_24 : getr R2 24%bv = Z_to_bv 64 (vgrow cap)) by (rewrite (KEPT2 24%bv) by in_cs; exact Rn24).
      assert (R2_3 : getr R2 3%bv = getr R 3%bv) by (rewrite (KEPT2 3%bv) by in_cs; exact Rn3).
      assert (R2_4 : getr R2 4%bv = getr R 4%bv) by (rewrite (KEPT2 4%bv) by in_cs; exact Rn4).
      assert (R2S : forall r, In r [23; 25; 26; 27]%bv -> getr R2 r = getr R r).
      { intros r Hr. pose proof Hr as Hr'. repeat (destruct Hr as [<-|Hr]; [rewrite (KEPT2 _) by in_cs; apply RnS; exact Hr' |]). destruct Hr. }
      assert (SRC2 : rdn SEGS M2 (Z_to_bv 64 src) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 x))).
      { change (fld SEGS M2 src 4 x). eapply fld_agree; [lia|cbn; lia|exact SRC'|]. apply AG2; cbn; lia. }

      unhide SRCp.
      assert (Hp16 : 16 <= p) by (pose proof (Z_div_mod_eq_full p 16) as E; rewrite Hpal in E; lia).
      destruct (LB fx R2 M2 sp v b cap src x p R2a0 R2_2 R2_8 R2_9 R2_18 R2_19 R2_20 ltac:(unfold n4 in R2_21; exact R2_21) R2_22 R2_24
                   Hcap Hb0 Hbc4 Hbal4 Hp16 Hpal ltac:(unfold n4 in Hpce; lia) Hx Hs0 Hs1 ltac:(unfold n4 in SRCp; lia) ltac:(unfold n4 in HDp; exact HDp) SRC2)
        as (R3 & RUNB & R3_10 & R3_11 & R3_12 & R3_1 & R3_2 & R3_8 & R3_9 & R3_18 & R3_20 & R3_21 & R3_23 & R3_3 & R3_4 & R3S).
      hide SRCp.
      eapply srz_msteps; [exact (ms_halt _ MS1) | exact (ms_lazy _ MS1) | exact RUNB | ].
      set (M3 := wbytes M2 (Z_to_bv 64 (p + 4 * cap)) (word_to_le_bytes 4 (v_lw (Z_to_bv 64 x)))).

      assert (HDp3 : mdef M3 p n4) by (unfold M3; apply mdef_wbytes; exact HDp).
      assert (BUF3 : rdn SEGS M3 (Z_to_bv 64 b) (length (vec_bytes xs)) = Some (vec_bytes xs)).
      { destruct (Z.eq_dec cap 0) as [Hc0|Hcnz].
        - assert (xs = []) as -> by (destruct xs; [reflexivity | unfold Zlen in LEN; cbn in LEN; lia]). reflexivity.
        - assert (Hbnz : b <> 0) by (unhide Hb; destruct Hb as [[Hb00 Hc00]|(Hbp & _)]; lia).
          rewrite vec_bytes_length.
          rewrite <- (fld_vec_rdn SEGS M b xs Hb0 ltac:(lia) FE).
          unfold M3. rewrite rdn_wbytes_out_Z by (rewrite length_N_to_le_bytes; cbn; destruct (BUFp Hbnz); unfold Zlen in *; lia).
          symmetry. rewrite <- (Nat2Z.id (4 * length xs)).
          eapply rdn_agree_win; [lia | unfold Zlen in *; lia |].
          intros a Ha. unfold zwin, Zlen in *. rewrite Nat2Z.id in Ha.
          rewrite (PRES2 a) by (right; right; right; split; [exact Hbnz | lia]).
          symmetry. apply (proj1 ST1). rewrite u64_of_Z by lia. unfold zwin.
          destruct (BUF Hbnz) as (_ & Hbce & _). lia. }
      assert (MC : mcH SEGS M3 (Z_to_bv 64 p) (Z_to_bv 64 b) (4 * cap) (vec_bytes xs)).
      { constructor.
        - lia.
        - rewrite vec_bytes_length. unfold Zlen in LEN. lia.
        - exact BUF3.
        - rewrite vec_bytes_length. apply (mdef_store_ok SEGS M3 p n4); unfold Zlen in LEN; try lia. exact HDp3.
        - rewrite !u64_of_Z by lia. unhide Hb. destruct Hb as [[Hb00 Hc00]|(Hbp & Hal & Hcp & Hbc & HIn & Hdj)].
          + right. lia.
          + destruct (BUFp ltac:(lia)); [right|left]; lia.
        - rewrite u64_of_Z by lia. lia.
        - rewrite u64_of_Z by lia. lia. }
      destruct (u1_memcpy M3 (Z_to_bv 64 p) (Z_to_bv 64 b) (4 * cap) (vec_bytes xs) (seg_rom SEGS) R3 (Z_to_bv 64 0x6a1fc)
                  MC ltac:(unfold ret_ok; apply bv_eq; vm_compute; reflexivity)
                  ltac:(rewrite R3_1; apply bv_eq; vm_compute; reflexivity)
                  R3_10 R3_11 R3_12)
        as (R4 & RUN4 & KEEP4).
      eapply srz_msteps; [exact (ms_halt _ MS1) | exact (ms_lazy _ MS1) | | ].
      { lazymatch goal with |- msteps _ (mkst _ ?pc _ _) _ =>
          replace pc with u1_memcpy_entry by (apply bv_eq; vm_compute; reflexivity) end.
        exact RUN4. }
      set (M4 := wbytes M3 (Z_to_bv 64 p) (vec_bytes xs)) in *.

      assert (R4_2 : getr R4 2%bv = Z_to_bv 64 (sp - 80)) by (rewrite (KEEP4 2%bv) by in_cs; exact R3_2).
      assert (R4_8 : getr R4 8%bv = Z_to_bv 64 b) by (rewrite (KEEP4 8%bv) by in_cs; exact R3_8).
      assert (R4_9 : getr R4 9%bv = Z_to_bv 64 v) by (rewrite (KEEP4 9%bv) by in_cs; exact R3_9).
      assert (R4_18 : getr R4 18%bv = Z_to_bv 64 (4 * cap)) by (rewrite (KEEP4 18%bv) by in_cs; exact R3_18).
      assert (R4_20 : getr R4 20%bv = Z_to_bv 64 p) by (rewrite (KEEP4 20%bv) by in_cs; exact R3_20).
      assert (R4_21 : getr R4 21%bv = Z_to_bv 64 (p + 4 * cap + 4)) by (rewrite (KEEP4 21%bv) by in_cs; exact R3_21).
      assert (R4_23 : getr R4 23%bv = Z_to_bv 64 (p + n4)) by (rewrite (KEEP4 23%bv) by in_cs; rewrite R3_23; unfold n4; reflexivity).
      assert (R4_3 : getr R4 3%bv = getr R 3%bv) by (rewrite (KEEP4 3%bv) by in_cs; rewrite R3_3; exact R2_3).
      assert (R4_4 : getr R4 4%bv = getr R 4%bv) by (rewrite (KEEP4 4%bv) by in_cs; rewrite R3_4; exact R2_4).
      assert (R4S : forall r, In r [25; 26; 27]%bv -> getr R4 r = getr R r).
      { intros r Hr. pose proof Hr as Hr'.
        repeat (destruct Hr as [<-|Hr]; [rewrite (KEEP4 _) by in_cs; rewrite (R3S _) by in_cs; apply R2S; in_cs |]). destruct Hr. }

      set (W := (sp - (80 + (16 + MALLOC_STACK MI)), sp)).
      set (FT := fun a => zwin v (v + 24) a \/ (b <> 0 /\ zwin b (b + 4 * cap) a) \/ zwin p (p + 4 * vgrow cap) a).
      assert (TAIL : forall A2 R6 M6 model2,
        ainv MI A2 M6 model2 -> mstd model2 -> m_fs model2 = m_fs model -> m_fds model2 = m_fds model ->
        sx_inv ST s M6 ->
        getr R6 2%bv = Z_to_bv 64 (sp - 80) -> getr R6 21%bv = Z_to_bv 64 (p + 4 * cap + 4) ->
        getr R6 3%bv = getr R 3%bv -> getr R6 4%bv = getr R 4%bv ->
        (forall r, In r [25; 26; 27]%bv -> getr R6 r = getr R r) ->
        agree_on (zwin (sp - 80) sp) M1 M6 ->
        mdef M6 v 24 -> fld SEGS M6 v 8 p -> fld SEGS M6 (v + 8) 8 (p + 4 * cap + 4) -> fld SEGS M6 (v + 16) 8 (p + n4) ->
        (forall i, 0 <= i < cap -> fld SEGS M6 (p + 4 * i) 4 (Znth i xs)) -> fld SEGS M6 (p + 4 * cap) 4 x ->
        In (p, n4) (live MI A2) ->
        (forall a, v <= a < v + 24 -> ~ owned MI A2 a /\ ~ in_ranges [(0x10000, 0x124000)] a) ->
        eff MI A A2 M M6 W FT -> lapply (live MI A) (LAdd p n4 :: del_if b) (live MI A2) ->
        srealizes SEGS (mkCfg (@mkst fx R6 (Z_to_bv 64 0x6a218) M6 (seg_rom SEGS)) model2) K).
      { intros A2 R6 M6 model2 AI2 MS2 Hfs2 Hfds2 SX2 R6_2 R6_21 R6_3 R6_4 R6S AG6 HDv6 G0 G1 G2 GEL Gx HinP2 HDR2 EFF6 LAP.
        assert (SLT : forall a vv, sp - 80 <= a -> a + 8 <= sp -> rdn SEGS M1 (Z_to_bv 64 a) 8 = Some vv -> rdn SEGS M6 (Z_to_bv 64 a) 8 = Some vv).
        { intros a vv H1 H2 H3. rewrite (rdn_agree_win SEGS M1 M6); [exact H3 | lia | cbn; lia |].
          eapply agree_on_weaken; [exact AG6|]. intros a' Ha. unfold zwin in *. cbn in Ha. lia. }
        eapply srz_msteps; [exact (ms_halt _ MS2) | exact (ms_lazy _ MS2) | | ].
        { apply (epilogue fx R6 M6 sp ret (Z_to_bv 64 (p + 4 * cap + 4))
                 (getr R 8%bv) (getr R 9%bv) (getr R 18%bv) (getr R 19%bv) (getr R 20%bv) (getr R 21%bv) (getr R 22%bv) (getr R 23%bv) (getr R 24%bv));
            try assumption; try lia.
          - apply SLT; [lia|lia|rdn_fix SL1].
          - apply SLT; [lia|lia|rdn_fix SL2].
          - apply SLT; [lia|lia|rdn_fix SL3].
          - apply SLT; [lia|lia|rdn_fix SL4].
          - apply SLT; [lia|lia|rdn_fix SL5].
          - apply SLT; [lia|lia|rdn_fix SL6].
          - apply SLT; [lia|lia|rdn_fix SL7].
          - apply SLT; [lia|lia|rdn_fix SL8].
          - apply SLT; [lia|lia|rdn_fix SL9].
          - apply SLT; [lia|lia|rdn_fix SL10]. }
        eapply (CONT A2 _ M6 model2 p).
        -   constructor.
          + exact AI2.
          + exact MS2.
          + exact Hfs2.
          + exact Hfds2.
          + exact SX2.
          + intros r Hr; unfold callee_saved in Hr.
            repeat (destruct Hr as [<-|Hr]; [gres; first [reflexivity | symmetry; assumption | rewrite ?R6_3, ?R6_4; reflexivity | apply R6S; in_cs ] |]).
            destruct Hr.
        -
          unhide HDRp. unfold vgrow in *.
          unfold CRep.vec32. rewrite Zlen_app1. rewrite LEN.
          split; [exact Hv0|]. split; [exact Hv1|]. split; [exact HDv6|].
          split; [lia|].
          split. { right. split; [lia|]. split; [exact Hpal|]. split; [lia|]. split; [lia|].
                   split; [replace (4 * Z.max (2 * cap) (cap + 1)) with n4 by lia; exact HinP2 | lia]. }
          split. { exact G0. }
          split. { replace (p + 4 * (cap + 1)) with (p + 4 * cap + 4) by lia. exact G1. }
          split. { replace (p + 4 * Z.max (2 * cap) (cap + 1)) with (p + n4) by lia. exact G2. }
          intros i Hi. destruct (Z.lt_ge_cases i cap) as [Hlt|Hge].
          + destruct (FE i ltac:(lia)) as [Hr _]. rewrite Znth_app_l by lia. split; [exact Hr|]. apply GEL; lia.
          + replace i with (Zlen xs) by lia. rewrite Znth_app_r1. split; [lia|]. rewrite LEN. exact Gx.
        - gres. rewrite LEN. replace (p + 4 * (cap + 1)) with (p + 4 * cap + 4) by lia. reflexivity.
        - replace (4 * vgrow cap) with n4 by (unfold vgrow; lia). exact LAP.
        -
          eapply eff_weaken; [exact EFF6 | intros a' H; exact H].
      }

      assert (HDv2 : mdef M2 v 24).
      { intros i Hi. destruct (DEF1 (Z_to_bv 64 (v + i)) (stores_in_mdef _ _ _ _ _ ST1 HDv i Hi)) as [H|[H|H]]; [exact H| |].
        - exfalso. rewrite u64_of_Z in H by lia. exact (proj1 (HDR (v + i) ltac:(lia)) H).
        - exfalso. rewrite u64_of_Z in H by lia. exact (proj2 (HDR (v + i) ltac:(lia)) (ly_errno_img _ H)). }
      assert (HDv4 : mdef M4 v 24) by (unfold M4, M3; apply mdef_wbytes, mdef_wbytes; exact HDv2).
      set (M5 := wbytes (wbytes (wbytes M4 (Z_to_bv 64 v) (word_to_le_bytes 8 (Z_to_bv 64 p)))
                                (Z_to_bv 64 (v + 8)) (word_to_le_bytes 8 (Z_to_bv 64 (p + 4 * cap + 4))))
                         (Z_to_bv 64 (v + 16)) (word_to_le_bytes 8 (Z_to_bv 64 (p + n4)))).
      assert (ST25 : stores_in (fun a => zwin p (p + n4) a \/ zwin v (v + 24) a) M2 M5).
      { unfold M5, M4, M3.
        eapply stores_in_wbytes_more; [eapply stores_in_wbytes_more; [eapply stores_in_wbytes_more;
          [eapply stores_in_wbytes_more; [apply stores_in_wbytes| | |] | | |] | | |] | | |];
          rewrite ?length_N_to_le_bytes, ?vec_bytes_length; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unfold Zlen in LEN; try lia;
          intros a Ha; unfold zwin; lia. }
      assert (AG25 : forall lo hi, 0 <= lo -> hi < 2 ^ 64 -> (hi <= p \/ p + n4 <= lo) -> (hi <= v \/ v + 24 <= lo) ->
                     agree_on (zwin lo hi) M2 M5).
      { intros lo hi H1 H2 H3 H4. eapply stores_in_agree; [exact ST25|]. intros a Ha. unfold zwin in *. lia. }
      unhide HDRp.
      assert (AG15 : agree_on (zwin (sp - 80) sp) M1 M5).
      { intros a Ha. unfold zwin in Ha. rewrite (AG25 (sp - 80) sp); try lia.
        - apply PRES2. left. lia.
        - unhide WINv'. lia.
        - unfold zwin. lia. }
      assert (G0 : fld SEGS M5 v 8 p).
      { unfold fld, M5. rewrite 2!rdn_wbytes_out_Z by (rewrite length_N_to_le_bytes; cbn; lia).
        apply rdn_wbytes_hit8. rewrite u64_of_Z by lia. lia. }
      assert (G1 : fld SEGS M5 (v + 8) 8 (p + 4 * cap + 4)).
      { unfold fld, M5. rewrite rdn_wbytes_out_Z by (rewrite length_N_to_le_bytes; cbn; lia).
        apply rdn_wbytes_hit8. rewrite u64_of_Z by lia. lia. }
      assert (G2 : fld SEGS M5 (v + 16) 8 (p + n4)).
      { unfold fld, M5. apply rdn_wbytes_hit8. rewrite u64_of_Z by lia. lia. }
      assert (EL4 : rdn SEGS M4 (Z_to_bv 64 p) (4 * length xs)%nat = Some (vec_bytes xs)).
      { unfold M4. rewrite <- vec_bytes_length. apply RefReadLib.rdn_wbytes_self.
        rewrite vec_bytes_length, u64_of_Z by lia. unfold Zlen in LEN. lia. }
      assert (GEL : forall i, 0 <= i < cap -> fld SEGS M5 (p + 4 * i) 4 (Znth i xs)).
      { intros i Hi. eapply fld_agree; [lia | cbn; lia | apply (rdn_vec_fld SEGS M4 p xs); try lia; exact EL4 |].
        unfold M5. eapply stores_in_agree.
        - eapply stores_in_wbytes_more; [eapply stores_in_wbytes_more; [apply stores_in_wbytes with (W := zwin v (v + 24)) | | |] | | |];
            rewrite ?length_N_to_le_bytes; cbn; try lia; intros a Ha; unfold zwin; lia.
        - intros a Ha. unfold zwin in *. cbn in Ha. lia. }
      assert (Gx : fld SEGS M5 (p + 4 * cap) 4 x).
      { assert (Gx3 : fld SEGS M3 (p + 4 * cap) 4 x).
        { unfold fld, M3. rewrite sw_of_lw by lia. apply rdn_wbytes_hit4. rewrite u64_of_Z by lia. lia. }
        eapply fld_agree; [lia | cbn; lia | exact Gx3 |].
        unfold M5, M4. eapply stores_in_agree.
        - eapply stores_in_wbytes_more; [eapply stores_in_wbytes_more; [eapply stores_in_wbytes_more;
            [apply stores_in_wbytes with (W := fun a => zwin p (p + 4 * cap) a \/ zwin v (v + 24) a) | | |] | | |] | | |];
            rewrite ?length_N_to_le_bytes, ?vec_bytes_length; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unfold Zlen in LEN; try lia;
            intros a Ha; unfold zwin; lia.
        - intros a Ha. unfold zwin in *. cbn in Ha. lia. }

      assert (EFF5 : eff MI A A1 M M5 W FT).
      { eapply eff_weaken.
        - eapply (eff_trans MI); [ | | intros a Ha; apply WIN1; unfold W_of, W in Ha; cbn in Ha; lia].
          + eapply (eff_trans MI); [ | | intros a Ha; apply WIN1; unfold W_of, W in Ha; cbn in Ha; lia].
            * apply (eff_store MI A M M1 W FT); [| exact (proj2 ST1)].
              intros a HF HW. apply (proj1 ST1). intros Hz. apply HW. unfold W_of, W, zwin in *. cbn. lia.
            * eapply (eff_of_new MI A A1 M1 M2 model1 W FT p n4); try eassumption.
              -- intros a Ha. unfold W_of, W, zwin in *. cbn. lia.
              -- intros a Ha. unfold FT. right; right. unfold zwin, vgrow. lia.
          + apply (eff_store MI A1 M2 M5 W FT); [| exact (proj2 ST25)].
            intros a HF HW. apply (proj1 ST25). intros [Hz|Hz]; apply HF; unfold FT; [right; right; unfold zwin, vgrow in *; lia | left; exact Hz].
        - intros a [[H|H]|H]; exact H. }
      hide HDRp.
      eapply srz_msteps; [exact (ms_halt _ MS1) | exact (ms_lazy _ MS1) | | ].
      { norm_pc.
        stw F_6a1bc D_6a1bc (Z_to_bv 64 v) (Z_to_bv 64 p) ltac:(ok_mdef HDv4).
        stw F_6a1c0 D_6a1c0 (Z_to_bv 64 (v + 8)) (Z_to_bv 64 (p + 4 * cap + 4)) ltac:(ok_mdef HDv4).
        stw F_6a1c4 D_6a1c4 (Z_to_bv 64 (v + 16)) (Z_to_bv 64 (p + n4)) ltac:(ok_mdef HDv4).
        apply mst_refl. }
      fold M5.
      assert (HDv5 : mdef M5 v 24) by (unfold M5; apply mdef_wbytes, mdef_wbytes, mdef_wbytes; exact HDv4).
      destruct (Z.eq_dec b 0) as [Hbz|Hbnz].
      *
        eapply srz_msteps; [exact (ms_halt _ MS1) | exact (ms_lazy _ MS1) | | ].
        { norm_pc. stepb_tk F_6a1c8 D_6a1c8 ltac:(rewrite R4_8, Hbz; apply c_eq_refl). apply mst_refl. }
        lazymatch goal with |- srealizes _ (mkCfg (mkst _ ?pc _ _) _) _ =>
          replace pc with (Z_to_bv 64 0x6a218) by (apply bv_eq; vm_compute; reflexivity) end.
        apply (TAIL A1 R4 M5 model1); try assumption.
        -- eapply (stores_in_ainv SEGS Ly.L MI); [exact AI1 | exact ST25 |].
           intros a [Ha|Ha]; [apply Hpown | apply HDR1]; unfold zwin in Ha; lia.
        -- eapply (stores_in_sx SEGS Ly.L ST); [exact SX1 | exact ST25 |].
           intros a Ha. assert (Hni : ~ in_ranges [(0x10000, 0x124000)] a)
             by (destruct Ha as [Ha|Ha]; [apply Hpown | apply HDR1]; unfold zwin in Ha; lia).
           destruct (offimg_sep a Hni) as (X1 & X2 & _). split; assumption.
        -- subst b. cbn. exists (live MI A1). split; [exact LADD | reflexivity].
      *
        unhide Hb. destruct Hb as [[Hb00 _]|(Hbp & Hal & Hcp & Hbc & HIn & Hdj)]; [lia|].
        eapply srz_msteps; [exact (ms_halt _ MS1) | exact (ms_lazy _ MS1) | | ].
        { norm_pc. stepb_ft F_6a1c8 D_6a1c8 ltac:(rewrite R4_8; rewrite c_eq_Z' by lia; apply Z.eqb_neq; lia).
          sv F_6a1cc D_6a1cc (Z_to_bv 64 b).
          sv F_6a1d0 D_6a1d0 (Z_to_bv 64 (4 * cap)).
          stepj F_6a1d4 D_6a1d4. apply mst_refl. }
        lazymatch goal with |- srealizes _ (mkCfg (mkst ?r ?pc _ _) _) _ =>
          replace pc with (Z_to_bv 64 DEL1) by (apply bv_eq; vm_compute; reflexivity); set (R5 := r) end.
        eapply (u1_op_delete1_spec MI fx A1 R5 M5 model1 b (4 * cap) (sp - 80) 0x6a218 K).
        -- eapply (stores_in_ainv SEGS Ly.L MI); [exact AI1 | exact ST25 |].
           intros a [Ha|Ha]; [apply Hpown | apply HDR1]; unfold zwin in Ha; lia.
        -- exact MS1.
        -- eapply (roc_stores Ly.L); [exact ROC2 | exact ST25 |]. intros a Ha. cbn [ly_img Ly.L].
           destruct Ha as [Ha|Ha]; [apply Hpown | apply HDR1]; unfold zwin in Ha; lia.
        -- constructor; unfold R5; gres.
           ++ apply bv_eq; vm_compute; reflexivity.
           ++ unfold ret_ok. apply bv_eq. vm_compute. reflexivity.
           ++ lia.
           ++ exact R4_2.
           ++ replace (sp - 80) with (sp - 16 * 5) by lia. apply mod16_sub. exact Hsp16.
           ++ lia.
           ++ rewrite R4_3. exact Hgp.
           ++ rewrite R4_4. exact Htp.
        -- unfold R5; gres; reflexivity.
        -- right. apply LIVE1. exact HIn.
        -- lia.
        -- unfold stack_room. eapply stores_in_store_ok; [exact ST25|].
           assert (HDW2 : mdef M2 (sp - (80 + (16 + MALLOC_STACK MI))) (80 + (16 + MALLOC_STACK MI))).
           { eapply (mdef_through (fun a => owned MI A a \/ errno_win Ly.L a)); [exact DEF1 | eapply stores_in_mdef; [exact ST1 | exact HDW] | lia | lia |].
             intros a Ha [Ho|He]; [exact (proj1 (WIN a ltac:(lia)) Ho) | exact (proj2 (WIN a ltac:(lia)) (ly_errno_img a He))]. }
           replace (sp - 80 - MALLOC_STACK MI) with (sp - (80 + (16 + MALLOC_STACK MI)) + 16) by lia.
           apply (mdef_store_ok_off SEGS M2 _ _ 16 _ HDW2); lia.
        -- intros a Ha. apply WIN1. unfold zwin in *. lia.
        -- intros A2 R6 M6 model2 AI2 MS2 Hfs2 Hfds2 KEPT6 LDEL CAPS2 BIGC2 OWN2 FR2 DEF2.
           assert (Hpb : p <> b).
           { intros ->. destruct LADD as [_ Hnin]. apply Hnin. apply in_map_iff. exists (b, 4 * cap). split; [reflexivity|exact HIn]. }
           pose proof (BUFp ltac:(lia)) as BUFp'.
           unhide Hdj.
           assert (FSEP : forall a, (sp - 80 <= a < sp) \/ (v <= a < v + 24) \/ (p <= a < p + n4) ->
                            ~ owned MI A1 a /\ ~ (b <= a < b + 4 * cap) /\ ~ zwin (sp - 80 - MALLOC_STACK MI) (sp - 80) a /\ ~ in_ranges (ly_img Ly.L) a).
           { intros a [Ha|[Ha|Ha]].
             - destruct (WIN1 a ltac:(lia)) as [Y1 Y2]. split; [exact Y1|]. split; [|split; [|exact Y2]]; (destruct (BUF ltac:(lia)) as (_ & Hbce & _); unfold zwin; lia).
             - destruct (HDR1 a ltac:(lia)) as [Y1 Y2]. split; [exact Y1|]. split; [|split; [|exact Y2]]; (unfold zwin; unhide WINv'; lia).
             - destruct (Hpown a ltac:(lia)) as [Y1 Y2]. split; [exact Y1|]. split; [|split; [|exact Y2]]; (unfold zwin; lia). }
           assert (AG56 : forall lo hi, 0 <= lo -> hi < 2 ^ 64 ->
                    ((sp - 80 <= lo /\ hi <= sp) \/ (v <= lo /\ hi <= v + 24) \/ (p <= lo /\ hi <= p + n4)) ->
                    agree_on (zwin lo hi) M5 M6).
           { intros lo hi H1 H2 Hc a Ha. unfold zwin in Ha. apply FR2. rewrite u64_of_Z by lia.
             destruct (FSEP a ltac:(clear -Hc Ha; destruct Hc as [H|[H|H]]; [left|right;left|right;right]; lia)) as (X1 & X2 & X3 & X4).
             intros [H|[H|[H|H]]]; [exact (X1 H)|exact (X2 H)|exact (X3 H)|exact (X4 (ly_errno_img a H))]. }
           apply (TAIL A2 R6 M6 model2).
           ++ exact AI2.
           ++ exact MS2.
           ++ rewrite Hfs2. exact Hfs1.
           ++ rewrite Hfds2. exact Hfds1.
           ++ eapply (sx_through SEGS Ly.L ST); [ | exact FR2 | ].
              ** eapply (stores_in_sx SEGS Ly.L ST); [exact SX1 | exact ST25 |].
                 intros a Ha. apply (offimg_not_sx SEGS Ly.L ST ly_rw_img ly_relro_img).
                 destruct Ha as [Ha|Ha]; [apply Hpown | apply HDR1]; unfold zwin in Ha; lia.
              ** intros a [Ho|[Hblk|[Hw|He]]].
                 --- eapply (owned_later_not_sx SEGS Ly.L MI ST ly_rw_img ly_relro_img ly_rw_not_relro); [exact AI | exact Hown_sx | exact NEWT1 | exact Ho].
                 --- apply (offimg_not_sx SEGS Ly.L ST ly_rw_img ly_relro_img). destruct (BUF ltac:(lia)) as (_ & _ & Hbown'). apply Hbown'. lia.
                 --- apply (offimg_not_sx SEGS Ly.L ST ly_rw_img ly_relro_img). apply WIN1. unfold zwin in Hw. lia.
                 --- split; [exact (Herr_sx a He) | intros Hr; exact (ly_rw_not_relro a (ly_errno_rw a He) Hr)].
           ++ rewrite (KEPT6 2%bv) by in_cs. unfold R5. gres. exact R4_2.
           ++ rewrite (KEPT6 21%bv) by in_cs. unfold R5. gres. exact R4_21.
           ++ rewrite (KEPT6 3%bv) by in_cs. unfold R5. gres. exact R4_3.
           ++ rewrite (KEPT6 4%bv) by in_cs. unfold R5. gres. exact R4_4.
           ++ intros r Hr. pose proof Hr as Hr'.
              repeat (destruct Hr as [<-|Hr]; [rewrite (KEPT6 _) by in_cs; unfold R5; gres; apply R4S; exact Hr' |]). destruct Hr.
           ++ intros a Ha. rewrite (AG56 (sp - 80) sp); [apply AG15; exact Ha | lia | lia | left; lia | exact Ha].
           ++ eapply (mdef_through (fun a => owned MI A1 a \/ ((b <= a < b + 4 * cap) \/ errno_win Ly.L a))); [exact DEF2 | exact HDv5 | lia | lia |].
              intros a Ha [Ho|[Hblk|He]]; [exact (proj1 (HDR1 a Ha) Ho)  |  lia | exact (proj2 (HDR1 a Ha) (ly_errno_img a He))].
           ++ eapply fld_agree; [lia | cbn; lia | exact G0 |]. apply AG56; cbn; lia.
           ++ eapply fld_agree; [lia | cbn; lia | exact G1 |]. apply AG56; cbn; lia.
           ++ eapply fld_agree; [lia | cbn; lia | exact G2 |]. apply AG56; cbn; lia.
           ++ intros i Hi. eapply fld_agree; [lia | cbn; lia | apply GEL; lia |]. apply AG56; cbn; lia.
           ++ eapply fld_agree; [lia | cbn; lia | exact Gx |]. apply AG56; cbn; lia.
           ++ eapply live_del_keeps; [exact LDEL | exact HinP | exact Hpb].
           ++ intros a Ha. split; [| apply HDR1; lia]. intros Ho. destruct (OWN2 a Ho) as [Ho1|Hblk]; [exact (proj1 (HDR1 a Ha) Ho1) | lia].
           ++ eapply eff_weaken.
              ** eapply (eff_trans MI); [exact EFF5 | | intros a Ha; apply (stack_sep A2 M6 model2 a AI2); unfold W_of, W in Ha; cbn in Ha; lia].
                 eapply (eff_of_del MI A1 A2 M5 M6 W FT b (4 * cap)); try eassumption.
                 --- intros a Ha. unfold W_of, W, zwin in *. cbn. lia.
                 --- intros a Ha. unfold FT. right; left. split; [lia|]. unfold zwin. lia.
                 --- intros a Ha. destruct (BUF ltac:(lia)) as (_ & _ & Hbown'). exact (proj2 (Hbown' a Ha)).
              ** intros a [H|H]; exact H.
           ++ cbn. exists (live MI A1). split; [exact LADD|]. unfold del_if. destruct (Z.eqb_spec b 0); [lia|].
              cbn. exists (live MI A2). split; [exact LDEL | reflexivity].
  Qed.
End PbSlow.
