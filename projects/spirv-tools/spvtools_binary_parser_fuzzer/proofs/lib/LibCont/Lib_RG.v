(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Plain.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StepTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.WalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StartupTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SumWalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MemSplit OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ShapeAlg OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SRealizes OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefReadLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibEff OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MmapSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibMaskBits OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.S1Layout.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.CRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.StrLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.S1Facts.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Module S1_code_6c040_6c160.

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_6c040 : bv 32 := 0x000016b7.
Lemma F_6c040 : fetch_word Plain.M.loaded_segments (0x6c080 : word) = Some W_6c040.
Proof. vm_refl. Qed.
Lemma D_6c040 : decode_any W_6c040 = Some (Lui 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c044 : bv 32 := 0xfffa9797.
Lemma F_6c044 : fetch_word Plain.M.loaded_segments (0x6c084 : word) = Some W_6c044.
Proof. vm_refl. Qed.
Lemma D_6c044 : decode_any W_6c044 = Some (Auipc 15 1048489, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c048 : bv 32 := 0x5716871b.
Lemma F_6c048 : fetch_word Plain.M.loaded_segments (0x6c088 : word) = Some W_6c048.
Proof. vm_refl. Qed.
Lemma D_6c048 : decode_any W_6c048 = Some (OpImm32 14 13 1393, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c04c : bv 32 := 0x8f47b683.
Lemma F_6c04c : fetch_word Plain.M.loaded_segments (0x6c08c : word) = Some W_6c04c.
Proof. vm_refl. Qed.
Lemma D_6c04c : decode_any W_6c04c = Some (Load SZ8 true 13 15 2292, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c050 : bv 32 := 0x00e53023.
Lemma F_6c050 : fetch_word Plain.M.loaded_segments (0x6c090 : word) = Some W_6c050.
Proof. vm_refl. Qed.
Lemma D_6c050 : decode_any W_6c050 = Some (Store SZ8 10 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c054 : bv 32 := 0x00850793.
Lemma F_6c054 : fetch_word Plain.M.loaded_segments (0x6c094 : word) = Some W_6c054.
Proof. vm_refl. Qed.
Lemma D_6c054 : decode_any W_6c054 = Some (OpImm ALU_ADD 15 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c058 : bv 32 := 0x00100813.
Lemma F_6c058 : fetch_word Plain.M.loaded_segments (0x6c098 : word) = Some W_6c058.
Proof. vm_refl. Qed.
Lemma D_6c058 : decode_any W_6c058 = Some (OpImm ALU_ADD 16 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c05c : bv 32 := 0x13800893.
Lemma F_6c05c : fetch_word Plain.M.loaded_segments (0x6c09c : word) = Some W_6c05c.
Proof. vm_refl. Qed.
Lemma D_6c05c : decode_any W_6c05c = Some (OpImm ALU_ADD 17 0 312, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c060 : bv 32 := 0x03e75293.
Lemma F_6c060 : fetch_word Plain.M.loaded_segments (0x6c0a0 : word) = Some W_6c060.
Proof. vm_refl. Qed.
Lemma D_6c060 : decode_any W_6c060 = Some (ShiftImm ALU_SRL 5 14 62, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c064 : bv 32 := 0x00e2c733.
Lemma F_6c064 : fetch_word Plain.M.loaded_segments (0x6c0a4 : word) = Some W_6c064.
Proof. vm_refl. Qed.
Lemma D_6c064 : decode_any W_6c064 = Some (Op ALU_XOR 14 5 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c068 : bv 32 := 0x02d70733.
Lemma F_6c068 : fetch_word Plain.M.loaded_segments (0x6c0a8 : word) = Some W_6c068.
Proof. vm_refl. Qed.
Lemma D_6c068 : decode_any W_6c068 = Some (Mul M_MUL 14 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c06c : bv 32 := 0x01070733.
Lemma F_6c06c : fetch_word Plain.M.loaded_segments (0x6c0ac : word) = Some W_6c06c.
Proof. vm_refl. Qed.
Lemma D_6c06c : decode_any W_6c06c = Some (Op ALU_ADD 14 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c070 : bv 32 := 0x00180813.
Lemma F_6c070 : fetch_word Plain.M.loaded_segments (0x6c0b0 : word) = Some W_6c070.
Proof. vm_refl. Qed.
Lemma D_6c070 : decode_any W_6c070 = Some (OpImm ALU_ADD 16 16 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c074 : bv 32 := 0x00e7b023.
Lemma F_6c074 : fetch_word Plain.M.loaded_segments (0x6c0b4 : word) = Some W_6c074.
Proof. vm_refl. Qed.
Lemma D_6c074 : decode_any W_6c074 = Some (Store SZ8 15 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c078 : bv 32 := 0x00878793.
Lemma F_6c078 : fetch_word Plain.M.loaded_segments (0x6c0b8 : word) = Some W_6c078.
Proof. vm_refl. Qed.
Lemma D_6c078 : decode_any W_6c078 = Some (OpImm ALU_ADD 15 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c07c : bv 32 := 0xff1812e3.
Lemma F_6c07c : fetch_word Plain.M.loaded_segments (0x6c0bc : word) = Some W_6c07c.
Proof. vm_refl. Qed.
Lemma D_6c07c : decode_any W_6c07c = Some (Branch BC_NE 16 17 8164, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c080 : bv 32 := 0x7ff50513.
Lemma F_6c080 : fetch_word Plain.M.loaded_segments (0x6c0c0 : word) = Some W_6c080.
Proof. vm_refl. Qed.
Lemma D_6c080 : decode_any W_6c080 = Some (OpImm ALU_ADD 10 10 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c084 : bv 32 := 0x1c0530a3.
Lemma F_6c084 : fetch_word Plain.M.loaded_segments (0x6c0c4 : word) = Some W_6c084.
Proof. vm_refl. Qed.
Lemma D_6c084 : decode_any W_6c084 = Some (Store SZ8 10 0 449, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c088 : bv 32 := 0x00058513.
Lemma F_6c088 : fetch_word Plain.M.loaded_segments (0x6c0c8 : word) = Some W_6c088.
Proof. vm_refl. Qed.
Lemma D_6c088 : decode_any W_6c088 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c08c : bv 32 := 0x00060593.
Lemma F_6c08c : fetch_word Plain.M.loaded_segments (0x6c0cc : word) = Some W_6c08c.
Proof. vm_refl. Qed.
Lemma D_6c08c : decode_any W_6c08c = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c090 : bv 32 := 0x0040006f.
Lemma F_6c090 : fetch_word Plain.M.loaded_segments (0x6c0d0 : word) = Some W_6c090.
Proof. vm_refl. Qed.
Lemma D_6c090 : decode_any W_6c090 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c094 : bv 32 := 0xff010113.
Lemma F_6c094 : fetch_word Plain.M.loaded_segments (0x6c0d4 : word) = Some W_6c094.
Proof. vm_refl. Qed.
Lemma D_6c094 : decode_any W_6c094 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c098 : bv 32 := 0x00113423.
Lemma F_6c098 : fetch_word Plain.M.loaded_segments (0x6c0d8 : word) = Some W_6c098.
Proof. vm_refl. Qed.
Lemma D_6c098 : decode_any W_6c098 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c09c : bv 32 := 0x0a050263.
Lemma F_6c09c : fetch_word Plain.M.loaded_segments (0x6c0dc : word) = Some W_6c09c.
Proof. vm_refl. Qed.
Lemma D_6c09c : decode_any W_6c09c = Some (Branch BC_EQ 10 0 164, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c0a0 : bv 32 := 0x00400693.
Lemma F_6c0a0 : fetch_word Plain.M.loaded_segments (0x6c0e0 : word) = Some W_6c0a0.
Proof. vm_refl. Qed.
Lemma D_6c0a0 : decode_any W_6c0a0 = Some (OpImm ALU_ADD 13 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c0a4 : bv 32 := 0x00058613.
Lemma F_6c0a4 : fetch_word Plain.M.loaded_segments (0x6c0e4 : word) = Some W_6c0a4.
Proof. vm_refl. Qed.
Lemma D_6c0a4 : decode_any W_6c0a4 = Some (OpImm ALU_ADD 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c0a8 : bv 32 := 0x00b6c463.
Lemma F_6c0a8 : fetch_word Plain.M.loaded_segments (0x6c0e8 : word) = Some W_6c0a8.
Proof. vm_refl. Qed.
Lemma D_6c0a8 : decode_any W_6c0a8 = Some (Branch BC_LT 13 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c0ac : bv 32 := 0x00400613.
Lemma F_6c0ac : fetch_word Plain.M.loaded_segments (0x6c0ec : word) = Some W_6c0ac.
Proof. vm_refl. Qed.
Lemma D_6c0ac : decode_any W_6c0ac = Some (OpImm ALU_ADD 12 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c0b0 : bv 32 := 0x00900693.
Lemma F_6c0b0 : fetch_word Plain.M.loaded_segments (0x6c0f0 : word) = Some W_6c0b0.
Proof. vm_refl. Qed.
Lemma D_6c0b0 : decode_any W_6c0b0 = Some (OpImm ALU_ADD 13 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c0b4 : bv 32 := 0x00d64463.
Lemma F_6c0b4 : fetch_word Plain.M.loaded_segments (0x6c0f4 : word) = Some W_6c0b4.
Proof. vm_refl. Qed.
Lemma D_6c0b4 : decode_any W_6c0b4 = Some (Branch BC_LT 12 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c0b8 : bv 32 := 0x00900613.
Lemma F_6c0b8 : fetch_word Plain.M.loaded_segments (0x6c0f8 : word) = Some W_6c0b8.
Proof. vm_refl. Qed.
Lemma D_6c0b8 : decode_any W_6c0b8 = Some (OpImm ALU_ADD 12 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c0bc : bv 32 := 0x01c60693.
Lemma F_6c0bc : fetch_word Plain.M.loaded_segments (0x6c0fc : word) = Some W_6c0bc.
Proof. vm_refl. Qed.
Lemma D_6c0bc : decode_any W_6c0bc = Some (OpImm ALU_ADD 13 12 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c0c0 : bv 32 := 0xffc60613.
Lemma F_6c0c0 : fetch_word Plain.M.loaded_segments (0x6c100 : word) = Some W_6c0c0.
Proof. vm_refl. Qed.
Lemma D_6c0c0 : decode_any W_6c0c0 = Some (OpImm ALU_ADD 12 12 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c0c4 : bv 32 := 0x00058713.
Lemma F_6c0c4 : fetch_word Plain.M.loaded_segments (0x6c104 : word) = Some W_6c0c4.
Proof. vm_refl. Qed.
Lemma D_6c0c4 : decode_any W_6c0c4 = Some (OpImm ALU_ADD 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c0c8 : bv 32 := 0x00d5c463.
Lemma F_6c0c8 : fetch_word Plain.M.loaded_segments (0x6c108 : word) = Some W_6c0c8.
Proof. vm_refl. Qed.
Lemma D_6c0c8 : decode_any W_6c0c8 = Some (Branch BC_LT 11 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c0cc : bv 32 := 0x00068713.
Lemma F_6c0cc : fetch_word Plain.M.loaded_segments (0x6c10c : word) = Some W_6c0cc.
Proof. vm_refl. Qed.
Lemma D_6c0cc : decode_any W_6c0cc = Some (OpImm ALU_ADD 14 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c0d0 : bv 32 := 0x00c59863.
Lemma F_6c0d0 : fetch_word Plain.M.loaded_segments (0x6c110 : word) = Some W_6c0d0.
Proof. vm_refl. Qed.
Lemma D_6c0d0 : decode_any W_6c0d0 = Some (Branch BC_NE 11 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c0e0 : bv 32 := 0xfffa9597.
Lemma F_6c0e0 : fetch_word Plain.M.loaded_segments (0x6c120 : word) = Some W_6c0e0.
Proof. vm_refl. Qed.
Lemma D_6c0e0 : decode_any W_6c0e0 = Some (Auipc 11 1048489, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c0e4 : bv 32 := 0x8705b583.
Lemma F_6c0e4 : fetch_word Plain.M.loaded_segments (0x6c124 : word) = Some W_6c0e4.
Proof. vm_refl. Qed.
Lemma D_6c0e4 : decode_any W_6c0e4 = Some (Load SZ8 true 11 11 2160, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c0e8 : bv 32 := 0x40c706b3.
Lemma F_6c0e8 : fetch_word Plain.M.loaded_segments (0x6c128 : word) = Some W_6c0e8.
Proof. vm_refl. Qed.
Lemma D_6c0e8 : decode_any W_6c0e8 = Some (Op ALU_SUB 13 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c0ec : bv 32 := 0xfffa9797.
Lemma F_6c0ec : fetch_word Plain.M.loaded_segments (0x6c12c : word) = Some W_6c0ec.
Proof. vm_refl. Qed.
Lemma D_6c0ec : decode_any W_6c0ec = Some (Auipc 15 1048489, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c0f0 : bv 32 := 0x8347b783.
Lemma F_6c0f0 : fetch_word Plain.M.loaded_segments (0x6c130 : word) = Some W_6c0f0.
Proof. vm_refl. Qed.
Lemma D_6c0f0 : decode_any W_6c0f0 = Some (Load SZ8 true 15 15 2100, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c0f4 : bv 32 := 0x00b685b3.
Lemma F_6c0f4 : fetch_word Plain.M.loaded_segments (0x6c134 : word) = Some W_6c0f4.
Proof. vm_refl. Qed.
Lemma D_6c0f4 : decode_any W_6c0f4 = Some (Op ALU_ADD 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c0f8 : bv 32 := 0xfffa9697.
Lemma F_6c0f8 : fetch_word Plain.M.loaded_segments (0x6c138 : word) = Some W_6c0f8.
Proof. vm_refl. Qed.
Lemma D_6c0f8 : decode_any W_6c0f8 = Some (Auipc 13 1048489, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c0fc : bv 32 := 0x8f86b683.
Lemma F_6c0fc : fetch_word Plain.M.loaded_segments (0x6c13c : word) = Some W_6c0fc.
Proof. vm_refl. Qed.
Lemma D_6c0fc : decode_any W_6c0fc = Some (Load SZ8 true 13 13 2296, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c100 : bv 32 := 0x00f5c5b3.
Lemma F_6c100 : fetch_word Plain.M.loaded_segments (0x6c140 : word) = Some W_6c100.
Proof. vm_refl. Qed.
Lemma D_6c100 : decode_any W_6c100 = Some (Op ALU_XOR 11 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c104 : bv 32 := 0x00c50633.
Lemma F_6c104 : fetch_word Plain.M.loaded_segments (0x6c144 : word) = Some W_6c104.
Proof. vm_refl. Qed.
Lemma D_6c104 : decode_any W_6c104 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c108 : bv 32 := 0x00e50533.
Lemma F_6c108 : fetch_word Plain.M.loaded_segments (0x6c148 : word) = Some W_6c108.
Proof. vm_refl. Qed.
Lemma D_6c108 : decode_any W_6c108 = Some (Op ALU_ADD 10 10 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c10c : bv 32 := 0x00064703.
Lemma F_6c10c : fetch_word Plain.M.loaded_segments (0x6c14c : word) = Some W_6c10c.
Proof. vm_refl. Qed.
Lemma D_6c10c : decode_any W_6c10c = Some (Load SZ1 false 14 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c110 : bv 32 := 0x00659793.
Lemma F_6c110 : fetch_word Plain.M.loaded_segments (0x6c150 : word) = Some W_6c110.
Proof. vm_refl. Qed.
Lemma D_6c110 : decode_any W_6c110 = Some (ShiftImm ALU_SLL 15 11 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c114 : bv 32 := 0x0025d813.
Lemma F_6c114 : fetch_word Plain.M.loaded_segments (0x6c154 : word) = Some W_6c114.
Proof. vm_refl. Qed.
Lemma D_6c114 : decode_any W_6c114 = Some (ShiftImm ALU_SRL 16 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c118 : bv 32 := 0x010787b3.
Lemma F_6c118 : fetch_word Plain.M.loaded_segments (0x6c158 : word) = Some W_6c118.
Proof. vm_refl. Qed.
Lemma D_6c118 : decode_any W_6c118 = Some (Op ALU_ADD 15 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c11c : bv 32 := 0x00e78733.
Lemma F_6c11c : fetch_word Plain.M.loaded_segments (0x6c15c : word) = Some W_6c11c.
Proof. vm_refl. Qed.
Lemma D_6c11c : decode_any W_6c11c = Some (Op ALU_ADD 14 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c120 : bv 32 := 0x00d70733.
Lemma F_6c120 : fetch_word Plain.M.loaded_segments (0x6c160 : word) = Some W_6c120.
Proof. vm_refl. Qed.
Lemma D_6c120 : decode_any W_6c120 = Some (Op ALU_ADD 14 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c124 : bv 32 := 0x00160613.
Lemma F_6c124 : fetch_word Plain.M.loaded_segments (0x6c164 : word) = Some W_6c124.
Proof. vm_refl. Qed.
Lemma D_6c124 : decode_any W_6c124 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c128 : bv 32 := 0x00b745b3.
Lemma F_6c128 : fetch_word Plain.M.loaded_segments (0x6c168 : word) = Some W_6c128.
Proof. vm_refl. Qed.
Lemma D_6c128 : decode_any W_6c128 = Some (Op ALU_XOR 11 14 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c12c : bv 32 := 0xfea610e3.
Lemma F_6c12c : fetch_word Plain.M.loaded_segments (0x6c16c : word) = Some W_6c12c.
Proof. vm_refl. Qed.
Lemma D_6c12c : decode_any W_6c12c = Some (Branch BC_NE 12 10 8160, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c130 : bv 32 := 0x00058513.
Lemma F_6c130 : fetch_word Plain.M.loaded_segments (0x6c170 : word) = Some W_6c130.
Proof. vm_refl. Qed.
Lemma D_6c130 : decode_any W_6c130 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c134 : bv 32 := 0x00813083.
Lemma F_6c134 : fetch_word Plain.M.loaded_segments (0x6c174 : word) = Some W_6c134.
Proof. vm_refl. Qed.
Lemma D_6c134 : decode_any W_6c134 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c138 : bv 32 := 0x01010113.
Lemma F_6c138 : fetch_word Plain.M.loaded_segments (0x6c178 : word) = Some W_6c138.
Proof. vm_refl. Qed.
Lemma D_6c138 : decode_any W_6c138 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c13c : bv 32 := 0x00008067.
Lemma F_6c13c : fetch_word Plain.M.loaded_segments (0x6c17c : word) = Some W_6c13c.
Proof. vm_refl. Qed.
Lemma D_6c13c : decode_any W_6c13c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
End S1_code_6c040_6c160.

Module S1_code_6c160_6c3e0.

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_6c160 : bv 32 := 0xfd010113.
Lemma F_6c160 : fetch_word Plain.M.loaded_segments (0x6c1a0 : word) = Some W_6c160.
Proof. vm_refl. Qed.
Lemma D_6c160 : decode_any W_6c160 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c164 : bv 32 := 0x02113423.
Lemma F_6c164 : fetch_word Plain.M.loaded_segments (0x6c1a4 : word) = Some W_6c164.
Proof. vm_refl. Qed.
Lemma D_6c164 : decode_any W_6c164 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c168 : bv 32 := 0x02813023.
Lemma F_6c168 : fetch_word Plain.M.loaded_segments (0x6c1a8 : word) = Some W_6c168.
Proof. vm_refl. Qed.
Lemma D_6c168 : decode_any W_6c168 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c16c : bv 32 := 0x00913c23.
Lemma F_6c16c : fetch_word Plain.M.loaded_segments (0x6c1ac : word) = Some W_6c16c.
Proof. vm_refl. Qed.
Lemma D_6c16c : decode_any W_6c16c = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c170 : bv 32 := 0x01213823.
Lemma F_6c170 : fetch_word Plain.M.loaded_segments (0x6c1b0 : word) = Some W_6c170.
Proof. vm_refl. Qed.
Lemma D_6c170 : decode_any W_6c170 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c174 : bv 32 := 0x00050413.
Lemma F_6c174 : fetch_word Plain.M.loaded_segments (0x6c1b4 : word) = Some W_6c174.
Proof. vm_refl. Qed.
Lemma D_6c174 : decode_any W_6c174 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c178 : bv 32 := 0x01a00913.
Lemma F_6c178 : fetch_word Plain.M.loaded_segments (0x6c1b8 : word) = Some W_6c178.
Proof. vm_refl. Qed.
Lemma D_6c178 : decode_any W_6c178 = Some (OpImm ALU_ADD 18 0 26, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c17c : bv 32 := 0x00012423.
Lemma F_6c17c : fetch_word Plain.M.loaded_segments (0x6c1bc : word) = Some W_6c17c.
Proof. vm_refl. Qed.
Lemma D_6c17c : decode_any W_6c17c = Some (Store SZ4 2 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c180 : bv 32 := 0x01212623.
Lemma F_6c180 : fetch_word Plain.M.loaded_segments (0x6c1c0 : word) = Some W_6c180.
Proof. vm_refl. Qed.
Lemma D_6c180 : decode_any W_6c180 = Some (Store SZ4 2 18 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c184 : bv 32 := 0x00810513.
Lemma F_6c184 : fetch_word Plain.M.loaded_segments (0x6c1c4 : word) = Some W_6c184.
Proof. vm_refl. Qed.
Lemma D_6c184 : decode_any W_6c184 = Some (OpImm ALU_ADD 10 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c188 : bv 32 := 0x00810613.
Lemma F_6c188 : fetch_word Plain.M.loaded_segments (0x6c1c8 : word) = Some W_6c188.
Proof. vm_refl. Qed.
Lemma D_6c188 : decode_any W_6c188 = Some (OpImm ALU_ADD 12 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c18c : bv 32 := 0x00040593.
Lemma F_6c18c : fetch_word Plain.M.loaded_segments (0x6c1cc : word) = Some W_6c18c.
Proof. vm_refl. Qed.
Lemma D_6c18c : decode_any W_6c18c = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c190 : bv 32 := 0x02c000ef.
Lemma F_6c190 : fetch_word Plain.M.loaded_segments (0x6c1d0 : word) = Some W_6c190.
Proof. vm_refl. Qed.
Lemma D_6c190 : decode_any W_6c190 = Some (Jal 1 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c194 : bv 32 := 0x00050493.
Lemma F_6c194 : fetch_word Plain.M.loaded_segments (0x6c1d4 : word) = Some W_6c194.
Proof. vm_refl. Qed.
Lemma D_6c194 : decode_any W_6c194 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c198 : bv 32 := 0xf7cff0ef.
Lemma F_6c198 : fetch_word Plain.M.loaded_segments (0x6c1d8 : word) = Some W_6c198.
Proof. vm_refl. Qed.
Lemma D_6c198 : decode_any W_6c198 = Some (Jal 1 2094972, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c19c : bv 32 := 0xfe0500e3.
Lemma F_6c19c : fetch_word Plain.M.loaded_segments (0x6c1dc : word) = Some W_6c19c.
Proof. vm_refl. Qed.
Lemma D_6c19c : decode_any W_6c19c = Some (Branch BC_EQ 10 0 8160, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c1a0 : bv 32 := 0x00048513.
Lemma F_6c1a0 : fetch_word Plain.M.loaded_segments (0x6c1e0 : word) = Some W_6c1a0.
Proof. vm_refl. Qed.
Lemma D_6c1a0 : decode_any W_6c1a0 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c1a4 : bv 32 := 0x02813083.
Lemma F_6c1a4 : fetch_word Plain.M.loaded_segments (0x6c1e4 : word) = Some W_6c1a4.
Proof. vm_refl. Qed.
Lemma D_6c1a4 : decode_any W_6c1a4 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c1a8 : bv 32 := 0x02013403.
Lemma F_6c1a8 : fetch_word Plain.M.loaded_segments (0x6c1e8 : word) = Some W_6c1a8.
Proof. vm_refl. Qed.
Lemma D_6c1a8 : decode_any W_6c1a8 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c1ac : bv 32 := 0x01813483.
Lemma F_6c1ac : fetch_word Plain.M.loaded_segments (0x6c1ec : word) = Some W_6c1ac.
Proof. vm_refl. Qed.
Lemma D_6c1ac : decode_any W_6c1ac = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c1b0 : bv 32 := 0x01013903.
Lemma F_6c1b0 : fetch_word Plain.M.loaded_segments (0x6c1f0 : word) = Some W_6c1b0.
Proof. vm_refl. Qed.
Lemma D_6c1b0 : decode_any W_6c1b0 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c1b4 : bv 32 := 0x03010113.
Lemma F_6c1b4 : fetch_word Plain.M.loaded_segments (0x6c1f4 : word) = Some W_6c1b4.
Proof. vm_refl. Qed.
Lemma D_6c1b4 : decode_any W_6c1b4 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c1b8 : bv 32 := 0x00008067.
Lemma F_6c1b8 : fetch_word Plain.M.loaded_segments (0x6c1f8 : word) = Some W_6c1b8.
Proof. vm_refl. Qed.
Lemma D_6c1b8 : decode_any W_6c1b8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c1bc : bv 32 := 0xfd010113.
Lemma F_6c1bc : fetch_word Plain.M.loaded_segments (0x6c1fc : word) = Some W_6c1bc.
Proof. vm_refl. Qed.
Lemma D_6c1bc : decode_any W_6c1bc = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c1c0 : bv 32 := 0x02113423.
Lemma F_6c1c0 : fetch_word Plain.M.loaded_segments (0x6c200 : word) = Some W_6c1c0.
Proof. vm_refl. Qed.
Lemma D_6c1c0 : decode_any W_6c1c0 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c1c4 : bv 32 := 0x02813023.
Lemma F_6c1c4 : fetch_word Plain.M.loaded_segments (0x6c204 : word) = Some W_6c1c4.
Proof. vm_refl. Qed.
Lemma D_6c1c4 : decode_any W_6c1c4 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c1c8 : bv 32 := 0x00913c23.
Lemma F_6c1c8 : fetch_word Plain.M.loaded_segments (0x6c208 : word) = Some W_6c1c8.
Proof. vm_refl. Qed.
Lemma D_6c1c8 : decode_any W_6c1c8 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c1cc : bv 32 := 0x01213823.
Lemma F_6c1cc : fetch_word Plain.M.loaded_segments (0x6c20c : word) = Some W_6c1cc.
Proof. vm_refl. Qed.
Lemma D_6c1cc : decode_any W_6c1cc = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c1d0 : bv 32 := 0x01313423.
Lemma F_6c1d0 : fetch_word Plain.M.loaded_segments (0x6c210 : word) = Some W_6c1d0.
Proof. vm_refl. Qed.
Lemma D_6c1d0 : decode_any W_6c1d0 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c1d4 : bv 32 := 0x00060413.
Lemma F_6c1d4 : fetch_word Plain.M.loaded_segments (0x6c214 : word) = Some W_6c1d4.
Proof. vm_refl. Qed.
Lemma D_6c1d4 : decode_any W_6c1d4 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c1d8 : bv 32 := 0x00062603.
Lemma F_6c1d8 : fetch_word Plain.M.loaded_segments (0x6c218 : word) = Some W_6c1d8.
Proof. vm_refl. Qed.
Lemma D_6c1d8 : decode_any W_6c1d8 = Some (Load SZ4 true 12 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c1dc : bv 32 := 0x00442503.
Lemma F_6c1dc : fetch_word Plain.M.loaded_segments (0x6c21c : word) = Some W_6c1dc.
Proof. vm_refl. Qed.
Lemma D_6c1dc : decode_any W_6c1dc = Some (Load SZ4 true 10 8 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c1e0 : bv 32 := 0x0cc50e63.
Lemma F_6c1e0 : fetch_word Plain.M.loaded_segments (0x6c220 : word) = Some W_6c1e0.
Proof. vm_refl. Qed.
Lemma D_6c1e0 : decode_any W_6c1e0 = Some (Branch BC_EQ 10 12 220, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c1e4 : bv 32 := 0x00058493.
Lemma F_6c1e4 : fetch_word Plain.M.loaded_segments (0x6c224 : word) = Some W_6c1e4.
Proof. vm_refl. Qed.
Lemma D_6c1e4 : decode_any W_6c1e4 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c1e8 : bv 32 := 0x40c5053b.
Lemma F_6c1e8 : fetch_word Plain.M.loaded_segments (0x6c228 : word) = Some W_6c1e8.
Proof. vm_refl. Qed.
Lemma D_6c1e8 : decode_any W_6c1e8 = Some (Op32 ALU_SUB 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c1ec : bv 32 := 0x0015091b.
Lemma F_6c1ec : fetch_word Plain.M.loaded_segments (0x6c22c : word) = Some W_6c1ec.
Proof. vm_refl. Qed.
Lemma D_6c1ec : decode_any W_6c1ec = Some (OpImm32 18 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c1f0 : bv 32 := 0x0c090263.
Lemma F_6c1f0 : fetch_word Plain.M.loaded_segments (0x6c230 : word) = Some W_6c1f0.
Proof. vm_refl. Qed.
Lemma D_6c1f0 : decode_any W_6c1f0 = Some (Branch BC_EQ 18 0 196, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c1f4 : bv 32 := 0x0019551b.
Lemma F_6c1f4 : fetch_word Plain.M.loaded_segments (0x6c234 : word) = Some W_6c1f4.
Proof. vm_refl. Qed.
Lemma D_6c1f4 : decode_any W_6c1f4 = Some (ShiftImm32 ALU_SRL 10 18 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c1f8 : bv 32 := 0x555555b7.
Lemma F_6c1f8 : fetch_word Plain.M.loaded_segments (0x6c238 : word) = Some W_6c1f8.
Proof. vm_refl. Qed.
Lemma D_6c1f8 : decode_any W_6c1f8 = Some (Lui 11 349525, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c1fc : bv 32 := 0x00a96533.
Lemma F_6c1fc : fetch_word Plain.M.loaded_segments (0x6c23c : word) = Some W_6c1fc.
Proof. vm_refl. Qed.
Lemma D_6c1fc : decode_any W_6c1fc = Some (Op ALU_OR 10 18 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c200 : bv 32 := 0x5555859b.
Lemma F_6c200 : fetch_word Plain.M.loaded_segments (0x6c240 : word) = Some W_6c200.
Proof. vm_refl. Qed.
Lemma D_6c200 : decode_any W_6c200 = Some (OpImm32 11 11 1365, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c204 : bv 32 := 0x0025561b.
Lemma F_6c204 : fetch_word Plain.M.loaded_segments (0x6c244 : word) = Some W_6c204.
Proof. vm_refl. Qed.
Lemma D_6c204 : decode_any W_6c204 = Some (ShiftImm32 ALU_SRL 12 10 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c208 : bv 32 := 0x00c56533.
Lemma F_6c208 : fetch_word Plain.M.loaded_segments (0x6c248 : word) = Some W_6c208.
Proof. vm_refl. Qed.
Lemma D_6c208 : decode_any W_6c208 = Some (Op ALU_OR 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c20c : bv 32 := 0x0045561b.
Lemma F_6c20c : fetch_word Plain.M.loaded_segments (0x6c24c : word) = Some W_6c20c.
Proof. vm_refl. Qed.
Lemma D_6c20c : decode_any W_6c20c = Some (ShiftImm32 ALU_SRL 12 10 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c210 : bv 32 := 0x00c56533.
Lemma F_6c210 : fetch_word Plain.M.loaded_segments (0x6c250 : word) = Some W_6c210.
Proof. vm_refl. Qed.
Lemma D_6c210 : decode_any W_6c210 = Some (Op ALU_OR 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c214 : bv 32 := 0x0085561b.
Lemma F_6c214 : fetch_word Plain.M.loaded_segments (0x6c254 : word) = Some W_6c214.
Proof. vm_refl. Qed.
Lemma D_6c214 : decode_any W_6c214 = Some (ShiftImm32 ALU_SRL 12 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c218 : bv 32 := 0x00c56533.
Lemma F_6c218 : fetch_word Plain.M.loaded_segments (0x6c258 : word) = Some W_6c218.
Proof. vm_refl. Qed.
Lemma D_6c218 : decode_any W_6c218 = Some (Op ALU_OR 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c21c : bv 32 := 0x0105561b.
Lemma F_6c21c : fetch_word Plain.M.loaded_segments (0x6c25c : word) = Some W_6c21c.
Proof. vm_refl. Qed.
Lemma D_6c21c : decode_any W_6c21c = Some (ShiftImm32 ALU_SRL 12 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c220 : bv 32 := 0x00c56533.
Lemma F_6c220 : fetch_word Plain.M.loaded_segments (0x6c260 : word) = Some W_6c220.
Proof. vm_refl. Qed.
Lemma D_6c220 : decode_any W_6c220 = Some (Op ALU_OR 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c224 : bv 32 := 0xfff54513.
Lemma F_6c224 : fetch_word Plain.M.loaded_segments (0x6c264 : word) = Some W_6c224.
Proof. vm_refl. Qed.
Lemma D_6c224 : decode_any W_6c224 = Some (OpImm ALU_XOR 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c228 : bv 32 := 0x00155613.
Lemma F_6c228 : fetch_word Plain.M.loaded_segments (0x6c268 : word) = Some W_6c228.
Proof. vm_refl. Qed.
Lemma D_6c228 : decode_any W_6c228 = Some (ShiftImm ALU_SRL 12 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c22c : bv 32 := 0x00b675b3.
Lemma F_6c22c : fetch_word Plain.M.loaded_segments (0x6c26c : word) = Some W_6c22c.
Proof. vm_refl. Qed.
Lemma D_6c22c : decode_any W_6c22c = Some (Op ALU_AND 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c230 : bv 32 := 0x33333637.
Lemma F_6c230 : fetch_word Plain.M.loaded_segments (0x6c270 : word) = Some W_6c230.
Proof. vm_refl. Qed.
Lemma D_6c230 : decode_any W_6c230 = Some (Lui 12 209715, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c234 : bv 32 := 0x3336061b.
Lemma F_6c234 : fetch_word Plain.M.loaded_segments (0x6c274 : word) = Some W_6c234.
Proof. vm_refl. Qed.
Lemma D_6c234 : decode_any W_6c234 = Some (OpImm32 12 12 819, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c238 : bv 32 := 0x40b50533.
Lemma F_6c238 : fetch_word Plain.M.loaded_segments (0x6c278 : word) = Some W_6c238.
Proof. vm_refl. Qed.
Lemma D_6c238 : decode_any W_6c238 = Some (Op ALU_SUB 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c23c : bv 32 := 0x00c575b3.
Lemma F_6c23c : fetch_word Plain.M.loaded_segments (0x6c27c : word) = Some W_6c23c.
Proof. vm_refl. Qed.
Lemma D_6c23c : decode_any W_6c23c = Some (Op ALU_AND 11 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c240 : bv 32 := 0x00255513.
Lemma F_6c240 : fetch_word Plain.M.loaded_segments (0x6c280 : word) = Some W_6c240.
Proof. vm_refl. Qed.
Lemma D_6c240 : decode_any W_6c240 = Some (ShiftImm ALU_SRL 10 10 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c244 : bv 32 := 0x00c57533.
Lemma F_6c244 : fetch_word Plain.M.loaded_segments (0x6c284 : word) = Some W_6c244.
Proof. vm_refl. Qed.
Lemma D_6c244 : decode_any W_6c244 = Some (Op ALU_AND 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c248 : bv 32 := 0x0f0f1637.
Lemma F_6c248 : fetch_word Plain.M.loaded_segments (0x6c288 : word) = Some W_6c248.
Proof. vm_refl. Qed.
Lemma D_6c248 : decode_any W_6c248 = Some (Lui 12 61681, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c24c : bv 32 := 0x00a58533.
Lemma F_6c24c : fetch_word Plain.M.loaded_segments (0x6c28c : word) = Some W_6c24c.
Proof. vm_refl. Qed.
Lemma D_6c24c : decode_any W_6c24c = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c250 : bv 32 := 0x00455593.
Lemma F_6c250 : fetch_word Plain.M.loaded_segments (0x6c290 : word) = Some W_6c250.
Proof. vm_refl. Qed.
Lemma D_6c250 : decode_any W_6c250 = Some (ShiftImm ALU_SRL 11 10 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c254 : bv 32 := 0x00b50533.
Lemma F_6c254 : fetch_word Plain.M.loaded_segments (0x6c294 : word) = Some W_6c254.
Proof. vm_refl. Qed.
Lemma D_6c254 : decode_any W_6c254 = Some (Op ALU_ADD 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c258 : bv 32 := 0x010105b7.
Lemma F_6c258 : fetch_word Plain.M.loaded_segments (0x6c298 : word) = Some W_6c258.
Proof. vm_refl. Qed.
Lemma D_6c258 : decode_any W_6c258 = Some (Lui 11 4112, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c25c : bv 32 := 0xf0f60613.
Lemma F_6c25c : fetch_word Plain.M.loaded_segments (0x6c29c : word) = Some W_6c25c.
Proof. vm_refl. Qed.
Lemma D_6c25c : decode_any W_6c25c = Some (OpImm ALU_ADD 12 12 3855, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c260 : bv 32 := 0x10158593.
Lemma F_6c260 : fetch_word Plain.M.loaded_segments (0x6c2a0 : word) = Some W_6c260.
Proof. vm_refl. Qed.
Lemma D_6c260 : decode_any W_6c260 = Some (OpImm ALU_ADD 11 11 257, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c264 : bv 32 := 0x00c57533.
Lemma F_6c264 : fetch_word Plain.M.loaded_segments (0x6c2a4 : word) = Some W_6c264.
Proof. vm_refl. Qed.
Lemma D_6c264 : decode_any W_6c264 = Some (Op ALU_AND 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c268 : bv 32 := 0x02b50533.
Lemma F_6c268 : fetch_word Plain.M.loaded_segments (0x6c2a8 : word) = Some W_6c268.
Proof. vm_refl. Qed.
Lemma D_6c268 : decode_any W_6c268 = Some (Mul M_MUL 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c26c : bv 32 := 0x0185551b.
Lemma F_6c26c : fetch_word Plain.M.loaded_segments (0x6c2ac : word) = Some W_6c26c.
Proof. vm_refl. Qed.
Lemma D_6c26c : decode_any W_6c26c = Some (ShiftImm32 ALU_SRL 10 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c270 : bv 32 := 0x00a915bb.
Lemma F_6c270 : fetch_word Plain.M.loaded_segments (0x6c2b0 : word) = Some W_6c270.
Proof. vm_refl. Qed.
Lemma D_6c270 : decode_any W_6c270 = Some (Op32 ALU_SLL 11 18 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c274 : bv 32 := 0x04056513.
Lemma F_6c274 : fetch_word Plain.M.loaded_segments (0x6c2b4 : word) = Some W_6c274.
Proof. vm_refl. Qed.
Lemma D_6c274 : decode_any W_6c274 = Some (OpImm ALU_OR 10 10 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c278 : bv 32 := 0x02159593.
Lemma F_6c278 : fetch_word Plain.M.loaded_segments (0x6c2b8 : word) = Some W_6c278.
Proof. vm_refl. Qed.
Lemma D_6c278 : decode_any W_6c278 = Some (ShiftImm ALU_SLL 11 11 33, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c27c : bv 32 := 0x0215d593.
Lemma F_6c27c : fetch_word Plain.M.loaded_segments (0x6c2bc : word) = Some W_6c27c.
Proof. vm_refl. Qed.
Lemma D_6c27c : decode_any W_6c27c = Some (ShiftImm ALU_SRL 11 11 33, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c280 : bv 32 := 0x0015b593.
Lemma F_6c280 : fetch_word Plain.M.loaded_segments (0x6c2c0 : word) = Some W_6c280.
Proof. vm_refl. Qed.
Lemma D_6c280 : decode_any W_6c280 = Some (OpImm ALU_SLTU 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c284 : bv 32 := 0x00b50533.
Lemma F_6c284 : fetch_word Plain.M.loaded_segments (0x6c2c4 : word) = Some W_6c284.
Proof. vm_refl. Qed.
Lemma D_6c284 : decode_any W_6c284 = Some (Op ALU_ADD 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c288 : bv 32 := 0xfe050513.
Lemma F_6c288 : fetch_word Plain.M.loaded_segments (0x6c2c8 : word) = Some W_6c288.
Proof. vm_refl. Qed.
Lemma D_6c288 : decode_any W_6c288 = Some (OpImm ALU_ADD 10 10 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c28c : bv 32 := 0xfff00593.
Lemma F_6c28c : fetch_word Plain.M.loaded_segments (0x6c2cc : word) = Some W_6c28c.
Proof. vm_refl. Qed.
Lemma D_6c28c : decode_any W_6c28c = Some (OpImm ALU_ADD 11 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c290 : bv 32 := 0x00a5d9b3.
Lemma F_6c290 : fetch_word Plain.M.loaded_segments (0x6c2d0 : word) = Some W_6c290.
Proof. vm_refl. Qed.
Lemma D_6c290 : decode_any W_6c290 = Some (Op ALU_SRL 19 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c294 : bv 32 := 0x00048513.
Lemma F_6c294 : fetch_word Plain.M.loaded_segments (0x6c2d4 : word) = Some W_6c294.
Proof. vm_refl. Qed.
Lemma D_6c294 : decode_any W_6c294 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c298 : bv 32 := 0x044000ef.
Lemma F_6c298 : fetch_word Plain.M.loaded_segments (0x6c2d8 : word) = Some W_6c298.
Proof. vm_refl. Qed.
Lemma D_6c298 : decode_any W_6c298 = Some (Jal 1 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c29c : bv 32 := 0x01357533.
Lemma F_6c29c : fetch_word Plain.M.loaded_segments (0x6c2dc : word) = Some W_6c29c.
Proof. vm_refl. Qed.
Lemma D_6c29c : decode_any W_6c29c = Some (Op ALU_AND 10 10 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c2a0 : bv 32 := 0x0005059b.
Lemma F_6c2a0 : fetch_word Plain.M.loaded_segments (0x6c2e0 : word) = Some W_6c2a0.
Proof. vm_refl. Qed.
Lemma D_6c2a0 : decode_any W_6c2a0 = Some (OpImm32 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c2a4 : bv 32 := 0xff25f8e3.
Lemma F_6c2a4 : fetch_word Plain.M.loaded_segments (0x6c2e4 : word) = Some W_6c2a4.
Proof. vm_refl. Qed.
Lemma D_6c2a4 : decode_any W_6c2a4 = Some (Branch BC_GEU 11 18 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c2a8 : bv 32 := 0x00042583.
Lemma F_6c2a8 : fetch_word Plain.M.loaded_segments (0x6c2e8 : word) = Some W_6c2a8.
Proof. vm_refl. Qed.
Lemma D_6c2a8 : decode_any W_6c2a8 = Some (Load SZ4 true 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c2ac : bv 32 := 0x00a58533.
Lemma F_6c2ac : fetch_word Plain.M.loaded_segments (0x6c2ec : word) = Some W_6c2ac.
Proof. vm_refl. Qed.
Lemma D_6c2ac : decode_any W_6c2ac = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c2b0 : bv 32 := 0x00c0006f.
Lemma F_6c2b0 : fetch_word Plain.M.loaded_segments (0x6c2f0 : word) = Some W_6c2b0.
Proof. vm_refl. Qed.
Lemma D_6c2b0 : decode_any W_6c2b0 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c2bc : bv 32 := 0x0005051b.
Lemma F_6c2bc : fetch_word Plain.M.loaded_segments (0x6c2fc : word) = Some W_6c2bc.
Proof. vm_refl. Qed.
Lemma D_6c2bc : decode_any W_6c2bc = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c2c0 : bv 32 := 0x02813083.
Lemma F_6c2c0 : fetch_word Plain.M.loaded_segments (0x6c300 : word) = Some W_6c2c0.
Proof. vm_refl. Qed.
Lemma D_6c2c0 : decode_any W_6c2c0 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c2c4 : bv 32 := 0x02013403.
Lemma F_6c2c4 : fetch_word Plain.M.loaded_segments (0x6c304 : word) = Some W_6c2c4.
Proof. vm_refl. Qed.
Lemma D_6c2c4 : decode_any W_6c2c4 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c2c8 : bv 32 := 0x01813483.
Lemma F_6c2c8 : fetch_word Plain.M.loaded_segments (0x6c308 : word) = Some W_6c2c8.
Proof. vm_refl. Qed.
Lemma D_6c2c8 : decode_any W_6c2c8 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c2cc : bv 32 := 0x01013903.
Lemma F_6c2cc : fetch_word Plain.M.loaded_segments (0x6c30c : word) = Some W_6c2cc.
Proof. vm_refl. Qed.
Lemma D_6c2cc : decode_any W_6c2cc = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c2d0 : bv 32 := 0x00813983.
Lemma F_6c2d0 : fetch_word Plain.M.loaded_segments (0x6c310 : word) = Some W_6c2d0.
Proof. vm_refl. Qed.
Lemma D_6c2d0 : decode_any W_6c2d0 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c2d4 : bv 32 := 0x03010113.
Lemma F_6c2d4 : fetch_word Plain.M.loaded_segments (0x6c314 : word) = Some W_6c2d4.
Proof. vm_refl. Qed.
Lemma D_6c2d4 : decode_any W_6c2d4 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c2d8 : bv 32 := 0x00008067.
Lemma F_6c2d8 : fetch_word Plain.M.loaded_segments (0x6c318 : word) = Some W_6c2d8.
Proof. vm_refl. Qed.
Lemma D_6c2d8 : decode_any W_6c2d8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c2dc : bv 32 := 0x7ff50593.
Lemma F_6c2dc : fetch_word Plain.M.loaded_segments (0x6c31c : word) = Some W_6c2dc.
Proof. vm_refl. Qed.
Lemma D_6c2dc : decode_any W_6c2dc = Some (OpImm ALU_ADD 11 10 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c2e0 : bv 32 := 0xfffa8617.
Lemma F_6c2e0 : fetch_word Plain.M.loaded_segments (0x6c320 : word) = Some W_6c2e0.
Proof. vm_refl. Qed.
Lemma D_6c2e0 : decode_any W_6c2e0 = Some (Auipc 12 1048488, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c2e4 : bv 32 := 0x1c15b683.
Lemma F_6c2e4 : fetch_word Plain.M.loaded_segments (0x6c324 : word) = Some W_6c2e4.
Proof. vm_refl. Qed.
Lemma D_6c2e4 : decode_any W_6c2e4 = Some (Load SZ8 true 13 11 449, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c2e8 : bv 32 := 0x13800713.
Lemma F_6c2e8 : fetch_word Plain.M.loaded_segments (0x6c328 : word) = Some W_6c2e8.
Proof. vm_refl. Qed.
Lemma D_6c2e8 : decode_any W_6c2e8 = Some (OpImm ALU_ADD 14 0 312, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c2ec : bv 32 := 0x800007b7.
Lemma F_6c2ec : fetch_word Plain.M.loaded_segments (0x6c32c : word) = Some W_6c2ec.
Proof. vm_refl. Qed.
Lemma D_6c2ec : decode_any W_6c2ec = Some (Lui 15 524288, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c2f0 : bv 32 := 0x62863603.
Lemma F_6c2f0 : fetch_word Plain.M.loaded_segments (0x6c330 : word) = Some W_6c2f0.
Proof. vm_refl. Qed.
Lemma D_6c2f0 : decode_any W_6c2f0 = Some (Load SZ8 true 12 12 1576, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c2f4 : bv 32 := 0x00168813.
Lemma F_6c2f4 : fetch_word Plain.M.loaded_segments (0x6c334 : word) = Some W_6c2f4.
Proof. vm_refl. Qed.
Lemma D_6c2f4 : decode_any W_6c2f4 = Some (OpImm ALU_ADD 16 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c2f8 : bv 32 := 0x09c68893.
Lemma F_6c2f8 : fetch_word Plain.M.loaded_segments (0x6c338 : word) = Some W_6c2f8.
Proof. vm_refl. Qed.
Lemma D_6c2f8 : decode_any W_6c2f8 = Some (OpImm ALU_ADD 17 13 156, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c2fc : bv 32 := 0x00385293.
Lemma F_6c2fc : fetch_word Plain.M.loaded_segments (0x6c33c : word) = Some W_6c2fc.
Proof. vm_refl. Qed.
Lemma D_6c2fc : decode_any W_6c2fc = Some (ShiftImm ALU_SRL 5 16 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c300 : bv 32 := 0x0038d313.
Lemma F_6c300 : fetch_word Plain.M.loaded_segments (0x6c340 : word) = Some W_6c300.
Proof. vm_refl. Qed.
Lemma D_6c300 : decode_any W_6c300 = Some (ShiftImm ALU_SRL 6 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c304 : bv 32 := 0x02c2b2b3.
Lemma F_6c304 : fetch_word Plain.M.loaded_segments (0x6c344 : word) = Some W_6c304.
Proof. vm_refl. Qed.
Lemma D_6c304 : decode_any W_6c304 = Some (Mul M_MULHU 5 5 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c308 : bv 32 := 0x02c33633.
Lemma F_6c308 : fetch_word Plain.M.loaded_segments (0x6c348 : word) = Some W_6c308.
Proof. vm_refl. Qed.
Lemma D_6c308 : decode_any W_6c308 = Some (Mul M_MULHU 12 6 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c30c : bv 32 := 0xfffa8317.
Lemma F_6c30c : fetch_word Plain.M.loaded_segments (0x6c34c : word) = Some W_6c30c.
Proof. vm_refl. Qed.
Lemma D_6c30c : decode_any W_6c30c = Some (Auipc 6 1048488, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c310 : bv 32 := 0x0012d293.
Lemma F_6c310 : fetch_word Plain.M.loaded_segments (0x6c350 : word) = Some W_6c310.
Proof. vm_refl. Qed.
Lemma D_6c310 : decode_any W_6c310 = Some (ShiftImm ALU_SRL 5 5 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c314 : bv 32 := 0x00165613.
Lemma F_6c314 : fetch_word Plain.M.loaded_segments (0x6c354 : word) = Some W_6c314.
Proof. vm_refl. Qed.
Lemma D_6c314 : decode_any W_6c314 = Some (ShiftImm ALU_SRL 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c318 : bv 32 := 0x02e282b3.
Lemma F_6c318 : fetch_word Plain.M.loaded_segments (0x6c358 : word) = Some W_6c318.
Proof. vm_refl. Qed.
Lemma D_6c318 : decode_any W_6c318 = Some (Mul M_MUL 5 5 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c31c : bv 32 := 0x02e60633.
Lemma F_6c31c : fetch_word Plain.M.loaded_segments (0x6c35c : word) = Some W_6c31c.
Proof. vm_refl. Qed.
Lemma D_6c31c : decode_any W_6c31c = Some (Mul M_MUL 12 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c320 : bv 32 := 0x00555737.
Lemma F_6c320 : fetch_word Plain.M.loaded_segments (0x6c360 : word) = Some W_6c320.
Proof. vm_refl. Qed.
Lemma D_6c320 : decode_any W_6c320 = Some (Lui 14 1365, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c324 : bv 32 := 0x00369693.
Lemma F_6c324 : fetch_word Plain.M.loaded_segments (0x6c364 : word) = Some W_6c324.
Proof. vm_refl. Qed.
Lemma D_6c324 : decode_any W_6c324 = Some (ShiftImm ALU_SLL 13 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c328 : bv 32 := 0x00d506b3.
Lemma F_6c328 : fetch_word Plain.M.loaded_segments (0x6c368 : word) = Some W_6c328.
Proof. vm_refl. Qed.
Lemma D_6c328 : decode_any W_6c328 = Some (Op ALU_ADD 13 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c32c : bv 32 := 0x40580833.
Lemma F_6c32c : fetch_word Plain.M.loaded_segments (0x6c36c : word) = Some W_6c32c.
Proof. vm_refl. Qed.
Lemma D_6c32c : decode_any W_6c32c = Some (Op ALU_SUB 16 16 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c330 : bv 32 := 0x40c88633.
Lemma F_6c330 : fetch_word Plain.M.loaded_segments (0x6c370 : word) = Some W_6c330.
Proof. vm_refl. Qed.
Lemma D_6c330 : decode_any W_6c330 = Some (Op ALU_SUB 12 17 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c334 : bv 32 := 0x00381893.
Lemma F_6c334 : fetch_word Plain.M.loaded_segments (0x6c374 : word) = Some W_6c334.
Proof. vm_refl. Qed.
Lemma D_6c334 : decode_any W_6c334 = Some (ShiftImm ALU_SLL 17 16 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c338 : bv 32 := 0x00361613.
Lemma F_6c338 : fetch_word Plain.M.loaded_segments (0x6c378 : word) = Some W_6c338.
Proof. vm_refl. Qed.
Lemma D_6c338 : decode_any W_6c338 = Some (ShiftImm ALU_SLL 12 12 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c33c : bv 32 := 0x011508b3.
Lemma F_6c33c : fetch_word Plain.M.loaded_segments (0x6c37c : word) = Some W_6c33c.
Proof. vm_refl. Qed.
Lemma D_6c33c : decode_any W_6c33c = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c340 : bv 32 := 0x0006b283.
Lemma F_6c340 : fetch_word Plain.M.loaded_segments (0x6c380 : word) = Some W_6c340.
Proof. vm_refl. Qed.
Lemma D_6c340 : decode_any W_6c340 = Some (Load SZ8 true 5 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c344 : bv 32 := 0x00c50633.
Lemma F_6c344 : fetch_word Plain.M.loaded_segments (0x6c384 : word) = Some W_6c344.
Proof. vm_refl. Qed.
Lemma D_6c344 : decode_any W_6c344 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c348 : bv 32 := 0x0008b883.
Lemma F_6c348 : fetch_word Plain.M.loaded_segments (0x6c388 : word) = Some W_6c348.
Proof. vm_refl. Qed.
Lemma D_6c348 : decode_any W_6c348 = Some (Load SZ8 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c34c : bv 32 := 0x00063603.
Lemma F_6c34c : fetch_word Plain.M.loaded_segments (0x6c38c : word) = Some W_6c34c.
Proof. vm_refl. Qed.
Lemma D_6c34c : decode_any W_6c34c = Some (Load SZ8 true 12 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c350 : bv 32 := 0x00f2f2b3.
Lemma F_6c350 : fetch_word Plain.M.loaded_segments (0x6c390 : word) = Some W_6c350.
Proof. vm_refl. Qed.
Lemma D_6c350 : decode_any W_6c350 = Some (Op ALU_AND 5 5 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c354 : bv 32 := 0xffe7879b.
Lemma F_6c354 : fetch_word Plain.M.loaded_segments (0x6c394 : word) = Some W_6c354.
Proof. vm_refl. Qed.
Lemma D_6c354 : decode_any W_6c354 = Some (OpImm32 15 15 4094, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c358 : bv 32 := 0x6c433303.
Lemma F_6c358 : fetch_word Plain.M.loaded_segments (0x6c398 : word) = Some W_6c358.
Proof. vm_refl. Qed.
Lemma D_6c358 : decode_any W_6c358 = Some (Load SZ8 true 6 6 1732, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c35c : bv 32 := 0x00f8f7b3.
Lemma F_6c35c : fetch_word Plain.M.loaded_segments (0x6c39c : word) = Some W_6c35c.
Proof. vm_refl. Qed.
Lemma D_6c35c : decode_any W_6c35c = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c360 : bv 32 := 0x03f89893.
Lemma F_6c360 : fetch_word Plain.M.loaded_segments (0x6c3a0 : word) = Some W_6c360.
Proof. vm_refl. Qed.
Lemma D_6c360 : decode_any W_6c360 = Some (ShiftImm ALU_SLL 17 17 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c364 : bv 32 := 0x0057e7b3.
Lemma F_6c364 : fetch_word Plain.M.loaded_segments (0x6c3a4 : word) = Some W_6c364.
Proof. vm_refl. Qed.
Lemma D_6c364 : decode_any W_6c364 = Some (Op ALU_OR 15 15 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c368 : bv 32 := 0x43f8d893.
Lemma F_6c368 : fetch_word Plain.M.loaded_segments (0x6c3a8 : word) = Some W_6c368.
Proof. vm_refl. Qed.
Lemma D_6c368 : decode_any W_6c368 = Some (ShiftImm ALU_SRA 17 17 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c36c : bv 32 := 0x0017d793.
Lemma F_6c36c : fetch_word Plain.M.loaded_segments (0x6c3ac : word) = Some W_6c36c.
Proof. vm_refl. Qed.
Lemma D_6c36c : decode_any W_6c36c = Some (ShiftImm ALU_SRL 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c370 : bv 32 := 0x0068f8b3.
Lemma F_6c370 : fetch_word Plain.M.loaded_segments (0x6c3b0 : word) = Some W_6c370.
Proof. vm_refl. Qed.
Lemma D_6c370 : decode_any W_6c370 = Some (Op ALU_AND 17 17 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c374 : bv 32 := 0x00c8c633.
Lemma F_6c374 : fetch_word Plain.M.loaded_segments (0x6c3b4 : word) = Some W_6c374.
Proof. vm_refl. Qed.
Lemma D_6c374 : decode_any W_6c374 = Some (Op ALU_XOR 12 17 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c378 : bv 32 := 0x00f64633.
Lemma F_6c378 : fetch_word Plain.M.loaded_segments (0x6c3b8 : word) = Some W_6c378.
Proof. vm_refl. Qed.
Lemma D_6c378 : decode_any W_6c378 = Some (Op ALU_XOR 12 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c37c : bv 32 := 0x00c6b023.
Lemma F_6c37c : fetch_word Plain.M.loaded_segments (0x6c3bc : word) = Some W_6c37c.
Proof. vm_refl. Qed.
Lemma D_6c37c : decode_any W_6c37c = Some (Store SZ8 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c380 : bv 32 := 0x1c15b603.
Lemma F_6c380 : fetch_word Plain.M.loaded_segments (0x6c3c0 : word) = Some W_6c380.
Proof. vm_refl. Qed.
Lemma D_6c380 : decode_any W_6c380 = Some (Load SZ8 true 12 11 449, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c384 : bv 32 := 0xfffa8697.
Lemma F_6c384 : fetch_word Plain.M.loaded_segments (0x6c3c4 : word) = Some W_6c384.
Proof. vm_refl. Qed.
Lemma D_6c384 : decode_any W_6c384 = Some (Auipc 13 1048488, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c388 : bv 32 := 0xfbf777b7.
Lemma F_6c388 : fetch_word Plain.M.loaded_segments (0x6c3c8 : word) = Some W_6c388.
Proof. vm_refl. Qed.
Lemma D_6c388 : decode_any W_6c388 = Some (Lui 15 1032055, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c38c : bv 32 := 0x5557071b.
Lemma F_6c38c : fetch_word Plain.M.loaded_segments (0x6c3cc : word) = Some W_6c38c.
Proof. vm_refl. Qed.
Lemma D_6c38c : decode_any W_6c38c = Some (OpImm32 14 14 1365, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c390 : bv 32 := 0x00361613.
Lemma F_6c390 : fetch_word Plain.M.loaded_segments (0x6c3d0 : word) = Some W_6c390.
Proof. vm_refl. Qed.
Lemma D_6c390 : decode_any W_6c390 = Some (ShiftImm ALU_SLL 12 12 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c394 : bv 32 := 0x00c50533.
Lemma F_6c394 : fetch_word Plain.M.loaded_segments (0x6c3d4 : word) = Some W_6c394.
Proof. vm_refl. Qed.
Lemma D_6c394 : decode_any W_6c394 = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c398 : bv 32 := 0x00053503.
Lemma F_6c398 : fetch_word Plain.M.loaded_segments (0x6c3d8 : word) = Some W_6c398.
Proof. vm_refl. Qed.
Lemma D_6c398 : decode_any W_6c398 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c39c : bv 32 := 0x5bc6b603.
Lemma F_6c39c : fetch_word Plain.M.loaded_segments (0x6c3dc : word) = Some W_6c39c.
Proof. vm_refl. Qed.
Lemma D_6c39c : decode_any W_6c39c = Some (Load SZ8 true 12 13 1468, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c3a0 : bv 32 := 0x00c71713.
Lemma F_6c3a0 : fetch_word Plain.M.loaded_segments (0x6c3e0 : word) = Some W_6c3a0.
Proof. vm_refl. Qed.
Lemma D_6c3a0 : decode_any W_6c3a0 = Some (ShiftImm ALU_SLL 14 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c3a4 : bv 32 := 0x55570693.
Lemma F_6c3a4 : fetch_word Plain.M.loaded_segments (0x6c3e4 : word) = Some W_6c3a4.
Proof. vm_refl. Qed.
Lemma D_6c3a4 : decode_any W_6c3a4 = Some (OpImm ALU_ADD 13 14 1365, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c3a8 : bv 32 := 0x01d55713.
Lemma F_6c3a8 : fetch_word Plain.M.loaded_segments (0x6c3e8 : word) = Some W_6c3a8.
Proof. vm_refl. Qed.
Lemma D_6c3a8 : decode_any W_6c3a8 = Some (ShiftImm ALU_SRL 14 10 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c3ac : bv 32 := 0x00d776b3.
Lemma F_6c3ac : fetch_word Plain.M.loaded_segments (0x6c3ec : word) = Some W_6c3ac.
Proof. vm_refl. Qed.
Lemma D_6c3ac : decode_any W_6c3ac = Some (Op ALU_AND 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c3b0 : bv 32 := 0x00a6c533.
Lemma F_6c3b0 : fetch_word Plain.M.loaded_segments (0x6c3f0 : word) = Some W_6c3b0.
Proof. vm_refl. Qed.
Lemma D_6c3b0 : decode_any W_6c3b0 = Some (Op ALU_XOR 10 13 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c3b4 : bv 32 := 0x01151693.
Lemma F_6c3b4 : fetch_word Plain.M.loaded_segments (0x6c3f4 : word) = Some W_6c3b4.
Proof. vm_refl. Qed.
Lemma D_6c3b4 : decode_any W_6c3b4 = Some (ShiftImm ALU_SLL 13 10 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c3b8 : bv 32 := 0x00c6f633.
Lemma F_6c3b8 : fetch_word Plain.M.loaded_segments (0x6c3f8 : word) = Some W_6c3b8.
Proof. vm_refl. Qed.
Lemma D_6c3b8 : decode_any W_6c3b8 = Some (Op ALU_AND 12 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c3bc : bv 32 := 0x00a64533.
Lemma F_6c3bc : fetch_word Plain.M.loaded_segments (0x6c3fc : word) = Some W_6c3bc.
Proof. vm_refl. Qed.
Lemma D_6c3bc : decode_any W_6c3bc = Some (Op ALU_XOR 10 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c3c0 : bv 32 := 0x02551613.
Lemma F_6c3c0 : fetch_word Plain.M.loaded_segments (0x6c400 : word) = Some W_6c3c0.
Proof. vm_refl. Qed.
Lemma D_6c3c0 : decode_any W_6c3c0 = Some (ShiftImm ALU_SLL 12 10 37, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c3c4 : bv 32 := 0x01979793.
Lemma F_6c3c4 : fetch_word Plain.M.loaded_segments (0x6c404 : word) = Some W_6c3c4.
Proof. vm_refl. Qed.
Lemma D_6c3c4 : decode_any W_6c3c4 = Some (ShiftImm ALU_SLL 15 15 25, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c3c8 : bv 32 := 0x00f67633.
Lemma F_6c3c8 : fetch_word Plain.M.loaded_segments (0x6c408 : word) = Some W_6c3c8.
Proof. vm_refl. Qed.
Lemma D_6c3c8 : decode_any W_6c3c8 = Some (Op ALU_AND 12 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c3cc : bv 32 := 0x00a64533.
Lemma F_6c3cc : fetch_word Plain.M.loaded_segments (0x6c40c : word) = Some W_6c3cc.
Proof. vm_refl. Qed.
Lemma D_6c3cc : decode_any W_6c3cc = Some (Op ALU_XOR 10 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c3d0 : bv 32 := 0x02b55613.
Lemma F_6c3d0 : fetch_word Plain.M.loaded_segments (0x6c410 : word) = Some W_6c3d0.
Proof. vm_refl. Qed.
Lemma D_6c3d0 : decode_any W_6c3d0 = Some (ShiftImm ALU_SRL 12 10 43, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c3d4 : bv 32 := 0x00a64533.
Lemma F_6c3d4 : fetch_word Plain.M.loaded_segments (0x6c414 : word) = Some W_6c3d4.
Proof. vm_refl. Qed.
Lemma D_6c3d4 : decode_any W_6c3d4 = Some (Op ALU_XOR 10 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c3d8 : bv 32 := 0x1d05b0a3.
Lemma F_6c3d8 : fetch_word Plain.M.loaded_segments (0x6c418 : word) = Some W_6c3d8.
Proof. vm_refl. Qed.
Lemma D_6c3d8 : decode_any W_6c3d8 = Some (Store SZ8 11 16 449, 4%Z).
Proof. vm_refl. Qed.

Definition W_6c3dc : bv 32 := 0x00008067.
Lemma F_6c3dc : fetch_word Plain.M.loaded_segments (0x6c41c : word) = Some W_6c3dc.
Proof. vm_refl. Qed.
Lemma D_6c3dc : decode_any W_6c3dc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
End S1_code_6c160_6c3e0.

Module S1_code_6b914_6b92c.

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_6b914 : bv 32 := 0x01b53593.
Lemma F_6b914 : fetch_word Plain.M.loaded_segments (0x6b954 : word) = Some W_6b914.
Proof. vm_refl. Qed.
Lemma D_6b914 : decode_any W_6b914 = Some (OpImm ALU_SLTU 11 10 27, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b918 : bv 32 := 0x07f80637.
Lemma F_6b918 : fetch_word Plain.M.loaded_segments (0x6b958 : word) = Some W_6b918.
Proof. vm_refl. Qed.
Lemma D_6b918 : decode_any W_6b918 = Some (Lui 12 32640, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b91c : bv 32 := 0xfff6061b.
Lemma F_6b91c : fetch_word Plain.M.loaded_segments (0x6b95c : word) = Some W_6b91c.
Proof. vm_refl. Qed.
Lemma D_6b91c : decode_any W_6b91c = Some (OpImm32 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b920 : bv 32 := 0x00a65533.
Lemma F_6b920 : fetch_word Plain.M.loaded_segments (0x6b960 : word) = Some W_6b920.
Proof. vm_refl. Qed.
Lemma D_6b920 : decode_any W_6b920 = Some (Op ALU_SRL 10 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b924 : bv 32 := 0x00a5f533.
Lemma F_6b924 : fetch_word Plain.M.loaded_segments (0x6b964 : word) = Some W_6b924.
Proof. vm_refl. Qed.
Lemma D_6b924 : decode_any W_6b924 = Some (Op ALU_AND 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b928 : bv 32 := 0x00008067.
Lemma F_6b928 : fetch_word Plain.M.loaded_segments (0x6b968 : word) = Some W_6b928.
Proof. vm_refl. Qed.
Lemma D_6b928 : decode_any W_6b928 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
End S1_code_6b914_6b92c.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac WalkTac StartupTac SumWalkTac StoreOk MemSplit Hoare ShapeAlg
  SRealizes RefMemcpyLib RefReadLib LibIface LibEff MmapSim LibMaskBits S1Layout.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContLib StrLib ContStmts S1Facts.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.Lib_RG.S1_code_6c040_6c160. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.Lib_RG.S1_code_6c160_6c3e0. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.Lib_RG.S1_code_6b914_6b92c.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation SEGS := Plain.M.loaded_segments.

Ltac rdn_fix H :=
  first [ exact H
        | lazymatch goal with |- rdn _ _ (Z_to_bv 64 ?a) _ = _ =>
            lazymatch type of H with rdn _ _ (Z_to_bv 64 ?a') _ = _ =>
              replace a with a' by lia; exact H end end ].
Ltac b2z8 := apply bytes_le_to_Z_8.
Ltac close_pc := lazymatch goal with |- msteps _ ?a ?bb => replace bb with a; [apply mst_refl|] end; f_equal; apply bv_eq; vm_compute; reflexivity.

Ltac wl := lazymatch goal with |- msteps _ (mkst (regupd _ _ ?v) _ _ _) _ => wlit v | |- _ => idtac end.
Ltac snl F D := stepn F D; pin; wl.

Definition K_MTF : Z := 0x14978.
Lemma img_K_MTF : rdn SEGS (fun _ => None) (Z_to_bv 64 K_MTF) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 MT_F)).
Proof. vm_refl_bv. Qed.

Lemma Z_to_bv_mod64 : forall z, Z_to_bv 64 z = Z_to_bv 64 (z mod 2 ^ 64).
Proof. intros z. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod, Z.mod_mod by lia. reflexivity. Qed.
Lemma v_add_wrap : forall a b, v_add (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof.
  intros a b. unfold v_add. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod, <- Zplus_mod. reflexivity.
Qed.
Lemma v_mul_wrap : forall a b, v_mul (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a * b).
Proof.
  intros a b. unfold v_mul. apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod, <- Zmult_mod. reflexivity.
Qed.
Lemma v_xor_Z : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> v_xor (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (Z.lxor a b).
Proof. intros a b Ha Hb. unfold v_xor. rewrite !u64_of_Z by lia. reflexivity. Qed.

Definition mt_next (x i : Z) : Z := (Z.lxor x (x / 2 ^ 62) * MT_F + i) mod 2 ^ 64.

Lemma mt_seq_step : forall k x i (j : nat), (S j < k)%nat ->
  nth (S j) (mt_seq x i k) 0 = mt_next (nth j (mt_seq x i k) 0) (i + Z.of_nat j).
Proof.
  induction k as [|k IH]; intros x i j Hj; [lia|].
  cbn [mt_seq]. destruct j as [|j].
  - destruct k; [lia|]. cbn [nth mt_seq]. unfold mt_next. rewrite Z.add_0_r. reflexivity.
  - cbn [nth]. rewrite IH by lia. f_equal. lia.
Qed.

Lemma mt_init_0 : Znth 0 mt_init = 5489.
Proof. reflexivity. Qed.

Lemma mt_init_step : forall j, 0 <= j -> j + 1 < 312 -> Znth (j + 1) mt_init = mt_next (Znth j mt_init) (j + 1).
Proof.
  intros j Hj Hj1. unfold Znth, mt_init. replace (Z.to_nat (j + 1)) with (S (Z.to_nat j)) by lia.
  rewrite (mt_seq_step 312) by lia. f_equal. lia.
Qed.

Lemma mt_init_range : forall j, 0 <= j < 312 -> 0 <= Znth j mt_init < 2 ^ 64.
Proof.
  intros j Hj. destruct (Z.eq_dec j 0) as [->|Hne]; [rewrite mt_init_0; lia|].
  replace j with (j - 1 + 1) by lia. rewrite mt_init_step by lia. unfold mt_next. apply Z.mod_pos_bound. lia.
Qed.

Lemma step_xor_at {fx : FPState} : forall segs regs pc mem rom w rd rs1 rs2 v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op ALU_XOR rd rs1 rs2, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_xor (getr regs rs1) (getr regs rs2) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs1 rs2 v Hf He Hd Hrd Hv.
  rewrite (step_xor segs regs pc mem rom w rd rs1 rs2 Hf He Hd). rewrite Hrd, Hv. reflexivity.
Qed.
Ltac stepxor F D vv tac :=
  chain_step;
  [ reflexivity
  | eapply step_xor_at with (v := vv); [ exact F | reflexivity | exact D | reflexivity | tac ]
  | step_simpl ].

Section RG.
  Context {fx : FPState}.
Context {AC : AllocCeiling}.

  Lemma SEED_BODY : forall (i obj : Z) R Mi,
    1 <= i <= 311 -> 0 <= obj -> obj + RG_SZ <= 2 ^ 63 -> mdef Mi obj RG_SZ ->
    getr R 13%bv = Z_to_bv 64 MT_F -> getr R 14%bv = Z_to_bv 64 (Znth (i - 1) mt_init) ->
    getr R 15%bv = Z_to_bv 64 (obj + 8 * i) -> getr R 16%bv = Z_to_bv 64 i ->
    exists R1,
      msteps SEGS (@mkst fx R (Z_to_bv 64 0x6c0a0) Mi (seg_rom SEGS))
                  (@mkst fx R1 (Z_to_bv 64 0x6c0bc) (wbytes Mi (Z_to_bv 64 (obj + 8 * i)) (word_to_le_bytes 8 (Z_to_bv 64 (Znth i mt_init)))) (seg_rom SEGS))
      /\ getr R1 13%bv = Z_to_bv 64 MT_F /\ getr R1 14%bv = Z_to_bv 64 (Znth i mt_init)
      /\ getr R1 15%bv = Z_to_bv 64 (obj + 8 * (i + 1)) /\ getr R1 16%bv = Z_to_bv 64 (i + 1)
      /\ (forall r, r <> 5%bv -> r <> 14%bv -> r <> 15%bv -> r <> 16%bv -> getr R1 r = getr R r).
  Proof using fx.
    intros i obj R Mi Hi Ho0 Ho1 HD H13 H14 H15 H16. unfold RG_SZ in *.
    set (x := Znth (i - 1) mt_init) in *.
    pose proof (mt_init_range (i - 1) ltac:(lia)) as Hx. fold x in Hx.
    assert (Hq : 0 <= x / 2 ^ 62 < 4) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    assert (HL : 0 <= Z.lxor (x / 2 ^ 62) x) by (apply Z.lxor_nonneg; lia).
    assert (Hxi : Z_to_bv 64 (Z.lxor (x / 2 ^ 62) x * MT_F + i) = Z_to_bv 64 (Znth i mt_init)).
    { replace i with (i - 1 + 1) at 2 by lia. rewrite mt_init_step by lia. unfold mt_next.
      rewrite <- Z_to_bv_mod64. rewrite Z.lxor_comm. replace (i - 1 + 1) with i by lia. reflexivity. }
    eexists. split.
    - norm_pc.
      stepiv F_6c060 D_6c060 (Z_to_bv 64 (x / 2 ^ 62)) ltac:(gres; pin; imm_norm; rewrite v_srli_Z by lia; reflexivity).
      stepxor F_6c064 D_6c064 (Z_to_bv 64 (Z.lxor (x / 2 ^ 62) x)) ltac:(gres; pin; rewrite v_xor_Z by lia; reflexivity).
      stepiv F_6c068 D_6c068 (Z_to_bv 64 (Z.lxor (x / 2 ^ 62) x * MT_F)) ltac:(gres; pin; apply v_mul_wrap).
      stepiv F_6c06c D_6c06c (Z_to_bv 64 (Znth i mt_init)) ltac:(gres; pin; rewrite v_add_wrap; exact Hxi).
      sv F_6c070 D_6c070 (Z_to_bv 64 (i + 1)).
      stw F_6c074 D_6c074 (Z_to_bv 64 (obj + 8 * i)) (Z_to_bv 64 (Znth i mt_init)) ltac:(ok_mdef HD).
      stepiv F_6c078 D_6c078 (Z_to_bv 64 (obj + 8 * (i + 1))) ltac:(gres; pin; imm_norm; rewrite v_addi_Z by lia; f_equal; lia).
      close_pc.
    - gres. repeat split; try reflexivity; try assumption.
      intros r H5 H14' H15' H16'. rewrite !getr_other by assumption. reflexivity.
  Qed.

  Lemma SEED : forall (k : nat) (i obj : Z) R (M Mi : mem),
    1 <= i -> i + Z.of_nat k = 311 -> 0 <= obj -> obj + RG_SZ <= 2 ^ 63 ->
    getr R 13%bv = Z_to_bv 64 MT_F -> getr R 14%bv = Z_to_bv 64 (Znth (i - 1) mt_init) ->
    getr R 15%bv = Z_to_bv 64 (obj + 8 * i) -> getr R 16%bv = Z_to_bv 64 i -> getr R 17%bv = Z_to_bv 64 312 ->
    mdef M obj RG_SZ -> stores_in (zwin obj (obj + RG_SZ)) M Mi ->
    (forall j, 0 <= j < i -> fld SEGS Mi (obj + 8 * j) 8 (Znth j mt_init)) ->
    exists R' M',
      msteps SEGS (@mkst fx R (Z_to_bv 64 0x6c0a0) Mi (seg_rom SEGS)) (@mkst fx R' (Z_to_bv 64 0x6c0c0) M' (seg_rom SEGS))
      /\ (forall r, r <> 5%bv -> r <> 14%bv -> r <> 15%bv -> r <> 16%bv -> getr R' r = getr R r)
      /\ stores_in (zwin obj (obj + RG_SZ)) M M'
      /\ (forall j, 0 <= j < 312 -> fld SEGS M' (obj + 8 * j) 8 (Znth j mt_init)).
  Proof using fx.
    induction k as [|k IH]; intros i obj R M Mi Hi Hk Ho0 Ho1 H13 H14 H15 H16 H17 HD SI FJ.
    - assert (Hi' : i = 311) by lia.
      destruct (SEED_BODY i obj R Mi ltac:(lia) Ho0 Ho1 ltac:(eapply stores_in_mdef; [exact SI|exact HD]) H13 H14 H15 H16)
        as (R1 & RUN & G13 & G14 & G15 & G16 & GS).
      eexists R1, _. split; [|split; [|split]].
      + eapply msteps_trans; [exact RUN|]. norm_pc.
        stepb_ft F_6c07c D_6c07c ltac:(rewrite G16, (GS 17%bv), H17 by (intros HH; inversion HH); rewrite Hi'; apply c_eq_refl).
        close_pc.
      + exact GS.
      + eapply stores_in_trans; [exact SI|]. apply stores_in_wbytes; rewrite ?length_N_to_le_bytes; unfold RG_SZ in *; cbn; try lia.
        intros a Ha. unfold zwin. lia.
      + intros j Hj. unfold fld. destruct (Z.eq_dec j i) as [->|Hne].
        * apply rdn_wbytes_hit8. rewrite u64_of_Z by (unfold RG_SZ in *; lia). unfold RG_SZ in *; lia.
        * rewrite rdn_wbytes_out_Z by (rewrite length_N_to_le_bytes; cbn; unfold RG_SZ in *; lia). apply FJ. lia.
    - destruct (SEED_BODY i obj R Mi ltac:(lia) Ho0 Ho1 ltac:(eapply stores_in_mdef; [exact SI|exact HD]) H13 H14 H15 H16)
        as (R1 & RUN & G13 & G14 & G15 & G16 & GS).
      destruct (IH (i + 1) obj R1 M (wbytes Mi (Z_to_bv 64 (obj + 8 * i)) (word_to_le_bytes 8 (Z_to_bv 64 (Znth i mt_init))))
                   ltac:(lia) ltac:(lia) Ho0 Ho1 G13 ltac:(replace (i + 1 - 1) with i by lia; exact G14) G15 G16
                   ltac:(rewrite (GS 17%bv) by (intros HH; inversion HH); exact H17) HD) as (R' & M' & RUN' & GS' & SI' & FJ').
      + eapply stores_in_trans; [exact SI|]. apply stores_in_wbytes; rewrite ?length_N_to_le_bytes; unfold RG_SZ in *; cbn; try lia.
        intros a Ha. unfold zwin. lia.
      + intros j Hj. unfold fld. destruct (Z.eq_dec j i) as [->|Hne].
        * apply rdn_wbytes_hit8. rewrite u64_of_Z by (unfold RG_SZ in *; lia). unfold RG_SZ in *; lia.
        * rewrite rdn_wbytes_out_Z by (rewrite length_N_to_le_bytes; cbn; unfold RG_SZ in *; lia). apply FJ. lia.
      + exists R', M'. split; [|split; [|split]].
        * eapply msteps_trans; [exact RUN|]. eapply msteps_trans; [|exact RUN']. norm_pc.
          stepb_tk F_6c07c D_6c07c ltac:(rewrite G16, (GS 17%bv), H17 by (intros HH; inversion HH); rewrite c_eq_Z' by lia; apply Z.eqb_neq; lia).
          close_pc.
        * intros r Ha Hb Hc Hd. rewrite (GS' r Ha Hb Hc Hd). apply GS; assumption.
        * exact SI'.
        * exact FJ'.
  Qed.

  Lemma HASH_BODY : forall (cur : Z) R M (b : byte),
    getr R 12%bv = Z_to_bv 64 cur -> 0 <= cur -> cur + 1 < 2 ^ 64 ->
    rdn SEGS M (Z_to_bv 64 cur) 1 = Some [b] ->
    exists R1,
      msteps SEGS (@mkst fx R (Z_to_bv 64 0x6c14c) M (seg_rom SEGS)) (@mkst fx R1 (Z_to_bv 64 0x6c16c) M (seg_rom SEGS))
      /\ getr R1 12%bv = Z_to_bv 64 (cur + 1) /\ getr R1 10%bv = getr R 10%bv
      /\ (forall r, r <> 11%bv -> r <> 12%bv -> r <> 14%bv -> r <> 15%bv -> r <> 16%bv -> getr R1 r = getr R r).
  Proof using fx.
    intros cur R M b H12 Hc0 Hc1 HB.
    eexists. split.
    - norm_pc.
      lb_step F_6c10c D_6c10c b ltac:(rdn_fix HB).
      sn F_6c110 D_6c110.
      sn F_6c114 D_6c114.
      sn F_6c118 D_6c118.
      sn F_6c11c D_6c11c.
      sn F_6c120 D_6c120.
      stepiv F_6c124 D_6c124 (Z_to_bv 64 (cur + 1)) ltac:(gres; pin; imm_norm; rewrite v_addi_Z by lia; reflexivity).
      sn F_6c128 D_6c128.
      close_pc.
    - gres. repeat split; try reflexivity.
      intros r Ha Hb Hc Hd He. rewrite !getr_other by assumption. reflexivity.
  Qed.

  Lemma HASH : forall (k : nat) (cur fin : Z) R M,
    cur + Z.of_nat (S k) = fin -> 0 <= cur -> fin <= 2 ^ 63 ->
    getr R 12%bv = Z_to_bv 64 cur -> getr R 10%bv = Z_to_bv 64 fin ->
    (forall a, cur <= a < fin -> exists b, rdn SEGS M (Z_to_bv 64 a) 1 = Some [b]) ->
    exists R',
      msteps SEGS (@mkst fx R (Z_to_bv 64 0x6c14c) M (seg_rom SEGS)) (@mkst fx R' (Z_to_bv 64 0x6c170) M (seg_rom SEGS))
      /\ (forall r, r <> 11%bv -> r <> 12%bv -> r <> 14%bv -> r <> 15%bv -> r <> 16%bv -> getr R' r = getr R r).
  Proof using fx.
    induction k as [|k IH]; intros cur fin R M Hk Hc0 Hf H12 H10 HB.
    - destruct (HB cur ltac:(lia)) as [b Hb].
      destruct (HASH_BODY cur R M b H12 Hc0 ltac:(lia) Hb) as (R1 & RUN & G12 & G10 & GS).
      exists R1. split.
      + eapply msteps_trans; [exact RUN|]. norm_pc.
        stepb_ft F_6c12c D_6c12c ltac:(rewrite G12, G10, H10; replace (cur + 1) with fin by lia; apply c_eq_refl).
        close_pc.
      + exact GS.
    - destruct (HB cur ltac:(lia)) as [b Hb].
      destruct (HASH_BODY cur R M b H12 Hc0 ltac:(lia) Hb) as (R1 & RUN & G12 & G10 & GS).
      destruct (IH (cur + 1) fin R1 M ltac:(lia) ltac:(lia) Hf G12 ltac:(rewrite G10; exact H10) ltac:(intros a Ha; apply HB; lia))
        as (R' & RUN' & GS').
      exists R'. split.
      + eapply msteps_trans; [exact RUN|]. eapply msteps_trans; [|exact RUN']. norm_pc.
        stepb_tk F_6c12c D_6c12c ltac:(rewrite G12, G10, H10; rewrite c_eq_Z' by lia; apply Z.eqb_neq; lia).
        close_pc.
      + intros r Ha Hb' Hc Hd He. rewrite (GS' r Ha Hb' Hc Hd He). apply GS; assumption.
  Qed.
  Definition cRG : rg_consts := {| rc_ctor := 0x6c080; rc_gettargetenv := 0x6c1a0; rc_ctor_stack := 16; rc_gte_stack := 96 |}.

  Lemma ro_rdn : forall M (a : Z) (k : nat), ro_clear Ly.L M -> 0x10000 <= a -> a + Z.of_nat k <= 0xe6000 ->
    rdn SEGS M (Z_to_bv 64 a) k = rdn SEGS (fun _ => None) (Z_to_bv 64 a) k.
  Proof using.
    intros M a k ROC H1 H2. symmetry. apply rdn_agree_win; [lia|lia|]. intros x Hx. unfold zwin in Hx.
    symmetry. apply ROC. rewrite u64_of_Z by lia. unfold ro_addr. cbn [ly_img ly_rw ly_relro Ly.L]. rewrite !in_ranges_1. lia.
  Qed.

  Lemma ro_clear_stores : forall W M M', ro_clear Ly.L M -> stores_in W M M' ->
    (forall a, W a -> alloc_ceiling <= a) -> ro_clear Ly.L M'.
  Proof using AC.
    intros W M M' ROC SI HW. eapply ro_clear_frame; [exact ROC | eapply stores_in_frame_eq; [exact SI | intros a Ha; exact Ha] |].
    intros a Hro Hw. pose proof (HW a Hw). pose proof ac_bounds_lit.
    unfold ro_addr in Hro. cbn [ly_img ly_rw ly_relro Ly.L] in Hro. rewrite !in_ranges_1 in Hro. lia.
  Qed.

  Lemma CTOR_A : forall R M (sp ret obj data size : Z),
    ro_clear Ly.L M -> 0 <= obj -> obj + RG_SZ <= 2 ^ 63 -> mdef M obj RG_SZ -> alloc_ceiling <= obj ->
    getr R 10%bv = Z_to_bv 64 obj -> getr R 11%bv = Z_to_bv 64 data -> getr R 12%bv = Z_to_bv 64 size ->
    exists R1 M1,
      msteps SEGS (@mkst fx R (Z_to_bv 64 0x6c080) M (seg_rom SEGS)) (@mkst fx R1 (Z_to_bv 64 0x6c0d4) M1 (seg_rom SEGS))
      /\ getr R1 10%bv = Z_to_bv 64 data /\ getr R1 11%bv = Z_to_bv 64 size
      /\ (forall r, ~ In r [5; 10; 11; 13; 14; 15; 16; 17]%bv -> getr R1 r = getr R r)
      /\ stores_in (zwin obj (obj + RG_SZ)) M M1
      /\ (forall j, 0 <= j < 312 -> fld SEGS M1 (obj + 8 * j) 8 (Znth j mt_init))
      /\ fld SEGS M1 (obj + 8 * 312) 8 0.
  Proof using fx AC.
    intros R M sp ret obj data size ROC Ho0 Ho1 HD Hoc Ha0 Ha1 Ha2. pose proof ac_bounds_lit as Hcv. unfold RG_SZ in *.
    assert (RDK : rdn SEGS M (Z_to_bv 64 K_MTF) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 MT_F))).
    { rewrite ro_rdn; [exact img_K_MTF | exact ROC | unfold K_MTF; lia | unfold K_MTF; cbn; lia]. }
    set (M0 := wbytes M (Z_to_bv 64 obj) (word_to_le_bytes 8 (Z_to_bv 64 5489))).

    assert (PRE : exists R0, msteps SEGS (@mkst fx R (Z_to_bv 64 0x6c080) M (seg_rom SEGS)) (@mkst fx R0 (Z_to_bv 64 0x6c0a0) M0 (seg_rom SEGS))
       /\ getr R0 13%bv = Z_to_bv 64 MT_F /\ getr R0 14%bv = Z_to_bv 64 (Znth (1 - 1) mt_init) /\ getr R0 15%bv = Z_to_bv 64 (obj + 8 * 1)
       /\ getr R0 16%bv = Z_to_bv 64 1 /\ getr R0 17%bv = Z_to_bv 64 312
       /\ getr R0 10%bv = Z_to_bv 64 obj /\ getr R0 11%bv = Z_to_bv 64 data /\ getr R0 12%bv = Z_to_bv 64 size
       /\ (forall r, ~ In r [5; 10; 11; 13; 14; 15; 16; 17]%bv -> getr R0 r = getr R r)).
    { eexists. split.
      - norm_pc.
        sv F_6c040 D_6c040 (Z_to_bv 64 0x1000).
        sv F_6c044 D_6c044 (Z_to_bv 64 0x15084).
        sv F_6c048 D_6c048 (Z_to_bv 64 5489).
        ld_step F_6c04c D_6c04c (word_to_le_bytes 8 (Z_to_bv 64 MT_F)) (Z_to_bv 64 MT_F) ltac:(rdn_fix RDK) ltac:(b2z8).
        stw F_6c050 D_6c050 (Z_to_bv 64 obj) (Z_to_bv 64 5489) ltac:(ok_mdef HD).
        sv F_6c054 D_6c054 (Z_to_bv 64 (obj + 8 * 1)).
        sv F_6c058 D_6c058 (Z_to_bv 64 1).
        sv F_6c05c D_6c05c (Z_to_bv 64 312).
        close_pc.
      - gres. change (1 - 1) with 0. rewrite mt_init_0. repeat split; try reflexivity; try assumption.
        intros r Hr. rewrite !getr_other by (intros ->; apply Hr; (first [solve [clear; cbv; tauto] | cbv; tauto])). reflexivity. }
    destruct PRE as (R0 & RUN0 & G13 & G14 & G15 & G16 & G17 & G10 & G11 & G12 & GS0).
    assert (SI0 : stores_in (zwin obj (obj + 2504)) M M0).
    { unfold M0. apply stores_in_wbytes; rewrite ?length_N_to_le_bytes; cbn; try lia. intros a Ha. unfold zwin. lia. }
    destruct (SEED 310 1 obj R0 M M0 ltac:(lia) ltac:(cbn; lia) Ho0 ltac:(unfold RG_SZ; lia) G13 G14 G15 G16 G17
                ltac:(unfold RG_SZ; exact HD) ltac:(unfold RG_SZ; exact SI0)) as (R1 & M1 & RUN1 & GS1 & SI1 & FJ1).
    { intros j Hj. replace j with 0 by lia. rewrite mt_init_0. unfold fld, M0. rewrite Z.mul_0_r, Z.add_0_r.
      apply rdn_wbytes_hit8. rewrite u64_of_Z by lia. lia. }
    unfold RG_SZ in SI1.
    assert (HD1 : mdef M1 obj 2504) by (eapply stores_in_mdef; [exact SI1 | exact HD]).
    set (M2 := wbytes M1 (Z_to_bv 64 (obj + 8 * 312)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
    assert (G1_10 : getr R1 10%bv = Z_to_bv 64 obj) by (rewrite GS1 by (intros HH; inversion HH); exact G10).
    assert (G1_11 : getr R1 11%bv = Z_to_bv 64 data) by (rewrite GS1 by (intros HH; inversion HH); exact G11).
    assert (G1_12 : getr R1 12%bv = Z_to_bv 64 size) by (rewrite GS1 by (intros HH; inversion HH); exact G12).
    eexists. exists M2. split; [|split; [|split; [|split; [|split; [|split]]]]].
    - eapply msteps_trans; [exact RUN0|]. eapply msteps_trans; [exact RUN1|]. norm_pc.
      stepiv F_6c080 D_6c080 (Z_to_bv 64 (obj + 2047)) ltac:(gres; pin; imm_norm; rewrite v_addi_Z by lia; reflexivity).
      stw F_6c084 D_6c084 (Z_to_bv 64 (obj + 8 * 312)) (Z_to_bv 64 0) ltac:(ok_mdef HD1).
      sv F_6c088 D_6c088 (Z_to_bv 64 data).
      sv F_6c08c D_6c08c (Z_to_bv 64 size).
      stepj F_6c090 D_6c090.
      fold M2.
      lazymatch goal with |- msteps _ (mkst ?r ?pc _ _) (mkst ?r' ?pc' _ _) =>
        unify r' r; replace pc with pc' by (apply bv_eq; vm_compute; reflexivity) end. apply mst_refl.
    - gres. reflexivity.
    - gres. reflexivity.
    - intros r Hr. rewrite !getr_other by (intros ->; apply Hr; (first [solve [clear; cbv; tauto] | cbv; tauto])).
      rewrite GS1 by (intros ->; apply Hr; (first [solve [clear; cbv; tauto] | cbv; tauto])). apply GS0. exact Hr.
    - eapply stores_in_trans; [exact SI1|]. unfold M2. apply stores_in_wbytes; rewrite ?length_N_to_le_bytes; cbn; try lia.
      intros a Ha. unfold zwin. lia.
    - intros j Hj. unfold fld, M2. rewrite rdn_wbytes_out_Z by (rewrite length_N_to_le_bytes; cbn; lia). apply FJ1. lia.
    - unfold fld, M2. apply rdn_wbytes_hit8. rewrite u64_of_Z by lia. lia.
  Qed.
  Lemma c_lts_Z : forall a b, 0 <= a < 2 ^ 63 -> 0 <= b < 2 ^ 63 -> c_lts (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
  Proof using. intros a b Ha Hb. unfold c_lts, bv_lts. rewrite !bv_signed_small64 by lia. reflexivity. Qed.

  Definition K1a : Z := 0x14990.  Definition K2a : Z := 0x14960.  Definition K3a : Z := 0x14a30.
  Lemma img_K1 : rdn SEGS (fun _ => None) (Z_to_bv 64 K1a) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 8298762835598203578)).
  Proof using. vm_refl_bv. Qed.
  Lemma img_K2 : rdn SEGS (fun _ => None) (Z_to_bv 64 K2a) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 14594272307789293969)).
  Proof using. vm_refl_bv. Qed.
  Lemma img_K3 : rdn SEGS (fun _ => None) (Z_to_bv 64 K3a) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 11400714819323198486)).
  Proof using. vm_refl_bv. Qed.

  #[local] Ltac other_regs Hs :=
    intros r Hr; rewrite !getr_other by (intros ->; apply Hr; (first [solve [clear; cbv; tauto] | cbv; tauto]));
    first [ reflexivity | apply Hs; intros HH; apply Hr; revert HH; (first [solve [clear; cbv; tauto] | cbv; tauto]) ].

  Lemma CSEED : forall R M1 (data size sp ret : Z) bs,
    ro_clear Ly.L M1 -> 0 < data -> data + size <= 2 ^ 63 -> 1 <= size ->
    rdn SEGS M1 (Z_to_bv 64 data) (Z.to_nat (Z.min size 37)) = Some bs ->
    mdef M1 (sp - 16) 16 -> alloc_ceiling <= sp - 16 -> sp < 2 ^ 47 ->
    (forall a, data <= a < data + Z.min size 37 -> ~ (sp - 16 <= a < sp)) ->
    ret_ok (Z_to_bv 64 ret) -> getr R 1%bv = Z_to_bv 64 ret -> getr R 2%bv = Z_to_bv 64 sp ->
    getr R 10%bv = Z_to_bv 64 data -> getr R 11%bv = Z_to_bv 64 size ->
    exists R',
      msteps SEGS (@mkst fx R (Z_to_bv 64 0x6c0d4) M1 (seg_rom SEGS))
                  (@mkst fx R' (Z_to_bv 64 ret) (wbytes M1 (Z_to_bv 64 (sp - 8)) (word_to_le_bytes 8 (Z_to_bv 64 ret))) (seg_rom SEGS))
      /\ getr R' 1%bv = Z_to_bv 64 ret /\ getr R' 2%bv = Z_to_bv 64 sp
      /\ (forall r, ~ In r [1; 2; 5; 10; 11; 12; 13; 14; 15; 16]%bv -> getr R' r = getr R r).
  Proof using fx AC.
    intros R M1 data size sp ret bs ROC Hd0 Hd1 Hsz RD HDW Hsp16 Hsp47 DJ Hret Hra Hsp Ha0 Ha1. pose proof ac_bounds_lit as Hcv.
    set (c := Z.min (Z.max size 4) 9). set (lo := c - 4). set (hi := Z.min size (c + 28)).
    assert (Hc : 4 <= c <= 9 /\ 0 <= lo <= 5 /\ lo < hi /\ hi <= Z.min size 37 /\ lo < size /\ hi <= size) by (unfold c, lo, hi; lia).
    set (M2 := wbytes M1 (Z_to_bv 64 (sp - 8)) (word_to_le_bytes 8 (Z_to_bv 64 ret))).
    assert (RO2 : forall K v, rdn SEGS (fun _ => None) (Z_to_bv 64 K) 8 = Some v -> 0x10000 <= K -> K + 8 <= 0xe6000 ->
                  rdn SEGS M2 (Z_to_bv 64 K) 8 = Some v).
    { intros K v HK H1 H2. unfold M2. rewrite rdn_wbytes_out_Z by (rewrite length_N_to_le_bytes; cbn; lia).
      rewrite ro_rdn; [exact HK | exact ROC | lia | cbn; lia]. }

    assert (S1 : exists R1, msteps SEGS (@mkst fx R (Z_to_bv 64 0x6c0d4) M1 (seg_rom SEGS)) (@mkst fx R1 (Z_to_bv 64 0x6c0f0) M2 (seg_rom SEGS))
       /\ getr R1 12%bv = Z_to_bv 64 (Z.max size 4) /\ getr R1 2%bv = Z_to_bv 64 (sp - 16) /\ getr R1 10%bv = Z_to_bv 64 data /\ getr R1 11%bv = Z_to_bv 64 size
       /\ (forall r, ~ In r [2; 12; 13]%bv -> getr R1 r = getr R r)).
    { destruct (Z.lt_ge_cases 4 size) as [Hlt|Hge].
      - eexists. split.
        + norm_pc.
          sv F_6c094 D_6c094 (Z_to_bv 64 (sp - 16)).
          stw F_6c098 D_6c098 (Z_to_bv 64 (sp - 8)) (Z_to_bv 64 ret) ltac:(ok_mdef HDW).
          stepb_ft F_6c09c D_6c09c ltac:(rewrite Ha0; rewrite c_eq_Z' by lia; apply Z.eqb_neq; lia).
          sv F_6c0a0 D_6c0a0 (Z_to_bv 64 4).
          sv F_6c0a4 D_6c0a4 (Z_to_bv 64 size).
          stepb_tk F_6c0a8 D_6c0a8 ltac:(rewrite Ha1; rewrite c_lts_Z by lia; apply Z.ltb_lt; lia).
          close_pc.
        + gres. replace (Z.max size 4) with size by lia. repeat split; try reflexivity; try assumption. other_regs I.
      - eexists. split.
        + norm_pc.
          sv F_6c094 D_6c094 (Z_to_bv 64 (sp - 16)).
          stw F_6c098 D_6c098 (Z_to_bv 64 (sp - 8)) (Z_to_bv 64 ret) ltac:(ok_mdef HDW).
          stepb_ft F_6c09c D_6c09c ltac:(rewrite Ha0; rewrite c_eq_Z' by lia; apply Z.eqb_neq; lia).
          sv F_6c0a0 D_6c0a0 (Z_to_bv 64 4).
          sv F_6c0a4 D_6c0a4 (Z_to_bv 64 size).
          stepb_ft F_6c0a8 D_6c0a8 ltac:(rewrite Ha1; rewrite c_lts_Z by lia; apply Z.ltb_ge; lia).
          sv F_6c0ac D_6c0ac (Z_to_bv 64 4).
          close_pc.
        + gres. replace (Z.max size 4) with 4 by lia. repeat split; try reflexivity; try assumption. other_regs I. }
    destruct S1 as (R1 & RUN1 & R1_12 & R1_2 & R1_10 & R1_11 & R1S).

    assert (S2 : exists R2, msteps SEGS (@mkst fx R1 (Z_to_bv 64 0x6c0f0) M2 (seg_rom SEGS)) (@mkst fx R2 (Z_to_bv 64 0x6c0fc) M2 (seg_rom SEGS))
       /\ getr R2 12%bv = Z_to_bv 64 c /\ getr R2 2%bv = Z_to_bv 64 (sp - 16) /\ getr R2 10%bv = Z_to_bv 64 data /\ getr R2 11%bv = Z_to_bv 64 size
       /\ (forall r, ~ In r [12; 13]%bv -> getr R2 r = getr R1 r)).
    { destruct (Z.lt_ge_cases (Z.max size 4) 9) as [Hlt|Hge].
      - eexists. split.
        + norm_pc. sv F_6c0b0 D_6c0b0 (Z_to_bv 64 9).
          stepb_tk F_6c0b4 D_6c0b4 ltac:(rewrite R1_12; rewrite c_lts_Z by lia; apply Z.ltb_lt; lia).
          close_pc.
        + gres. replace c with (Z.max size 4) by (unfold c; lia). repeat split; try reflexivity; try assumption. other_regs I.
      - eexists. split.
        + norm_pc. sv F_6c0b0 D_6c0b0 (Z_to_bv 64 9).
          stepb_ft F_6c0b4 D_6c0b4 ltac:(rewrite R1_12; rewrite c_lts_Z by lia; apply Z.ltb_ge; lia).
          sv F_6c0b8 D_6c0b8 (Z_to_bv 64 9).
          close_pc.
        + gres. replace c with 9 by (unfold c; lia). repeat split; try reflexivity; try assumption. other_regs I. }
    destruct S2 as (R2 & RUN2 & R2_12 & R2_2 & R2_10 & R2_11 & R2S).

    assert (S3 : exists R3, msteps SEGS (@mkst fx R2 (Z_to_bv 64 0x6c0fc) M2 (seg_rom SEGS)) (@mkst fx R3 (Z_to_bv 64 0x6c110) M2 (seg_rom SEGS))
       /\ getr R3 12%bv = Z_to_bv 64 lo /\ getr R3 14%bv = Z_to_bv 64 hi /\ getr R3 2%bv = Z_to_bv 64 (sp - 16)
       /\ getr R3 10%bv = Z_to_bv 64 data /\ getr R3 11%bv = Z_to_bv 64 size
       /\ (forall r, ~ In r [12; 13; 14]%bv -> getr R3 r = getr R2 r)).
    { destruct (Z.lt_ge_cases size (c + 28)) as [Hlt|Hge].
      - eexists. split.
        + norm_pc.
          stepiv F_6c0bc D_6c0bc (Z_to_bv 64 (c + 28)) ltac:(gres; pin; imm_norm; rewrite v_addi_Z by lia; reflexivity).
          stepiv F_6c0c0 D_6c0c0 (Z_to_bv 64 lo) ltac:(gres; pin; imm_norm; rewrite v_addi_Z by lia; f_equal; unfold lo; lia).
          sv F_6c0c4 D_6c0c4 (Z_to_bv 64 size).
          stepb_tk F_6c0c8 D_6c0c8 ltac:(rewrite R2_11; rewrite c_lts_Z by lia; apply Z.ltb_lt; lia).
          close_pc.
        + gres. replace hi with size by (unfold hi; lia). repeat split; try reflexivity; try assumption. other_regs I.
      - eexists. split.
        + norm_pc.
          stepiv F_6c0bc D_6c0bc (Z_to_bv 64 (c + 28)) ltac:(gres; pin; imm_norm; rewrite v_addi_Z by lia; reflexivity).
          stepiv F_6c0c0 D_6c0c0 (Z_to_bv 64 lo) ltac:(gres; pin; imm_norm; rewrite v_addi_Z by lia; f_equal; unfold lo; lia).
          sv F_6c0c4 D_6c0c4 (Z_to_bv 64 size).
          stepb_ft F_6c0c8 D_6c0c8 ltac:(rewrite R2_11; rewrite c_lts_Z by lia; apply Z.ltb_ge; lia).
          sv F_6c0cc D_6c0cc (Z_to_bv 64 (c + 28)).
          close_pc.
        + gres. replace hi with (c + 28) by (unfold hi; lia). repeat split; try reflexivity; try assumption. other_regs I. }
    destruct S3 as (R3 & RUN3 & R3_12 & R3_14 & R3_2 & R3_10 & R3_11 & R3S).

    assert (S4 : exists R4, msteps SEGS (@mkst fx R3 (Z_to_bv 64 0x6c110) M2 (seg_rom SEGS)) (@mkst fx R4 (Z_to_bv 64 0x6c14c) M2 (seg_rom SEGS))
       /\ getr R4 12%bv = Z_to_bv 64 (data + lo) /\ getr R4 10%bv = Z_to_bv 64 (data + hi) /\ getr R4 2%bv = Z_to_bv 64 (sp - 16)
       /\ (forall r, ~ In r [10; 11; 12; 13; 15]%bv -> getr R4 r = getr R3 r)).
    { eexists. split.
      - norm_pc.
        stepb_tk F_6c0d0 D_6c0d0 ltac:(rewrite R3_11, R3_12; rewrite c_eq_Z' by lia; apply Z.eqb_neq; lia).
        sv F_6c0e0 D_6c0e0 (Z_to_bv 64 0x15120).
        ld_step F_6c0e4 D_6c0e4 (word_to_le_bytes 8 (Z_to_bv 64 8298762835598203578)) (Z_to_bv 64 8298762835598203578)
          ltac:(apply (RO2 K1a); [exact img_K1 | unfold K1a; lia | unfold K1a; lia]) ltac:(b2z8).
        stepiv F_6c0e8 D_6c0e8 (Z_to_bv 64 (hi - lo)) ltac:(gres; pin; rewrite v_sub_Z by lia; reflexivity).
        sv F_6c0ec D_6c0ec (Z_to_bv 64 0x1512c).
        ld_step F_6c0f0 D_6c0f0 (word_to_le_bytes 8 (Z_to_bv 64 14594272307789293969)) (Z_to_bv 64 14594272307789293969)
          ltac:(apply (RO2 K2a); [exact img_K2 | unfold K2a; lia | unfold K2a; lia]) ltac:(b2z8).
        sn F_6c0f4 D_6c0f4.
        sv F_6c0f8 D_6c0f8 (Z_to_bv 64 0x15138).
        ld_step F_6c0fc D_6c0fc (word_to_le_bytes 8 (Z_to_bv 64 11400714819323198486)) (Z_to_bv 64 11400714819323198486)
          ltac:(apply (RO2 K3a); [exact img_K3 | unfold K3a; lia | unfold K3a; lia]) ltac:(b2z8).
        sn F_6c100 D_6c100.
        stepiv F_6c104 D_6c104 (Z_to_bv 64 (data + lo)) ltac:(gres; pin; rewrite v_add_Z by lia; reflexivity).
        stepiv F_6c108 D_6c108 (Z_to_bv 64 (data + hi)) ltac:(gres; pin; rewrite v_add_Z by lia; reflexivity).
        close_pc.
      - gres. repeat split; try reflexivity; try assumption. other_regs I. }
    destruct S4 as (R4 & RUN4 & R4_12 & R4_10 & R4_2 & R4S).

    destruct (HASH (Z.to_nat (hi - lo - 1)) (data + lo) (data + hi) R4 M2 ltac:(rewrite Nat2Z.inj_succ, Z2Nat.id by lia; lia) ltac:(lia) ltac:(lia) R4_12 R4_10)
      as (R5 & RUN5 & R5S).
    { intros a Ha. unfold M2. rewrite rdn_wbytes_out_Z by (rewrite length_N_to_le_bytes; cbn; pose proof (DJ a ltac:(lia)); lia).
      exists (nth (Z.to_nat (a - data)) bs (Z_to_bv 8 0)).
      pose proof (rdn_sub SEGS M1 _ (Z_to_bv 64 data) bs (Z.to_nat (a - data)) 1 RD ltac:(lia)) as HS.
      unfold at_ in HS. rewrite u64_of_Z in HS by lia. replace (data + Z.of_nat (Z.to_nat (a - data))) with a in HS by lia.
      rewrite HS. f_equal. unfold sub.
      pose proof (rdn_length _ _ _ _ _ RD) as HL.
      rewrite (skipn_nth bs (Z.to_nat (a - data)) (Z_to_bv 8 0)) by lia. reflexivity. }

    assert (SL : rdn SEGS M2 (Z_to_bv 64 (sp - 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 ret))).
    { unfold M2. apply rdn_wbytes_hit8. rewrite u64_of_Z by lia. lia. }
    assert (R5_2 : getr R5 2%bv = Z_to_bv 64 (sp - 16)) by (rewrite R5S by (intros HH; inversion HH); exact R4_2).
    eexists. split; [|split; [|split]].
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|].
      eapply msteps_trans; [exact RUN4|]. eapply msteps_trans; [exact RUN5|]. norm_pc.
      sn F_6c130 D_6c130.
      ld_step F_6c134 D_6c134 (word_to_le_bytes 8 (Z_to_bv 64 ret)) (Z_to_bv 64 ret) ltac:(rdn_fix SL) ltac:(b2z8).
      sv F_6c138 D_6c138 (Z_to_bv 64 sp).
      stepjr F_6c13c D_6c13c (Z_to_bv 64 ret) ltac:(gres; reflexivity).
      fold M2.
      lazymatch goal with |- msteps _ (mkst ?r ?pc _ _) (mkst ?r' _ _ _) => unify r' r;
        replace pc with (Z_to_bv 64 ret) by (symmetry; imm_norm; exact Hret) end. apply mst_refl.
    - gres. reflexivity.
    - gres. reflexivity.
    - intros r Hr. rewrite !getr_other by (intros ->; apply Hr; (first [solve [clear; cbv; tauto] | cbv; tauto])).
      rewrite R5S by (intros HH; apply Hr; subst r; (first [solve [clear; cbv; tauto] | cbv; tauto])).
      rewrite R4S, R3S, R2S, R1S; [reflexivity | | | |]; intros HH; apply Hr; revert HH; (first [solve [clear; cbv; tauto] | cbv; tauto]).
  Qed.
End RG.

  Theorem rg_ctor_6bfdc_spec {AC : AllocCeiling} : rg_ctor_stmt SEGS Ly.L cRG.
  Proof.
    intros fx M R sp ret obj data size bs. cbn [rc_ctor rc_ctor_stack cRG]. lazy zeta.
    intros ROC Ho0 Ho1 HDo Hd0 Hd1 Hsz RD DJ1 DJ2 HROOM Hspc Hsp47 Hoc Hret Hra Hsp Ha0 Ha1 Ha2.
    pose proof ac_bounds_lit as Hcv. unfold RG_SZ in *.
    assert (DJo : obj + 2504 <= sp - 16 \/ sp <= obj).
    { destruct (Z.lt_ge_cases obj sp); [left|right; lia].
      destruct (Z.lt_ge_cases (obj + 2504) (sp - 16 + 1)); [lia|]. exfalso.
      destruct (Z.lt_ge_cases obj (sp - 16)).
      - apply (DJ1 (sp - 16)); [left|]; unfold zwin; lia.
      - apply (DJ1 obj); [left|]; unfold zwin; lia. }
    destruct (CTOR_A R M sp ret obj data size ROC Ho0 ltac:(unfold RG_SZ; lia) ltac:(unfold RG_SZ; exact HDo) Hoc Ha0 Ha1 Ha2)
      as (R1 & M1 & RUN1 & R1_10 & R1_11 & R1S & SI1 & FJ1 & FI1). unfold RG_SZ in SI1.
    assert (ROC1 : ro_clear Ly.L M1) by (eapply ro_clear_stores; [exact ROC | exact SI1 | intros a Ha; unfold zwin in Ha; lia]).
    assert (HDW : mdef M (sp - 16) 16).
    { unfold stack_room in HROOM. eapply store_ok_mdef_offimg; [exact HROOM | lia | lia | lia |]. intros w Hw. apply ly_noseg. lia. }
    assert (HDW1 : mdef M1 (sp - 16) 16) by (eapply stores_in_mdef; [exact SI1 | exact HDW]).
    assert (RD1 : rdn SEGS M1 (Z_to_bv 64 data) (Z.to_nat (Z.min size 37)) = Some bs).
    { rewrite <- RD. apply rdn_agree_win; [lia | lia |]. eapply stores_in_agree; [exact SI1|].
      intros a Ha. unfold zwin in Ha. split; [lia|]. intros Hz. apply (DJ2 a); unfold zwin in *; lia. }
    destruct (CSEED R1 M1 data size sp ret bs ROC1 Hd0 Hd1 Hsz RD1 HDW1 Hspc Hsp47
                ltac:(intros a Ha Hw; apply (DJ1 a); [right|]; unfold zwin; lia) Hret
                ltac:(rewrite R1S by (first [solve [clear; cbv; intuition discriminate] | cbv; intuition discriminate]); exact Hra)
                ltac:(rewrite R1S by (first [solve [clear; cbv; intuition discriminate] | cbv; intuition discriminate]); exact Hsp) R1_10 R1_11)
      as (R' & RUN2 & R'_1 & R'_2 & R'S).
    set (M2 := wbytes M1 (Z_to_bv 64 (sp - 8)) (word_to_le_bytes 8 (Z_to_bv 64 ret))) in *.
    assert (SI : stores_in (fun a => zwin obj (obj + 2504) a \/ zwin (sp - 16) sp a) M M2).
    { eapply stores_in_trans; [eapply stores_in_weaken; [exact SI1|]; intros a Ha; left; exact Ha |].
      unfold M2. apply stores_in_wbytes; rewrite ?length_N_to_le_bytes; cbn; try lia. intros a Ha. right. unfold zwin. lia. }
    exists R', M2. split; [|split; [|split; [|split; [|split]]]].
    - eapply msteps_trans; [exact RUN1 | exact RUN2].
    - intros r Hr. unfold callee_saved in Hr.
      destruct (bv_eq_dec _ r 1%bv) as [->|H1]; [rewrite R'_1; symmetry; exact Hra|].
      destruct (bv_eq_dec _ r 2%bv) as [->|H2]; [rewrite R'_2; symmetry; exact Hsp|].
      rewrite R'S by (first [ solve [clear - Hr H1 H2; cbv; intros HH; decompose [or] HH; try subst r; try contradiction; cbv in Hr; intuition discriminate] | cbv; intros HH; decompose [or] HH; try subst r; try contradiction; cbv in Hr; intuition discriminate ]).
      apply R1S. first [ solve [clear - Hr H1 H2; cbv; intros HH; decompose [or] HH; try subst r; cbv in Hr; intuition discriminate] | cbv; intros HH; decompose [or] HH; try subst r; cbv in Hr; intuition discriminate ].
    -
      split; [eapply stores_in_mdef; [exact SI | unfold RG_SZ; exact HDo] |]. split.
      + intros i Hi. unfold MT_N in Hi. unfold fld, M2. rewrite rdn_wbytes_out_Z by (rewrite length_N_to_le_bytes; cbn; lia). apply FJ1. lia.
      + unfold MT_N, fld, M2. rewrite rdn_wbytes_out_Z by (rewrite length_N_to_le_bytes; cbn; lia). exact FI1.
    - eapply stores_in_frame_eq; [exact SI|]. intros a [Ha|Ha]; [left; unfold RG_SZ; exact Ha | right; exact Ha].
    - exact (proj2 SI).
    - eapply ro_clear_stores; [exact ROC | exact SI |]. intros a [Ha|Ha]; unfold zwin in Ha; lia.
  Qed.
