(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Plain.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SRealizes OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StepTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibBudget OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibEff OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.S1Layout OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SumMemset OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Lib_Cxx_OperatorNew.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.MallocIfaceStmt OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.MallocInstS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.MallocHeapOwnS1.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv.S1Statics.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.CRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContStmts3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.S1Facts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.Lib_Vec32_PushBack OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.Lib_Vec32_PushBack_69278 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.Lib_Vec32_PushBack_697a0 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.Lib_Vec32_PushBack_6b8f8 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.Lib_VecOpnd_PushBack OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.Lib_Str_PushBack.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.WalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StartupTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SumWalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MemSplit OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ShapeAlg OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefReadLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MmapSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibMaskBits.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.StrLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.LiveStats.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Module S1_code_65fec_660b8.

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_65fec : bv 32 := 0x00053023.
Lemma F_65fec : fetch_word Plain.M.loaded_segments (0x6602c : word) = Some W_65fec.
Proof. vm_refl. Qed.
Lemma D_65fec : decode_any W_65fec = Some (Store SZ8 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65ff0 : bv 32 := 0x00053423.
Lemma F_65ff0 : fetch_word Plain.M.loaded_segments (0x66030 : word) = Some W_65ff0.
Proof. vm_refl. Qed.
Lemma D_65ff0 : decode_any W_65ff0 = Some (Store SZ8 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_65ff4 : bv 32 := 0x00053823.
Lemma F_65ff4 : fetch_word Plain.M.loaded_segments (0x66034 : word) = Some W_65ff4.
Proof. vm_refl. Qed.
Lemma D_65ff4 : decode_any W_65ff4 = Some (Store SZ8 10 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_65ff8 : bv 32 := 0x0a060e63.
Lemma F_65ff8 : fetch_word Plain.M.loaded_segments (0x66038 : word) = Some W_65ff8.
Proof. vm_refl. Qed.
Lemma D_65ff8 : decode_any W_65ff8 = Some (Branch BC_EQ 12 0 188, 4%Z).
Proof. vm_refl. Qed.

Definition W_65ffc : bv 32 := 0xfc010113.
Lemma F_65ffc : fetch_word Plain.M.loaded_segments (0x6603c : word) = Some W_65ffc.
Proof. vm_refl. Qed.
Lemma D_65ffc : decode_any W_65ffc = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_66000 : bv 32 := 0x02113c23.
Lemma F_66000 : fetch_word Plain.M.loaded_segments (0x66040 : word) = Some W_66000.
Proof. vm_refl. Qed.
Lemma D_66000 : decode_any W_66000 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_66004 : bv 32 := 0x02813823.
Lemma F_66004 : fetch_word Plain.M.loaded_segments (0x66044 : word) = Some W_66004.
Proof. vm_refl. Qed.
Lemma D_66004 : decode_any W_66004 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_66008 : bv 32 := 0x02913423.
Lemma F_66008 : fetch_word Plain.M.loaded_segments (0x66048 : word) = Some W_66008.
Proof. vm_refl. Qed.
Lemma D_66008 : decode_any W_66008 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_6600c : bv 32 := 0x03213023.
Lemma F_6600c : fetch_word Plain.M.loaded_segments (0x6604c : word) = Some W_6600c.
Proof. vm_refl. Qed.
Lemma D_6600c : decode_any W_6600c = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_66010 : bv 32 := 0x01313c23.
Lemma F_66010 : fetch_word Plain.M.loaded_segments (0x66050 : word) = Some W_66010.
Proof. vm_refl. Qed.
Lemma D_66010 : decode_any W_66010 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_66014 : bv 32 := 0x01413823.
Lemma F_66014 : fetch_word Plain.M.loaded_segments (0x66054 : word) = Some W_66014.
Proof. vm_refl. Qed.
Lemma D_66014 : decode_any W_66014 = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_66018 : bv 32 := 0x01513423.
Lemma F_66018 : fetch_word Plain.M.loaded_segments (0x66058 : word) = Some W_66018.
Proof. vm_refl. Qed.
Lemma D_66018 : decode_any W_66018 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6601c : bv 32 := 0x00058413.
Lemma F_6601c : fetch_word Plain.M.loaded_segments (0x6605c : word) = Some W_6601c.
Proof. vm_refl. Qed.
Lemma D_6601c : decode_any W_6601c = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_66020 : bv 32 := 0x00050493.
Lemma F_66020 : fetch_word Plain.M.loaded_segments (0x66060 : word) = Some W_66020.
Proof. vm_refl. Qed.
Lemma D_66020 : decode_any W_66020 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_66024 : bv 32 := 0x00261913.
Lemma F_66024 : fetch_word Plain.M.loaded_segments (0x66064 : word) = Some W_66024.
Proof. vm_refl. Qed.
Lemma D_66024 : decode_any W_66024 = Some (ShiftImm ALU_SLL 18 12 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_66028 : bv 32 := 0x00010537.
Lemma F_66028 : fetch_word Plain.M.loaded_segments (0x66068 : word) = Some W_66028.
Proof. vm_refl. Qed.
Lemma D_66028 : decode_any W_66028 = Some (Lui 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6602c : bv 32 := 0xf005099b.
Lemma F_6602c : fetch_word Plain.M.loaded_segments (0x6606c : word) = Some W_6602c.
Proof. vm_refl. Qed.
Lemma D_6602c : decode_any W_6602c = Some (OpImm32 19 10 3840, 4%Z).
Proof. vm_refl. Qed.

Definition W_66030 : bv 32 := 0x00ff0a37.
Lemma F_66030 : fetch_word Plain.M.loaded_segments (0x66070 : word) = Some W_66030.
Proof. vm_refl. Qed.
Lemma D_66030 : decode_any W_66030 = Some (Lui 20 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_66034 : bv 32 := 0x00046a83.
Lemma F_66034 : fetch_word Plain.M.loaded_segments (0x66074 : word) = Some W_66034.
Proof. vm_refl. Qed.
Lemma D_66034 : decode_any W_66034 = Some (Load SZ4 false 21 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_66038 : bv 32 := 0x0ffaf593.
Lemma F_66038 : fetch_word Plain.M.loaded_segments (0x66078 : word) = Some W_66038.
Proof. vm_refl. Qed.
Lemma D_66038 : decode_any W_66038 = Some (OpImm ALU_AND 11 21 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_6603c : bv 32 := 0x04058c63.
Lemma F_6603c : fetch_word Plain.M.loaded_segments (0x6607c : word) = Some W_6603c.
Proof. vm_refl. Qed.
Lemma D_6603c : decode_any W_6603c = Some (Branch BC_EQ 11 0 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_66040 : bv 32 := 0x00048513.
Lemma F_66040 : fetch_word Plain.M.loaded_segments (0x66080 : word) = Some W_66040.
Proof. vm_refl. Qed.
Lemma D_66040 : decode_any W_66040 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_66044 : bv 32 := 0x3fc250ef.
Lemma F_66044 : fetch_word Plain.M.loaded_segments (0x66084 : word) = Some W_66044.
Proof. vm_refl. Qed.
Lemma D_66044 : decode_any W_66044 = Some (Jal 1 152572, 4%Z).
Proof. vm_refl. Qed.

Definition W_66048 : bv 32 := 0x013af533.
Lemma F_66048 : fetch_word Plain.M.loaded_segments (0x66088 : word) = Some W_66048.
Proof. vm_refl. Qed.
Lemma D_66048 : decode_any W_66048 = Some (Op ALU_AND 10 21 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_6604c : bv 32 := 0x04050463.
Lemma F_6604c : fetch_word Plain.M.loaded_segments (0x6608c : word) = Some W_6604c.
Proof. vm_refl. Qed.
Lemma D_6604c : decode_any W_6604c = Some (Branch BC_EQ 10 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_66050 : bv 32 := 0x030a9593.
Lemma F_66050 : fetch_word Plain.M.loaded_segments (0x66090 : word) = Some W_66050.
Proof. vm_refl. Qed.
Lemma D_66050 : decode_any W_66050 = Some (ShiftImm ALU_SLL 11 21 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_66054 : bv 32 := 0x0385d593.
Lemma F_66054 : fetch_word Plain.M.loaded_segments (0x66094 : word) = Some W_66054.
Proof. vm_refl. Qed.
Lemma D_66054 : decode_any W_66054 = Some (ShiftImm ALU_SRL 11 11 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_66058 : bv 32 := 0x00048513.
Lemma F_66058 : fetch_word Plain.M.loaded_segments (0x66098 : word) = Some W_66058.
Proof. vm_refl. Qed.
Lemma D_66058 : decode_any W_66058 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6605c : bv 32 := 0x3e4250ef.
Lemma F_6605c : fetch_word Plain.M.loaded_segments (0x6609c : word) = Some W_6605c.
Proof. vm_refl. Qed.
Lemma D_6605c : decode_any W_6605c = Some (Jal 1 152548, 4%Z).
Proof. vm_refl. Qed.

Definition W_66060 : bv 32 := 0x014af533.
Lemma F_66060 : fetch_word Plain.M.loaded_segments (0x660a0 : word) = Some W_66060.
Proof. vm_refl. Qed.
Lemma D_66060 : decode_any W_66060 = Some (Op ALU_AND 10 21 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_66064 : bv 32 := 0x02050863.
Lemma F_66064 : fetch_word Plain.M.loaded_segments (0x660a4 : word) = Some W_66064.
Proof. vm_refl. Qed.
Lemma D_66064 : decode_any W_66064 = Some (Branch BC_EQ 10 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_66068 : bv 32 := 0x028a9593.
Lemma F_66068 : fetch_word Plain.M.loaded_segments (0x660a8 : word) = Some W_66068.
Proof. vm_refl. Qed.
Lemma D_66068 : decode_any W_66068 = Some (ShiftImm ALU_SLL 11 21 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_6606c : bv 32 := 0x0385d593.
Lemma F_6606c : fetch_word Plain.M.loaded_segments (0x660ac : word) = Some W_6606c.
Proof. vm_refl. Qed.
Lemma D_6606c : decode_any W_6606c = Some (ShiftImm ALU_SRL 11 11 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_66070 : bv 32 := 0x00048513.
Lemma F_66070 : fetch_word Plain.M.loaded_segments (0x660b0 : word) = Some W_66070.
Proof. vm_refl. Qed.
Lemma D_66070 : decode_any W_66070 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_66074 : bv 32 := 0x3cc250ef.
Lemma F_66074 : fetch_word Plain.M.loaded_segments (0x660b4 : word) = Some W_66074.
Proof. vm_refl. Qed.
Lemma D_66074 : decode_any W_66074 = Some (Jal 1 152524, 4%Z).
Proof. vm_refl. Qed.

Definition W_66078 : bv 32 := 0x018ad593.
Lemma F_66078 : fetch_word Plain.M.loaded_segments (0x660b8 : word) = Some W_66078.
Proof. vm_refl. Qed.
Lemma D_66078 : decode_any W_66078 = Some (ShiftImm ALU_SRL 11 21 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_6607c : bv 32 := 0x00058c63.
Lemma F_6607c : fetch_word Plain.M.loaded_segments (0x660bc : word) = Some W_6607c.
Proof. vm_refl. Qed.
Lemma D_6607c : decode_any W_6607c = Some (Branch BC_EQ 11 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_66080 : bv 32 := 0x00048513.
Lemma F_66080 : fetch_word Plain.M.loaded_segments (0x660c0 : word) = Some W_66080.
Proof. vm_refl. Qed.
Lemma D_66080 : decode_any W_66080 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_66084 : bv 32 := 0x3bc250ef.
Lemma F_66084 : fetch_word Plain.M.loaded_segments (0x660c4 : word) = Some W_66084.
Proof. vm_refl. Qed.
Lemma D_66084 : decode_any W_66084 = Some (Jal 1 152508, 4%Z).
Proof. vm_refl. Qed.

Definition W_66088 : bv 32 := 0xffc90913.
Lemma F_66088 : fetch_word Plain.M.loaded_segments (0x660c8 : word) = Some W_66088.
Proof. vm_refl. Qed.
Lemma D_66088 : decode_any W_66088 = Some (OpImm ALU_ADD 18 18 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_6608c : bv 32 := 0x00440413.
Lemma F_6608c : fetch_word Plain.M.loaded_segments (0x660cc : word) = Some W_6608c.
Proof. vm_refl. Qed.
Lemma D_6608c : decode_any W_6608c = Some (OpImm ALU_ADD 8 8 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_66090 : bv 32 := 0xfa0912e3.
Lemma F_66090 : fetch_word Plain.M.loaded_segments (0x660d0 : word) = Some W_66090.
Proof. vm_refl. Qed.
Lemma D_66090 : decode_any W_66090 = Some (Branch BC_NE 18 0 8100, 4%Z).
Proof. vm_refl. Qed.

Definition W_66094 : bv 32 := 0x03813083.
Lemma F_66094 : fetch_word Plain.M.loaded_segments (0x660d4 : word) = Some W_66094.
Proof. vm_refl. Qed.
Lemma D_66094 : decode_any W_66094 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_66098 : bv 32 := 0x03013403.
Lemma F_66098 : fetch_word Plain.M.loaded_segments (0x660d8 : word) = Some W_66098.
Proof. vm_refl. Qed.
Lemma D_66098 : decode_any W_66098 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_6609c : bv 32 := 0x02813483.
Lemma F_6609c : fetch_word Plain.M.loaded_segments (0x660dc : word) = Some W_6609c.
Proof. vm_refl. Qed.
Lemma D_6609c : decode_any W_6609c = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_660a0 : bv 32 := 0x02013903.
Lemma F_660a0 : fetch_word Plain.M.loaded_segments (0x660e0 : word) = Some W_660a0.
Proof. vm_refl. Qed.
Lemma D_660a0 : decode_any W_660a0 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_660a4 : bv 32 := 0x01813983.
Lemma F_660a4 : fetch_word Plain.M.loaded_segments (0x660e4 : word) = Some W_660a4.
Proof. vm_refl. Qed.
Lemma D_660a4 : decode_any W_660a4 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_660a8 : bv 32 := 0x01013a03.
Lemma F_660a8 : fetch_word Plain.M.loaded_segments (0x660e8 : word) = Some W_660a8.
Proof. vm_refl. Qed.
Lemma D_660a8 : decode_any W_660a8 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_660ac : bv 32 := 0x00813a83.
Lemma F_660ac : fetch_word Plain.M.loaded_segments (0x660ec : word) = Some W_660ac.
Proof. vm_refl. Qed.
Lemma D_660ac : decode_any W_660ac = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_660b0 : bv 32 := 0x04010113.
Lemma F_660b0 : fetch_word Plain.M.loaded_segments (0x660f0 : word) = Some W_660b0.
Proof. vm_refl. Qed.
Lemma D_660b0 : decode_any W_660b0 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_660b4 : bv 32 := 0x00008067.
Lemma F_660b4 : fetch_word Plain.M.loaded_segments (0x660f4 : word) = Some W_660b4.
Proof. vm_refl. Qed.
Lemma D_660b4 : decode_any W_660b4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
End S1_code_65fec_660b8.

Module Lib_MakeString.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StepTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.WalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StartupTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SumWalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MemSplit OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ShapeAlg OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SRealizes OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefReadLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibEff OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MmapSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibMaskBits OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.S1Layout.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.CRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.StrLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.LiveStats OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContStmts3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.S1Facts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.Lib_Str_PushBack OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmInstS1.S1_code_65fec_660b8.
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

Lemma ms_chars_cons : forall x ws, ms_chars (x :: ws) =
  let (p, f) := take_nz (word_chars (x mod 2 ^ 32) 4) in if f then p else p ++ ms_chars ws.
Proof. reflexivity. Qed.

Lemma skipn_nth_cons : forall (k : nat) (ws : list Z), (k < length ws)%nat -> skipn k ws = nth k ws 0 :: skipn (S k) ws.
Proof.
  induction k as [|k IH]; intros ws Hk; destruct ws as [|y ws]; cbn in *; try lia; [reflexivity|].
  apply IH. lia.
Qed.
Lemma skipn_Znth : forall j ws, 0 <= j < Zlen ws -> skipn (Z.to_nat j) ws = Znth j ws :: skipn (Z.to_nat (j + 1)) ws.
Proof.
  intros j ws Hj. unfold Znth, Zlen in *. replace (Z.to_nat (j + 1)) with (S (Z.to_nat j)) by lia.
  apply skipn_nth_cons. lia.
Qed.

Lemma skipn_all_Z : forall ws : list Z, skipn (Z.to_nat (Zlen ws)) ws = [].
Proof. intros. apply skipn_all2. unfold Zlen. lia. Qed.

Lemma step_and_at {fx : FPState} : forall segs regs pc mem rom w rd rs1 rs2 v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op ALU_AND rd rs1 rs2, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_and (getr regs rs1) (getr regs rs2) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs1 rs2 v Hf He Hd Hrd Hv.
  rewrite (step_and segs regs pc mem rom w rd rs1 rs2 Hf He Hd). rewrite Hrd, Hv. reflexivity.
Qed.
Ltac stepand F D vv tac :=
  chain_step;
  [ reflexivity
  | eapply step_and_at with (v := vv); [ exact F | reflexivity | exact D | reflexivity | tac ]
  | step_simpl ].

Section EffW.
Context {AC : AllocCeiling}.
  Variable MI : MallocIface SEGS Ly.L.
  Lemma eff_widen : forall A A' M M' (W W' : Z * Z) F,
    eff MI A A' M M' W F -> (forall a, W_of W a -> W_of W' a) -> eff MI A A' M M' W' F.
  Proof using AC MI.
    intros A A' M M' W W' F [C B O FR D OI] HW. constructor.
    - exact C. - exact B. - exact O.
    - intros a Hn. apply FR. intros [H|[H|[H|[H|[H|H]]]]]; apply Hn.
      + left; exact H. + right; left; exact H. + right; right; left; exact H.
      + right; right; right; left; exact H.
      + right; right; right; right; left; apply HW; exact H.
      + right; right; right; right; right; exact H.
    - exact D.
    - exact OI.
  Qed.
End EffW.

Section MakeString.
Context {AC : AllocCeiling}.
  Variable MI : MallocIface SEGS Ly.L.
  Variable ST : StaticsIface SEGS Ly.L.
  Hypothesis MALLOC_STACK_pos : (0 <= MALLOC_STACK MI)%Z.
  Hypothesis NEW : new_rule_stmt SEGS Ly.L MI ST (NEW_STACK SEGS Ly.L MI).

  #[local] Notation placed_sep := (placed_sep SEGS Ly.L MI ly_img_low ly_rw_img).
  #[local] Notation stack_sep := (stack_sep SEGS Ly.L MI ly_img_low ly_rw_img).
  #[local] Notation offimg_sep := (offimg_sep SEGS Ly.L ST ly_rw_img ly_relro_img ly_errno_img).

  Section Body.
    Variables (fx : FPState) (A : AS MI) (s : SX ST) (R : bvmap 5 word) (M : mem) (model : Model).
    Variables (sp ret p w nw : Z) (ws : list Z) (K : TSet).
    Definition STK : Z := 128 + (16 + MALLOC_STACK MI).
    Hypothesis CB : callB MI ST A s R M model sp ret STK.
    Hypothesis Ha0 : getr R 10%bv = Z_to_bv 64 p.
    Hypothesis Ha1 : getr R 11%bv = Z_to_bv 64 w.
    Hypothesis Ha2 : getr R 12%bv = Z_to_bv 64 nw.
    Hypotheses (Hp0 : 0 <= p) (Hp1 : p + 24 <= 2 ^ 63) (HDp : mdef M p 24) (OBJp : obj_ok MI A sp STK p 24).
    Hypotheses (Hnw0 : 0 <= nw) (Hws : Zlen ws = nw) (Hw0 : 0 <= w) (Hw1 : w + 4 * nw <= 2 ^ 63).
    Hypothesis WS : forall i, 0 <= i < nw -> 0 <= Znth i ws < 2 ^ 32 /\ fld SEGS M (w + 4 * i) 4 (Znth i ws).
    Hypothesis OBJw : obj_ok MI A sp STK w (4 * nw).
    Hypothesis DJ : forall a, zwin w (w + 4 * nw) a -> ~ zwin p (p + 24) a.
    Hypothesis HNMAX : 8 * nw + 48 <= NMAX MI.
    Hypothesis ROOM : forall n, str_gsize n -> n <= 8 * nw + 2 ->
       (n < BIG MI -> count_class SEGS Ly.L MI A (size_class MI n) + 2 <= caps MI A (size_class MI n)
                      /\ count_class SEGS Ly.L MI A (size_class MI n + 1) + 2 <= caps MI A (size_class MI n + 1))
       /\ (BIG MI <= n -> big_bytes SEGS Ly.L MI A + 2 * round_big MI n <= bigcap MI A).
    Hypothesis CONT : forall A' R' M' model' (m' : sbuf) (J : Z -> Prop),
        retB MI ST A' s R R' M' model model' ->
        str_rep MI A' M' p m' (ms_chars ws) ->
        (forall q k, In (q, k) (live MI A') <-> In (q, k) (live MI A) \/ In (q, k) (str_blocks m')) ->
        (forall q k, In (q, k) (str_blocks m') -> ~ In q (map fst (live MI A))) ->
        junk_ok MI A J ->
        sbuf_asz_le m' (8 * nw + 2) ->
        eff MI A A' M M' (sp - STK, sp) (fun a => zwin p (p + 24) a \/ sbuf_fp m' a \/ J a) ->
        srealizes SEGS (mkCfg (@mkst fx R' (Z_to_bv 64 ret) M' (seg_rom SEGS)) model') K.

    Definition Wn : Z * Z := (sp - STK, sp).

    Record INV (A' : AS MI) (M' : mem) (model' : Model) (m' : sbuf) (cs' : list Z) (J : Z -> Prop) : Prop := MKINV {
      iv_ainv : ainv MI A' M' model';
      iv_mstd : mstd model';
      iv_fs   : m_fs model' = m_fs model /\ m_fds model' = m_fds model;
      iv_sx   : sx_inv ST s M';
      iv_roc  : img_ro_clear Ly.L M';
      iv_sl1  : rdn SEGS M' (Z_to_bv 64 (sp - 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 ret));
      iv_sl2  : rdn SEGS M' (Z_to_bv 64 (sp - 16)) 8 = Some (word_to_le_bytes 8 (getr R 8%bv));
      iv_sl3  : rdn SEGS M' (Z_to_bv 64 (sp - 24)) 8 = Some (word_to_le_bytes 8 (getr R 9%bv));
      iv_sl4  : rdn SEGS M' (Z_to_bv 64 (sp - 32)) 8 = Some (word_to_le_bytes 8 (getr R 18%bv));
      iv_sl5  : rdn SEGS M' (Z_to_bv 64 (sp - 40)) 8 = Some (word_to_le_bytes 8 (getr R 19%bv));
      iv_sl6  : rdn SEGS M' (Z_to_bv 64 (sp - 48)) 8 = Some (word_to_le_bytes 8 (getr R 20%bv));
      iv_sl7  : rdn SEGS M' (Z_to_bv 64 (sp - 56)) 8 = Some (word_to_le_bytes 8 (getr R 21%bv));
      iv_str  : str_rep MI A' M' p m' cs';
      iv_gs   : m' = SShort \/ exists d asz, m' = SLong d asz /\ str_gsize asz /\ asz <= 8 * nw + 2;
      iv_lv   : forall q k, In (q, k) (live MI A') <-> In (q, k) (live MI A) \/ In (q, k) (str_blocks m');
      iv_dj   : forall q k, In (q, k) (str_blocks m') -> ~ In q (map fst (live MI A));
      iv_caps : caps MI A' = caps MI A /\ bigcap MI A' = bigcap MI A;
      iv_junk : junk_ok MI A J;
      iv_eff  : eff MI A A' M M' Wn (fun a => zwin p (p + 24) a \/ sbuf_fp m' a \/ J a);
      iv_win  : mdef M' (sp - STK) STK;
      iv_wdef : mdef M' w (4 * nw);
      iv_ws   : forall i, 0 <= i < nw -> fld SEGS M' (w + 4 * i) 4 (Znth i ws)
    }.

    Record REGS (R' : bvmap 5 word) (j : Z) (x : word) : Prop := MKREGS {
      rg_sp : getr R' 2%bv = Z_to_bv 64 (sp - 64);
      rg_s0 : getr R' 8%bv = Z_to_bv 64 (w + 4 * j);
      rg_s1 : getr R' 9%bv = Z_to_bv 64 p;
      rg_s2 : getr R' 18%bv = Z_to_bv 64 (4 * (nw - j));
      rg_s3 : getr R' 19%bv = Z_to_bv 64 0xff00;
      rg_s4 : getr R' 20%bv = Z_to_bv 64 0xff0000;
      rg_s5 : getr R' 21%bv = x;
      rg_gp : getr R' 3%bv = getr R 3%bv;
      rg_tp : getr R' 4%bv = getr R 4%bv;
      rg_hi : forall r, In r [22; 23; 24; 25; 26; 27]%bv -> getr R' r = getr R r
    }.
    #[local] Ltac dCB := destruct CB as [AI MS ROC SXI SXH CR Hceil HROOM Hwin Hown_sx Herr_sx].

    Lemma Hspr : alloc_ceiling + STK <= sp /\ sp < 2 ^ 47 /\ sp mod 16 = 0 /\ 2 ^ 24 <= sp - STK /\ 0 <= MALLOC_STACK MI /\ STK = 128 + (16 + MALLOC_STACK MI).
    Proof using AC MI ST MALLOC_STACK_pos A s R M model sp ret CB. dCB. destruct CR. pose proof ac_bounds_lit. unfold STK in *. lia. Qed.

    Lemma WINp : p + 24 <= sp - STK \/ sp <= p.
    Proof using AC MI MALLOC_STACK_pos A sp p OBJp.
      destruct OBJp as [_ W]. unfold STK in *.
      destruct (Z.lt_ge_cases p sp); [left|right; lia].
      destruct (Z.lt_ge_cases (p + 24) (sp - (128 + (16 + MALLOC_STACK MI)) + 1)); [lia|]. exfalso.
      destruct (Z.lt_ge_cases p (sp - (128 + (16 + MALLOC_STACK MI)))).
      - apply (W (sp - (128 + (16 + MALLOC_STACK MI)))); unfold zwin; lia.
      - apply (W p); unfold zwin; lia.
    Qed.

    Lemma WINw : w + 4 * nw <= sp - STK \/ sp <= w \/ nw = 0.
    Proof using AC MI MALLOC_STACK_pos A sp w nw Hnw0 OBJw.
      destruct OBJw as [_ W]. unfold STK in *.
      destruct (Z.eq_dec nw 0); [right; right; lia|].
      destruct (Z.lt_ge_cases w sp); [left|right; left; lia].
      destruct (Z.lt_ge_cases (w + 4 * nw) (sp - (128 + (16 + MALLOC_STACK MI)) + 1)); [lia|]. exfalso.
      destruct (Z.lt_ge_cases w (sp - (128 + (16 + MALLOC_STACK MI)))).
      - apply (W (sp - (128 + (16 + MALLOC_STACK MI)))); unfold zwin; lia.
      - apply (W w); unfold zwin; lia.
    Qed.

    Lemma rdn_noseg_mdef : forall Mx a (k : nat) bs,
      rdn SEGS Mx (Z_to_bv 64 a) k = Some bs -> 0 <= a -> a + Z.of_nat k < 2 ^ 64 ->
      (forall x, a <= x < a + Z.of_nat k -> find_segment SEGS x 1 = None) -> mdef Mx a (Z.of_nat k).
    Proof using.
      intros Mx a k. revert a. induction k as [|k IH]; intros a bs HR Ha Hk Hseg i Hi; [lia|].
      cbn [rdn] in HR.
      destruct (Mx (Z_to_bv 64 a)) as [b0|] eqn:Hm.
      - destruct (Z.eq_dec i 0) as [->|Hne]; [rewrite Z.add_0_r, Hm; discriminate|].
        destruct (rdn SEGS Mx (Z_to_bv 64 a + 1) k) as [rest|] eqn:HR'; [|discriminate].
        replace (Z_to_bv 64 a + 1)%bv with (Z_to_bv 64 (a + 1)) in HR'
          by (apply bv_eq; rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod; change (bv_unsigned (1%bv : bv 64)) with 1;
              rewrite (Z.mod_small (a + 1)), (Z.mod_small a), Z.mod_small by lia; reflexivity).
        replace (a + i) with (a + 1 + (i - 1)) by lia. apply (IH (a + 1) rest HR'); try lia. intros x Hx. apply Hseg. lia.
      - exfalso. unfold seg_rom, memory_read in HR. rewrite u64_of_Z in HR by lia.
        change (Z.of_N 1) with 1 in HR. rewrite (Hseg a) in HR by lia. discriminate.
    Qed.

    Lemma WDEF0 : mdef M w (4 * nw).
    Proof using AC MI ST A s R M model sp ret w nw ws CB Hws Hw1 WS OBJw.
      dCB. destruct OBJw as [PL _]. pose proof ac_bounds_lit as Hcv.
      destruct PL as [Hst|(q & k & Hin & Hq & Hqk)].
      - intros i Hi. pose proof (Z.div_mod i 4 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound i 4 ltac:(lia)) as Hmb.
        set (q4 := i / 4) in *. set (r4 := i mod 4) in *.
        pose proof (WS q4 ltac:(lia)) as [_ HF]. unfold fld in HF.
        pose proof (rdn_noseg_mdef M (w + 4 * q4) 4 _ HF ltac:(lia) ltac:(cbn; lia)) as HD.
        specialize (HD ltac:(intros x Hx; apply ly_noseg; lia)).
        replace (w + i) with (w + 4 * q4 + r4) by lia. apply HD. cbn. lia.
      - intros i Hi. destruct (ai_live_block MI A M model q k AI Hin) as (_ & _ & _ & _ & Hown).
        apply (proj2 (proj2 (Hown (w + i) ltac:(lia)))).
    Qed.

    Lemma inv_blk : forall A' M' model' m' cs' J d asz,
      INV A' M' model' m' cs' J -> m' = SLong d asz ->
      In (d, asz) (live MI A') /\ ~ In d (map fst (live MI A)) /\ 0 < d /\ d + asz <= alloc_ceiling /\ 0 <= asz /\
      (forall a, d <= a < d + asz -> ~ owned MI A' a /\ ~ in_ranges (ly_img Ly.L) a /\ M' (Z_to_bv 64 a) <> None) /\
      (forall q k, In (q, k) (live MI A) -> d + asz <= q \/ q + k <= d).
    Proof using AC MI ST A s R M model sp ret p w nw ws.
      intros A' M' model' m' cs' J d asz IV ->.
      destruct IV as [AI' MS' FS' SX' ROC' SL1 SL2 SL3 SL4 SL5 SL6 SL7 STR GS LV DJ' CAPS JK EFF WIN WDEF WSM].
      assert (Hin : In (d, asz) (live MI A')) by (apply (str_blocks_live MI _ _ _ _ _ STR); left; reflexivity).
      assert (Hnd : ~ In d (map fst (live MI A))) by (apply (DJ' d asz); left; reflexivity).
      destruct (ai_live_block MI A' M' model' d asz AI' Hin) as (H0 & H16 & Hd & Hce & Hown).
      repeat (split; [first [assumption | lia] |]).
      intros q k Hq. assert (Hq' : In (q, k) (live MI A')) by (apply LV; left; exact Hq).
      assert (Hne : d <> q) by (intros ->; apply Hnd; apply in_map_iff; exists (q, k); split; [reflexivity|exact Hq]).
      destruct (ai_live_disjoint MI A' M' model' d asz q k AI' Hin Hq' Hne); lia.
    Qed.

    Lemma inv_fp : forall A' M' model' m' cs' J a,
      INV A' M' model' m' cs' J -> (zwin p (p + 24) a \/ sbuf_fp m' a \/ J a) ->
      ~ in_ranges (ly_img Ly.L) a /\ ~ (sp - STK <= a < sp).
    Proof using AC MI ST MALLOC_STACK_pos A s R M model sp ret p w nw ws CB OBJp.
      intros A' M' model' m' cs' J a IV HF. pose proof Hspr as (Hc & _ & _ & _ & _ & HSTK). pose proof WINp as WP.
      pose proof IV as IV'. destruct IV as [AI' MS' FS' SX' ROC' SL1 SL2 SL3 SL4 SL5 SL6 SL7 STR GS LV DJ' CAPS JK EFF WIN WDEF WSM].
      destruct HF as [Ho|[Hs|Hj]].
      - dCB. destruct OBJp as [PL _]. destruct (placed_sep A M model p 24 a AI PL ltac:(unfold zwin in Ho; lia)) as [X1 X2].
        split; [exact X2|]. unfold zwin in Ho. lia.
      - destruct m' as [|d asz]; cbn [sbuf_fp] in Hs; [destruct Hs|]. unfold zwin in Hs.
        destruct (inv_blk A' M' model' (SLong d asz) cs' J d asz IV' eq_refl) as (Hin & Hnd & Hd & Hce & H0 & Hown & Hdisj).
        split; [exact (proj1 (proj2 (Hown a Hs)))|]. lia.
      - destruct (JK a Hj) as (H1 & H2 & H3). split; [exact H2 | lia].
    Qed.

    Lemma inv_callB : forall A' M' model' m' cs' J R1 ra,
      INV A' M' model' m' cs' J ->
      getr R1 2%bv = Z_to_bv 64 (sp - 64) -> getr R1 1%bv = Z_to_bv 64 ra -> ret_ok (Z_to_bv 64 ra) -> 0 <= ra < 2 ^ 64 ->
      getr R1 3%bv = getr R 3%bv -> getr R1 4%bv = getr R 4%bv ->
      callB MI ST A' s R1 M' model' (sp - 64) ra (64 + (16 + MALLOC_STACK MI)).
    Proof using AC MI ST MALLOC_STACK_pos A s R M model sp ret p w nw ws CB OBJp.
      intros A' M' model' m' cs' J R1 ra IV H2 H1 Hret Hra H3 H4.
      pose proof Hspr as (Hc & Hs47 & Hs16 & Hs20 & HMS & HSTK). pose proof IV as IV'.
      destruct IV as [AI' MS' FS' SX' ROC' SL1 SL2 SL3 SL4 SL5 SL6 SL7 STR GS LV DJ' CAPS JK EFF WIN WDEF WSM]. dCB. destruct CR.
      constructor.
      - exact AI'. - exact MS'. - exact ROC'. - exact SX'. - exact SXH.
      - constructor; try assumption.
        + replace (sp - 64) with (sp - 16 * 4) by lia. apply mod16_sub. exact Hs16.
        + lia.
        + rewrite H3. assumption.
        + rewrite H4. assumption.
      - unfold STK in Hc. lia.
      - unfold stack_room. replace (sp - 64 - (64 + (16 + MALLOC_STACK MI))) with (sp - STK + 0) by (unfold STK; lia).
        apply (mdef_store_ok_off SEGS M' (sp - STK) STK 0 _ WIN); unfold STK in *; lia.
      - intros a Ha. unfold zwin, STK in *. split.
        + apply (stack_sep A' M' model' a AI'). lia.
        + apply (proj2 (Hwin a ltac:(unfold zwin; lia))).
      - intros a Ho. destruct EFF as [_ _ OWN _ _ _]. destruct (OWN a Ho) as [HoA|[Hnm|HF]].
        + exact (Hown_sx a HoA).
        + destruct Hnm as (Hni & _). exact (proj1 (offimg_sep a Hni)).
        + exact (proj1 (offimg_sep a (proj1 (inv_fp A' M' model' m' cs' J a IV' HF)))).
      - exact Herr_sx.
    Qed.

    Lemma inv_obj : forall A' M' model' m' cs' J,
      INV A' M' model' m' cs' J -> obj_ok MI A' (sp - 64) (64 + (16 + MALLOC_STACK MI)) p 24.
    Proof using AC MI ST A s R M model sp ret p w nw ws OBJp.
      intros A' M' model' m' cs' J IV. destruct IV as [AI' MS' FS' SX' ROC' SL1 SL2 SL3 SL4 SL5 SL6 SL7 STR GS LV DJ' CAPS JK EFF WIN WDEF WSM].
      destruct OBJp as [PL W]. split.
      - eapply (placed_mono SEGS Ly.L MI); [|exact PL]. intros blk Hb. destruct blk as [q k]. apply LV. left. exact Hb.
      - intros a Ha Hw. apply (W a Ha). unfold zwin, STK in *. lia.
    Qed.

    Lemma inv_room : forall A' M' model' m' cs' J,
      INV A' M' model' m' cs' J -> Zlen cs' < 4 * nw ->
      Zlen cs' = str_cap m' -> str_grow m' <= NMAX MI /\ roomL MI A' (live MI A') (str_grow m').
    Proof using AC MI ST A s R M model sp ret p w nw ws CB Hws HNMAX ROOM.
      intros A' M' model' m' cs' J IV Hlt Hfull. pose proof IV as IV'.
      destruct IV as [AI' MS' FS' SX' ROC' SL1 SL2 SL3 SL4 SL5 SL6 SL7 STR GS LV DJ' CAPS JK EFF WIN WDEF WSM]. dCB.
      pose proof (ai_nmax_bound MI) as HNM. pose proof (ai_big_pos MI) as HBIG.
      assert (Hgs : str_gsize (str_grow m') /\ str_grow m' <= 8 * nw + 2 /\ str_grow m' <= NMAX MI
                    /\ (forall d asz, m' = SLong d asz -> 0 <= asz <= str_grow m')).
      { destruct GS as [-> | (d & asz & -> & (k & Hk & Hasz) & Hle8)]; cbn [str_grow str_cap] in *.
        - unfold SSO_CAP in Hfull. split; [exists 0; split; [lia|reflexivity] |]. split; [lia|]. split; [lia|]. intros; discriminate.
        - assert (0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
          split; [exists (k + 1); split; [lia|]; rewrite Z.pow_add_r by lia; change (2 ^ 1) with 2; lia |].
          split; [lia|]. split; [lia|]. intros d' asz' Heq. inversion Heq; subst. lia. }
      destruct Hgs as (Hg1 & Hg2 & Hg3 & Hasz). split; [exact Hg3|].
      destruct (ROOM _ Hg1 Hg2) as [RS RB].
      assert (NDA : NoDup (map fst (live MI A))) by (eapply ai_live_nodup; exact AI).
      assert (ND' : NoDup (map fst (live MI A'))) by (eapply ai_live_nodup; exact AI').
      assert (NDB : NoDup (map fst (live MI A ++ str_blocks m'))).
      { apply NoDup_fst_app; [exact NDA | | exact DJ']. destruct m'; cbn [str_blocks]; [apply NoDup_fst_nil | apply NoDup_fst_single]. }
      assert (EQV : forall q k, In (q, k) (live MI A') <-> In (q, k) (live MI A ++ str_blocks m')).
      { intros q k. rewrite in_app_iff. apply LV. }
      unfold roomL. destruct CAPS as [-> ->]. unfold count_class, big_bytes in RS, RB.
      split.
      - intros Hsm. destruct (RS Hsm) as [R1 R2].
        rewrite !(live_equiv_count _ _ _ _ _ ND' NDB EQV), !count_class_f_app.
        assert (HB : forall c, count_class_f (size_class MI) (BIG MI) (str_blocks m') c <= 1).
        { intros c. destruct m'; cbn [str_blocks count_class_f]; [lia|]. destruct (_ && _); lia. }
        pose proof (HB (size_class MI (str_grow m'))). pose proof (HB (size_class MI (str_grow m') + 1)). lia.
      - intros Hbg. specialize (RB Hbg).
        rewrite (live_equiv_big _ _ _ _ ND' NDB EQV), big_bytes_f_app.
        assert (HB : big_bytes_f (round_big MI) (BIG MI) (str_blocks m') <= round_big MI (str_grow m')).
        { destruct m' as [|d asz]; cbn [str_blocks big_bytes_f].
          - apply (ai_round_big_nonneg MI). lia.
          - specialize (Hasz d asz eq_refl). destruct (Z.leb_spec (BIG MI) asz).
            + rewrite Z.add_0_r. apply (ai_round_big_mono MI). lia.
            + pose proof (ai_round_big_nonneg MI (str_grow (SLong d asz)) ltac:(lia)). lia. }
        lia.
    Qed.

    Lemma blk_sep : forall A' M' model' d asz,
      ainv MI A' M' model' -> In (d, asz) (live MI A') -> ~ In d (map fst (live MI A)) ->
      (forall q k, In (q, k) (live MI A) -> In (q, k) (live MI A')) ->
      0 < d /\ d + asz <= alloc_ceiling /\ 0 <= asz /\
      (forall a, d <= a < d + asz -> ~ owned MI A' a /\ ~ in_ranges (ly_img Ly.L) a /\ M' (Z_to_bv 64 a) <> None) /\
      (forall q k, In (q, k) (live MI A) -> d + asz <= q \/ q + k <= d) /\
      (forall a, d <= a < d + asz -> ~ (w <= a < w + 4 * nw) /\ ~ (p <= a < p + 24) /\ ~ (sp - STK <= a < sp)).
    Proof using AC MI ST MALLOC_STACK_pos A s R M model sp ret p w nw CB OBJp OBJw.
      intros A' M' model' d asz AI' Hin Hnd HL. pose proof Hspr as (Hc & _ & _ & _ & _ & HSTK). dCB.
      destruct (ai_live_block MI A' M' model' d asz AI' Hin) as (H0 & H16 & Hd & Hce & Hown).
      assert (Hdisj : forall q k, In (q, k) (live MI A) -> d + asz <= q \/ q + k <= d).
      { intros q k Hq. assert (Hne : d <> q) by (intros ->; apply Hnd; apply in_map_iff; exists (q, k); split; [reflexivity|exact Hq]).
        destruct (ai_live_disjoint MI A' M' model' d asz q k AI' Hin (HL _ _ Hq) Hne); lia. }
      repeat (split; [first [assumption | lia] |]).
      intros a Ha. split; [|split].
      - destruct OBJw as [[Hst|(q & k & Hq & H1 & H2)] _]; [lia|]. destruct (Hdisj q k Hq); lia.
      - destruct OBJp as [[Hst|(q & k & Hq & H1 & H2)] _]; [lia|]. destruct (Hdisj q k Hq); lia.
      - lia.
    Qed.

    Lemma grow_gsize : forall m', (m' = SShort \/ exists d asz, m' = SLong d asz /\ str_gsize asz) -> str_gsize (str_grow m').
    Proof using.
      intros m' [-> | (d & asz & -> & (k & Hk & Hasz))]; cbn [str_grow].
      - exists 0. split; [lia|reflexivity].
      - exists (k + 1). split; [lia|]. rewrite Z.pow_add_r by lia. change (2 ^ 1) with 2. lia.
    Qed.

    Lemma inv_post : forall A' M' model' m' cs' J R1 A'' R'' M'' model'' m'' c,
      INV A' M' model' m' cs' J -> Zlen cs' < 4 * nw ->
      retB MI ST A'' s R1 R'' M'' model' model'' ->
      str_rep MI A'' M'' p m'' (cs' ++ [c]) ->
      (Zlen cs' < str_cap m' /\ m'' = m' /\ live MI A'' = live MI A'
       \/ Zlen cs' = str_cap m' /\ (exists d', m'' = SLong d' (str_grow m') /\
            lapply (live MI A') (LAdd d' (str_grow m') :: sbuf_del m') (live MI A''))) ->
      eff MI A' A'' M' M'' (sp - 64 - (64 + (16 + MALLOC_STACK MI)), sp - 64)
          (fun a => zwin p (p + 24) a \/ sbuf_fp m' a \/ sbuf_fp m'' a) ->
      INV A'' M'' model'' m'' (cs' ++ [c]) (fun a => J a \/ sbuf_fp m' a).
    Proof using AC MI ST MALLOC_STACK_pos A s R M model sp ret p w nw ws CB Hp0 OBJp Hnw0 Hws Hw0 Hw1 OBJw DJ.
      intros A' M' model' m' cs' J R1 A'' R'' M'' model'' m'' c IV Hlt4 RB STR'' ALT EFF2.
      pose proof Hspr as (Hc & Hs47 & Hs16 & Hs20 & HMS & HSTK). pose proof ac_bounds_lit as Hcv. pose proof WINp as WP. pose proof WINw as WW.
      pose proof IV as IV'.
      destruct IV as [AI' MS' FS' SX' ROC' SL1 SL2 SL3 SL4 SL5 SL6 SL7 STR GS LV DJ' CAPS JK EFF WIN WDEF WSM].
      destruct RB as [AI'' MS'' Hfs'' Hfds'' SX'' KEPT''].
      pose proof CB as CB'. dCB.
      assert (LA : forall q k, In (q, k) (live MI A) -> In (q, k) (live MI A')) by (intros q k Hq; apply LV; left; exact Hq).

      assert (NEWST : (forall q k, In (q, k) (live MI A'') <-> In (q, k) (live MI A) \/ In (q, k) (str_blocks m''))
                      /\ (forall q k, In (q, k) (str_blocks m'') -> ~ In q (map fst (live MI A)))
                      /\ (m'' = SShort \/ exists d asz, m'' = SLong d asz /\ str_gsize asz /\ asz <= 8 * nw + 2)).
      { destruct ALT as [(Hlt & -> & HLeq) | (Hfull & d' & -> & LAP)].
        - rewrite HLeq. split; [exact LV|]. split; [exact DJ'|exact GS].
        - cbn [lapply] in LAP. destruct LAP as (lv1 & [-> Hnin] & LAP).
          assert (Hnd' : ~ In d' (map fst (live MI A))).
          { intros Hin. apply Hnin. apply in_map_iff in Hin. destruct Hin as ([q k] & Hq & Hin). cbn in Hq. subst q.
            apply in_map_iff. exists (d', k). split; [reflexivity|]. apply LA. exact Hin. }
          assert (Hgrow8 : str_grow m' <= 8 * nw + 2).
          { pose proof STR as (_ & _ & _ & HlenS & _). destruct m' as [|d0 asz0]; cbn [str_grow str_cap] in *; [unfold SSO_CAP in *; lia | lia]. }
          assert (GSo : m' = SShort \/ exists d asz, m' = SLong d asz /\ str_gsize asz).
          { destruct GS as [G0|(d0 & asz0 & G1 & G2 & _)]; [left; exact G0 | right; exists d0, asz0; split; [exact G1 | exact G2]]. }
          split; [|split; [intros q k [Heq|[]]; inversion Heq; subst; exact Hnd' | right; exists d', (str_grow m'); split; [reflexivity | split; [apply grow_gsize; exact GSo | exact Hgrow8]]]].
          destruct m' as [|d asz]; cbn [sbuf_del lapply str_blocks] in *.
          + intros q k. rewrite LAP. cbn [In]. rewrite LV. cbn [In]. clear. intuition.
          + destruct LAP as (lv2 & HDL & ->).
            assert (Hdd : d' <> d).
            { intros ->. apply Hnin. apply in_map_iff. exists (d, asz). split; [reflexivity|].
              apply (str_blocks_live MI _ _ _ _ _ STR). left. reflexivity. }
            assert (HdA : ~ In d (map fst (live MI A))) by (apply (DJ' d asz); left; reflexivity).
            intros q k. rewrite (HDL q k). cbn [In]. rewrite LV. cbn [In]. split.
            * intros [[H|[H|[H|[]]]] Hne]; [right; left; exact H | left; exact H | exfalso; inversion H; subst; apply Hne; reflexivity].
            * intros [H|[H|[]]].
              -- split; [right; left; exact H|]. intros ->. apply HdA. apply in_map_iff. exists (d, k). split; [reflexivity|exact H].
              -- split; [left; exact H|]. inversion H; subst. exact Hdd. }
      destruct NEWST as (LV'' & DJ'' & GS'').
      assert (LA'' : forall q k, In (q, k) (live MI A) -> In (q, k) (live MI A'')) by (intros q k Hq; apply LV''; left; exact Hq).

      assert (BO : forall a, sbuf_fp m' a -> a < alloc_ceiling /\ 0 < a /\ ~ in_ranges (ly_img Ly.L) a /\
                     ~ (w <= a < w + 4 * nw) /\ ~ (p <= a < p + 24) /\ ~ (sp - STK <= a < sp) /\
                     (forall q k, In (q, k) (live MI A) -> ~ (q <= a < q + k))).
      { intros a Hs. destruct m' as [|d asz]; cbn [sbuf_fp] in Hs; [destruct Hs|]. unfold zwin in Hs.
        destruct (blk_sep A' M' model' d asz AI' ltac:(apply (str_blocks_live MI _ _ _ _ _ STR); left; reflexivity)
                    ltac:(apply (DJ' d asz); left; reflexivity) LA) as (Hd & Hce & H0 & Hown & Hdisj & Hsep).
        destruct (Hsep a Hs) as (X1 & X2 & X3). destruct (Hown a Hs) as (_ & Xi & _).
        repeat (split; [first [assumption | lia] |]). intros q k Hq. destruct (Hdisj q k Hq); lia. }
      assert (BN : forall a, sbuf_fp m'' a -> a < alloc_ceiling /\ 0 < a /\ ~ in_ranges (ly_img Ly.L) a /\
                     ~ (w <= a < w + 4 * nw) /\ ~ (p <= a < p + 24) /\ ~ (sp - STK <= a < sp) /\
                     (forall q k, In (q, k) (live MI A) -> ~ (q <= a < q + k))).
      { intros a Hs. destruct m'' as [|d asz]; cbn [sbuf_fp] in Hs; [destruct Hs|]. unfold zwin in Hs.
        destruct (blk_sep A'' M'' model'' d asz AI'' ltac:(apply (str_blocks_live MI _ _ _ _ _ STR''); left; reflexivity)
                    ltac:(apply (DJ'' d asz); left; reflexivity) LA'') as (Hd & Hce & H0 & Hown & Hdisj & Hsep).
        destruct (Hsep a Hs) as (X1 & X2 & X3). destruct (Hown a Hs) as (_ & Xi & _).
        repeat (split; [first [assumption | lia] |]). intros q k Hq. destruct (Hdisj q k Hq); lia. }

      pose proof EFF2 as EFF2'. destruct EFF2 as [C2 B2 O2 FR2 D2 OI2].
      assert (PLw' : placed MI A' w (4 * nw)) by (eapply (placed_mono SEGS Ly.L MI); [|exact (proj1 OBJw)]; intros [q k] Hb; apply LA; exact Hb).
      assert (PLw'' : placed MI A'' w (4 * nw)) by (eapply (placed_mono SEGS Ly.L MI); [|exact (proj1 OBJw)]; intros [q k] Hb; apply LA''; exact Hb).
      assert (AGX : forall a, (sp - 64 <= a < sp) \/ (w <= a < w + 4 * nw) -> M'' (Z_to_bv 64 a) = M' (Z_to_bv 64 a)).
      { intros a Ha. assert (Hr : 0 <= a < 2 ^ 64) by lia.
        apply FR2. rewrite u64_of_Z by lia. intros [Ho|[Ho|[Hn|[HF|[HW|He]]]]].
        - destruct Ha as [Ha|Ha]; [exact (proj1 (stack_sep A' M' model' a AI' ltac:(unfold STK in Hc; lia)) Ho) | exact (proj1 (placed_sep A' M' model' w (4 * nw) a AI' PLw' Ha) Ho)].
        - destruct Ha as [Ha|Ha]; [exact (proj1 (stack_sep A'' M'' model'' a AI'' ltac:(unfold STK in Hc; lia)) Ho) | exact (proj1 (placed_sep A'' M'' model'' w (4 * nw) a AI'' PLw'' Ha) Ho)].
        - destruct Hn as (_ & _ & Hn). destruct Ha as [Ha|Ha]; [exact (WIN (a - (sp - STK)) ltac:(unfold STK in *; lia) ltac:(replace (sp - STK + (a - (sp - STK))) with a by lia; exact Hn)) |].
          exact (WDEF (a - w) ltac:(lia) ltac:(replace (w + (a - w)) with a by lia; exact Hn)).
        - destruct HF as [Hob|[Hs1|Hs2]].
          + unfold zwin in Hob. destruct Ha as [Ha|Ha]; [unfold STK in WP; lia | exact (DJ a ltac:(unfold zwin; lia) ltac:(unfold zwin; lia))].
          + destruct (BO a Hs1) as (X1 & X2 & X3 & X4 & X5 & X6 & X7). destruct Ha as [Ha|Ha]; [unfold STK in X6; lia | exact (X4 Ha)].
          + destruct (BN a Hs2) as (X1 & X2 & X3 & X4 & X5 & X6 & X7). destruct Ha as [Ha|Ha]; [unfold STK in X6; lia | exact (X4 Ha)].
        - unfold W_of in HW. cbn in HW. destruct Ha as [Ha|Ha]; [lia|]. unfold STK in WW. lia.
        - pose proof (ly_img_low a (ly_errno_img a He)) as Hi. destruct Ha as [Ha|Ha]; [lia|].
          exact (proj2 (placed_sep A' M' model' w (4 * nw) a AI' PLw' Ha) (ly_errno_img a He)). }
      assert (SLT : forall a vv, sp - 64 <= a -> a + 8 <= sp -> rdn SEGS M' (Z_to_bv 64 a) 8 = Some vv -> rdn SEGS M'' (Z_to_bv 64 a) 8 = Some vv).
      { intros a vv H1 H2 H3. rewrite <- H3. apply rdn_agree_win; [lia | cbn; lia |]. intros x Hx. apply AGX. left. unfold zwin in Hx. cbn in Hx. lia. }
      constructor.
      - exact AI''.
      - exact MS''.
      - rewrite Hfs'', Hfds''. exact FS'.
      - exact SX''.
      - eapply (roc_frame Ly.L); [exact ROC' | exact FR2 |]. intros a [Ho|[Ho|[Hn|[HF|[HW|He]]]]].
        + exact (roc_owned SEGS Ly.L MI A' M' model' a AI' Ho).
        + exact (roc_owned SEGS Ly.L MI A'' M'' model'' a AI'' Ho).
        + right. exact (proj1 Hn).
        + right. destruct HF as [Hob|[Hs1|Hs2]].
          * exact (proj2 (placed_sep A M model p 24 a AI (proj1 OBJp) ltac:(unfold zwin in Hob; lia))).
          * exact (proj1 (proj2 (proj2 (BO a Hs1)))).
          * exact (proj1 (proj2 (proj2 (BN a Hs2)))).
        + right. unfold W_of in HW. cbn in HW. apply (proj2 (stack_sep A' M' model' a AI' ltac:(lia))).
        + left. apply ly_errno_rw. exact He.
      - apply SLT; [lia|lia|exact SL1].
      - apply SLT; [lia|lia|exact SL2].
      - apply SLT; [lia|lia|exact SL3].
      - apply SLT; [lia|lia|exact SL4].
      - apply SLT; [lia|lia|exact SL5].
      - apply SLT; [lia|lia|exact SL6].
      - apply SLT; [lia|lia|exact SL7].
      - exact STR''.
      - exact GS''.
      - exact LV''.
      - exact DJ''.
      - rewrite C2, B2. exact CAPS.
      - intros a [Hj|Hs]; [exact (JK a Hj)|]. destruct (BO a Hs) as (X1 & X2 & X3 & X4 & X5 & X6 & X7).
        split; [lia|]. split; [exact X3|]. exact X7.
      - eapply eff_weaken.
        + eapply (eff_trans MI); [exact EFF | | intros a Ha; apply (stack_sep A'' M'' model'' a AI''); unfold W_of, Wn in Ha; cbn in Ha; lia].
          eapply eff_widen; [exact EFF2'|]. intros a Ha. unfold W_of, Wn in *. cbn in *. lia.
        + intros a [[H|[H|H]]|[H|[H|H]]]; [left | right; right; right | right; right; left | left | right; right; right | right; left]; exact H.
      -
        intros i Hi. destruct (D2 (sp - STK + i) ltac:(lia) (WIN i Hi)) as [H|[Ho|[HF|He]]];
          [exact H| | | exfalso; pose proof (ly_img_low _ (ly_errno_img _ He)); lia].
        + exfalso. exact (proj1 (stack_sep A' M' model' (sp - STK + i) AI' ltac:(lia)) Ho).
        + exfalso. destruct HF as [Hob|[Hs1|Hs2]].
          * unfold zwin in Hob. lia.
          * destruct (BO _ Hs1) as (X1 & X2 & X3 & X4 & X5 & X6 & X7). lia.
          * destruct (BN _ Hs2) as (X1 & X2 & X3 & X4 & X5 & X6 & X7). lia.
      - intros i Hi. destruct (D2 (w + i) ltac:(lia) (WDEF i Hi)) as [H|[Ho|[HF|He]]];
          [exact H| | | exfalso; exact (proj2 (placed_sep A' M' model' w (4 * nw) (w + i) AI' PLw' ltac:(lia)) (ly_errno_img _ He))].
        + exfalso. exact (proj1 (placed_sep A' M' model' w (4 * nw) (w + i) AI' PLw' ltac:(lia)) Ho).
        + exfalso. destruct HF as [Hob|[Hs1|Hs2]].
          * exact (DJ (w + i) ltac:(unfold zwin; lia) Hob).
          * destruct (BO _ Hs1) as (X1 & X2 & X3 & X4 & X5 & X6 & X7). lia.
          * destruct (BN _ Hs2) as (X1 & X2 & X3 & X4 & X5 & X6 & X7). lia.
      - intros i Hi. eapply fld_agree; [lia | cbn; lia | exact (WSM i Hi) |].
        intros a Ha. apply AGX. right. unfold zwin in Ha. cbn in Ha. lia.
    Qed.
    #[local] Ltac dIV IV := destruct IV as [AI' MS' FS' SX' ROC' SL1 SL2 SL3 SL4 SL5 SL6 SL7 STR GS LV DJ' CAPS JK EFF WIN WDEF WSM].

    Lemma EXIT : forall A' R' M' model' m' cs' J,
      INV A' M' model' m' cs' J -> ms_chars ws = cs' ->
      getr R' 2%bv = Z_to_bv 64 (sp - 64) -> getr R' 3%bv = getr R 3%bv -> getr R' 4%bv = getr R 4%bv ->
      (forall r, In r [22; 23; 24; 25; 26; 27]%bv -> getr R' r = getr R r) ->
      srealizes SEGS (mkCfg (@mkst fx R' (Z_to_bv 64 0x660d4) M' (seg_rom SEGS)) model') K.
    Proof using AC MI ST MALLOC_STACK_pos fx A s R M model sp ret p w nw ws K CB CONT.
      intros A' R' M' model' m' cs' J IV Hcs H2 H3 H4 HS. subst cs'.
      pose proof Hspr as (Hc & Hs47 & Hs16 & Hs20 & HMS & HSTK). pose proof ac_bounds_lit as Hcv.
      dIV IV. dCB. destruct CR as [Hra Hret Hretr Hsp Hsp16 Hsphi Hgp Htp].
      eapply srz_msteps; [exact (ms_halt _ MS') | exact (ms_lazy _ MS') | | ].
      { norm_pc.
        ld_step F_66094 D_66094 (word_to_le_bytes 8 (Z_to_bv 64 ret)) (Z_to_bv 64 ret) ltac:(rdn_fix SL1) ltac:(b2z8).
        ld_step F_66098 D_66098 (word_to_le_bytes 8 (getr R 8%bv)) (getr R 8%bv) ltac:(rdn_fix SL2) ltac:(b2z8).
        ld_step F_6609c D_6609c (word_to_le_bytes 8 (getr R 9%bv)) (getr R 9%bv) ltac:(rdn_fix SL3) ltac:(b2z8).
        ld_step F_660a0 D_660a0 (word_to_le_bytes 8 (getr R 18%bv)) (getr R 18%bv) ltac:(rdn_fix SL4) ltac:(b2z8).
        ld_step F_660a4 D_660a4 (word_to_le_bytes 8 (getr R 19%bv)) (getr R 19%bv) ltac:(rdn_fix SL5) ltac:(b2z8).
        ld_step F_660a8 D_660a8 (word_to_le_bytes 8 (getr R 20%bv)) (getr R 20%bv) ltac:(rdn_fix SL6) ltac:(b2z8).
        ld_step F_660ac D_660ac (word_to_le_bytes 8 (getr R 21%bv)) (getr R 21%bv) ltac:(rdn_fix SL7) ltac:(b2z8).
        sv F_660b0 D_660b0 (Z_to_bv 64 sp).
        stepjr F_660b4 D_660b4 (Z_to_bv 64 ret) ltac:(gres; reflexivity).
        lazymatch goal with |- msteps _ (mkst ?r ?pc _ _) _ =>
          replace pc with (Z_to_bv 64 ret) by (symmetry; imm_norm; exact Hret) end. apply mst_refl. }
      eapply (CONT A' _ M' model' m' J).
      - constructor; [exact AI' | exact MS' | exact (proj1 FS') | exact (proj2 FS') | exact SX' |].
        intros r Hr; unfold callee_saved in Hr.
        repeat (destruct Hr as [<-|Hr]; [gres; first [reflexivity | symmetry; assumption | assumption | apply HS; in_cs] |]). destruct Hr.
      - exact STR.
      - exact LV.
      - exact DJ'.
      - exact JK.
      - destruct GS as [-> | (d & asz & -> & _ & Hle)]; cbn; [exact Logic.I | exact Hle].
      - exact EFF.
    Qed.

    Lemma CALL1 : forall j x c A' R' M' model' m' cs' J,
      INV A' M' model' m' cs' J -> REGS R' j x -> getr R' 11%bv = Z_to_bv 64 c -> 0 < c < 256 -> Zlen cs' < 4 * nw ->
      (forall A'' R'' M'' model'' m'' J'', INV A'' M'' model'' m'' (cs' ++ [c]) J'' -> REGS R'' j x ->
         srealizes SEGS (mkCfg (@mkst fx R'' (Z_to_bv 64 0x66088) M'' (seg_rom SEGS)) model'') K) ->
      srealizes SEGS (mkCfg (@mkst fx R' (Z_to_bv 64 0x66080) M' (seg_rom SEGS)) model') K.
    Proof using AC MI ST MALLOC_STACK_pos NEW fx A s R M model sp ret p w nw ws K CB Hp0 Hp1 OBJp Hnw0 Hws Hw0 Hw1 OBJw DJ HNMAX ROOM.
      intros j x c A' R' M' model' m' cs' J IV RG Hc Hcr Hlt HK.
      pose proof IV as IV'. destruct IV as [AI' MS' FS' SX' ROC' SL1 SL2 SL3 SL4 SL5 SL6 SL7 STR GS LV DJ' CAPS JK EFF WIN WDEF WSM].
      destruct RG as [G2 G8 G9 G18 G19 G20 G21 G3 G4 GS6].
      eapply srz_msteps; [exact (ms_halt _ MS') | exact (ms_lazy _ MS') | norm_pc; sv F_66040 D_66040 (Z_to_bv 64 p); stepj F_66044 D_66044; close_pc | ].
      lazymatch goal with |- srealizes _ (mkCfg (mkst ?r ?pc _ _) _) _ =>
         replace pc with (Z_to_bv 64 (sc_push_back c8b3ec)) by (apply bv_eq; vm_compute; reflexivity); set (R1 := r) end.
      eapply (str_push_back_8b3ec_spec MI ST MALLOC_STACK_pos NEW fx A' s R1 M' model' (sp - 64) 0x66088 p c m' cs' K).
      - cbn [sc_push_stack c8b3ec]. unfold NEW_STACK. eapply (inv_callB _ _ _ _ _ _ R1 0x66088 IV');
          [unfold R1; gres; exact G2 | unfold R1; gres; apply bv_eq; vm_compute; reflexivity
          | unfold ret_ok; apply bv_eq; vm_compute; reflexivity | lia | unfold R1; gres; exact G3 | unfold R1; gres; exact G4].
      - unfold R1; gres; reflexivity.
      - unfold R1; gres; exact Hc.
      - exact STR.
      - cbn [sc_push_stack c8b3ec]. unfold NEW_STACK. exact (inv_obj _ _ _ _ _ _ IV').
      - cbn [sc_push_stack c8b3ec]. intros Hfull. exact (inv_room _ _ _ _ _ _ IV' Hlt Hfull).
      - intros A'' R'' M'' model'' m'' RB STR'' ALT EFF2. rewrite (Z.mod_small c 256) in STR'' by lia.
        apply (HK A'' R'' M'' model'' m'' (fun a => J a \/ sbuf_fp m' a)).
        + eapply (inv_post _ _ _ _ _ _ R1 _ R'' _ _ _ _ IV' Hlt RB STR'' ALT).
          cbn [sc_push_stack c8b3ec] in EFF2. unfold NEW_STACK in EFF2. exact EFF2.
        + destruct RB as [_ _ _ _ _ KP]. constructor;
          first [ rewrite (KP _) by in_cs; unfold R1; gres; assumption
                | intros r Hr; pose proof Hr as Hr'; repeat (destruct Hr as [<-|Hr]; [rewrite (KP _) by in_cs; unfold R1; gres; apply GS6; exact Hr' |]); destruct Hr ].
    Qed.

    Lemma CALL2 : forall j x c A' R' M' model' m' cs' J,
      INV A' M' model' m' cs' J -> REGS R' j x -> getr R' 11%bv = Z_to_bv 64 c -> 0 < c < 256 -> Zlen cs' < 4 * nw ->
      (forall A'' R'' M'' model'' m'' J'', INV A'' M'' model'' m'' (cs' ++ [c]) J'' -> REGS R'' j x ->
         srealizes SEGS (mkCfg (@mkst fx R'' (Z_to_bv 64 0x660a0) M'' (seg_rom SEGS)) model'') K) ->
      srealizes SEGS (mkCfg (@mkst fx R' (Z_to_bv 64 0x66098) M' (seg_rom SEGS)) model') K.
    Proof using AC MI ST MALLOC_STACK_pos NEW fx A s R M model sp ret p w nw ws K CB Hp0 Hp1 OBJp Hnw0 Hws Hw0 Hw1 OBJw DJ HNMAX ROOM.
      intros j x c A' R' M' model' m' cs' J IV RG Hc Hcr Hlt HK.
      pose proof IV as IV'. destruct IV as [AI' MS' FS' SX' ROC' SL1 SL2 SL3 SL4 SL5 SL6 SL7 STR GS LV DJ' CAPS JK EFF WIN WDEF WSM].
      destruct RG as [G2 G8 G9 G18 G19 G20 G21 G3 G4 GS6].
      eapply srz_msteps; [exact (ms_halt _ MS') | exact (ms_lazy _ MS') | norm_pc; sv F_66058 D_66058 (Z_to_bv 64 p); stepj F_6605c D_6605c; close_pc | ].
      lazymatch goal with |- srealizes _ (mkCfg (mkst ?r ?pc _ _) _) _ =>
         replace pc with (Z_to_bv 64 (sc_push_back c8b3ec)) by (apply bv_eq; vm_compute; reflexivity); set (R1 := r) end.
      eapply (str_push_back_8b3ec_spec MI ST MALLOC_STACK_pos NEW fx A' s R1 M' model' (sp - 64) 0x660a0 p c m' cs' K).
      - cbn [sc_push_stack c8b3ec]. unfold NEW_STACK. eapply (inv_callB _ _ _ _ _ _ R1 0x660a0 IV');
          [unfold R1; gres; exact G2 | unfold R1; gres; apply bv_eq; vm_compute; reflexivity
          | unfold ret_ok; apply bv_eq; vm_compute; reflexivity | lia | unfold R1; gres; exact G3 | unfold R1; gres; exact G4].
      - unfold R1; gres; reflexivity.
      - unfold R1; gres; exact Hc.
      - exact STR.
      - cbn [sc_push_stack c8b3ec]. unfold NEW_STACK. exact (inv_obj _ _ _ _ _ _ IV').
      - cbn [sc_push_stack c8b3ec]. intros Hfull. exact (inv_room _ _ _ _ _ _ IV' Hlt Hfull).
      - intros A'' R'' M'' model'' m'' RB STR'' ALT EFF2. rewrite (Z.mod_small c 256) in STR'' by lia.
        apply (HK A'' R'' M'' model'' m'' (fun a => J a \/ sbuf_fp m' a)).
        + eapply (inv_post _ _ _ _ _ _ R1 _ R'' _ _ _ _ IV' Hlt RB STR'' ALT).
          cbn [sc_push_stack c8b3ec] in EFF2. unfold NEW_STACK in EFF2. exact EFF2.
        + destruct RB as [_ _ _ _ _ KP]. constructor;
          first [ rewrite (KP _) by in_cs; unfold R1; gres; assumption
                | intros r Hr; pose proof Hr as Hr'; repeat (destruct Hr as [<-|Hr]; [rewrite (KP _) by in_cs; unfold R1; gres; apply GS6; exact Hr' |]); destruct Hr ].
    Qed.

    Lemma CALL3 : forall j x c A' R' M' model' m' cs' J,
      INV A' M' model' m' cs' J -> REGS R' j x -> getr R' 11%bv = Z_to_bv 64 c -> 0 < c < 256 -> Zlen cs' < 4 * nw ->
      (forall A'' R'' M'' model'' m'' J'', INV A'' M'' model'' m'' (cs' ++ [c]) J'' -> REGS R'' j x ->
         srealizes SEGS (mkCfg (@mkst fx R'' (Z_to_bv 64 0x660b8) M'' (seg_rom SEGS)) model'') K) ->
      srealizes SEGS (mkCfg (@mkst fx R' (Z_to_bv 64 0x660b0) M' (seg_rom SEGS)) model') K.
    Proof using AC MI ST MALLOC_STACK_pos NEW fx A s R M model sp ret p w nw ws K CB Hp0 Hp1 OBJp Hnw0 Hws Hw0 Hw1 OBJw DJ HNMAX ROOM.
      intros j x c A' R' M' model' m' cs' J IV RG Hc Hcr Hlt HK.
      pose proof IV as IV'. destruct IV as [AI' MS' FS' SX' ROC' SL1 SL2 SL3 SL4 SL5 SL6 SL7 STR GS LV DJ' CAPS JK EFF WIN WDEF WSM].
      destruct RG as [G2 G8 G9 G18 G19 G20 G21 G3 G4 GS6].
      eapply srz_msteps; [exact (ms_halt _ MS') | exact (ms_lazy _ MS') | norm_pc; sv F_66070 D_66070 (Z_to_bv 64 p); stepj F_66074 D_66074; close_pc | ].
      lazymatch goal with |- srealizes _ (mkCfg (mkst ?r ?pc _ _) _) _ =>
         replace pc with (Z_to_bv 64 (sc_push_back c8b3ec)) by (apply bv_eq; vm_compute; reflexivity); set (R1 := r) end.
      eapply (str_push_back_8b3ec_spec MI ST MALLOC_STACK_pos NEW fx A' s R1 M' model' (sp - 64) 0x660b8 p c m' cs' K).
      - cbn [sc_push_stack c8b3ec]. unfold NEW_STACK. eapply (inv_callB _ _ _ _ _ _ R1 0x660b8 IV');
          [unfold R1; gres; exact G2 | unfold R1; gres; apply bv_eq; vm_compute; reflexivity
          | unfold ret_ok; apply bv_eq; vm_compute; reflexivity | lia | unfold R1; gres; exact G3 | unfold R1; gres; exact G4].
      - unfold R1; gres; reflexivity.
      - unfold R1; gres; exact Hc.
      - exact STR.
      - cbn [sc_push_stack c8b3ec]. unfold NEW_STACK. exact (inv_obj _ _ _ _ _ _ IV').
      - cbn [sc_push_stack c8b3ec]. intros Hfull. exact (inv_room _ _ _ _ _ _ IV' Hlt Hfull).
      - intros A'' R'' M'' model'' m'' RB STR'' ALT EFF2. rewrite (Z.mod_small c 256) in STR'' by lia.
        apply (HK A'' R'' M'' model'' m'' (fun a => J a \/ sbuf_fp m' a)).
        + eapply (inv_post _ _ _ _ _ _ R1 _ R'' _ _ _ _ IV' Hlt RB STR'' ALT).
          cbn [sc_push_stack c8b3ec] in EFF2. unfold NEW_STACK in EFF2. exact EFF2.
        + destruct RB as [_ _ _ _ _ KP]. constructor;
          first [ rewrite (KP _) by in_cs; unfold R1; gres; assumption
                | intros r Hr; pose proof Hr as Hr'; repeat (destruct Hr as [<-|Hr]; [rewrite (KP _) by in_cs; unfold R1; gres; apply GS6; exact Hr' |]); destruct Hr ].
    Qed.

    Lemma CALL4 : forall j x c A' R' M' model' m' cs' J,
      INV A' M' model' m' cs' J -> REGS R' j x -> getr R' 11%bv = Z_to_bv 64 c -> 0 < c < 256 -> Zlen cs' < 4 * nw ->
      (forall A'' R'' M'' model'' m'' J'', INV A'' M'' model'' m'' (cs' ++ [c]) J'' -> REGS R'' j x ->
         srealizes SEGS (mkCfg (@mkst fx R'' (Z_to_bv 64 0x660c8) M'' (seg_rom SEGS)) model'') K) ->
      srealizes SEGS (mkCfg (@mkst fx R' (Z_to_bv 64 0x660c0) M' (seg_rom SEGS)) model') K.
    Proof using AC MI ST MALLOC_STACK_pos NEW fx A s R M model sp ret p w nw ws K CB Hp0 Hp1 OBJp Hnw0 Hws Hw0 Hw1 OBJw DJ HNMAX ROOM.
      intros j x c A' R' M' model' m' cs' J IV RG Hc Hcr Hlt HK.
      pose proof IV as IV'. destruct IV as [AI' MS' FS' SX' ROC' SL1 SL2 SL3 SL4 SL5 SL6 SL7 STR GS LV DJ' CAPS JK EFF WIN WDEF WSM].
      destruct RG as [G2 G8 G9 G18 G19 G20 G21 G3 G4 GS6].
      eapply srz_msteps; [exact (ms_halt _ MS') | exact (ms_lazy _ MS') | norm_pc; sv F_66080 D_66080 (Z_to_bv 64 p); stepj F_66084 D_66084; close_pc | ].
      lazymatch goal with |- srealizes _ (mkCfg (mkst ?r ?pc _ _) _) _ =>
         replace pc with (Z_to_bv 64 (sc_push_back c8b3ec)) by (apply bv_eq; vm_compute; reflexivity); set (R1 := r) end.
      eapply (str_push_back_8b3ec_spec MI ST MALLOC_STACK_pos NEW fx A' s R1 M' model' (sp - 64) 0x660c8 p c m' cs' K).
      - cbn [sc_push_stack c8b3ec]. unfold NEW_STACK. eapply (inv_callB _ _ _ _ _ _ R1 0x660c8 IV');
          [unfold R1; gres; exact G2 | unfold R1; gres; apply bv_eq; vm_compute; reflexivity
          | unfold ret_ok; apply bv_eq; vm_compute; reflexivity | lia | unfold R1; gres; exact G3 | unfold R1; gres; exact G4].
      - unfold R1; gres; reflexivity.
      - unfold R1; gres; exact Hc.
      - exact STR.
      - cbn [sc_push_stack c8b3ec]. unfold NEW_STACK. exact (inv_obj _ _ _ _ _ _ IV').
      - cbn [sc_push_stack c8b3ec]. intros Hfull. exact (inv_room _ _ _ _ _ _ IV' Hlt Hfull).
      - intros A'' R'' M'' model'' m'' RB STR'' ALT EFF2. rewrite (Z.mod_small c 256) in STR'' by lia.
        apply (HK A'' R'' M'' model'' m'' (fun a => J a \/ sbuf_fp m' a)).
        + eapply (inv_post _ _ _ _ _ _ R1 _ R'' _ _ _ _ IV' Hlt RB STR'' ALT).
          cbn [sc_push_stack c8b3ec] in EFF2. unfold NEW_STACK in EFF2. exact EFF2.
        + destruct RB as [_ _ _ _ _ KP]. constructor;
          first [ rewrite (KP _) by in_cs; unfold R1; gres; assumption
                | intros r Hr; pose proof Hr as Hr'; repeat (destruct Hr as [<-|Hr]; [rewrite (KP _) by in_cs; unfold R1; gres; apply GS6; exact Hr' |]); destruct Hr ].
    Qed.

    Lemma ms_word : forall x rest, 0 <= x < 2 ^ 32 ->
      ms_chars (x :: rest) =
        if x mod 256 =? 0 then []
        else if (x / 256) mod 256 =? 0 then [x mod 256]
        else if (x / 256 / 256) mod 256 =? 0 then [x mod 256; (x / 256) mod 256]
        else if (x / 256 / 256 / 256) mod 256 =? 0 then [x mod 256; (x / 256) mod 256; (x / 256 / 256) mod 256]
        else [x mod 256; (x / 256) mod 256; (x / 256 / 256) mod 256; (x / 256 / 256 / 256) mod 256] ++ ms_chars rest.
    Proof using.
      intros x rest Hx. rewrite ms_chars_cons. rewrite (Z.mod_small x (2 ^ 32)) by lia.
      cbn [word_chars take_nz].
      destruct (x mod 256 =? 0); [reflexivity|].
      destruct ((x / 256) mod 256 =? 0); [reflexivity|].
      destruct ((x / 256 / 256) mod 256 =? 0); [reflexivity|].
      destruct ((x / 256 / 256 / 256) mod 256 =? 0); reflexivity.
    Qed.

    Lemma WORD : forall j, 0 <= j < nw ->
      (j + 1 < nw -> forall A' R' M' model' m' cs' J x, INV A' M' model' m' cs' J -> REGS R' (j + 1) x -> Zlen cs' <= 4 * (j + 1) ->
          ms_chars ws = cs' ++ ms_chars (skipn (Z.to_nat (j + 1)) ws) ->
          srealizes SEGS (mkCfg (@mkst fx R' (Z_to_bv 64 0x66074) M' (seg_rom SEGS)) model') K) ->
      forall A' R' M' model' m' cs' J x, INV A' M' model' m' cs' J -> REGS R' j x -> Zlen cs' <= 4 * j ->
          ms_chars ws = cs' ++ ms_chars (skipn (Z.to_nat j) ws) ->
          srealizes SEGS (mkCfg (@mkst fx R' (Z_to_bv 64 0x66074) M' (seg_rom SEGS)) model') K.
    Proof using AC MI ST MALLOC_STACK_pos NEW fx A s R M model sp ret p w nw ws K CB Hp0 Hp1 OBJp Hnw0 Hws Hw0 Hw1 WS OBJw DJ HNMAX ROOM CONT.
      intros j Hj IH A' R' M' model' m' cs' J x0 IV RG Hlen Hms.
      rewrite (skipn_Znth j ws) in Hms by lia.
      set (x := Znth j ws) in *. destruct (WS j Hj) as [Hx _]. fold x in Hx.
      rewrite (ms_word x) in Hms by lia.
      set (b0 := x mod 256) in *. set (b1 := (x / 256) mod 256) in *.
      set (b2 := (x / 256 / 256) mod 256) in *. set (b3 := (x / 256 / 256 / 256) mod 256) in *.
      assert (Hb0 : 0 <= b0 < 256) by (unfold b0; apply Z.mod_pos_bound; lia).
      assert (Hb1 : 0 <= b1 < 256) by (unfold b1; apply Z.mod_pos_bound; lia).
      assert (Hb2 : 0 <= b2 < 256) by (unfold b2; apply Z.mod_pos_bound; lia).
      assert (Hb3 : 0 <= b3 < 256) by (unfold b3; apply Z.mod_pos_bound; lia).
      pose proof IV as IV'. destruct IV as [AI' MS' FS' SX' ROC' SL1 SL2 SL3 SL4 SL5 SL6 SL7 STR GS LV DJ' CAPS JK EFF WIN WDEF WSM].
      destruct RG as [G2 G8 G9 G18 G19 G20 G21 G3 G4 GS6].
      pose proof (WSM j Hj) as Wj. fold x in Wj. unfold fld in Wj.

      destruct (Z.eqb_spec b0 0) as [Hz0|Hnz0].
      {
        rewrite app_nil_r in Hms.
        eapply srz_msteps; [exact (ms_halt _ MS') | exact (ms_lazy _ MS') | | ].
        { norm_pc.
          ld_step F_66034 D_66034 (word_to_le_bytes 4 (Z_to_bv 64 x)) (Z_to_bv 64 x) ltac:(rdn_fix Wj) ltac:(apply lwu_val; lia).
          stepiv F_66038 D_66038 (Z_to_bv 64 b0) ltac:(gres; pin; imm_norm; rewrite v_andi_Z by lia; rewrite land_255 by lia; reflexivity).
          stepb_tk F_6603c D_6603c ltac:(rewrite Hz0; apply c_eq_refl).
          apply mst_refl. }
        lazymatch goal with |- srealizes _ (mkCfg (mkst _ ?pc _ _) _) _ =>
          replace pc with (Z_to_bv 64 0x660d4) by (apply bv_eq; vm_compute; reflexivity) end.
        eapply (EXIT _ _ _ _ _ _ _ IV'); [exact Hms | gres; exact G2 | gres; exact G3 | gres; exact G4 |].
        intros r Hr. pose proof Hr as Hr'. repeat (destruct Hr as [<-|Hr]; [gres; apply GS6; exact Hr' |]). destruct Hr. }

      eapply srz_msteps; [exact (ms_halt _ MS') | exact (ms_lazy _ MS') | | ].
      { norm_pc.
        ld_step F_66034 D_66034 (word_to_le_bytes 4 (Z_to_bv 64 x)) (Z_to_bv 64 x) ltac:(rdn_fix Wj) ltac:(apply lwu_val; lia).
        stepiv F_66038 D_66038 (Z_to_bv 64 b0) ltac:(gres; pin; imm_norm; rewrite v_andi_Z by lia; rewrite land_255 by lia; reflexivity).
        stepb_ft F_6603c D_6603c ltac:(rewrite c_eq_Z' by lia; apply Z.eqb_neq; exact Hnz0).
        apply mst_refl. }
      lazymatch goal with |- srealizes _ (mkCfg (mkst _ ?pc _ _) _) _ =>
        replace pc with (Z_to_bv 64 0x66080) by (apply bv_eq; vm_compute; reflexivity) end.
      eapply (CALL1 j (Z_to_bv 64 x) b0 _ _ _ _ _ _ _ IV');
        [ constructor; try (gres; first [reflexivity | assumption]);
          intros r Hr; pose proof Hr as Hr'; repeat (destruct Hr as [<-|Hr]; [gres; apply GS6; exact Hr'|]); destruct Hr
        | gres; reflexivity | lia | lia | ].
      clear AI' MS' FS' SX' ROC' SL1 SL2 SL3 SL4 SL5 SL6 SL7 STR GS LV DJ' CAPS JK EFF WIN WDEF WSM IV' G2 G8 G9 G18 G19 G20 G21 G3 G4 GS6 Wj.
      clear A' R' M' model' m' J.
      intros A' R' M' model' m' J IV RG.
      pose proof IV as IV'. destruct IV as [AI' MS' FS' SX' ROC' SL1 SL2 SL3 SL4 SL5 SL6 SL7 STR GS LV DJ' CAPS JK EFF WIN WDEF WSM].
      destruct RG as [G2 G8 G9 G18 G19 G20 G21 G3 G4 GS6].

      destruct (Z.eqb_spec b1 0) as [Hz1|Hnz1].
      { eapply srz_msteps; [exact (ms_halt _ MS') | exact (ms_lazy _ MS') | | ].
        { norm_pc.
          stepand F_66048 D_66048 (Z_to_bv 64 (256 * b1)) ltac:(gres; pin; rewrite v_and_Z by lia; rewrite land_ff00 by lia; reflexivity).
          stepb_tk F_6604c D_6604c ltac:(rewrite Hz1; apply c_eq_refl).
          apply mst_refl. }
        lazymatch goal with |- srealizes _ (mkCfg (mkst _ ?pc _ _) _) _ =>
          replace pc with (Z_to_bv 64 0x660d4) by (apply bv_eq; vm_compute; reflexivity) end.
        eapply (EXIT _ _ _ _ _ _ _ IV'); [exact Hms | gres; exact G2 | gres; exact G3 | gres; exact G4 |].
        intros r Hr. pose proof Hr as Hr'. repeat (destruct Hr as [<-|Hr]; [gres; apply GS6; exact Hr' |]). destruct Hr. }
      eapply srz_msteps; [exact (ms_halt _ MS') | exact (ms_lazy _ MS') | | ].
      { norm_pc.
        stepand F_66048 D_66048 (Z_to_bv 64 (256 * b1)) ltac:(gres; pin; rewrite v_and_Z by lia; rewrite land_ff00 by lia; reflexivity).
        stepb_ft F_6604c D_6604c ltac:(rewrite c_eq_Z' by lia; apply Z.eqb_neq; lia).
        stepiv F_66050 D_66050 (Z_to_bv 64 ((x mod 2 ^ 16) * 2 ^ 48)) ltac:(gres; pin; imm_norm; rewrite v_slli_Z by lia; rewrite (shl_mod64 x 48) by lia; reflexivity).
        stepiv F_66054 D_66054 (Z_to_bv 64 b1)
          ltac:(gres; pin; imm_norm; pose proof (Z.mod_pos_bound x (2 ^ 16) ltac:(lia));
                rewrite v_srli_Z by (change (2 ^ 16) with 65536 in *; lia); f_equal; apply byte1_via_shifts; lia).
        apply mst_refl. }
      lazymatch goal with |- srealizes _ (mkCfg (mkst _ ?pc _ _) _) _ =>
        replace pc with (Z_to_bv 64 0x66098) by (apply bv_eq; vm_compute; reflexivity) end.
      eapply (CALL2 j (Z_to_bv 64 x) b1 _ _ _ _ _ _ _ IV');
        [ constructor; try (gres; first [reflexivity | assumption]);
          intros r Hr; pose proof Hr as Hr'; repeat (destruct Hr as [<-|Hr]; [gres; apply GS6; exact Hr'|]); destruct Hr
        | gres; reflexivity | lia | rewrite Zlen_app1; lia | ].
      clear AI' MS' FS' SX' ROC' SL1 SL2 SL3 SL4 SL5 SL6 SL7 STR GS LV DJ' CAPS JK EFF WIN WDEF WSM IV' G2 G8 G9 G18 G19 G20 G21 G3 G4 GS6.
      clear A' R' M' model' m' J.
      intros A' R' M' model' m' J IV RG. rewrite <- app_assoc in IV. cbn [app] in IV.
      pose proof IV as IV'. destruct IV as [AI' MS' FS' SX' ROC' SL1 SL2 SL3 SL4 SL5 SL6 SL7 STR GS LV DJ' CAPS JK EFF WIN WDEF WSM].
      destruct RG as [G2 G8 G9 G18 G19 G20 G21 G3 G4 GS6].

      destruct (Z.eqb_spec b2 0) as [Hz2|Hnz2].
      { eapply srz_msteps; [exact (ms_halt _ MS') | exact (ms_lazy _ MS') | | ].
        { norm_pc.
          stepand F_66060 D_66060 (Z_to_bv 64 (65536 * b2)) ltac:(gres; pin; rewrite v_and_Z by lia; rewrite land_ff0000 by lia; reflexivity).
          stepb_tk F_66064 D_66064 ltac:(rewrite Hz2; apply c_eq_refl).
          apply mst_refl. }
        lazymatch goal with |- srealizes _ (mkCfg (mkst _ ?pc _ _) _) _ =>
          replace pc with (Z_to_bv 64 0x660d4) by (apply bv_eq; vm_compute; reflexivity) end.
        eapply (EXIT _ _ _ _ _ _ _ IV'); [exact Hms | gres; exact G2 | gres; exact G3 | gres; exact G4 |].
        intros r Hr. pose proof Hr as Hr'. repeat (destruct Hr as [<-|Hr]; [gres; apply GS6; exact Hr' |]). destruct Hr. }
      eapply srz_msteps; [exact (ms_halt _ MS') | exact (ms_lazy _ MS') | | ].
      { norm_pc.
        stepand F_66060 D_66060 (Z_to_bv 64 (65536 * b2)) ltac:(gres; pin; rewrite v_and_Z by lia; rewrite land_ff0000 by lia; reflexivity).
        stepb_ft F_66064 D_66064 ltac:(rewrite c_eq_Z' by lia; apply Z.eqb_neq; lia).
        stepiv F_66068 D_66068 (Z_to_bv 64 ((x mod 2 ^ 24) * 2 ^ 40)) ltac:(gres; pin; imm_norm; rewrite v_slli_Z by lia; rewrite (shl_mod64 x 40) by lia; reflexivity).
        stepiv F_6606c D_6606c (Z_to_bv 64 b2)
          ltac:(gres; pin; imm_norm; pose proof (Z.mod_pos_bound x (2 ^ 24) ltac:(lia));
                rewrite v_srli_Z by (change (2 ^ 24) with 16777216 in *; lia); f_equal; apply byte2_via_shifts; lia).
        apply mst_refl. }
      lazymatch goal with |- srealizes _ (mkCfg (mkst _ ?pc _ _) _) _ =>
        replace pc with (Z_to_bv 64 0x660b0) by (apply bv_eq; vm_compute; reflexivity) end.
      eapply (CALL3 j (Z_to_bv 64 x) b2 _ _ _ _ _ _ _ IV');
        [ constructor; try (gres; first [reflexivity | assumption]);
          intros r Hr; pose proof Hr as Hr'; repeat (destruct Hr as [<-|Hr]; [gres; apply GS6; exact Hr'|]); destruct Hr
        | gres; reflexivity | lia | replace (Zlen (cs' ++ [b0; b1])) with (Zlen cs' + 2) by (rewrite Zlen_app; reflexivity); lia | ].
      clear AI' MS' FS' SX' ROC' SL1 SL2 SL3 SL4 SL5 SL6 SL7 STR GS LV DJ' CAPS JK EFF WIN WDEF WSM IV' G2 G8 G9 G18 G19 G20 G21 G3 G4 GS6.
      clear A' R' M' model' m' J.
      intros A' R' M' model' m' J IV RG. rewrite <- app_assoc in IV. cbn [app] in IV.
      pose proof IV as IV'. destruct IV as [AI' MS' FS' SX' ROC' SL1 SL2 SL3 SL4 SL5 SL6 SL7 STR GS LV DJ' CAPS JK EFF WIN WDEF WSM].
      destruct RG as [G2 G8 G9 G18 G19 G20 G21 G3 G4 GS6].

      destruct (Z.eqb_spec b3 0) as [Hz3|Hnz3].
      { eapply srz_msteps; [exact (ms_halt _ MS') | exact (ms_lazy _ MS') | | ].
        { norm_pc.
          stepiv F_66078 D_66078 (Z_to_bv 64 b3) ltac:(gres; pin; imm_norm; rewrite v_srli_Z by lia; f_equal; apply byte3_val; lia).
          stepb_tk F_6607c D_6607c ltac:(rewrite Hz3; apply c_eq_refl).
          apply mst_refl. }
        lazymatch goal with |- srealizes _ (mkCfg (mkst _ ?pc _ _) _) _ =>
          replace pc with (Z_to_bv 64 0x660d4) by (apply bv_eq; vm_compute; reflexivity) end.
        eapply (EXIT _ _ _ _ _ _ _ IV'); [exact Hms | gres; exact G2 | gres; exact G3 | gres; exact G4 |].
        intros r Hr. pose proof Hr as Hr'. repeat (destruct Hr as [<-|Hr]; [gres; apply GS6; exact Hr' |]). destruct Hr. }
      eapply srz_msteps; [exact (ms_halt _ MS') | exact (ms_lazy _ MS') | | ].
      { norm_pc.
        stepiv F_66078 D_66078 (Z_to_bv 64 b3) ltac:(gres; pin; imm_norm; rewrite v_srli_Z by lia; f_equal; apply byte3_val; lia).
        stepb_ft F_6607c D_6607c ltac:(rewrite c_eq_Z' by lia; apply Z.eqb_neq; lia).
        apply mst_refl. }
      lazymatch goal with |- srealizes _ (mkCfg (mkst _ ?pc _ _) _) _ =>
        replace pc with (Z_to_bv 64 0x660c0) by (apply bv_eq; vm_compute; reflexivity) end.
      eapply (CALL4 j (Z_to_bv 64 x) b3 _ _ _ _ _ _ _ IV');
        [ constructor; try (gres; first [reflexivity | assumption]);
          intros r Hr; pose proof Hr as Hr'; repeat (destruct Hr as [<-|Hr]; [gres; apply GS6; exact Hr'|]); destruct Hr
        | gres; reflexivity | lia | replace (Zlen (cs' ++ [b0; b1; b2])) with (Zlen cs' + 3) by (rewrite Zlen_app; reflexivity); lia | ].
      clear AI' MS' FS' SX' ROC' SL1 SL2 SL3 SL4 SL5 SL6 SL7 STR GS LV DJ' CAPS JK EFF WIN WDEF WSM IV' G2 G8 G9 G18 G19 G20 G21 G3 G4 GS6.
      clear A' R' M' model' m' J.
      intros A' R' M' model' m' J IV RG. rewrite <- app_assoc in IV. cbn [app] in IV.
      pose proof IV as IV'. destruct IV as [AI' MS' FS' SX' ROC' SL1 SL2 SL3 SL4 SL5 SL6 SL7 STR GS LV DJ' CAPS JK EFF WIN WDEF WSM].
      destruct RG as [G2 G8 G9 G18 G19 G20 G21 G3 G4 GS6].

      destruct (Z.lt_ge_cases (j + 1) nw) as [Hmore|Hlast].
      { eapply srz_msteps; [exact (ms_halt _ MS') | exact (ms_lazy _ MS') | | ].
        { norm_pc.
          stepiv F_66088 D_66088 (Z_to_bv 64 (4 * (nw - (j + 1)))) ltac:(gres; pin; imm_norm; rewrite v_addi_Z by lia; f_equal; lia).
          stepiv F_6608c D_6608c (Z_to_bv 64 (w + 4 * (j + 1))) ltac:(gres; pin; imm_norm; rewrite v_addi_Z by lia; f_equal; lia).
          stepb_tk F_66090 D_66090 ltac:(rewrite c_eq_Z' by lia; apply Z.eqb_neq; lia).
          apply mst_refl. }
        lazymatch goal with |- srealizes _ (mkCfg (mkst _ ?pc _ _) _) _ =>
          replace pc with (Z_to_bv 64 0x66074) by (apply bv_eq; vm_compute; reflexivity) end.
        eapply (IH Hmore _ _ _ _ _ _ _ (Z_to_bv 64 x) IV');
          [ constructor; try (gres; first [reflexivity | assumption]);
            intros r Hr; pose proof Hr as Hr'; repeat (destruct Hr as [<-|Hr]; [gres; apply GS6; exact Hr'|]); destruct Hr
          | replace (Zlen (cs' ++ [b0; b1; b2; b3])) with (Zlen cs' + 4) by (rewrite Zlen_app; reflexivity); lia
          | rewrite Hms, <- !app_assoc; reflexivity ]. }
      eapply srz_msteps; [exact (ms_halt _ MS') | exact (ms_lazy _ MS') | | ].
      { norm_pc.
        stepiv F_66088 D_66088 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite v_addi_Z by lia; f_equal; lia).
        stepiv F_6608c D_6608c (Z_to_bv 64 (w + 4 * (j + 1))) ltac:(gres; pin; imm_norm; rewrite v_addi_Z by lia; f_equal; lia).
        stepb_ft F_66090 D_66090 ltac:(apply c_eq_refl).
        apply mst_refl. }
      lazymatch goal with |- srealizes _ (mkCfg (mkst _ ?pc _ _) _) _ =>
        replace pc with (Z_to_bv 64 0x660d4) by (apply bv_eq; vm_compute; reflexivity) end.
      eapply (EXIT _ _ _ _ _ _ _ IV'); [ | gres; exact G2 | gres; exact G3 | gres; exact G4 |].
      { rewrite Hms. replace (j + 1) with (Zlen ws) by lia. rewrite skipn_all_Z. cbn [ms_chars]. rewrite ?app_nil_r, <- ?app_assoc. reflexivity. }
      intros r Hr. pose proof Hr as Hr'. repeat (destruct Hr as [<-|Hr]; [gres; apply GS6; exact Hr' |]). destruct Hr.
    Qed.
    Lemma LOOP : forall (k : nat) j, 0 <= j < nw -> nw - j <= Z.of_nat k ->
      forall A' R' M' model' m' cs' J x, INV A' M' model' m' cs' J -> REGS R' j x -> Zlen cs' <= 4 * j ->
        ms_chars ws = cs' ++ ms_chars (skipn (Z.to_nat j) ws) ->
        srealizes SEGS (mkCfg (@mkst fx R' (Z_to_bv 64 0x66074) M' (seg_rom SEGS)) model') K.
    Proof using AC MI ST MALLOC_STACK_pos NEW fx A s R M model sp ret p w nw ws K CB Hp0 Hp1 OBJp Hnw0 Hws Hw0 Hw1 WS OBJw DJ HNMAX ROOM CONT.
      induction k as [|k IHk]; intros j Hj Hk; [lia|].
      apply WORD; [exact Hj|]. intros Hmore. apply IHk; lia.
    Qed.

    Lemma w8_zero : word_to_le_bytes 8 (Z_to_bv 64 0) = repeat (Z_to_bv 8 0) 8.
    Proof using. reflexivity. Qed.

    Lemma ENTRY : srealizes SEGS (mkCfg (@mkst fx R (Z_to_bv 64 0x6602c) M (seg_rom SEGS)) model) K.
    Proof using AC MI ST MALLOC_STACK_pos NEW fx A s R M model sp ret p w nw ws K CB Ha0 Ha1 Ha2 Hp0 Hp1 HDp OBJp Hnw0 Hws Hw0 Hw1 WS OBJw DJ HNMAX ROOM CONT.
      pose proof Hspr as (Hc & Hs47 & Hs16 & Hs20 & HMS & HSTK). pose proof ac_bounds_lit as Hcv.
      pose proof WINp as WP. pose proof WINw as WW. pose proof WDEF0 as WD0.
      pose proof CB as CB'. destruct CB' as [AI MS ROC SXI SXH CR Hceil HROOM Hwin Hown_sx Herr_sx].
      destruct CR as [Hra Hret Hretr Hsp Hsp16 Hsphi Hgp Htp].
      assert (HDR : forall a, p <= a < p + 24 -> ~ owned MI A a /\ ~ in_ranges (ly_img Ly.L) a).
      { intros a Ha. exact (placed_sep A M model p 24 a AI (proj1 OBJp) Ha). }
      assert (WIN : forall a, sp - STK <= a < sp -> ~ owned MI A a /\ ~ in_ranges (ly_img Ly.L) a).
      { intros a Ha. apply (stack_sep A M model a AI). lia. }
      assert (HDW : mdef M (sp - STK) STK).
      { pose proof HROOM as HOK. unfold stack_room in HOK.
        eapply store_ok_mdef_offimg; [exact HOK | lia | lia | lia |]. intros x Hx. apply ly_noseg. lia. }
      set (M0 := wbytes (wbytes (wbytes M (Z_to_bv 64 p) (word_to_le_bytes 8 (Z_to_bv 64 0)))
                                (Z_to_bv 64 (p + 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
                         (Z_to_bv 64 (p + 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
      assert (ST0 : stores_in (zwin p (p + 24)) M M0).
      { unfold M0. eapply stores_in_wbytes_more; [eapply stores_in_wbytes_more; [apply stores_in_wbytes | | |] | | |];
          rewrite ?length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; try lia; intros a Ha; unfold zwin in *; lia. }
      assert (Z0 : forall d, 0 <= d < 8 -> rdn SEGS M0 (Z_to_bv 64 (p + d)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 0))).
      { intros d Hd. unfold M0. rewrite 2!rdn_wbytes_out_Z by (rewrite length_N_to_le_bytes; cbn; lia).
        rewrite w8_zero. change (word_to_le_bytes 1 (Z_to_bv 64 0)) with (repeat (Z_to_bv 8 0) 1).
        apply rdn_zeros_sub; cbn; lia. }
      assert (PRE : msteps SEGS (@mkst fx R (Z_to_bv 64 0x6602c) M (seg_rom SEGS)) (@mkst fx R (Z_to_bv 64 0x66038) M0 (seg_rom SEGS))).
      { norm_pc.
        stw F_65fec D_65fec (Z_to_bv 64 p) (Z_to_bv 64 0) ltac:(ok_mdef HDp).
        stw F_65ff0 D_65ff0 (Z_to_bv 64 (p + 8)) (Z_to_bv 64 0) ltac:(ok_mdef HDp).
        stw F_65ff4 D_65ff4 (Z_to_bv 64 (p + 16)) (Z_to_bv 64 0) ltac:(ok_mdef HDp).
        close_pc. }
      destruct (Z.eq_dec nw 0) as [Hnw|Hnw].
      -
        assert (Hws0 : ws = []) by (destruct ws; [reflexivity | unfold Zlen in Hws; cbn in Hws; lia]).
        eapply srz_msteps; [exact (ms_halt _ MS) | exact (ms_lazy _ MS) | | ].
        { eapply msteps_trans; [exact PRE|]. norm_pc.
          stepb_tk F_65ff8 D_65ff8 ltac:(rewrite Ha2, Hnw; apply c_eq_refl).
          stepjr F_660b4 D_660b4 (Z_to_bv 64 ret) ltac:(gres; exact Hra).
          lazymatch goal with |- msteps _ (mkst ?r ?pc _ _) _ =>
            replace pc with (Z_to_bv 64 ret) by (symmetry; imm_norm; exact Hret) end. apply mst_refl. }
        eapply (CONT A R M0 model SShort (fun _ => False)).
        + constructor; [ | exact MS | reflexivity | reflexivity | | intros r Hr; reflexivity].
          * eapply (stores_in_ainv SEGS Ly.L MI); [exact AI | exact ST0 |]. intros a Ha. apply HDR. unfold zwin in Ha. lia.
          * eapply (stores_in_sx SEGS Ly.L ST); [exact SXI | exact ST0 |].
            intros a Ha. destruct (offimg_sep a (proj2 (HDR a ltac:(unfold zwin in Ha; lia)))) as (X1 & X2 & _). split; assumption.
        + rewrite Hws0. cbn [ms_chars]. apply (str_nil MI); [lia | lia | eapply stores_in_mdef; [exact ST0 | exact HDp] | |].
          * unfold fld. replace p with (p + 0) by lia. apply Z0. lia.
          * unfold fld. apply Z0. lia.
        + intros q k. cbn [str_blocks In]. tauto.
        + intros q k [].
        + intros a [].
        + exact Logic.I.
        + apply eff_store; [| exact (proj2 ST0)].
          intros a HF HW. apply (proj1 ST0). intros Hz. apply HF. left. exact Hz.
      -
        set (R1 := regupd (regupd (regupd (regupd (regupd (regupd (regupd R
                     2%bv (Z_to_bv 64 (sp - 64))) 8%bv (Z_to_bv 64 w)) 9%bv (Z_to_bv 64 p)) 18%bv (Z_to_bv 64 (4 * nw)))
                     10%bv (Z_to_bv 64 0x10000)) 19%bv (Z_to_bv 64 0xff00)) 20%bv (Z_to_bv 64 0xff0000)).
        set (M1 := wslots M0 sp [getr R 21%bv; getr R 20%bv; getr R 19%bv; getr R 18%bv; getr R 9%bv; getr R 8%bv; Z_to_bv 64 ret]).
        assert (ST01 : stores_in (zwin (sp - 56) sp) M0 M1).
        { unfold M1. eapply stores_in_weaken; [apply wslots_stores_in; unfold Zlen; cbn; lia|].
          intros a Ha. unfold zwin, Zlen in *. cbn in *. lia. }
        assert (ST1 : stores_in (fun a => zwin p (p + 24) a \/ zwin (sp - 56) sp a) M M1).
        { eapply stores_in_trans; [eapply stores_in_weaken; [exact ST0|]; intros a Ha; left; exact Ha |].
          eapply stores_in_weaken; [exact ST01|]. intros a Ha; right; exact Ha. }
        assert (SL : forall k, 1 <= k <= 7 ->
                  rdn SEGS M1 (Z_to_bv 64 (sp - 8 * k)) 8
                  = Some (word_to_le_bytes 8 (nth (Z.to_nat (7 - k)) [getr R 21%bv; getr R 20%bv; getr R 19%bv; getr R 18%bv; getr R 9%bv; getr R 8%bv; Z_to_bv 64 ret] (Z_to_bv 64 0)))).
        { intros k Hk. unfold M1. apply wslots_read; unfold Zlen; cbn; lia. }
        pose proof HROOM as HOK. unfold stack_room in HOK.
        eapply srz_msteps; [exact (ms_halt _ MS) | exact (ms_lazy _ MS) | | ].
        { eapply msteps_trans; [exact PRE|]. norm_pc.
          stepb_ft F_65ff8 D_65ff8 ltac:(rewrite Ha2; rewrite c_eq_Z' by lia; apply Z.eqb_neq; exact Hnw).
          sv F_65ffc D_65ffc (Z_to_bv 64 (sp - 64)).
          stw F_66000 D_66000 (Z_to_bv 64 (sp - 8)) (Z_to_bv 64 ret) ltac:(unhide WP; ok_sub HOK).
          stw F_66004 D_66004 (Z_to_bv 64 (sp - 16)) (getr R 8%bv) ltac:(ok_sub HOK).
          stw F_66008 D_66008 (Z_to_bv 64 (sp - 24)) (getr R 9%bv) ltac:(ok_sub HOK).
          stw F_6600c D_6600c (Z_to_bv 64 (sp - 32)) (getr R 18%bv) ltac:(ok_sub HOK).
          stw F_66010 D_66010 (Z_to_bv 64 (sp - 40)) (getr R 19%bv) ltac:(ok_sub HOK).
          stw F_66014 D_66014 (Z_to_bv 64 (sp - 48)) (getr R 20%bv) ltac:(ok_sub HOK).
          stw F_66018 D_66018 (Z_to_bv 64 (sp - 56)) (getr R 21%bv) ltac:(ok_sub HOK).
          sv F_6601c D_6601c (Z_to_bv 64 w).
          sv F_66020 D_66020 (Z_to_bv 64 p).
          stepiv F_66024 D_66024 (Z_to_bv 64 (4 * nw)) ltac:(gres; pin; imm_norm; rewrite v_slli_Z by lia; f_equal; change (2 ^ 2) with 4; lia).
          sv F_66028 D_66028 (Z_to_bv 64 0x10000).
          stepiv F_6602c D_6602c (Z_to_bv 64 0xff00) ltac:(gres; apply bv_eq; vm_compute; reflexivity).
          sv F_66030 D_66030 (Z_to_bv 64 0xff0000).
          lazymatch goal with |- msteps _ (mkst ?r ?pc ?m _) _ =>
            unify r R1; change m with M1; replace pc with (Z_to_bv 64 0x66074) by (apply bv_eq; vm_compute; reflexivity) end.
          apply mst_refl. }
        apply (LOOP (Z.to_nat nw) 0 ltac:(lia) ltac:(lia) A R1 M1 model SShort [] (fun _ => False) (getr R 21%bv)).
        + constructor.
          * eapply (stores_in_ainv SEGS Ly.L MI); [exact AI | exact ST1 |].
            intros a [Ha|Ha]; [apply HDR | apply WIN]; unfold zwin in Ha; lia.
          * exact MS.
          * split; reflexivity.
          * eapply (stores_in_sx SEGS Ly.L ST); [exact SXI | exact ST1 |].
            intros a Ha. assert (Hni : ~ in_ranges (ly_img Ly.L) a) by (destruct Ha as [Ha|Ha]; [apply HDR | apply WIN]; unfold zwin in Ha; lia).
            destruct (offimg_sep a Hni) as (X1 & X2 & _). split; assumption.
          * eapply (roc_stores Ly.L); [exact ROC | exact ST1 |].
            intros a [Ha|Ha]; [apply HDR | apply WIN]; unfold zwin in Ha; lia.
          * apply (SL 1); lia.
          * apply (SL 2); lia.
          * apply (SL 3); lia.
          * apply (SL 4); lia.
          * apply (SL 5); lia.
          * apply (SL 6); lia.
          * apply (SL 7); lia.
          * apply (str_nil MI); [lia | lia | eapply stores_in_mdef; [exact ST1 | exact HDp] | |].
            -- unfold fld, M1. rewrite wslots_out; [| unfold Zlen; cbn; lia | lia | lia | cbn; lia | unfold Zlen; cbn; lia].
               replace p with (p + 0) by lia. apply Z0. lia.
            -- unfold fld, M1. rewrite wslots_out; [| unfold Zlen; cbn; lia | lia | lia | cbn; lia | unfold Zlen; cbn; lia].
               apply Z0. lia.
          * left; reflexivity.
          * intros q k. cbn [str_blocks In]. tauto.
          * intros q k [].
          * split; reflexivity.
          * intros a [].
          * apply eff_store; [| exact (proj2 ST1)].
            intros a HF HW. apply (proj1 ST1). intros [Hz|Hz]; [apply HF; left; exact Hz | apply HW; unfold W_of, Wn, zwin in *; cbn; lia].
          * eapply stores_in_mdef; [exact ST1 | exact HDW].
          * eapply stores_in_mdef; [exact ST1 | exact WD0].
          * intros i Hi. destruct (WS i Hi) as [_ HF]. eapply fld_agree; [lia | cbn; lia | exact HF |].
            eapply stores_in_agree; [exact ST1|]. intros a Ha. unfold zwin in Ha. cbn in Ha. split; [lia|]. intros [Hz|Hz].
            -- exact (DJ a ltac:(unfold zwin; lia) Hz).
            -- unfold zwin in *. lia.
        + constructor; unfold R1; gres; try reflexivity; try assumption; try (f_equal; lia).
          intros r Hr. pose proof Hr as Hr'. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity |]). destruct Hr.
        + change (Zlen (@nil Z)) with 0. lia.
        + reflexivity.
    Qed.
  End Body.

  Theorem makestring_65f88_spec' : makestring_stmt' SEGS Ly.L MI ST c8b3ec.
  Proof using AC MI ST MALLOC_STACK_pos NEW.
    intros fx A s R M model sp ret p w nw ws K. cbn [sc_makestring sc_ms_stack c8b3ec]. lazy zeta. unfold NEW_STACK.
    intros CB Ha0 Ha1 Ha2 Hp0 Hp1 HDp OBJp Hnw Hws Hw0 Hw1 WS OBJw DJ HNMAX ROOM CONT.
    eapply (ENTRY fx A s R M model sp ret p w nw ws K); try eassumption.
  Qed.

End MakeString.
End Lib_MakeString.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.Lib_Cxx_OperatorDelete.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRepFacts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HConstsS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HFind.
From Stdlib Require NArith.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3Sound OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymRun3.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HLib.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Module S1_code_696d8_69804.

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_69800 : bv 32 := 0x00008067.
Lemma F_69800 : fetch_word Plain.M.loaded_segments (0x69840 : word) = Some W_69800.
Proof. vm_refl. Qed.
Lemma D_69800 : decode_any W_69800 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
End S1_code_696d8_69804.

Module HFind2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StepTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.WalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ShapeAlg OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SRealizes OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibEff OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3Sound OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymRun3.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HConstsS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmInstS1.S1_code_696d8_69804.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation SEGS := Plain.M.loaded_segments.

Definition FIND : Z := 0x69718.
Definition B_PC : Z := 0x697bc.
Definition LP_PC : Z := 0x697fc.
Definition LM_PC : Z := 0x69828.
Definition RET_PC : Z := 0x69840.
Definition STOPS : list Z := [B_PC; LP_PC; LM_PC; RET_PC].

Lemma BSEQ_bound : forall bc, In bc BSEQ -> 0 <= bc <= 26339969.
Proof.
  intros bc Hin. unfold BSEQ in Hin.
  repeat (destruct Hin as [<-|Hin]; [lia|]). destruct Hin.
Qed.

Lemma chain_at : forall (V : Type) (M : mem) l1 (p k : Z) (v : V) l2,
  chain SEGS M (l1 ++ (p, (k, v)) :: l2) -> cell8 SEGS M p (hdaddr l2).
Proof.
  intros V M l1. induction l1 as [|[q kv] l1 IH]; intros p k v l2 H; cbn in H.
  - exact (proj1 H).
  - apply (IH p k v l2). exact (proj2 H).
Qed.

Lemma in_split_ents : forall (V : Type) (p : Z) (ents : list (Z * (Z * V))),
  In p (map fst ents) -> exists l1 k v l2, ents = l1 ++ (p, (k, v)) :: l2.
Proof.
  intros V p ents Hin. apply in_map_iff in Hin. destruct Hin as ([p' [k v]] & Hp & Hin). cbn in Hp. subst p'.
  apply in_split in Hin. destruct Hin as (l1 & l2 & ->). exists l1, k, v, l2. reflexivity.
Qed.

Definition popc : expr :=
  Eval vm_compute in
    (let '(ss, _, _) := sym_exec SEGS 100 true STOPS (SCR [false; false] [EVar 34; EVar 35] [])
                          (SS FIND sr_id [] [] 50) [] in
     sr_get (s_regs ss) 14%bv).
Definition popcw (w : word) : word := edenot (Env (fun _ => w) (fun _ => [])) popc.

Lemma popc_env : forall E, edenot E popc = popcw (ev E 34).
Proof. intros E. unfold popcw, popc. cbn [edenot ev]. reflexivity. Qed.

Ltac vm_popc :=
  match goal with |- context [bv_unsigned (popcw ?w)] =>
    let v := eval vm_compute in (bv_unsigned (popcw w)) in
    replace (bv_unsigned (popcw w)) with v by (vm_compute; reflexivity) end.

Lemma popcw_cases : forall bc, In bc BSEQ -> bc <> 0 ->
  (bc = 2 /\ bv_unsigned (popcw (Z_to_bv 64 bc)) = 1) \/ (bc <> 2 /\ 2 <= bv_unsigned (popcw (Z_to_bv 64 bc))).
Proof.
  intros bc Hin Hnz. unfold BSEQ in Hin.
  repeat (destruct Hin as [<-|Hin];
    [ first [ exfalso; lia
            | left; split; [reflexivity | vm_popc; reflexivity]
            | right; split; [lia | vm_popc; lia] ] |]).
  destruct Hin.
Qed.

Lemma remuw_val : forall k bc, 0 <= k < 2 ^ 32 -> 0 < bc < 2 ^ 31 ->
  alu64 ALU_SRL (mul_div M_MUL (Z_to_bv 64 4294967296)
                   (sext 64 (mul_div M_REMU (low32 (Z_to_bv 64 k)) (low32 (Z_to_bv 64 bc)))))
        (Z_to_bv 64 32)
  = Z_to_bv 64 (k mod bc).
Proof.
  intros k bc Hk Hbc.
  pose proof (Z.mod_pos_bound k bc ltac:(lia)) as Hm.
  assert (Hlk : low32 (Z_to_bv 64 k) = Z_to_bv 32 k).
  { apply bv_eq. unfold low32. rewrite bv_extract_unsigned, !Z_to_bv_unsigned, bv_wrap64_mod, Z.shiftr_0_r.
    rewrite Z.mod_small by lia. reflexivity. }
  assert (Hlb : low32 (Z_to_bv 64 bc) = Z_to_bv 32 bc).
  { apply bv_eq. unfold low32. rewrite bv_extract_unsigned, !Z_to_bv_unsigned, bv_wrap64_mod, Z.shiftr_0_r.
    rewrite Z.mod_small by lia. reflexivity. }
  rewrite Hlk, Hlb.
  assert (Hr : mul_div M_REMU (Z_to_bv 32 k) (Z_to_bv 32 bc) = Z_to_bv 32 (k mod bc)).
  { cbn [mul_div]. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32).
    rewrite (Z.mod_small bc) by lia. destruct (Z.eqb_spec bc 0); [lia|].
    apply bv_eq. rewrite bv_modu_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32).
    rewrite (Z.mod_small k), (Z.mod_small bc), (Z.mod_small (k mod bc)) by lia. reflexivity. }
  rewrite Hr.
  assert (Hs : sext 64 (Z_to_bv 32 (k mod bc)) = Z_to_bv 64 (k mod bc)).
  { apply bv_eq. unfold sext. rewrite bv_sign_extend_unsigned, Z_to_bv_signed, !Z_to_bv_unsigned, bv_wrap64_mod.
    rewrite (bv_swrap_small 32) by (change (bv_half_modulus 32) with (2 ^ 31); lia). unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). reflexivity. }
  rewrite Hs. apply bv_eq. cbn [alu64 alu mul_div].
  rewrite bv_shiftr_unsigned, bv_mul_unsigned, bv_and_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite (Z.mod_small 4294967296), (Z.mod_small (k mod bc)), (Z.mod_small 32), (Z.mod_small 63) by lia.
  change (Z.land 32 63) with 32.
  rewrite (Z.mod_small (4294967296 * (k mod bc))) by lia.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 32) with 4294967296.
  rewrite Z.mul_comm, Z.div_mul by lia. reflexivity.
Qed.

Section FindProof.
  Context {fx : FPState}.
Context {AC : AllocCeiling}.
  Variable L : Layout.
  Variable MI : MallocIface SEGS L.
  Variables (NS : Z) (V : Type) (nval : mem -> Z -> V -> Prop).
  Variable rom : word -> option byte.

  Variables (A : AS MI) (M : mem) (obj bl bc keyp key : Z) (ents : list (Z * (Z * V))).
  Hypothesis U : umapx MI NS nval A M obj bl bc ents.
  Hypothesis Hkey : cell4 SEGS M keyp key.
  Hypothesis Hkp0 : 0 < keyp.
  Hypothesis Hkp1 : keyp + 4 <= 2 ^ 47.
  Hypothesis HNS : 24 <= NS.

  #[local] Abbreviation st R pc := (@mkst fx R (Z_to_bv 64 pc) M rom).

  Let Hhdr : hdr SEGS M obj bl bc ents := u_hdr U.
  Let Hbc_in : In bc BSEQ := u_bseq U.
  Let Hkey_rng : 0 <= key < 2 ^ 32 := proj1 Hkey.

  Lemma bc_rng : 0 <= bc <= 26339969.
  Proof using AC L MI NS V nval A M obj bl bc ents U. apply BSEQ_bound. exact Hbc_in. Qed.

  Lemma node_facts : forall l1 p k v l2, ents = l1 ++ (p, (k, v)) :: l2 ->
    0 < p /\ p + NS <= 2 ^ 47 /\ cell8 SEGS M (p + 8) k /\ cell4 SEGS M (p + 16) k /\ 0 <= k < 2 ^ 32
    /\ cell8 SEGS M p (hdaddr l2).
  Proof using AC L MI NS V nval A M obj bl bc ents U.
    intros l1 p k v l2 He.
    destruct (u_node U p k v) as (_ & Hp0 & Hp1 & _ & Hh & Hk & Hkr & _).
    { rewrite He. apply in_app_iff. right. left. reflexivity. }
    split; [lia|]. split; [lia|]. split; [exact Hh|]. split; [exact Hk|]. split; [lia|].
    apply (chain_at V M l1 p k v l2). rewrite <- He. exact (u_chain U).
  Qed.

  Lemma hdaddr_cases : forall (l2 : list (Z * (Z * V))),
    hdaddr l2 = 0 /\ l2 = [] \/ exists p k v l2', l2 = (p, (k, v)) :: l2' /\ hdaddr l2 = p.
  Proof using V.
    intros [|[p [k v]] l2']; [left; split; reflexivity | right]. exists p, k, v, l2'. split; reflexivity.
  Qed.

  Lemma blkA0 : forall R,
    getr R 10%bv = Z_to_bv 64 obj -> getr R 11%bv = Z_to_bv 64 keyp -> bc = 0 ->
    exists R', msteps SEGS (st R FIND) (st R' RET_PC) /\ aonly R R' /\ getr R' 10%bv = Z_to_bv 64 0.
  Proof using fx AC L MI NS V nval rom A M obj bl bc keyp key ents U.
    intros R H10 H11 Hbc0. destruct Hhdr as [Hbl Hbc8 Hp1c Hsz Hmlf Hdef].
    pose proof bc_rng as Hbcr. pose proof (u_obj_lo U) as Ho0. pose proof (u_obj_hi U) as Ho1.
    pose (E := Eseed R [Z_to_bv 64 obj; Z_to_bv 64 keyp; Z_to_bv 64 bc; Z_to_bv 64 key]).
    assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32); (11%bv, EVar 33)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
    assert (HK : know_ok SEGS E M []) by constructor.
    xrun HR HK 100%nat STOPS (SCR [true] [EVar 34; EVar 35] []) 50%N.
    { split_scs; sc_auto1. }
    exists R'. split; [exact Hms|]. split.
    - eapply aonly_of_syms; [exact HR'| reflexivity].
    - rreg HR' 10%bv H. exact H.
  Qed.

  Lemma blkA : forall R,
    getr R 10%bv = Z_to_bv 64 obj -> getr R 11%bv = Z_to_bv 64 keyp -> bc <> 0 ->
    exists R', msteps SEGS (st R FIND) (st R' B_PC) /\ aonly R R'
      /\ getr R' 10%bv = Z_to_bv 64 obj /\ getr R' 11%bv = Z_to_bv 64 key
      /\ getr R' 12%bv = Z_to_bv 64 bc /\ getr R' 13%bv = Z_to_bv 64 (hmod key bc)
      /\ getr R' 14%bv = popcw (Z_to_bv 64 bc).
  Proof using fx AC L MI NS V nval rom A M obj bl bc keyp key ents U Hkey Hkp0 Hkp1.
    intros R H10 H11 Hbc. destruct Hhdr as [Hbl Hbc8 Hp1c Hsz Hmlf Hdef].
    pose proof bc_rng as Hbcr. pose proof (u_obj_lo U) as Ho0. pose proof (u_obj_hi U) as Ho1.
    pose (E := Eseed R [Z_to_bv 64 obj; Z_to_bv 64 keyp; Z_to_bv 64 bc; Z_to_bv 64 key]).
    assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32); (11%bv, EVar 33)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
    assert (HK : know_ok SEGS E M []) by constructor.
    assert (Hpc : forall b : bool, branch_taken BC_LTU (edenot E (ELit 1)) (edenot E popc) = b ->
                  sc_denot SEGS M E (SCBr b BC_LTU (ELit 1) popc)).
    { intros b Hb. exact Hb. }
    destruct (popcw_cases bc Hbc_in Hbc) as [[Hbc2 Hp1] | [Hbc2 Hp2]].
    -
      xrun HR HK 100%nat STOPS (SCR [false; false] [EVar 34; EVar 35] []) 50%N.
      { split_scs; try sc_auto1.
        apply Hpc. rewrite popc_env. evs. rewrite branch_ltu_lit_l by lia. bool_lia. }
      exists R'. split; [exact Hms|]. split; [eapply aonly_of_syms; [exact HR'| reflexivity]|].
      rreg HR' 10%bv H10'. rreg HR' 11%bv H11'. rreg HR' 12%bv H12'. rreg HR' 13%bv H13'.
      repeat split; try assumption.
      + rewrite H13'. rewrite w_addm, w_and by lia. subst bc. unfold hmod.
        change (2 + -1) with (Z.ones 1). rewrite Z.land_comm, Z.land_ones by lia. reflexivity.
      + lazymatch type of HR' with regs_ok ?E' _ _ => exact (eq_trans (HR' 14%bv) (popc_env E')) end.
    - destruct (Z.ltb_spec key bc) as [Hlt|Hge].
      +
        xrun HR HK 100%nat STOPS (SCR [false; true; true] [EVar 34; EVar 35] []) 50%N.
        { split_scs; try sc_auto1.
          apply Hpc. rewrite popc_env. evs. rewrite branch_ltu_lit_l by lia. bool_lia. }
        exists R'. split; [exact Hms|]. split; [eapply aonly_of_syms; [exact HR'| reflexivity]|].
        rreg HR' 10%bv H10'. rreg HR' 11%bv H11'. rreg HR' 12%bv H12'. rreg HR' 13%bv H13'.
        repeat split; try assumption.
        * rewrite H13'. unfold hmod. rewrite Z.mod_small by lia. reflexivity.
        * lazymatch type of HR' with regs_ok ?E' _ _ => exact (eq_trans (HR' 14%bv) (popc_env E')) end.
      +
        xrun HR HK 100%nat STOPS (SCR [false; true; false] [EVar 34; EVar 35] []) 50%N.
        { split_scs; try sc_auto1.
          apply Hpc. rewrite popc_env. evs. rewrite branch_ltu_lit_l by lia. bool_lia. }
        exists R'. split; [exact Hms|]. split; [eapply aonly_of_syms; [exact HR'| reflexivity]|].
        rreg HR' 10%bv H10'. rreg HR' 11%bv H11'. rreg HR' 12%bv H12'. rreg HR' 13%bv H13'.
        repeat split; try assumption.
        * rewrite H13'. unfold hmod. apply remuw_val; lia.
        * lazymatch type of HR' with regs_ok ?E' _ _ => exact (eq_trans (HR' 14%bv) (popc_env E')) end.
  Qed.

  Lemma blkB : forall R idx b q0 (w4 : word),
    getr R 10%bv = Z_to_bv 64 obj -> getr R 11%bv = Z_to_bv 64 key -> getr R 12%bv = Z_to_bv 64 bc ->
    getr R 13%bv = Z_to_bv 64 idx -> getr R 14%bv = w4 ->
    0 <= idx < bc -> bc <> 0 ->
    cell8 SEGS M (bl + 8 * idx) b -> 0 <= b -> b + 8 <= 2 ^ 47 ->
    (b <> 0 -> cell8 SEGS M b q0) ->
    exists R', aonly R R' /\
      ( ((b = 0 \/ q0 = 0) /\ msteps SEGS (st R B_PC) (st R' RET_PC) /\ getr R' 10%bv = Z_to_bv 64 0)
      \/ (b <> 0 /\ q0 <> 0 /\ 2 <= bv_unsigned w4 /\ msteps SEGS (st R B_PC) (st R' LM_PC)
          /\ getr R' 10%bv = Z_to_bv 64 q0 /\ getr R' 11%bv = Z_to_bv 64 key /\ getr R' 12%bv = Z_to_bv 64 bc
          /\ getr R' 13%bv = Z_to_bv 64 idx /\ getr R' 14%bv = sxw key)
      \/ (b <> 0 /\ q0 <> 0 /\ bv_unsigned w4 < 2 /\ msteps SEGS (st R B_PC) (st R' LP_PC)
          /\ getr R' 10%bv = Z_to_bv 64 q0 /\ getr R' 11%bv = Z_to_bv 64 key /\ getr R' 12%bv = Z_to_bv 64 (bc - 1)
          /\ getr R' 13%bv = Z_to_bv 64 idx /\ getr R' 14%bv = sxw key) ).
  Proof using fx AC L MI NS V nval rom A M obj bl bc keyp key ents U Hkey.
    intros R idx b q0 w4 H10 H11 H12 H13 H14 Hidx Hbc Hb Hb0 Hb1 Hq0.
    destruct Hhdr as [Hbl Hbc8 Hp1c Hsz Hmlf Hdef].
    pose proof bc_rng as Hbcr. pose proof (u_obj_lo U) as Ho0. pose proof (u_obj_hi U) as Ho1.
    pose proof (u_bl_lo U Hbc) as Hbl0. pose proof (u_bl_hi U) as Hbl1.
    pose proof (proj1 Hb) as Hbr.
    pose (E := Eseed R [Z_to_bv 64 obj; Z_to_bv 64 key; Z_to_bv 64 bc; Z_to_bv 64 idx; w4; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0;
                        Z_to_bv 64 bl; Z_to_bv 64 b; Z_to_bv 64 q0]).
    assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32); (11%bv, EVar 33); (12%bv, EVar 34); (13%bv, EVar 35); (14%bv, EVar 36)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
    assert (HK : know_ok SEGS E M []) by constructor.

    assert (Hrd_b : forall e, edenot E e = Z_to_bv 64 b ->
      sc_denot SEGS M E (SCReadBase (SA (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 35)) (EVar 40)) 0) 8 false e)).
    { intros e He. eapply (sc_read_cellw _ _ _ _ _ _ _ _ Hb); [cbn; lia| |exact He].
      evs. rewrite w_mul, w_add, v_addi_Z by lia. f_equal. lia. }
    assert (Hfl_b : sc_denot SEGS M E (SCFlat (SA (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 35)) (EVar 40)) 0) (ELit 8))).
    { eapply (sc_flat _ _ _ _ (bl + 8 * idx)); [evs; rewrite w_mul, w_add by lia; f_equal; lia | lia | cbn; lia | lia | cbn; lia]. }
    destruct (Z.eq_dec b 0) as [Hbz|Hbnz].
    -
      xrun HR HK 100%nat STOPS (SCR [true] [EVar 40; EVar 41; EVar 42] []) 50%N.
      { split_scs; try sc_auto1; first [exact Hfl_b | apply Hrd_b; evs; reflexivity]. }
      exists R'. split; [eapply aonly_of_syms; [exact HR'| reflexivity]|]. left.
      split; [left; exact Hbz|]. split; [exact Hms|]. rreg HR' 10%bv H. rewrite H, Hbz. reflexivity.
    - specialize (Hq0 Hbnz). pose proof (proj1 Hq0) as Hq0r.
      destruct (Z.eq_dec q0 0) as [Hqz|Hqnz].
      + xrun HR HK 100%nat STOPS (SCR [false; true] [EVar 40; EVar 41; EVar 42] []) 50%N.
        { split_scs; try sc_auto1; first [exact Hfl_b | apply Hrd_b; evs; reflexivity]. }
        exists R'. split; [eapply aonly_of_syms; [exact HR'| reflexivity]|]. left.
        split; [right; exact Hqz|]. split; [exact Hms|]. rreg HR' 10%bv H. rewrite H, Hqz. reflexivity.
      + destruct (Z.le_gt_cases 2 (bv_unsigned w4)) as [Hw|Hw].
        *
          xrun HR HK 100%nat STOPS (SCR [false; false; true] [EVar 40; EVar 41; EVar 42] []) 50%N.
          { split_scs; try sc_auto1; first [exact Hfl_b | apply Hrd_b; evs; reflexivity
                                            | cbn [sc_denot]; evs; rewrite branch_geu_lit_r by lia; bool_lia]. }
          exists R'. split; [eapply aonly_of_syms; [exact HR'| reflexivity]|]. right; left.
          rreg HR' 10%bv H10'. rreg HR' 11%bv H11'. rreg HR' 12%bv H12'. rreg HR' 13%bv H13'. rreg HR' 14%bv H14'.
          repeat split; try assumption. rewrite H14'. apply sextw_val. lia.
        *
          xrun HR HK 100%nat STOPS (SCR [false; false; false] [EVar 40; EVar 41; EVar 42] []) 50%N.
          { split_scs; try sc_auto1; first [exact Hfl_b | apply Hrd_b; evs; reflexivity
                                            | cbn [sc_denot]; evs; rewrite branch_geu_lit_r by lia; bool_lia]. }
          exists R'. split; [eapply aonly_of_syms; [exact HR'| reflexivity]|]. right; right.
          rreg HR' 10%bv H10'. rreg HR' 11%bv H11'. rreg HR' 12%bv H12'. rreg HR' 13%bv H13'. rreg HR' 14%bv H14'.
          repeat split; try assumption.
          -- rewrite H12'. apply w_addm; lia.
          -- rewrite H14'. apply sextw_val. lia.
  Qed.

  Definition found (r : Z) : Prop := r = 0 \/ exists v, In (r, (key, v)) ents.

  Ltac seedL R vals :=
    let E := fresh "E" in let HR := fresh "HR" in let HK := fresh "HK" in
    pose (E := Eseed R vals);
    assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32); (11%bv, EVar 33); (12%bv, EVar 34); (13%bv, EVar 35); (14%bv, EVar 36)]) R)
      by (apply regs_ok_srs; [apply regs_ok_seed|];
          repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption);
    assert (HK : know_ok SEGS E M []) by constructor.

  Ltac fin_ret HR' Hms r :=
    lazymatch type of HR' with regs_ok _ _ ?R1 =>
      exists R1, r; split; [exact Hms|]; split; [eapply aonly_of_syms; [exact HR'| reflexivity]|];
      split; [let H := fresh in rreg HR' 10%bv H; first [exact H | rewrite H; reflexivity] |]
    end.

  Lemma loopM : forall l2 l1 p k v R,
    ents = l1 ++ (p, (k, v)) :: l2 ->
    getr R 10%bv = Z_to_bv 64 p -> getr R 11%bv = Z_to_bv 64 key -> getr R 12%bv = Z_to_bv 64 bc ->
    getr R 13%bv = Z_to_bv 64 (key mod bc) -> getr R 14%bv = sxw key -> bc <> 0 ->
    exists R' r, msteps SEGS (st R LM_PC) (st R' RET_PC) /\ aonly R R' /\ getr R' 10%bv = Z_to_bv 64 r /\ found r.
  Proof using fx AC L MI NS V nval rom A M obj bl bc keyp key ents U Hkey HNS.
    induction l2 as [|[p' [k' v']] l2' IH]; intros l1 p k v R He H10 H11 H12 H13 H14 Hbc;
      pose proof bc_rng as Hbcr;
      destruct (node_facts l1 p k v _ He) as (Hp0 & Hp1 & Hh & Hk & Hkr & Hnx); cbn [hdaddr] in Hnx;
      pose proof (Z.mod_pos_bound key bc ltac:(lia)) as Hmk;
      pose proof (Z.mod_pos_bound k bc ltac:(lia)) as Hmk';
      unfold cell8 in Hh, Hnx; unfold cell4 in Hk.
    -
      destruct (Z.eq_dec k key) as [->|Hne].
      +
        seedL R [Z_to_bv 64 p; Z_to_bv 64 key; Z_to_bv 64 bc; Z_to_bv 64 (key mod bc); sxw key; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0;
                 Z_to_bv 64 key; sxw key].
        xrun HR HK 100%nat STOPS (SCR [true; true] [EVar 40; EVar 41] []) 50%N.
        { split_scs; try sc_auto1. sc_rd_sx Hk. }
        fin_ret HR' Hms p. right. exists v. rewrite He. apply in_app_iff. right. left. reflexivity.
      + destruct (Z.eq_dec (k mod bc) (key mod bc)) as [Hc|Hc].
        *
          seedL R [Z_to_bv 64 p; Z_to_bv 64 key; Z_to_bv 64 bc; Z_to_bv 64 (key mod bc); sxw key; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0;
                   Z_to_bv 64 k; Z_to_bv 64 0].
          destruct (Z.ltb_spec k bc).
          -- rewrite (Z.mod_small k bc) in Hc by lia.
             xrun HR HK 100%nat STOPS (SCR [false; true; true; true] [EVar 40; EVar 41] []) 50%N.
             { split_scs; try sc_auto1. }
             fin_ret HR' Hms 0. left; reflexivity.
          -- xrun HR HK 100%nat STOPS (SCR [false; false; true; true] [EVar 40; EVar 41] []) 50%N.
             { split_scs; try sc_auto1. cbn [sc_denot]. evs. rewrite w_remu, br_eq by lia. bool_lia. }
             fin_ret HR' Hms 0. left; reflexivity.
        *
          seedL R [Z_to_bv 64 p; Z_to_bv 64 key; Z_to_bv 64 bc; Z_to_bv 64 (key mod bc); sxw key; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0;
                   Z_to_bv 64 k].
          destruct (Z.ltb_spec k bc).
          -- rewrite (Z.mod_small k bc) in Hc by lia.
             xrun HR HK 100%nat STOPS (SCR [false; true; false] [EVar 40] []) 50%N.
             { split_scs; try sc_auto1. }
             fin_ret HR' Hms 0. left; reflexivity.
          -- xrun HR HK 100%nat STOPS (SCR [false; false; false] [EVar 40] []) 50%N.
             { split_scs; try sc_auto1. cbn [sc_denot]. evs. rewrite w_remu, br_eq by lia. bool_lia. }
             fin_ret HR' Hms 0. left; reflexivity.
    -
      assert (He' : ents = (l1 ++ [(p, (k, v))]) ++ (p', (k', v')) :: l2') by (rewrite He, <- app_assoc; reflexivity).
      destruct (node_facts _ p' k' v' _ He') as (Hp0' & Hp1' & _).
      destruct (Z.eq_dec k key) as [->|Hne].
      + seedL R [Z_to_bv 64 p; Z_to_bv 64 key; Z_to_bv 64 bc; Z_to_bv 64 (key mod bc); sxw key; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0;
                 Z_to_bv 64 key; sxw key].
        xrun HR HK 100%nat STOPS (SCR [true; true] [EVar 40; EVar 41] []) 50%N.
        { split_scs; try sc_auto1. sc_rd_sx Hk. }
        fin_ret HR' Hms p. right. exists v. rewrite He. apply in_app_iff. right. left. reflexivity.
      + destruct (Z.eq_dec (k mod bc) (key mod bc)) as [Hc|Hc].
        *
          seedL R [Z_to_bv 64 p; Z_to_bv 64 key; Z_to_bv 64 bc; Z_to_bv 64 (key mod bc); sxw key; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0;
                   Z_to_bv 64 k; Z_to_bv 64 p'].
          assert (STEP : exists R1, msteps SEGS (st R LM_PC) (st R1 LM_PC) /\ aonly R R1
                    /\ getr R1 10%bv = Z_to_bv 64 p' /\ getr R1 11%bv = Z_to_bv 64 key /\ getr R1 12%bv = Z_to_bv 64 bc
                    /\ getr R1 13%bv = Z_to_bv 64 (key mod bc) /\ getr R1 14%bv = sxw key).
          { destruct (Z.ltb_spec k bc).
            -- rewrite (Z.mod_small k bc) in Hc by lia.
               xrun HR HK 100%nat STOPS (SCR [false; true; true; false] [EVar 40; EVar 41] []) 50%N.
               { split_scs; try sc_auto1. }
               exists R'. split; [exact Hms|]. split; [eapply aonly_of_syms; [exact HR'| reflexivity]|].
               rreg HR' 10%bv H10'. rreg HR' 11%bv H11'. rreg HR' 12%bv H12'. rreg HR' 13%bv H13'. rreg HR' 14%bv H14'.
               repeat split; assumption.
            -- xrun HR HK 100%nat STOPS (SCR [false; false; true; false] [EVar 40; EVar 41] []) 50%N.
               { split_scs; try sc_auto1. cbn [sc_denot]. evs. rewrite w_remu, br_eq by lia. bool_lia. }
               exists R'. split; [exact Hms|]. split; [eapply aonly_of_syms; [exact HR'| reflexivity]|].
               rreg HR' 10%bv H10'. rreg HR' 11%bv H11'. rreg HR' 12%bv H12'. rreg HR' 13%bv H13'. rreg HR' 14%bv H14'.
               repeat split; assumption. }
          destruct STEP as (R1 & Hms1 & Ha1 & G10 & G11 & G12 & G13 & G14).
          destruct (IH (l1 ++ [(p, (k, v))]) p' k' v' R1 He' G10 G11 G12 G13 G14 Hbc) as (R' & r & Hms2 & Ha2 & Hr & Hf).
          exists R', r. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
          split; [eapply aonly_trans; eassumption|]. split; assumption.
        * seedL R [Z_to_bv 64 p; Z_to_bv 64 key; Z_to_bv 64 bc; Z_to_bv 64 (key mod bc); sxw key; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0;
                   Z_to_bv 64 k].
          destruct (Z.ltb_spec k bc).
          -- rewrite (Z.mod_small k bc) in Hc by lia.
             xrun HR HK 100%nat STOPS (SCR [false; true; false] [EVar 40] []) 50%N.
             { split_scs; try sc_auto1. }
             fin_ret HR' Hms 0. left; reflexivity.
          -- xrun HR HK 100%nat STOPS (SCR [false; false; false] [EVar 40] []) 50%N.
             { split_scs; try sc_auto1. cbn [sc_denot]. evs. rewrite w_remu, br_eq by lia. bool_lia. }
             fin_ret HR' Hms 0. left; reflexivity.
  Qed.

  Lemma land_1 : forall k, Z.land k 1 = k mod 2.
  Proof using. intros k. pose proof (Z.land_ones k 1 ltac:(lia)) as H. exact H. Qed.

  Lemma loopP : forall l2 l1 p k v R,
    ents = l1 ++ (p, (k, v)) :: l2 -> bc = 2 ->
    getr R 10%bv = Z_to_bv 64 p -> getr R 11%bv = Z_to_bv 64 key -> getr R 12%bv = Z_to_bv 64 (bc - 1) ->
    getr R 13%bv = Z_to_bv 64 (key mod bc) -> getr R 14%bv = sxw key ->
    exists R' r, msteps SEGS (st R LP_PC) (st R' RET_PC) /\ aonly R R' /\ getr R' 10%bv = Z_to_bv 64 r /\ found r.
  Proof using fx AC L MI NS V nval rom A M obj bl bc keyp key ents U Hkey HNS.
    induction l2 as [|[p' [k' v']] l2' IH]; intros l1 p k v R He Hbc2 H10 H11 H12 H13 H14;
      destruct (node_facts l1 p k v _ He) as (Hp0 & Hp1 & Hh & Hk & Hkr & Hnx); cbn [hdaddr] in Hnx;
      pose proof (Z.mod_pos_bound key bc ltac:(lia)) as Hmk;
      pose proof (Z.mod_pos_bound k bc ltac:(lia)) as Hmk';
      pose proof (Z.mod_pos_bound key 2 ltac:(lia)) as Hmk2;
      pose proof (Z.mod_pos_bound k 2 ltac:(lia)) as Hmk2';
      pose proof (land_1 k) as Hl1;
      unfold cell8 in Hh, Hnx; unfold cell4 in Hk.
    - destruct (Z.eq_dec k key) as [->|Hne].
      + seedL R [Z_to_bv 64 p; Z_to_bv 64 key; Z_to_bv 64 (bc - 1); Z_to_bv 64 (key mod bc); sxw key; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0;
                 Z_to_bv 64 key; sxw key].
        xrun HR HK 100%nat STOPS (SCR [true; true] [EVar 40; EVar 41] []) 50%N.
        { split_scs; try sc_auto1. sc_rd_sx Hk. }
        fin_ret HR' Hms p. right. exists v. rewrite He. apply in_app_iff. right. left. reflexivity.
      + destruct (Z.eq_dec (k mod bc) (key mod bc)) as [Hc|Hc].
        * seedL R [Z_to_bv 64 p; Z_to_bv 64 key; Z_to_bv 64 (bc - 1); Z_to_bv 64 (key mod bc); sxw key; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0;
                   Z_to_bv 64 k; Z_to_bv 64 0].
          xrun HR HK 100%nat STOPS (SCR [false; true; true] [EVar 40; EVar 41] []) 50%N.
          { split_scs; try sc_auto1. cbn [sc_denot]. evs. rewrite Hbc2. change (2 - 1) with 1. rewrite w_and, land_1, br_eq by lia. rewrite Hbc2 in Hc. bool_lia. }
          fin_ret HR' Hms 0. left; reflexivity.
        * seedL R [Z_to_bv 64 p; Z_to_bv 64 key; Z_to_bv 64 (bc - 1); Z_to_bv 64 (key mod bc); sxw key; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0;
                   Z_to_bv 64 k].
          xrun HR HK 100%nat STOPS (SCR [false; false] [EVar 40] []) 50%N.
          { split_scs; try sc_auto1. cbn [sc_denot]. evs. rewrite Hbc2. change (2 - 1) with 1. rewrite w_and, land_1, br_eq by lia. rewrite Hbc2 in Hc. bool_lia. }
          fin_ret HR' Hms 0. left; reflexivity.
    - assert (He' : ents = (l1 ++ [(p, (k, v))]) ++ (p', (k', v')) :: l2') by (rewrite He, <- app_assoc; reflexivity).
      destruct (node_facts _ p' k' v' _ He') as (Hp0' & Hp1' & _).
      destruct (Z.eq_dec k key) as [->|Hne].
      + seedL R [Z_to_bv 64 p; Z_to_bv 64 key; Z_to_bv 64 (bc - 1); Z_to_bv 64 (key mod bc); sxw key; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0;
                 Z_to_bv 64 key; sxw key].
        xrun HR HK 100%nat STOPS (SCR [true; true] [EVar 40; EVar 41] []) 50%N.
        { split_scs; try sc_auto1. sc_rd_sx Hk. }
        fin_ret HR' Hms p. right. exists v. rewrite He. apply in_app_iff. right. left. reflexivity.
      + destruct (Z.eq_dec (k mod bc) (key mod bc)) as [Hc|Hc].
        * seedL R [Z_to_bv 64 p; Z_to_bv 64 key; Z_to_bv 64 (bc - 1); Z_to_bv 64 (key mod bc); sxw key; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0;
                   Z_to_bv 64 k; Z_to_bv 64 p'].
          xrun HR HK 100%nat STOPS (SCR [false; true; false] [EVar 40; EVar 41] []) 50%N.
          { split_scs; try sc_auto1. cbn [sc_denot]. evs. rewrite Hbc2. change (2 - 1) with 1. rewrite w_and, land_1, br_eq by lia. rewrite Hbc2 in Hc. bool_lia. }
          rreg HR' 10%bv G10. rreg HR' 11%bv G11. rreg HR' 12%bv G12. rreg HR' 13%bv G13. rreg HR' 14%bv G14.
          pose proof (aonly_of_syms _ _ _ _ HR' eq_refl) as Ha1.
          destruct (IH (l1 ++ [(p, (k, v))]) p' k' v' R' He' Hbc2 G10 G11 G12 G13 G14) as (R'' & r & Hms2 & Ha2 & Hr & Hf).
          exists R'', r. split; [eapply msteps_trans; [exact Hms | exact Hms2]|].
          split; [eapply aonly_trans; eassumption|]. split; assumption.
        * seedL R [Z_to_bv 64 p; Z_to_bv 64 key; Z_to_bv 64 (bc - 1); Z_to_bv 64 (key mod bc); sxw key; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0;
                   Z_to_bv 64 k].
          xrun HR HK 100%nat STOPS (SCR [false; false] [EVar 40] []) 50%N.
          { split_scs; try sc_auto1. cbn [sc_denot]. evs. rewrite Hbc2. change (2 - 1) with 1. rewrite w_and, land_1, br_eq by lia. rewrite Hbc2 in Hc. bool_lia. }
          fin_ret HR' Hms 0. left; reflexivity.
  Qed.

  Lemma ret_step : forall R1 (ret : word),
    getr R1 1%bv = ret -> ret_ok ret ->
    msteps SEGS (st R1 RET_PC) (@mkst fx R1 ret M rom).
  Proof using fx rom M.
    intros R1 ret Hra Hret. unfold RET_PC. norm_pc.
    stepjr F_69800 D_69800 ret ltac:(exact Hra).
    change (bv_signed (0%bv : bv 12)) with 0%Z. unfold ret_ok in Hret. rewrite Hret. apply mst_refl.
  Qed.

  Theorem find_correct : forall R (ret : word),
    getr R 10%bv = Z_to_bv 64 obj -> getr R 11%bv = Z_to_bv 64 keyp ->
    getr R 1%bv = ret -> ret_ok ret ->
    exists R' (p : Z),
      msteps SEGS (st R FIND) (@mkst fx R' ret M rom)
      /\ keeps_cs R R' /\ getr R' 10%bv = Z_to_bv 64 p /\ found p.
  Proof using fx AC L MI NS V nval rom A M obj bl bc keyp key ents U Hkey Hkp0 Hkp1 HNS.
    intros R ret H10 H11 Hra Hret.
    pose proof bc_rng as Hbcr. pose proof (u_obj_hi U) as Ho1. pose proof (u_obj_lo U) as Ho0.
    destruct (Z.eq_dec bc 0) as [Hbc0|Hbc].
    { destruct (blkA0 R H10 H11 Hbc0) as (R1 & Hms1 & Ha1 & G10).
      exists R1, 0. split; [eapply msteps_trans; [exact Hms1 | apply ret_step; [|exact Hret]]|].
      { rewrite (Ha1 1%bv) by (first [solve [clear; cbn; tauto] | cbn; tauto]). exact Hra. }
      split; [apply aonly_kept; exact Ha1|]. split; [exact G10 | left; reflexivity]. }
    destruct (blkA R H10 H11 Hbc) as (R1 & Hms1 & Ha1 & G10 & G11 & G12 & G13 & G14).
    pose proof (Z.mod_pos_bound key bc ltac:(lia)) as Hidx.
    destruct (u_bkt U (hmod key bc) ltac:(unfold hmod; lia)) as (b & Hb & Hbok).

    assert (Hq : exists q0 pre l,
              0 <= b /\ b + 8 <= 2 ^ 47 /\ (b <> 0 -> cell8 SEGS M b q0)
              /\ (b <> 0 -> q0 = hdaddr l /\ ents = pre ++ l)).
    { destruct Hbok as [Hb0 | [Hbn | (Hbs & Hne & _)]].
      - exists 0, [], ents. subst b. split; [lia|]. split; [lia|]. split; intros HH; exfalso; exact (HH eq_refl).
      - destruct (in_split_ents V b ents Hbn) as (l1 & k & v & l2 & He).
        destruct (node_facts l1 b k v l2 He) as (Hp0 & Hp1 & _ & _ & _ & Hnx).
        exists (hdaddr l2), (l1 ++ [(b, (k, v))]), l2. split; [lia|]. split; [lia|]. split; [intros _; exact Hnx|].
        intros _. split; [reflexivity|]. rewrite He, <- app_assoc. reflexivity.
      - exists (hdaddr ents), [], ents. subst b. split; [lia|]. split; [lia|].
        split; [intros _; exact (h_p1 (u_hdr U))|]. intros _. split; reflexivity. }
    destruct Hq as (q0 & pre & l & Hb0 & Hb1 & Hbq & Hql).
    destruct (blkB R1 (hmod key bc) b q0 (popcw (Z_to_bv 64 bc)) G10 G11 G12 G13 G14 ltac:(unfold hmod; lia) Hbc Hb Hb0 Hb1 Hbq)
      as (R2 & Ha2 & [ (Hz & Hms2 & F10) | [ (Hbn & Hqn & Hw & Hms2 & F10 & F11 & F12 & F13 & F14)
                                          | (Hbn & Hqn & Hw & Hms2 & F10 & F11 & F12 & F13 & F14) ] ]).
    -
      exists R2, 0. split.
      { eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2|]. apply ret_step; [|exact Hret].
        rewrite (Ha2 1%bv), (Ha1 1%bv) by (first [solve [clear; cbn; tauto] | cbn; tauto]). exact Hra. }
      split; [apply aonly_kept; eapply aonly_trans; eassumption|]. split; [exact F10 | left; reflexivity].
    -
      destruct (Hql Hbn) as [Hq0 He]. destruct (hdaddr_cases l) as [[Hl0 _] | (p & k & v & l2 & Hl & Hlp)]; [exfalso; lia|].
      subst l. cbn [hdaddr] in Hq0. subst q0.
      destruct (loopM l2 pre p k v R2 He F10 F11 F12 ltac:(exact F13) F14 Hbc) as (R3 & r & Hms3 & Ha3 & Hr & Hf).
      exists R3, r. split.
      { eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2|]. eapply msteps_trans; [exact Hms3|].
        apply ret_step; [|exact Hret]. rewrite (Ha3 1%bv), (Ha2 1%bv), (Ha1 1%bv) by (first [solve [clear; cbn; tauto] | cbn; tauto]). exact Hra. }
      split; [apply aonly_kept; eapply aonly_trans; [eapply aonly_trans|]; eassumption|]. split; assumption.
    -
      assert (Hbc2 : bc = 2).
      { destruct (popcw_cases bc Hbc_in Hbc) as [[E _]|[_ Hge]]; [exact E | exfalso; lia]. }
      destruct (Hql Hbn) as [Hq0 He]. destruct (hdaddr_cases l) as [[Hl0 _] | (p & k & v & l2 & Hl & Hlp)]; [exfalso; lia|].
      subst l. cbn [hdaddr] in Hq0. subst q0.
      destruct (loopP l2 pre p k v R2 He Hbc2 F10 F11 F12 ltac:(exact F13) F14) as (R3 & r & Hms3 & Ha3 & Hr & Hf).
      exists R3, r. split.
      { eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2|]. eapply msteps_trans; [exact Hms3|].
        apply ret_step; [|exact Hret]. rewrite (Ha3 1%bv), (Ha2 1%bv), (Ha1 1%bv) by (first [solve [clear; cbn; tauto] | cbn; tauto]). exact Hra. }
      split; [apply aonly_kept; eapply aonly_trans; [eapply aonly_trans|]; eassumption|]. split; assumption.
  Qed.

End FindProof.

Theorem find_spec {AC : AllocCeiling} : forall (L : Layout) (MI : MallocIface SEGS L) (NS : Z) (V : Type) (nval : mem -> Z -> V -> Prop),
  find_stmt SEGS L MI FIND NS V nval.
Proof.
  intros L MI NS V nval fx A R M obj bl bc keyp key ents ret U HNS Hkey Hkp0 Hkp1 H10 H11 Hra Hret.
  exact (find_correct L MI NS V nval (seg_rom SEGS) A M obj bl bc keyp key ents U Hkey Hkp0 Hkp1 HNS R ret H10 H11 Hra Hret).
Qed.
End HFind2.

Module S1_code_69948_69a68.

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.
End S1_code_69948_69a68.

Module HFindNT.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StepTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.WalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ShapeAlg OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SRealizes OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibEff OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3Sound OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymRun3.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HConstsS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HFind OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmInstS1.S1_code_69948_69a68.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation SEGS := Plain.M.loaded_segments.

Definition NTF_ENTRY : Z := 0x69988.
Definition B3_PC     : Z := 0x69a34.
Definition LM3_PC    : Z := 0x69a90.
Definition LP3_PC    : Z := 0x69a6c.
Definition NTF_MISS  : Z := 0x69aa4.
Definition NTF_HIT   : Z := 0x69b64.
Definition STOPS3 : list Z := [B3_PC; LM3_PC; LP3_PC; NTF_MISS; NTF_HIT].

Definition popc3 : expr :=
  Eval vm_compute in
    (let '(ss, _, _) := sym_exec SEGS 100 true STOPS3 (SCR [false; false] [EVar 34; EVar 35] [])
                          (SS NTF_ENTRY (srs sr_id [(10%bv, EVar 32); (8%bv, EVar 33)]) [] [] 50) [] in
     sr_get (s_regs ss) 16%bv).
Definition popcw3 (w : word) : word := edenot (Env (fun _ => w) (fun _ => [])) popc3.

Lemma popc3_env : forall E, edenot E popc3 = popcw3 (ev E 34).
Proof. intros E. unfold popcw3, popc3. cbn [edenot ev]. reflexivity. Qed.

Ltac vm_popc3 :=
  match goal with |- context [bv_unsigned (popcw3 ?w)] =>
    let v := eval vm_compute in (bv_unsigned (popcw3 w)) in
    replace (bv_unsigned (popcw3 w)) with v by (vm_compute; reflexivity) end.

Lemma popcw3_cases : forall bc, In bc BSEQ -> bc <> 0 ->
  (bc = 2 /\ bv_unsigned (popcw3 (Z_to_bv 64 bc)) = 1) \/ (bc <> 2 /\ 2 <= bv_unsigned (popcw3 (Z_to_bv 64 bc))).
Proof.
  intros bc Hin Hnz. unfold BSEQ in Hin.
  repeat (destruct Hin as [<-|Hin];
    [ first [ exfalso; lia
            | left; split; [reflexivity | vm_popc3; reflexivity]
            | right; split; [lia | vm_popc3; lia] ] |]).
  destruct Hin.
Qed.

Lemma sx32_sxw : forall k, 0 <= k < 2 ^ 32 -> Z_to_bv 64 (HStmts.sx32 k) = sxw k.
Proof.
  intros k Hk. unfold HStmts.sx32, sxw. rewrite bv_swrap32_cases by lia.
  apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
  destruct (Z.ltb_spec k (2 ^ 31)); [reflexivity|].
  replace (k + 2 ^ 64 - 2 ^ 32) with ((k - 2 ^ 32) + 1 * 2 ^ 64) by lia.
  rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma low32_sxw : forall k, 0 <= k < 2 ^ 32 -> low32 (sxw k) = low32 (Z_to_bv 64 k).
Proof.
  intros k Hk. unfold low32, sxw. apply bv_eq. rewrite !bv_extract_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod, !Z.shiftr_0_r.
  unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32).
  rewrite bv_swrap32_cases by lia. destruct (Z.ltb_spec k (2 ^ 31)); [reflexivity|].
  replace ((k - 2 ^ 32) mod 2 ^ 64) with (k - 2 ^ 32 + 2 ^ 64).
  2:{ rewrite <- (Z.mod_add _ 1) by lia. symmetry. apply Z.mod_small. lia. }
  replace (k - 2 ^ 32 + 2 ^ 64) with (k + (2 ^ 32 - 1) * 2 ^ 32) by lia. rewrite Z.mod_add by lia. rewrite (Z.mod_small k (2 ^ 64)) by lia. reflexivity.
Qed.

Lemma zext_sxw : forall k, 0 <= k < 2 ^ 32 ->
  alu64 ALU_SRL (mul_div M_MUL (Z_to_bv 64 4294967296) (sxw k)) (Z_to_bv 64 32) = Z_to_bv 64 k.
Proof.
  intros k Hk. unfold sxw. apply bv_eq. cbn [alu64 alu mul_div].
  rewrite bv_shiftr_unsigned, bv_mul_unsigned, bv_and_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite (Z.mod_small 4294967296), (Z.mod_small 32), (Z.mod_small 63), (Z.mod_small k) by lia.
  change (Z.land 32 63) with 32. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 32) with 4294967296.
  rewrite bv_swrap32_cases by lia. destruct (Z.ltb_spec k (2 ^ 31)).
  - rewrite (Z.mod_small k), Z.mod_small by lia. rewrite Z.mul_comm, Z.div_mul by lia. reflexivity.
  - replace ((k - 2 ^ 32) mod 2 ^ 64) with (k - 2 ^ 32 + 2 ^ 64).
    2:{ rewrite <- (Z.mod_add _ 1) by lia. symmetry. apply Z.mod_small. lia. }
    replace (4294967296 * (k - 2 ^ 32 + 2 ^ 64)) with (k * 4294967296 + (4294967296 - 1) * 2 ^ 64) by lia.
    rewrite Z.mod_add, Z.mod_small by lia. rewrite Z.div_mul by lia. reflexivity.
Qed.

Ltac in_bv := cbn [In]; first [left; apply bv_eq; vm_compute; reflexivity | right; in_bv].

Section NTFind.
  Context {fx : FPState}.
Context {AC : AllocCeiling}.
  Variable L : Layout.
  Variable MI : MallocIface SEGS L.
  Variable rom : word -> option byte.

  Variables (A : AS MI) (M : mem) (this bl bc tid : Z) (ents : list (Z * (Z * (Z * Z * Z)))).
  Hypothesis U : umapx MI 32 (nval32 SEGS) A M (this + 136) bl bc ents.
  Hypothesis Htid : 0 <= tid < 2 ^ 32.
  Hypothesis Hthis0 : 0 < this.
  Hypothesis Hthis1 : this + 288 <= 2 ^ 47.

  #[local] Abbreviation st R pc := (@mkst fx R (Z_to_bv 64 pc) M rom).

  Let Hbc_in : In bc BSEQ := u_bseq U.

  Lemma bc_rng3 : 0 <= bc <= 26339969.
  Proof using AC L MI A M this bl bc ents U. exact (BSEQ_bound bc Hbc_in). Qed.

  Lemma node_facts3 : forall l1 p k v l2, ents = l1 ++ (p, (k, v)) :: l2 ->
    0 < p /\ p + 32 <= 2 ^ 47 /\ cell8 SEGS M (p + 8) k /\ cell4 SEGS M (p + 16) k /\ 0 <= k < 2 ^ 32
    /\ cell8 SEGS M p (hdaddr l2).
  Proof using AC L MI A M this bl bc ents U.
    intros l1 p k v l2 He.
    destruct (u_node U p k v) as (_ & Hp0 & Hp1 & _ & Hh & Hk & Hkr & _).
    { rewrite He. apply in_app_iff. right. left. reflexivity. }
    split; [lia|]. split; [lia|]. split; [exact Hh|]. split; [exact Hk|]. split; [lia|].
    apply (chain_at _ M l1 p k v l2). rewrite <- He. exact (u_chain U).
  Qed.

  Lemma hdaddr_cases3 : forall (l2 : list (Z * (Z * (Z * Z * Z)))),
    hdaddr l2 = 0 /\ l2 = [] \/ exists p k v l2', l2 = (p, (k, v)) :: l2' /\ hdaddr l2 = p.
  Proof using.
    intros [|[p [k v]] l2']; [left; split; reflexivity | right]. exists p, k, v, l2'. split; reflexivity.
  Qed.

  Definition keep3 : list reg := [1; 2; 3; 4; 5; 6; 7; 9; 11; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
  Definition kept3 (R R' : bvmap 5 word) : Prop :=
    (forall r, In r keep3 -> getr R' r = getr R r) /\ getr R' 10%bv = getr R 10%bv /\ getr R' 8%bv = getr R 8%bv.
  Lemma kept3_trans : forall R1 R2 R3, kept3 R1 R2 -> kept3 R2 R3 -> kept3 R1 R3.
  Proof using.
    intros R1 R2 R3 (A1 & B1 & C1) (A2 & B2 & C2). split; [| split; congruence].
    intros r Hr. rewrite (A2 r Hr). apply A1, Hr.
  Qed.
  Lemma kept3_all : forall R R', kept3 R R' -> forall r, ~ In r [12; 13; 14; 15; 16; 17]%bv -> getr R' r = getr R r.
  Proof using.
    intros R R' (HA & HB & HC) r Hr.
    pose proof (bv_unsigned_in_range _ r) as Hrr. change (bv_modulus 5) with 32 in Hrr.
    assert (E : r = Z_to_bv 5 (bv_unsigned r)) by (symmetry; apply Z_to_bv_bv_unsigned).
    assert (Hn : exists n, (n < 32)%nat /\ bv_unsigned r = Z.of_nat n) by (exists (Z.to_nat (bv_unsigned r)); split; lia).
    destruct Hn as (n & Hn & Hzn). rewrite Hzn in E. clear Hzn Hrr. subst r.
    do 32 (destruct n as [|n];
      [ first [ apply HA; in_bv
              | etransitivity; [| exact HB]; f_equal; apply bv_eq; vm_compute; reflexivity
              | etransitivity; [| exact HC]; f_equal; apply bv_eq; vm_compute; reflexivity
              | exfalso; apply Hr; in_bv
              | unfold getr; vm_compute; reflexivity ] |]).
    lia.
  Qed.
  Ltac kept3_of HR' H10 H8 :=
    split; [exact (syms_id_sound _ _ _ _ keep3 HR' eq_refl)
          | split; [let Q := fresh in rreg HR' 10%bv Q; rewrite Q; symmetry; exact H10
                   | let Q := fresh in rreg HR' 8%bv Q; rewrite Q; symmetry; exact H8]].

  Lemma blkA3 : forall R,
    getr R 10%bv = Z_to_bv 64 this -> getr R 8%bv = sxw tid ->
    exists R', kept3 R R' /\
      ( (bc = 0 /\ msteps SEGS (st R NTF_ENTRY) (st R' NTF_MISS))
      \/ (bc <> 0 /\ msteps SEGS (st R NTF_ENTRY) (st R' B3_PC)
          /\ getr R' 12%bv = Z_to_bv 64 bc /\ getr R' 13%bv = Z_to_bv 64 tid /\ getr R' 14%bv = Z_to_bv 64 bl
          /\ getr R' 15%bv = Z_to_bv 64 (hmod tid bc) /\ getr R' 16%bv = popcw3 (Z_to_bv 64 bc)) ).
  Proof using fx AC L MI rom A M this bl bc tid ents U Htid Hthis0 Hthis1.
    intros R H10 H8. pose proof (u_hdr U) as HD. destruct HD as [Hbl Hbc8 Hp1c Hsz Hmlf Hdef].
    pose proof bc_rng3 as Hbcr. pose proof (u_bl_hi U) as Hbl1.
    unfold cell8 in Hbl, Hbc8. pose proof (proj1 Hbl) as Hblr.
    replace (this + 136 + 8) with (this + 144) in Hbc8 by lia.
    pose (E := Eseed R [Z_to_bv 64 this; sxw tid; Z_to_bv 64 bc; Z_to_bv 64 bl]).
    assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32); (8%bv, EVar 33)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
    assert (HK : know_ok SEGS E M []) by constructor.
    assert (Hpc : forall b : bool, branch_taken BC_LTU (edenot E (ELit 1)) (edenot E popc3) = b ->
                  sc_denot SEGS M E (SCBr b BC_LTU (ELit 1) popc3)).
    { intros b Hb. exact Hb. }
    pose proof (zext_sxw tid Htid) as Hz.
    destruct (Z.eq_dec bc 0) as [Hbc0 | Hbc].
    - xrun HR HK 100%nat STOPS3 (SCR [true] [EVar 34; EVar 35] []) 50%N.
      { split_scs; try sc_auto1. }
      exists R'. split; [kept3_of HR' H10 H8|]. left. split; [exact Hbc0 | exact Hms].
    - destruct (popcw3_cases bc Hbc_in Hbc) as [[Hbc2 Hp1] | [Hbc2 Hp2]].
      +
        xrun HR HK 100%nat STOPS3 (SCR [false; false] [EVar 34; EVar 35] []) 50%N.
        { split_scs; try sc_auto1.
          apply Hpc. rewrite popc3_env. evs. rewrite branch_ltu_lit_l by lia. bool_lia. }
        exists R'. split; [kept3_of HR' H10 H8|]. right. split; [exact Hbc|]. split; [exact Hms|].
        rreg HR' 12%bv H12'. rreg HR' 13%bv H13'. rreg HR' 14%bv H14'. rreg HR' 15%bv H15'.
        rewrite Hz in H13', H15'.
        repeat split; try assumption.
        * rewrite H15'. rewrite w_addm, w_and by lia. subst bc. unfold hmod.
          change (2 + -1) with (Z.ones 1). rewrite Z.land_comm, Z.land_ones by lia. reflexivity.
        * lazymatch type of HR' with regs_ok ?E' _ _ => exact (eq_trans (HR' 16%bv) (popc3_env E')) end.
      + destruct (Z.ltb_spec tid bc) as [Hlt|Hge].
        *
          xrun HR HK 100%nat STOPS3 (SCR [false; true; true] [EVar 34; EVar 35] []) 50%N.
          { split_scs; try sc_auto1.
            - cbn [sc_denot]. evs. rewrite Hz. rewrite br_ltu by lia. bool_lia.
            - apply Hpc. rewrite popc3_env. evs. rewrite branch_ltu_lit_l by lia. bool_lia. }
          exists R'. split; [kept3_of HR' H10 H8|]. right. split; [exact Hbc|]. split; [exact Hms|].
          rreg HR' 12%bv H12'. rreg HR' 13%bv H13'. rreg HR' 14%bv H14'. rreg HR' 15%bv H15'.
          rewrite Hz in H13', H15'.
          repeat split; try assumption.
          -- rewrite H15'. unfold hmod. rewrite Z.mod_small by lia. reflexivity.
          -- lazymatch type of HR' with regs_ok ?E' _ _ => exact (eq_trans (HR' 16%bv) (popc3_env E')) end.
        *
          xrun HR HK 100%nat STOPS3 (SCR [false; true; false] [EVar 34; EVar 35] []) 50%N.
          { split_scs; try sc_auto1.
            - cbn [sc_denot]. evs. rewrite Hz. rewrite br_ltu by lia. bool_lia.
            - apply Hpc. rewrite popc3_env. evs. rewrite branch_ltu_lit_l by lia. bool_lia. }
          exists R'. split; [kept3_of HR' H10 H8|]. right. split; [exact Hbc|]. split; [exact Hms|].
          rreg HR' 12%bv H12'. rreg HR' 13%bv H13'. rreg HR' 14%bv H14'. rreg HR' 15%bv H15'.
          rewrite Hz in H13'.
          repeat split; try assumption.
          -- rewrite H15'. rewrite low32_sxw by lia. unfold hmod. apply remuw_val; lia.
          -- lazymatch type of HR' with regs_ok ?E' _ _ => exact (eq_trans (HR' 16%bv) (popc3_env E')) end.
  Qed.

  Lemma blkB3 : forall R idx b q0 (w4 : word),
    getr R 10%bv = Z_to_bv 64 this -> getr R 8%bv = sxw tid ->
    getr R 12%bv = Z_to_bv 64 bc -> getr R 13%bv = Z_to_bv 64 tid -> getr R 14%bv = Z_to_bv 64 bl ->
    getr R 15%bv = Z_to_bv 64 idx -> getr R 16%bv = w4 ->
    0 <= idx < bc -> bc <> 0 ->
    cell8 SEGS M (bl + 8 * idx) b -> 0 <= b -> b + 8 <= 2 ^ 47 ->
    (b <> 0 -> cell8 SEGS M b q0) ->
    exists R', kept3 R R' /\
      ( ((b = 0 \/ q0 = 0) /\ msteps SEGS (st R B3_PC) (st R' NTF_MISS))
      \/ (b <> 0 /\ q0 <> 0 /\ 2 <= bv_unsigned w4 /\ msteps SEGS (st R B3_PC) (st R' LM3_PC)
          /\ getr R' 14%bv = Z_to_bv 64 q0 /\ getr R' 12%bv = Z_to_bv 64 bc /\ getr R' 13%bv = Z_to_bv 64 tid
          /\ getr R' 15%bv = Z_to_bv 64 idx)
      \/ (b <> 0 /\ q0 <> 0 /\ bv_unsigned w4 < 2 /\ msteps SEGS (st R B3_PC) (st R' LP3_PC)
          /\ getr R' 14%bv = Z_to_bv 64 q0 /\ getr R' 12%bv = Z_to_bv 64 (bc - 1) /\ getr R' 13%bv = Z_to_bv 64 tid
          /\ getr R' 15%bv = Z_to_bv 64 idx) ).
  Proof using fx AC L MI rom A M this bl bc tid ents U.
    intros R idx b q0 w4 H10 H8 H12 H13 H14 H15 H16 Hidx Hbc Hb Hb0 Hb1 Hq0.
    pose proof bc_rng3 as Hbcr. pose proof (u_bl_lo U Hbc) as Hbl0. pose proof (u_bl_hi U) as Hbl1.
    pose proof (proj1 Hb) as Hbr.
    pose (E := Eseed R [Z_to_bv 64 this; sxw tid; Z_to_bv 64 bc; Z_to_bv 64 tid; Z_to_bv 64 bl; Z_to_bv 64 idx; w4; Z_to_bv 64 0;
                        Z_to_bv 64 b; Z_to_bv 64 q0]).
    assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32); (8%bv, EVar 33); (12%bv, EVar 34); (13%bv, EVar 35); (14%bv, EVar 36); (15%bv, EVar 37); (16%bv, EVar 38)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
    assert (HK : know_ok SEGS E M []) by constructor.
    assert (Hrd_b : forall (e : expr) (ba : expr), edenot E e = Z_to_bv 64 b ->
      edenot E ba = Z_to_bv 64 (bl + 8 * idx) ->
      sc_denot SEGS M E (SCReadBase (SA ba 0) 8 false e)).
    { intros e ba He Hba. eapply (sc_read_cellw _ _ _ _ _ _ _ _ Hb); [cbn; lia| |exact He].
      unfold adenot. cbn [a_base a_off]. rewrite Hba, v_addi_Z by lia. f_equal. lia. }
    Ltac scB Hrd_b := split_scs; try sc_auto1;
      first [ apply Hrd_b; evs; rewrite ?w_mul, ?w_add by lia; first [reflexivity | f_equal; lia]
            | eapply sc_flat; [evs; rewrite ?w_mul, ?w_add by lia; reflexivity | lia | cbn [a_off]; lia | lia | cbn [a_off]; lia]
            | cbn [sc_denot]; evs; rewrite branch_geu_lit_r by lia; bool_lia
            | idtac ].
    destruct (Z.eq_dec b 0) as [Hbz|Hbnz].
    - xrun HR HK 100%nat STOPS3 (SCR [true] [EVar 40; EVar 41] []) 50%N; [scB Hrd_b|].
      exists R'. split; [kept3_of HR' H10 H8|]. left. split; [left; exact Hbz | exact Hms].
    - specialize (Hq0 Hbnz). pose proof (proj1 Hq0) as Hq0r.
      destruct (Z.eq_dec q0 0) as [Hqz|Hqnz].
      + xrun HR HK 100%nat STOPS3 (SCR [false; true] [EVar 40; EVar 41] []) 50%N; [scB Hrd_b|].
        exists R'. split; [kept3_of HR' H10 H8|]. left. split; [right; exact Hqz | exact Hms].
      + destruct (Z.le_gt_cases 2 (bv_unsigned w4)) as [Hw|Hw].
        * xrun HR HK 100%nat STOPS3 (SCR [false; false; true] [EVar 40; EVar 41] []) 50%N; [scB Hrd_b|].
          exists R'. split; [kept3_of HR' H10 H8|]. right; left.
          rreg HR' 14%bv G14. rreg HR' 12%bv G12. rreg HR' 13%bv G13. rreg HR' 15%bv G15.
          repeat split; assumption.
        * xrun HR HK 100%nat STOPS3 (SCR [false; false; false] [EVar 40; EVar 41] []) 50%N; [scB Hrd_b|].
          exists R'. split; [kept3_of HR' H10 H8|]. right; right.
          rreg HR' 14%bv G14. rreg HR' 12%bv G12. rreg HR' 13%bv G13. rreg HR' 15%bv G15.
          repeat split; try assumption. rewrite G12. apply w_addm; lia.
  Qed.

  Definition walk3 (R : bvmap 5 word) (pc0 : Z) (R' : bvmap 5 word) : Prop :=
    kept3 R R' /\
    ( (exists p v, In (p, (tid, v)) ents /\ msteps SEGS (st R pc0) (st R' NTF_HIT) /\ getr R' 14%bv = Z_to_bv 64 p)
      \/ msteps SEGS (st R pc0) (st R' NTF_MISS) ).

  Ltac seed3 R vals :=
    let E := fresh "E" in let HR := fresh "HR" in let HK := fresh "HK" in
    pose (E := Eseed R vals);
    assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32); (8%bv, EVar 33); (12%bv, EVar 34); (13%bv, EVar 35); (14%bv, EVar 36); (15%bv, EVar 37)]) R)
      by (apply regs_ok_srs; [apply regs_ok_seed|];
          repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption);
    assert (HK : know_ok SEGS E M []) by constructor.

  Ltac fin_hit HR' Hms p v He H10 H8 :=
    lazymatch type of HR' with regs_ok _ _ ?R1 =>
      exists R1; split; [kept3_of HR' H10 H8|];
      left; exists p, v; split; [rewrite He; apply in_app_iff; right; left; reflexivity|];
      split; [exact Hms | let G := fresh in rreg HR' 14%bv G; exact G]
    end.
  Ltac fin_miss HR' Hms H10 H8 :=
    lazymatch type of HR' with regs_ok _ _ ?R1 =>
      exists R1; split; [kept3_of HR' H10 H8|]; right; exact Hms
    end.

  Lemma loopM3 : forall l2 l1 p k v R,
    ents = l1 ++ (p, (k, v)) :: l2 ->
    getr R 10%bv = Z_to_bv 64 this -> getr R 8%bv = sxw tid ->
    getr R 14%bv = Z_to_bv 64 p -> getr R 12%bv = Z_to_bv 64 bc -> getr R 13%bv = Z_to_bv 64 tid ->
    getr R 15%bv = Z_to_bv 64 (tid mod bc) -> bc <> 0 ->
    exists R', walk3 R LM3_PC R'.
  Proof using fx AC L MI rom A M this bl bc tid ents U Htid.
    induction l2 as [|[p' [k' v']] l2' IH]; intros l1 p k v R He H10 H8 H14 H12 H13 H15 Hbc;
      pose proof bc_rng3 as Hbcr;
      destruct (node_facts3 l1 p k v _ He) as (Hp0 & Hp1 & Hh & Hk & Hkr & Hnx); cbn [hdaddr] in Hnx;
      pose proof (Z.mod_pos_bound tid bc ltac:(lia)) as Hmk;
      pose proof (Z.mod_pos_bound k bc ltac:(lia)) as Hmk';
      unfold cell8 in Hh, Hnx; unfold cell4 in Hk; unfold walk3.
    - destruct (Z.eq_dec k tid) as [->|Hne].
      + seed3 R [Z_to_bv 64 this; sxw tid; Z_to_bv 64 bc; Z_to_bv 64 tid; Z_to_bv 64 p; Z_to_bv 64 (tid mod bc); Z_to_bv 64 0; Z_to_bv 64 0;
                 Z_to_bv 64 tid; sxw tid].
        xrun HR HK 100%nat STOPS3 (SCR [true; true] [EVar 40; EVar 41] []) 50%N.
        { split_scs; try sc_auto1. sc_rd_sx Hk. }
        fin_hit HR' Hms p v He H10 H8.
      + destruct (Z.eq_dec (k mod bc) (tid mod bc)) as [Hc|Hc].
        * seed3 R [Z_to_bv 64 this; sxw tid; Z_to_bv 64 bc; Z_to_bv 64 tid; Z_to_bv 64 p; Z_to_bv 64 (tid mod bc); Z_to_bv 64 0; Z_to_bv 64 0;
                   Z_to_bv 64 k; Z_to_bv 64 0].
          destruct (Z.ltb_spec k bc).
          -- rewrite (Z.mod_small k bc) in Hc by lia.
             xrun HR HK 100%nat STOPS3 (SCR [false; true; true; true] [EVar 40; EVar 41] []) 50%N; [split_scs; try sc_auto1|].
             fin_miss HR' Hms H10 H8.
          -- xrun HR HK 100%nat STOPS3 (SCR [false; false; true; true] [EVar 40; EVar 41] []) 50%N.
             { split_scs; try sc_auto1. cbn [sc_denot]. evs. rewrite w_remu, br_eq by lia. bool_lia. }
             fin_miss HR' Hms H10 H8.
        * seed3 R [Z_to_bv 64 this; sxw tid; Z_to_bv 64 bc; Z_to_bv 64 tid; Z_to_bv 64 p; Z_to_bv 64 (tid mod bc); Z_to_bv 64 0; Z_to_bv 64 0;
                   Z_to_bv 64 k].
          destruct (Z.ltb_spec k bc).
          -- rewrite (Z.mod_small k bc) in Hc by lia.
             xrun HR HK 100%nat STOPS3 (SCR [false; true; false] [EVar 40] []) 50%N; [split_scs; try sc_auto1|].
             fin_miss HR' Hms H10 H8.
          -- xrun HR HK 100%nat STOPS3 (SCR [false; false; false] [EVar 40] []) 50%N.
             { split_scs; try sc_auto1. cbn [sc_denot]. evs. rewrite w_remu, br_eq by lia. bool_lia. }
             fin_miss HR' Hms H10 H8.
    - assert (He' : ents = (l1 ++ [(p, (k, v))]) ++ (p', (k', v')) :: l2') by (rewrite He, <- app_assoc; reflexivity).
      destruct (node_facts3 _ p' k' v' _ He') as (Hp0' & Hp1' & _).
      destruct (Z.eq_dec k tid) as [->|Hne].
      + seed3 R [Z_to_bv 64 this; sxw tid; Z_to_bv 64 bc; Z_to_bv 64 tid; Z_to_bv 64 p; Z_to_bv 64 (tid mod bc); Z_to_bv 64 0; Z_to_bv 64 0;
                 Z_to_bv 64 tid; sxw tid].
        xrun HR HK 100%nat STOPS3 (SCR [true; true] [EVar 40; EVar 41] []) 50%N.
        { split_scs; try sc_auto1. sc_rd_sx Hk. }
        fin_hit HR' Hms p v He H10 H8.
      + destruct (Z.eq_dec (k mod bc) (tid mod bc)) as [Hc|Hc].
        * seed3 R [Z_to_bv 64 this; sxw tid; Z_to_bv 64 bc; Z_to_bv 64 tid; Z_to_bv 64 p; Z_to_bv 64 (tid mod bc); Z_to_bv 64 0; Z_to_bv 64 0;
                   Z_to_bv 64 k; Z_to_bv 64 p'].
          assert (STEP : exists R1, msteps SEGS (st R LM3_PC) (st R1 LM3_PC) /\ kept3 R R1
                    /\ getr R1 14%bv = Z_to_bv 64 p' /\ getr R1 12%bv = Z_to_bv 64 bc /\ getr R1 13%bv = Z_to_bv 64 tid
                    /\ getr R1 15%bv = Z_to_bv 64 (tid mod bc) /\ getr R1 10%bv = Z_to_bv 64 this /\ getr R1 8%bv = sxw tid).
          { destruct (Z.ltb_spec k bc).
            -- rewrite (Z.mod_small k bc) in Hc by lia.
               xrun HR HK 100%nat STOPS3 (SCR [false; true; true; false] [EVar 40; EVar 41] []) 50%N; [split_scs; try sc_auto1|].
               exists R'. split; [exact Hms|]. split; [kept3_of HR' H10 H8|].
               rreg HR' 14%bv G14. rreg HR' 12%bv G12. rreg HR' 13%bv G13. rreg HR' 15%bv G15. rreg HR' 10%bv G10. rreg HR' 8%bv G8.
               repeat split; assumption.
            -- xrun HR HK 100%nat STOPS3 (SCR [false; false; true; false] [EVar 40; EVar 41] []) 50%N.
               { split_scs; try sc_auto1. cbn [sc_denot]. evs. rewrite w_remu, br_eq by lia. bool_lia. }
               exists R'. split; [exact Hms|]. split; [kept3_of HR' H10 H8|].
               rreg HR' 14%bv G14. rreg HR' 12%bv G12. rreg HR' 13%bv G13. rreg HR' 15%bv G15. rreg HR' 10%bv G10. rreg HR' 8%bv G8.
               repeat split; assumption. }
          destruct STEP as (R1 & Hms1 & Hk1 & G14 & G12 & G13 & G15 & G10 & G8).
          destruct (IH (l1 ++ [(p, (k, v))]) p' k' v' R1 He' G10 G8 G14 G12 G13 G15 Hbc) as (R' & Hk2 & Hw).
          exists R'. split; [eapply kept3_trans; eassumption|].
          destruct Hw as [(q & vq & Hin & Hms2 & F14) | Hms2].
          -- left. exists q, vq. split; [exact Hin|]. split; [eapply msteps_trans; [exact Hms1 | exact Hms2] | exact F14].
          -- right. eapply msteps_trans; [exact Hms1 | exact Hms2].
        * seed3 R [Z_to_bv 64 this; sxw tid; Z_to_bv 64 bc; Z_to_bv 64 tid; Z_to_bv 64 p; Z_to_bv 64 (tid mod bc); Z_to_bv 64 0; Z_to_bv 64 0;
                   Z_to_bv 64 k].
          destruct (Z.ltb_spec k bc).
          -- rewrite (Z.mod_small k bc) in Hc by lia.
             xrun HR HK 100%nat STOPS3 (SCR [false; true; false] [EVar 40] []) 50%N; [split_scs; try sc_auto1|].
             fin_miss HR' Hms H10 H8.
          -- xrun HR HK 100%nat STOPS3 (SCR [false; false; false] [EVar 40] []) 50%N.
             { split_scs; try sc_auto1. cbn [sc_denot]. evs. rewrite w_remu, br_eq by lia. bool_lia. }
             fin_miss HR' Hms H10 H8.
  Qed.

  Lemma loopP3 : forall l2 l1 p k v R,
    ents = l1 ++ (p, (k, v)) :: l2 -> bc = 2 ->
    getr R 10%bv = Z_to_bv 64 this -> getr R 8%bv = sxw tid ->
    getr R 14%bv = Z_to_bv 64 p -> getr R 12%bv = Z_to_bv 64 (bc - 1) -> getr R 13%bv = Z_to_bv 64 tid ->
    getr R 15%bv = Z_to_bv 64 (tid mod bc) ->
    exists R', walk3 R LP3_PC R'.
  Proof using fx AC L MI rom A M this bl bc tid ents U Htid.
    induction l2 as [|[p' [k' v']] l2' IH]; intros l1 p k v R He Hbc2 H10 H8 H14 H12 H13 H15;
      destruct (node_facts3 l1 p k v _ He) as (Hp0 & Hp1 & Hh & Hk & Hkr & Hnx); cbn [hdaddr] in Hnx;
      pose proof (Z.mod_pos_bound tid bc ltac:(lia)) as Hmk;
      pose proof (Z.mod_pos_bound k bc ltac:(lia)) as Hmk';
      pose proof (Z.mod_pos_bound tid 2 ltac:(lia)) as Hmk2;
      pose proof (Z.mod_pos_bound k 2 ltac:(lia)) as Hmk2';
      pose proof (land_1 k) as Hl1;
      unfold cell8 in Hh, Hnx; unfold cell4 in Hk; unfold walk3.
    - destruct (Z.eq_dec k tid) as [->|Hne].
      + seed3 R [Z_to_bv 64 this; sxw tid; Z_to_bv 64 (bc - 1); Z_to_bv 64 tid; Z_to_bv 64 p; Z_to_bv 64 (tid mod bc); Z_to_bv 64 0; Z_to_bv 64 0;
                 Z_to_bv 64 tid; sxw tid].
        xrun HR HK 100%nat STOPS3 (SCR [true; true] [EVar 40; EVar 41] []) 50%N.
        { split_scs; try sc_auto1. sc_rd_sx Hk. }
        fin_hit HR' Hms p v He H10 H8.
      + destruct (Z.eq_dec (k mod bc) (tid mod bc)) as [Hc|Hc].
        * seed3 R [Z_to_bv 64 this; sxw tid; Z_to_bv 64 (bc - 1); Z_to_bv 64 tid; Z_to_bv 64 p; Z_to_bv 64 (tid mod bc); Z_to_bv 64 0; Z_to_bv 64 0;
                   Z_to_bv 64 k; Z_to_bv 64 0].
          xrun HR HK 100%nat STOPS3 (SCR [false; true; true] [EVar 40; EVar 41] []) 50%N.
          { split_scs; try sc_auto1. cbn [sc_denot]. evs. rewrite Hbc2. change (2 - 1) with 1. rewrite w_and, land_1, br_eq by lia. rewrite Hbc2 in Hc. bool_lia. }
          fin_miss HR' Hms H10 H8.
        * seed3 R [Z_to_bv 64 this; sxw tid; Z_to_bv 64 (bc - 1); Z_to_bv 64 tid; Z_to_bv 64 p; Z_to_bv 64 (tid mod bc); Z_to_bv 64 0; Z_to_bv 64 0;
                   Z_to_bv 64 k].
          xrun HR HK 100%nat STOPS3 (SCR [false; false] [EVar 40] []) 50%N.
          { split_scs; try sc_auto1. cbn [sc_denot]. evs. rewrite Hbc2. change (2 - 1) with 1. rewrite w_and, land_1, br_eq by lia. rewrite Hbc2 in Hc. bool_lia. }
          fin_miss HR' Hms H10 H8.
    - assert (He' : ents = (l1 ++ [(p, (k, v))]) ++ (p', (k', v')) :: l2') by (rewrite He, <- app_assoc; reflexivity).
      destruct (node_facts3 _ p' k' v' _ He') as (Hp0' & Hp1' & _).
      destruct (Z.eq_dec k tid) as [->|Hne].
      + seed3 R [Z_to_bv 64 this; sxw tid; Z_to_bv 64 (bc - 1); Z_to_bv 64 tid; Z_to_bv 64 p; Z_to_bv 64 (tid mod bc); Z_to_bv 64 0; Z_to_bv 64 0;
                 Z_to_bv 64 tid; sxw tid].
        xrun HR HK 100%nat STOPS3 (SCR [true; true] [EVar 40; EVar 41] []) 50%N.
        { split_scs; try sc_auto1. sc_rd_sx Hk. }
        fin_hit HR' Hms p v He H10 H8.
      + destruct (Z.eq_dec (k mod bc) (tid mod bc)) as [Hc|Hc].
        * seed3 R [Z_to_bv 64 this; sxw tid; Z_to_bv 64 (bc - 1); Z_to_bv 64 tid; Z_to_bv 64 p; Z_to_bv 64 (tid mod bc); Z_to_bv 64 0; Z_to_bv 64 0;
                   Z_to_bv 64 k; Z_to_bv 64 p'].
          xrun HR HK 100%nat STOPS3 (SCR [false; true; false] [EVar 40; EVar 41] []) 50%N.
          { split_scs; try sc_auto1. cbn [sc_denot]. evs. rewrite Hbc2. change (2 - 1) with 1. rewrite w_and, land_1, br_eq by lia. rewrite Hbc2 in Hc. bool_lia. }
          rreg HR' 14%bv G14. rreg HR' 12%bv G12. rreg HR' 13%bv G13. rreg HR' 15%bv G15. rreg HR' 10%bv G10. rreg HR' 8%bv G8.
          assert (Hk1 : kept3 R R') by (kept3_of HR' H10 H8).
          destruct (IH (l1 ++ [(p, (k, v))]) p' k' v' R' He' Hbc2 G10 G8 G14 G12 G13 G15) as (R'' & Hk2 & Hw).
          exists R''. split; [eapply kept3_trans; eassumption|].
          destruct Hw as [(q & vq & Hin & Hms2 & F14) | Hms2].
          -- left. exists q, vq. split; [exact Hin|]. split; [eapply msteps_trans; [exact Hms | exact Hms2] | exact F14].
          -- right. eapply msteps_trans; [exact Hms | exact Hms2].
        * seed3 R [Z_to_bv 64 this; sxw tid; Z_to_bv 64 (bc - 1); Z_to_bv 64 tid; Z_to_bv 64 p; Z_to_bv 64 (tid mod bc); Z_to_bv 64 0; Z_to_bv 64 0;
                   Z_to_bv 64 k].
          xrun HR HK 100%nat STOPS3 (SCR [false; false] [EVar 40] []) 50%N.
          { split_scs; try sc_auto1. cbn [sc_denot]. evs. rewrite Hbc2. change (2 - 1) with 1. rewrite w_and, land_1, br_eq by lia. rewrite Hbc2 in Hc. bool_lia. }
          fin_miss HR' Hms H10 H8.
  Qed.

  Theorem ntfind_correct : forall R,
    getr R 10%bv = Z_to_bv 64 this -> getr R 8%bv = Z_to_bv 64 (HStmts.sx32 tid) ->
    exists R' (pc' : Z),
      msteps SEGS (st R NTF_ENTRY) (st R' pc')
      /\ (forall r, ~ In r [12; 13; 14; 15; 16; 17]%bv -> getr R' r = getr R r)
      /\ ( pc' = NTF_MISS \/ (pc' = NTF_HIT /\ exists p v, In (p, (tid, v)) ents /\ getr R' 14%bv = Z_to_bv 64 p)).
  Proof using fx AC L MI rom A M this bl bc tid ents U Htid Hthis0 Hthis1.
    intros R H10 H8. rewrite sx32_sxw in H8 by exact Htid.
    pose proof bc_rng3 as Hbcr.
    destruct (blkA3 R H10 H8) as (R1 & K1 & [[Hbc0 Hms1] | (Hbc & Hms1 & G12 & G13 & G14 & G15 & G16)]).
    { exists R1, NTF_MISS. split; [exact Hms1|]. split; [exact (kept3_all _ _ K1) | left; reflexivity]. }
    pose proof (Z.mod_pos_bound tid bc ltac:(lia)) as Hidx.
    destruct (u_bkt U (hmod tid bc) ltac:(unfold hmod; lia)) as (b & Hb & Hbok).
    assert (Hq : exists q0 pre l,
              0 <= b /\ b + 8 <= 2 ^ 47 /\ (b <> 0 -> cell8 SEGS M b q0)
              /\ (b <> 0 -> q0 = hdaddr l /\ ents = pre ++ l)).
    { destruct Hbok as [Hb0 | [Hbn | (Hbs & Hne & _)]].
      - exists 0, [], ents. subst b. split; [lia|]. split; [lia|]. split; intros HH; exfalso; exact (HH eq_refl).
      - destruct (in_split_ents _ b ents Hbn) as (l1 & k & v & l2 & He).
        destruct (node_facts3 l1 b k v l2 He) as (Hp0 & Hp1 & _ & _ & _ & Hnx).
        exists (hdaddr l2), (l1 ++ [(b, (k, v))]), l2. split; [lia|]. split; [lia|]. split; [intros _; exact Hnx|].
        intros _. split; [reflexivity|]. rewrite He, <- app_assoc. reflexivity.
      - exists (hdaddr ents), [], ents. subst b. pose proof (u_obj_hi U). split; [lia|]. split; [lia|].
        split; [intros _; exact (h_p1 (u_hdr U))|]. intros _. split; reflexivity. }
    destruct Hq as (q0 & pre & l & Hb0 & Hb1 & Hbq & Hql).
    assert (K110 : getr R1 10%bv = Z_to_bv 64 this) by (rewrite (proj1 (proj2 K1)); exact H10).
    assert (K18 : getr R1 8%bv = sxw tid) by (rewrite (proj2 (proj2 K1)); exact H8).
    destruct (blkB3 R1 (hmod tid bc) b q0 (popcw3 (Z_to_bv 64 bc)) K110 K18 G12 G13 G14 G15 G16 ltac:(unfold hmod; lia) Hbc Hb Hb0 Hb1 Hbq)
      as (R2 & K2 & [ (Hz & Hms2) | [ (Hbn & Hqn & Hw & Hms2 & F14 & F12 & F13 & F15)
                                      | (Hbn & Hqn & Hw & Hms2 & F14 & F12 & F13 & F15) ] ]).
    - exists R2, NTF_MISS. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
      split; [apply kept3_all; eapply kept3_trans; [exact K1 | exact K2] | left; reflexivity].
    - destruct (Hql Hbn) as [Hq0 He]. destruct (hdaddr_cases3 l) as [[Hl0 _] | (p & k & v & l2 & Hl & Hlp)]; [exfalso; lia|].
      subst l. cbn [hdaddr] in Hq0. subst q0.
      assert (K210 : getr R2 10%bv = Z_to_bv 64 this) by (rewrite (proj1 (proj2 K2)); exact K110).
      assert (K28 : getr R2 8%bv = sxw tid) by (rewrite (proj2 (proj2 K2)); exact K18).
      destruct (loopM3 l2 pre p k v R2 He K210 K28 F14 F12 F13 ltac:(exact F15) Hbc) as (R3 & K3 & Hw3).
      assert (KK : kept3 R R3) by (eapply kept3_trans; [eapply kept3_trans; [exact K1 | exact K2] | exact K3]).
      destruct Hw3 as [(q & vq & Hin & Hms3 & T14) | Hms3].
      + exists R3, NTF_HIT. split; [eapply msteps_trans; [exact Hms1|]; eapply msteps_trans; [exact Hms2 | exact Hms3]|].
        split; [exact (kept3_all _ _ KK)|]. right. split; [reflexivity|]. exists q, vq. split; assumption.
      + exists R3, NTF_MISS. split; [eapply msteps_trans; [exact Hms1|]; eapply msteps_trans; [exact Hms2 | exact Hms3]|].
        split; [exact (kept3_all _ _ KK) | left; reflexivity].
    - assert (Hbc2 : bc = 2).
      { destruct (popcw3_cases bc Hbc_in Hbc) as [[E _]|[_ Hge]]; [exact E | exfalso; lia]. }
      destruct (Hql Hbn) as [Hq0 He]. destruct (hdaddr_cases3 l) as [[Hl0 _] | (p & k & v & l2 & Hl & Hlp)]; [exfalso; lia|].
      subst l. cbn [hdaddr] in Hq0. subst q0.
      assert (K210 : getr R2 10%bv = Z_to_bv 64 this) by (rewrite (proj1 (proj2 K2)); exact K110).
      assert (K28 : getr R2 8%bv = sxw tid) by (rewrite (proj2 (proj2 K2)); exact K18).
      destruct (loopP3 l2 pre p k v R2 He Hbc2 K210 K28 F14 F12 F13 ltac:(exact F15)) as (R3 & K3 & Hw3).
      assert (KK : kept3 R R3) by (eapply kept3_trans; [eapply kept3_trans; [exact K1 | exact K2] | exact K3]).
      destruct Hw3 as [(q & vq & Hin & Hms3 & T14) | Hms3].
      + exists R3, NTF_HIT. split; [eapply msteps_trans; [exact Hms1|]; eapply msteps_trans; [exact Hms2 | exact Hms3]|].
        split; [exact (kept3_all _ _ KK)|]. right. split; [reflexivity|]. exists q, vq. split; assumption.
      + exists R3, NTF_MISS. split; [eapply msteps_trans; [exact Hms1|]; eapply msteps_trans; [exact Hms2 | exact Hms3]|].
        split; [exact (kept3_all _ _ KK) | left; reflexivity].
  Qed.
End NTFind.

Theorem nt_find_block_spec {AC : AllocCeiling} : forall (L : Layout) (MI : MallocIface SEGS L),
  nt_find_block_stmt SEGS L MI NTF_ENTRY NTF_MISS NTF_HIT.
Proof.
  intros L MI fx A R M this bl bc tid ents U H10 H8 Htid Hthis0 Hthis1.
  exact (ntfind_correct L MI (seg_rom SEGS) A M this bl bc tid ents U Htid Hthis0 Hthis1 R H10 H8).
Qed.
End HFindNT.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HEmplace OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HEmplace2 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRehash OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRehash2 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HNextPrime OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HMva OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HMva2 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HNtCtx OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HNt OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HStateMvaA OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HStateMvaNT OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HStateMva OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HStateDtor.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablData OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablGrammar OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablFacts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablImgP1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.Tabl_SmallP1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.Tabl_JumpP1.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsGrammar.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Module Tabl_AccessorsP1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StepTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.WalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ShapeAlg OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SRealizes OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibEff OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3Sound OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymRun3.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.CRep.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HLib.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsGrammar.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablData OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablGrammar OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablStmts.

Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.Tabl_SmallP1.S1_code_6b09c_6b294.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module Img := TablImgP1.
Abbreviation SEGS := Plain.M.loaded_segments.
Abbreviation L := Img.Ly.L.
Abbreviation ti := Img.ti.
Abbreviation tc := Img.tc.

Definition IOPS_RET : Z := 0x6b29c.
Definition OOPS_RET : Z := 0x6b280.
Definition EOPS_RET : Z := 0x6b2d0.
Definition NAME_RET : Z := 0x6b2b4.

Lemma cell4_of_fld : forall M a v, CRep.fld SEGS M a 4 v -> 0 <= v < 2 ^ 32 -> cell4 SEGS M a v.
Proof. intros M a v H Hv. split; [cbn; lia | exact H]. Qed.

Section Acc.

  Theorem idesc_operands_spec : idesc_operands_stmt SEGS L TG tc (idesc ti).
  Proof.
    intros fx R M ret HRO (d & op & Hd & Ha0) Hra Hret.
    destruct (idesc_facts SEGS L ti Img.rodata Img.IFX d op Hd)
      as (r & Hfind & Hop & Htg & Hd0 & Hd1 & Hfld & Hf0 & Hc0 & Hfc & Hnc & Hnf & Hncb & SP & AL & LEN & CS & CN).
    destruct (Hfld M HRO) as (F0 & F8 & F12 & F16 & F20).
    assert (Zlen SPANS = 1151) as HLS by reflexivity.
    pose proof (cell4_of_fld M _ _ F8 ltac:(lia)) as C8. pose proof (cell4_of_fld M _ _ F12 ltac:(lia)) as C12.
    unfold INSN_STRIDE in *.
    pose (E := Eseed R [Z_to_bv 64 d; Z_to_bv 64 (i_first r); Z_to_bv 64 (i_count r)]).
    assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
    assert (HK : know_ok SEGS E M []) by constructor.
    xrun HR HK 50%nat [IOPS_RET] (SCR [] [EVar 33; EVar 34] []) 40%N.
    { split_scs; try sc_auto1. }
    assert (Hra1 : getr R' 1%bv = ret).
    { rewrite <- Hra. apply (kept_of_syms R _ _ R' HR' eq_refl). cbn. tauto. }
    exists R'. split; [|split].
    - eapply msteps_trans; [exact Hms|].
      norm_pc. stepjr F_6b25c D_6b25c ret ltac:(exact Hra1).
      change (bv_signed (0%bv : bv 12)) with 0%Z. unfold ret_ok in Hret. rewrite Hret. apply mst_refl.
    - exact (kept_of_syms R _ _ R' HR' eq_refl).
    - intros d' op' Hd' Ha0'.
      destruct (idesc_facts SEGS L ti Img.rodata Img.IFX d' op' Hd') as (r' & Hfind' & Hop' & Htg' & Hd0' & Hd1' & _).
      assert (Ed : d' = d).
      { rewrite Ha0 in Ha0'. apply (f_equal bv_unsigned) in Ha0'. unfold INSN_STRIDE in Hd1'.
        rewrite (u64_of_Z d) in Ha0' by lia. rewrite (u64_of_Z d') in Ha0' by lia. lia. }
      subst d'. destruct (find_insn_fun _ _ _ _ _ Hfind Hfind') as [<- <-].
      exists (ti_spans ti + 4 * i_first r), (i_span r).
      split; [exact Htg|]. split; [exact SP|]. split; [exact AL|].
      rreg HR' 10%bv H10. rreg HR' 11%bv H11. rewrite H10, H11. split.
      + rewrite w_mul, w_add by lia. f_equal. cbn [ti_spans Img.ti]. lia.
      + rewrite LEN. reflexivity.
  Qed.

  Theorem odesc_operands_spec : odesc_operands_stmt SEGS L TG tc (odesc ti).
  Proof.
    intros fx R M ret HRO (d & t & v & Hd & Ha0) Hra Hret.
    destruct (odesc_facts SEGS L ti Img.rodata Img.IFX d t v Hd)
      as (r & Hfind & Htg & Hv & Hd0 & Hd1 & Hfld & Hvb & Hf0 & Hc0 & Hfc & SP & AL & LEN).
    destruct (Hfld M HRO) as (F0 & F4 & F8).
    assert (Zlen SPANS = 1151) as HLS by reflexivity.
    pose proof (cell4_of_fld M _ _ F4 ltac:(lia)) as C4. pose proof (cell4_of_fld M _ _ F8 ltac:(lia)) as C8.
    unfold OPND_STRIDE in *.
    pose (E := Eseed R [Z_to_bv 64 d; Z_to_bv 64 (v_first r); Z_to_bv 64 (v_count r)]).
    assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
    assert (HK : know_ok SEGS E M []) by constructor.
    xrun HR HK 50%nat [OOPS_RET] (SCR [] [EVar 33; EVar 34] []) 40%N.
    { split_scs; try sc_auto1. }
    assert (Hra1 : getr R' 1%bv = ret).
    { rewrite <- Hra. apply (kept_of_syms R _ _ R' HR' eq_refl). cbn. tauto. }
    exists R'. split; [|split].
    - eapply msteps_trans; [exact Hms|].
      norm_pc. stepjr F_6b240 D_6b240 ret ltac:(exact Hra1).
      change (bv_signed (0%bv : bv 12)) with 0%Z. unfold ret_ok in Hret. rewrite Hret. apply mst_refl.
    - exact (kept_of_syms R _ _ R' HR' eq_refl).
    - intros d' t' v' Hd' Ha0'.
      destruct (odesc_facts SEGS L ti Img.rodata Img.IFX d' t' v' Hd') as (r' & Hfind' & Htg' & Hv' & Hd0' & Hd1' & _).
      assert (Ed : d' = d).
      { rewrite Ha0 in Ha0'. apply (f_equal bv_unsigned) in Ha0'. unfold OPND_STRIDE in Hd1'.
        rewrite (u64_of_Z d) in Ha0' by lia. rewrite (u64_of_Z d') in Ha0' by lia. lia. }
      subst d'. unfold find_opnd in Hfind, Hfind'.
      destruct (find_byvalue_ix_fun _ _ _ _ _ _ _ _ _ Hfind Hfind') as [<- <-].
      exists (ti_spans ti + 4 * v_first r), (v_span r).
      split; [exact Htg'|]. split; [exact SP|]. split; [exact AL|].
      rreg HR' 10%bv H10. rreg HR' 11%bv H11. rewrite H10, H11. split.
      + rewrite w_mul, w_add by lia. f_equal. cbn [ti_spans Img.ti]. lia.
      + rewrite LEN. reflexivity.
  Qed.

  Theorem edesc_operands_spec : edesc_operands_stmt SEGS L TG tc (edesc ti).
  Proof.
    intros fx R M ret HRO (d & t & v & Hd & Ha0) Hra Hret.
    destruct (edesc_facts SEGS L ti Img.rodata Img.IFX d t v Hd)
      as (r & Hfind & Htg & Hv & Hd0 & Hd1 & Hfld & Hvb & Hf0 & Hc0 & Hfc & SP & AL & LEN).
    destruct (Hfld M HRO) as (F0 & F4 & F8).
    assert (Zlen SPANS = 1151) as HLS by reflexivity.
    pose proof (cell4_of_fld M _ _ F4 ltac:(lia)) as C4. pose proof (cell4_of_fld M _ _ F8 ltac:(lia)) as C8.
    unfold EXT_STRIDE in *.
    pose (E := Eseed R [Z_to_bv 64 d; Z_to_bv 64 (v_first r); Z_to_bv 64 (v_count r)]).
    assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
    assert (HK : know_ok SEGS E M []) by constructor.
    xrun HR HK 50%nat [EOPS_RET] (SCR [] [EVar 33; EVar 34] []) 40%N.
    { split_scs; try sc_auto1. }
    assert (Hra1 : getr R' 1%bv = ret).
    { rewrite <- Hra. apply (kept_of_syms R _ _ R' HR' eq_refl). cbn. tauto. }
    exists R'. split; [|split].
    - eapply msteps_trans; [exact Hms|].
      norm_pc. stepjr F_6b290 D_6b290 ret ltac:(exact Hra1).
      change (bv_signed (0%bv : bv 12)) with 0%Z. unfold ret_ok in Hret. rewrite Hret. apply mst_refl.
    - exact (kept_of_syms R _ _ R' HR' eq_refl).
    - intros d' t' v' Hd' Ha0'.
      destruct (edesc_facts SEGS L ti Img.rodata Img.IFX d' t' v' Hd') as (r' & Hfind' & Htg' & Hv' & Hd0' & Hd1' & _).
      assert (Ed : d' = d).
      { rewrite Ha0 in Ha0'. apply (f_equal bv_unsigned) in Ha0'. unfold EXT_STRIDE in Hd1'.
        rewrite (u64_of_Z d) in Ha0' by lia. rewrite (u64_of_Z d') in Ha0' by lia. lia. }
      subst d'. unfold find_ext in Hfind, Hfind'.
      destruct (find_byvalue_ix_fun _ _ _ _ _ _ _ _ _ Hfind Hfind') as [<- <-].
      exists (ti_spans ti + 4 * v_first r), (v_span r).
      split; [exact Htg'|]. split; [exact SP|]. split; [exact AL|].
      rreg HR' 10%bv H10. rreg HR' 11%bv H11. rewrite H10, H11. split.
      + rewrite w_mul, w_add by lia. f_equal. cbn [ti_spans Img.ti]. lia.
      + rewrite LEN. reflexivity.
  Qed.

  Theorem idesc_name_spec : idesc_name_stmt SEGS L tc (idesc ti).
  Proof.
    intros fx R M ret HRO (d & op & Hd & Ha0) Hra Hret.
    destruct (idesc_facts SEGS L ti Img.rodata Img.IFX d op Hd)
      as (r & Hfind & Hop & Htg & Hd0 & Hd1 & Hfld & Hf0 & Hc0 & Hfc & Hnc & Hnf & Hncb & SP & AL & LEN & CS & CN).
    destruct (Hfld M HRO) as (F0 & F8 & F12 & F16 & F20).
    pose proof (cell4_of_fld M _ _ F16 ltac:(lia)) as C16. pose proof (cell4_of_fld M _ _ F20 ltac:(lia)) as C20.
    unfold INSN_STRIDE in *.
    pose (E := Eseed R [Z_to_bv 64 d; Z_to_bv 64 (i_nfirst r); Z_to_bv 64 (i_ncount r)]).
    assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
    assert (HK : know_ok SEGS E M []) by constructor.
    xrun HR HK 50%nat [NAME_RET] (SCR [] [EVar 33; EVar 34] []) 40%N.
    { split_scs; try sc_auto1. }
    assert (Hra1 : getr R' 1%bv = ret).
    { rewrite <- Hra. apply (kept_of_syms R _ _ R' HR' eq_refl). cbn. tauto. }
    exists R'. split; [|split].
    - eapply msteps_trans; [exact Hms|].
      norm_pc. stepjr F_6b274 D_6b274 ret ltac:(exact Hra1).
      change (bv_signed (0%bv : bv 12)) with 0%Z. unfold ret_ok in Hret. rewrite Hret. apply mst_refl.
    - exact (kept_of_syms R _ _ R' HR' eq_refl).
    - exists (ti_strings ti + i_nfirst r), (i_ncount r - 1).
      split; [exact CS|]. split; [exact CN|].
      rreg HR' 10%bv H10. rewrite H10. rewrite w_add by lia. f_equal. cbn [ti_strings Img.ti]. lia.
  Qed.

  Theorem odesc_value_spec : odesc_value_stmt SEGS L (odesc ti).
  Proof.
    intros d t v M Hd HRO.
    destruct (odesc_facts SEGS L ti Img.rodata Img.IFX d t v Hd) as (r & _ & _ & _ & Hd0 & Hd1 & Hfld & _).
    destruct (Hfld M HRO) as (F0 & _). unfold OPND_STRIDE in Hd1. split; [exact F0 | lia].
  Qed.
End Acc.
End Tabl_AccessorsP1.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.Tabl_StrlenP1.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablLib.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Module Tabl_SplitP1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StepTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.WalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ShapeAlg OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SRealizes OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibEff OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3Sound OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymRun3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MmapSim.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.CRep.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HLib.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsGrammar.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablLib.

Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module Img := TablImgP1.
Abbreviation SEGS := Plain.M.loaded_segments.
Abbreviation L := Img.Ly.L.
Abbreviation tc := Img.tc.

Definition OS_RETS : list Z := [0x6b0f0].
Definition BE_RETS : list Z := [0x6ab80; 0x6ab88; 0x6abb8].

Section Split.
Context {AC : AllocCeiling}.

  Theorem opcode_split_spec : opcode_split_stmt SEGS tc.
  Proof using AC.
    intros fx R M w pwc pop ret Ha0 Ha1 Ha2 Hw Hc1 Hh1 Hc2 Hh2 Hal1 Hal2 Hd1 Hd2 Hra Hret.
    pose proof ac_bounds_lit as HAC.
    pose (E := Eseed R [Z_to_bv 64 (TablStmts.sx32 w); Z_to_bv 64 pwc; Z_to_bv 64 pop]).
    pose proof (sx32_range w Hw) as Hsw.
    assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32); (11%bv, EVar 33); (12%bv, EVar 34)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
    assert (HK : know_ok SEGS E M [KRange (EVar 33) 1 (2 ^ 47); KRange (EVar 34) 1 (2 ^ 47)]).
    { constructor; [|constructor; [|constructor]]; (eapply krange_var; [evs; reflexivity | lia | lia]). }
    assert (D1 : defined M pwc 2) by (intros i Hi; apply Hd1; lia).
    assert (D2 : defined M pop 2) by (intros i Hi; apply Hd2; lia).
    xrun HR HK 60%nat OS_RETS (SCR [] [] []) 40%N.
    { split_scs; sc_so; rewrite Z.add_0_r; [exact D2 | exact D1]. }
    match type of Hms with msteps _ _ (mkst _ _ ?M1 _) =>
      match goal with |- exists R'', msteps _ _ (mkst _ _ ?M2 _) /\ _ => assert (EM : M1 = M2) end end.
    { evs. rewrite !v_addi_Z by lia. rewrite !Z.add_0_r.
      rewrite srl16_val by lia.
      rewrite (w2_eq (TablStmts.sx32 w / 2 ^ 16) (w / 2 ^ 16)) by (apply sx32_hi16; lia).
      rewrite (w2_eq (TablStmts.sx32 w) (w mod 2 ^ 16)) by (rewrite sx32_mod16 by lia; rewrite Z.mod_mod by lia; reflexivity).
      reflexivity. }
    rewrite EM in Hms.
    assert (Hra1 : getr R' 1%bv = ret) by (etransitivity; [apply (kept_of_syms _ _ _ R' HR' eq_refl); (first [solve [clear; cbn; tauto] | cbn; tauto]) | exact Hra]).
    exists R'. split; [| exact (kept_of_syms _ _ _ R' HR' eq_refl)].
    eapply msteps_trans; [exact Hms|]. eapply ret_run; [ vm_compute; reflexivity | exact Hra1 | exact Hret ].
  Qed.

  Theorem binary_endianness_spec : binary_endianness_stmt SEGS L tc.
  Proof using AC.
    intros fx R M pb pe words n sp ret HRO Ha0 Ha1 Hsp Fw Fn Hn Hw0 Hwn Hdw Hce Hpe4 Hdpe Hcb Hpb16 Hal8 Hal4w Hal4e Hdisj Hroom Hcs Hsp47 Hra Hret.
    pose proof ac_bounds_lit as HAC.
    destruct (mdef_byte M words 4 0 Hdw ltac:(lia)) as [c0 E0]. rewrite Z.add_0_r in E0.
    destruct (mdef_byte M words 4 1 Hdw ltac:(lia)) as [c1 E1].
    destruct (mdef_byte M words 4 2 Hdw ltac:(lia)) as [c2 E2].
    destruct (mdef_byte M words 4 3 Hdw ltac:(lia)) as [c3 E3].
    pose proof (cell1_of_M SEGS M _ _ E0) as C0. pose proof (cell1_of_M SEGS M _ _ E1) as C1.
    pose proof (cell1_of_M SEGS M _ _ E2) as C2. pose proof (cell1_of_M SEGS M _ _ E3) as C3.
    pose proof (proj1 C0) as B0. pose proof (proj1 C1) as B1. pose proof (proj1 C2) as B2. pose proof (proj1 C3) as B3. cbn in B0, B1, B2, B3.
    assert (Hn64 : n < 2 ^ 45) by lia.
    assert (Cw : cell8 SEGS M pb words) by (split; [cbn; lia | exact Fw]).
    assert (Cn : cell8 SEGS M (pb + 8) n) by (split; [cbn; lia | exact Fn]).
    assert (Dpe : defined M pe 4) by (intros i Hi; apply Hdpe; lia).
    pose (E := Eseed R [Z_to_bv 64 pb; Z_to_bv 64 pe; Z_to_bv 64 words; Z_to_bv 64 n;
                        Z_to_bv 64 (bv_unsigned c0); Z_to_bv 64 (bv_unsigned c1); Z_to_bv 64 (bv_unsigned c2); Z_to_bv 64 (bv_unsigned c3)]).
    assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32); (11%bv, EVar 33)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
    assert (HK : know_ok SEGS E M [KRange (EVar 33) 1 (2 ^ 47); KRange (EVar 34) 1 (2 ^ 47); KRange (EVar 35) 1 (2 ^ 45)]).
    { constructor; [|constructor; [|constructor; [|constructor]]]; (eapply krange_var; [evs; reflexivity | lia | lia]). }
    destruct (mdef4_fld SEGS M pe Hdpe ltac:(lia) ltac:(lia)) as (e0 & He0 & Fe0).
    xtree HR HK 80%nat BE_RETS 40%N (@nil bool) [EVar 34; EVar 35; EVar 36; EVar 37; EVar 38; EVar 39]
      ltac:(try sc_auto1; sc_so; rewrite Z.add_0_r; exact Dpe) ltac:(idtac) ltac:(br_kill_all).
    all: assert (Hra1 : getr R' 1%bv = ret) by (etransitivity; [apply (kept_of_syms _ _ _ R' HR' eq_refl); (first [solve [clear; cbn; tauto] | cbn; tauto]) | exact Hra]).
    all: rreg HR' 10%bv H10.
    all: lazymatch type of Hms with msteps _ _ (mkst ?R1 (Z_to_bv 64 _) ?MF _) =>
           lazymatch type of H10 with _ = Z_to_bv 64 ?rv =>
             let r := eval vm_compute in (if rv <? 2 ^ 63 then rv else rv - 2 ^ 64)%Z in
             exists R1, MF, r end end.

    all: lazymatch goal with
         | |- exists e, msteps _ _ (mkst _ _ (wbytes _ _ (word_to_le_bytes 4 (edenot _ (ELit ?v)))) _) /\ _ => exists v
         | |- _ => exists e0
         end.
    all: split; [eapply msteps_trans; [exact Hms | eapply ret_run; [ vm_compute; reflexivity | exact Hra1 | exact Hret ]] |].
    all: split; [exact (kept_of_syms _ _ _ R' HR' eq_refl) |].
    all: split; [rewrite H10; apply bv_eq; vm_compute; reflexivity |].
    all: split; [lia|]. all: split; [lia|].
    all: evs; rewrite ?v_addi_Z by lia; rewrite ?Z.add_0_r.
    all: lazymatch goal with
         | |- CRep.fld _ (wbytes _ _ _) _ _ _ /\ _ =>
             split; [apply fld_wbytes4; lia|]; split; [intros; lia|];
             split; [apply frame_wbytes4; [lia|lia|intros x Hx; left; unfold zwin; lia] |];
             intros a Ha; apply defined_wbytes4; [lia|lia|exact Ha]
         | |- _ =>
             split; [exact Fe0|]; split; [intros; lia|]; split; [intros a _; reflexivity | intros a Ha; exact Ha]
         end.
  Qed.
End Split.
End Tabl_SplitP1.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.Tabl_LookupOpP1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.Tabl_LookupOpndP1.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablByValue.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Module Tabl_LookupExtP1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StepTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.WalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ShapeAlg OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SRealizes OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibEff OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3Sound OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymRun3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MmapSim.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.CRep.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HLib.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsGrammar.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablData OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablGrammar OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablByValue.

Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module Img := TablImgP1.
Abbreviation SEGS := Plain.M.loaded_segments.
Abbreviation L := Img.Ly.L.
Abbreviation ti := Img.ti.
Abbreviation tc := Img.tc.

Definition LE_ENTRY : Z := 0x6b8a8.
Definition LE_LOOP  : Z := 0x6b900.
Definition LE_EXIT  : Z := 0x6b92c.
Definition LE_RET   : Z := 0x6b950.
Definition LE_STOPS : list Z := [LE_LOOP; LE_EXIT; LE_RET].
Definition NEXT : Z := 500.
Lemma NEXT_eq : Zlen EXT = NEXT. Proof. reflexivity. Qed.
Lemma ext_base_bounds : 0x10000 <= ti_ext ti /\ ti_ext ti + 28 * NEXT + 28 <= 2 ^ 40.
Proof. unfold NEXT. cbn [ti_ext Img.ti]. lia. Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma half_bounds : forall len, 0 < len -> 0 <= len / 2 < len /\ 0 <= len - len / 2 - 1 < len.
Proof. intros len H. lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation V := (VAL EXT).

Section LE.
  Context {fx : FPState}.
Context {AC : AllocCeiling}.
  Variables (M : mem) (y : Z) (f c : Z).
  Hypothesis HRO : ro_clear L M.
  Hypothesis Hy : 0 <= y < 2 ^ 32.
  Hypothesis Hf : 0 <= f.
  Hypothesis Hc : 0 <= c.
  Hypothesis Hfc : f + c <= NEXT.
  Hypothesis HS : sorted_adj (map v_value (zsub f c EXT)) = true.
  #[local] Abbreviation st R pc := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom SEGS)).
  Let base := ti_ext ti.

  Definition keptX (R R' : bvmap 5 word) : Prop :=
    kept R R' /\ getr R' 10%bv = getr R 10%bv /\ getr R' 11%bv = getr R 11%bv /\ getr R' 12%bv = getr R 12%bv
    /\ getr R' 14%bv = getr R 14%bv /\ getr R' 15%bv = getr R 15%bv.
  Lemma keptX_trans : forall R1 R2 R3, keptX R1 R2 -> keptX R2 R3 -> keptX R1 R3.
  Proof using y Hy. intros R1 R2 R3 (A & B) (D & E). split; [exact (keeps_cs_trans _ _ _ A D) | repeat split; intuition congruence]. Qed.
  Ltac keptX_of HR' :=
    split; [exact (kept_of_syms _ _ _ _ HR' eq_refl)
          | repeat split;
            [ let H := fresh in rreg HR' 10%bv H; first [exact H | rewrite H; symmetry; assumption]
            | let H := fresh in rreg HR' 11%bv H; first [exact H | rewrite H; symmetry; assumption]
            | let H := fresh in rreg HR' 12%bv H; first [exact H | rewrite H; symmetry; assumption]
            | let H := fresh in rreg HR' 14%bv H; first [exact H | rewrite H; symmetry; assumption]
            | let H := fresh in rreg HR' 15%bv H; first [exact H | rewrite H; symmetry; assumption] ] ].

  Definition split_at (i len : Z) : Prop :=
    (forall j, f <= j < i -> V j < y) /\ (forall j, i + len <= j < f + c -> y <= V j).

  Lemma lb_step : forall R i len,
    f <= i -> 0 < len -> i + len <= f + c ->
    getr R 13%bv = Z_to_bv 64 (base + 28 * i) -> getr R 17%bv = Z_to_bv 64 len -> getr R 11%bv = Z_to_bv 64 (TablStmts.sx32 y) ->
    let half := len / 2 in
    let i' := (if y <=? V (i + half) then i else i + half + 1) in
    let len' := (if y <=? V (i + half) then half else len - half - 1) in
    exists R', keptX R R' /\
      msteps SEGS (st R LE_LOOP) (st R' (if len' =? 0 then LE_EXIT else LE_LOOP)) /\
      getr R' 13%bv = Z_to_bv 64 (base + 28 * i') /\ getr R' 17%bv = Z_to_bv 64 len'.
  Proof using fx M y f c HRO Hy Hf Hfc.
    intros R i len Hi Hlen Hil H13 H17 H11 half i' len'.
    pose proof ext_base_bounds as [B0 B1]. pose proof (half_bounds len Hlen) as [Hh1 Hh2].
    pose proof (VAL_row EXT_KIND EXT ext_cert (i + half)) as VR0. rewrite NEXT_eq in VR0. destruct (VR0 ltac:(lia)) as (r & _ & _ & HV). clear VR0.
    pose proof (ext_cell SEGS L ti Img.rodata Img.IFX M (i + half) HRO) as CL. rewrite NEXT_eq in CL. destruct (CL ltac:(lia)) as (CELL & _ & _). clear CL.
    pose (E := Eseed R [Z_to_bv 64 (base + 28 * i); Z_to_bv 64 len; Z_to_bv 64 (TablStmts.sx32 y); Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0;
                        sxw (V (i + half))]).
    assert (HR : regs_ok E (srs sr_id [(13%bv, EVar 32); (17%bv, EVar 33); (11%bv, EVar 34)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
    assert (HK : know_ok SEGS E M []) by constructor.
    assert (ADDR : alu64 ALU_ADD (Z_to_bv 64 (base + 28 * i)) (mul_div M_MUL (Z_to_bv 64 28) (alu64 ALU_SRL (Z_to_bv 64 len) (Z_to_bv 64 1)))
                   = Z_to_bv 64 (base + 28 * (i + half))).
    { rewrite w_srl by lia. change (2 ^ 1) with 2. rewrite zbv_mul, zbv_add. f_equal. subst half. lia. }
    assert (RD : sc_denot SEGS M E (SCReadBase (SA (EAlu ALU_ADD (EVar 32) (EMd M_MUL (ELit 28) (EAlu ALU_SRL (EVar 33) (ELit 1)))) 0) 4 true (EVar 40))).
    { eapply (sc_read_cell4_sx _ _ _ _ _ _ _ CELL); [| evs; reflexivity].
      unfold adenot. cbn [a_base a_off]. evs. rewrite ADDR. rewrite v_addi_Z by (unfold NEXT in *; lia). f_equal. lia. }
    assert (FL : sc_denot SEGS M E (SCFlat (SA (EAlu ALU_ADD (EVar 32) (EMd M_MUL (ELit 28) (EAlu ALU_SRL (EVar 33) (ELit 1)))) 0) (ELit 4))).
    { cbn [sc_denot]. unfold flat, estart, elenZ. cbn [a_base a_off edenot]. evs. rewrite ADDR. rewrite !u64_of_Z by (unfold NEXT in *; lia). unfold NEXT in *. lia. }
    assert (BR : forall b : bool, (if b then y <= V (i + half) else V (i + half) < y) ->
                 sc_denot SEGS M E (SCBr b BC_GEU (EVar 40) (EVar 34))).
    { intros b Hb. cbn [sc_denot]. evs. rewrite sx32_sxw by lia. rewrite br_geu_sxw by lia. destruct b; bool_lia. }
    assert (LEN0 : forall b : bool, (if b then len' = 0 else len' <> 0) ->
      sc_denot SEGS M E (SCBr b BC_EQ
         (if y <=? V (i + half) then EAlu ALU_SRL (EVar 33) (ELit 1)
          else EAlu ALU_ADD (EAlu ALU_ADD (EVar 33) (EMd M_MUL (ELit (-1)) (EAlu ALU_SRL (EVar 33) (ELit 1)))) (ELit (-1))) (ELit 0))).
    { intros b Hb. subst len'. cbn [sc_denot]. destruct (Z.leb_spec y (V (i + half))); cbn [sc_denot]; evs;
        rewrite w_srl by lia; change (2 ^ 1) with 2; fold half; rewrite ?zbv_mul, ?zbv_add.
      - rewrite br_eq by lia. destruct b; bool_lia.
      - replace (len + -1 * half + -1) with (len - half - 1) by lia. rewrite br_eq by lia. destruct b; bool_lia. }
    destruct (Z.leb_spec y (V (i + half))) as [GE|LT].
    - destruct (Z.eqb_spec half 0) as [Hz|Hnz].
      + subst i' len'. rewrite Hz. cbn [Z.eqb].
        xrun HR HK 40%nat LE_STOPS (SCR [true; true] [EVar 40] []) 41%N.
        { split_scs; first [exact RD | exact FL | apply BR; exact GE | apply (LEN0 true); exact Hz | sc_auto1]. }
        exists R'. split; [keptX_of HR'|]. split; [exact Hms|].
        rreg HR' 13%bv H13'. rreg HR' 17%bv H17'. rewrite H13', H17'. rewrite w_srl by lia. change (2 ^ 1) with 2. fold half. rewrite Hz. split; reflexivity.
      + subst i' len'. replace (half =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hnz).
        xrun HR HK 40%nat LE_STOPS (SCR [true; false] [EVar 40] []) 41%N.
        { split_scs; first [exact RD | exact FL | apply BR; exact GE | apply (LEN0 false); exact Hnz | sc_auto1]. }
        exists R'. split; [keptX_of HR'|]. split; [exact Hms|].
        rreg HR' 13%bv H13'. rreg HR' 17%bv H17'. rewrite H13', H17'. rewrite w_srl by lia. change (2 ^ 1) with 2. split; reflexivity.
    - destruct (Z.eqb_spec (len - half - 1) 0) as [Hz|Hnz].
      + subst i' len'. rewrite Hz. cbn [Z.eqb].
        xrun HR HK 40%nat LE_STOPS (SCR [false; true] [EVar 40] []) 41%N.
        { split_scs; first [exact RD | exact FL | apply BR; exact LT | apply (LEN0 true); exact Hz | sc_auto1]. }
        exists R'. split; [keptX_of HR'|]. split; [exact Hms|].
        rreg HR' 13%bv H13'. rreg HR' 17%bv H17'. rewrite H13', H17'. rewrite w_srl by lia. change (2 ^ 1) with 2. fold half.
        rewrite !zbv_mul, !zbv_add. split; f_equal; lia.
      + subst i' len'. replace (len - half - 1 =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hnz).
        xrun HR HK 40%nat LE_STOPS (SCR [false; false] [EVar 40] []) 41%N.
        { split_scs; first [exact RD | exact FL | apply BR; exact LT | apply (LEN0 false); exact Hnz | sc_auto1]. }
        exists R'. split; [keptX_of HR'|]. split; [exact Hms|].
        rreg HR' 13%bv H13'. rreg HR' 17%bv H17'. rewrite H13', H17'. rewrite w_srl by lia. change (2 ^ 1) with 2. fold half.
        rewrite !zbv_mul, !zbv_add. split; f_equal; lia.
  Qed.

  Lemma lb_loop : forall (m : nat) R i len,
    len <= Z.of_nat m -> f <= i -> 0 < len -> i + len <= f + c -> split_at i len ->
    getr R 13%bv = Z_to_bv 64 (base + 28 * i) -> getr R 17%bv = Z_to_bv 64 len -> getr R 11%bv = Z_to_bv 64 (TablStmts.sx32 y) ->
    exists R' i', keptX R R' /\ msteps SEGS (st R LE_LOOP) (st R' LE_EXIT) /\
      getr R' 13%bv = Z_to_bv 64 (base + 28 * i') /\ f <= i' <= f + c /\ split_at i' 0.
  Proof using fx M y f c HRO Hy Hf Hfc HS.
    induction m as [|m IH]; intros R i len Hm Hi Hlen Hil [SL SR] H13 H17 H11; [lia|].
    pose proof (half_bounds len Hlen) as [Hh1 Hh2].
    destruct (lb_step R i len Hi Hlen Hil H13 H17 H11) as (R1 & K1 & MS1 & A13 & A17).
    cbv zeta in MS1, A13, A17.
    set (half := len / 2) in *.
    destruct (Z.leb_spec y (V (i + half))) as [GE|LT].
    - assert (SPL : split_at i half).
      { split; [exact SL|]. intros j Hj. destruct (Z.lt_ge_cases j (i + len)); [|apply SR; lia].
        pose proof (VAL_mono EXT_KIND EXT ext_cert f c (i + half) j Hf ltac:(rewrite NEXT_eq; lia) HS ltac:(lia) ltac:(lia) ltac:(lia)). lia. }
      destruct (Z.eqb_spec half 0) as [Hz|Hnz].
      + exists R1, i. split; [exact K1|]. split; [exact MS1|]. split; [exact A13|]. split; [lia|]. rewrite Hz in SPL. exact SPL.
      + destruct K1 as (K1 & K1a & K1b & K1r).
        destruct (IH R1 i half ltac:(lia) Hi ltac:(lia) ltac:(lia) SPL A13 A17 ltac:(rewrite K1b; exact H11)) as (R' & i' & K' & MS' & P).
        exists R', i'. split; [exact (keptX_trans _ _ _ (conj K1 (conj K1a (conj K1b K1r))) K')|]. split; [eapply msteps_trans; [exact MS1|exact MS']|]. exact P.
    - assert (SPL : split_at (i + half + 1) (len - half - 1)).
      { split; [|intros j Hj; apply SR; lia]. intros j Hj. destruct (Z.lt_ge_cases j i); [apply SL; lia|].
        pose proof (VAL_mono EXT_KIND EXT ext_cert f c j (i + half) Hf ltac:(rewrite NEXT_eq; lia) HS ltac:(lia) ltac:(lia) ltac:(lia)). lia. }
      destruct (Z.eqb_spec (len - half - 1) 0) as [Hz|Hnz].
      + exists R1, (i + half + 1). split; [exact K1|]. split; [exact MS1|]. split; [exact A13|]. split; [lia|]. rewrite Hz in SPL. exact SPL.
      + destruct K1 as (K1 & K1a & K1b & K1r).
        destruct (IH R1 (i + half + 1) (len - half - 1) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) SPL A13 A17 ltac:(rewrite K1b; exact H11)) as (R' & i' & K' & MS' & P).
        exists R', i'. split; [exact (keptX_trans _ _ _ (conj K1 (conj K1a (conj K1b K1r))) K')|]. split; [eapply msteps_trans; [exact MS1|exact MS']|]. exact P.
  Qed.

#[local] Definition HTPmInstS1_0 : list (reg * expr) := [(13%bv, EVar 32); (11%bv, EVar 33); (12%bv, EVar 34); (14%bv, EVar 35); (15%bv, EVar 36); (10%bv, EVar 37)].
  Lemma tail_block : forall R i pd (ret : word),
    f <= i <= f + c -> split_at i 0 ->
    getr R 13%bv = Z_to_bv 64 (base + 28 * i) -> getr R 14%bv = Z_to_bv 64 c -> getr R 15%bv = Z_to_bv 64 (base + 28 * f) ->
    getr R 11%bv = Z_to_bv 64 (TablStmts.sx32 y) -> getr R 12%bv = Z_to_bv 64 pd -> getr R 10%bv = Z_to_bv 64 (-9) ->
    alloc_ceiling <= pd -> pd + 8 <= 2 ^ 47 -> mdef M pd 8 ->
    getr R 1%bv = ret -> ret_ok ret ->
    exists R' M',
      kept R R' /\ msteps SEGS (st R LE_EXIT) (@mkst fx R' ret M' (seg_rom SEGS)) /\
      ( (i < f + c /\ V i = y /\ getr R' 10%bv = Z_to_bv 64 0 /\ M' = wbytes M (Z_to_bv 64 pd) (word_to_le_bytes 8 (Z_to_bv 64 (base + 28 * i))))
      \/ (~ (i < f + c /\ V i = y) /\ getr R' 10%bv = Z_to_bv 64 (-9) /\ M' = M) ).
  Proof using fx AC M y f c HRO Hy Hf Hc Hfc.
    intros R i pd ret Hi [SL SR] H13 H14 H15 H11 H12 H10 Hce Hpd Hdef Hra Hret.
    pose proof ext_base_bounds as [B0 B1]. pose proof ac_bounds_lit as HAC.
    assert (Dpd : defined M pd 8) by (intros k Hk; apply Hdef; lia).
    assert (ENDEQ : alu64 ALU_ADD (mul_div M_MUL (Z_to_bv 64 28) (Z_to_bv 64 c)) (Z_to_bv 64 (base + 28 * f)) = Z_to_bv 64 (base + 28 * (f + c))).
    { rewrite zbv_mul, zbv_add. f_equal. lia. }
    destruct (Z_lt_le_dec i (f + c)) as [Hlt|Hge].
    - pose proof (VAL_row EXT_KIND EXT ext_cert i) as VR0. rewrite NEXT_eq in VR0. destruct (VR0 ltac:(lia)) as (r & _ & _ & HV). clear VR0.
      pose proof (ext_cell SEGS L ti Img.rodata Img.IFX M i HRO) as CL. rewrite NEXT_eq in CL. destruct (CL ltac:(lia)) as (CELL & _ & _). clear CL.
      pose (E := Eseed R [Z_to_bv 64 (base + 28 * i); Z_to_bv 64 (TablStmts.sx32 y); Z_to_bv 64 pd; Z_to_bv 64 c; Z_to_bv 64 (base + 28 * f); Z_to_bv 64 (-9); Z_to_bv 64 0; Z_to_bv 64 0; sxw (V i)]).
      assert (HR : regs_ok E (srs sr_id HTPmInstS1_0) R).
      { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
      assert (HK : know_ok SEGS E M [KRange (EVar 34) 1 (2 ^ 47)]).
      { constructor; [|constructor]. eapply krange_var; [evs; reflexivity | lia | lia]. }
      assert (BE : sc_denot SEGS M E (SCBr false BC_EQ (EVar 32) (EAlu ALU_ADD (EMd M_MUL (ELit 28) (EVar 35)) (EVar 36)))).
      { cbn [sc_denot]. evs. rewrite ENDEQ. rewrite br_eq by lia. bool_lia. }
      destruct (Z.eq_dec (V i) y) as [EQ|NE].
      + xrun HR HK 30%nat LE_STOPS (SCR [false; false] [EVar 40] []) 41%N.
        { split_scs; try sc_auto1; first [exact BE | sc_rd_sx CELL | sc_so; rewrite Z.add_0_r; exact Dpd
                                          | cbn [sc_denot]; evs; rewrite sx32_sxw by lia; rewrite br_ne_sxw by lia; bool_lia ]. }
        assert (Hra1 : getr R' 1%bv = ret) by (etransitivity; [apply (kept_of_syms _ _ _ R' HR' eq_refl); (first [solve [clear; cbn; tauto] | cbn; tauto]) | exact Hra]).
        eexists R', _. split; [exact (kept_of_syms _ _ _ _ HR' eq_refl)|]. split.
        { eapply msteps_trans; [exact Hms|]. eapply ret_run; [vm_compute; reflexivity | exact Hra1 | exact Hret]. }
        left. split; [exact Hlt|]. split; [exact EQ|]. split; [rreg HR' 10%bv H10'; exact H10'|].
        evs. rewrite v_addi_Z by lia. rewrite Z.add_0_r. reflexivity.
      + xrun HR HK 30%nat LE_STOPS (SCR [false; true] [EVar 40] []) 41%N.
        { split_scs; try sc_auto1; first [exact BE | sc_rd_sx CELL
                                          | cbn [sc_denot]; evs; rewrite sx32_sxw by lia; rewrite br_ne_sxw by lia; bool_lia ]. }
        assert (Hra1 : getr R' 1%bv = ret) by (etransitivity; [apply (kept_of_syms _ _ _ R' HR' eq_refl); (first [solve [clear; cbn; tauto] | cbn; tauto]) | exact Hra]).
        eexists R', M. split; [exact (kept_of_syms _ _ _ _ HR' eq_refl)|]. split.
        { eapply msteps_trans; [exact Hms|]. eapply ret_run; [vm_compute; reflexivity | exact Hra1 | exact Hret]. }
        right. split; [lia|]. split; [rreg HR' 10%bv H10'; rewrite H10'; apply bv_eq; vm_compute; reflexivity | reflexivity].
    - assert (Hi' : i = f + c) by lia.
      pose (E := Eseed R [Z_to_bv 64 (base + 28 * i); Z_to_bv 64 (TablStmts.sx32 y); Z_to_bv 64 pd; Z_to_bv 64 c; Z_to_bv 64 (base + 28 * f); Z_to_bv 64 (-9)]).
      assert (HR : regs_ok E (srs sr_id HTPmInstS1_0) R).
      { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
      assert (HK : know_ok SEGS E M []) by constructor.
      xrun HR HK 30%nat LE_STOPS (SCR [true] [EVar 40] []) 41%N.
      { split_scs; try sc_auto1. all: cbn [sc_denot]; evs; rewrite ENDEQ; rewrite Hi'; rewrite br_eq by lia; bool_lia. }
      assert (Hra1 : getr R' 1%bv = ret) by (etransitivity; [apply (kept_of_syms _ _ _ R' HR' eq_refl); (first [solve [clear; cbn; tauto] | cbn; tauto]) | exact Hra]).
      eexists R', M. split; [exact (kept_of_syms _ _ _ _ HR' eq_refl)|]. split.
      { eapply msteps_trans; [exact Hms|]. eapply ret_run; [vm_compute; reflexivity | exact Hra1 | exact Hret]. }
      right. split; [lia|]. split; [rreg HR' 10%bv H10'; rewrite H10'; apply bv_eq; vm_compute; reflexivity | reflexivity].
  Qed.
End LE.

Section Post.
  Context {fx : FPState}.
Context {AC : AllocCeiling}.
  Variables (R : bvmap 5 word) (M : mem) (x y pd sp : Z) (ret : word).

  #[local] Notation le_post R' M' r d :=
    (msteps SEGS (@mkst fx R (Z_to_bv 64 (tc_lookup_ext tc)) M (seg_rom SEGS)) (@mkst fx R' ret M' (seg_rom SEGS))
    /\ kept R R' /\ getr R' 10%bv = Z_to_bv 64 r /\ - 2 ^ 31 <= r < 2 ^ 31
    /\ CRep.fld SEGS M' pd 8 d
    /\ (r = 0 <-> (exists l, g_ext TG x y = Some l)) /\ (r = 0 -> edesc ti d x y)
    /\ frame_eq (fun a => zwin pd (pd + 8) a \/ zwin (sp - tc_lookup_stack tc) sp a) M M'
    /\ (forall a : word, M a <> None -> M' a <> None)) (only parsing).

  Lemma post_missed : forall R', find_ext x y = None -> mdef M pd 8 -> alloc_ceiling <= pd -> pd + 8 <= 2 ^ 47 ->
    msteps SEGS (@mkst fx R (Z_to_bv 64 (tc_lookup_ext tc)) M (seg_rom SEGS)) (@mkst fx R' ret M (seg_rom SEGS)) ->
    kept R R' -> getr R' 10%bv = Z_to_bv 64 (-9) ->
    exists R'' M' r d, le_post R'' M' r d.
  Proof using fx AC R M x y pd sp ret.
    intros R' Hnone Hdef Hce Hpd MS K A10. pose proof ac_bounds_lit.
    destruct (mdef8_fld SEGS M pd Hdef ltac:(lia) ltac:(lia)) as (d0 & _ & Fd0).
    exists R', M, (-9), d0. split; [exact MS|]. split; [exact K|]. split; [exact A10|]. split; [lia|]. split; [exact Fd0|].
    split. { split; [intros C; lia|]. intros [l Hl]. cbn [g_ext TG] in Hl. unfold tg_ext in Hl. rewrite Hnone in Hl. discriminate. }
    split. { intros C; lia. }
    split; [intros a _; reflexivity | intros a Ha; exact Ha].
  Qed.

  Lemma post_found : forall R' i r, find_ext x y = Some (i, r) -> alloc_ceiling <= pd -> pd + 8 <= 2 ^ 47 ->
    msteps SEGS (@mkst fx R (Z_to_bv 64 (tc_lookup_ext tc)) M (seg_rom SEGS))
                (@mkst fx R' ret (wbytes M (Z_to_bv 64 pd) (word_to_le_bytes 8 (Z_to_bv 64 (ti_ext ti + 28 * i)))) (seg_rom SEGS)) ->
    kept R R' -> getr R' 10%bv = Z_to_bv 64 0 ->
    exists R'' M' rr d, le_post R'' M' rr d.
  Proof using fx AC R M x y pd sp ret.
    intros R' i r Hf Hce Hpd MS K A10. pose proof ac_bounds_lit.
    exists R', (wbytes M (Z_to_bv 64 pd) (word_to_le_bytes 8 (Z_to_bv 64 (ti_ext ti + 28 * i)))), 0, (ti_ext ti + 28 * i).
    split; [exact MS|]. split; [exact K|]. split; [exact A10|]. split; [lia|]. split; [apply fld_wbytes8; lia|].
    split. { split; [|intros; reflexivity]. intros _. exists (v_span r). cbn [g_ext TG]. unfold tg_ext. rewrite Hf. reflexivity. }
    split. { intros _. exists i, r. split; [exact Hf | reflexivity]. }
    split. { apply frame_wbytes8; [lia|lia|]. intros a Ha. left. unfold zwin. lia. }
    intros a Ha. apply defined_wbytes8; [lia|lia|exact Ha].
  Qed.
End Post.

Lemma HKimg_ext : forall E M, ro_clear L M -> know_ok SEGS E M [KImg (ti_ro_lo ti) (ti_ro_hi ti)].
Proof. intros E M HRO. constructor; [|constructor]. apply (kimg_ro SEGS L E M _ _ HRO Img.rodata); cbn; lia. Qed.

Lemma kind_run {AC : AllocCeiling} : forall (fx : FPState) R M x y pd sp (ret : word) R1 f c,
  ro_clear L M -> 0 <= y < 2 ^ 32 -> kind_range EXT_KIND x = (f, c) -> 0 <= f -> 0 < c -> f + c <= NEXT ->
  sorted_adj (map v_value (zsub f c EXT)) = true ->
  alloc_ceiling <= pd -> pd + 8 <= 2 ^ 47 -> mdef M pd 8 -> getr R 1%bv = ret -> ret_ok ret ->
  msteps SEGS (@mkst fx R (Z_to_bv 64 (tc_lookup_ext tc)) M (seg_rom SEGS)) (@mkst fx R1 (Z_to_bv 64 LE_LOOP) M (seg_rom SEGS)) ->
  kept R R1 ->
  getr R1 13%bv = Z_to_bv 64 (ti_ext ti + 28 * f) -> getr R1 17%bv = Z_to_bv 64 c -> getr R1 11%bv = Z_to_bv 64 (TablStmts.sx32 y) ->
  getr R1 14%bv = Z_to_bv 64 c -> getr R1 15%bv = Z_to_bv 64 (ti_ext ti + 28 * f) -> getr R1 12%bv = Z_to_bv 64 pd -> getr R1 10%bv = Z_to_bv 64 (-9) ->
  exists R' M' r d,
    msteps SEGS (@mkst fx R (Z_to_bv 64 (tc_lookup_ext tc)) M (seg_rom SEGS)) (@mkst fx R' ret M' (seg_rom SEGS))
    /\ kept R R' /\ getr R' 10%bv = Z_to_bv 64 r /\ - 2 ^ 31 <= r < 2 ^ 31
    /\ CRep.fld SEGS M' pd 8 d
    /\ (r = 0 <-> (exists l, g_ext TG x y = Some l)) /\ (r = 0 -> edesc ti d x y)
    /\ frame_eq (fun a => zwin pd (pd + 8) a \/ zwin (sp - tc_lookup_stack tc) sp a) M M'
    /\ (forall a : word, M a <> None -> M' a <> None).
Proof.
  intros fx R M x y pd sp ret R1 f c HRO Hy Hk Hf Hc Hfc HS Hce Hpd Hdef Hra Hret MS1 K1 A13 A17 A11 A14 A15 A12 A10.
  assert (SP0 : split_at y f c f c) by (split; intros j Hj; lia).
  destruct (lb_loop M y f c HRO Hy Hf Hfc HS (Z.to_nat c) R1 f c ltac:(lia) ltac:(lia) Hc ltac:(lia) SP0 A13 A17 A11)
    as (R2 & i & (K2 & K2a & K2b & K2c & K2d & K2e) & MS2 & B13 & Hi & SPL).
  destruct (tail_block M y f c HRO Hy Hf ltac:(lia) Hfc R2 i pd ret Hi SPL B13
              ltac:(rewrite K2d; exact A14) ltac:(rewrite K2e; exact A15) ltac:(rewrite K2b; exact A11) ltac:(rewrite K2c; exact A12) ltac:(rewrite K2a; exact A10)
              Hce Hpd Hdef ltac:(rewrite K2, K1; [exact Hra | (first [solve [clear; cbn; tauto] | cbn; tauto]) | (first [solve [clear; cbn; tauto] | cbn; tauto])]) Hret) as (R3 & M' & K3 & MS3 & RES).
  assert (KK : kept R R3) by (exact (keeps_cs_trans _ _ _ (keeps_cs_trans _ _ _ K1 K2) K3)).
  assert (MS : msteps SEGS (@mkst fx R (Z_to_bv 64 (tc_lookup_ext tc)) M (seg_rom SEGS)) (@mkst fx R3 ret M' (seg_rom SEGS))).
  { eapply msteps_trans; [exact MS1|]. eapply msteps_trans; [exact MS2|exact MS3]. }
  destruct SPL as [SL SR]. rewrite Z.add_0_r in SR.
  destruct RES as [(Hlt & HV & B10 & HM')|(Hno & B10 & HM')]; subst M'.
  - destruct (lbv_found EXT_KIND EXT ext_cert x f c y i Hk Hf ltac:(lia) ltac:(rewrite NEXT_eq; lia) HV SL) as (r & Hfd & Hr).
    eapply post_found; [exact Hfd | exact Hce | exact Hpd | exact MS | exact KK | exact B10].
  - pose proof (lbv_missed EXT_KIND EXT ext_cert x f c y i Hk Hf ltac:(lia) ltac:(rewrite NEXT_eq; lia) HS Hi SL SR Hno) as Hnone.
    eapply post_missed; [exact Hnone | exact Hdef | exact Hce | exact Hpd | exact MS | exact KK | exact B10].
Qed.

Theorem lookup_ext_spec {AC : AllocCeiling} : lookup_ext_stmt SEGS L TG tc (edesc ti).
Proof.
  intros fx R M x y pd sp ret HRO Ha0 Hx _ H3 Hsp Hce Hpd8 Hdef Hal Hdisj Hroom Hcs Hsp47 Hsp16 Hra Hret.
  destruct (H3 eq_refl) as (H11 & Hy & H12). clear H3.
  pose proof ac_bounds_lit as HAC. pose proof ext_base_bounds as [B0 B1].

  assert (Hcases : x = 0 \/ 16 <= x \/ (1 <= x < 1 + Z.of_nat 15)) by lia.
  destruct Hcases as [X0 | [X16 | XR]].
  -
    subst x. pose (E := Eseed R (@nil word)).
    assert (HR : regs_ok E (srs sr_id [(10%bv, ELit 0)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; exact Ha0. }
    assert (HK : know_ok SEGS E M []) by constructor.
    xrun HR HK 40%nat LE_STOPS (SCR [] [] []) 41%N. { split_scs; try sc_auto1. }
    assert (Hra1 : getr R' 1%bv = ret) by (etransitivity; [apply (kept_of_syms _ _ _ R' HR' eq_refl); (first [solve [clear; cbn; tauto] | cbn; tauto]) | exact Hra]).
    eapply (post_missed R M 0 y pd sp ret R'); [apply (kind_empty EXT_KIND EXT); reflexivity | exact Hdef | exact Hce | exact Hpd8 | | exact (kept_of_syms _ _ _ _ HR' eq_refl) | rreg HR' 10%bv H10'; rewrite H10'; apply bv_eq; vm_compute; reflexivity].
    eapply msteps_trans; [exact Hms|]. eapply ret_run; [vm_compute; reflexivity | exact Hra1 | exact Hret].
  -
    pose (E := Eseed R [Z_to_bv 64 x]).
    assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; exact Ha0. }
    assert (HK : know_ok SEGS E M []) by constructor.
    xrun HR HK 40%nat LE_STOPS (SCR [true] [] []) 41%N.
    { split_scs; try sc_auto1. cbn [sc_denot]. evs. rewrite aluw_add_val. rewrite br_ltu; [| lia | apply sx32_range; apply Z.mod_pos_bound; lia].
      apply Z.ltb_lt. unfold TablStmts.sx32.
      assert (Hm : (x + -1) mod 2 ^ 32 = x - 1) by (apply Z.mod_small; lia). rewrite Hm.
      destruct (Z.ltb_spec (x - 1) (2 ^ 31)); lia. }
    assert (Hra1 : getr R' 1%bv = ret) by (etransitivity; [apply (kept_of_syms _ _ _ R' HR' eq_refl); (first [solve [clear; cbn; tauto] | cbn; tauto]) | exact Hra]).
    assert (Hk0 : kind_range EXT_KIND x = (0, 0)).
    { unfold kind_range. rewrite (proj2 (find_none _ _) ) || idtac.
      destruct (find (fun k => v_value k =? x) EXT_KIND) as [k|] eqn:EF; [|reflexivity].
      apply find_some in EF as [Hin Eq]. apply Z.eqb_eq in Eq. exfalso.
      assert (HB : forallb (fun k => v_value k <? 16) EXT_KIND = true) by (vm_compute; reflexivity).
      rewrite forallb_forall in HB. specialize (HB k Hin). apply Z.ltb_lt in HB. lia. }
    eapply (post_missed R M x y pd sp ret R'); [apply (kind_empty EXT_KIND EXT); exact Hk0 | exact Hdef | exact Hce | exact Hpd8 | | exact (kept_of_syms _ _ _ _ HR' eq_refl) | rreg HR' 10%bv H10'; rewrite H10'; apply bv_eq; vm_compute; reflexivity].
    eapply msteps_trans; [exact Hms|]. eapply ret_run; [vm_compute; reflexivity | exact Hra1 | exact Hret].
  -
    enum_range x 1 15%nat XR; lit_in Ha0;
    lazymatch type of Ha0 with getr _ _ = Z_to_bv 64 ?xv =>
      let fc := eval vm_compute in (kind_range EXT_KIND xv) in
      lazymatch fc with (?f, ?c) =>
        pose (E := Eseed R [Z_to_bv 64 (TablStmts.sx32 y); Z_to_bv 64 pd]);
        assert (HR : regs_ok E (srs sr_id [(10%bv, ELit xv); (11%bv, EVar 32); (12%bv, EVar 33)]) R)
          by (apply regs_ok_srs; [apply regs_ok_seed|]; repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption);
        pose proof (HKimg_ext E M HRO) as HK;
        xrun HR HK 40%nat LE_STOPS (SCR [] [] []) 41%N; [split_scs; try sc_auto1|];
        rreg HR' 13%bv A13; rreg HR' 17%bv A17; rreg HR' 11%bv A11; rreg HR' 14%bv A14; rreg HR' 15%bv A15; rreg HR' 12%bv A12; rreg HR' 10%bv A10;
        eapply (kind_run fx R M xv y pd sp ret R' f c HRO Hy eq_refl);
        [ lia | lia | unfold NEXT; lia | vm_compute; reflexivity | exact Hce | exact Hpd8 | exact Hdef | exact Hra | exact Hret
        | exact Hms | exact (kept_of_syms _ _ _ _ HR' eq_refl)
        | rewrite A13; f_equal; reflexivity | exact A17 | exact A11 | exact A14 | rewrite A15; f_equal; reflexivity | exact A12
        | rewrite A10; apply bv_eq; vm_compute; reflexivity ]
      end end.
Qed.
End Tabl_LookupExtP1.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.Tabl_SpecP1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.Tabl_ImportP1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.Tabl_PushP1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.Tabl_TakeP1.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.DRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.DiagS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.DiagStmts.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsNeeds OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsInv OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmHyps OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmCoreS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmWrapS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmWrap2S1.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RunRandom.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec SRealizes StepTac LibIface LibBudget LibEff S1Layout SumMemset Lib_Cxx_OperatorNew.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ Require Import MallocIfaceStmt MallocInstS1 MallocHeapOwnS1.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import S1Statics.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContStmts ContStmts3 S1Facts Lib_Vec32_PushBack Lib_Vec32_PushBack_69278 Lib_Vec32_PushBack_697a0 Lib_Vec32_PushBack_6b8f8 Lib_VecOpnd_PushBack Lib_Str_PushBack.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmInstS1.Lib_MakeString. From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import Lib_Cxx_OperatorDelete.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts HConstsS1 HFind.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmInstS1.HFind2. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmInstS1.HFindNT. From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HEmplace HEmplace2 HRehash HRehash2 HNextPrime HMva HMva2 HNtCtx HNt HStateMvaA HStateMvaNT HStateMva HStateDtor.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablStmts TablRep TablData TablGrammar TablFacts TablImgP1 Tabl_SmallP1 Tabl_JumpP1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmInstS1.Tabl_AccessorsP1. From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import Tabl_StrlenP1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmInstS1.Tabl_SplitP1. From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import Tabl_LookupOpP1 Tabl_LookupOpndP1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmInstS1.Tabl_LookupExtP1. From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import Tabl_SpecP1 Tabl_ImportP1 Tabl_PushP1 Tabl_TakeP1.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag Require Import DRep DiagS1 DiagStmts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsGrammar PrsNeeds PrsInv PrsStmts PmHyps PmCoreS1 PmWrapS1 PmWrap2S1.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import RunRandom.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Module Ly := S1Layout.
Abbreviation SEGS := Plain.M.loaded_segments.

Lemma ms_val {AC : AllocCeiling} {RRND : RunRandom} : MALLOC_STACK MI_S1 = 8192.
Proof. rewrite (mc_stack _ _ _ MI_S1_consts_ok). reflexivity. Qed.
Lemma ms_nonneg {AC : AllocCeiling} {RRND : RunRandom} : 0 <= MALLOC_STACK MI_S1.
Proof. rewrite ms_val. lia. Qed.
Lemma ns_nonneg {AC : AllocCeiling} {RRND : RunRandom} : 0 <= ContStmts.NEW_STACK SEGS Ly.L MI_S1.
Proof. unfold ContStmts.NEW_STACK. rewrite ms_val. lia. Qed.
Lemma ms_range {AC : AllocCeiling} {RRND : RunRandom} : 0 <= MALLOC_STACK MI_S1 <= 8192.
Proof. rewrite ms_val. lia. Qed.

Lemma round_up_pg_bounds : forall x, x <= mng_round_up_pg x < x + 4096.
Proof.
  intros x. unfold mng_round_up_pg, MNG_PGSZ. change (4096 - 1) with (Z.ones 12). rewrite Z.land_ones by lia.
  change 4096 with (2 ^ 12). pose proof (Z.mod_pos_bound (- x) (2 ^ 12) ltac:(lia)). lia.
Qed.
Lemma rb_S1 {AC : AllocCeiling} {RRND : RunRandom} : round_big_law MI_S1.
Proof.
  intros n Hn. rewrite (mc_round_big _ _ _ MI_S1_consts_ok n). unfold mng_round_big, MNG_IB, MNG_UNIT.
  pose proof (round_up_pg_bounds (n + 4 + 16)). lia.
Qed.
Lemma classes_S1 {AC : AllocCeiling} {RRND : RunRandom} : size_class MI_S1 24 <= 2 /\ (size_class MI_S1 32 <= 2 /\ size_class MI_S1 24 <> size_class MI_S1 32) /\ 4096 <= BIG MI_S1.
Proof.
  rewrite !(mc_size_class _ _ _ MI_S1_consts_ok), (mc_big _ _ _ MI_S1_consts_ok).
  vm_compute. repeat split; congruence.
Qed.

Lemma new_S1 {AC : AllocCeiling} {RRND : RunRandom} : new_rule_stmt SEGS Ly.L MI_S1 S1ST (ContStmts.NEW_STACK SEGS Ly.L MI_S1).
Proof. exact (operator_new_spec MI_S1 S1ST ms_nonneg). Qed.
Lemma delr_S1 {AC : AllocCeiling} {RRND : RunRandom} : delete_rule_stmt SEGS Ly.L MI_S1 (MALLOC_STACK MI_S1).
Proof. exact (operator_delete_spec MI_S1). Qed.

Lemma memset_S1 : HStmts.memset_stmt SEGS HConstsS1.hc.
Proof.
  intros fx mem0 d cv ret n regs Hn Hnw Hok Hret H10 H11 H12 H1.
  replace (Z_to_bv 64 (hc_memset HConstsS1.hc)) with s1_memset_entry by (apply bv_eq; vm_compute; reflexivity).
  exact (s1_memset mem0 d cv ret n (seg_rom SEGS) regs Hn Hnw Hok Hret H10 H11 H12 H1).
Qed.
Lemma next_prime_S1 : HStmts.next_prime_stmt SEGS Ly.L HConstsS1.hc.
Proof. apply (next_prime_spec Ly.L); reflexivity. Qed.

Lemma rehash_u32_S1 {AC : AllocCeiling} {RRND : RunRandom} : rehash24_stmt SEGS Ly.L MI_S1 S1ST (ContStmts.NEW_STACK SEGS Ly.L MI_S1) (MALLOC_STACK MI_S1) HRehash.REH.
Proof.
  eapply (HRehash.rehash24_spec Ly.L MI_S1 S1ST); try reflexivity.
  - exact ns_nonneg. - exact ms_nonneg. - exact new_S1. - exact delr_S1. - exact memset_S1.
  - exact ly_img_low. - exact ly_rw_img. - exact ly_relro_img. - exact ly_rw_not_relro. - exact ly_errno_rw.
Qed.
Lemma rehash_ext_S1 {AC : AllocCeiling} {RRND : RunRandom} : rehash24_stmt SEGS Ly.L MI_S1 S1ST (ContStmts.NEW_STACK SEGS Ly.L MI_S1) (MALLOC_STACK MI_S1) HRehash2.REH.
Proof.
  eapply (HRehash2.rehash24_spec Ly.L MI_S1 S1ST); try reflexivity.
  - exact ns_nonneg. - exact ms_nonneg. - exact new_S1. - exact delr_S1. - exact memset_S1.
  - exact ly_img_low. - exact ly_rw_img. - exact ly_relro_img. - exact ly_rw_not_relro. - exact ly_errno_rw.
Qed.
Lemma emplace_u32_S1 {AC : AllocCeiling} {RRND : RunRandom} : emplace24_stmt SEGS Ly.L MI_S1 S1ST (ContStmts.NEW_STACK SEGS Ly.L MI_S1) (MALLOC_STACK MI_S1) (hc_emplace_u32 HConstsS1.hc).
Proof.
  eapply (HEmplace.emplace24_spec Ly.L MI_S1 S1ST); try reflexivity.
  - exact ns_nonneg. - exact ms_nonneg. - exact new_S1. - exact next_prime_S1. - exact rehash_u32_S1.
  - exact ly_img_low. - exact ly_rw_img. - exact ly_relro_img. - exact ly_rw_not_relro. - exact ly_errno_rw.
Qed.
Lemma emplace_ext_S1 {AC : AllocCeiling} {RRND : RunRandom} : emplace24_stmt SEGS Ly.L MI_S1 S1ST (ContStmts.NEW_STACK SEGS Ly.L MI_S1) (MALLOC_STACK MI_S1) (hc_emplace_ext HConstsS1.hc).
Proof.
  eapply (HEmplace2.emplace24_spec Ly.L MI_S1 S1ST); try reflexivity.
  - exact ns_nonneg. - exact ms_nonneg. - exact new_S1. - exact next_prime_S1. - exact rehash_ext_S1.
  - exact ly_img_low. - exact ly_rw_img. - exact ly_relro_img. - exact ly_rw_not_relro. - exact ly_errno_rw.
Qed.
Lemma nt_block_S1 {AC : AllocCeiling} {RRND : RunRandom} : emplace_nt_block_stmt SEGS Ly.L MI_S1 S1ST HConstsS1.hc (ContStmts.NEW_STACK SEGS Ly.L MI_S1) (MALLOC_STACK MI_S1).
Proof.
  eapply (HNt.emplace_nt_block_spec Ly.L MI_S1 S1ST); try reflexivity.
  - exact ns_nonneg. - exact ms_nonneg. - exact new_S1. - exact delr_S1. - exact next_prime_S1. - exact memset_S1.
  - exact ly_img_low. - exact ly_rw_img. - exact ly_relro_img. - exact ly_rw_not_relro. - exact ly_errno_rw.
Qed.
Lemma mva_u32_S1 {AC : AllocCeiling} {RRND : RunRandom} : mva_stmt SEGS Ly.L MI_S1 S1ST (MALLOC_STACK MI_S1) HStateMvaA.MVA1E 24 Z (nval24 SEGS).
Proof.
  eapply (HMva.mva_spec Ly.L MI_S1 S1ST); try reflexivity.
  - exact ms_nonneg. - exact delr_S1. - exact memset_S1.
  - exact ly_img_low. - exact ly_rw_img. - exact ly_relro_img. - exact ly_rw_not_relro. - exact ly_errno_rw.
  - exact (HRepFacts.nval24_agree SEGS).
Qed.
Lemma mva_ext_S1 {AC : AllocCeiling} {RRND : RunRandom} : mva_stmt SEGS Ly.L MI_S1 S1ST (MALLOC_STACK MI_S1) HStateMvaA.MVA3E 24 Z (nval24 SEGS).
Proof.
  eapply (HMva2.mva_spec Ly.L MI_S1 S1ST); try reflexivity.
  - exact ms_nonneg. - exact delr_S1. - exact memset_S1.
  - exact ly_img_low. - exact ly_rw_img. - exact ly_relro_img. - exact ly_rw_not_relro. - exact ly_errno_rw.
  - exact (HRepFacts.nval24_agree SEGS).
Qed.
Lemma nt_inl_S1 {AC : AllocCeiling} {RRND : RunRandom} : nt_inl_stmt Ly.L MI_S1 (MALLOC_STACK MI_S1).
Proof.
  eapply (HStateMvaNT.nt_inl_spec Ly.L MI_S1); try reflexivity.
  - exact ms_nonneg. - exact delr_S1. - exact memset_S1.
  - exact ly_img_low. - exact ly_rw_img. - exact ly_errno_rw.
Qed.
Lemma state_mva_S1 {AC : AllocCeiling} {RRND : RunRandom} : state_mva_stmt SEGS Ly.L MI_S1 S1ST HConstsS1.hc (MALLOC_STACK MI_S1).
Proof.
  eapply (HStateMva.state_mva_spec Ly.L MI_S1 S1ST); try reflexivity.
  - exact ms_nonneg. - exact delr_S1. - exact mva_u32_S1. - exact mva_ext_S1. - exact nt_inl_S1.
  - exact ly_img_low. - exact ly_rw_img. - exact ly_relro_img. - exact ly_rw_not_relro. - exact ly_errno_rw.
Qed.

Lemma state_dtor'_S1 {AC : AllocCeiling} {RRND : RunRandom} : @PmWrapS1.state_dtor_stmt' AC MI_S1 S1ST.
Proof.
  pose proof (HStateDtor.state_dtor_spec' Ly.L MI_S1 S1ST (MALLOC_STACK MI_S1) ms_nonneg delr_S1 eq_refl
                ly_img_low ly_rw_img ly_relro_img ly_rw_not_relro ly_errno_rw) as T.
  exact T.
Qed.

Definition spec_len_okb : bool :=
  forallb (fun op => match tg_op op with Some l => (3 <=? Zlen l) | None => true end) SPECOPS.
Lemma spec_len_okb_true : spec_len_okb = true.
Proof. vm_compute. reflexivity. Qed.
Lemma tg_spec_len : forall op l, g_specop TG op = true -> g_op TG op = Some l -> 3 <= Zlen l.
Proof.
  intros op l Hs H. cbn [g_specop TG] in Hs. unfold tg_specop in Hs. apply existsb_exists in Hs. destruct Hs as (op' & Hin & Heq).
  apply Z.eqb_eq in Heq. subst op'.
  pose proof spec_len_okb_true as OK. unfold spec_len_okb in OK. rewrite forallb_forall in OK. specialize (OK op Hin).
  cbn [g_op TG] in H. rewrite H in OK. apply Z.leb_le. exact OK.
Qed.

Section Inst.
Context {AC : AllocCeiling}.
Context {RRND : RunRandom}.
  Hypothesis D : DiagStmts.diag_contract MI_S1 S1ST.
  Hypothesis DX : PrsNeeds.exhausted_stmt SEGS Ly.L MI_S1 S1ST dcS1.

  Definition CL_S1 : pm_callees SEGS Ly.L MI_S1 S1ST TG tcS1 dcS1 nfcS1 HConstsS1.hc ccS1 kcS1
                       (idesc ti) (odesc ti) (edesc ti) tg_generates_type (fun _ => false) (fun _ => false) (DRep.ds_rep MI_S1).
  Proof using AC RRND D DX.
    destruct D as (D0 & D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10).
    constructor.
    -   exact (TG_ok).
    -   exact (tg_maxlen).
    -   exact (tg_mask_len).
    -   exact (tg_spec_len).
    -   exact (eq_refl).
    -   exact (eq_refl).
    -   exact (tg_gt_rid).
    -   exact (tg_rid1).
    -   exact (tg_import).
    -   exact (tg_spec_rid).
    -   exact (rb_S1).
    -   exact (new_S1).
    -   exact (op_delete1_spec MI_S1).
    -   exact (ms_range).
    -   exact (classes_S1).
    -   exact (fixword_spec).
    -   exact (is_host_endian_spec).
    -   exact (generates_type_spec).
    -   exact (is_ext_inst_spec).
    -   exact (is_optional_spec).
    -   exact (is_nonsemantic_spec).
    -   exact (fpenc_spec).
    -   exact (operand_type_str_spec).
    -   exact (idesc_name_spec).
    -   exact (idesc_operands_spec).
    -   exact (odesc_operands_spec).
    -   exact (edesc_operands_spec).
    -   exact (odesc_value_spec).
    -   exact (strlen_ro_spec).
    -   exact (opcode_split_spec).
    -   exact (binary_endianness_spec).
    -   exact (lookup_opcode_spec).
    -   exact (lookup_operand_spec).
    -   exact (lookup_ext_spec).
    -   exact (spec_lookup_spec).
    -   exact (import_type_get_spec MI_S1).
    -   exact (push_types_spec MI_S1 S1ST ms_nonneg (vec32_push_back_6b8f8_spec MI_S1 S1ST ms_nonneg new_S1)).
    -   exact (take_first_spec MI_S1 S1ST ms_nonneg (vec32_push_back_6b8f8_spec MI_S1 S1ST ms_nonneg new_S1) (vec32_push_back_697a0_spec MI_S1 S1ST ms_nonneg new_S1)).
    -   cbn. lia.
    -   exact (D0).
    -   exact (D1).
    -   exact (D2).
    -   exact (D3).
    -   exact (D4).
    -   exact (D5).
    -   exact (D6).
    -   exact (D7).
    -   exact (D8).
    -   exact (D9).
    -   exact (D10).
    -   exact (DX).
    -   cbn. split; [lia | reflexivity].
    -   exact (HFind.find_spec Ly.L MI_S1 24 Z (nval24 SEGS)).
    -   exact (HFind2.find_spec Ly.L MI_S1 24 Z (nval24 SEGS)).
    -   exact (emplace_u32_S1).
    -   exact (emplace_ext_S1).
    -   exact (nt_block_S1).
    -   exact (HFindNT.nt_find_block_spec Ly.L MI_S1).
    -   exact (vec32_push_back_68efc_spec MI_S1 S1ST ms_nonneg new_S1).
    -   exact (vec32_push_back_69278_spec MI_S1 S1ST ms_nonneg new_S1).
    -   exact (vec32_push_back_697a0_spec MI_S1 S1ST ms_nonneg new_S1).
    -   exact (vec_opnd_push_back_69bf4_spec MI_S1 S1ST ms_nonneg new_S1).
    -   exact (makestring_65f88_spec' MI_S1 S1ST ms_nonneg new_S1).
  Defined.

  Definition PO_S1 : @PmWrapS1.po_callees AC MI_S1 S1ST := {| PmWrapS1.po_mva := state_mva_S1; PmWrapS1.po_dtor := state_dtor'_S1 |}.

  Theorem binary_parse_S1_inst : binary_parse_stmt SEGS Ly.L MI_S1 S1ST kcS1.
  Proof using AC RRND D DX. exact (PmWrap2S1.binary_parse_S1 CL_S1 PO_S1). Qed.

End Inst.
