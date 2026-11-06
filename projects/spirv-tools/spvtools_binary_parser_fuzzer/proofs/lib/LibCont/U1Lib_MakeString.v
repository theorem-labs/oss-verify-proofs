(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Ubsan.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StepTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.WalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StartupTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SumWalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MemSplit OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ShapeAlg OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SRealizes OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefReadLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibEff OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MmapSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibMaskBits OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.U1Layout.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.CRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.StrLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.LiveStats OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContStmts2 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.U1Facts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.U1Lib_Str_PushBack.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Module U1_code_667ec_66904.

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Ubsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_667ec : bv 32 := 0xfc010113.
Lemma F_667ec : fetch_word Ubsan.M.loaded_segments (0x6682c : word) = Some W_667ec.
Proof. vm_refl. Qed.
Lemma D_667ec : decode_any W_667ec = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_667f0 : bv 32 := 0x02113c23.
Lemma F_667f0 : fetch_word Ubsan.M.loaded_segments (0x66830 : word) = Some W_667f0.
Proof. vm_refl. Qed.
Lemma D_667f0 : decode_any W_667f0 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_667f4 : bv 32 := 0x02813823.
Lemma F_667f4 : fetch_word Ubsan.M.loaded_segments (0x66834 : word) = Some W_667f4.
Proof. vm_refl. Qed.
Lemma D_667f4 : decode_any W_667f4 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_667f8 : bv 32 := 0x02913423.
Lemma F_667f8 : fetch_word Ubsan.M.loaded_segments (0x66838 : word) = Some W_667f8.
Proof. vm_refl. Qed.
Lemma D_667f8 : decode_any W_667f8 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_667fc : bv 32 := 0x03213023.
Lemma F_667fc : fetch_word Ubsan.M.loaded_segments (0x6683c : word) = Some W_667fc.
Proof. vm_refl. Qed.
Lemma D_667fc : decode_any W_667fc = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_66800 : bv 32 := 0x01313c23.
Lemma F_66800 : fetch_word Ubsan.M.loaded_segments (0x66840 : word) = Some W_66800.
Proof. vm_refl. Qed.
Lemma D_66800 : decode_any W_66800 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_66804 : bv 32 := 0x01413823.
Lemma F_66804 : fetch_word Ubsan.M.loaded_segments (0x66844 : word) = Some W_66804.
Proof. vm_refl. Qed.
Lemma D_66804 : decode_any W_66804 = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_66808 : bv 32 := 0x01513423.
Lemma F_66808 : fetch_word Ubsan.M.loaded_segments (0x66848 : word) = Some W_66808.
Proof. vm_refl. Qed.
Lemma D_66808 : decode_any W_66808 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6680c : bv 32 := 0x01613023.
Lemma F_6680c : fetch_word Ubsan.M.loaded_segments (0x6684c : word) = Some W_6680c.
Proof. vm_refl. Qed.
Lemma D_6680c : decode_any W_6680c = Some (Store SZ8 2 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_66810 : bv 32 := 0x00058413.
Lemma F_66810 : fetch_word Ubsan.M.loaded_segments (0x66850 : word) = Some W_66810.
Proof. vm_refl. Qed.
Lemma D_66810 : decode_any W_66810 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_66814 : bv 32 := 0x00261913.
Lemma F_66814 : fetch_word Ubsan.M.loaded_segments (0x66854 : word) = Some W_66814.
Proof. vm_refl. Qed.
Lemma D_66814 : decode_any W_66814 = Some (ShiftImm ALU_SLL 18 12 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_66818 : bv 32 := 0x00b905b3.
Lemma F_66818 : fetch_word Ubsan.M.loaded_segments (0x66858 : word) = Some W_66818.
Proof. vm_refl. Qed.
Lemma D_66818 : decode_any W_66818 = Some (Op ALU_ADD 11 18 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_6681c : bv 32 := 0x008036b3.
Lemma F_6681c : fetch_word Ubsan.M.loaded_segments (0x6685c : word) = Some W_6681c.
Proof. vm_refl. Qed.
Lemma D_6681c : decode_any W_6681c = Some (Op ALU_SLTU 13 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_66820 : bv 32 := 0x0015b713.
Lemma F_66820 : fetch_word Ubsan.M.loaded_segments (0x66860 : word) = Some W_66820.
Proof. vm_refl. Qed.
Lemma D_66820 : decode_any W_66820 = Some (OpImm ALU_SLTU 14 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_66824 : bv 32 := 0x0ce68e63.
Lemma F_66824 : fetch_word Ubsan.M.loaded_segments (0x66864 : word) = Some W_66824.
Proof. vm_refl. Qed.
Lemma D_66824 : decode_any W_66824 = Some (Branch BC_EQ 13 14 220, 4%Z).
Proof. vm_refl. Qed.

Definition W_66828 : bv 32 := 0x00050493.
Lemma F_66828 : fetch_word Ubsan.M.loaded_segments (0x66868 : word) = Some W_66828.
Proof. vm_refl. Qed.
Lemma D_66828 : decode_any W_66828 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6682c : bv 32 := 0x00100513.
Lemma F_6682c : fetch_word Ubsan.M.loaded_segments (0x6686c : word) = Some W_6682c.
Proof. vm_refl. Qed.
Lemma D_6682c : decode_any W_6682c = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_66830 : bv 32 := 0x03d51513.
Lemma F_66830 : fetch_word Ubsan.M.loaded_segments (0x66870 : word) = Some W_66830.
Proof. vm_refl. Qed.
Lemma D_66830 : decode_any W_66830 = Some (ShiftImm ALU_SLL 10 10 61, 4%Z).
Proof. vm_refl. Qed.

Definition W_66834 : bv 32 := 0x00a60533.
Lemma F_66834 : fetch_word Ubsan.M.loaded_segments (0x66874 : word) = Some W_66834.
Proof. vm_refl. Qed.
Lemma D_66834 : decode_any W_66834 = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_66838 : bv 32 := 0x03e55513.
Lemma F_66838 : fetch_word Ubsan.M.loaded_segments (0x66878 : word) = Some W_66838.
Proof. vm_refl. Qed.
Lemma D_66838 : decode_any W_66838 = Some (ShiftImm ALU_SRL 10 10 62, 4%Z).
Proof. vm_refl. Qed.

Definition W_6683c : bv 32 := 0x0c051263.
Lemma F_6683c : fetch_word Ubsan.M.loaded_segments (0x6687c : word) = Some W_6683c.
Proof. vm_refl. Qed.
Lemma D_6683c : decode_any W_6683c = Some (Branch BC_NE 10 0 196, 4%Z).
Proof. vm_refl. Qed.

Definition W_66840 : bv 32 := 0x0c85e063.
Lemma F_66840 : fetch_word Ubsan.M.loaded_segments (0x66880 : word) = Some W_66840.
Proof. vm_refl. Qed.
Lemma D_66840 : decode_any W_66840 = Some (Branch BC_LTU 11 8 192, 4%Z).
Proof. vm_refl. Qed.

Definition W_66844 : bv 32 := 0x0a048e63.
Lemma F_66844 : fetch_word Ubsan.M.loaded_segments (0x66884 : word) = Some W_66844.
Proof. vm_refl. Qed.
Lemma D_66844 : decode_any W_66844 = Some (Branch BC_EQ 9 0 188, 4%Z).
Proof. vm_refl. Qed.

Definition W_66848 : bv 32 := 0x0004b023.
Lemma F_66848 : fetch_word Ubsan.M.loaded_segments (0x66888 : word) = Some W_66848.
Proof. vm_refl. Qed.
Lemma D_66848 : decode_any W_66848 = Some (Store SZ8 9 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6684c : bv 32 := 0x0004b423.
Lemma F_6684c : fetch_word Ubsan.M.loaded_segments (0x6688c : word) = Some W_6684c.
Proof. vm_refl. Qed.
Lemma D_6684c : decode_any W_6684c = Some (Store SZ8 9 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_66850 : bv 32 := 0x0004b823.
Lemma F_66850 : fetch_word Ubsan.M.loaded_segments (0x66890 : word) = Some W_66850.
Proof. vm_refl. Qed.
Lemma D_66850 : decode_any W_66850 = Some (Store SZ8 9 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_66854 : bv 32 := 0x08060263.
Lemma F_66854 : fetch_word Ubsan.M.loaded_segments (0x66894 : word) = Some W_66854.
Proof. vm_refl. Qed.
Lemma D_66854 : decode_any W_66854 = Some (Branch BC_EQ 12 0 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_66858 : bv 32 := 0x00347513.
Lemma F_66858 : fetch_word Ubsan.M.loaded_segments (0x66898 : word) = Some W_66858.
Proof. vm_refl. Qed.
Lemma D_66858 : decode_any W_66858 = Some (OpImm ALU_AND 10 8 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_6685c : bv 32 := 0x0a051263.
Lemma F_6685c : fetch_word Ubsan.M.loaded_segments (0x6689c : word) = Some W_6685c.
Proof. vm_refl. Qed.
Lemma D_6685c : decode_any W_6685c = Some (Branch BC_NE 10 0 164, 4%Z).
Proof. vm_refl. Qed.

Definition W_66860 : bv 32 := 0x00010537.
Lemma F_66860 : fetch_word Ubsan.M.loaded_segments (0x668a0 : word) = Some W_66860.
Proof. vm_refl. Qed.
Lemma D_66860 : decode_any W_66860 = Some (Lui 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_66864 : bv 32 := 0x00ff09b7.
Lemma F_66864 : fetch_word Ubsan.M.loaded_segments (0x668a4 : word) = Some W_66864.
Proof. vm_refl. Qed.
Lemma D_66864 : decode_any W_66864 = Some (Lui 19 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_66868 : bv 32 := 0xf0050a1b.
Lemma F_66868 : fetch_word Ubsan.M.loaded_segments (0x668a8 : word) = Some W_66868.
Proof. vm_refl. Qed.
Lemma D_66868 : decode_any W_66868 = Some (OpImm32 20 10 3840, 4%Z).
Proof. vm_refl. Qed.

Definition W_6686c : bv 32 := 0xffc00a93.
Lemma F_6686c : fetch_word Ubsan.M.loaded_segments (0x668ac : word) = Some W_6686c.
Proof. vm_refl. Qed.
Lemma D_6686c : decode_any W_6686c = Some (OpImm ALU_ADD 21 0 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_66870 : bv 32 := 0x08040863.
Lemma F_66870 : fetch_word Ubsan.M.loaded_segments (0x668b0 : word) = Some W_66870.
Proof. vm_refl. Qed.
Lemma D_66870 : decode_any W_66870 = Some (Branch BC_EQ 8 0 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_66874 : bv 32 := 0x00046b03.
Lemma F_66874 : fetch_word Ubsan.M.loaded_segments (0x668b4 : word) = Some W_66874.
Proof. vm_refl. Qed.
Lemma D_66874 : decode_any W_66874 = Some (Load SZ4 false 22 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_66878 : bv 32 := 0x0ffb7593.
Lemma F_66878 : fetch_word Ubsan.M.loaded_segments (0x668b8 : word) = Some W_66878.
Proof. vm_refl. Qed.
Lemma D_66878 : decode_any W_66878 = Some (OpImm ALU_AND 11 22 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_6687c : bv 32 := 0x04058e63.
Lemma F_6687c : fetch_word Ubsan.M.loaded_segments (0x668bc : word) = Some W_6687c.
Proof. vm_refl. Qed.
Lemma D_6687c : decode_any W_6687c = Some (Branch BC_EQ 11 0 92, 4%Z).
Proof. vm_refl. Qed.

Definition W_66880 : bv 32 := 0x00048513.
Lemma F_66880 : fetch_word Ubsan.M.loaded_segments (0x668c0 : word) = Some W_66880.
Proof. vm_refl. Qed.
Lemma D_66880 : decode_any W_66880 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_66884 : bv 32 := 0x115260ef.
Lemma F_66884 : fetch_word Ubsan.M.loaded_segments (0x668c4 : word) = Some W_66884.
Proof. vm_refl. Qed.
Lemma D_66884 : decode_any W_66884 = Some (Jal 1 157972, 4%Z).
Proof. vm_refl. Qed.

Definition W_66888 : bv 32 := 0x014b7533.
Lemma F_66888 : fetch_word Ubsan.M.loaded_segments (0x668c8 : word) = Some W_66888.
Proof. vm_refl. Qed.
Lemma D_66888 : decode_any W_66888 = Some (Op ALU_AND 10 22 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_6688c : bv 32 := 0x04050663.
Lemma F_6688c : fetch_word Ubsan.M.loaded_segments (0x668cc : word) = Some W_6688c.
Proof. vm_refl. Qed.
Lemma D_6688c : decode_any W_6688c = Some (Branch BC_EQ 10 0 76, 4%Z).
Proof. vm_refl. Qed.

Definition W_66890 : bv 32 := 0x030b1593.
Lemma F_66890 : fetch_word Ubsan.M.loaded_segments (0x668d0 : word) = Some W_66890.
Proof. vm_refl. Qed.
Lemma D_66890 : decode_any W_66890 = Some (ShiftImm ALU_SLL 11 22 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_66894 : bv 32 := 0x0385d593.
Lemma F_66894 : fetch_word Ubsan.M.loaded_segments (0x668d4 : word) = Some W_66894.
Proof. vm_refl. Qed.
Lemma D_66894 : decode_any W_66894 = Some (ShiftImm ALU_SRL 11 11 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_66898 : bv 32 := 0x00048513.
Lemma F_66898 : fetch_word Ubsan.M.loaded_segments (0x668d8 : word) = Some W_66898.
Proof. vm_refl. Qed.
Lemma D_66898 : decode_any W_66898 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6689c : bv 32 := 0x0fd260ef.
Lemma F_6689c : fetch_word Ubsan.M.loaded_segments (0x668dc : word) = Some W_6689c.
Proof. vm_refl. Qed.
Lemma D_6689c : decode_any W_6689c = Some (Jal 1 157948, 4%Z).
Proof. vm_refl. Qed.

Definition W_668a0 : bv 32 := 0x013b7533.
Lemma F_668a0 : fetch_word Ubsan.M.loaded_segments (0x668e0 : word) = Some W_668a0.
Proof. vm_refl. Qed.
Lemma D_668a0 : decode_any W_668a0 = Some (Op ALU_AND 10 22 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_668a4 : bv 32 := 0x02050a63.
Lemma F_668a4 : fetch_word Ubsan.M.loaded_segments (0x668e4 : word) = Some W_668a4.
Proof. vm_refl. Qed.
Lemma D_668a4 : decode_any W_668a4 = Some (Branch BC_EQ 10 0 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_668a8 : bv 32 := 0x028b1593.
Lemma F_668a8 : fetch_word Ubsan.M.loaded_segments (0x668e8 : word) = Some W_668a8.
Proof. vm_refl. Qed.
Lemma D_668a8 : decode_any W_668a8 = Some (ShiftImm ALU_SLL 11 22 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_668ac : bv 32 := 0x0385d593.
Lemma F_668ac : fetch_word Ubsan.M.loaded_segments (0x668ec : word) = Some W_668ac.
Proof. vm_refl. Qed.
Lemma D_668ac : decode_any W_668ac = Some (ShiftImm ALU_SRL 11 11 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_668b0 : bv 32 := 0x00048513.
Lemma F_668b0 : fetch_word Ubsan.M.loaded_segments (0x668f0 : word) = Some W_668b0.
Proof. vm_refl. Qed.
Lemma D_668b0 : decode_any W_668b0 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_668b4 : bv 32 := 0x0e5260ef.
Lemma F_668b4 : fetch_word Ubsan.M.loaded_segments (0x668f4 : word) = Some W_668b4.
Proof. vm_refl. Qed.
Lemma D_668b4 : decode_any W_668b4 = Some (Jal 1 157924, 4%Z).
Proof. vm_refl. Qed.

Definition W_668b8 : bv 32 := 0x018b5593.
Lemma F_668b8 : fetch_word Ubsan.M.loaded_segments (0x668f8 : word) = Some W_668b8.
Proof. vm_refl. Qed.
Lemma D_668b8 : decode_any W_668b8 = Some (ShiftImm ALU_SRL 11 22 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_668bc : bv 32 := 0x00058e63.
Lemma F_668bc : fetch_word Ubsan.M.loaded_segments (0x668fc : word) = Some W_668bc.
Proof. vm_refl. Qed.
Lemma D_668bc : decode_any W_668bc = Some (Branch BC_EQ 11 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_668c0 : bv 32 := 0x00048513.
Lemma F_668c0 : fetch_word Ubsan.M.loaded_segments (0x66900 : word) = Some W_668c0.
Proof. vm_refl. Qed.
Lemma D_668c0 : decode_any W_668c0 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_668c4 : bv 32 := 0x0d5260ef.
Lemma F_668c4 : fetch_word Ubsan.M.loaded_segments (0x66904 : word) = Some W_668c4.
Proof. vm_refl. Qed.
Lemma D_668c4 : decode_any W_668c4 = Some (Jal 1 157908, 4%Z).
Proof. vm_refl. Qed.

Definition W_668c8 : bv 32 := 0x03547c63.
Lemma F_668c8 : fetch_word Ubsan.M.loaded_segments (0x66908 : word) = Some W_668c8.
Proof. vm_refl. Qed.
Lemma D_668c8 : decode_any W_668c8 = Some (Branch BC_GEU 8 21 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_668cc : bv 32 := 0xffc90913.
Lemma F_668cc : fetch_word Ubsan.M.loaded_segments (0x6690c : word) = Some W_668cc.
Proof. vm_refl. Qed.
Lemma D_668cc : decode_any W_668cc = Some (OpImm ALU_ADD 18 18 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_668d0 : bv 32 := 0x00440413.
Lemma F_668d0 : fetch_word Ubsan.M.loaded_segments (0x66910 : word) = Some W_668d0.
Proof. vm_refl. Qed.
Lemma D_668d0 : decode_any W_668d0 = Some (OpImm ALU_ADD 8 8 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_668d4 : bv 32 := 0xf8091ee3.
Lemma F_668d4 : fetch_word Ubsan.M.loaded_segments (0x66914 : word) = Some W_668d4.
Proof. vm_refl. Qed.
Lemma D_668d4 : decode_any W_668d4 = Some (Branch BC_NE 18 0 8092, 4%Z).
Proof. vm_refl. Qed.

Definition W_668d8 : bv 32 := 0x03813083.
Lemma F_668d8 : fetch_word Ubsan.M.loaded_segments (0x66918 : word) = Some W_668d8.
Proof. vm_refl. Qed.
Lemma D_668d8 : decode_any W_668d8 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_668dc : bv 32 := 0x03013403.
Lemma F_668dc : fetch_word Ubsan.M.loaded_segments (0x6691c : word) = Some W_668dc.
Proof. vm_refl. Qed.
Lemma D_668dc : decode_any W_668dc = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_668e0 : bv 32 := 0x02813483.
Lemma F_668e0 : fetch_word Ubsan.M.loaded_segments (0x66920 : word) = Some W_668e0.
Proof. vm_refl. Qed.
Lemma D_668e0 : decode_any W_668e0 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_668e4 : bv 32 := 0x02013903.
Lemma F_668e4 : fetch_word Ubsan.M.loaded_segments (0x66924 : word) = Some W_668e4.
Proof. vm_refl. Qed.
Lemma D_668e4 : decode_any W_668e4 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_668e8 : bv 32 := 0x01813983.
Lemma F_668e8 : fetch_word Ubsan.M.loaded_segments (0x66928 : word) = Some W_668e8.
Proof. vm_refl. Qed.
Lemma D_668e8 : decode_any W_668e8 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_668ec : bv 32 := 0x01013a03.
Lemma F_668ec : fetch_word Ubsan.M.loaded_segments (0x6692c : word) = Some W_668ec.
Proof. vm_refl. Qed.
Lemma D_668ec : decode_any W_668ec = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_668f0 : bv 32 := 0x00813a83.
Lemma F_668f0 : fetch_word Ubsan.M.loaded_segments (0x66930 : word) = Some W_668f0.
Proof. vm_refl. Qed.
Lemma D_668f0 : decode_any W_668f0 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_668f4 : bv 32 := 0x00013b03.
Lemma F_668f4 : fetch_word Ubsan.M.loaded_segments (0x66934 : word) = Some W_668f4.
Proof. vm_refl. Qed.
Lemma D_668f4 : decode_any W_668f4 = Some (Load SZ8 true 22 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_668f8 : bv 32 := 0x04010113.
Lemma F_668f8 : fetch_word Ubsan.M.loaded_segments (0x66938 : word) = Some W_668f8.
Proof. vm_refl. Qed.
Lemma D_668f8 : decode_any W_668f8 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_668fc : bv 32 := 0x00008067.
Lemma F_668fc : fetch_word Ubsan.M.loaded_segments (0x6693c : word) = Some W_668fc.
Proof. vm_refl. Qed.
Lemma D_668fc : decode_any W_668fc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
End U1_code_667ec_66904.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac WalkTac StartupTac SumWalkTac StoreOk MemSplit Hoare ShapeAlg
  SRealizes RefMemcpyLib RefReadLib LibIface LibEff MmapSim LibMaskBits U1Layout.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContLib StrLib LiveStats ContStmts ContStmts2 U1Facts U1Lib_Str_PushBack.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.U1Lib_MakeString.U1_code_667ec_66904.
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
Ltac b2z8 := apply bytes_le_to_Z_8.
Ltac cmpz := pin; unfold c_ltu, c_eq, c_lts, bv_ltu, bv_lts, bv_eqb; imm_norm; rewrite ?u64_of_Z by lia; rewrite ?bv_signed_small64 by lia;
  first [apply Z.ltb_lt; lia | apply Z.ltb_ge; lia | apply Z.eqb_eq; lia | apply Z.eqb_neq; lia | reflexivity].
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

Lemma step_sltu_at {fx : FPState} : forall segs regs pc mem rom w rd rs1 rs2 v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op ALU_SLTU rd rs1 rs2, 4%Z) -> bv_eqb rd 0 = false ->
  v_sltu (getr regs rs1) (getr regs rs2) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) = MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof. intros segs regs pc mem rom w rd rs1 rs2 v Hf He Hd Hrd Hv. rewrite (step_sltu segs regs pc mem rom w rd rs1 rs2 Hf He Hd). rewrite Hrd, Hv. reflexivity. Qed.
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
    Hypotheses (Hnw0 : 0 <= nw) (Hws : Zlen ws = nw) (Hw0 : 0 <= w) (Hw1 : w + 4 * nw <= 2 ^ 63) (Hw4 : w mod 4 = 0).
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
      iv_sl8  : rdn SEGS M' (Z_to_bv 64 (sp - 64)) 8 = Some (word_to_le_bytes 8 (getr R 22%bv));
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
      rg_s3 : getr R' 19%bv = Z_to_bv 64 0xff0000;
      rg_s4 : getr R' 20%bv = Z_to_bv 64 0xff00;
      rg_s5 : getr R' 21%bv = Z_to_bv 64 (2 ^ 64 - 4);
      rg_s6 : getr R' 22%bv = x;
      rg_gp : getr R' 3%bv = getr R 3%bv;
      rg_tp : getr R' 4%bv = getr R 4%bv;
      rg_hi : forall r, In r [23; 24; 25; 26; 27]%bv -> getr R' r = getr R r
    }.
    #[local] Ltac dCB := destruct CB as [AI MS ROC SXI SXH CR Hceil HROOM Hwin Hown_sx Herr_sx].

    Lemma Hspr : alloc_ceiling + STK <= sp /\ sp < 2 ^ 47 /\ sp mod 16 = 0 /\ 2 ^ 24 <= sp - STK /\ 0 <= MALLOC_STACK MI /\ STK = 128 + (16 + MALLOC_STACK MI).
    Proof using AC MI ST MALLOC_STACK_pos A s R M model sp ret w CB Hw0. dCB. destruct CR. pose proof ac_bounds_lit. unfold STK in *. lia. Qed.

    Lemma WINp : p + 24 <= sp - STK \/ sp <= p.
    Proof using AC MI MALLOC_STACK_pos A sp p w OBJp Hw0.
      destruct OBJp as [_ W]. unfold STK in *.
      destruct (Z.lt_ge_cases p sp); [left|right; lia].
      destruct (Z.lt_ge_cases (p + 24) (sp - (128 + (16 + MALLOC_STACK MI)) + 1)); [lia|]. exfalso.
      destruct (Z.lt_ge_cases p (sp - (128 + (16 + MALLOC_STACK MI)))).
      - apply (W (sp - (128 + (16 + MALLOC_STACK MI)))); unfold zwin; lia.
      - apply (W p); unfold zwin; lia.
    Qed.

    Lemma WINw : w + 4 * nw <= sp - STK \/ sp <= w \/ nw = 0.
    Proof using AC MI MALLOC_STACK_pos A sp w nw Hnw0 Hw0 OBJw.
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
    Proof using w Hw0.
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
    Proof using AC MI ST A s R M model sp ret w nw ws CB Hws Hw0 Hw1 WS OBJw.
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
    Proof using AC MI ST A s R M model sp ret p w nw ws Hw0.
      intros A' M' model' m' cs' J d asz IV ->.
      destruct IV as [AI' MS' FS' SX' ROC' SL1 SL2 SL3 SL4 SL5 SL6 SL7 SL8 STR GS LV DJ' CAPS JK EFF WIN WDEF WSM].
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
    Proof using AC MI ST MALLOC_STACK_pos A s R M model sp ret p w nw ws CB OBJp Hw0.
      intros A' M' model' m' cs' J a IV HF. pose proof Hspr as (Hc & _ & _ & _ & _ & HSTK). pose proof WINp as WP.
      pose proof IV as IV'. destruct IV as [AI' MS' FS' SX' ROC' SL1 SL2 SL3 SL4 SL5 SL6 SL7 SL8 STR GS LV DJ' CAPS JK EFF WIN WDEF WSM].
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
    Proof using AC MI ST MALLOC_STACK_pos A s R M model sp ret p w nw ws CB OBJp Hw0.
      intros A' M' model' m' cs' J R1 ra IV H2 H1 Hret Hra H3 H4.
      pose proof Hspr as (Hc & Hs47 & Hs16 & Hs20 & HMS & HSTK). pose proof IV as IV'.
      destruct IV as [AI' MS' FS' SX' ROC' SL1 SL2 SL3 SL4 SL5 SL6 SL7 SL8 STR GS LV DJ' CAPS JK EFF WIN WDEF WSM]. dCB. destruct CR.
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
    Proof using AC MI ST A s R M model sp ret p w nw ws OBJp Hw0.
      intros A' M' model' m' cs' J IV. destruct IV as [AI' MS' FS' SX' ROC' SL1 SL2 SL3 SL4 SL5 SL6 SL7 SL8 STR GS LV DJ' CAPS JK EFF WIN WDEF WSM].
      destruct OBJp as [PL W]. split.
      - eapply (placed_mono SEGS Ly.L MI); [|exact PL]. intros blk Hb. destruct blk as [q k]. apply LV. left. exact Hb.
      - intros a Ha Hw. apply (W a Ha). unfold zwin, STK in *. lia.
    Qed.

    Lemma inv_room : forall A' M' model' m' cs' J,
      INV A' M' model' m' cs' J -> Zlen cs' < 4 * nw ->
      Zlen cs' = str_cap m' -> str_grow m' <= NMAX MI /\ roomL MI A' (live MI A') (str_grow m').
    Proof using AC MI ST A s R M model sp ret p w nw ws CB Hws Hw0 HNMAX ROOM.
      intros A' M' model' m' cs' J IV Hlt Hfull. pose proof IV as IV'.
      destruct IV as [AI' MS' FS' SX' ROC' SL1 SL2 SL3 SL4 SL5 SL6 SL7 SL8 STR GS LV DJ' CAPS JK EFF WIN WDEF WSM]. dCB.
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
    Proof using AC MI ST MALLOC_STACK_pos A s R M model sp ret p w nw CB OBJp Hw0 OBJw.
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
    Proof using w Hw0.
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
      destruct IV as [AI' MS' FS' SX' ROC' SL1 SL2 SL3 SL4 SL5 SL6 SL7 SL8 STR GS LV DJ' CAPS JK EFF WIN WDEF WSM].
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
      - apply SLT; [lia|lia|exact SL8].
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
    #[local] Ltac dIV IV := destruct IV as [AI' MS' FS' SX' ROC' SL1 SL2 SL3 SL4 SL5 SL6 SL7 SL8 STR GS LV DJ' CAPS JK EFF WIN WDEF WSM].

    Lemma EXIT : forall A' R' M' model' m' cs' J,
      INV A' M' model' m' cs' J -> ms_chars ws = cs' ->
      getr R' 2%bv = Z_to_bv 64 (sp - 64) -> getr R' 3%bv = getr R 3%bv -> getr R' 4%bv = getr R 4%bv ->
      (forall r, In r [23; 24; 25; 26; 27]%bv -> getr R' r = getr R r) ->
      srealizes SEGS (mkCfg (@mkst fx R' (Z_to_bv 64 0x66918) M' (seg_rom SEGS)) model') K.
    Proof using AC MI ST MALLOC_STACK_pos fx A s R M model sp ret p w nw ws K CB Hw0 CONT.
      intros A' R' M' model' m' cs' J IV Hcs H2 H3 H4 HS. subst cs'.
      pose proof Hspr as (Hc & Hs47 & Hs16 & Hs20 & HMS & HSTK). pose proof ac_bounds_lit as Hcv.
      dIV IV. dCB. destruct CR as [Hra Hret Hretr Hsp Hsp16 Hsphi Hgp Htp].
      eapply srz_msteps; [exact (ms_halt _ MS') | exact (ms_lazy _ MS') | | ].
      { norm_pc.
        ld_step F_668d8 D_668d8 (word_to_le_bytes 8 (Z_to_bv 64 ret)) (Z_to_bv 64 ret) ltac:(rdn_fix SL1) ltac:(b2z8).
        ld_step F_668dc D_668dc (word_to_le_bytes 8 (getr R 8%bv)) (getr R 8%bv) ltac:(rdn_fix SL2) ltac:(b2z8).
        ld_step F_668e0 D_668e0 (word_to_le_bytes 8 (getr R 9%bv)) (getr R 9%bv) ltac:(rdn_fix SL3) ltac:(b2z8).
        ld_step F_668e4 D_668e4 (word_to_le_bytes 8 (getr R 18%bv)) (getr R 18%bv) ltac:(rdn_fix SL4) ltac:(b2z8).
        ld_step F_668e8 D_668e8 (word_to_le_bytes 8 (getr R 19%bv)) (getr R 19%bv) ltac:(rdn_fix SL5) ltac:(b2z8).
        ld_step F_668ec D_668ec (word_to_le_bytes 8 (getr R 20%bv)) (getr R 20%bv) ltac:(rdn_fix SL6) ltac:(b2z8).
        ld_step F_668f0 D_668f0 (word_to_le_bytes 8 (getr R 21%bv)) (getr R 21%bv) ltac:(rdn_fix SL7) ltac:(b2z8).
        ld_step F_668f4 D_668f4 (word_to_le_bytes 8 (getr R 22%bv)) (getr R 22%bv) ltac:(rdn_fix SL8) ltac:(b2z8).
        sv F_668f8 D_668f8 (Z_to_bv 64 sp).
        stepjr F_668fc D_668fc (Z_to_bv 64 ret) ltac:(gres; reflexivity).
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
         srealizes SEGS (mkCfg (@mkst fx R'' (Z_to_bv 64 0x668c8) M'' (seg_rom SEGS)) model'') K) ->
      srealizes SEGS (mkCfg (@mkst fx R' (Z_to_bv 64 0x668c0) M' (seg_rom SEGS)) model') K.
    Proof using AC MI ST MALLOC_STACK_pos NEW fx A s R M model sp ret p w nw ws K CB Hp0 Hp1 OBJp Hnw0 Hws Hw0 Hw1 OBJw DJ HNMAX ROOM.
      intros j x c A' R' M' model' m' cs' J IV RG Hc Hcr Hlt HK.
      pose proof IV as IV'. destruct IV as [AI' MS' FS' SX' ROC' SL1 SL2 SL3 SL4 SL5 SL6 SL7 SL8 STR GS LV DJ' CAPS JK EFF WIN WDEF WSM].
      destruct RG as [G2 G8 G9 G18 G19 G20 G21 G22 G3 G4 GS6].
      eapply srz_msteps; [exact (ms_halt _ MS') | exact (ms_lazy _ MS') | norm_pc; sv F_66880 D_66880 (Z_to_bv 64 p); stepj F_66884 D_66884; close_pc | ].
      lazymatch goal with |- srealizes _ (mkCfg (mkst ?r ?pc _ _) _) _ =>
         replace pc with (Z_to_bv 64 (sc_push_back c8d144)) by (apply bv_eq; vm_compute; reflexivity); set (R1 := r) end.
      eapply (str_push_back_8d144_spec MI ST MALLOC_STACK_pos NEW fx A' s R1 M' model' (sp - 64) 0x668c8 p c m' cs' K).
      - cbn [sc_push_stack c8d144]. unfold NEW_STACK. eapply (inv_callB _ _ _ _ _ _ R1 0x668c8 IV');
          [unfold R1; gres; exact G2 | unfold R1; gres; apply bv_eq; vm_compute; reflexivity
          | unfold ret_ok; apply bv_eq; vm_compute; reflexivity | lia | unfold R1; gres; exact G3 | unfold R1; gres; exact G4].
      - unfold R1; gres; reflexivity.
      - unfold R1; gres; exact Hc.
      - exact STR.
      - cbn [sc_push_stack c8d144]. unfold NEW_STACK. exact (inv_obj _ _ _ _ _ _ IV').
      - cbn [sc_push_stack c8d144]. intros Hfull. exact (inv_room _ _ _ _ _ _ IV' Hlt Hfull).
      - intros A'' R'' M'' model'' m'' RB STR'' ALT EFF2. rewrite (Z.mod_small c 256) in STR'' by lia.
        apply (HK A'' R'' M'' model'' m'' (fun a => J a \/ sbuf_fp m' a)).
        + eapply (inv_post _ _ _ _ _ _ R1 _ R'' _ _ _ _ IV' Hlt RB STR'' ALT).
          cbn [sc_push_stack c8d144] in EFF2. unfold NEW_STACK in EFF2. exact EFF2.
        + destruct RB as [_ _ _ _ _ KP]. constructor;
          first [ rewrite (KP _) by in_cs; unfold R1; gres; assumption
                | intros r Hr; pose proof Hr as Hr'; repeat (destruct Hr as [<-|Hr]; [rewrite (KP _) by in_cs; unfold R1; gres; apply GS6; exact Hr' |]); destruct Hr ].
    Qed.

    Lemma CALL2 : forall j x c A' R' M' model' m' cs' J,
      INV A' M' model' m' cs' J -> REGS R' j x -> getr R' 11%bv = Z_to_bv 64 c -> 0 < c < 256 -> Zlen cs' < 4 * nw ->
      (forall A'' R'' M'' model'' m'' J'', INV A'' M'' model'' m'' (cs' ++ [c]) J'' -> REGS R'' j x ->
         srealizes SEGS (mkCfg (@mkst fx R'' (Z_to_bv 64 0x668e0) M'' (seg_rom SEGS)) model'') K) ->
      srealizes SEGS (mkCfg (@mkst fx R' (Z_to_bv 64 0x668d8) M' (seg_rom SEGS)) model') K.
    Proof using AC MI ST MALLOC_STACK_pos NEW fx A s R M model sp ret p w nw ws K CB Hp0 Hp1 OBJp Hnw0 Hws Hw0 Hw1 OBJw DJ HNMAX ROOM.
      intros j x c A' R' M' model' m' cs' J IV RG Hc Hcr Hlt HK.
      pose proof IV as IV'. destruct IV as [AI' MS' FS' SX' ROC' SL1 SL2 SL3 SL4 SL5 SL6 SL7 SL8 STR GS LV DJ' CAPS JK EFF WIN WDEF WSM].
      destruct RG as [G2 G8 G9 G18 G19 G20 G21 G22 G3 G4 GS6].
      eapply srz_msteps; [exact (ms_halt _ MS') | exact (ms_lazy _ MS') | norm_pc; sv F_66898 D_66898 (Z_to_bv 64 p); stepj F_6689c D_6689c; close_pc | ].
      lazymatch goal with |- srealizes _ (mkCfg (mkst ?r ?pc _ _) _) _ =>
         replace pc with (Z_to_bv 64 (sc_push_back c8d144)) by (apply bv_eq; vm_compute; reflexivity); set (R1 := r) end.
      eapply (str_push_back_8d144_spec MI ST MALLOC_STACK_pos NEW fx A' s R1 M' model' (sp - 64) 0x668e0 p c m' cs' K).
      - cbn [sc_push_stack c8d144]. unfold NEW_STACK. eapply (inv_callB _ _ _ _ _ _ R1 0x668e0 IV');
          [unfold R1; gres; exact G2 | unfold R1; gres; apply bv_eq; vm_compute; reflexivity
          | unfold ret_ok; apply bv_eq; vm_compute; reflexivity | lia | unfold R1; gres; exact G3 | unfold R1; gres; exact G4].
      - unfold R1; gres; reflexivity.
      - unfold R1; gres; exact Hc.
      - exact STR.
      - cbn [sc_push_stack c8d144]. unfold NEW_STACK. exact (inv_obj _ _ _ _ _ _ IV').
      - cbn [sc_push_stack c8d144]. intros Hfull. exact (inv_room _ _ _ _ _ _ IV' Hlt Hfull).
      - intros A'' R'' M'' model'' m'' RB STR'' ALT EFF2. rewrite (Z.mod_small c 256) in STR'' by lia.
        apply (HK A'' R'' M'' model'' m'' (fun a => J a \/ sbuf_fp m' a)).
        + eapply (inv_post _ _ _ _ _ _ R1 _ R'' _ _ _ _ IV' Hlt RB STR'' ALT).
          cbn [sc_push_stack c8d144] in EFF2. unfold NEW_STACK in EFF2. exact EFF2.
        + destruct RB as [_ _ _ _ _ KP]. constructor;
          first [ rewrite (KP _) by in_cs; unfold R1; gres; assumption
                | intros r Hr; pose proof Hr as Hr'; repeat (destruct Hr as [<-|Hr]; [rewrite (KP _) by in_cs; unfold R1; gres; apply GS6; exact Hr' |]); destruct Hr ].
    Qed.

    Lemma CALL3 : forall j x c A' R' M' model' m' cs' J,
      INV A' M' model' m' cs' J -> REGS R' j x -> getr R' 11%bv = Z_to_bv 64 c -> 0 < c < 256 -> Zlen cs' < 4 * nw ->
      (forall A'' R'' M'' model'' m'' J'', INV A'' M'' model'' m'' (cs' ++ [c]) J'' -> REGS R'' j x ->
         srealizes SEGS (mkCfg (@mkst fx R'' (Z_to_bv 64 0x668f8) M'' (seg_rom SEGS)) model'') K) ->
      srealizes SEGS (mkCfg (@mkst fx R' (Z_to_bv 64 0x668f0) M' (seg_rom SEGS)) model') K.
    Proof using AC MI ST MALLOC_STACK_pos NEW fx A s R M model sp ret p w nw ws K CB Hp0 Hp1 OBJp Hnw0 Hws Hw0 Hw1 OBJw DJ HNMAX ROOM.
      intros j x c A' R' M' model' m' cs' J IV RG Hc Hcr Hlt HK.
      pose proof IV as IV'. destruct IV as [AI' MS' FS' SX' ROC' SL1 SL2 SL3 SL4 SL5 SL6 SL7 SL8 STR GS LV DJ' CAPS JK EFF WIN WDEF WSM].
      destruct RG as [G2 G8 G9 G18 G19 G20 G21 G22 G3 G4 GS6].
      eapply srz_msteps; [exact (ms_halt _ MS') | exact (ms_lazy _ MS') | norm_pc; sv F_668b0 D_668b0 (Z_to_bv 64 p); stepj F_668b4 D_668b4; close_pc | ].
      lazymatch goal with |- srealizes _ (mkCfg (mkst ?r ?pc _ _) _) _ =>
         replace pc with (Z_to_bv 64 (sc_push_back c8d144)) by (apply bv_eq; vm_compute; reflexivity); set (R1 := r) end.
      eapply (str_push_back_8d144_spec MI ST MALLOC_STACK_pos NEW fx A' s R1 M' model' (sp - 64) 0x668f8 p c m' cs' K).
      - cbn [sc_push_stack c8d144]. unfold NEW_STACK. eapply (inv_callB _ _ _ _ _ _ R1 0x668f8 IV');
          [unfold R1; gres; exact G2 | unfold R1; gres; apply bv_eq; vm_compute; reflexivity
          | unfold ret_ok; apply bv_eq; vm_compute; reflexivity | lia | unfold R1; gres; exact G3 | unfold R1; gres; exact G4].
      - unfold R1; gres; reflexivity.
      - unfold R1; gres; exact Hc.
      - exact STR.
      - cbn [sc_push_stack c8d144]. unfold NEW_STACK. exact (inv_obj _ _ _ _ _ _ IV').
      - cbn [sc_push_stack c8d144]. intros Hfull. exact (inv_room _ _ _ _ _ _ IV' Hlt Hfull).
      - intros A'' R'' M'' model'' m'' RB STR'' ALT EFF2. rewrite (Z.mod_small c 256) in STR'' by lia.
        apply (HK A'' R'' M'' model'' m'' (fun a => J a \/ sbuf_fp m' a)).
        + eapply (inv_post _ _ _ _ _ _ R1 _ R'' _ _ _ _ IV' Hlt RB STR'' ALT).
          cbn [sc_push_stack c8d144] in EFF2. unfold NEW_STACK in EFF2. exact EFF2.
        + destruct RB as [_ _ _ _ _ KP]. constructor;
          first [ rewrite (KP _) by in_cs; unfold R1; gres; assumption
                | intros r Hr; pose proof Hr as Hr'; repeat (destruct Hr as [<-|Hr]; [rewrite (KP _) by in_cs; unfold R1; gres; apply GS6; exact Hr' |]); destruct Hr ].
    Qed.

    Lemma CALL4 : forall j x c A' R' M' model' m' cs' J,
      INV A' M' model' m' cs' J -> REGS R' j x -> getr R' 11%bv = Z_to_bv 64 c -> 0 < c < 256 -> Zlen cs' < 4 * nw ->
      (forall A'' R'' M'' model'' m'' J'', INV A'' M'' model'' m'' (cs' ++ [c]) J'' -> REGS R'' j x ->
         srealizes SEGS (mkCfg (@mkst fx R'' (Z_to_bv 64 0x66908) M'' (seg_rom SEGS)) model'') K) ->
      srealizes SEGS (mkCfg (@mkst fx R' (Z_to_bv 64 0x66900) M' (seg_rom SEGS)) model') K.
    Proof using AC MI ST MALLOC_STACK_pos NEW fx A s R M model sp ret p w nw ws K CB Hp0 Hp1 OBJp Hnw0 Hws Hw0 Hw1 OBJw DJ HNMAX ROOM.
      intros j x c A' R' M' model' m' cs' J IV RG Hc Hcr Hlt HK.
      pose proof IV as IV'. destruct IV as [AI' MS' FS' SX' ROC' SL1 SL2 SL3 SL4 SL5 SL6 SL7 SL8 STR GS LV DJ' CAPS JK EFF WIN WDEF WSM].
      destruct RG as [G2 G8 G9 G18 G19 G20 G21 G22 G3 G4 GS6].
      eapply srz_msteps; [exact (ms_halt _ MS') | exact (ms_lazy _ MS') | norm_pc; sv F_668c0 D_668c0 (Z_to_bv 64 p); stepj F_668c4 D_668c4; close_pc | ].
      lazymatch goal with |- srealizes _ (mkCfg (mkst ?r ?pc _ _) _) _ =>
         replace pc with (Z_to_bv 64 (sc_push_back c8d144)) by (apply bv_eq; vm_compute; reflexivity); set (R1 := r) end.
      eapply (str_push_back_8d144_spec MI ST MALLOC_STACK_pos NEW fx A' s R1 M' model' (sp - 64) 0x66908 p c m' cs' K).
      - cbn [sc_push_stack c8d144]. unfold NEW_STACK. eapply (inv_callB _ _ _ _ _ _ R1 0x66908 IV');
          [unfold R1; gres; exact G2 | unfold R1; gres; apply bv_eq; vm_compute; reflexivity
          | unfold ret_ok; apply bv_eq; vm_compute; reflexivity | lia | unfold R1; gres; exact G3 | unfold R1; gres; exact G4].
      - unfold R1; gres; reflexivity.
      - unfold R1; gres; exact Hc.
      - exact STR.
      - cbn [sc_push_stack c8d144]. unfold NEW_STACK. exact (inv_obj _ _ _ _ _ _ IV').
      - cbn [sc_push_stack c8d144]. intros Hfull. exact (inv_room _ _ _ _ _ _ IV' Hlt Hfull).
      - intros A'' R'' M'' model'' m'' RB STR'' ALT EFF2. rewrite (Z.mod_small c 256) in STR'' by lia.
        apply (HK A'' R'' M'' model'' m'' (fun a => J a \/ sbuf_fp m' a)).
        + eapply (inv_post _ _ _ _ _ _ R1 _ R'' _ _ _ _ IV' Hlt RB STR'' ALT).
          cbn [sc_push_stack c8d144] in EFF2. unfold NEW_STACK in EFF2. exact EFF2.
        + destruct RB as [_ _ _ _ _ KP]. constructor;
          first [ rewrite (KP _) by in_cs; unfold R1; gres; assumption
                | intros r Hr; pose proof Hr as Hr'; repeat (destruct Hr as [<-|Hr]; [rewrite (KP _) by in_cs; unfold R1; gres; apply GS6; exact Hr' |]); destruct Hr ].
    Qed.

    Lemma Wpos : 0 < nw -> 0 < w.
    Proof using AC MI ST A s R M model sp ret w nw CB Hw0 OBJw.
      intros Hn. dCB. destruct OBJw as [PL _]. pose proof ac_bounds_lit.
      destruct PL as [Hst|(q & k & Hin & Hq & Hqk)]; [lia|].
      destruct (ai_live_block MI A M model q k AI Hin) as (_ & _ & Hq0 & _). lia.
    Qed.

    Lemma ms_word : forall x rest, 0 <= x < 2 ^ 32 ->
      ms_chars (x :: rest) =
        if x mod 256 =? 0 then []
        else if (x / 256) mod 256 =? 0 then [x mod 256]
        else if (x / 256 / 256) mod 256 =? 0 then [x mod 256; (x / 256) mod 256]
        else if (x / 256 / 256 / 256) mod 256 =? 0 then [x mod 256; (x / 256) mod 256; (x / 256 / 256) mod 256]
        else [x mod 256; (x / 256) mod 256; (x / 256 / 256) mod 256; (x / 256 / 256 / 256) mod 256] ++ ms_chars rest.
    Proof using w Hw0.
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
          srealizes SEGS (mkCfg (@mkst fx R' (Z_to_bv 64 0x668b0) M' (seg_rom SEGS)) model') K) ->
      forall A' R' M' model' m' cs' J x, INV A' M' model' m' cs' J -> REGS R' j x -> Zlen cs' <= 4 * j ->
          ms_chars ws = cs' ++ ms_chars (skipn (Z.to_nat j) ws) ->
          srealizes SEGS (mkCfg (@mkst fx R' (Z_to_bv 64 0x668b0) M' (seg_rom SEGS)) model') K.
    Proof using AC MI ST MALLOC_STACK_pos NEW fx A s R M model sp ret p w nw ws K CB Hp0 Hp1 OBJp Hnw0 Hws Hw0 Hw1 WS OBJw DJ HNMAX ROOM CONT.
      intros j Hj IH A' R' M' model' m' cs' J x0 IV RG Hlen Hms. pose proof (Wpos ltac:(lia)) as Hwp.
      rewrite (skipn_Znth j ws) in Hms by lia.
      set (x := Znth j ws) in *. destruct (WS j Hj) as [Hx _]. fold x in Hx.
      rewrite (ms_word x) in Hms by lia.
      set (b0 := x mod 256) in *. set (b1 := (x / 256) mod 256) in *.
      set (b2 := (x / 256 / 256) mod 256) in *. set (b3 := (x / 256 / 256 / 256) mod 256) in *.
      assert (Hb0 : 0 <= b0 < 256) by (unfold b0; apply Z.mod_pos_bound; lia).
      assert (Hb1 : 0 <= b1 < 256) by (unfold b1; apply Z.mod_pos_bound; lia).
      assert (Hb2 : 0 <= b2 < 256) by (unfold b2; apply Z.mod_pos_bound; lia).
      assert (Hb3 : 0 <= b3 < 256) by (unfold b3; apply Z.mod_pos_bound; lia).
      pose proof IV as IV'. destruct IV as [AI' MS' FS' SX' ROC' SL1 SL2 SL3 SL4 SL5 SL6 SL7 SL8 STR GS LV DJ' CAPS JK EFF WIN WDEF WSM].
      destruct RG as [G2 G8 G9 G18 G19 G20 G21 G22 G3 G4 GS6].
      pose proof (WSM j Hj) as Wj. fold x in Wj. unfold fld in Wj.

      destruct (Z.eqb_spec b0 0) as [Hz0|Hnz0].
      {
        rewrite app_nil_r in Hms.
        eapply srz_msteps; [exact (ms_halt _ MS') | exact (ms_lazy _ MS') | | ].
        { norm_pc.
          stepb_ft F_66870 D_66870 ltac:(cmpz).
          ld_step F_66874 D_66874 (word_to_le_bytes 4 (Z_to_bv 64 x)) (Z_to_bv 64 x) ltac:(rdn_fix Wj) ltac:(apply lwu_val; lia).
          stepiv F_66878 D_66878 (Z_to_bv 64 b0) ltac:(gres; pin; imm_norm; rewrite v_andi_Z by lia; rewrite land_255 by lia; reflexivity).
          stepb_tk F_6687c D_6687c ltac:(rewrite Hz0; apply c_eq_refl).
          apply mst_refl. }
        lazymatch goal with |- srealizes _ (mkCfg (mkst _ ?pc _ _) _) _ =>
          replace pc with (Z_to_bv 64 0x66918) by (apply bv_eq; vm_compute; reflexivity) end.
        eapply (EXIT _ _ _ _ _ _ _ IV'); [exact Hms | gres; exact G2 | gres; exact G3 | gres; exact G4 |].
        intros r Hr. pose proof Hr as Hr'. repeat (destruct Hr as [<-|Hr]; [gres; apply GS6; exact Hr' |]). destruct Hr. }

      eapply srz_msteps; [exact (ms_halt _ MS') | exact (ms_lazy _ MS') | | ].
      { norm_pc.
        stepb_ft F_66870 D_66870 ltac:(cmpz).
          ld_step F_66874 D_66874 (word_to_le_bytes 4 (Z_to_bv 64 x)) (Z_to_bv 64 x) ltac:(rdn_fix Wj) ltac:(apply lwu_val; lia).
        stepiv F_66878 D_66878 (Z_to_bv 64 b0) ltac:(gres; pin; imm_norm; rewrite v_andi_Z by lia; rewrite land_255 by lia; reflexivity).
        stepb_ft F_6687c D_6687c ltac:(rewrite c_eq_Z' by lia; apply Z.eqb_neq; exact Hnz0).
        apply mst_refl. }
      lazymatch goal with |- srealizes _ (mkCfg (mkst _ ?pc _ _) _) _ =>
        replace pc with (Z_to_bv 64 0x668c0) by (apply bv_eq; vm_compute; reflexivity) end.
      eapply (CALL1 j (Z_to_bv 64 x) b0 _ _ _ _ _ _ _ IV');
        [ constructor; try (gres; first [reflexivity | assumption]);
          intros r Hr; pose proof Hr as Hr'; repeat (destruct Hr as [<-|Hr]; [gres; apply GS6; exact Hr'|]); destruct Hr
        | gres; reflexivity | lia | lia | ].
      clear AI' MS' FS' SX' ROC' SL1 SL2 SL3 SL4 SL5 SL6 SL7 SL8 STR GS LV DJ' CAPS JK EFF WIN WDEF WSM IV' G2 G8 G9 G18 G19 G20 G21 G22 G3 G4 GS6 Wj.
      clear A' R' M' model' m' J.
      intros A' R' M' model' m' J IV RG.
      pose proof IV as IV'. destruct IV as [AI' MS' FS' SX' ROC' SL1 SL2 SL3 SL4 SL5 SL6 SL7 SL8 STR GS LV DJ' CAPS JK EFF WIN WDEF WSM].
      destruct RG as [G2 G8 G9 G18 G19 G20 G21 G22 G3 G4 GS6].

      destruct (Z.eqb_spec b1 0) as [Hz1|Hnz1].
      { eapply srz_msteps; [exact (ms_halt _ MS') | exact (ms_lazy _ MS') | | ].
        { norm_pc.
          stepand F_66888 D_66888 (Z_to_bv 64 (256 * b1)) ltac:(gres; pin; rewrite v_and_Z by lia; rewrite land_ff00 by lia; reflexivity).
          stepb_tk F_6688c D_6688c ltac:(rewrite Hz1; apply c_eq_refl).
          apply mst_refl. }
        lazymatch goal with |- srealizes _ (mkCfg (mkst _ ?pc _ _) _) _ =>
          replace pc with (Z_to_bv 64 0x66918) by (apply bv_eq; vm_compute; reflexivity) end.
        eapply (EXIT _ _ _ _ _ _ _ IV'); [exact Hms | gres; exact G2 | gres; exact G3 | gres; exact G4 |].
        intros r Hr. pose proof Hr as Hr'. repeat (destruct Hr as [<-|Hr]; [gres; apply GS6; exact Hr' |]). destruct Hr. }
      eapply srz_msteps; [exact (ms_halt _ MS') | exact (ms_lazy _ MS') | | ].
      { norm_pc.
        stepand F_66888 D_66888 (Z_to_bv 64 (256 * b1)) ltac:(gres; pin; rewrite v_and_Z by lia; rewrite land_ff00 by lia; reflexivity).
        stepb_ft F_6688c D_6688c ltac:(rewrite c_eq_Z' by lia; apply Z.eqb_neq; lia).
        stepiv F_66890 D_66890 (Z_to_bv 64 ((x mod 2 ^ 16) * 2 ^ 48)) ltac:(gres; pin; imm_norm; rewrite v_slli_Z by lia; rewrite (shl_mod64 x 48) by lia; reflexivity).
        stepiv F_66894 D_66894 (Z_to_bv 64 b1)
          ltac:(gres; pin; imm_norm; pose proof (Z.mod_pos_bound x (2 ^ 16) ltac:(lia));
                rewrite v_srli_Z by (change (2 ^ 16) with 65536 in *; lia); f_equal; apply byte1_via_shifts; lia).
        apply mst_refl. }
      lazymatch goal with |- srealizes _ (mkCfg (mkst _ ?pc _ _) _) _ =>
        replace pc with (Z_to_bv 64 0x668d8) by (apply bv_eq; vm_compute; reflexivity) end.
      eapply (CALL2 j (Z_to_bv 64 x) b1 _ _ _ _ _ _ _ IV');
        [ constructor; try (gres; first [reflexivity | assumption]);
          intros r Hr; pose proof Hr as Hr'; repeat (destruct Hr as [<-|Hr]; [gres; apply GS6; exact Hr'|]); destruct Hr
        | gres; reflexivity | lia | rewrite Zlen_app1; lia | ].
      clear AI' MS' FS' SX' ROC' SL1 SL2 SL3 SL4 SL5 SL6 SL7 SL8 STR GS LV DJ' CAPS JK EFF WIN WDEF WSM IV' G2 G8 G9 G18 G19 G20 G21 G22 G3 G4 GS6.
      clear A' R' M' model' m' J.
      intros A' R' M' model' m' J IV RG. rewrite <- app_assoc in IV. cbn [app] in IV.
      pose proof IV as IV'. destruct IV as [AI' MS' FS' SX' ROC' SL1 SL2 SL3 SL4 SL5 SL6 SL7 SL8 STR GS LV DJ' CAPS JK EFF WIN WDEF WSM].
      destruct RG as [G2 G8 G9 G18 G19 G20 G21 G22 G3 G4 GS6].

      destruct (Z.eqb_spec b2 0) as [Hz2|Hnz2].
      { eapply srz_msteps; [exact (ms_halt _ MS') | exact (ms_lazy _ MS') | | ].
        { norm_pc.
          stepand F_668a0 D_668a0 (Z_to_bv 64 (65536 * b2)) ltac:(gres; pin; rewrite v_and_Z by lia; rewrite land_ff0000 by lia; reflexivity).
          stepb_tk F_668a4 D_668a4 ltac:(rewrite Hz2; apply c_eq_refl).
          apply mst_refl. }
        lazymatch goal with |- srealizes _ (mkCfg (mkst _ ?pc _ _) _) _ =>
          replace pc with (Z_to_bv 64 0x66918) by (apply bv_eq; vm_compute; reflexivity) end.
        eapply (EXIT _ _ _ _ _ _ _ IV'); [exact Hms | gres; exact G2 | gres; exact G3 | gres; exact G4 |].
        intros r Hr. pose proof Hr as Hr'. repeat (destruct Hr as [<-|Hr]; [gres; apply GS6; exact Hr' |]). destruct Hr. }
      eapply srz_msteps; [exact (ms_halt _ MS') | exact (ms_lazy _ MS') | | ].
      { norm_pc.
        stepand F_668a0 D_668a0 (Z_to_bv 64 (65536 * b2)) ltac:(gres; pin; rewrite v_and_Z by lia; rewrite land_ff0000 by lia; reflexivity).
        stepb_ft F_668a4 D_668a4 ltac:(rewrite c_eq_Z' by lia; apply Z.eqb_neq; lia).
        stepiv F_668a8 D_668a8 (Z_to_bv 64 ((x mod 2 ^ 24) * 2 ^ 40)) ltac:(gres; pin; imm_norm; rewrite v_slli_Z by lia; rewrite (shl_mod64 x 40) by lia; reflexivity).
        stepiv F_668ac D_668ac (Z_to_bv 64 b2)
          ltac:(gres; pin; imm_norm; pose proof (Z.mod_pos_bound x (2 ^ 24) ltac:(lia));
                rewrite v_srli_Z by (change (2 ^ 24) with 16777216 in *; lia); f_equal; apply byte2_via_shifts; lia).
        apply mst_refl. }
      lazymatch goal with |- srealizes _ (mkCfg (mkst _ ?pc _ _) _) _ =>
        replace pc with (Z_to_bv 64 0x668f0) by (apply bv_eq; vm_compute; reflexivity) end.
      eapply (CALL3 j (Z_to_bv 64 x) b2 _ _ _ _ _ _ _ IV');
        [ constructor; try (gres; first [reflexivity | assumption]);
          intros r Hr; pose proof Hr as Hr'; repeat (destruct Hr as [<-|Hr]; [gres; apply GS6; exact Hr'|]); destruct Hr
        | gres; reflexivity | lia | replace (Zlen (cs' ++ [b0; b1])) with (Zlen cs' + 2) by (rewrite Zlen_app; reflexivity); lia | ].
      clear AI' MS' FS' SX' ROC' SL1 SL2 SL3 SL4 SL5 SL6 SL7 SL8 STR GS LV DJ' CAPS JK EFF WIN WDEF WSM IV' G2 G8 G9 G18 G19 G20 G21 G22 G3 G4 GS6.
      clear A' R' M' model' m' J.
      intros A' R' M' model' m' J IV RG. rewrite <- app_assoc in IV. cbn [app] in IV.
      pose proof IV as IV'. destruct IV as [AI' MS' FS' SX' ROC' SL1 SL2 SL3 SL4 SL5 SL6 SL7 SL8 STR GS LV DJ' CAPS JK EFF WIN WDEF WSM].
      destruct RG as [G2 G8 G9 G18 G19 G20 G21 G22 G3 G4 GS6].

      destruct (Z.eqb_spec b3 0) as [Hz3|Hnz3].
      { eapply srz_msteps; [exact (ms_halt _ MS') | exact (ms_lazy _ MS') | | ].
        { norm_pc.
          stepiv F_668b8 D_668b8 (Z_to_bv 64 b3) ltac:(gres; pin; imm_norm; rewrite v_srli_Z by lia; f_equal; apply byte3_val; lia).
          stepb_tk F_668bc D_668bc ltac:(rewrite Hz3; apply c_eq_refl).
          apply mst_refl. }
        lazymatch goal with |- srealizes _ (mkCfg (mkst _ ?pc _ _) _) _ =>
          replace pc with (Z_to_bv 64 0x66918) by (apply bv_eq; vm_compute; reflexivity) end.
        eapply (EXIT _ _ _ _ _ _ _ IV'); [exact Hms | gres; exact G2 | gres; exact G3 | gres; exact G4 |].
        intros r Hr. pose proof Hr as Hr'. repeat (destruct Hr as [<-|Hr]; [gres; apply GS6; exact Hr' |]). destruct Hr. }
      eapply srz_msteps; [exact (ms_halt _ MS') | exact (ms_lazy _ MS') | | ].
      { norm_pc.
        stepiv F_668b8 D_668b8 (Z_to_bv 64 b3) ltac:(gres; pin; imm_norm; rewrite v_srli_Z by lia; f_equal; apply byte3_val; lia).
        stepb_ft F_668bc D_668bc ltac:(rewrite c_eq_Z' by lia; apply Z.eqb_neq; lia).
        apply mst_refl. }
      lazymatch goal with |- srealizes _ (mkCfg (mkst _ ?pc _ _) _) _ =>
        replace pc with (Z_to_bv 64 0x66900) by (apply bv_eq; vm_compute; reflexivity) end.
      eapply (CALL4 j (Z_to_bv 64 x) b3 _ _ _ _ _ _ _ IV');
        [ constructor; try (gres; first [reflexivity | assumption]);
          intros r Hr; pose proof Hr as Hr'; repeat (destruct Hr as [<-|Hr]; [gres; apply GS6; exact Hr'|]); destruct Hr
        | gres; reflexivity | lia | replace (Zlen (cs' ++ [b0; b1; b2])) with (Zlen cs' + 3) by (rewrite Zlen_app; reflexivity); lia | ].
      clear AI' MS' FS' SX' ROC' SL1 SL2 SL3 SL4 SL5 SL6 SL7 SL8 STR GS LV DJ' CAPS JK EFF WIN WDEF WSM IV' G2 G8 G9 G18 G19 G20 G21 G22 G3 G4 GS6.
      clear A' R' M' model' m' J.
      intros A' R' M' model' m' J IV RG. rewrite <- app_assoc in IV. cbn [app] in IV.
      pose proof IV as IV'. destruct IV as [AI' MS' FS' SX' ROC' SL1 SL2 SL3 SL4 SL5 SL6 SL7 SL8 STR GS LV DJ' CAPS JK EFF WIN WDEF WSM].
      destruct RG as [G2 G8 G9 G18 G19 G20 G21 G22 G3 G4 GS6].

      destruct (Z.lt_ge_cases (j + 1) nw) as [Hmore|Hlast].
      { eapply srz_msteps; [exact (ms_halt _ MS') | exact (ms_lazy _ MS') | | ].
        { norm_pc.
          stepb_ft F_668c8 D_668c8 ltac:(cmpz).
          stepiv F_668cc D_668cc (Z_to_bv 64 (4 * (nw - (j + 1)))) ltac:(gres; pin; imm_norm; rewrite v_addi_Z by lia; f_equal; lia).
          stepiv F_668d0 D_668d0 (Z_to_bv 64 (w + 4 * (j + 1))) ltac:(gres; pin; imm_norm; rewrite v_addi_Z by lia; f_equal; lia).
          stepb_tk F_668d4 D_668d4 ltac:(rewrite c_eq_Z' by lia; apply Z.eqb_neq; lia).
          apply mst_refl. }
        lazymatch goal with |- srealizes _ (mkCfg (mkst _ ?pc _ _) _) _ =>
          replace pc with (Z_to_bv 64 0x668b0) by (apply bv_eq; vm_compute; reflexivity) end.
        eapply (IH Hmore _ _ _ _ _ _ _ (Z_to_bv 64 x) IV');
          [ constructor; try (gres; first [reflexivity | assumption]);
            intros r Hr; pose proof Hr as Hr'; repeat (destruct Hr as [<-|Hr]; [gres; apply GS6; exact Hr'|]); destruct Hr
          | replace (Zlen (cs' ++ [b0; b1; b2; b3])) with (Zlen cs' + 4) by (rewrite Zlen_app; reflexivity); lia
          | rewrite Hms, <- !app_assoc; reflexivity ]. }
      eapply srz_msteps; [exact (ms_halt _ MS') | exact (ms_lazy _ MS') | | ].
      { norm_pc.
        stepb_ft F_668c8 D_668c8 ltac:(cmpz).
        stepiv F_668cc D_668cc (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite v_addi_Z by lia; f_equal; lia).
        stepiv F_668d0 D_668d0 (Z_to_bv 64 (w + 4 * (j + 1))) ltac:(gres; pin; imm_norm; rewrite v_addi_Z by lia; f_equal; lia).
        stepb_ft F_668d4 D_668d4 ltac:(apply c_eq_refl).
        apply mst_refl. }
      lazymatch goal with |- srealizes _ (mkCfg (mkst _ ?pc _ _) _) _ =>
        replace pc with (Z_to_bv 64 0x66918) by (apply bv_eq; vm_compute; reflexivity) end.
      eapply (EXIT _ _ _ _ _ _ _ IV'); [ | gres; exact G2 | gres; exact G3 | gres; exact G4 |].
      { rewrite Hms. replace (j + 1) with (Zlen ws) by lia. rewrite skipn_all_Z. cbn [ms_chars]. rewrite ?app_nil_r, <- ?app_assoc. reflexivity. }
      intros r Hr. pose proof Hr as Hr'. repeat (destruct Hr as [<-|Hr]; [gres; apply GS6; exact Hr' |]). destruct Hr.
    Qed.
    Lemma LOOP : forall (k : nat) j, 0 <= j < nw -> nw - j <= Z.of_nat k ->
      forall A' R' M' model' m' cs' J x, INV A' M' model' m' cs' J -> REGS R' j x -> Zlen cs' <= 4 * j ->
        ms_chars ws = cs' ++ ms_chars (skipn (Z.to_nat j) ws) ->
        srealizes SEGS (mkCfg (@mkst fx R' (Z_to_bv 64 0x668b0) M' (seg_rom SEGS)) model') K.
    Proof using AC MI ST MALLOC_STACK_pos NEW fx A s R M model sp ret p w nw ws K CB Hp0 Hp1 OBJp Hnw0 Hws Hw0 Hw1 WS OBJw DJ HNMAX ROOM CONT.
      induction k as [|k IHk]; intros j Hj Hk; [lia|].
      apply WORD; [exact Hj|]. intros Hmore. apply IHk; lia.
    Qed.

    Lemma w8_zero : word_to_le_bytes 8 (Z_to_bv 64 0) = repeat (Z_to_bv 8 0) 8.
    Proof using. reflexivity. Qed.

    Lemma Ppos : 0 < p.
    Proof using AC MI ST A s R M model sp ret p w CB OBJp Hw0.
      dCB. destruct OBJp as [PL _]. pose proof ac_bounds_lit.
      destruct PL as [Hst|(q & k & Hin & Hq & Hqk)]; [lia|].
      destruct (ai_live_block MI A M model q k AI Hin) as (_ & _ & Hq0 & _). lia.
    Qed.

    Definition PRO : list word := [getr R 22%bv; getr R 21%bv; getr R 20%bv; getr R 19%bv; getr R 18%bv; getr R 9%bv; getr R 8%bv; Z_to_bv 64 ret].

    Lemma PRE : forall (a3v a4v : Z),
      v_sltu (Z_to_bv 64 0) (Z_to_bv 64 w) = Z_to_bv 64 a3v -> v_sltiu (Z_to_bv 64 (w + 4 * nw)) 1 = Z_to_bv 64 a4v ->
      0 <= a3v <= 1 -> 0 <= a4v <= 1 -> a3v <> a4v -> nw < 2 ^ 40 ->
      store_ok SEGS M (Z_to_bv 64 (sp - 64)) 64 = true -> (p + 24 <= sp - STK \/ sp <= p) ->
      exists R1,
        msteps SEGS (@mkst fx R (Z_to_bv 64 0x6682c) M (seg_rom SEGS))
                    (@mkst fx R1 (Z_to_bv 64 0x66894)
                       (wbytes (wbytes (wbytes (wslots M sp PRO) (Z_to_bv 64 p) (word_to_le_bytes 8 (Z_to_bv 64 0)))
                                (Z_to_bv 64 (p + 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
                         (Z_to_bv 64 (p + 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (seg_rom SEGS))
        /\ getr R1 2%bv = Z_to_bv 64 (sp - 64) /\ getr R1 8%bv = Z_to_bv 64 w /\ getr R1 9%bv = Z_to_bv 64 p /\ getr R1 18%bv = Z_to_bv 64 (4 * nw)
        /\ getr R1 12%bv = Z_to_bv 64 nw /\ getr R1 3%bv = getr R 3%bv /\ getr R1 4%bv = getr R 4%bv
        /\ (forall r, In r [19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr R1 r = getr R r).
    Proof using AC MI ST MALLOC_STACK_pos fx A s R M model sp ret p w nw ws CB Ha0 Ha1 Ha2 Hp0 Hp1 HDp OBJp Hnw0 Hws Hw0 Hw1.
      intros a3v a4v H3 H4 Ha3 Ha4 Hne Hnw HOK WP.
      pose proof Hspr as (Hc & Hs47 & Hs16 & Hs20 & HMS & HSTK). pose proof Ppos as Hpp.
      dCB. destruct CR as [Hra Hret Hretr Hsp Hsp16 Hsphi Hgp Htp].
      assert (HDp1 : mdef (wslots M sp PRO) p 24).
      { eapply stores_in_mdef; [| exact HDp]. eapply stores_in_weaken; [apply wslots_stores_in; unfold PRO, Zlen; cbn; lia|]. intros a Ha; exact I. }
      eexists. split.
      - norm_pc.
        sv F_667ec D_667ec (Z_to_bv 64 (sp - 64)).
        stw F_667f0 D_667f0 (Z_to_bv 64 (sp - 8)) (Z_to_bv 64 ret) ltac:(ok_sub HOK).
        stw F_667f4 D_667f4 (Z_to_bv 64 (sp - 16)) (getr R 8%bv) ltac:(ok_sub HOK).
        stw F_667f8 D_667f8 (Z_to_bv 64 (sp - 24)) (getr R 9%bv) ltac:(ok_sub HOK).
        stw F_667fc D_667fc (Z_to_bv 64 (sp - 32)) (getr R 18%bv) ltac:(ok_sub HOK).
        stw F_66800 D_66800 (Z_to_bv 64 (sp - 40)) (getr R 19%bv) ltac:(ok_sub HOK).
        stw F_66804 D_66804 (Z_to_bv 64 (sp - 48)) (getr R 20%bv) ltac:(ok_sub HOK).
        stw F_66808 D_66808 (Z_to_bv 64 (sp - 56)) (getr R 21%bv) ltac:(ok_sub HOK).
        stw F_6680c D_6680c (Z_to_bv 64 (sp - 64)) (getr R 22%bv) ltac:(ok_sub HOK).
        sv F_66810 D_66810 (Z_to_bv 64 w).
        stepiv F_66814 D_66814 (Z_to_bv 64 (4 * nw)) ltac:(gres; pin; imm_norm; rewrite v_slli_Z by lia; f_equal; change (2 ^ 2) with 4; lia).
        stepiv F_66818 D_66818 (Z_to_bv 64 (w + 4 * nw)) ltac:(gres; pin; rewrite v_add_Z by lia; f_equal; lia).
        steprr (@step_sltu_at fx) F_6681c D_6681c (Z_to_bv 64 a3v) ltac:(gres; pin; rewrite ?getr_zero; exact H3).
        stepiv F_66820 D_66820 (Z_to_bv 64 a4v) ltac:(gres; pin; imm_norm; exact H4).
        stepb_ft F_66824 D_66824 ltac:(cmpz).
        sv F_66828 D_66828 (Z_to_bv 64 p).
        stepiv F_6682c D_6682c (Z_to_bv 64 1) ltac:(gres; pin; imm_norm; reflexivity).
        stepiv F_66830 D_66830 (Z_to_bv 64 (2 ^ 61)) ltac:(gres; pin; imm_norm; apply bv_eq; vm_compute; reflexivity).
        stepiv F_66834 D_66834 (Z_to_bv 64 (nw + 2 ^ 61)) ltac:(gres; pin; rewrite v_add_Z by lia; reflexivity).
        stepiv F_66838 D_66838 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite v_srli_Z by lia; f_equal; rewrite Z.div_small by lia; reflexivity).
        stepb_ft F_6683c D_6683c ltac:(apply c_eq_refl).
        stepb_ft F_66840 D_66840 ltac:(cmpz).
        stepb_ft F_66844 D_66844 ltac:(cmpz).
        stw F_66848 D_66848 (Z_to_bv 64 p) (Z_to_bv 64 0) ltac:(store_ok_peel; ok_mdef HDp).
        stw F_6684c D_6684c (Z_to_bv 64 (p + 8)) (Z_to_bv 64 0) ltac:(store_ok_peel; ok_mdef HDp).
        stw F_66850 D_66850 (Z_to_bv 64 (p + 16)) (Z_to_bv 64 0) ltac:(store_ok_peel; ok_mdef HDp).
        unfold PRO. cbn [wslots Zlen length Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Pos.mul].
        lazymatch goal with |- msteps _ ?a ?bb => replace bb with a; [apply mst_refl|] end.
        repeat first [reflexivity | lia | apply bv_eq; vm_compute; reflexivity | progress f_equal].
      - gres. repeat split; first [reflexivity | assumption | f_equal; lia | intros r Hr; repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]); destruct Hr].
    Qed.

    Lemma ENTRY : srealizes SEGS (mkCfg (@mkst fx R (Z_to_bv 64 0x6682c) M (seg_rom SEGS)) model) K.
    Proof using AC MI ST MALLOC_STACK_pos NEW fx A s R M model sp ret p w nw ws K CB Ha0 Ha1 Ha2 Hp0 Hp1 HDp OBJp Hnw0 Hws Hw0 Hw1 Hw4 WS OBJw DJ HNMAX ROOM CONT.
      pose proof Hspr as (Hc & Hs47 & Hs16 & Hs20 & HMS & HSTK). pose proof ac_bounds_lit as Hcv.
      pose proof WINp as WP. pose proof WINw as WW. pose proof WDEF0 as WD0. pose proof Ppos as Hpp.
      pose proof CB as CB'. destruct CB' as [AI MS ROC SXI SXH CR Hceil HROOM Hwin Hown_sx Herr_sx].
      destruct CR as [Hra Hret Hretr Hsp Hsp16 Hsphi Hgp Htp].
      pose proof (ai_nmax_bound MI) as HNM. assert (Hnw40 : nw < 2 ^ 40) by lia.
      assert (HDR : forall a, p <= a < p + 24 -> ~ owned MI A a /\ ~ in_ranges (ly_img Ly.L) a).
      { intros a Ha. exact (placed_sep A M model p 24 a AI (proj1 OBJp) Ha). }
      assert (WIN : forall a, sp - STK <= a < sp -> ~ owned MI A a /\ ~ in_ranges (ly_img Ly.L) a).
      { intros a Ha. apply (stack_sep A M model a AI). lia. }
      assert (HDW : mdef M (sp - STK) STK).
      { pose proof HROOM as HOK. unfold stack_room in HOK.
        eapply store_ok_mdef_offimg; [exact HOK | lia | lia | lia |]. intros x Hx. apply ly_noseg. lia. }
      pose proof HROOM as HOK. unfold stack_room in HOK.

      assert (FL : exists a3v a4v, v_sltu (Z_to_bv 64 0) (Z_to_bv 64 w) = Z_to_bv 64 a3v /\ v_sltiu (Z_to_bv 64 (w + 4 * nw)) 1 = Z_to_bv 64 a4v
                                /\ 0 <= a3v <= 1 /\ 0 <= a4v <= 1 /\ a3v <> a4v).
      { destruct (Z.eq_dec w 0) as [Hw0z|Hwnz].
        - assert (Hn0 : nw = 0) by (destruct (Z.eq_dec nw 0); [assumption|]; pose proof (Wpos ltac:(lia)); lia).
          exists 0, 1. rewrite Hw0z, Hn0. split; [reflexivity|]. split; [rewrite sltiu_1_Z by lia; reflexivity|]. lia.
        - exists 1, 0. split; [apply snez_Z; lia|]. split; [rewrite sltiu_1_Z by lia; destruct (Z.eqb_spec (w + 4 * nw) 0); [lia|reflexivity]|]. lia. }
      destruct FL as (a3v & a4v & H3 & H4 & Ha3 & Ha4 & Hne).
      destruct (PRE a3v a4v H3 H4 Ha3 Ha4 Hne Hnw40 ltac:(unfold STK in HOK; ok_sub HOK) WP) as (R1 & RUN1 & R1_2 & R1_8 & R1_9 & R1_18 & R1_12 & R1_3 & R1_4 & R1S).
      set (M1 := wslots M sp PRO) in *.
      set (M0 := wbytes (wbytes (wbytes M1 (Z_to_bv 64 p) (word_to_le_bytes 8 (Z_to_bv 64 0)))
                                (Z_to_bv 64 (p + 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
                         (Z_to_bv 64 (p + 16)) (word_to_le_bytes 8 (Z_to_bv 64 0))) in *.
      assert (ST01 : stores_in (zwin (sp - 64) sp) M M1).
      { unfold M1. eapply stores_in_weaken; [apply wslots_stores_in; unfold PRO, Zlen; cbn; lia|].
        intros a Ha. unfold zwin, PRO, Zlen in *. cbn in *. lia. }
      assert (ST0 : stores_in (zwin p (p + 24)) M1 M0).
      { unfold M0. eapply stores_in_wbytes_more; [eapply stores_in_wbytes_more; [apply stores_in_wbytes | | |] | | |];
          rewrite ?length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; try lia; intros a Ha; unfold zwin in *; lia. }
      assert (ST1 : stores_in (fun a => zwin p (p + 24) a \/ zwin (sp - 64) sp a) M M0).
      { eapply stores_in_trans; [eapply stores_in_weaken; [exact ST01|]; intros a Ha; right; exact Ha |].
        eapply stores_in_weaken; [exact ST0|]. intros a Ha; left; exact Ha. }
      assert (Z0 : forall d, 0 <= d < 8 -> rdn SEGS M0 (Z_to_bv 64 (p + d)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 0))).
      { intros d Hd. unfold M0. rewrite 2!rdn_wbytes_out_Z by (rewrite length_N_to_le_bytes; cbn; lia).
        rewrite w8_zero. change (word_to_le_bytes 1 (Z_to_bv 64 0)) with (repeat (Z_to_bv 8 0) 1).
        apply rdn_zeros_sub; cbn; lia. }
      assert (SL : forall k, 1 <= k <= 8 ->
                rdn SEGS M0 (Z_to_bv 64 (sp - 8 * k)) 8 = Some (word_to_le_bytes 8 (nth (Z.to_nat (8 - k)) PRO (Z_to_bv 64 0)))).
      { intros k Hk. unfold M0. unfold STK in WP. rewrite 3!rdn_wbytes_out_Z by (rewrite length_N_to_le_bytes; cbn; lia).
        unfold M1. apply wslots_read; unfold PRO, Zlen; cbn; lia. }
      assert (IV0 : INV A M0 model SShort [] (fun _ => False)).
      { constructor.
        * eapply (stores_in_ainv SEGS Ly.L MI); [exact AI | exact ST1 |].
          intros a [Ha|Ha]; [apply HDR | apply WIN]; unfold zwin, STK in *; lia.
        * exact MS.
        * split; reflexivity.
        * eapply (stores_in_sx SEGS Ly.L ST); [exact SXI | exact ST1 |].
          intros a Ha. assert (Hni : ~ in_ranges (ly_img Ly.L) a) by (destruct Ha as [Ha|Ha]; [apply HDR | apply WIN]; unfold zwin, STK in *; lia).
          destruct (offimg_sep a Hni) as (X1 & X2 & _). split; assumption.
        * eapply (roc_stores Ly.L); [exact ROC | exact ST1 |].
          intros a [Ha|Ha]; [apply HDR | apply WIN]; unfold zwin, STK in *; lia.
        * apply (SL 1); lia.
        * apply (SL 2); lia.
        * apply (SL 3); lia.
        * apply (SL 4); lia.
        * apply (SL 5); lia.
        * apply (SL 6); lia.
        * apply (SL 7); lia.
        * apply (SL 8); lia.
        * apply (str_nil MI); [lia | lia | eapply stores_in_mdef; [exact ST1 | exact HDp] | |].
          -- unfold fld. replace p with (p + 0) by lia. apply Z0. lia.
          -- unfold fld. apply Z0. lia.
        * left; reflexivity.
        * intros q k. cbn [str_blocks In]. tauto.
        * intros q k [].
        * split; reflexivity.
        * intros a [].
        * apply eff_store; [| exact (proj2 ST1)].
          intros a HF HW. apply (proj1 ST1). intros [Hz|Hz]; [apply HF; left; exact Hz | apply HW; unfold W_of, Wn, zwin, STK in *; cbn; lia].
        * eapply stores_in_mdef; [exact ST1 | exact HDW].
        * eapply stores_in_mdef; [exact ST1 | exact WD0].
        * intros i Hi. destruct (WS i Hi) as [_ HF]. eapply fld_agree; [lia | cbn; lia | exact HF |].
          eapply stores_in_agree; [exact ST1|]. intros a Ha. unfold zwin in Ha. cbn in Ha. split; [lia|]. intros [Hz|Hz].
          -- exact (DJ a ltac:(unfold zwin; lia) Hz).
          -- unfold zwin, STK in *. lia. }
      eapply srz_msteps; [exact (ms_halt _ MS) | exact (ms_lazy _ MS) | exact RUN1 | ].
      destruct (Z.eq_dec nw 0) as [Hnw|Hnw].
      -
        assert (Hws0 : ws = []) by (destruct ws; [reflexivity | unfold Zlen in Hws; cbn in Hws; lia]).
        eapply srz_msteps; [exact (ms_halt _ MS) | exact (ms_lazy _ MS) | | ].
        { norm_pc. stepb_tk F_66854 D_66854 ltac:(rewrite R1_12, Hnw; apply c_eq_refl). apply mst_refl. }
        lazymatch goal with |- srealizes _ (mkCfg (mkst _ ?pc _ _) _) _ =>
          replace pc with (Z_to_bv 64 0x66918) by (apply bv_eq; vm_compute; reflexivity) end.
        eapply (EXIT _ _ _ _ _ _ _ IV0); [rewrite Hws0; reflexivity | exact R1_2 | exact R1_3 | exact R1_4 |].
        intros r Hr. apply R1S. revert Hr. clear. intros Hr. cbn in Hr |- *. tauto.
      -
        assert (Hw40 : Z.land w 3 = 0) by (change 3 with (2 ^ 2 - 1); rewrite land_ones_mod by lia; change (2 ^ 2) with 4; exact Hw4).
        assert (RUN2 : exists R2, msteps SEGS (@mkst fx R1 (Z_to_bv 64 0x66894) M0 (seg_rom SEGS)) (@mkst fx R2 (Z_to_bv 64 0x668b0) M0 (seg_rom SEGS))
                 /\ REGS R2 0 (getr R 22%bv)).
        { eexists. split.
          - norm_pc.
            stepb_ft F_66854 D_66854 ltac:(cmpz).
            stepiv F_66858 D_66858 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite v_andi_Z by lia; f_equal; exact Hw40).
            stepb_ft F_6685c D_6685c ltac:(apply c_eq_refl).
            stepiv F_66860 D_66860 (Z_to_bv 64 0x10000) ltac:(gres; pin; imm_norm; apply bv_eq; vm_compute; reflexivity).
            stepiv F_66864 D_66864 (Z_to_bv 64 0xff0000) ltac:(gres; pin; imm_norm; apply bv_eq; vm_compute; reflexivity).
            stepiv F_66868 D_66868 (Z_to_bv 64 0xff00) ltac:(gres; pin; imm_norm; apply bv_eq; vm_compute; reflexivity).
            stepiv F_6686c D_6686c (Z_to_bv 64 (2 ^ 64 - 4)) ltac:(gres; pin; imm_norm; apply bv_eq; vm_compute; reflexivity).
            close_pc.
          - constructor; try (intros r Hr; pose proof Hr as Hr'; repeat (destruct Hr as [<-|Hr]; [gres; apply R1S; revert Hr'; clear; intros Hr'; cbn in Hr' |- *; tauto|]); destruct Hr);
              gres; try reflexivity; try assumption; try (rewrite R1_8; f_equal; lia); try (rewrite R1_18; f_equal; lia); try (apply R1S; (first [solve [clear; cbn; tauto] | cbn; tauto])). }
        destruct RUN2 as (R2 & RUN2 & RG2).
        eapply srz_msteps; [exact (ms_halt _ MS) | exact (ms_lazy _ MS) | exact RUN2 | ].
        apply (LOOP (Z.to_nat nw) 0 ltac:(lia) ltac:(lia) A R2 M0 model SShort [] (fun _ => False) (getr R 22%bv) IV0 RG2).
        + change (Zlen (@nil Z)) with 0. lia.
        + reflexivity.
    Qed.
  End Body.

  Theorem makestring_66788_spec : makestringU_stmt SEGS Ly.L MI ST c8d144.
  Proof using AC MI ST MALLOC_STACK_pos NEW.
    intros fx A s R M model sp ret p w nw ws K. cbn [sc_makestring sc_ms_stack c8d144]. lazy zeta. unfold NEW_STACK.
    intros CB Ha0 Ha1 Ha2 Hp0 Hp1 HDp OBJp Hnw Hws Hw0 Hw1 Hw4 WS OBJw DJ HNMAX ROOM CONT.
    eapply (ENTRY fx A s R M model sp ret p w nw ws K); try eassumption.
  Qed.
End MakeString.
