(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Plain.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StepTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.WalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StartupTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SumWalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MemSplit OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ShapeAlg OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SRealizes OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefReadLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibEff OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MmapSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SumMemcpyBase OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SumMemcpy OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.S1Layout.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.CRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.S1Facts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.Lib_Cxx_OperatorDelete.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Module S1_code_6b95c_6ba90.

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_6b95c : bv 32 := 0xfc010113.
Lemma F_6b95c : fetch_word Plain.M.loaded_segments (0x6b99c : word) = Some W_6b95c.
Proof. vm_refl. Qed.
Lemma D_6b95c : decode_any W_6b95c = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b960 : bv 32 := 0x02113c23.
Lemma F_6b960 : fetch_word Plain.M.loaded_segments (0x6b9a0 : word) = Some W_6b960.
Proof. vm_refl. Qed.
Lemma D_6b960 : decode_any W_6b960 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b964 : bv 32 := 0x02813823.
Lemma F_6b964 : fetch_word Plain.M.loaded_segments (0x6b9a4 : word) = Some W_6b964.
Proof. vm_refl. Qed.
Lemma D_6b964 : decode_any W_6b964 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b968 : bv 32 := 0x02913423.
Lemma F_6b968 : fetch_word Plain.M.loaded_segments (0x6b9a8 : word) = Some W_6b968.
Proof. vm_refl. Qed.
Lemma D_6b968 : decode_any W_6b968 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b96c : bv 32 := 0x03213023.
Lemma F_6b96c : fetch_word Plain.M.loaded_segments (0x6b9ac : word) = Some W_6b96c.
Proof. vm_refl. Qed.
Lemma D_6b96c : decode_any W_6b96c = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b970 : bv 32 := 0x01313c23.
Lemma F_6b970 : fetch_word Plain.M.loaded_segments (0x6b9b0 : word) = Some W_6b970.
Proof. vm_refl. Qed.
Lemma D_6b970 : decode_any W_6b970 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b974 : bv 32 := 0x01413823.
Lemma F_6b974 : fetch_word Plain.M.loaded_segments (0x6b9b4 : word) = Some W_6b974.
Proof. vm_refl. Qed.
Lemma D_6b974 : decode_any W_6b974 = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b978 : bv 32 := 0x01513423.
Lemma F_6b978 : fetch_word Plain.M.loaded_segments (0x6b9b8 : word) = Some W_6b978.
Proof. vm_refl. Qed.
Lemma D_6b978 : decode_any W_6b978 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b97c : bv 32 := 0x01613023.
Lemma F_6b97c : fetch_word Plain.M.loaded_segments (0x6b9bc : word) = Some W_6b97c.
Proof. vm_refl. Qed.
Lemma D_6b97c : decode_any W_6b97c = Some (Store SZ8 2 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b980 : bv 32 := 0x00050413.
Lemma F_6b980 : fetch_word Plain.M.loaded_segments (0x6b9c0 : word) = Some W_6b980.
Proof. vm_refl. Qed.
Lemma D_6b980 : decode_any W_6b980 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b984 : bv 32 := 0x00853a83.
Lemma F_6b984 : fetch_word Plain.M.loaded_segments (0x6b9c4 : word) = Some W_6b984.
Proof. vm_refl. Qed.
Lemma D_6b984 : decode_any W_6b984 = Some (Load SZ8 true 21 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b988 : bv 32 := 0x01053503.
Lemma F_6b988 : fetch_word Plain.M.loaded_segments (0x6b9c8 : word) = Some W_6b988.
Proof. vm_refl. Qed.
Lemma D_6b988 : decode_any W_6b988 = Some (Load SZ8 true 10 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b98c : bv 32 := 0x00aafa63.
Lemma F_6b98c : fetch_word Plain.M.loaded_segments (0x6b9cc : word) = Some W_6b98c.
Proof. vm_refl. Qed.
Lemma D_6b98c : decode_any W_6b98c = Some (Branch BC_GEU 21 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b990 : bv 32 := 0x0005a503.
Lemma F_6b990 : fetch_word Plain.M.loaded_segments (0x6b9d0 : word) = Some W_6b990.
Proof. vm_refl. Qed.
Lemma D_6b990 : decode_any W_6b990 = Some (Load SZ4 true 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b994 : bv 32 := 0x00aaa023.
Lemma F_6b994 : fetch_word Plain.M.loaded_segments (0x6b9d4 : word) = Some W_6b994.
Proof. vm_refl. Qed.
Lemma D_6b994 : decode_any W_6b994 = Some (Store SZ4 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b998 : bv 32 := 0x004a8a93.
Lemma F_6b998 : fetch_word Plain.M.loaded_segments (0x6b9d8 : word) = Some W_6b998.
Proof. vm_refl. Qed.
Lemma D_6b998 : decode_any W_6b998 = Some (OpImm ALU_ADD 21 21 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b99c : bv 32 := 0x0c00006f.
Lemma F_6b99c : fetch_word Plain.M.loaded_segments (0x6b9dc : word) = Some W_6b99c.
Proof. vm_refl. Qed.
Lemma D_6b99c : decode_any W_6b99c = Some (Jal 0 192, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b9a0 : bv 32 := 0x00043483.
Lemma F_6b9a0 : fetch_word Plain.M.loaded_segments (0x6b9e0 : word) = Some W_6b9a0.
Proof. vm_refl. Qed.
Lemma D_6b9a0 : decode_any W_6b9a0 = Some (Load SZ8 true 9 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b9a4 : bv 32 := 0x409a89b3.
Lemma F_6b9a4 : fetch_word Plain.M.loaded_segments (0x6b9e4 : word) = Some W_6b9a4.
Proof. vm_refl. Qed.
Lemma D_6b9a4 : decode_any W_6b9a4 = Some (Op ALU_SUB 19 21 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b9a8 : bv 32 := 0x4029da93.
Lemma F_6b9a8 : fetch_word Plain.M.loaded_segments (0x6b9e8 : word) = Some W_6b9a8.
Proof. vm_refl. Qed.
Lemma D_6b9a8 : decode_any W_6b9a8 = Some (ShiftImm ALU_SRA 21 19 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b9ac : bv 32 := 0x001a8613.
Lemma F_6b9ac : fetch_word Plain.M.loaded_segments (0x6b9ec : word) = Some W_6b9ac.
Proof. vm_refl. Qed.
Lemma D_6b9ac : decode_any W_6b9ac = Some (OpImm ALU_ADD 12 21 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b9b0 : bv 32 := 0x03e65693.
Lemma F_6b9b0 : fetch_word Plain.M.loaded_segments (0x6b9f0 : word) = Some W_6b9b0.
Proof. vm_refl. Qed.
Lemma D_6b9b0 : decode_any W_6b9b0 = Some (ShiftImm ALU_SRL 13 12 62, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b9b4 : bv 32 := 0x0c069a63.
Lemma F_6b9b4 : fetch_word Plain.M.loaded_segments (0x6b9f4 : word) = Some W_6b9b4.
Proof. vm_refl. Qed.
Lemma D_6b9b4 : decode_any W_6b9b4 = Some (Branch BC_NE 13 0 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b9b8 : bv 32 := 0x40950933.
Lemma F_6b9b8 : fetch_word Plain.M.loaded_segments (0x6b9f8 : word) = Some W_6b9b8.
Proof. vm_refl. Qed.
Lemma D_6b9b8 : decode_any W_6b9b8 = Some (Op ALU_SUB 18 10 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b9bc : bv 32 := 0x40195513.
Lemma F_6b9bc : fetch_word Plain.M.loaded_segments (0x6b9fc : word) = Some W_6b9bc.
Proof. vm_refl. Qed.
Lemma D_6b9bc : decode_any W_6b9bc = Some (ShiftImm ALU_SRA 10 18 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b9c0 : bv 32 := 0x00a67e63.
Lemma F_6b9c0 : fetch_word Plain.M.loaded_segments (0x6ba00 : word) = Some W_6b9c0.
Proof. vm_refl. Qed.
Lemma D_6b9c0 : decode_any W_6b9c0 = Some (Branch BC_GEU 12 10 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b9c4 : bv 32 := 0xff900613.
Lemma F_6b9c4 : fetch_word Plain.M.loaded_segments (0x6ba04 : word) = Some W_6b9c4.
Proof. vm_refl. Qed.
Lemma D_6b9c4 : decode_any W_6b9c4 = Some (OpImm ALU_ADD 12 0 4089, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b9c8 : bv 32 := 0x00165613.
Lemma F_6b9c8 : fetch_word Plain.M.loaded_segments (0x6ba08 : word) = Some W_6b9c8.
Proof. vm_refl. Qed.
Lemma D_6b9c8 : decode_any W_6b9c8 = Some (ShiftImm ALU_SRL 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b9cc : bv 32 := 0x02c97063.
Lemma F_6b9cc : fetch_word Plain.M.loaded_segments (0x6ba0c : word) = Some W_6b9cc.
Proof. vm_refl. Qed.
Lemma D_6b9cc : decode_any W_6b9cc = Some (Branch BC_GEU 18 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b9d0 : bv 32 := 0x00251a13.
Lemma F_6b9d0 : fetch_word Plain.M.loaded_segments (0x6ba10 : word) = Some W_6b9d0.
Proof. vm_refl. Qed.
Lemma D_6b9d0 : decode_any W_6b9d0 = Some (ShiftImm ALU_SLL 20 10 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b9d4 : bv 32 := 0x02051463.
Lemma F_6b9d4 : fetch_word Plain.M.loaded_segments (0x6ba14 : word) = Some W_6b9d4.
Proof. vm_refl. Qed.
Lemma D_6b9d4 : decode_any W_6b9d4 = Some (Branch BC_NE 10 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b9dc : bv 32 := 0x00060513.
Lemma F_6b9dc : fetch_word Plain.M.loaded_segments (0x6ba1c : word) = Some W_6b9dc.
Proof. vm_refl. Qed.
Lemma D_6b9dc : decode_any W_6b9dc = Some (OpImm ALU_ADD 10 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b9e0 : bv 32 := 0xff900613.
Lemma F_6b9e0 : fetch_word Plain.M.loaded_segments (0x6ba20 : word) = Some W_6b9e0.
Proof. vm_refl. Qed.
Lemma D_6b9e0 : decode_any W_6b9e0 = Some (OpImm ALU_ADD 12 0 4089, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b9e4 : bv 32 := 0x00165613.
Lemma F_6b9e4 : fetch_word Plain.M.loaded_segments (0x6ba24 : word) = Some W_6b9e4.
Proof. vm_refl. Qed.
Lemma D_6b9e4 : decode_any W_6b9e4 = Some (ShiftImm ALU_SRL 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b9e8 : bv 32 := 0xfec964e3.
Lemma F_6b9e8 : fetch_word Plain.M.loaded_segments (0x6ba28 : word) = Some W_6b9e8.
Proof. vm_refl. Qed.
Lemma D_6b9e8 : decode_any W_6b9e8 = Some (Branch BC_LTU 18 12 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_6b9fc : bv 32 := 0x03e55513.
Lemma F_6b9fc : fetch_word Plain.M.loaded_segments (0x6ba3c : word) = Some W_6b9fc.
Proof. vm_refl. Qed.
Lemma D_6b9fc : decode_any W_6b9fc = Some (ShiftImm ALU_SRL 10 10 62, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ba00 : bv 32 := 0x08051663.
Lemma F_6ba00 : fetch_word Plain.M.loaded_segments (0x6ba40 : word) = Some W_6ba00.
Proof. vm_refl. Qed.
Lemma D_6ba00 : decode_any W_6ba00 = Some (Branch BC_NE 10 0 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ba04 : bv 32 := 0x00058b13.
Lemma F_6ba04 : fetch_word Plain.M.loaded_segments (0x6ba44 : word) = Some W_6ba04.
Proof. vm_refl. Qed.
Lemma D_6ba04 : decode_any W_6ba04 = Some (OpImm ALU_ADD 22 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ba08 : bv 32 := 0x000a0513.
Lemma F_6ba08 : fetch_word Plain.M.loaded_segments (0x6ba48 : word) = Some W_6ba08.
Proof. vm_refl. Qed.
Lemma D_6ba08 : decode_any W_6ba08 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ba0c : bv 32 := 0x3907a0ef.
Lemma F_6ba0c : fetch_word Plain.M.loaded_segments (0x6ba4c : word) = Some W_6ba0c.
Proof. vm_refl. Qed.
Lemma D_6ba0c : decode_any W_6ba0c = Some (Jal 1 500624, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ba10 : bv 32 := 0x000b0593.
Lemma F_6ba10 : fetch_word Plain.M.loaded_segments (0x6ba50 : word) = Some W_6ba10.
Proof. vm_refl. Qed.
Lemma D_6ba10 : decode_any W_6ba10 = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ba14 : bv 32 := 0x01350633.
Lemma F_6ba14 : fetch_word Plain.M.loaded_segments (0x6ba54 : word) = Some W_6ba14.
Proof. vm_refl. Qed.
Lemma D_6ba14 : decode_any W_6ba14 = Some (Op ALU_ADD 12 10 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ba18 : bv 32 := 0x0005a583.
Lemma F_6ba18 : fetch_word Plain.M.loaded_segments (0x6ba58 : word) = Some W_6ba18.
Proof. vm_refl. Qed.
Lemma D_6ba18 : decode_any W_6ba18 = Some (Load SZ4 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ba1c : bv 32 := 0x01450b33.
Lemma F_6ba1c : fetch_word Plain.M.loaded_segments (0x6ba5c : word) = Some W_6ba1c.
Proof. vm_refl. Qed.
Lemma D_6ba1c : decode_any W_6ba1c = Some (Op ALU_ADD 22 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ba20 : bv 32 := 0x002a9513.
Lemma F_6ba20 : fetch_word Plain.M.loaded_segments (0x6ba60 : word) = Some W_6ba20.
Proof. vm_refl. Qed.
Lemma D_6ba20 : decode_any W_6ba20 = Some (ShiftImm ALU_SLL 10 21 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ba24 : bv 32 := 0x00460a93.
Lemma F_6ba24 : fetch_word Plain.M.loaded_segments (0x6ba64 : word) = Some W_6ba24.
Proof. vm_refl. Qed.
Lemma D_6ba24 : decode_any W_6ba24 = Some (OpImm ALU_ADD 21 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ba28 : bv 32 := 0x00b62023.
Lemma F_6ba28 : fetch_word Plain.M.loaded_segments (0x6ba68 : word) = Some W_6ba28.
Proof. vm_refl. Qed.
Lemma D_6ba28 : decode_any W_6ba28 = Some (Store SZ4 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ba2c : bv 32 := 0x40a60a33.
Lemma F_6ba2c : fetch_word Plain.M.loaded_segments (0x6ba6c : word) = Some W_6ba2c.
Proof. vm_refl. Qed.
Lemma D_6ba2c : decode_any W_6ba2c = Some (Op ALU_SUB 20 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ba30 : bv 32 := 0x000a0513.
Lemma F_6ba30 : fetch_word Plain.M.loaded_segments (0x6ba70 : word) = Some W_6ba30.
Proof. vm_refl. Qed.
Lemma D_6ba30 : decode_any W_6ba30 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ba34 : bv 32 := 0x00048593.
Lemma F_6ba34 : fetch_word Plain.M.loaded_segments (0x6ba74 : word) = Some W_6ba34.
Proof. vm_refl. Qed.
Lemma D_6ba34 : decode_any W_6ba34 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ba38 : bv 32 := 0x00098613.
Lemma F_6ba38 : fetch_word Plain.M.loaded_segments (0x6ba78 : word) = Some W_6ba38.
Proof. vm_refl. Qed.
Lemma D_6ba38 : decode_any W_6ba38 = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ba3c : bv 32 := 0x3c8750ef.
Lemma F_6ba3c : fetch_word Plain.M.loaded_segments (0x6ba7c : word) = Some W_6ba3c.
Proof. vm_refl. Qed.
Lemma D_6ba3c : decode_any W_6ba3c = Some (Jal 1 480200, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ba40 : bv 32 := 0x01443023.
Lemma F_6ba40 : fetch_word Plain.M.loaded_segments (0x6ba80 : word) = Some W_6ba40.
Proof. vm_refl. Qed.
Lemma D_6ba40 : decode_any W_6ba40 = Some (Store SZ8 8 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ba44 : bv 32 := 0x01543423.
Lemma F_6ba44 : fetch_word Plain.M.loaded_segments (0x6ba84 : word) = Some W_6ba44.
Proof. vm_refl. Qed.
Lemma D_6ba44 : decode_any W_6ba44 = Some (Store SZ8 8 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ba48 : bv 32 := 0x01643823.
Lemma F_6ba48 : fetch_word Plain.M.loaded_segments (0x6ba88 : word) = Some W_6ba48.
Proof. vm_refl. Qed.
Lemma D_6ba48 : decode_any W_6ba48 = Some (Store SZ8 8 22 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ba4c : bv 32 := 0x00048863.
Lemma F_6ba4c : fetch_word Plain.M.loaded_segments (0x6ba8c : word) = Some W_6ba4c.
Proof. vm_refl. Qed.
Lemma D_6ba4c : decode_any W_6ba4c = Some (Branch BC_EQ 9 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ba50 : bv 32 := 0x00048513.
Lemma F_6ba50 : fetch_word Plain.M.loaded_segments (0x6ba90 : word) = Some W_6ba50.
Proof. vm_refl. Qed.
Lemma D_6ba50 : decode_any W_6ba50 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ba54 : bv 32 := 0x00090593.
Lemma F_6ba54 : fetch_word Plain.M.loaded_segments (0x6ba94 : word) = Some W_6ba54.
Proof. vm_refl. Qed.
Lemma D_6ba54 : decode_any W_6ba54 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ba58 : bv 32 := 0x0dc020ef.
Lemma F_6ba58 : fetch_word Plain.M.loaded_segments (0x6ba98 : word) = Some W_6ba58.
Proof. vm_refl. Qed.
Lemma D_6ba58 : decode_any W_6ba58 = Some (Jal 1 8412, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ba5c : bv 32 := 0x01543423.
Lemma F_6ba5c : fetch_word Plain.M.loaded_segments (0x6ba9c : word) = Some W_6ba5c.
Proof. vm_refl. Qed.
Lemma D_6ba5c : decode_any W_6ba5c = Some (Store SZ8 8 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ba60 : bv 32 := 0x03813083.
Lemma F_6ba60 : fetch_word Plain.M.loaded_segments (0x6baa0 : word) = Some W_6ba60.
Proof. vm_refl. Qed.
Lemma D_6ba60 : decode_any W_6ba60 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ba64 : bv 32 := 0x03013403.
Lemma F_6ba64 : fetch_word Plain.M.loaded_segments (0x6baa4 : word) = Some W_6ba64.
Proof. vm_refl. Qed.
Lemma D_6ba64 : decode_any W_6ba64 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ba68 : bv 32 := 0x02813483.
Lemma F_6ba68 : fetch_word Plain.M.loaded_segments (0x6baa8 : word) = Some W_6ba68.
Proof. vm_refl. Qed.
Lemma D_6ba68 : decode_any W_6ba68 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ba6c : bv 32 := 0x02013903.
Lemma F_6ba6c : fetch_word Plain.M.loaded_segments (0x6baac : word) = Some W_6ba6c.
Proof. vm_refl. Qed.
Lemma D_6ba6c : decode_any W_6ba6c = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ba70 : bv 32 := 0x01813983.
Lemma F_6ba70 : fetch_word Plain.M.loaded_segments (0x6bab0 : word) = Some W_6ba70.
Proof. vm_refl. Qed.
Lemma D_6ba70 : decode_any W_6ba70 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ba74 : bv 32 := 0x01013a03.
Lemma F_6ba74 : fetch_word Plain.M.loaded_segments (0x6bab4 : word) = Some W_6ba74.
Proof. vm_refl. Qed.
Lemma D_6ba74 : decode_any W_6ba74 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ba78 : bv 32 := 0x00813a83.
Lemma F_6ba78 : fetch_word Plain.M.loaded_segments (0x6bab8 : word) = Some W_6ba78.
Proof. vm_refl. Qed.
Lemma D_6ba78 : decode_any W_6ba78 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ba7c : bv 32 := 0x00013b03.
Lemma F_6ba7c : fetch_word Plain.M.loaded_segments (0x6babc : word) = Some W_6ba7c.
Proof. vm_refl. Qed.
Lemma D_6ba7c : decode_any W_6ba7c = Some (Load SZ8 true 22 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ba80 : bv 32 := 0x04010113.
Lemma F_6ba80 : fetch_word Plain.M.loaded_segments (0x6bac0 : word) = Some W_6ba80.
Proof. vm_refl. Qed.
Lemma D_6ba80 : decode_any W_6ba80 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ba84 : bv 32 := 0x00008067.
Lemma F_6ba84 : fetch_word Plain.M.loaded_segments (0x6bac4 : word) = Some W_6ba84.
Proof. vm_refl. Qed.
Lemma D_6ba84 : decode_any W_6ba84 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
End S1_code_6b95c_6ba90.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PeLia.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac WalkTac StartupTac SumWalkTac StoreOk MemSplit Hoare ShapeAlg
  SRealizes RefMemcpyLib RefReadLib LibIface LibEff MmapSim SumMemcpyBase SumMemcpy S1Layout.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContLib ContStmts S1Facts Lib_Cxx_OperatorDelete.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.Lib_Vec32_PushBack_6b8f8.S1_code_6b95c_6ba90.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PeLia.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Local Ltac lia ::= pe_lia.
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
Ltac rdA H := peel; rdn_fix H.

Ltac slotv SL k H :=
  pose proof (SL k ltac:(lia)) as H;
  lazymatch type of H with rdn _ _ _ _ = Some (word_to_le_bytes 8 ?v) =>
    let v' := eval simpl in v in change v with v' in H end.
Ltac b2z8 := apply bytes_le_to_Z_8.

Section PushBack.
Context {AC : AllocCeiling}.
  Variable MI : MallocIface SEGS Ly.L.
  Variable ST : StaticsIface SEGS Ly.L.
  Hypothesis MALLOC_STACK_pos : (0 <= MALLOC_STACK MI)%Z.
  Hypothesis NEW : new_rule_stmt SEGS Ly.L MI ST (NEW_STACK SEGS Ly.L MI).

  #[local] Notation placed_sep := (placed_sep SEGS Ly.L MI ly_img_low ly_rw_img).
  #[local] Notation stack_sep := (stack_sep SEGS Ly.L MI ly_img_low ly_rw_img).
  #[local] Notation offimg_sep := (offimg_sep SEGS Ly.L ST ly_rw_img ly_relro_img ly_errno_img).

  Definition PRO_vals (R : bvmap 5 word) (ret : Z) : list word :=
    [getr R 22%bv; getr R 21%bv; getr R 20%bv; getr R 19%bv; getr R 18%bv; getr R 9%bv; getr R 8%bv; Z_to_bv 64 ret].

  Lemma prologue : forall (fx : FPState) R M sp ret v,
    getr R 2%bv = Z_to_bv 64 sp -> getr R 1%bv = Z_to_bv 64 ret -> getr R 10%bv = Z_to_bv 64 v ->
    store_ok SEGS M (Z_to_bv 64 (sp - 64)) 64 = true -> 64 <= sp < 2 ^ 63 ->
    msteps SEGS (@mkst fx R (Z_to_bv 64 0x6b99c) M (seg_rom SEGS))
                (@mkst fx (regupd (regupd R 2%bv (Z_to_bv 64 (sp - 64))) 8%bv (Z_to_bv 64 v))
                          (Z_to_bv 64 0x6b9c4) (wslots M sp (PRO_vals R ret)) (seg_rom SEGS)).
  Proof using.
    intros fx R M sp ret v Hsp Hra Ha0 HOK Hsp'.
    norm_pc.
    sv F_6b95c D_6b95c (Z_to_bv 64 (sp - 64)).
    stw F_6b960 D_6b960 (Z_to_bv 64 (sp - 8)) (Z_to_bv 64 ret) ltac:(ok_sub HOK).
    stw F_6b964 D_6b964 (Z_to_bv 64 (sp - 16)) (getr R 8%bv) ltac:(ok_sub HOK).
    stw F_6b968 D_6b968 (Z_to_bv 64 (sp - 24)) (getr R 9%bv) ltac:(ok_sub HOK).
    stw F_6b96c D_6b96c (Z_to_bv 64 (sp - 32)) (getr R 18%bv) ltac:(ok_sub HOK).
    stw F_6b970 D_6b970 (Z_to_bv 64 (sp - 40)) (getr R 19%bv) ltac:(ok_sub HOK).
    stw F_6b974 D_6b974 (Z_to_bv 64 (sp - 48)) (getr R 20%bv) ltac:(ok_sub HOK).
    stw F_6b978 D_6b978 (Z_to_bv 64 (sp - 56)) (getr R 21%bv) ltac:(ok_sub HOK).
    stw F_6b97c D_6b97c (Z_to_bv 64 (sp - 64)) (getr R 22%bv) ltac:(ok_sub HOK).
    sv F_6b980 D_6b980 (Z_to_bv 64 v).
    lazymatch goal with |- msteps _ ?a ?b => replace b with a; [apply mst_refl|] end.
    f_equal. apply bv_eq; reflexivity.
  Qed.
  Lemma epilogue : forall (fx : FPState) R M sp ret v (s5v v8 v9 v18 v19 v20 v21 v22 : word),
    getr R 2%bv = Z_to_bv 64 (sp - 64) -> getr R 8%bv = Z_to_bv 64 v -> getr R 21%bv = s5v ->
    64 <= sp < 2 ^ 63 -> 0 <= v -> v + 24 <= 2 ^ 63 -> (v + 24 <= sp - 64 \/ sp <= v) ->
    store_ok SEGS M (Z_to_bv 64 (v + 8)) 8 = true ->
    rdn SEGS M (Z_to_bv 64 (sp - 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 ret)) ->
    rdn SEGS M (Z_to_bv 64 (sp - 16)) 8 = Some (word_to_le_bytes 8 v8) ->
    rdn SEGS M (Z_to_bv 64 (sp - 24)) 8 = Some (word_to_le_bytes 8 v9) ->
    rdn SEGS M (Z_to_bv 64 (sp - 32)) 8 = Some (word_to_le_bytes 8 v18) ->
    rdn SEGS M (Z_to_bv 64 (sp - 40)) 8 = Some (word_to_le_bytes 8 v19) ->
    rdn SEGS M (Z_to_bv 64 (sp - 48)) 8 = Some (word_to_le_bytes 8 v20) ->
    rdn SEGS M (Z_to_bv 64 (sp - 56)) 8 = Some (word_to_le_bytes 8 v21) ->
    rdn SEGS M (Z_to_bv 64 (sp - 64)) 8 = Some (word_to_le_bytes 8 v22) ->
    ret_ok (Z_to_bv 64 ret) ->
    msteps SEGS (@mkst fx R (Z_to_bv 64 0x6ba9c) M (seg_rom SEGS))
                (@mkst fx (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd R
                             1%bv (Z_to_bv 64 ret)) 8%bv v8) 9%bv v9) 18%bv v18) 19%bv v19) 20%bv v20) 21%bv v21) 22%bv v22)
                             2%bv (Z_to_bv 64 sp))
                          (Z_to_bv 64 ret) (wbytes M (Z_to_bv 64 (v + 8)) (word_to_le_bytes 8 s5v)) (seg_rom SEGS)).
  Proof using.
    intros fx R M sp ret v s5v v8 v9 v18 v19 v20 v21 v22 Hsp Hs0 Hs5 Hsp' Hv0 Hv1 Hdisj HOKv
           L1 L8 L9 L18 L19 L20 L21 L22 Hret.
    norm_pc.
    stw F_6ba5c D_6ba5c (Z_to_bv 64 (v + 8)) s5v ltac:(exact HOKv).
    ld_step F_6ba60 D_6ba60 (word_to_le_bytes 8 (Z_to_bv 64 ret)) (Z_to_bv 64 ret) ltac:(rdA L1) ltac:(b2z8).
    ld_step F_6ba64 D_6ba64 (word_to_le_bytes 8 v8) v8 ltac:(rdA L8) ltac:(b2z8).
    ld_step F_6ba68 D_6ba68 (word_to_le_bytes 8 v9) v9 ltac:(rdA L9) ltac:(b2z8).
    ld_step F_6ba6c D_6ba6c (word_to_le_bytes 8 v18) v18 ltac:(rdA L18) ltac:(b2z8).
    ld_step F_6ba70 D_6ba70 (word_to_le_bytes 8 v19) v19 ltac:(rdA L19) ltac:(b2z8).
    ld_step F_6ba74 D_6ba74 (word_to_le_bytes 8 v20) v20 ltac:(rdA L20) ltac:(b2z8).
    ld_step F_6ba78 D_6ba78 (word_to_le_bytes 8 v21) v21 ltac:(rdA L21) ltac:(b2z8).
    ld_step F_6ba7c D_6ba7c (word_to_le_bytes 8 v22) v22 ltac:(rdA L22) ltac:(b2z8).
    sv F_6ba80 D_6ba80 (Z_to_bv 64 sp).
    stepjr F_6ba84 D_6ba84 (Z_to_bv 64 ret) ltac:(gres; reflexivity).
    lazymatch goal with |- msteps _ ?a ?b => replace b with a; [apply mst_refl|] end.
    f_equal. exact Hret.
  Qed.
  Definition c6b8f8 : vec_consts := {| vc_entry := 0x6b99c; vc_stack := 64 |}.

  Theorem vec32_push_back_6b8f8_spec : vec32_push_back_stmt SEGS Ly.L MI ST c6b8f8.
  Proof using AC MI ST MALLOC_STACK_pos NEW.
    intros fx A s R M model sp ret v b cap src x xs K.
    cbn [vc_entry vc_stack c6b8f8]. lazy zeta.
    intros CB Ha0 Ha1 VEC OBJ SRC Hx SOBJ Hs0 Hs1 SRCV HNMAX ROOM CONT.
    destruct CB as [AI MS ROC SXI SXH CR Hceil HROOM Hwin Hown_sx Herr_sx].
    destruct CR as [Hra Hret Hretr Hsp Hsp16 Hsphi Hgp Htp].
    cbn [ly_gp ly_tp ly_errno_off ly_img ly_relro ly_rw Ly.L] in *.
    unfold NEW_STACK in *.
    pose proof ac_bounds_lit as Hceilv.
    destruct VEC as (Hv0 & Hv1 & HDv & Hlen & Hb & F0 & F1 & F2 & FE).
    pose proof HROOM as HOK. unfold stack_room in HOK.
    assert (Hspr : 2 ^ 20 <= sp - (64 + (16 + MALLOC_STACK MI))) by (lia).
    pose proof (ai_nmax_bound MI) as HNM. pose proof (ai_big_pos MI) as HBIG.
    assert (Hcap : 0 <= cap < 2 ^ 40) by (unfold vgrow in HNMAX; lia).
    destruct OBJ as [PLv WINv]. destruct SOBJ as [PLs WINs].
    assert (WINv' : v + 24 <= sp - (64 + (16 + MALLOC_STACK MI)) \/ sp <= v).
    { destruct (Z.lt_ge_cases v sp); [left|right; lia].
      destruct (Z.lt_ge_cases (v + 24) (sp - (64 + (16 + MALLOC_STACK MI)) + 1)); [lia|].
      exfalso. destruct (Z.lt_ge_cases v (sp - (64 + (16 + MALLOC_STACK MI)))).
      - apply (WINv (sp - (64 + (16 + MALLOC_STACK MI)))); unfold zwin; lia.
      - apply (WINv v); unfold zwin; lia. }
    assert (WINs' : src + 4 <= sp - (64 + (16 + MALLOC_STACK MI)) \/ sp <= src).
    { destruct (Z.lt_ge_cases src sp); [left|right; lia].
      destruct (Z.lt_ge_cases (src + 4) (sp - (64 + (16 + MALLOC_STACK MI)) + 1)); [lia|].
      exfalso. destruct (Z.lt_ge_cases src (sp - (64 + (16 + MALLOC_STACK MI)))).
      - apply (WINs (sp - (64 + (16 + MALLOC_STACK MI)))); unfold zwin; lia.
      - apply (WINs src); unfold zwin; lia. }
    hide WINv'. hide WINs'.

    assert (BUF : b <> 0 -> mdef M b (4 * cap) /\ b + 4 * cap <= alloc_ceiling /\
                  (forall a, b <= a < b + 4 * cap -> ~ owned MI A a /\ ~ in_ranges [(0x10000, 0x122000)] a)).
    { intros Hbnz. destruct Hb as [[Hb0 _]|(Hbp & Hal & Hcp & Hbc & HIn & Hdj)]; [lia|].
      split; [eapply (live_mdef SEGS Ly.L MI); eassumption|].
      split; [eapply (live_range SEGS Ly.L MI); eassumption|].
      intros a Ha. split; [eapply (live_unowned SEGS Ly.L MI); eassumption|].
      eapply (live_offimg SEGS Ly.L MI); eassumption. }
    hide Hb.
    assert (Hb0 : 0 <= b) by (unhide Hb; destruct Hb as [[-> _]|(Hbp & _)]; lia).
    assert (Hbc4 : b + 4 * cap <= 2 ^ 63) by (unhide Hb; destruct Hb as [[-> ->]|(Hbp & Hal & Hcp & Hbc & _)]; lia).
    assert (HDR : forall a, v <= a < v + 24 -> ~ owned MI A a /\ ~ in_ranges [(0x10000, 0x122000)] a).
    { intros a Ha. exact (placed_sep A M model v 24 a AI PLv Ha). }
    assert (WIN : forall a, sp - (64 + (16 + MALLOC_STACK MI)) <= a < sp -> ~ owned MI A a /\ ~ in_ranges [(0x10000, 0x122000)] a).
    { intros a Ha. apply (stack_sep A M model a AI). lia. }
    assert (HDW : mdef M (sp - (64 + (16 + MALLOC_STACK MI))) (64 + (16 + MALLOC_STACK MI))).
    { eapply store_ok_mdef_offimg; [exact HOK | lia | lia | lia |]. intros w Hw. apply ly_noseg. lia. }

    set (M1 := wslots M sp (PRO_vals R ret)).
    assert (ST1 : stores_in (zwin (sp - 64) sp) M M1).
    { unfold M1. apply (wslots_stores_in M sp (PRO_vals R ret)); unfold Zlen; cbn; lia. }
    assert (AG1 : forall lo hi, (hi <= sp - 64 \/ sp <= lo) -> 0 <= lo -> hi < 2 ^ 64 -> agree_on (zwin lo hi) M M1).
    { intros lo hi Hd Hlo Hhi. eapply stores_in_agree; [exact ST1|]. intros a Ha. unfold zwin in *. lia. }
    assert (F0' : fld SEGS M1 v 8 b).
    { eapply fld_agree; [lia| cbn; lia | exact F0 |]. apply AG1; cbn; unhide WINv'; lia. }
    assert (F1' : fld SEGS M1 (v + 8) 8 (b + 4 * Zlen xs)).
    { eapply fld_agree; [lia| cbn; lia | exact F1 |]. apply AG1; cbn; unhide WINv'; lia. }
    assert (F2' : fld SEGS M1 (v + 16) 8 (b + 4 * cap)).
    { eapply fld_agree; [lia| cbn; lia | exact F2 |]. apply AG1; cbn; unhide WINv'; lia. }
    assert (SRC' : fld SEGS M1 src 4 x).
    { eapply fld_agree; [lia| cbn; lia | exact SRC |]. apply AG1; cbn; unhide WINs'; lia. }
    assert (SL : forall k, 1 <= k <= 8 ->
              rdn SEGS M1 (Z_to_bv 64 (sp - 8 * k)) 8
              = Some (word_to_le_bytes 8 (nth (Z.to_nat (8 - k)) (PRO_vals R ret) (Z_to_bv 64 0)))).
    { intros k Hk. unfold M1. apply wslots_read; unfold Zlen; cbn; lia. }
    slotv SL 1 SL1. slotv SL 2 SL2. slotv SL 3 SL3. slotv SL 4 SL4.
    slotv SL 5 SL5. slotv SL 6 SL6. slotv SL 7 SL7. slotv SL 8 SL8. clear SL.
    unfold fld in F0', F1', F2', SRC'.
    destruct (Z.lt_ge_cases (Zlen xs) cap) as [LT|GE].
    -
      assert (Hbnz : b <> 0) by (unhide Hb; destruct Hb as [[-> ->]|]; lia).
      destruct (BUF Hbnz) as (HDb & Hbce & Hbown).
      set (M2 := wbytes M1 (Z_to_bv 64 (b + 4 * Zlen xs)) (word_to_le_bytes 4 (v_lw (Z_to_bv 64 x)))).
      set (M3 := wbytes M2 (Z_to_bv 64 (v + 8)) (word_to_le_bytes 8 (Z_to_bv 64 (b + 4 * Zlen xs + 4)))).
      eapply srz_msteps; [exact (ms_halt _ MS) | exact (ms_lazy _ MS) | | ].
      + eapply msteps_trans.
        { apply (prologue fx R M sp ret v Hsp Hra Ha0); [ok_sub HOK | lia]. }
        fold M1.
        eapply msteps_trans.
        { norm_pc.
          ld_step F_6b984 D_6b984 (word_to_le_bytes 8 (Z_to_bv 64 (b + 4 * Zlen xs))) (Z_to_bv 64 (b + 4 * Zlen xs))
                  ltac:(rdn_fix F1') ltac:(b2z8).
          ld_step F_6b988 D_6b988 (word_to_le_bytes 8 (Z_to_bv 64 (b + 4 * cap))) (Z_to_bv 64 (b + 4 * cap))
                  ltac:(rdn_fix F2') ltac:(b2z8).
          stepb_ft F_6b98c D_6b98c ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_lt; lia).
          ld_step F_6b990 D_6b990 (word_to_le_bytes 4 (Z_to_bv 64 x)) (Z_to_bv 64 x)
                  ltac:(rdn_fix SRC') ltac:(apply lwu_val; lia).
          stw F_6b994 D_6b994 (Z_to_bv 64 (b + 4 * Zlen xs)) (v_lw (Z_to_bv 64 x))
              ltac:(eapply stores_in_store_ok; [exact ST1|]; apply (mdef_store_ok_off SEGS M b (4 * cap) (4 * Zlen xs) 4 HDb); lia).
          sv F_6b998 D_6b998 (Z_to_bv 64 (b + 4 * Zlen xs + 4)).
          stepj F_6b99c D_6b99c.
          apply mst_refl. }
        fold M2.
        lazymatch goal with |- msteps _ (mkst _ ?pc _ _) _ =>
          replace pc with (Z_to_bv 64 0x6ba9c) by (apply bv_eq; vm_compute; reflexivity) end.
        apply (epilogue fx _ M2 sp ret v (Z_to_bv 64 (b + 4 * Zlen xs + 4))
                 (getr R 8%bv) (getr R 9%bv) (getr R 18%bv) (getr R 19%bv) (getr R 20%bv) (getr R 21%bv) (getr R 22%bv));
          try (gres; reflexivity); try (unhide WINv'; lia); try exact Hret.
        * unfold M2. eapply stores_in_store_ok; [apply stores_in_wbytes with (W := fun _ => True); auto; rewrite ?length_N_to_le_bytes; cbn; lia|].
          eapply stores_in_store_ok; [exact ST1|]. apply (mdef_store_ok_off SEGS M v 24 8 8 HDv); lia.
        * unfold M2. rdA SL1.
        * unfold M2. rdA SL2.
        * unfold M2. rdA SL3.
        * unfold M2. rdA SL4.
        * unfold M2. rdA SL5.
        * unfold M2. rdA SL6.
        * unfold M2. rdA SL7.
        * unfold M2. rdA SL8.
      + fold M1 M2 M3.

        assert (ST3 : stores_in (fun a => zwin (sp - 64) sp a \/ zwin (b + 4 * Zlen xs) (b + 4 * Zlen xs + 4) a
                                          \/ zwin (v + 8) (v + 16) a) M M3).
        { unfold M3, M2. eapply stores_in_wbytes_more; [eapply stores_in_wbytes_more; [eapply stores_in_weaken; [exact ST1|] | | |] | | |];
            rewrite ?length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; try lia;
            intros a Ha; unfold zwin in *; lia. }
        eapply (CONT A _ M3 model b cap).
        *   constructor.
          -- eapply (stores_in_ainv SEGS Ly.L MI); [exact AI | exact ST3 |].
             intros a [Hw|[Hbuf|Hhd]].
             ++ apply WIN. unfold zwin in *; lia.
             ++ apply Hbown. unfold zwin in Hbuf. lia.
             ++ apply HDR. unfold zwin in Hhd. lia.
          -- exact MS.
          -- reflexivity.
          -- reflexivity.
          -- eapply (stores_in_sx SEGS Ly.L ST); [exact SXI | exact ST3 |].
             intros a Ha. pose proof (offimg_sep a) as OS.
             destruct Ha as [Hw|[Hbuf|Hhd]].
             ++ destruct (OS (proj2 (WIN a ltac:(unfold zwin in *; lia)))) as (X1 & X2 & _). split; assumption.
             ++ destruct (OS (proj2 (Hbown a ltac:(unfold zwin in *; lia)))) as (X1 & X2 & _). split; assumption.
             ++ destruct (OS (proj2 (HDR a ltac:(unfold zwin in *; lia)))) as (X1 & X2 & _). split; assumption.
          -- intros r Hr; unfold callee_saved in Hr.
             repeat (destruct Hr as [<-|Hr]; [gres; first [reflexivity | symmetry; assumption] |]). destruct Hr.
        *
          unhide Hb. destruct Hb as [[Hb00 _]|(Hbp & Hal & Hcp & Hbc & HIn & Hdj)]; [lia|]. hide Hdj.
          assert (AG3 : forall lo hi, 0 <= lo -> hi < 2 ^ 64 ->
                    (hi <= sp - 64 \/ sp <= lo) -> (hi <= b + 4 * Zlen xs \/ b + 4 * Zlen xs + 4 <= lo) ->
                    (hi <= v + 8 \/ v + 16 <= lo) -> agree_on (zwin lo hi) M M3).
          { intros lo hi H1 H2 H3 H4 H5. eapply stores_in_agree; [exact ST3|]. intros a Ha. unfold zwin in *. lia. }
          unfold CRep.vec32. rewrite Zlen_app1.
          split; [exact Hv0|]. split; [exact Hv1|]. split; [eapply stores_in_mdef; [exact ST3|exact HDv]|].
          split; [lia|]. split; [right; repeat split; try assumption; try lia|].
          split. { eapply fld_agree; [lia|cbn; lia|exact F0|]. apply AG3; cbn; unhide WINv'; unhide Hdj; lia. }
          split. { unfold fld, M3. replace (b + 4 * (Zlen xs + 1)) with (b + 4 * Zlen xs + 4) by lia.
                   apply rdn_wbytes_hit8. rewrite u64_of_Z by lia. lia. }
          split. { eapply fld_agree; [lia|cbn; lia|exact F2|]. apply AG3; cbn; unhide WINv'; unhide Hdj; lia. }
          intros i Hi. destruct (Z.lt_ge_cases i (Zlen xs)) as [Hlt|Hge].
          -- destruct (FE i ltac:(lia)) as [Hr HF]. rewrite Znth_app_l by lia. split; [exact Hr|].
             eapply fld_agree; [lia|cbn; lia|exact HF|]. apply AG3; cbn; unhide Hdj; lia.
          -- replace i with (Zlen xs) by lia. rewrite Znth_app_r1. split; [exact Hx|].
             unfold fld, M3, M2. unhide Hdj. rewrite rdn_wbytes_out_Z by (rewrite length_N_to_le_bytes; cbn; lia).
             rewrite sw_of_lw by lia. apply rdn_wbytes_hit4. rewrite u64_of_Z by lia. lia.
        * left. repeat split; try reflexivity. exact LT.
        * apply eff_store.
          -- intros a HF HW. apply (proj1 ST3). intros [Hw|[Hbuf|Hhd]].
             ++ apply HW. unfold W_of, zwin in *. cbn. lia.
             ++ apply HF. right; right. unfold zwin in *. lia.
             ++ apply HF. left. unfold zwin in *. lia.
          -- exact (proj2 ST3).
    -
      assert (LEN : Zlen xs = cap) by lia.
      set (R1 := regupd (regupd (regupd (regupd R 2%bv (Z_to_bv 64 (sp - 64))) 8%bv (Z_to_bv 64 v))
                          21%bv (Z_to_bv 64 (b + 4 * Zlen xs))) 10%bv (Z_to_bv 64 (b + 4 * cap))).

      assert (B2 : exists Rn,
        msteps SEGS (@mkst fx R1 (Z_to_bv 64 0x6b9e0) M1 (seg_rom SEGS))
                    (@mkst fx Rn (Z_to_bv 64 (ly_new Ly.L)) M1 (seg_rom SEGS))
        /\ getr Rn 10%bv = Z_to_bv 64 (4 * vgrow cap) /\ getr Rn 1%bv = Z_to_bv 64 0x6ba50
        /\ getr Rn 2%bv = Z_to_bv 64 (sp - 64) /\ getr Rn 3%bv = getr R 3%bv /\ getr Rn 4%bv = getr R 4%bv
        /\ getr Rn 8%bv = Z_to_bv 64 v /\ getr Rn 9%bv = Z_to_bv 64 b /\ getr Rn 18%bv = Z_to_bv 64 (4 * cap)
        /\ getr Rn 19%bv = Z_to_bv 64 (4 * cap) /\ getr Rn 20%bv = Z_to_bv 64 (4 * vgrow cap)
        /\ getr Rn 21%bv = Z_to_bv 64 cap /\ getr Rn 22%bv = Z_to_bv 64 src
        /\ (forall r, In r [23; 24; 25; 26; 27]%bv -> getr Rn r = getr R r)).
      { destruct (Z.lt_ge_cases 1 cap) as [Hc2|Hc1].
        -
          replace (vgrow cap) with (2 * cap) by (unfold vgrow; lia).
          eexists. split.
          + unfold R1. norm_pc.
            ld_step F_6b9a0 D_6b9a0 (word_to_le_bytes 8 (Z_to_bv 64 b)) (Z_to_bv 64 b) ltac:(rdn_fix F0') ltac:(b2z8).
            stepiv F_6b9a4 D_6b9a4 (Z_to_bv 64 (4 * cap)) ltac:(gres; rewrite v_sub_Z by lia; f_equal; lia).
            stepiv F_6b9a8 D_6b9a8 (Z_to_bv 64 cap) ltac:(gres; imm_norm; rewrite v_srai_Z by lia; f_equal; change (2^2) with 4; rewrite Z.mul_comm; apply Z.div_mul; lia).
            stepiv F_6b9ac D_6b9ac (Z_to_bv 64 (cap + 1)) ltac:(gres; imm_norm; rewrite v_addi_Z by lia; reflexivity).
            stepiv F_6b9b0 D_6b9b0 (Z_to_bv 64 0) ltac:(gres; imm_norm; rewrite v_srli_Z by lia; f_equal; rewrite Z.div_small by lia; reflexivity).
            stepb_ft F_6b9b4 D_6b9b4 ltac:(apply c_eq_refl).
            stepiv F_6b9b8 D_6b9b8 (Z_to_bv 64 (4 * cap)) ltac:(gres; rewrite v_sub_Z by lia; f_equal; lia).
            stepiv F_6b9bc D_6b9bc (Z_to_bv 64 (2 * cap)) ltac:(gres; imm_norm; rewrite v_srai_Z by lia; f_equal; change (2^1) with 2; replace (4 * cap) with (2 * cap * 2) by lia; apply Z.div_mul; lia).
            stepb_ft F_6b9c0 D_6b9c0 ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_lt; lia).
            stepiv F_6b9c4 D_6b9c4 (Z_to_bv 64 (2 ^ 64 - 7)) ltac:(gres; imm_norm; apply bv_eq; vm_compute; reflexivity).
            stepiv F_6b9c8 D_6b9c8 (Z_to_bv 64 0x7ffffffffffffffc) ltac:(gres; imm_norm; apply bv_eq; vm_compute; reflexivity).
            stepb_ft F_6b9cc D_6b9cc ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_lt; lia).
            stepiv F_6b9d0 D_6b9d0 (Z_to_bv 64 (4 * (2 * cap))) ltac:(gres; imm_norm; rewrite v_slli_Z by lia; f_equal; change (2^2) with 4; lia).
            stepb_tk F_6b9d4 D_6b9d4 ltac:(rewrite c_eq_Z' by lia; apply Z.eqb_neq; lia).
            stepiv F_6b9fc D_6b9fc (Z_to_bv 64 0) ltac:(gres; imm_norm; rewrite v_srli_Z by lia; f_equal; rewrite Z.div_small by lia; reflexivity).
            stepb_ft F_6ba00 D_6ba00 ltac:(apply c_eq_refl).
            sv F_6ba04 D_6ba04 (Z_to_bv 64 src).
            sv F_6ba08 D_6ba08 (Z_to_bv 64 (4 * (2 * cap))).
            stepj F_6ba0c D_6ba0c.
            lazymatch goal with |- msteps _ ?a ?bb => replace bb with a; [apply mst_refl|] end.
            f_equal. apply bv_eq; vm_compute; reflexivity.
          + gres. repeat split; try reflexivity; try assumption.
            intros r Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
        -
          replace (vgrow cap) with (cap + 1) by (unfold vgrow; lia).
          eexists. split.
          + unfold R1. norm_pc.
            ld_step F_6b9a0 D_6b9a0 (word_to_le_bytes 8 (Z_to_bv 64 b)) (Z_to_bv 64 b) ltac:(rdn_fix F0') ltac:(b2z8).
            stepiv F_6b9a4 D_6b9a4 (Z_to_bv 64 (4 * cap)) ltac:(gres; rewrite v_sub_Z by lia; f_equal; lia).
            stepiv F_6b9a8 D_6b9a8 (Z_to_bv 64 cap) ltac:(gres; imm_norm; rewrite v_srai_Z by lia; f_equal; change (2^2) with 4; rewrite Z.mul_comm; apply Z.div_mul; lia).
            stepiv F_6b9ac D_6b9ac (Z_to_bv 64 (cap + 1)) ltac:(gres; imm_norm; rewrite v_addi_Z by lia; reflexivity).
            stepiv F_6b9b0 D_6b9b0 (Z_to_bv 64 0) ltac:(gres; imm_norm; rewrite v_srli_Z by lia; f_equal; rewrite Z.div_small by lia; reflexivity).
            stepb_ft F_6b9b4 D_6b9b4 ltac:(apply c_eq_refl).
            stepiv F_6b9b8 D_6b9b8 (Z_to_bv 64 (4 * cap)) ltac:(gres; rewrite v_sub_Z by lia; f_equal; lia).
            stepiv F_6b9bc D_6b9bc (Z_to_bv 64 (2 * cap)) ltac:(gres; imm_norm; rewrite v_srai_Z by lia; f_equal; change (2^1) with 2; replace (4 * cap) with (2 * cap * 2) by lia; apply Z.div_mul; lia).
            stepb_tk F_6b9c0 D_6b9c0 ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_ge; lia).
            sv F_6b9dc D_6b9dc (Z_to_bv 64 (cap + 1)).
            stepiv F_6b9e0 D_6b9e0 (Z_to_bv 64 (2 ^ 64 - 7)) ltac:(gres; imm_norm; apply bv_eq; vm_compute; reflexivity).
            stepiv F_6b9e4 D_6b9e4 (Z_to_bv 64 0x7ffffffffffffffc) ltac:(gres; imm_norm; apply bv_eq; vm_compute; reflexivity).
            stepb_tk F_6b9e8 D_6b9e8 ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_lt; lia).
            stepiv F_6b9d0 D_6b9d0 (Z_to_bv 64 (4 * (cap + 1))) ltac:(gres; imm_norm; rewrite v_slli_Z by lia; f_equal; change (2^2) with 4; lia).
            stepb_tk F_6b9d4 D_6b9d4 ltac:(rewrite c_eq_Z' by lia; apply Z.eqb_neq; lia).
            stepiv F_6b9fc D_6b9fc (Z_to_bv 64 0) ltac:(gres; imm_norm; rewrite v_srli_Z by lia; f_equal; rewrite Z.div_small by lia; reflexivity).
            stepb_ft F_6ba00 D_6ba00 ltac:(apply c_eq_refl).
            sv F_6ba04 D_6ba04 (Z_to_bv 64 src).
            sv F_6ba08 D_6ba08 (Z_to_bv 64 (4 * (cap + 1))).
            stepj F_6ba0c D_6ba0c.
            lazymatch goal with |- msteps _ ?a ?bb => replace bb with a; [apply mst_refl|] end.
            f_equal. apply bv_eq; vm_compute; reflexivity.
          + gres. repeat split; try reflexivity; try assumption.
            intros r Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr. }
      destruct B2 as (Rn & RUN2 & Rn10 & Rn1 & Rn2 & Rn3 & Rn4 & Rn8 & Rn9 & Rn18 & Rn19 & Rn20 & Rn21 & Rn22 & RnS).

      eapply srz_msteps; [exact (ms_halt _ MS) | exact (ms_lazy _ MS) | | ].
      { eapply msteps_trans.
        { apply (prologue fx R M sp ret v Hsp Hra Ha0); [ok_sub HOK | lia]. }
        fold M1. eapply msteps_trans; [|exact RUN2].
        norm_pc.
        ld_step F_6b984 D_6b984 (word_to_le_bytes 8 (Z_to_bv 64 (b + 4 * Zlen xs))) (Z_to_bv 64 (b + 4 * Zlen xs))
                ltac:(rdn_fix F1') ltac:(b2z8).
        ld_step F_6b988 D_6b988 (word_to_le_bytes 8 (Z_to_bv 64 (b + 4 * cap))) (Z_to_bv 64 (b + 4 * cap))
                ltac:(rdn_fix F2') ltac:(b2z8).
        stepb_tk F_6b98c D_6b98c ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_ge; lia).
        unfold R1.
        lazymatch goal with |- msteps _ ?a ?bb => replace bb with a; [apply mst_refl|] end.
        f_equal. apply bv_eq; vm_compute; reflexivity. }
      assert (Hng : 4 <= 4 * vgrow cap) by (unfold vgrow; lia).
      eapply (NEW fx A s Rn M1 model (4 * vgrow cap) (sp - 64) 0x6ba50 K).
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
        * replace (sp - 64) with (sp - 16 * 4) by lia. apply mod16_sub. exact Hsp16.
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
      + rewrite new_size_id by lia. eapply (roomL_room_for SEGS Ly.L MI); [exact AI | lia | exact (ROOM LEN)].
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
        assert (Hn4 : n4 = Z.max (2 * cap) (cap + 1) * 4) by (unfold n4, vgrow; lia). clearbody n4.
        assert (HinP : In (p, n4) (live MI A1)) by (apply (live_add_new _ _ _ _ LADD)).
        destruct (live_range SEGS Ly.L MI A1 M2 model1 p n4 AI1 HinP) as (_ & Hpal & _ & Hpce).
        assert (HDp : mdef M2 p n4) by (eapply (live_mdef SEGS Ly.L MI); eassumption).
        assert (Hpown : forall a, p <= a < p + n4 -> ~ owned MI A1 a /\ ~ in_ranges [(0x10000, 0x122000)] a).
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
        assert (WIN1 : forall a, sp - (64 + (16 + MALLOC_STACK MI)) <= a < sp -> ~ owned MI A1 a /\ ~ in_ranges [(0x10000, 0x122000)] a).
        { intros a Ha. apply (stack_sep A1 M2 model1 a AI1). lia. }
        assert (HDR1 : forall a, v <= a < v + 24 -> ~ owned MI A1 a /\ ~ in_ranges [(0x10000, 0x122000)] a).
        { intros a Ha. exact (placed_sep A1 M2 model1 v 24 a AI1 PLv1 Ha). }
        assert (SRC1 : forall a, src <= a < src + 4 -> ~ owned MI A1 a /\ ~ in_ranges [(0x10000, 0x122000)] a).
        { intros a Ha. exact (placed_sep A1 M2 model1 src 4 a AI1 PLs1 Ha). }

        assert (PRES2 : forall a, (sp - 64 <= a < sp) \/ (v <= a < v + 24) \/ (src <= a < src + 4)
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
            + pose proof (proj2 (WIN1 a ltac:(lia))) as X. rewrite ly_img_iff in X. lia.
            + pose proof (proj2 (HDR1 a H)) as X. rewrite ly_img_iff in X. lia.
            + pose proof (proj2 (SRC1 a H)) as X. rewrite ly_img_iff in X. lia.
            + unhide Hb. destruct Hb as [[Hb00 _]|(Hbp & Hal & Hcp & Hbc & HIn & Hdj)]; [lia|].
              pose proof (live_offimg SEGS Ly.L MI A1 M2 model1 b (4 * cap) a AI1 (LIVE1 _ HIn) H) as X. rewrite ly_img_iff in X. lia. }
        assert (AG2 : forall lo hi, 0 <= lo -> hi < 2 ^ 64 ->
                 ((sp - 64 <= lo /\ hi <= sp) \/ (v <= lo /\ hi <= v + 24) \/ (src <= lo /\ hi <= src + 4)
                  \/ (b <> 0 /\ b <= lo /\ hi <= b + 4 * cap)) -> agree_on (zwin lo hi) M1 M2).
        { intros lo hi Hlo Hhi Hc a Ha. apply PRES2. unfold zwin in Ha. clear -Hc Ha.
          destruct Hc as [H|[H|[H|H]]]; [left|right;left|right;right;left|right;right;right]; lia. }

        assert (R2_2 : getr R2 2%bv = Z_to_bv 64 (sp - 64)) by (rewrite (KEPT2 2%bv) by in_cs; exact Rn2).
        assert (R2_8 : getr R2 8%bv = Z_to_bv 64 v) by (rewrite (KEPT2 8%bv) by in_cs; exact Rn8).
        assert (R2_9 : getr R2 9%bv = Z_to_bv 64 b) by (rewrite (KEPT2 9%bv) by in_cs; exact Rn9).
        assert (R2_18 : getr R2 18%bv = Z_to_bv 64 (4 * cap)) by (rewrite (KEPT2 18%bv) by in_cs; exact Rn18).
        assert (R2_19 : getr R2 19%bv = Z_to_bv 64 (4 * cap)) by (rewrite (KEPT2 19%bv) by in_cs; exact Rn19).
        assert (R2_20 : getr R2 20%bv = Z_to_bv 64 n4) by (rewrite (KEPT2 20%bv) by in_cs; exact Rn20).
        assert (R2_21 : getr R2 21%bv = Z_to_bv 64 cap) by (rewrite (KEPT2 21%bv) by in_cs; exact Rn21).
        assert (R2_22 : getr R2 22%bv = Z_to_bv 64 src) by (rewrite (KEPT2 22%bv) by in_cs; exact Rn22).
        assert (SRC2 : rdn SEGS M2 (Z_to_bv 64 src) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 x))).
        { change (fld SEGS M2 src 4 x). eapply fld_agree; [lia|cbn; lia|exact SRC'|]. apply AG2; cbn; lia. }
        set (M3 := wbytes M2 (Z_to_bv 64 (p + 4 * cap)) (word_to_le_bytes 4 (v_lw (Z_to_bv 64 x)))).

        eapply srz_msteps; [exact (ms_halt _ MS1) | exact (ms_lazy _ MS1) | | ].
        { norm_pc.
          sv F_6ba10 D_6ba10 (Z_to_bv 64 src).
          stepiv F_6ba14 D_6ba14 (Z_to_bv 64 (p + 4 * cap)) ltac:(gres; rewrite R2a0, R2_19; rewrite v_add_Z by lia; reflexivity).
          ld_step F_6ba18 D_6ba18 (word_to_le_bytes 4 (Z_to_bv 64 x)) (Z_to_bv 64 x) ltac:(rdn_fix SRC2) ltac:(apply lwu_val; lia).
          stepiv F_6ba1c D_6ba1c (Z_to_bv 64 (p + n4)) ltac:(gres; rewrite R2a0, R2_20; rewrite v_add_Z by lia; reflexivity).
          stepiv F_6ba20 D_6ba20 (Z_to_bv 64 (4 * cap)) ltac:(gres; rewrite R2_21; imm_norm; rewrite v_slli_Z by lia; f_equal; change (2^2) with 4; lia).
          stepiv F_6ba24 D_6ba24 (Z_to_bv 64 (p + 4 * cap + 4)) ltac:(gres; imm_norm; rewrite v_addi_Z by lia; reflexivity).
          stw F_6ba28 D_6ba28 (Z_to_bv 64 (p + 4 * cap)) (v_lw (Z_to_bv 64 x))
              ltac:(apply (mdef_store_ok_off SEGS M2 p n4 (4 * cap) 4 HDp); lia).
          stepiv F_6ba2c D_6ba2c (Z_to_bv 64 p) ltac:(gres; rewrite v_sub_Z by lia; f_equal; lia).
          sv F_6ba30 D_6ba30 (Z_to_bv 64 p).
          sv F_6ba34 D_6ba34 (Z_to_bv 64 b).
          sv F_6ba38 D_6ba38 (Z_to_bv 64 (4 * cap)).
          stepj F_6ba3c D_6ba3c.
          apply mst_refl. }
        fold M3.

        lazymatch goal with |- srealizes _ (mkCfg (mkst ?r _ _ _) _) _ => set (R3 := r) end.
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
        destruct (s1_memcpy M3 (Z_to_bv 64 p) (Z_to_bv 64 b) (4 * cap) (vec_bytes xs) (seg_rom SEGS) R3 (Z_to_bv 64 0x6ba80)
                    MC ltac:(unfold ret_ok; apply bv_eq; vm_compute; reflexivity)
                    ltac:(unfold R3; gres; apply bv_eq; vm_compute; reflexivity)
                    ltac:(unfold R3; gres; reflexivity) ltac:(unfold R3; gres; reflexivity) ltac:(unfold R3; gres; reflexivity))
          as (R4 & RUN4 & KEEP4).
        eapply srz_msteps; [exact (ms_halt _ MS1) | exact (ms_lazy _ MS1) | | ].
        { lazymatch goal with |- msteps _ (mkst _ ?pc _ _) _ =>
            replace pc with s1_memcpy_entry by (apply bv_eq; vm_compute; reflexivity) end.
          exact RUN4. }
        set (M4 := wbytes M3 (Z_to_bv 64 p) (vec_bytes xs)) in *.

        assert (R4_2 : getr R4 2%bv = Z_to_bv 64 (sp - 64)) by (rewrite (KEEP4 2%bv) by in_cs; unfold R3; gres; exact R2_2).
        assert (R4_8 : getr R4 8%bv = Z_to_bv 64 v) by (rewrite (KEEP4 8%bv) by in_cs; unfold R3; gres; exact R2_8).
        assert (R4_9 : getr R4 9%bv = Z_to_bv 64 b) by (rewrite (KEEP4 9%bv) by in_cs; unfold R3; gres; exact R2_9).
        assert (R4_18 : getr R4 18%bv = Z_to_bv 64 (4 * cap)) by (rewrite (KEEP4 18%bv) by in_cs; unfold R3; gres; exact R2_18).
        assert (R4_20 : getr R4 20%bv = Z_to_bv 64 p) by (rewrite (KEEP4 20%bv) by in_cs; unfold R3; gres; reflexivity).
        assert (R4_21 : getr R4 21%bv = Z_to_bv 64 (p + 4 * cap + 4)) by (rewrite (KEEP4 21%bv) by in_cs; unfold R3; gres; reflexivity).
        assert (R4_22 : getr R4 22%bv = Z_to_bv 64 (p + n4)) by (rewrite (KEEP4 22%bv) by in_cs; unfold R3; gres; reflexivity).

        set (W := (sp - (64 + (16 + MALLOC_STACK MI)), sp)).
        set (FT := fun a => zwin v (v + 24) a \/ (b <> 0 /\ zwin b (b + 4 * cap) a) \/ zwin p (p + 4 * vgrow cap) a).
        assert (TAIL : forall A2 R6 M6 model2,
          ainv MI A2 M6 model2 -> mstd model2 -> m_fs model2 = m_fs model -> m_fds model2 = m_fds model ->
          sx_inv ST s M6 ->
          getr R6 2%bv = Z_to_bv 64 (sp - 64) -> getr R6 8%bv = Z_to_bv 64 v -> getr R6 21%bv = Z_to_bv 64 (p + 4 * cap + 4) ->
          getr R6 3%bv = getr R 3%bv -> getr R6 4%bv = getr R 4%bv ->
          (forall r, In r [23; 24; 25; 26; 27]%bv -> getr R6 r = getr R r) ->
          agree_on (zwin (sp - 64) sp) M1 M6 ->
          mdef M6 v 24 -> fld SEGS M6 v 8 p -> fld SEGS M6 (v + 16) 8 (p + n4) ->
          (forall i, 0 <= i < cap -> fld SEGS M6 (p + 4 * i) 4 (Znth i xs)) -> fld SEGS M6 (p + 4 * cap) 4 x ->
          In (p, n4) (live MI A2) ->
          (forall a, v <= a < v + 24 -> ~ owned MI A2 a /\ ~ in_ranges [(0x10000, 0x122000)] a) ->
          eff MI A A2 M M6 W FT -> lapply (live MI A) (LAdd p n4 :: del_if b) (live MI A2) ->
          srealizes SEGS (mkCfg (@mkst fx R6 (Z_to_bv 64 0x6ba9c) M6 (seg_rom SEGS)) model2) K).
        { intros A2 R6 M6 model2 AI2 MS2 Hfs2 Hfds2 SX2 R6_2 R6_8 R6_21 R6_3 R6_4 R6S AG6 HDv6 G0 G2 GEL Gx HinP2 HDR2 EFF6 LAP.
          assert (SLT : forall a vv, sp - 64 <= a -> a + 8 <= sp -> rdn SEGS M1 (Z_to_bv 64 a) 8 = Some vv -> rdn SEGS M6 (Z_to_bv 64 a) 8 = Some vv).
          { intros a vv H1 H2 H3. rewrite (rdn_agree_win SEGS M1 M6); [exact H3 | lia | cbn; lia |].
            eapply agree_on_weaken; [exact AG6|]. intros a' Ha. unfold zwin in *. cbn in Ha. lia. }
          assert (WIN2 : forall a, sp - (64 + (16 + MALLOC_STACK MI)) <= a < sp -> ~ owned MI A2 a /\ ~ in_ranges [(0x10000, 0x122000)] a).
          { intros a Ha. apply (stack_sep A2 M6 model2 a AI2). lia. }
          set (M7 := wbytes M6 (Z_to_bv 64 (v + 8)) (word_to_le_bytes 8 (Z_to_bv 64 (p + 4 * cap + 4)))).
          assert (ST7 : stores_in (zwin (v + 8) (v + 16)) M6 M7).
          { unfold M7. apply stores_in_wbytes; rewrite ?length_N_to_le_bytes; cbn; try lia. intros a Ha. unfold zwin. lia. }
          eapply srz_msteps; [exact (ms_halt _ MS2) | exact (ms_lazy _ MS2) | | ].
          { apply (epilogue fx R6 M6 sp ret v (Z_to_bv 64 (p + 4 * cap + 4))
                   (getr R 8%bv) (getr R 9%bv) (getr R 18%bv) (getr R 19%bv) (getr R 20%bv) (getr R 21%bv) (getr R 22%bv));
              try assumption; try lia; try (unhide WINv'; lia).
            - apply (mdef_store_ok_off SEGS M6 v 24 8 8 HDv6); lia.
            - apply SLT; [lia|lia|rdn_fix SL1].
            - apply SLT; [lia|lia|rdn_fix SL2].
            - apply SLT; [lia|lia|rdn_fix SL3].
            - apply SLT; [lia|lia|rdn_fix SL4].
            - apply SLT; [lia|lia|rdn_fix SL5].
            - apply SLT; [lia|lia|rdn_fix SL6].
            - apply SLT; [lia|lia|rdn_fix SL7].
            - apply SLT; [lia|lia|rdn_fix SL8]. }
          fold M7.
          eapply (CONT A2 _ M7 model2 p (vgrow cap)).
          -   constructor.
            + eapply (stores_in_ainv SEGS Ly.L MI); [exact AI2 | exact ST7 |].
              intros a Ha. apply HDR2. unfold zwin in Ha; lia.
            + exact MS2.
            + exact Hfs2.
            + exact Hfds2.
            + eapply (stores_in_sx SEGS Ly.L ST); [exact SX2 | exact ST7 |].
              intros a Ha. destruct (offimg_sep a (proj2 (HDR2 a ltac:(unfold zwin in Ha; lia)))) as (X1 & X2 & _). split; assumption.
            + intros r Hr; unfold callee_saved in Hr.
              repeat (destruct Hr as [<-|Hr]; [gres; first [reflexivity | symmetry; assumption | rewrite ?R6_3, ?R6_4; reflexivity | apply R6S; in_cs ] |]).
              destruct Hr.
          -
            assert (AG7 : forall lo hi, 0 <= lo -> hi < 2 ^ 64 -> (hi <= v + 8 \/ v + 16 <= lo) -> agree_on (zwin lo hi) M6 M7).
            { intros lo hi H1 H2 H3. eapply stores_in_agree; [exact ST7|]. intros a Ha. unfold zwin in *. lia. }
            unhide HDRp. unfold vgrow in *.
            unfold CRep.vec32. rewrite Zlen_app1.
            split; [exact Hv0|]. split; [exact Hv1|]. split; [eapply stores_in_mdef; [exact ST7|exact HDv6]|].
            split; [lia|].
            split. { right. split; [lia|]. split; [exact Hpal|]. split; [lia|]. split; [lia|].
                     split; [replace (4 * Z.max (2 * cap) (cap + 1)) with n4 by lia; exact HinP2 | lia]. }
            split. { eapply fld_agree; [lia|cbn; lia|exact G0|]. apply AG7; cbn; lia. }
            split. { unfold fld, M7. replace (p + 4 * (Zlen xs + 1)) with (p + 4 * cap + 4) by lia.
                     apply rdn_wbytes_hit8. rewrite u64_of_Z by lia. lia. }
            split. { replace (p + 4 * Z.max (2 * cap) (cap + 1)) with (p + n4) by lia. eapply fld_agree; [lia|cbn; lia|exact G2|]. apply AG7; cbn; lia. }
            intros i Hi. destruct (Z.lt_ge_cases i (Zlen xs)) as [Hlt|Hge].
            + destruct (FE i ltac:(lia)) as [Hr _]. rewrite Znth_app_l by lia. split; [exact Hr|].
              eapply fld_agree; [lia|cbn; lia|apply GEL; lia|]. apply AG7; cbn; lia.
            + replace i with (Zlen xs) by lia. rewrite Znth_app_r1. split; [exact Hx|].
              rewrite LEN. eapply fld_agree; [lia|cbn; lia|exact Gx|]. apply AG7; cbn; lia.
          - right. split; [exact LEN|]. split; [reflexivity|]. replace (4 * vgrow cap) with n4 by (unfold vgrow; lia). exact LAP.
          -
            eapply eff_weaken.
            + eapply (eff_trans MI); [exact EFF6 | | intros a Ha; apply WIN2; unfold W_of, W in Ha; cbn in Ha; lia].
              apply (eff_store MI A2 M6 M7 W FT); [| exact (proj2 ST7)].
              intros a HF HW. apply (proj1 ST7). intros Hz. apply HF. unfold FT. left. unfold zwin in *. lia.
            + intros a' [H|H]; exact H.
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
        assert (AG15 : agree_on (zwin (sp - 64) sp) M1 M5).
        { intros a Ha. unfold zwin in Ha. rewrite (AG25 (sp - 64) sp); try lia.
          - apply PRES2. left. lia.
          - unhide WINv'. lia.
          - unfold zwin. lia. }
        assert (G0 : fld SEGS M5 v 8 p).
        { unfold fld, M5. rewrite 2!rdn_wbytes_out_Z by (rewrite length_N_to_le_bytes; cbn; lia).
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
          stw F_6ba40 D_6ba40 (Z_to_bv 64 v) (Z_to_bv 64 p) ltac:(ok_mdef HDv4).
          stw F_6ba44 D_6ba44 (Z_to_bv 64 (v + 8)) (Z_to_bv 64 (p + 4 * cap + 4)) ltac:(ok_mdef HDv4).
          stw F_6ba48 D_6ba48 (Z_to_bv 64 (v + 16)) (Z_to_bv 64 (p + n4)) ltac:(ok_mdef HDv4).
          apply mst_refl. }
        fold M5.
        assert (HDv5 : mdef M5 v 24) by (unfold M5; apply mdef_wbytes, mdef_wbytes, mdef_wbytes; exact HDv4).

        assert (R4_3 : getr R4 3%bv = getr R 3%bv) by (rewrite (KEEP4 3%bv) by in_cs; unfold R3; gres; rewrite (KEPT2 3%bv) by in_cs; exact Rn3).
        assert (R4_4 : getr R4 4%bv = getr R 4%bv) by (rewrite (KEEP4 4%bv) by in_cs; unfold R3; gres; rewrite (KEPT2 4%bv) by in_cs; exact Rn4).
        assert (R4S : forall r, In r [23; 24; 25; 26; 27]%bv -> getr R4 r = getr R r).
        { intros r Hr. pose proof Hr as Hr'.
          repeat (destruct Hr as [<-|Hr]; [rewrite (KEEP4 _) by in_cs; unfold R3; gres; rewrite (KEPT2 _) by in_cs; apply RnS; exact Hr' |]). destruct Hr. }
        destruct (Z.eq_dec b 0) as [Hbz|Hbnz].
        *
          eapply srz_msteps; [exact (ms_halt _ MS1) | exact (ms_lazy _ MS1) | | ].
          { norm_pc. stepb_tk F_6ba4c D_6ba4c ltac:(rewrite R4_9, Hbz; apply c_eq_refl). apply mst_refl. }
          lazymatch goal with |- srealizes _ (mkCfg (mkst _ ?pc _ _) _) _ =>
            replace pc with (Z_to_bv 64 0x6ba9c) by (apply bv_eq; vm_compute; reflexivity) end.
          apply (TAIL A1 R4 M5 model1); try assumption.
          -- eapply (stores_in_ainv SEGS Ly.L MI); [exact AI1 | exact ST25 |].
             intros a [Ha|Ha]; [apply Hpown | apply HDR1]; unfold zwin in Ha; lia.
          -- eapply (stores_in_sx SEGS Ly.L ST); [exact SX1 | exact ST25 |].
             intros a Ha. assert (Hni : ~ in_ranges [(0x10000, 0x122000)] a)
               by (destruct Ha as [Ha|Ha]; [apply Hpown | apply HDR1]; unfold zwin in Ha; lia).
             destruct (offimg_sep a Hni) as (X1 & X2 & _). split; assumption.
          -- subst b. cbn. exists (live MI A1). split; [exact LADD | reflexivity].
        *
          unhide Hb. destruct Hb as [[Hb00 _]|(Hbp & Hal & Hcp & Hbc & HIn & Hdj)]; [lia|].
          eapply srz_msteps; [exact (ms_halt _ MS1) | exact (ms_lazy _ MS1) | | ].
          { norm_pc. stepb_ft F_6ba4c D_6ba4c ltac:(rewrite R4_9; rewrite c_eq_Z' by lia; apply Z.eqb_neq; lia).
            sv F_6ba50 D_6ba50 (Z_to_bv 64 b).
            sv F_6ba54 D_6ba54 (Z_to_bv 64 (4 * cap)).
            stepj F_6ba58 D_6ba58. apply mst_refl. }
          lazymatch goal with |- srealizes _ (mkCfg (mkst ?r ?pc _ _) _) _ =>
            replace pc with (Z_to_bv 64 DEL1) by (apply bv_eq; vm_compute; reflexivity); set (R5 := r) end.
          eapply (op_delete1_spec MI fx A1 R5 M5 model1 b (4 * cap) (sp - 64) 0x6ba9c K).
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
             ++ replace (sp - 64) with (sp - 16 * 4) by lia. apply mod16_sub. exact Hsp16.
             ++ lia.
             ++ rewrite R4_3. exact Hgp.
             ++ rewrite R4_4. exact Htp.
          -- unfold R5; gres; reflexivity.
          -- right. apply LIVE1. exact HIn.
          -- lia.
          -- unfold stack_room. eapply stores_in_store_ok; [exact ST25|].
             assert (HDW2 : mdef M2 (sp - (64 + (16 + MALLOC_STACK MI))) (64 + (16 + MALLOC_STACK MI))).
             { eapply (mdef_through (fun a => owned MI A a \/ errno_win Ly.L a)); [exact DEF1 | eapply stores_in_mdef; [exact ST1 | exact HDW] | lia | lia |].
               intros a Ha [Ho|He]; [exact (proj1 (WIN a ltac:(lia)) Ho) | exact (proj2 (WIN a ltac:(lia)) (ly_errno_img a He))]. }
             replace (sp - 64 - MALLOC_STACK MI) with (sp - (64 + (16 + MALLOC_STACK MI)) + 16) by lia.
             apply (mdef_store_ok_off SEGS M2 _ _ 16 _ HDW2); lia.
          -- intros a Ha. apply WIN1. unfold zwin in *. lia.
          -- intros A2 R6 M6 model2 AI2 MS2 Hfs2 Hfds2 KEPT6 LDEL CAPS2 BIGC2 OWN2 FR2 DEF2.
             assert (Hpb : p <> b).
             { intros ->. destruct LADD as [_ Hnin]. apply Hnin. apply in_map_iff. exists (b, 4 * cap). split; [reflexivity|exact HIn]. }
             pose proof (BUFp ltac:(lia)) as BUFp'.
             unhide Hdj.
             assert (FSEP : forall a, (sp - 64 <= a < sp) \/ (v <= a < v + 24) \/ (p <= a < p + n4) ->
                              ~ owned MI A1 a /\ ~ (b <= a < b + 4 * cap) /\ ~ zwin (sp - 64 - MALLOC_STACK MI) (sp - 64) a /\ ~ in_ranges (ly_img Ly.L) a).
             { intros a [Ha|[Ha|Ha]].
               - destruct (WIN1 a ltac:(lia)) as [Y1 Y2]. split; [exact Y1|]. split; [|split; [|exact Y2]]; (destruct (BUF ltac:(lia)) as (_ & Hbce & _); unfold zwin; lia).
               - destruct (HDR1 a ltac:(lia)) as [Y1 Y2]. split; [exact Y1|]. split; [|split; [|exact Y2]]; (unfold zwin; unhide WINv'; lia).
               - destruct (Hpown a ltac:(lia)) as [Y1 Y2]. split; [exact Y1|]. split; [|split; [|exact Y2]]; (unfold zwin; lia). }
             assert (AG56 : forall lo hi, 0 <= lo -> hi < 2 ^ 64 ->
                      ((sp - 64 <= lo /\ hi <= sp) \/ (v <= lo /\ hi <= v + 24) \/ (p <= lo /\ hi <= p + n4)) ->
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
             ++ rewrite (KEPT6 8%bv) by in_cs. unfold R5. gres. exact R4_8.
             ++ rewrite (KEPT6 21%bv) by in_cs. unfold R5. gres. exact R4_21.
             ++ rewrite (KEPT6 3%bv) by in_cs. unfold R5. gres. exact R4_3.
             ++ rewrite (KEPT6 4%bv) by in_cs. unfold R5. gres. exact R4_4.
             ++ intros r Hr. pose proof Hr as Hr'.
                repeat (destruct Hr as [<-|Hr]; [rewrite (KEPT6 _) by in_cs; unfold R5; gres; apply R4S; exact Hr' |]). destruct Hr.
             ++ intros a Ha. rewrite (AG56 (sp - 64) sp); [apply AG15; exact Ha | lia | lia | left; lia | exact Ha].
             ++ eapply (mdef_through (fun a => owned MI A1 a \/ ((b <= a < b + 4 * cap) \/ errno_win Ly.L a))); [exact DEF2 | exact HDv5 | lia | lia |].
                intros a Ha [Ho|[Hblk|He]]; [exact (proj1 (HDR1 a Ha) Ho)  |  lia | exact (proj2 (HDR1 a Ha) (ly_errno_img a He))].
             ++ eapply fld_agree; [lia | cbn; lia | exact G0 |]. apply AG56; cbn; lia.
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
End PushBack.
