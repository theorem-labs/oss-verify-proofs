(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Ubsan.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StepTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.WalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StartupTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SumWalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MemSplit OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ShapeAlg OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SRealizes OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefReadLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibEff OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MmapSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SumMemcpyBase OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SumMemcpy OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibMaskBits OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.U1Layout.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.CRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.U1Facts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContStmts2 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.U1Lib_Cxx_OperatorDelete.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Module U1_code_6bd00_6bed0.

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Ubsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_6bd00 : bv 32 := 0xfc010113.
Lemma F_6bd00 : fetch_word Ubsan.M.loaded_segments (0x6bd40 : word) = Some W_6bd00.
Proof. vm_refl. Qed.
Lemma D_6bd00 : decode_any W_6bd00 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bd04 : bv 32 := 0x02113c23.
Lemma F_6bd04 : fetch_word Ubsan.M.loaded_segments (0x6bd44 : word) = Some W_6bd04.
Proof. vm_refl. Qed.
Lemma D_6bd04 : decode_any W_6bd04 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bd08 : bv 32 := 0x02813823.
Lemma F_6bd08 : fetch_word Ubsan.M.loaded_segments (0x6bd48 : word) = Some W_6bd08.
Proof. vm_refl. Qed.
Lemma D_6bd08 : decode_any W_6bd08 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bd0c : bv 32 := 0x02913423.
Lemma F_6bd0c : fetch_word Ubsan.M.loaded_segments (0x6bd4c : word) = Some W_6bd0c.
Proof. vm_refl. Qed.
Lemma D_6bd0c : decode_any W_6bd0c = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bd10 : bv 32 := 0x03213023.
Lemma F_6bd10 : fetch_word Ubsan.M.loaded_segments (0x6bd50 : word) = Some W_6bd10.
Proof. vm_refl. Qed.
Lemma D_6bd10 : decode_any W_6bd10 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bd14 : bv 32 := 0x01313c23.
Lemma F_6bd14 : fetch_word Ubsan.M.loaded_segments (0x6bd54 : word) = Some W_6bd14.
Proof. vm_refl. Qed.
Lemma D_6bd14 : decode_any W_6bd14 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bd18 : bv 32 := 0x01413823.
Lemma F_6bd18 : fetch_word Ubsan.M.loaded_segments (0x6bd58 : word) = Some W_6bd18.
Proof. vm_refl. Qed.
Lemma D_6bd18 : decode_any W_6bd18 = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bd1c : bv 32 := 0x01513423.
Lemma F_6bd1c : fetch_word Ubsan.M.loaded_segments (0x6bd5c : word) = Some W_6bd1c.
Proof. vm_refl. Qed.
Lemma D_6bd1c : decode_any W_6bd1c = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bd20 : bv 32 := 0x01613023.
Lemma F_6bd20 : fetch_word Ubsan.M.loaded_segments (0x6bd60 : word) = Some W_6bd20.
Proof. vm_refl. Qed.
Lemma D_6bd20 : decode_any W_6bd20 = Some (Store SZ8 2 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bd24 : bv 32 := 0x00050493.
Lemma F_6bd24 : fetch_word Ubsan.M.loaded_segments (0x6bd64 : word) = Some W_6bd24.
Proof. vm_refl. Qed.
Lemma D_6bd24 : decode_any W_6bd24 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bd28 : bv 32 := 0x00053403.
Lemma F_6bd28 : fetch_word Ubsan.M.loaded_segments (0x6bd68 : word) = Some W_6bd28.
Proof. vm_refl. Qed.
Lemma D_6bd28 : decode_any W_6bd28 = Some (Load SZ8 true 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bd2c : bv 32 := 0x00853503.
Lemma F_6bd2c : fetch_word Ubsan.M.loaded_segments (0x6bd6c : word) = Some W_6bd2c.
Proof. vm_refl. Qed.
Lemma D_6bd2c : decode_any W_6bd2c = Some (Load SZ8 true 10 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bd30 : bv 32 := 0xccccd637.
Lemma F_6bd30 : fetch_word Ubsan.M.loaded_segments (0x6bd70 : word) = Some W_6bd30.
Proof. vm_refl. Qed.
Lemma D_6bd30 : decode_any W_6bd30 = Some (Lui 12 838861, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bd34 : bv 32 := 0xfffa9717.
Lemma F_6bd34 : fetch_word Ubsan.M.loaded_segments (0x6bd74 : word) = Some W_6bd34.
Proof. vm_refl. Qed.
Lemma D_6bd34 : decode_any W_6bd34 = Some (Auipc 14 1048489, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bd38 : bv 32 := 0xccd6069b.
Lemma F_6bd38 : fetch_word Ubsan.M.loaded_segments (0x6bd78 : word) = Some W_6bd38.
Proof. vm_refl. Qed.
Lemma D_6bd38 : decode_any W_6bd38 = Some (OpImm32 13 12 3277, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bd3c : bv 32 := 0x02069613.
Lemma F_6bd3c : fetch_word Ubsan.M.loaded_segments (0x6bd7c : word) = Some W_6bd3c.
Proof. vm_refl. Qed.
Lemma D_6bd3c : decode_any W_6bd3c = Some (ShiftImm ALU_SLL 12 13 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bd40 : bv 32 := 0x00c686b3.
Lemma F_6bd40 : fetch_word Ubsan.M.loaded_segments (0x6bd80 : word) = Some W_6bd40.
Proof. vm_refl. Qed.
Lemma D_6bd40 : decode_any W_6bd40 = Some (Op ALU_ADD 13 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bd44 : bv 32 := 0x408509b3.
Lemma F_6bd44 : fetch_word Ubsan.M.loaded_segments (0x6bd84 : word) = Some W_6bd44.
Proof. vm_refl. Qed.
Lemma D_6bd44 : decode_any W_6bd44 = Some (Op ALU_SUB 19 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bd48 : bv 32 := 0xbe473503.
Lemma F_6bd48 : fetch_word Ubsan.M.loaded_segments (0x6bd88 : word) = Some W_6bd48.
Proof. vm_refl. Qed.
Lemma D_6bd48 : decode_any W_6bd48 = Some (Load SZ8 true 10 14 3044, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bd4c : bv 32 := 0x4029d613.
Lemma F_6bd4c : fetch_word Ubsan.M.loaded_segments (0x6bd8c : word) = Some W_6bd4c.
Proof. vm_refl. Qed.
Lemma D_6bd4c : decode_any W_6bd4c = Some (ShiftImm ALU_SRA 12 19 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bd50 : bv 32 := 0x02d60633.
Lemma F_6bd50 : fetch_word Ubsan.M.loaded_segments (0x6bd90 : word) = Some W_6bd50.
Proof. vm_refl. Qed.
Lemma D_6bd50 : decode_any W_6bd50 = Some (Mul M_MUL 12 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bd54 : bv 32 := 0x00160613.
Lemma F_6bd54 : fetch_word Ubsan.M.loaded_segments (0x6bd94 : word) = Some W_6bd54.
Proof. vm_refl. Qed.
Lemma D_6bd54 : decode_any W_6bd54 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bd58 : bv 32 := 0x16a67463.
Lemma F_6bd58 : fetch_word Ubsan.M.loaded_segments (0x6bd98 : word) = Some W_6bd58.
Proof. vm_refl. Qed.
Lemma D_6bd58 : decode_any W_6bd58 = Some (Branch BC_GEU 12 10 360, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bd5c : bv 32 := 0x00058a13.
Lemma F_6bd5c : fetch_word Ubsan.M.loaded_segments (0x6bd9c : word) = Some W_6bd5c.
Proof. vm_refl. Qed.
Lemma D_6bd5c : decode_any W_6bd5c = Some (OpImm ALU_ADD 20 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bd60 : bv 32 := 0x0104b583.
Lemma F_6bd60 : fetch_word Ubsan.M.loaded_segments (0x6bda0 : word) = Some W_6bd60.
Proof. vm_refl. Qed.
Lemma D_6bd60 : decode_any W_6bd60 = Some (Load SZ8 true 11 9 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bd64 : bv 32 := 0x40858933.
Lemma F_6bd64 : fetch_word Ubsan.M.loaded_segments (0x6bda4 : word) = Some W_6bd64.
Proof. vm_refl. Qed.
Lemma D_6bd64 : decode_any W_6bd64 = Some (Op ALU_SUB 18 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bd68 : bv 32 := 0x40295593.
Lemma F_6bd68 : fetch_word Ubsan.M.loaded_segments (0x6bda8 : word) = Some W_6bd68.
Proof. vm_refl. Qed.
Lemma D_6bd68 : decode_any W_6bd68 = Some (ShiftImm ALU_SRA 11 18 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bd6c : bv 32 := 0x02d585b3.
Lemma F_6bd6c : fetch_word Ubsan.M.loaded_segments (0x6bdac : word) = Some W_6bd6c.
Proof. vm_refl. Qed.
Lemma D_6bd6c : decode_any W_6bd6c = Some (Mul M_MUL 11 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bd70 : bv 32 := 0x00159a93.
Lemma F_6bd70 : fetch_word Ubsan.M.loaded_segments (0x6bdb0 : word) = Some W_6bd70.
Proof. vm_refl. Qed.
Lemma D_6bd70 : decode_any W_6bd70 = Some (ShiftImm ALU_SLL 21 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bd74 : bv 32 := 0x01566463.
Lemma F_6bd74 : fetch_word Ubsan.M.loaded_segments (0x6bdb4 : word) = Some W_6bd74.
Proof. vm_refl. Qed.
Lemma D_6bd74 : decode_any W_6bd74 = Some (Branch BC_LTU 12 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bd78 : bv 32 := 0x00060a93.
Lemma F_6bd78 : fetch_word Ubsan.M.loaded_segments (0x6bdb8 : word) = Some W_6bd78.
Proof. vm_refl. Qed.
Lemma D_6bd78 : decode_any W_6bd78 = Some (OpImm ALU_ADD 21 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bd7c : bv 32 := 0xfffa9617.
Lemma F_6bd7c : fetch_word Ubsan.M.loaded_segments (0x6bdbc : word) = Some W_6bd7c.
Proof. vm_refl. Qed.
Lemma D_6bd7c : decode_any W_6bd7c = Some (Auipc 12 1048489, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bd80 : bv 32 := 0xbec63603.
Lemma F_6bd80 : fetch_word Ubsan.M.loaded_segments (0x6bdc0 : word) = Some W_6bd80.
Proof. vm_refl. Qed.
Lemma D_6bd80 : decode_any W_6bd80 = Some (Load SZ8 true 12 12 3052, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bd84 : bv 32 := 0x00c5e663.
Lemma F_6bd84 : fetch_word Ubsan.M.loaded_segments (0x6bdc4 : word) = Some W_6bd84.
Proof. vm_refl. Qed.
Lemma D_6bd84 : decode_any W_6bd84 = Some (Branch BC_LTU 11 12 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bd90 : bv 32 := 0x020a8063.
Lemma F_6bd90 : fetch_word Ubsan.M.loaded_segments (0x6bdd0 : word) = Some W_6bd90.
Proof. vm_refl. Qed.
Lemma D_6bd90 : decode_any W_6bd90 = Some (Branch BC_EQ 21 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bd94 : bv 32 := 0x12aafa63.
Lemma F_6bd94 : fetch_word Ubsan.M.loaded_segments (0x6bdd4 : word) = Some W_6bd94.
Proof. vm_refl. Qed.
Lemma D_6bd94 : decode_any W_6bd94 = Some (Branch BC_GEU 21 10 308, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bd98 : bv 32 := 0x01400513.
Lemma F_6bd98 : fetch_word Ubsan.M.loaded_segments (0x6bdd8 : word) = Some W_6bd98.
Proof. vm_refl. Qed.
Lemma D_6bd98 : decode_any W_6bd98 = Some (OpImm ALU_ADD 10 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bd9c : bv 32 := 0x02aa8533.
Lemma F_6bd9c : fetch_word Ubsan.M.loaded_segments (0x6bddc : word) = Some W_6bd9c.
Proof. vm_refl. Qed.
Lemma D_6bd9c : decode_any W_6bd9c = Some (Mul M_MUL 10 21 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bda0 : bv 32 := 0x5557b0ef.
Lemma F_6bda0 : fetch_word Ubsan.M.loaded_segments (0x6bde0 : word) = Some W_6bda0.
Proof. vm_refl. Qed.
Lemma D_6bda0 : decode_any W_6bda0 = Some (Jal 1 507220, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bda4 : bv 32 := 0x013505b3.
Lemma F_6bda4 : fetch_word Ubsan.M.loaded_segments (0x6bde4 : word) = Some W_6bda4.
Proof. vm_refl. Qed.
Lemma D_6bda4 : decode_any W_6bda4 = Some (Op ALU_ADD 11 10 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bda8 : bv 32 := 0x00a5fa63.
Lemma F_6bda8 : fetch_word Ubsan.M.loaded_segments (0x6bde8 : word) = Some W_6bda8.
Proof. vm_refl. Qed.
Lemma D_6bda8 : decode_any W_6bda8 = Some (Branch BC_GEU 11 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bdbc : bv 32 := 0x00a03733.
Lemma F_6bdbc : fetch_word Ubsan.M.loaded_segments (0x6bdfc : word) = Some W_6bdbc.
Proof. vm_refl. Qed.
Lemma D_6bdbc : decode_any W_6bdbc = Some (Op ALU_SLTU 14 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bdc0 : bv 32 := 0x0015b613.
Lemma F_6bdc0 : fetch_word Ubsan.M.loaded_segments (0x6be00 : word) = Some W_6bdc0.
Proof. vm_refl. Qed.
Lemma D_6bdc0 : decode_any W_6bdc0 = Some (OpImm ALU_SLTU 12 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bdc4 : bv 32 := 0x00c74633.
Lemma F_6bdc4 : fetch_word Ubsan.M.loaded_segments (0x6be04 : word) = Some W_6bdc4.
Proof. vm_refl. Qed.
Lemma D_6bdc4 : decode_any W_6bdc4 = Some (Op ALU_XOR 12 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bdc8 : bv 32 := 0x10060263.
Lemma F_6bdc8 : fetch_word Ubsan.M.loaded_segments (0x6be08 : word) = Some W_6bdc8.
Proof. vm_refl. Qed.
Lemma D_6bdc8 : decode_any W_6bdc8 = Some (Branch BC_EQ 12 0 260, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bdcc : bv 32 := 0x01400613.
Lemma F_6bdcc : fetch_word Ubsan.M.loaded_segments (0x6be0c : word) = Some W_6bdcc.
Proof. vm_refl. Qed.
Lemma D_6bdcc : decode_any W_6bdcc = Some (OpImm ALU_ADD 12 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bdd0 : bv 32 := 0x02ca86b3.
Lemma F_6bdd0 : fetch_word Ubsan.M.loaded_segments (0x6be10 : word) = Some W_6bdd0.
Proof. vm_refl. Qed.
Lemma D_6bdd0 : decode_any W_6bdd0 = Some (Mul M_MUL 13 21 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bdd4 : bv 32 := 0x00a687b3.
Lemma F_6bdd4 : fetch_word Ubsan.M.loaded_segments (0x6be14 : word) = Some W_6bdd4.
Proof. vm_refl. Qed.
Lemma D_6bdd4 : decode_any W_6bdd4 = Some (Op ALU_ADD 15 13 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bdd8 : bv 32 := 0x0017b813.
Lemma F_6bdd8 : fetch_word Ubsan.M.loaded_segments (0x6be18 : word) = Some W_6bdd8.
Proof. vm_refl. Qed.
Lemma D_6bdd8 : decode_any W_6bdd8 = Some (OpImm ALU_SLTU 16 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bddc : bv 32 := 0x0f070863.
Lemma F_6bddc : fetch_word Ubsan.M.loaded_segments (0x6be1c : word) = Some W_6bddc.
Proof. vm_refl. Qed.
Lemma D_6bddc : decode_any W_6bddc = Some (Branch BC_EQ 14 16 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bde0 : bv 32 := 0x0ea7e663.
Lemma F_6bde0 : fetch_word Ubsan.M.loaded_segments (0x6be20 : word) = Some W_6bde0.
Proof. vm_refl. Qed.
Lemma D_6bde0 : decode_any W_6bde0 = Some (Branch BC_LTU 15 10 236, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bde4 : bv 32 := 0x02ca9633.
Lemma F_6bde4 : fetch_word Ubsan.M.loaded_segments (0x6be24 : word) = Some W_6bde4.
Proof. vm_refl. Qed.
Lemma D_6bde4 : decode_any W_6bde4 = Some (Mul M_MULH 12 21 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bde8 : bv 32 := 0x43f6d693.
Lemma F_6bde8 : fetch_word Ubsan.M.loaded_segments (0x6be28 : word) = Some W_6bde8.
Proof. vm_refl. Qed.
Lemma D_6bde8 : decode_any W_6bde8 = Some (ShiftImm ALU_SRA 13 13 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bdec : bv 32 := 0x00d64633.
Lemma F_6bdec : fetch_word Ubsan.M.loaded_segments (0x6be2c : word) = Some W_6bdec.
Proof. vm_refl. Qed.
Lemma D_6bdec : decode_any W_6bdec = Some (Op ALU_XOR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bdf0 : bv 32 := 0x00c03633.
Lemma F_6bdf0 : fetch_word Ubsan.M.loaded_segments (0x6be30 : word) = Some W_6bdf0.
Proof. vm_refl. Qed.
Lemma D_6bdf0 : decode_any W_6bdf0 = Some (Op ALU_SLTU 12 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bdf4 : bv 32 := 0x0c061c63.
Lemma F_6bdf4 : fetch_word Ubsan.M.loaded_segments (0x6be34 : word) = Some W_6bdf4.
Proof. vm_refl. Qed.
Lemma D_6bdf4 : decode_any W_6bdf4 = Some (Branch BC_NE 12 0 216, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bdf8 : bv 32 := 0x0035f613.
Lemma F_6bdf8 : fetch_word Ubsan.M.loaded_segments (0x6be38 : word) = Some W_6bdf8.
Proof. vm_refl. Qed.
Lemma D_6bdf8 : decode_any W_6bdf8 = Some (OpImm ALU_AND 12 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bdfc : bv 32 := 0x0c061863.
Lemma F_6bdfc : fetch_word Ubsan.M.loaded_segments (0x6be3c : word) = Some W_6bdfc.
Proof. vm_refl. Qed.
Lemma D_6bdfc : decode_any W_6bdfc = Some (Branch BC_NE 12 0 208, 4%Z).
Proof. vm_refl. Qed.

Definition W_6be00 : bv 32 := 0x0c050663.
Lemma F_6be00 : fetch_word Ubsan.M.loaded_segments (0x6be40 : word) = Some W_6be00.
Proof. vm_refl. Qed.
Lemma D_6be00 : decode_any W_6be00 = Some (Branch BC_EQ 10 0 204, 4%Z).
Proof. vm_refl. Qed.

Definition W_6be04 : bv 32 := 0x010a2603.
Lemma F_6be04 : fetch_word Ubsan.M.loaded_segments (0x6be44 : word) = Some W_6be04.
Proof. vm_refl. Qed.
Lemma D_6be04 : decode_any W_6be04 = Some (Load SZ4 true 12 20 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6be08 : bv 32 := 0x000a2683.
Lemma F_6be08 : fetch_word Ubsan.M.loaded_segments (0x6be48 : word) = Some W_6be08.
Proof. vm_refl. Qed.
Lemma D_6be08 : decode_any W_6be08 = Some (Load SZ4 true 13 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6be0c : bv 32 := 0x004a2703.
Lemma F_6be0c : fetch_word Ubsan.M.loaded_segments (0x6be4c : word) = Some W_6be0c.
Proof. vm_refl. Qed.
Lemma D_6be0c : decode_any W_6be0c = Some (Load SZ4 true 14 20 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_6be10 : bv 32 := 0x008a2783.
Lemma F_6be10 : fetch_word Ubsan.M.loaded_segments (0x6be50 : word) = Some W_6be10.
Proof. vm_refl. Qed.
Lemma D_6be10 : decode_any W_6be10 = Some (Load SZ4 true 15 20 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6be14 : bv 32 := 0x00ca2803.
Lemma F_6be14 : fetch_word Ubsan.M.loaded_segments (0x6be54 : word) = Some W_6be14.
Proof. vm_refl. Qed.
Lemma D_6be14 : decode_any W_6be14 = Some (Load SZ4 true 16 20 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6be18 : bv 32 := 0x00c5a823.
Lemma F_6be18 : fetch_word Ubsan.M.loaded_segments (0x6be58 : word) = Some W_6be18.
Proof. vm_refl. Qed.
Lemma D_6be18 : decode_any W_6be18 = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6be1c : bv 32 := 0xfec00613.
Lemma F_6be1c : fetch_word Ubsan.M.loaded_segments (0x6be5c : word) = Some W_6be1c.
Proof. vm_refl. Qed.
Lemma D_6be1c : decode_any W_6be1c = Some (OpImm ALU_ADD 12 0 4076, 4%Z).
Proof. vm_refl. Qed.

Definition W_6be20 : bv 32 := 0x00d5a023.
Lemma F_6be20 : fetch_word Ubsan.M.loaded_segments (0x6be60 : word) = Some W_6be20.
Proof. vm_refl. Qed.
Lemma D_6be20 : decode_any W_6be20 = Some (Store SZ4 11 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6be24 : bv 32 := 0x00e5a223.
Lemma F_6be24 : fetch_word Ubsan.M.loaded_segments (0x6be64 : word) = Some W_6be24.
Proof. vm_refl. Qed.
Lemma D_6be24 : decode_any W_6be24 = Some (Store SZ4 11 14 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_6be28 : bv 32 := 0x00f5a423.
Lemma F_6be28 : fetch_word Ubsan.M.loaded_segments (0x6be68 : word) = Some W_6be28.
Proof. vm_refl. Qed.
Lemma D_6be28 : decode_any W_6be28 = Some (Store SZ4 11 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6be2c : bv 32 := 0x0105a623.
Lemma F_6be2c : fetch_word Ubsan.M.loaded_segments (0x6be6c : word) = Some W_6be2c.
Proof. vm_refl. Qed.
Lemma D_6be2c : decode_any W_6be2c = Some (Store SZ4 11 16 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6be30 : bv 32 := 0x08c5fe63.
Lemma F_6be30 : fetch_word Ubsan.M.loaded_segments (0x6be70 : word) = Some W_6be30.
Proof. vm_refl. Qed.
Lemma D_6be30 : decode_any W_6be30 = Some (Branch BC_GEU 11 12 156, 4%Z).
Proof. vm_refl. Qed.

Definition W_6be34 : bv 32 := 0x41358a33.
Lemma F_6be34 : fetch_word Ubsan.M.loaded_segments (0x6be74 : word) = Some W_6be34.
Proof. vm_refl. Qed.
Lemma D_6be34 : decode_any W_6be34 = Some (Op ALU_SUB 20 11 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_6be38 : bv 32 := 0x080a0a63.
Lemma F_6be38 : fetch_word Ubsan.M.loaded_segments (0x6be78 : word) = Some W_6be38.
Proof. vm_refl. Qed.
Lemma D_6be38 : decode_any W_6be38 = Some (Branch BC_EQ 20 0 148, 4%Z).
Proof. vm_refl. Qed.

Definition W_6be3c : bv 32 := 0x00ba3633.
Lemma F_6be3c : fetch_word Ubsan.M.loaded_segments (0x6be7c : word) = Some W_6be3c.
Proof. vm_refl. Qed.
Lemma D_6be3c : decode_any W_6be3c = Some (Op ALU_SLTU 12 20 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_6be40 : bv 32 := 0x013026b3.
Lemma F_6be40 : fetch_word Ubsan.M.loaded_segments (0x6be80 : word) = Some W_6be40.
Proof. vm_refl. Qed.
Lemma D_6be40 : decode_any W_6be40 = Some (Op ALU_SLT 13 0 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_6be44 : bv 32 := 0x00d64633.
Lemma F_6be44 : fetch_word Ubsan.M.loaded_segments (0x6be84 : word) = Some W_6be44.
Proof. vm_refl. Qed.
Lemma D_6be44 : decode_any W_6be44 = Some (Op ALU_XOR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_6be48 : bv 32 := 0x00164613.
Lemma F_6be48 : fetch_word Ubsan.M.loaded_segments (0x6be88 : word) = Some W_6be48.
Proof. vm_refl. Qed.
Lemma D_6be48 : decode_any W_6be48 = Some (OpImm ALU_XOR 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6be4c : bv 32 := 0x08060063.
Lemma F_6be4c : fetch_word Ubsan.M.loaded_segments (0x6be8c : word) = Some W_6be4c.
Proof. vm_refl. Qed.
Lemma D_6be4c : decode_any W_6be4c = Some (Branch BC_EQ 12 0 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_6be50 : bv 32 := 0x00347613.
Lemma F_6be50 : fetch_word Ubsan.M.loaded_segments (0x6be90 : word) = Some W_6be50.
Proof. vm_refl. Qed.
Lemma D_6be50 : decode_any W_6be50 = Some (OpImm ALU_AND 12 8 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_6be54 : bv 32 := 0x06061c63.
Lemma F_6be54 : fetch_word Ubsan.M.loaded_segments (0x6be94 : word) = Some W_6be54.
Proof. vm_refl. Qed.
Lemma D_6be54 : decode_any W_6be54 = Some (Branch BC_NE 12 0 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_6be58 : bv 32 := 0x01400613.
Lemma F_6be58 : fetch_word Ubsan.M.loaded_segments (0x6be98 : word) = Some W_6be58.
Proof. vm_refl. Qed.
Lemma D_6be58 : decode_any W_6be58 = Some (OpImm ALU_ADD 12 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_6be5c : bv 32 := 0x02ca8633.
Lemma F_6be5c : fetch_word Ubsan.M.loaded_segments (0x6be9c : word) = Some W_6be5c.
Proof. vm_refl. Qed.
Lemma D_6be5c : decode_any W_6be5c = Some (Mul M_MUL 12 21 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6be60 : bv 32 := 0x00c50b33.
Lemma F_6be60 : fetch_word Ubsan.M.loaded_segments (0x6bea0 : word) = Some W_6be60.
Proof. vm_refl. Qed.
Lemma D_6be60 : decode_any W_6be60 = Some (Op ALU_ADD 22 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6be64 : bv 32 := 0x01458a93.
Lemma F_6be64 : fetch_word Ubsan.M.loaded_segments (0x6bea4 : word) = Some W_6be64.
Proof. vm_refl. Qed.
Lemma D_6be64 : decode_any W_6be64 = Some (OpImm ALU_ADD 21 11 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_6be68 : bv 32 := 0x000a0513.
Lemma F_6be68 : fetch_word Ubsan.M.loaded_segments (0x6bea8 : word) = Some W_6be68.
Proof. vm_refl. Qed.
Lemma D_6be68 : decode_any W_6be68 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6be6c : bv 32 := 0x00040593.
Lemma F_6be6c : fetch_word Ubsan.M.loaded_segments (0x6beac : word) = Some W_6be6c.
Proof. vm_refl. Qed.
Lemma D_6be6c : decode_any W_6be6c = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6be70 : bv 32 := 0x00098613.
Lemma F_6be70 : fetch_word Ubsan.M.loaded_segments (0x6beb0 : word) = Some W_6be70.
Proof. vm_refl. Qed.
Lemma D_6be70 : decode_any W_6be70 = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6be74 : bv 32 := 0x4e9760ef.
Lemma F_6be74 : fetch_word Ubsan.M.loaded_segments (0x6beb4 : word) = Some W_6be74.
Proof. vm_refl. Qed.
Lemma D_6be74 : decode_any W_6be74 = Some (Jal 1 486632, 4%Z).
Proof. vm_refl. Qed.

Definition W_6be78 : bv 32 := 0x0144b023.
Lemma F_6be78 : fetch_word Ubsan.M.loaded_segments (0x6beb8 : word) = Some W_6be78.
Proof. vm_refl. Qed.
Lemma D_6be78 : decode_any W_6be78 = Some (Store SZ8 9 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6be7c : bv 32 := 0x0154b423.
Lemma F_6be7c : fetch_word Ubsan.M.loaded_segments (0x6bebc : word) = Some W_6be7c.
Proof. vm_refl. Qed.
Lemma D_6be7c : decode_any W_6be7c = Some (Store SZ8 9 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6be80 : bv 32 := 0x0164b823.
Lemma F_6be80 : fetch_word Ubsan.M.loaded_segments (0x6bec0 : word) = Some W_6be80.
Proof. vm_refl. Qed.
Lemma D_6be80 : decode_any W_6be80 = Some (Store SZ8 9 22 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6be84 : bv 32 := 0x00040863.
Lemma F_6be84 : fetch_word Ubsan.M.loaded_segments (0x6bec4 : word) = Some W_6be84.
Proof. vm_refl. Qed.
Lemma D_6be84 : decode_any W_6be84 = Some (Branch BC_EQ 8 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6be88 : bv 32 := 0x00040513.
Lemma F_6be88 : fetch_word Ubsan.M.loaded_segments (0x6bec8 : word) = Some W_6be88.
Proof. vm_refl. Qed.
Lemma D_6be88 : decode_any W_6be88 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6be8c : bv 32 := 0x00090593.
Lemma F_6be8c : fetch_word Ubsan.M.loaded_segments (0x6becc : word) = Some W_6be8c.
Proof. vm_refl. Qed.
Lemma D_6be8c : decode_any W_6be8c = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6be90 : bv 32 := 0x1fd030ef.
Lemma F_6be90 : fetch_word Ubsan.M.loaded_segments (0x6bed0 : word) = Some W_6be90.
Proof. vm_refl. Qed.
Lemma D_6be90 : decode_any W_6be90 = Some (Jal 1 14844, 4%Z).
Proof. vm_refl. Qed.

Definition W_6be94 : bv 32 := 0x000a8513.
Lemma F_6be94 : fetch_word Ubsan.M.loaded_segments (0x6bed4 : word) = Some W_6be94.
Proof. vm_refl. Qed.
Lemma D_6be94 : decode_any W_6be94 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6be98 : bv 32 := 0x03813083.
Lemma F_6be98 : fetch_word Ubsan.M.loaded_segments (0x6bed8 : word) = Some W_6be98.
Proof. vm_refl. Qed.
Lemma D_6be98 : decode_any W_6be98 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_6be9c : bv 32 := 0x03013403.
Lemma F_6be9c : fetch_word Ubsan.M.loaded_segments (0x6bedc : word) = Some W_6be9c.
Proof. vm_refl. Qed.
Lemma D_6be9c : decode_any W_6be9c = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bea0 : bv 32 := 0x02813483.
Lemma F_6bea0 : fetch_word Ubsan.M.loaded_segments (0x6bee0 : word) = Some W_6bea0.
Proof. vm_refl. Qed.
Lemma D_6bea0 : decode_any W_6bea0 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bea4 : bv 32 := 0x02013903.
Lemma F_6bea4 : fetch_word Ubsan.M.loaded_segments (0x6bee4 : word) = Some W_6bea4.
Proof. vm_refl. Qed.
Lemma D_6bea4 : decode_any W_6bea4 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bea8 : bv 32 := 0x01813983.
Lemma F_6bea8 : fetch_word Ubsan.M.loaded_segments (0x6bee8 : word) = Some W_6bea8.
Proof. vm_refl. Qed.
Lemma D_6bea8 : decode_any W_6bea8 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_6beac : bv 32 := 0x01013a03.
Lemma F_6beac : fetch_word Ubsan.M.loaded_segments (0x6beec : word) = Some W_6beac.
Proof. vm_refl. Qed.
Lemma D_6beac : decode_any W_6beac = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6beb0 : bv 32 := 0x00813a83.
Lemma F_6beb0 : fetch_word Ubsan.M.loaded_segments (0x6bef0 : word) = Some W_6beb0.
Proof. vm_refl. Qed.
Lemma D_6beb0 : decode_any W_6beb0 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6beb4 : bv 32 := 0x00013b03.
Lemma F_6beb4 : fetch_word Ubsan.M.loaded_segments (0x6bef4 : word) = Some W_6beb4.
Proof. vm_refl. Qed.
Lemma D_6beb4 : decode_any W_6beb4 = Some (Load SZ8 true 22 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6beb8 : bv 32 := 0x04010113.
Lemma F_6beb8 : fetch_word Ubsan.M.loaded_segments (0x6bef8 : word) = Some W_6beb8.
Proof. vm_refl. Qed.
Lemma D_6beb8 : decode_any W_6beb8 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_6bebc : bv 32 := 0x00008067.
Lemma F_6bebc : fetch_word Ubsan.M.loaded_segments (0x6befc : word) = Some W_6bebc.
Proof. vm_refl. Qed.
Lemma D_6bebc : decode_any W_6bebc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
End U1_code_6bd00_6bed0.
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
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContLib ContStmts U1Facts ContStmts2 U1Lib_Cxx_OperatorDelete.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.U1Lib_VecOpnd_PbSlow.U1_code_6bd00_6bed0.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PeLia.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Local Ltac lia ::= pe3_lia.
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

Lemma step_mulh_at {fx : FPState} : forall segs regs pc mem rom w rd rs1 rs2 v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Mul M_MULH rd rs1 rs2, 4%Z) -> bv_eqb rd 0 = false ->
  v_mulh (getr regs rs1) (getr regs rs2) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) = MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof. intros segs regs pc mem rom w rd rs1 rs2 v Hf He Hd Hrd Hv. rewrite (step_mulh segs regs pc mem rom w rd rs1 rs2 Hf He Hd). rewrite Hrd, Hv. reflexivity. Qed.
Lemma v_mulh_small : forall a b, 0 <= a < 2 ^ 63 -> 0 <= b < 2 ^ 63 -> a * b < 2 ^ 64 -> v_mulh (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 0.
Proof.
  intros a b Ha Hb Hab. unfold v_mulh. rewrite !bv_signed_small64 by lia. rewrite Z.shiftr_div_pow2 by lia.
  rewrite Z.div_small by lia. reflexivity.
Qed.

Definition K_MAXP1 : Z := 0x14958.
Definition K_HALF  : Z := 0x149a8.
Definition K_MAX   : Z := 0x14970.
Lemma img_K_MAXP1 : rdn SEGS (fun _ => None) (Z_to_bv 64 K_MAXP1) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x0ccccccccccccccd)).
Proof. vm_refl_bv. Qed.
Lemma img_K_HALF : rdn SEGS (fun _ => None) (Z_to_bv 64 K_HALF) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x0666666666666666)).
Proof. vm_refl_bv. Qed.

Section OpndPbSlow.
Context {AC : AllocCeiling}.
  Variable MI : MallocIface SEGS Ly.L.
  Variable ST : StaticsIface SEGS Ly.L.
  Hypothesis MALLOC_STACK_pos : (0 <= MALLOC_STACK MI)%Z.
  Hypothesis NEW : new_rule_stmt SEGS Ly.L MI ST (NEW_STACK SEGS Ly.L MI).

  #[local] Notation placed_sep := (placed_sep SEGS Ly.L MI ly_img_low ly_rw_img).
  #[local] Notation stack_sep := (stack_sep SEGS Ly.L MI ly_img_low ly_rw_img).
  #[local] Notation offimg_sep := (offimg_sep SEGS Ly.L ST ly_rw_img ly_relro_img ly_errno_img).

  Definition u1c6bc9c : vec_consts := {| vc_entry := 0x6bd40; vc_stack := 64 |}.

  Definition PRO_vals (R : bvmap 5 word) (ret : Z) : list word :=
    [getr R 22%bv; getr R 21%bv; getr R 20%bv; getr R 19%bv; getr R 18%bv; getr R 9%bv; getr R 8%bv; Z_to_bv 64 ret].

  Lemma LA : forall (fx : FPState) R M (sp ret v b cap src : Z),
    getr R 1%bv = Z_to_bv 64 ret -> getr R 2%bv = Z_to_bv 64 sp -> getr R 10%bv = Z_to_bv 64 v -> getr R 11%bv = Z_to_bv 64 src ->
    0 <= cap < 2 ^ 40 -> 0 <= b -> b + 20 * cap <= 2 ^ 63 -> 2 ^ 20 <= sp - 64 -> sp < 2 ^ 47 -> 0 <= v -> v + 24 <= 2 ^ 63 ->
    (v + 24 <= sp - 64 \/ sp <= v) ->
    store_ok SEGS M (Z_to_bv 64 (sp - 64)) 64 = true ->
    rdn SEGS M (Z_to_bv 64 v) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 b)) ->
    rdn SEGS M (Z_to_bv 64 (v + 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (b + 20 * cap))) ->
    rdn SEGS M (Z_to_bv 64 (v + 16)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (b + 20 * cap))) ->
    rdn SEGS M (Z_to_bv 64 K_MAXP1) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x0ccccccccccccccd)) ->
    rdn SEGS M (Z_to_bv 64 K_HALF) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x0666666666666666)) ->
    exists Rn,
      msteps SEGS (@mkst fx R (Z_to_bv 64 0x6bd40) M (seg_rom SEGS)) (@mkst fx Rn (Z_to_bv 64 (ly_new Ly.L)) (wslots M sp (PRO_vals R ret)) (seg_rom SEGS))
      /\ getr Rn 10%bv = Z_to_bv 64 (20 * vgrow cap) /\ getr Rn 1%bv = Z_to_bv 64 0x6bde4 /\ getr Rn 2%bv = Z_to_bv 64 (sp - 64)
      /\ getr Rn 8%bv = Z_to_bv 64 b /\ getr Rn 9%bv = Z_to_bv 64 v /\ getr Rn 18%bv = Z_to_bv 64 (20 * cap) /\ getr Rn 19%bv = Z_to_bv 64 (20 * cap)
      /\ getr Rn 20%bv = Z_to_bv 64 src /\ getr Rn 21%bv = Z_to_bv 64 (vgrow cap)
      /\ getr Rn 3%bv = getr R 3%bv /\ getr Rn 4%bv = getr R 4%bv
      /\ (forall r, In r [23; 24; 25; 26; 27]%bv -> getr Rn r = getr R r).
  Proof using.
    intros fx R M sp ret v b cap src Hra Hsp Ha0 Ha1 Hcap Hb0 Hbc Hspr Hsphi Hv0 Hv1 WINv HOK F0 F1 F2 K1 K2.
    unfold K_MAXP1 in K1. unfold K_HALF in K2.
    assert (PRO : forall Rx, Rx = regupd (regupd R 2%bv (Z_to_bv 64 (sp - 64))) 9%bv (Z_to_bv 64 v) ->
      msteps SEGS (@mkst fx R (Z_to_bv 64 0x6bd40) M (seg_rom SEGS)) (@mkst fx Rx (Z_to_bv 64 0x6bd68) (wslots M sp (PRO_vals R ret)) (seg_rom SEGS))).
    { intros Rx ->. norm_pc.
      sv F_6bd00 D_6bd00 (Z_to_bv 64 (sp - 64)).
      stw F_6bd04 D_6bd04 (Z_to_bv 64 (sp - 8)) (Z_to_bv 64 ret) ltac:(ok_sub HOK).
      stw F_6bd08 D_6bd08 (Z_to_bv 64 (sp - 16)) (getr R 8%bv) ltac:(ok_sub HOK).
      stw F_6bd0c D_6bd0c (Z_to_bv 64 (sp - 24)) (getr R 9%bv) ltac:(ok_sub HOK).
      stw F_6bd10 D_6bd10 (Z_to_bv 64 (sp - 32)) (getr R 18%bv) ltac:(ok_sub HOK).
      stw F_6bd14 D_6bd14 (Z_to_bv 64 (sp - 40)) (getr R 19%bv) ltac:(ok_sub HOK).
      stw F_6bd18 D_6bd18 (Z_to_bv 64 (sp - 48)) (getr R 20%bv) ltac:(ok_sub HOK).
      stw F_6bd1c D_6bd1c (Z_to_bv 64 (sp - 56)) (getr R 21%bv) ltac:(ok_sub HOK).
      stw F_6bd20 D_6bd20 (Z_to_bv 64 (sp - 64)) (getr R 22%bv) ltac:(ok_sub HOK).
      sv F_6bd24 D_6bd24 (Z_to_bv 64 v).
      lazymatch goal with |- msteps _ ?a ?bb => replace bb with a; [apply mst_refl|] end.
      f_equal. apply bv_eq; reflexivity. }
    assert (WO : forall a k bs, rdn SEGS M (Z_to_bv 64 a) k = Some bs -> 0 <= a -> a + Z.of_nat k < 2 ^ 64 -> (a + Z.of_nat k <= sp - 64 \/ sp <= a) ->
                 rdn SEGS (wslots M sp (PRO_vals R ret)) (Z_to_bv 64 a) k = Some bs).
    { intros a k bs H Ha Hk Hd. rewrite wslots_out; [exact H | unfold Zlen; cbn; lia | lia | lia | lia | unfold Zlen; cbn; lia]. }
    pose proof (WO _ _ _ F0 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia)) as F0'. pose proof (WO _ _ _ F1 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia)) as F1'.
    pose proof (WO _ _ _ F2 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia)) as F2'.
    pose proof (WO _ _ _ K1 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia)) as K1'. pose proof (WO _ _ _ K2 ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia)) as K2'.

    assert (PRE : forall Rx, Rx = regupd (regupd R 2%bv (Z_to_bv 64 (sp - 64))) 9%bv (Z_to_bv 64 v) -> exists Ry,
      msteps SEGS (@mkst fx Rx (Z_to_bv 64 0x6bd68) (wslots M sp (PRO_vals R ret)) (seg_rom SEGS))
                  (@mkst fx Ry (Z_to_bv 64 0x6bdb4) (wslots M sp (PRO_vals R ret)) (seg_rom SEGS))
      /\ getr Ry 8%bv = Z_to_bv 64 b /\ getr Ry 9%bv = Z_to_bv 64 v /\ getr Ry 2%bv = Z_to_bv 64 (sp - 64)
      /\ getr Ry 10%bv = Z_to_bv 64 0x0ccccccccccccccd /\ getr Ry 11%bv = Z_to_bv 64 cap /\ getr Ry 12%bv = Z_to_bv 64 (cap + 1)
      /\ getr Ry 18%bv = Z_to_bv 64 (20 * cap) /\ getr Ry 19%bv = Z_to_bv 64 (20 * cap) /\ getr Ry 20%bv = Z_to_bv 64 src /\ getr Ry 21%bv = Z_to_bv 64 (2 * cap)
      /\ getr Ry 3%bv = getr R 3%bv /\ getr Ry 4%bv = getr R 4%bv /\ getr Ry 1%bv = getr R 1%bv
      /\ (forall r, In r [23; 24; 25; 26; 27]%bv -> getr Ry r = getr R r)).
    { intros Rx ->. eexists. split.
      - norm_pc.
        ld_step F_6bd28 D_6bd28 (word_to_le_bytes 8 (Z_to_bv 64 b)) (Z_to_bv 64 b) ltac:(rdn_fix F0') ltac:(b2z8).
        ld_step F_6bd2c D_6bd2c (word_to_le_bytes 8 (Z_to_bv 64 (b + 20 * cap))) (Z_to_bv 64 (b + 20 * cap)) ltac:(rdn_fix F1') ltac:(b2z8).
        snl F_6bd30 D_6bd30. snl F_6bd34 D_6bd34. snl F_6bd38 D_6bd38. snl F_6bd3c D_6bd3c. snl F_6bd40 D_6bd40.
        stepiv F_6bd44 D_6bd44 (Z_to_bv 64 (20 * cap)) ltac:(gres; pin; rewrite v_sub_Z by lia; f_equal; lia).
        ld_step F_6bd48 D_6bd48 (word_to_le_bytes 8 (Z_to_bv 64 0x0ccccccccccccccd)) (Z_to_bv 64 0x0ccccccccccccccd) ltac:(rdn_fix K1') ltac:(b2z8).
        stepiv F_6bd4c D_6bd4c (Z_to_bv 64 (5 * cap)) ltac:(gres; pin; imm_norm; rewrite v_srai_Z by lia; f_equal; change (2^2) with 4; replace (20 * cap) with (5 * cap * 4) by lia; apply Z.div_mul; lia).
        stepiv F_6bd50 D_6bd50 (Z_to_bv 64 cap) ltac:(gres; pin; apply v_mul_inv5; lia).
        stepiv F_6bd54 D_6bd54 (Z_to_bv 64 (cap + 1)) ltac:(gres; pin; imm_norm; rewrite v_addi_Z by lia; reflexivity).
        stepb_ft F_6bd58 D_6bd58 ltac:(cmpz).
        sv F_6bd5c D_6bd5c (Z_to_bv 64 src).
        ld_step F_6bd60 D_6bd60 (word_to_le_bytes 8 (Z_to_bv 64 (b + 20 * cap))) (Z_to_bv 64 (b + 20 * cap)) ltac:(rdn_fix F2') ltac:(b2z8).
        stepiv F_6bd64 D_6bd64 (Z_to_bv 64 (20 * cap)) ltac:(gres; pin; rewrite v_sub_Z by lia; f_equal; lia).
        stepiv F_6bd68 D_6bd68 (Z_to_bv 64 (5 * cap)) ltac:(gres; pin; imm_norm; rewrite v_srai_Z by lia; f_equal; change (2^2) with 4; replace (20 * cap) with (5 * cap * 4) by lia; apply Z.div_mul; lia).
        stepiv F_6bd6c D_6bd6c (Z_to_bv 64 cap) ltac:(gres; pin; apply v_mul_inv5; lia).
        stepiv F_6bd70 D_6bd70 (Z_to_bv 64 (2 * cap)) ltac:(gres; pin; imm_norm; rewrite v_slli_Z by lia; f_equal; change (2^1) with 2; lia).
        close_pc.
      - gres. repeat split; first [reflexivity | assumption | f_equal; lia | intros r Hr; repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]); destruct Hr]. }
    destruct (PRE _ eq_refl) as (Ry & RUNP & Ry8 & Ry9 & Ry2 & Ry10 & Ry11 & Ry12 & Ry18 & Ry19 & Ry20 & Ry21 & Ry3 & Ry4 & Ry1 & RyS).
    destruct (Z.lt_ge_cases 1 cap) as [Hc1 | Hc1].
    -
      replace (vgrow cap) with (2 * cap) by (unfold vgrow; lia).
      eexists. split.
      + eapply msteps_trans; [apply PRO; reflexivity|]. eapply msteps_trans; [exact RUNP|]. norm_pc.
        stepb_tk F_6bd74 D_6bd74 ltac:(cmpz).
        snl F_6bd7c D_6bd7c.
        ld_step F_6bd80 D_6bd80 (word_to_le_bytes 8 (Z_to_bv 64 0x0666666666666666)) (Z_to_bv 64 0x0666666666666666) ltac:(rdn_fix K2') ltac:(b2z8).
        stepb_tk F_6bd84 D_6bd84 ltac:(cmpz).
        stepb_ft F_6bd90 D_6bd90 ltac:(cmpz).
        stepb_ft F_6bd94 D_6bd94 ltac:(cmpz).
        stepiv F_6bd98 D_6bd98 (Z_to_bv 64 20) ltac:(gres; pin; imm_norm; reflexivity).
        stepiv F_6bd9c D_6bd9c (Z_to_bv 64 (20 * (2 * cap))) ltac:(gres; pin; rewrite v_mul_Z by lia; f_equal; lia).
        stepj F_6bda0 D_6bda0.
        close_pc.
      + gres. repeat split; first [reflexivity | assumption | f_equal; lia | intros r Hr; pose proof Hr as Hr'; repeat (destruct Hr as [<-|Hr]; [gres; apply RyS; exact Hr'|]); destruct Hr].
    -
      replace (vgrow cap) with (cap + 1) by (unfold vgrow; lia).
      eexists. split.
      + eapply msteps_trans; [apply PRO; reflexivity|]. eapply msteps_trans; [exact RUNP|]. norm_pc.
        stepb_ft F_6bd74 D_6bd74 ltac:(cmpz).
        sv F_6bd78 D_6bd78 (Z_to_bv 64 (cap + 1)).
        snl F_6bd7c D_6bd7c.
        ld_step F_6bd80 D_6bd80 (word_to_le_bytes 8 (Z_to_bv 64 0x0666666666666666)) (Z_to_bv 64 0x0666666666666666) ltac:(rdn_fix K2') ltac:(b2z8).
        stepb_tk F_6bd84 D_6bd84 ltac:(cmpz).
        stepb_ft F_6bd90 D_6bd90 ltac:(cmpz).
        stepb_ft F_6bd94 D_6bd94 ltac:(cmpz).
        stepiv F_6bd98 D_6bd98 (Z_to_bv 64 20) ltac:(gres; pin; imm_norm; reflexivity).
        stepiv F_6bd9c D_6bd9c (Z_to_bv 64 (20 * (cap + 1))) ltac:(gres; pin; rewrite v_mul_Z by lia; f_equal; lia).
        stepj F_6bda0 D_6bda0.
        close_pc.
      + gres. repeat split; first [reflexivity | assumption | f_equal; lia | intros r Hr; pose proof Hr as Hr'; repeat (destruct Hr as [<-|Hr]; [gres; apply RyS; exact Hr'|]); destruct Hr].
  Qed.

  Lemma LB : forall (fx : FPState) R2 Mb (sp v b cap src p : Z) (w0 w4 w8 w12 w16 : list byte),
    getr R2 10%bv = Z_to_bv 64 p -> getr R2 2%bv = Z_to_bv 64 (sp - 64) ->
    getr R2 8%bv = Z_to_bv 64 b -> getr R2 9%bv = Z_to_bv 64 v -> getr R2 18%bv = Z_to_bv 64 (20 * cap) -> getr R2 19%bv = Z_to_bv 64 (20 * cap) ->
    getr R2 20%bv = Z_to_bv 64 src -> getr R2 21%bv = Z_to_bv 64 (vgrow cap) ->
    0 <= cap < 2 ^ 40 -> 0 <= b -> b + 20 * cap <= 2 ^ 63 -> b mod 4 = 0 -> 16 <= p -> p mod 16 = 0 -> p + 20 * vgrow cap <= 2 ^ 47 -> 0 <= src -> src + 20 <= 2 ^ 63 ->
    (src + 20 <= p \/ p + 20 * vgrow cap <= src) ->
    mdef Mb p (20 * vgrow cap) ->
    rdn SEGS Mb (Z_to_bv 64 src) 4 = Some w0 -> length w0 = 4%nat ->
    rdn SEGS Mb (Z_to_bv 64 (src + 4)) 4 = Some w4 -> length w4 = 4%nat ->
    rdn SEGS Mb (Z_to_bv 64 (src + 8)) 4 = Some w8 -> length w8 = 4%nat ->
    rdn SEGS Mb (Z_to_bv 64 (src + 12)) 4 = Some w12 -> length w12 = 4%nat ->
    rdn SEGS Mb (Z_to_bv 64 (src + 16)) 4 = Some w16 -> length w16 = 4%nat ->
    exists R3,
      msteps SEGS (@mkst fx R2 (Z_to_bv 64 0x6bde4) Mb (seg_rom SEGS))
                  (@mkst fx R3 (Z_to_bv 64 0xe2b9c)
                     (wbytes (wbytes (wbytes (wbytes (wbytes Mb
                        (Z_to_bv 64 (p + 20 * cap + 16)) (word_to_le_bytes 4 (v_lw (Z_to_bv 64 (bytes_le_to_Z w16)))))
                        (Z_to_bv 64 (p + 20 * cap)) (word_to_le_bytes 4 (v_lw (Z_to_bv 64 (bytes_le_to_Z w0)))))
                        (Z_to_bv 64 (p + 20 * cap + 4)) (word_to_le_bytes 4 (v_lw (Z_to_bv 64 (bytes_le_to_Z w4)))))
                        (Z_to_bv 64 (p + 20 * cap + 8)) (word_to_le_bytes 4 (v_lw (Z_to_bv 64 (bytes_le_to_Z w8)))))
                        (Z_to_bv 64 (p + 20 * cap + 12)) (word_to_le_bytes 4 (v_lw (Z_to_bv 64 (bytes_le_to_Z w12))))) (seg_rom SEGS))
      /\ getr R3 10%bv = Z_to_bv 64 p /\ getr R3 11%bv = Z_to_bv 64 b /\ getr R3 12%bv = Z_to_bv 64 (20 * cap) /\ getr R3 1%bv = Z_to_bv 64 0x6beb8
      /\ getr R3 2%bv = Z_to_bv 64 (sp - 64) /\ getr R3 8%bv = Z_to_bv 64 b /\ getr R3 9%bv = Z_to_bv 64 v /\ getr R3 18%bv = Z_to_bv 64 (20 * cap)
      /\ getr R3 20%bv = Z_to_bv 64 p /\ getr R3 21%bv = Z_to_bv 64 (p + 20 * cap + 20) /\ getr R3 22%bv = Z_to_bv 64 (p + 20 * vgrow cap)
      /\ getr R3 3%bv = getr R2 3%bv /\ getr R3 4%bv = getr R2 4%bv
      /\ (forall r, In r [19; 23; 24; 25; 26; 27]%bv -> getr R3 r = getr R2 r).
  Proof using.
    intros fx R2 Mb sp v b cap src p w0 w4 w8 w12 w16 G10 G2 G8 G9 G18 G19 G20 G21 Hcap Hb0 Hbc Hb4 Hp16 Hpal Hpv Hs0 Hs1 Hsp HDp Q0 L0 Q4 L4 Q8 L8 Q12 L12 Q16 L16.
    assert (Hvg : cap + 1 <= vgrow cap /\ vgrow cap <= 2 * cap + 1) by (unfold vgrow; lia).
    assert (Hp4 : (p + 20 * cap) mod 4 = 0).
    { pose proof (Z_div_mod_eq_full p 16) as E. rewrite Hpal in E. replace (p + 20 * cap) with ((4 * (p / 16) + 5 * cap) * 4) by lia. apply Z_mod_mult. }
    eexists. split.
    - norm_pc.
      stepiv F_6bda4 D_6bda4 (Z_to_bv 64 (p + 20 * cap)) ltac:(gres; pin; rewrite v_add_Z by lia; reflexivity).
      stepb_tk F_6bda8 D_6bda8 ltac:(cmpz).
      steprr (@step_sltu_at fx) F_6bdbc D_6bdbc (Z_to_bv 64 1) ltac:(gres; pin; rewrite ?getr_zero; apply snez_Z; lia).
      stepiv F_6bdc0 D_6bdc0 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite sltiu_1_Z by lia; destruct (Z.eqb_spec (p + 20 * cap) 0); [lia|reflexivity]).
      steprr (@step_xor_at fx) F_6bdc4 D_6bdc4 (Z_to_bv 64 1) ltac:(gres; pin; apply bv_eq; vm_compute; reflexivity).
      stepb_ft F_6bdc8 D_6bdc8 ltac:(cmpz).
      stepiv F_6bdcc D_6bdcc (Z_to_bv 64 20) ltac:(gres; pin; imm_norm; reflexivity).
      stepiv F_6bdd0 D_6bdd0 (Z_to_bv 64 (20 * vgrow cap)) ltac:(gres; pin; rewrite v_mul_Z by lia; f_equal; lia).
      stepiv F_6bdd4 D_6bdd4 (Z_to_bv 64 (p + 20 * vgrow cap)) ltac:(gres; pin; rewrite v_add_Z by lia; f_equal; lia).
      stepiv F_6bdd8 D_6bdd8 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite sltiu_1_Z by lia; destruct (Z.eqb_spec (p + 20 * vgrow cap) 0); [lia|reflexivity]).
      stepb_ft F_6bddc D_6bddc ltac:(cmpz).
      stepb_ft F_6bde0 D_6bde0 ltac:(cmpz).
      steprr (@step_mulh_at fx) F_6bde4 D_6bde4 (Z_to_bv 64 0) ltac:(gres; pin; apply v_mulh_small; lia).
      stepiv F_6bde8 D_6bde8 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite v_srai_Z by lia; f_equal; rewrite Z.div_small by lia; reflexivity).
      steprr (@step_xor_at fx) F_6bdec D_6bdec (Z_to_bv 64 0) ltac:(gres; pin; apply xor_same).
      steprr (@step_sltu_at fx) F_6bdf0 D_6bdf0 (Z_to_bv 64 0) ltac:(gres; pin; rewrite ?getr_zero; reflexivity).
      stepb_ft F_6bdf4 D_6bdf4 ltac:(apply c_eq_refl).
      stepiv F_6bdf8 D_6bdf8 (Z_to_bv 64 0)
        ltac:(gres; pin; imm_norm; rewrite v_andi_Z by lia; f_equal; change 3 with (2 ^ 2 - 1); rewrite land_ones_mod by lia; change (2 ^ 2) with 4; exact Hp4).
      stepb_ft F_6bdfc D_6bdfc ltac:(apply c_eq_refl).
      stepb_ft F_6be00 D_6be00 ltac:(cmpz).
      ld_step F_6be04 D_6be04 w16 (Z_to_bv 64 (bytes_le_to_Z w16)) ltac:(rdn_fix Q16) ltac:(apply lez4_val; exact L16).
      ld_step F_6be08 D_6be08 w0 (Z_to_bv 64 (bytes_le_to_Z w0)) ltac:(rdn_fix Q0) ltac:(apply lez4_val; exact L0).
      ld_step F_6be0c D_6be0c w4 (Z_to_bv 64 (bytes_le_to_Z w4)) ltac:(rdn_fix Q4) ltac:(apply lez4_val; exact L4).
      ld_step F_6be10 D_6be10 w8 (Z_to_bv 64 (bytes_le_to_Z w8)) ltac:(rdn_fix Q8) ltac:(apply lez4_val; exact L8).
      ld_step F_6be14 D_6be14 w12 (Z_to_bv 64 (bytes_le_to_Z w12)) ltac:(rdn_fix Q12) ltac:(apply lez4_val; exact L12).
      stw F_6be18 D_6be18 (Z_to_bv 64 (p + 20 * cap + 16)) (v_lw (Z_to_bv 64 (bytes_le_to_Z w16))) ltac:(ok_mdef HDp).
      stepiv F_6be1c D_6be1c (Z_to_bv 64 (2 ^ 64 - 20)) ltac:(gres; pin; imm_norm; apply bv_eq; vm_compute; reflexivity).
      stw F_6be20 D_6be20 (Z_to_bv 64 (p + 20 * cap)) (v_lw (Z_to_bv 64 (bytes_le_to_Z w0))) ltac:(ok_mdef HDp).
      stw F_6be24 D_6be24 (Z_to_bv 64 (p + 20 * cap + 4)) (v_lw (Z_to_bv 64 (bytes_le_to_Z w4))) ltac:(ok_mdef HDp).
      stw F_6be28 D_6be28 (Z_to_bv 64 (p + 20 * cap + 8)) (v_lw (Z_to_bv 64 (bytes_le_to_Z w8))) ltac:(ok_mdef HDp).
      stw F_6be2c D_6be2c (Z_to_bv 64 (p + 20 * cap + 12)) (v_lw (Z_to_bv 64 (bytes_le_to_Z w12))) ltac:(ok_mdef HDp).
      stepb_ft F_6be30 D_6be30 ltac:(cmpz).
      stepiv F_6be34 D_6be34 (Z_to_bv 64 p) ltac:(gres; pin; rewrite v_sub_Z by lia; f_equal; lia).
      stepb_ft F_6be38 D_6be38 ltac:(cmpz).
      steprr (@step_sltu_at fx) F_6be3c D_6be3c (Z_to_bv 64 (if 20 * cap =? 0 then 0 else 1)) ltac:(gres; pin; apply sltu_pp; lia).
      steprr (@step_slt_at fx) F_6be40 D_6be40 (Z_to_bv 64 (if 20 * cap =? 0 then 0 else 1))
        ltac:(gres; pin; rewrite ?getr_zero; rewrite sgtz_Z by lia; reflexivity).
      steprr (@step_xor_at fx) F_6be44 D_6be44 (Z_to_bv 64 0) ltac:(gres; pin; apply xor_same).
      stepiv F_6be48 D_6be48 (Z_to_bv 64 1) ltac:(gres; pin; imm_norm; reflexivity).
      stepb_ft F_6be4c D_6be4c ltac:(cmpz).
      stepiv F_6be50 D_6be50 (Z_to_bv 64 0)
        ltac:(gres; pin; imm_norm; rewrite v_andi_Z by lia; f_equal; change 3 with (2 ^ 2 - 1); rewrite land_ones_mod by lia; change (2 ^ 2) with 4; exact Hb4).
      stepb_ft F_6be54 D_6be54 ltac:(apply c_eq_refl).
      stepiv F_6be58 D_6be58 (Z_to_bv 64 20) ltac:(gres; pin; imm_norm; reflexivity).
      stepiv F_6be5c D_6be5c (Z_to_bv 64 (20 * vgrow cap)) ltac:(gres; pin; rewrite v_mul_Z by lia; f_equal; lia).
      stepiv F_6be60 D_6be60 (Z_to_bv 64 (p + 20 * vgrow cap)) ltac:(gres; pin; rewrite v_add_Z by lia; reflexivity).
      stepiv F_6be64 D_6be64 (Z_to_bv 64 (p + 20 * cap + 20)) ltac:(gres; pin; imm_norm; rewrite v_addi_Z by lia; reflexivity).
      sv F_6be68 D_6be68 (Z_to_bv 64 p).
      sv F_6be6c D_6be6c (Z_to_bv 64 b).
      sv F_6be70 D_6be70 (Z_to_bv 64 (20 * cap)).
      stepj F_6be74 D_6be74.
      close_pc.
    - gres. repeat split; first [reflexivity | assumption | f_equal; lia | intros r Hr; repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]); destruct Hr].
  Qed.

  Lemma epilogue : forall (fx : FPState) R M sp ret (a0v v8 v9 v18 v19 v20 v21 v22 : word),
    getr R 2%bv = Z_to_bv 64 (sp - 64) -> getr R 21%bv = a0v -> 64 <= sp < 2 ^ 63 ->
    rdn SEGS M (Z_to_bv 64 (sp - 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 ret)) ->
    rdn SEGS M (Z_to_bv 64 (sp - 16)) 8 = Some (word_to_le_bytes 8 v8) ->
    rdn SEGS M (Z_to_bv 64 (sp - 24)) 8 = Some (word_to_le_bytes 8 v9) ->
    rdn SEGS M (Z_to_bv 64 (sp - 32)) 8 = Some (word_to_le_bytes 8 v18) ->
    rdn SEGS M (Z_to_bv 64 (sp - 40)) 8 = Some (word_to_le_bytes 8 v19) ->
    rdn SEGS M (Z_to_bv 64 (sp - 48)) 8 = Some (word_to_le_bytes 8 v20) ->
    rdn SEGS M (Z_to_bv 64 (sp - 56)) 8 = Some (word_to_le_bytes 8 v21) ->
    rdn SEGS M (Z_to_bv 64 (sp - 64)) 8 = Some (word_to_le_bytes 8 v22) ->
    ret_ok (Z_to_bv 64 ret) ->
    msteps SEGS (@mkst fx R (Z_to_bv 64 0x6bed4) M (seg_rom SEGS))
                (@mkst fx (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd R
                             10%bv a0v) 1%bv (Z_to_bv 64 ret)) 8%bv v8) 9%bv v9) 18%bv v18) 19%bv v19) 20%bv v20) 21%bv v21) 22%bv v22)
                             2%bv (Z_to_bv 64 sp))
                          (Z_to_bv 64 ret) M (seg_rom SEGS)).
  Proof using.
    intros fx R M sp ret a0v v8 v9 v18 v19 v20 v21 v22 Hsp Hs5 Hsp' L1 L8 L9 L18 L19 L20 L21 L22 Hret.
    norm_pc.
    sv F_6be94 D_6be94 a0v.
    ld_step F_6be98 D_6be98 (word_to_le_bytes 8 (Z_to_bv 64 ret)) (Z_to_bv 64 ret) ltac:(rdA L1) ltac:(b2z8).
    ld_step F_6be9c D_6be9c (word_to_le_bytes 8 v8) v8 ltac:(rdA L8) ltac:(b2z8).
    ld_step F_6bea0 D_6bea0 (word_to_le_bytes 8 v9) v9 ltac:(rdA L9) ltac:(b2z8).
    ld_step F_6bea4 D_6bea4 (word_to_le_bytes 8 v18) v18 ltac:(rdA L18) ltac:(b2z8).
    ld_step F_6bea8 D_6bea8 (word_to_le_bytes 8 v19) v19 ltac:(rdA L19) ltac:(b2z8).
    ld_step F_6beac D_6beac (word_to_le_bytes 8 v20) v20 ltac:(rdA L20) ltac:(b2z8).
    ld_step F_6beb0 D_6beb0 (word_to_le_bytes 8 v21) v21 ltac:(rdA L21) ltac:(b2z8).
    ld_step F_6beb4 D_6beb4 (word_to_le_bytes 8 v22) v22 ltac:(rdA L22) ltac:(b2z8).
    sv F_6beb8 D_6beb8 (Z_to_bv 64 sp).
    stepjr F_6bebc D_6bebc (Z_to_bv 64 ret) ltac:(gres; reflexivity).
    lazymatch goal with |- msteps _ ?a ?b => replace b with a; [apply mst_refl|] end.
    f_equal. exact Hret.
  Qed.

  Theorem vec_opnd_pbslow_6bc9c_spec : vec_opnd_pbslow_stmt SEGS Ly.L MI ST u1c6bc9c.
  Proof using AC MI ST MALLOC_STACK_pos NEW.
    intros fx A s R M model sp ret v b cap src K.
    cbn [vc_entry vc_stack u1c6bc9c]. lazy zeta.
    intros CB Ha0 Ha1 VEC OBJ Hv8 ROC HDs SOBJ Hs0 Hs1 Hs4 SRCV HNMAX ROOM CONT.
    destruct CB as [AI MS IRC SXI SXH CR Hceil HROOM Hwin Hown_sx Herr_sx].
    destruct CR as [Hra Hret Hretr Hsp Hsp16 Hsphi Hgp Htp].
    cbn [ly_gp ly_tp ly_errno_off ly_img ly_relro ly_rw Ly.L] in *.
    pose proof ac_bounds_lit as Hceilv.
    destruct VEC as (Hv0 & Hv1 & HDv & Hlen & Hb & F0 & F1 & F2).
    unfold NEW_STACK, OPND_SZ in *.
    pose proof HROOM as HOK. unfold stack_room in HOK.
    assert (Hspr : 2 ^ 20 <= sp - (64 + (16 + MALLOC_STACK MI))) by (lia).
    pose proof (ai_nmax_bound MI) as HNM. pose proof (ai_big_pos MI) as HBIG.
    assert (Hcap : 0 <= cap < 2 ^ 36) by (unfold vgrow in HNMAX; lia).
    destruct OBJ as [PLv WINv]. destruct SOBJ as [PLs WINs].
    assert (WINv' : v + 24 <= sp - (64 + (16 + MALLOC_STACK MI)) \/ sp <= v).
    { destruct (Z.lt_ge_cases v sp); [left|right; lia].
      destruct (Z.lt_ge_cases (v + 24) (sp - (64 + (16 + MALLOC_STACK MI)) + 1)); [lia|].
      exfalso. destruct (Z.lt_ge_cases v (sp - (64 + (16 + MALLOC_STACK MI)))).
      - apply (WINv (sp - (64 + (16 + MALLOC_STACK MI)))); unfold zwin; lia.
      - apply (WINv v); unfold zwin; lia. }
    assert (WINs' : src + 20 <= sp - (64 + (16 + MALLOC_STACK MI)) \/ sp <= src).
    { destruct (Z.lt_ge_cases src sp); [left|right; lia].
      destruct (Z.lt_ge_cases (src + 20) (sp - (64 + (16 + MALLOC_STACK MI)) + 1)); [lia|].
      exfalso. destruct (Z.lt_ge_cases src (sp - (64 + (16 + MALLOC_STACK MI)))).
      - apply (WINs (sp - (64 + (16 + MALLOC_STACK MI)))); unfold zwin; lia.
      - apply (WINs src); unfold zwin; lia. }
    hide WINv'. hide WINs'.
    assert (BUF : b <> 0 -> mdef M b (20 * cap) /\ b + 20 * cap <= alloc_ceiling /\
                  (forall a, b <= a < b + 20 * cap -> ~ owned MI A a /\ ~ in_ranges [(0x10000, 0x124000)] a)).
    { intros Hbnz. destruct Hb as [[Hb0 _]|(Hbp & Hal & Hcp & Hbc & HIn & Hdj)]; [lia|].
      split; [eapply (live_mdef SEGS Ly.L MI); eassumption|].
      split; [eapply (live_range SEGS Ly.L MI); eassumption|].
      intros a Ha. split; [eapply (live_unowned SEGS Ly.L MI); eassumption|].
      eapply (live_offimg SEGS Ly.L MI); eassumption. }
    hide Hb.
    assert (Hb0 : 0 <= b) by (unhide Hb; destruct Hb as [[-> _]|(Hbp & _)]; lia).
    assert (Hbc4 : b + 20 * cap <= 2 ^ 63) by (unhide Hb; destruct Hb as [[-> ->]|(Hbp & Hal & Hcp & Hbc & _)]; lia).
    assert (Hbal4 : b mod 4 = 0).
    { unhide Hb. destruct Hb as [[-> _]|(Hbp & Hal & _)]; [reflexivity|].
      pose proof (Z_div_mod_eq_full b 16) as E. rewrite Hal in E. replace b with ((4 * (b / 16)) * 4) by lia. apply Z_mod_mult. }
    assert (HDR : forall a, v <= a < v + 24 -> ~ owned MI A a /\ ~ in_ranges [(0x10000, 0x124000)] a).
    { intros a Ha. exact (placed_sep A M model v 24 a AI PLv Ha). }
    assert (WIN : forall a, sp - (64 + (16 + MALLOC_STACK MI)) <= a < sp -> ~ owned MI A a /\ ~ in_ranges [(0x10000, 0x124000)] a).
    { intros a Ha. apply (stack_sep A M model a AI). lia. }
    assert (HDW : mdef M (sp - (64 + (16 + MALLOC_STACK MI))) (64 + (16 + MALLOC_STACK MI))).
    { eapply store_ok_mdef_offimg; [exact HOK | lia | lia | lia |]. intros w Hw. apply ly_noseg. lia. }
    assert (RO : forall a, 0x10000 <= a < 0xe8000 -> M (Z_to_bv 64 a) = None).
    { intros a Ha. apply ROC. rewrite u64_of_Z by lia. unfold ro_addr. cbn [ly_img ly_rw ly_relro Ly.L].
      rewrite !in_ranges_1. lia. }

    set (M1 := wslots M sp (PRO_vals R ret)).
    assert (ST1 : stores_in (zwin (sp - 64) sp) M M1).
    { unfold M1. apply (wslots_stores_in M sp (PRO_vals R ret)); unfold Zlen; cbn; lia. }
    assert (AG1 : forall lo hi, (hi <= sp - 64 \/ sp <= lo) -> 0 <= lo -> hi < 2 ^ 64 -> agree_on (zwin lo hi) M M1).
    { intros lo hi Hd Hlo Hhi. eapply stores_in_agree; [exact ST1|]. intros a Ha. unfold zwin in *. lia. }
    assert (HDs1 : mdef M1 src 20) by (eapply stores_in_mdef; [exact ST1 | exact HDs]).
    assert (SL : forall k, 1 <= k <= 8 ->
              rdn SEGS M1 (Z_to_bv 64 (sp - 8 * k)) 8
              = Some (word_to_le_bytes 8 (nth (Z.to_nat (8 - k)) (PRO_vals R ret) (Z_to_bv 64 0)))).
    { intros k Hk. unfold M1. apply wslots_read; unfold Zlen; cbn; lia. }
    slotv SL 1 SL1. slotv SL 2 SL2. slotv SL 3 SL3. slotv SL 4 SL4.
    slotv SL 5 SL5. slotv SL 6 SL6. slotv SL 7 SL7. slotv SL 8 SL8. clear SL.
    unfold fld in F0, F1, F2.

    destruct (LA fx R M sp ret v b cap src Hra Hsp Ha0 Ha1 ltac:(lia) Hb0 Hbc4 ltac:(lia) ltac:(lia) Hv0 Hv1 ltac:(unhide WINv'; lia)
                 ltac:(ok_sub HOK) F0 F1 F2
                 ltac:(unfold K_MAXP1; rewrite <- img_K_MAXP1; unfold K_MAXP1; apply rdn_agree_win; [lia|lia|]; intros x Hx; unfold zwin in Hx; apply RO; lia)
                 ltac:(unfold K_HALF; rewrite <- img_K_HALF; unfold K_HALF; apply rdn_agree_win; [lia|lia|]; intros x Hx; unfold zwin in Hx; apply RO; lia))
      as (Rn & RUNA & Rn10 & Rn1 & Rn2 & Rn8 & Rn9 & Rn18 & Rn19 & Rn20 & Rn21 & Rn3 & Rn4 & RnS).
    fold M1 in RUNA.
    eapply srz_msteps; [exact (ms_halt _ MS) | exact (ms_lazy _ MS) | exact RUNA | ].
    assert (Hng : 20 <= 20 * vgrow cap) by (unfold vgrow; lia).
    eapply (NEW fx A s Rn M1 model (20 * vgrow cap) (sp - 64) 0x6bde4 K).
    + eapply (stores_in_ainv SEGS Ly.L MI); [exact AI | exact ST1 |]. intros a Ha. apply WIN. unfold zwin in Ha. lia.
    + exact MS.
    + eapply (roc_stores Ly.L); [exact IRC | exact ST1 |]. intros a Ha. cbn [ly_img Ly.L]. apply (proj2 (WIN a ltac:(unfold zwin in Ha; lia))).
    + eapply (stores_in_sx SEGS Ly.L ST); [exact SXI | exact ST1 |].
      intros a Ha. destruct (offimg_sep a (proj2 (WIN a ltac:(unfold zwin in Ha; lia)))) as (X1 & X2 & _). split; assumption.
    + exact SXH.
    + constructor.
      * exact Rn1. * unfold ret_ok. apply bv_eq. vm_compute. reflexivity. * lia. * exact Rn2.
      * replace (sp - 64) with (sp - 16 * 4) by lia. apply mod16_sub. exact Hsp16.
      * lia. * rewrite Rn3. exact Hgp. * rewrite Rn4. exact Htp.
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
      { eapply (roc_stores Ly.L); [exact IRC | exact ST1 |]. intros a Ha. cbn [ly_img Ly.L]. apply (proj2 (WIN a ltac:(unfold zwin in Ha; lia))). }
      assert (ROC2 : img_ro_clear Ly.L M2).
      { eapply (roc_frame Ly.L); [exact ROC1 | exact FR1 |]. intros a [Ho|[Hblk|[Hw|He]]].
        - exact (roc_owned SEGS Ly.L MI A1 M2 model1 a AI1 Ho).
        - right. eapply (live_offimg SEGS Ly.L MI); [exact AI1 | apply (live_add_new _ _ _ _ LADD) | exact Hblk].
        - right. apply (proj2 (stack_sep A1 M2 model1 a AI1 ltac:(unfold zwin in Hw; lia))).
        - left. apply ly_errno_rw. exact He. }
      set (n4 := 20 * vgrow cap) in *.
      assert (Hn4 : n4 = Z.max (2 * cap) (cap + 1) * 20) by (unfold n4, vgrow; lia).
      assert (HinP : In (p, n4) (live MI A1)) by (apply (live_add_new _ _ _ _ LADD)).
      destruct (live_range SEGS Ly.L MI A1 M2 model1 p n4 AI1 HinP) as (_ & Hpal & _ & Hpce).
      assert (HDp : mdef M2 p n4) by (eapply (live_mdef SEGS Ly.L MI); eassumption).
      assert (Hpown : forall a, p <= a < p + n4 -> ~ owned MI A1 a /\ ~ in_ranges [(0x10000, 0x124000)] a).
      { intros a Ha. split; [eapply (live_unowned SEGS Ly.L MI); eassumption | eapply (live_offimg SEGS Ly.L MI); eassumption]. }
      assert (LIVE1 : forall blk, In blk (live MI A) -> In blk (live MI A1)) by (intros blk Hblk; eapply live_add_keeps; eassumption).
      assert (PLv1 : placed MI A1 v 24) by (eapply (placed_mono SEGS Ly.L MI); eassumption).
      assert (PLs1 : placed MI A1 src 20) by (eapply (placed_mono SEGS Ly.L MI); eassumption).
      assert (HDRp : v + 24 <= p \/ p + n4 <= v).
      { destruct (placed_new_block_disjoint SEGS Ly.L MI A A1 M M2 model model1 v 24 p n4 AI AI1 PLv LADD ltac:(lia)) as [H|[H|H]]; [left|right|]; lia. }
      hide HDRp.
      assert (SRCp : src + 20 <= p \/ p + n4 <= src).
      { destruct (placed_new_block_disjoint SEGS Ly.L MI A A1 M M2 model model1 src 20 p n4 AI AI1 PLs LADD ltac:(lia)) as [H|[H|H]]; [left|right|]; lia. }
      hide SRCp.
      assert (BUFp : b <> 0 -> b + 20 * cap <= p \/ p + n4 <= b).
      { intros Hbnz. unhide Hb. destruct Hb as [[Hb00 _]|(Hbp & Hal & Hcp & Hbc & HIn & Hdj)]; [lia|].
        assert (Hne : p <> b).
        { intros ->. destruct LADD as [_ Hnin]. apply Hnin. apply in_map_iff. exists (b, 20 * cap). split; [reflexivity|exact HIn]. }
        destruct (ai_live_disjoint MI A1 M2 model1 p n4 b (20 * cap) AI1 HinP (LIVE1 _ HIn) Hne); [right|left]; lia. }
      assert (WIN1 : forall a, sp - (64 + (16 + MALLOC_STACK MI)) <= a < sp -> ~ owned MI A1 a /\ ~ in_ranges [(0x10000, 0x124000)] a).
      { intros a Ha. apply (stack_sep A1 M2 model1 a AI1). lia. }
      assert (HDR1 : forall a, v <= a < v + 24 -> ~ owned MI A1 a /\ ~ in_ranges [(0x10000, 0x124000)] a).
      { intros a Ha. exact (placed_sep A1 M2 model1 v 24 a AI1 PLv1 Ha). }
      assert (SRC1 : forall a, src <= a < src + 20 -> ~ owned MI A1 a /\ ~ in_ranges [(0x10000, 0x124000)] a).
      { intros a Ha. exact (placed_sep A1 M2 model1 src 20 a AI1 PLs1 Ha). }
      assert (PRES2 : forall a, (sp - 64 <= a < sp) \/ (v <= a < v + 24) \/ (src <= a < src + 20)
                                \/ (b <> 0 /\ b <= a < b + 20 * cap) -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
      { intros a Ha.
        assert (Hr : 0 <= a < 2 ^ 64) by (destruct Ha as [H|[H|[H|[Hnz H]]]]; lia).
        apply FR1. rewrite u64_of_Z by lia. intros [Ho|[Hblk|[Hw|He]]].
        - destruct Ha as [H|[H|[H|[Hnz H]]]].
          + exact (proj1 (WIN1 a ltac:(lia)) Ho).
          + exact (proj1 (HDR1 a H) Ho).
          + exact (proj1 (SRC1 a H) Ho).
          + unhide Hb. destruct Hb as [[Hb00 _]|(Hbp & Hal & Hcp & Hbc & HIn & Hdj)]; [lia|].
            exact (live_unowned SEGS Ly.L MI A1 M2 model1 b (20 * cap) a AI1 (LIVE1 _ HIn) H Ho).
        - destruct Ha as [H|[H|[H|[Hnz H]]]].
          + lia. + unhide HDRp; lia. + unhide SRCp; lia. + destruct (BUFp Hnz); lia.
        - unfold zwin in Hw. destruct Ha as [H|[H|[H|[Hnz H]]]].
          + lia. + unhide WINv'; lia. + unhide WINs'; lia.
          + unhide Hb. destruct Hb as [[Hb00 _]|(Hbp & Hal & Hcp & Hbc & HIn & Hdj)]; [lia|].
            destruct (live_range SEGS Ly.L MI A M model b (20 * cap) AI HIn) as (_ & _ & _ & Hbce). lia.
        - pose proof (ly_errno_img a He) as Hi. rewrite ly_img_iff in Hi.
          destruct Ha as [H|[H|[H|[Hnz H]]]].
          + pose proof (proj2 (WIN1 a ltac:(lia))) as X. rewrite in_ranges_1 in X. lia.
          + pose proof (proj2 (HDR1 a H)) as X. rewrite in_ranges_1 in X. lia.
          + pose proof (proj2 (SRC1 a H)) as X. rewrite in_ranges_1 in X. lia.
          + unhide Hb. destruct Hb as [[Hb00 _]|(Hbp & Hal & Hcp & Hbc & HIn & Hdj)]; [lia|].
            pose proof (live_offimg SEGS Ly.L MI A1 M2 model1 b (20 * cap) a AI1 (LIVE1 _ HIn) H) as X. rewrite ly_img_iff in X. lia. }
      assert (R2_2 : getr R2 2%bv = Z_to_bv 64 (sp - 64)) by (rewrite (KEPT2 2%bv) by in_cs; exact Rn2).
      assert (R2_8 : getr R2 8%bv = Z_to_bv 64 b) by (rewrite (KEPT2 8%bv) by in_cs; exact Rn8).
      assert (R2_9 : getr R2 9%bv = Z_to_bv 64 v) by (rewrite (KEPT2 9%bv) by in_cs; exact Rn9).
      assert (R2_18 : getr R2 18%bv = Z_to_bv 64 (20 * cap)) by (rewrite (KEPT2 18%bv) by in_cs; exact Rn18).
      assert (R2_19 : getr R2 19%bv = Z_to_bv 64 (20 * cap)) by (rewrite (KEPT2 19%bv) by in_cs; exact Rn19).
      assert (R2_20 : getr R2 20%bv = Z_to_bv 64 src) by (rewrite (KEPT2 20%bv) by in_cs; exact Rn20).
      assert (R2_21 : getr R2 21%bv = Z_to_bv 64 (vgrow cap)) by (rewrite (KEPT2 21%bv) by in_cs; exact Rn21).
      assert (R2_3 : getr R2 3%bv = getr R 3%bv) by (rewrite (KEPT2 3%bv) by in_cs; exact Rn3).
      assert (R2_4 : getr R2 4%bv = getr R 4%bv) by (rewrite (KEPT2 4%bv) by in_cs; exact Rn4).
      assert (R2S : forall r, In r [23; 24; 25; 26; 27]%bv -> getr R2 r = getr R r).
      { intros r Hr. pose proof Hr as Hr'. repeat (destruct Hr as [<-|Hr]; [rewrite (KEPT2 _) by in_cs; apply RnS; exact Hr' |]). destruct Hr. }

      assert (HDs2 : mdef M2 src 20).
      { eapply (mdef_through (fun a => owned MI A a \/ errno_win Ly.L a)); [exact DEF1 | exact HDs1 | lia | lia |].
        intros a Ha [Ho|He]; [exact (proj1 (placed_sep A M model src 20 a AI PLs Ha) Ho) | exact (proj2 (placed_sep A M model src 20 a AI PLs Ha) (ly_errno_img a He))]. }
      destruct (mdef_rdn SEGS M2 src 20 16 4 HDs2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; lia)) as (w16 & Q16 & L16).
      destruct (mdef_rdn SEGS M2 src 20 12 4 HDs2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; lia)) as (w12 & Q12 & L12).
      destruct (mdef_rdn SEGS M2 src 20 8 4 HDs2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; lia)) as (w8 & Q8 & L8).
      destruct (mdef_rdn SEGS M2 src 20 4 4 HDs2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; lia)) as (w4 & Q4 & L4).
      destruct (mdef_rdn SEGS M2 src 20 0 4 HDs2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; lia)) as (w0 & Q0 & L0).
      rewrite Z.add_0_r in Q0.
      set (d := p + 20 * cap).

      unhide SRCp.
      assert (Hp16 : 16 <= p) by (pose proof (Z_div_mod_eq_full p 16) as E; rewrite Hpal in E; lia).
      destruct (LB fx R2 M2 sp v b cap src p w0 w4 w8 w12 w16 R2a0 R2_2 R2_8 R2_9 R2_18 R2_19 R2_20 R2_21
                   ltac:(lia) Hb0 Hbc4 Hbal4 Hp16 Hpal ltac:(unfold n4 in Hpce; lia) Hs0 Hs1 ltac:(unfold n4 in SRCp; lia) ltac:(unfold n4 in HDp; exact HDp)
                   Q0 L0 Q4 L4 Q8 L8 Q12 L12 Q16 L16)
        as (R3 & RUNB & R3_10 & R3_11 & R3_12 & R3_1 & R3_2 & R3_8 & R3_9 & R3_18 & R3_20 & R3_21 & R3_22 & R3_3 & R3_4 & R3S).
      hide SRCp.
      eapply srz_msteps; [exact (ms_halt _ MS1) | exact (ms_lazy _ MS1) | exact RUNB | ].
      rewrite !sw_lw_bytes by assumption.
      set (M3 := wbytes (wbytes (wbytes (wbytes (wbytes M2
                   (Z_to_bv 64 (p + 20 * cap + 16)) w16) (Z_to_bv 64 (p + 20 * cap)) w0) (Z_to_bv 64 (p + 20 * cap + 4)) w4) (Z_to_bv 64 (p + 20 * cap + 8)) w8) (Z_to_bv 64 (p + 20 * cap + 12)) w12).
      assert (ST23 : stores_in (zwin d (d + 20)) M2 M3).
      { unfold M3, d. eapply stores_in_wbytes_more; [eapply stores_in_wbytes_more; [eapply stores_in_wbytes_more; [eapply stores_in_wbytes_more; [apply stores_in_wbytes| | |]| | |]| | |]| | |];
          rewrite ?L16, ?L12, ?L8, ?L4, ?L0; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; try lia; intros a Ha; unfold zwin in *; lia. }

      assert (HDp3 : mdef M3 p n4) by (eapply stores_in_mdef; [exact ST23 | exact HDp]).
      assert (HDb3 : mdef M3 b (20 * cap)).
      { destruct (Z.eq_dec cap 0) as [Hc0|Hcnz]; [intros i Hi; lia|].
        assert (Hbnz : b <> 0) by (unhide Hb; destruct Hb as [[Hb00 Hc00]|(Hbp & _)]; lia).
        destruct (BUF Hbnz) as (HDb & Hbce & _).
        intros i Hi. rewrite (proj1 ST23) by (rewrite u64_of_Z by lia; unfold zwin, d; destruct (BUFp Hbnz); lia).
        rewrite PRES2 by (right; right; right; split; [exact Hbnz | lia]).
        exact (stores_in_mdef _ _ _ _ _ ST1 HDb i Hi). }
      destruct (mdef_rdn SEGS M3 b (20 * cap) 0 (Z.to_nat (20 * cap)) HDb3 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (obs & OBS & OBSL).
      rewrite Z.add_0_r in OBS.
      assert (MC : mcH SEGS M3 (Z_to_bv 64 p) (Z_to_bv 64 b) (20 * cap) obs).
      { constructor.
        - lia.
        - exact OBSL.
        - rewrite OBSL. exact OBS.
        - rewrite OBSL. apply (mdef_store_ok SEGS M3 p n4); try lia. exact HDp3.
        - rewrite !u64_of_Z by lia. unhide Hb. destruct Hb as [[Hb00 Hc00]|(Hbp & Hal & Hcp & Hbc & HIn & Hdj)].
          + right. lia.
          + destruct (BUFp ltac:(lia)); [right|left]; lia.
        - rewrite u64_of_Z by lia. lia.
        - rewrite u64_of_Z by lia. lia. }
      destruct (u1_memcpy M3 (Z_to_bv 64 p) (Z_to_bv 64 b) (20 * cap) obs (seg_rom SEGS) R3 (Z_to_bv 64 0x6beb8)
                  MC ltac:(unfold ret_ok; apply bv_eq; vm_compute; reflexivity)
                  ltac:(rewrite R3_1; apply bv_eq; vm_compute; reflexivity)
                  R3_10 R3_11 R3_12)
        as (R4 & RUN4 & KEEP4).
      eapply srz_msteps; [exact (ms_halt _ MS1) | exact (ms_lazy _ MS1) | | ].
      { lazymatch goal with |- msteps _ (mkst _ ?pc _ _) _ =>
          replace pc with u1_memcpy_entry by (apply bv_eq; vm_compute; reflexivity) end.
        exact RUN4. }
      set (M4 := wbytes M3 (Z_to_bv 64 p) obs) in *.
      assert (ST34 : stores_in (zwin p (p + 20 * cap)) M3 M4).
      { unfold M4. apply stores_in_wbytes; rewrite ?OBSL; try lia. intros a Ha. unfold zwin. lia. }
      assert (R4_2 : getr R4 2%bv = Z_to_bv 64 (sp - 64)) by (rewrite (KEEP4 2%bv) by in_cs; exact R3_2).
      assert (R4_8 : getr R4 8%bv = Z_to_bv 64 b) by (rewrite (KEEP4 8%bv) by in_cs; exact R3_8).
      assert (R4_9 : getr R4 9%bv = Z_to_bv 64 v) by (rewrite (KEEP4 9%bv) by in_cs; exact R3_9).
      assert (R4_18 : getr R4 18%bv = Z_to_bv 64 (20 * cap)) by (rewrite (KEEP4 18%bv) by in_cs; exact R3_18).
      assert (R4_20 : getr R4 20%bv = Z_to_bv 64 p) by (rewrite (KEEP4 20%bv) by in_cs; exact R3_20).
      assert (R4_21 : getr R4 21%bv = Z_to_bv 64 (d + 20)) by (rewrite (KEEP4 21%bv) by in_cs; rewrite R3_21; unfold d; reflexivity).
      assert (R4_22 : getr R4 22%bv = Z_to_bv 64 (p + n4)) by (rewrite (KEEP4 22%bv) by in_cs; rewrite R3_22; unfold n4; reflexivity).
      assert (R4_3 : getr R4 3%bv = getr R 3%bv) by (rewrite (KEEP4 3%bv) by in_cs; rewrite R3_3; exact R2_3).
      assert (R4_4 : getr R4 4%bv = getr R 4%bv) by (rewrite (KEEP4 4%bv) by in_cs; rewrite R3_4; exact R2_4).
      assert (R4S : forall r, In r [23; 24; 25; 26; 27]%bv -> getr R4 r = getr R r).
      { intros r Hr. pose proof Hr as Hr'.
        repeat (destruct Hr as [<-|Hr]; [rewrite (KEEP4 _) by in_cs; rewrite (R3S _) by in_cs; apply R2S; in_cs |]). destruct Hr. }

      set (W := (sp - (64 + (16 + MALLOC_STACK MI)), sp)).
      set (FT := fun a => zwin v (v + 24) a \/ (b <> 0 /\ zwin b (b + 20 * cap) a) \/ zwin p (p + 20 * vgrow cap) a).
      assert (TAIL : forall A2 R6 M6 model2,
        ainv MI A2 M6 model2 -> mstd model2 -> m_fs model2 = m_fs model -> m_fds model2 = m_fds model ->
        sx_inv ST s M6 ->
        getr R6 2%bv = Z_to_bv 64 (sp - 64) -> getr R6 21%bv = Z_to_bv 64 (d + 20) ->
        getr R6 3%bv = getr R 3%bv -> getr R6 4%bv = getr R 4%bv ->
        (forall r, In r [23; 24; 25; 26; 27]%bv -> getr R6 r = getr R r) ->
        agree_on (zwin (sp - 64) sp) M1 M6 ->
        mdef M6 v 24 -> fld SEGS M6 v 8 p -> fld SEGS M6 (v + 8) 8 (d + 20) -> fld SEGS M6 (v + 16) 8 (p + n4) ->
        In (p, n4) (live MI A2) ->
        (forall a, v <= a < v + 24 -> ~ owned MI A2 a /\ ~ in_ranges [(0x10000, 0x124000)] a) ->
        eff MI A A2 M M6 W FT -> lapply (live MI A) (LAdd p n4 :: del_if b) (live MI A2) ->
        srealizes SEGS (mkCfg (@mkst fx R6 (Z_to_bv 64 0x6bed4) M6 (seg_rom SEGS)) model2) K).
      { intros A2 R6 M6 model2 AI2 MS2 Hfs2 Hfds2 SX2 R6_2 R6_21 R6_3 R6_4 R6S AG6 HDv6 G0 G1 G2 HinP2 HDR2 EFF6 LAP.
        assert (SLT : forall a vv, sp - 64 <= a -> a + 8 <= sp -> rdn SEGS M1 (Z_to_bv 64 a) 8 = Some vv -> rdn SEGS M6 (Z_to_bv 64 a) 8 = Some vv).
        { intros a vv H1 H2 H3. rewrite (rdn_agree_win SEGS M1 M6); [exact H3 | lia | cbn; lia |].
          eapply agree_on_weaken; [exact AG6|]. intros a' Ha. unfold zwin in *. cbn in Ha. lia. }
        eapply srz_msteps; [exact (ms_halt _ MS2) | exact (ms_lazy _ MS2) | | ].
        { apply (epilogue fx R6 M6 sp ret (Z_to_bv 64 (d + 20))
                 (getr R 8%bv) (getr R 9%bv) (getr R 18%bv) (getr R 19%bv) (getr R 20%bv) (getr R 21%bv) (getr R 22%bv));
            [ exact R6_2 | exact R6_21 | lia
            | apply SLT; [lia|lia|rdn_fix SL1] | apply SLT; [lia|lia|rdn_fix SL2] | apply SLT; [lia|lia|rdn_fix SL3]
            | apply SLT; [lia|lia|rdn_fix SL4] | apply SLT; [lia|lia|rdn_fix SL5] | apply SLT; [lia|lia|rdn_fix SL6]
            | apply SLT; [lia|lia|rdn_fix SL7] | apply SLT; [lia|lia|rdn_fix SL8] | exact Hret ]. }
        eapply (CONT A2 _ M6 model2 p).
        - constructor.
          + exact AI2. + exact MS2. + exact Hfs2. + exact Hfds2. + exact SX2.
          + intros r Hr; unfold callee_saved in Hr.
            repeat (destruct Hr as [<-|Hr]; [gres; first [reflexivity | symmetry; assumption | rewrite ?R6_3, ?R6_4; reflexivity | apply R6S; in_cs ] |]).
            destruct Hr.
        - unhide HDRp. unfold vgrow in *.
          unfold CRep.vec_opnd, OPND_SZ.
          split; [exact Hv0|]. split; [exact Hv1|]. split; [exact HDv6|].
          split; [lia|].
          split. { right. split; [lia|]. split; [exact Hpal|]. split; [lia|]. split; [lia|].
                   split; [replace (20 * Z.max (2 * cap) (cap + 1)) with n4 by lia; exact HinP2 | lia]. }
          split. { exact G0. }
          split. { replace (p + 20 * (cap + 1)) with (d + 20) by (unfold d; lia). exact G1. }
          replace (p + 20 * Z.max (2 * cap) (cap + 1)) with (p + n4) by lia. exact G2.
        - gres. unfold d. f_equal. lia.
        - replace (20 * vgrow cap) with n4 by (unfold vgrow; lia). exact LAP.
        - eapply eff_weaken; [exact EFF6 | intros a' H; exact H]. }

      assert (HDv2 : mdef M2 v 24).
      { eapply (mdef_through (fun a => owned MI A a \/ errno_win Ly.L a)); [exact DEF1 | eapply stores_in_mdef; [exact ST1 | exact HDv] | lia | lia |].
        intros a Ha [Ho|He]; [exact (proj1 (HDR a ltac:(lia)) Ho) | exact (proj2 (HDR a ltac:(lia)) (ly_errno_img a He))]. }
      assert (HDv4 : mdef M4 v 24) by (eapply stores_in_mdef; [exact ST34|]; eapply stores_in_mdef; [exact ST23 | exact HDv2]).
      set (M5 := wbytes (wbytes (wbytes M4 (Z_to_bv 64 v) (word_to_le_bytes 8 (Z_to_bv 64 p)))
                                (Z_to_bv 64 (v + 8)) (word_to_le_bytes 8 (Z_to_bv 64 (d + 20))))
                         (Z_to_bv 64 (v + 16)) (word_to_le_bytes 8 (Z_to_bv 64 (p + n4)))).
      assert (ST25 : stores_in (fun a => zwin p (p + n4) a \/ zwin v (v + 24) a) M2 M5).
      { eapply stores_in_trans; [eapply stores_in_trans; [eapply stores_in_weaken; [exact ST23|] | eapply stores_in_weaken; [exact ST34|]] |].
        - intros a Ha; left; unfold zwin, d in *; lia.
        - intros a Ha; left; unfold zwin in *; lia.
        - unfold M5. eapply stores_in_wbytes_more; [eapply stores_in_wbytes_more; [apply stores_in_wbytes| | |] | | |];
            rewrite ?length_N_to_le_bytes; cbn; try lia; intros a Ha; right; unfold zwin; lia. }
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
      assert (G1 : fld SEGS M5 (v + 8) 8 (d + 20)).
      { unfold fld, M5. rewrite rdn_wbytes_out_Z by (rewrite length_N_to_le_bytes; cbn; lia).
        apply rdn_wbytes_hit8. rewrite u64_of_Z by lia. unfold d. lia. }
      assert (G2 : fld SEGS M5 (v + 16) 8 (p + n4)).
      { unfold fld, M5. apply rdn_wbytes_hit8. rewrite u64_of_Z by lia. lia. }
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
        stw F_6be78 D_6be78 (Z_to_bv 64 v) (Z_to_bv 64 p) ltac:(ok_mdef HDv4).
        stw F_6be7c D_6be7c (Z_to_bv 64 (v + 8)) (Z_to_bv 64 (d + 20)) ltac:(ok_mdef HDv4).
        stw F_6be80 D_6be80 (Z_to_bv 64 (v + 16)) (Z_to_bv 64 (p + n4)) ltac:(ok_mdef HDv4).
        apply mst_refl. }
      fold M5.
      assert (HDv5 : mdef M5 v 24) by (unfold M5; apply mdef_wbytes, mdef_wbytes, mdef_wbytes; exact HDv4).
      destruct (Z.eq_dec b 0) as [Hbz|Hbnz].
      *
        eapply srz_msteps; [exact (ms_halt _ MS1) | exact (ms_lazy _ MS1) | | ].
        { norm_pc. stepb_tk F_6be84 D_6be84 ltac:(rewrite R4_8, Hbz; apply c_eq_refl). apply mst_refl. }
        lazymatch goal with |- srealizes _ (mkCfg (mkst _ ?pc _ _) _) _ =>
          replace pc with (Z_to_bv 64 0x6bed4) by (apply bv_eq; vm_compute; reflexivity) end.
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
        { norm_pc. stepb_ft F_6be84 D_6be84 ltac:(rewrite R4_8; rewrite c_eq_Z' by lia; apply Z.eqb_neq; lia).
          sv F_6be88 D_6be88 (Z_to_bv 64 b).
          sv F_6be8c D_6be8c (Z_to_bv 64 (20 * cap)).
          stepj F_6be90 D_6be90. apply mst_refl. }
        lazymatch goal with |- srealizes _ (mkCfg (mkst ?r ?pc _ _) _) _ =>
          replace pc with (Z_to_bv 64 DEL1) by (apply bv_eq; vm_compute; reflexivity); set (R5 := r) end.
        eapply (u1_op_delete1_spec MI fx A1 R5 M5 model1 b (20 * cap) (sp - 64) 0x6bed4 K).
        -- eapply (stores_in_ainv SEGS Ly.L MI); [exact AI1 | exact ST25 |].
           intros a [Ha|Ha]; [apply Hpown | apply HDR1]; unfold zwin in Ha; lia.
        -- exact MS1.
        -- eapply (roc_stores Ly.L); [exact ROC2 | exact ST25 |]. intros a Ha. cbn [ly_img Ly.L]. destruct Ha as [Ha|Ha]; [apply Hpown | apply HDR1]; unfold zwin in Ha; lia.
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
           { intros ->. destruct LADD as [_ Hnin]. apply Hnin. apply in_map_iff. exists (b, 20 * cap). split; [reflexivity|exact HIn]. }
           pose proof (BUFp ltac:(lia)) as BUFp'.
           unhide Hdj.
           assert (FSEP : forall a, (sp - 64 <= a < sp) \/ (v <= a < v + 24) \/ (p <= a < p + n4) ->
                            ~ owned MI A1 a /\ ~ (b <= a < b + 20 * cap) /\ ~ zwin (sp - 64 - MALLOC_STACK MI) (sp - 64) a /\ ~ in_ranges (ly_img Ly.L) a).
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
           ++ rewrite (KEPT6 21%bv) by in_cs. unfold R5. gres. exact R4_21.
           ++ rewrite (KEPT6 3%bv) by in_cs. unfold R5. gres. exact R4_3.
           ++ rewrite (KEPT6 4%bv) by in_cs. unfold R5. gres. exact R4_4.
           ++ intros r Hr. pose proof Hr as Hr'.
              repeat (destruct Hr as [<-|Hr]; [rewrite (KEPT6 _) by in_cs; unfold R5; gres; apply R4S; exact Hr' |]). destruct Hr.
           ++ intros a Ha. rewrite (AG56 (sp - 64) sp); [apply AG15; exact Ha | lia | lia | left; lia | exact Ha].
           ++ eapply (mdef_through (fun a => owned MI A1 a \/ ((b <= a < b + 20 * cap) \/ errno_win Ly.L a))); [exact DEF2 | exact HDv5 | lia | lia |].
              intros a Ha [Ho|[Hblk|He]]; [exact (proj1 (HDR1 a Ha) Ho)  |  lia | exact (proj2 (HDR1 a Ha) (ly_errno_img a He))].
           ++ eapply fld_agree; [lia | cbn; lia | exact G0 |]. apply AG56; cbn; lia.
           ++ eapply fld_agree; [lia | cbn; lia | exact G1 |]. apply AG56; cbn; lia.
           ++ eapply fld_agree; [lia | cbn; lia | exact G2 |]. apply AG56; cbn; lia.
           ++ eapply live_del_keeps; [exact LDEL | exact HinP | exact Hpb].
           ++ intros a Ha. split; [| apply HDR1; lia]. intros Ho. destruct (OWN2 a Ho) as [Ho1|Hblk]; [exact (proj1 (HDR1 a Ha) Ho1) | lia].
           ++ eapply eff_weaken.
              ** eapply (eff_trans MI); [exact EFF5 | | intros a Ha; apply (stack_sep A2 M6 model2 a AI2); unfold W_of, W in Ha; cbn in Ha; lia].
                 eapply (eff_of_del MI A1 A2 M5 M6 W FT b (20 * cap)); try eassumption.
                 --- intros a Ha. unfold W_of, W, zwin in *. cbn. lia.
                 --- intros a Ha. unfold FT. right; left. split; [lia|]. unfold zwin. lia.
                 --- intros a Ha. destruct (BUF ltac:(lia)) as (_ & _ & Hbown'). exact (proj2 (Hbown' a Ha)).
              ** intros a [H|H]; exact H.
           ++ cbn. exists (live MI A1). split; [exact LADD|]. unfold del_if. destruct (Z.eqb_spec b 0); [lia|].
              cbn. exists (live MI A2). split; [exact LDEL | reflexivity].
  Qed.
End OpndPbSlow.
