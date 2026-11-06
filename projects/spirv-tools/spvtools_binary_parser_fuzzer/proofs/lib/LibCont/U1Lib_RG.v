(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Ubsan.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StepTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.WalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StartupTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SumWalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MemSplit OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ShapeAlg OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SRealizes OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefReadLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibEff OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MmapSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibMaskBits OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.U1Layout.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.CRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.StrLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.Lib_RG OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.U1Facts.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Module U1_code_6dcb4_6ddf0.

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Ubsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_6dcb4 : bv 32 := 0x000016b7.
Lemma F_6dcb4 : fetch_word Ubsan.M.loaded_segments (0x6dcf4 : word) = Some W_6dcb4.
Proof. vm_refl. Qed.
Lemma D_6dcb4 : decode_any W_6dcb4 = Some (Lui 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dcb8 : bv 32 := 0xfffa7797.
Lemma F_6dcb8 : fetch_word Ubsan.M.loaded_segments (0x6dcf8 : word) = Some W_6dcb8.
Proof. vm_refl. Qed.
Lemma D_6dcb8 : decode_any W_6dcb8 = Some (Auipc 15 1048487, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dcbc : bv 32 := 0x5716871b.
Lemma F_6dcbc : fetch_word Ubsan.M.loaded_segments (0x6dcfc : word) = Some W_6dcbc.
Proof. vm_refl. Qed.
Lemma D_6dcbc : decode_any W_6dcbc = Some (OpImm32 14 13 1393, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dcc0 : bv 32 := 0xc807b683.
Lemma F_6dcc0 : fetch_word Ubsan.M.loaded_segments (0x6dd00 : word) = Some W_6dcc0.
Proof. vm_refl. Qed.
Lemma D_6dcc0 : decode_any W_6dcc0 = Some (Load SZ8 true 13 15 3200, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dcc4 : bv 32 := 0x00e53023.
Lemma F_6dcc4 : fetch_word Ubsan.M.loaded_segments (0x6dd04 : word) = Some W_6dcc4.
Proof. vm_refl. Qed.
Lemma D_6dcc4 : decode_any W_6dcc4 = Some (Store SZ8 10 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dcc8 : bv 32 := 0x00850793.
Lemma F_6dcc8 : fetch_word Ubsan.M.loaded_segments (0x6dd08 : word) = Some W_6dcc8.
Proof. vm_refl. Qed.
Lemma D_6dcc8 : decode_any W_6dcc8 = Some (OpImm ALU_ADD 15 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dccc : bv 32 := 0x00100813.
Lemma F_6dccc : fetch_word Ubsan.M.loaded_segments (0x6dd0c : word) = Some W_6dccc.
Proof. vm_refl. Qed.
Lemma D_6dccc : decode_any W_6dccc = Some (OpImm ALU_ADD 16 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dcd0 : bv 32 := 0x13800893.
Lemma F_6dcd0 : fetch_word Ubsan.M.loaded_segments (0x6dd10 : word) = Some W_6dcd0.
Proof. vm_refl. Qed.
Lemma D_6dcd0 : decode_any W_6dcd0 = Some (OpImm ALU_ADD 17 0 312, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dcd4 : bv 32 := 0x03e75293.
Lemma F_6dcd4 : fetch_word Ubsan.M.loaded_segments (0x6dd14 : word) = Some W_6dcd4.
Proof. vm_refl. Qed.
Lemma D_6dcd4 : decode_any W_6dcd4 = Some (ShiftImm ALU_SRL 5 14 62, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dcd8 : bv 32 := 0x00e2c733.
Lemma F_6dcd8 : fetch_word Ubsan.M.loaded_segments (0x6dd18 : word) = Some W_6dcd8.
Proof. vm_refl. Qed.
Lemma D_6dcd8 : decode_any W_6dcd8 = Some (Op ALU_XOR 14 5 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dcdc : bv 32 := 0x02d70733.
Lemma F_6dcdc : fetch_word Ubsan.M.loaded_segments (0x6dd1c : word) = Some W_6dcdc.
Proof. vm_refl. Qed.
Lemma D_6dcdc : decode_any W_6dcdc = Some (Mul M_MUL 14 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dce0 : bv 32 := 0x01070733.
Lemma F_6dce0 : fetch_word Ubsan.M.loaded_segments (0x6dd20 : word) = Some W_6dce0.
Proof. vm_refl. Qed.
Lemma D_6dce0 : decode_any W_6dce0 = Some (Op ALU_ADD 14 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dce4 : bv 32 := 0x00180813.
Lemma F_6dce4 : fetch_word Ubsan.M.loaded_segments (0x6dd24 : word) = Some W_6dce4.
Proof. vm_refl. Qed.
Lemma D_6dce4 : decode_any W_6dce4 = Some (OpImm ALU_ADD 16 16 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dce8 : bv 32 := 0x00e7b023.
Lemma F_6dce8 : fetch_word Ubsan.M.loaded_segments (0x6dd28 : word) = Some W_6dce8.
Proof. vm_refl. Qed.
Lemma D_6dce8 : decode_any W_6dce8 = Some (Store SZ8 15 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dcec : bv 32 := 0x00878793.
Lemma F_6dcec : fetch_word Ubsan.M.loaded_segments (0x6dd2c : word) = Some W_6dcec.
Proof. vm_refl. Qed.
Lemma D_6dcec : decode_any W_6dcec = Some (OpImm ALU_ADD 15 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dcf0 : bv 32 := 0xff1812e3.
Lemma F_6dcf0 : fetch_word Ubsan.M.loaded_segments (0x6dd30 : word) = Some W_6dcf0.
Proof. vm_refl. Qed.
Lemma D_6dcf0 : decode_any W_6dcf0 = Some (Branch BC_NE 16 17 8164, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dcf4 : bv 32 := 0x7ff50513.
Lemma F_6dcf4 : fetch_word Ubsan.M.loaded_segments (0x6dd34 : word) = Some W_6dcf4.
Proof. vm_refl. Qed.
Lemma D_6dcf4 : decode_any W_6dcf4 = Some (OpImm ALU_ADD 10 10 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dcf8 : bv 32 := 0x1c0530a3.
Lemma F_6dcf8 : fetch_word Ubsan.M.loaded_segments (0x6dd38 : word) = Some W_6dcf8.
Proof. vm_refl. Qed.
Lemma D_6dcf8 : decode_any W_6dcf8 = Some (Store SZ8 10 0 449, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dcfc : bv 32 := 0x00058513.
Lemma F_6dcfc : fetch_word Ubsan.M.loaded_segments (0x6dd3c : word) = Some W_6dcfc.
Proof. vm_refl. Qed.
Lemma D_6dcfc : decode_any W_6dcfc = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dd00 : bv 32 := 0x00060593.
Lemma F_6dd00 : fetch_word Ubsan.M.loaded_segments (0x6dd40 : word) = Some W_6dd00.
Proof. vm_refl. Qed.
Lemma D_6dd00 : decode_any W_6dd00 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dd04 : bv 32 := 0x0040006f.
Lemma F_6dd04 : fetch_word Ubsan.M.loaded_segments (0x6dd44 : word) = Some W_6dd04.
Proof. vm_refl. Qed.
Lemma D_6dd04 : decode_any W_6dd04 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dd08 : bv 32 := 0x0a050e63.
Lemma F_6dd08 : fetch_word Ubsan.M.loaded_segments (0x6dd48 : word) = Some W_6dd08.
Proof. vm_refl. Qed.
Lemma D_6dd08 : decode_any W_6dd08 = Some (Branch BC_EQ 10 0 188, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dd0c : bv 32 := 0xffc58613.
Lemma F_6dd0c : fetch_word Ubsan.M.loaded_segments (0x6dd4c : word) = Some W_6dd0c.
Proof. vm_refl. Qed.
Lemma D_6dd0c : decode_any W_6dd0c = Some (OpImm ALU_ADD 12 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dd10 : bv 32 := 0x0cb65e63.
Lemma F_6dd10 : fetch_word Ubsan.M.loaded_segments (0x6dd50 : word) = Some W_6dd10.
Proof. vm_refl. Qed.
Lemma D_6dd10 : decode_any W_6dd10 = Some (Branch BC_GE 12 11 220, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dd14 : bv 32 := 0x00c026b3.
Lemma F_6dd14 : fetch_word Ubsan.M.loaded_segments (0x6dd54 : word) = Some W_6dd14.
Proof. vm_refl. Qed.
Lemma D_6dd14 : decode_any W_6dd14 = Some (Op ALU_SLT 13 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dd18 : bv 32 := 0x40d006b3.
Lemma F_6dd18 : fetch_word Ubsan.M.loaded_segments (0x6dd58 : word) = Some W_6dd18.
Proof. vm_refl. Qed.
Lemma D_6dd18 : decode_any W_6dd18 = Some (Op ALU_SUB 13 0 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dd1c : bv 32 := 0x00c6f633.
Lemma F_6dd1c : fetch_word Ubsan.M.loaded_segments (0x6dd5c : word) = Some W_6dd1c.
Proof. vm_refl. Qed.
Lemma D_6dd1c : decode_any W_6dd1c = Some (Op ALU_AND 12 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dd20 : bv 32 := 0x00500693.
Lemma F_6dd20 : fetch_word Ubsan.M.loaded_segments (0x6dd60 : word) = Some W_6dd20.
Proof. vm_refl. Qed.
Lemma D_6dd20 : decode_any W_6dd20 = Some (OpImm ALU_ADD 13 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dd24 : bv 32 := 0x00d64463.
Lemma F_6dd24 : fetch_word Ubsan.M.loaded_segments (0x6dd64 : word) = Some W_6dd24.
Proof. vm_refl. Qed.
Lemma D_6dd24 : decode_any W_6dd24 = Some (Branch BC_LT 12 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dd28 : bv 32 := 0x00500613.
Lemma F_6dd28 : fetch_word Ubsan.M.loaded_segments (0x6dd68 : word) = Some W_6dd28.
Proof. vm_refl. Qed.
Lemma D_6dd28 : decode_any W_6dd28 = Some (OpImm ALU_ADD 12 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dd2c : bv 32 := 0xfff54693.
Lemma F_6dd2c : fetch_word Ubsan.M.loaded_segments (0x6dd6c : word) = Some W_6dd2c.
Proof. vm_refl. Qed.
Lemma D_6dd2c : decode_any W_6dd2c = Some (OpImm ALU_XOR 13 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dd30 : bv 32 := 0x0ac6ee63.
Lemma F_6dd30 : fetch_word Ubsan.M.loaded_segments (0x6dd70 : word) = Some W_6dd30.
Proof. vm_refl. Qed.
Lemma D_6dd30 : decode_any W_6dd30 = Some (Branch BC_LTU 13 12 188, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dd34 : bv 32 := 0x02060713.
Lemma F_6dd34 : fetch_word Ubsan.M.loaded_segments (0x6dd74 : word) = Some W_6dd34.
Proof. vm_refl. Qed.
Lemma D_6dd34 : decode_any W_6dd34 = Some (OpImm ALU_ADD 14 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dd38 : bv 32 := 0x00058693.
Lemma F_6dd38 : fetch_word Ubsan.M.loaded_segments (0x6dd78 : word) = Some W_6dd38.
Proof. vm_refl. Qed.
Lemma D_6dd38 : decode_any W_6dd38 = Some (OpImm ALU_ADD 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dd3c : bv 32 := 0x00e5c463.
Lemma F_6dd3c : fetch_word Ubsan.M.loaded_segments (0x6dd7c : word) = Some W_6dd3c.
Proof. vm_refl. Qed.
Lemma D_6dd3c : decode_any W_6dd3c = Some (Branch BC_LT 11 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dd40 : bv 32 := 0x00070693.
Lemma F_6dd40 : fetch_word Ubsan.M.loaded_segments (0x6dd80 : word) = Some W_6dd40.
Proof. vm_refl. Qed.
Lemma D_6dd40 : decode_any W_6dd40 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dd44 : bv 32 := 0x00c59863.
Lemma F_6dd44 : fetch_word Ubsan.M.loaded_segments (0x6dd84 : word) = Some W_6dd44.
Proof. vm_refl. Qed.
Lemma D_6dd44 : decode_any W_6dd44 = Some (Branch BC_NE 11 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dd54 : bv 32 := 0xfffa7717.
Lemma F_6dd54 : fetch_word Ubsan.M.loaded_segments (0x6dd94 : word) = Some W_6dd54.
Proof. vm_refl. Qed.
Lemma D_6dd54 : decode_any W_6dd54 = Some (Auipc 14 1048487, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dd58 : bv 32 := 0xbfc73883.
Lemma F_6dd58 : fetch_word Ubsan.M.loaded_segments (0x6dd98 : word) = Some W_6dd58.
Proof. vm_refl. Qed.
Lemma D_6dd58 : decode_any W_6dd58 = Some (Load SZ8 true 17 14 3068, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dd5c : bv 32 := 0x40c686b3.
Lemma F_6dd5c : fetch_word Ubsan.M.loaded_segments (0x6dd9c : word) = Some W_6dd5c.
Proof. vm_refl. Qed.
Lemma D_6dd5c : decode_any W_6dd5c = Some (Op ALU_SUB 13 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dd60 : bv 32 := 0xfffa7717.
Lemma F_6dd60 : fetch_word Ubsan.M.loaded_segments (0x6dda0 : word) = Some W_6dd60.
Proof. vm_refl. Qed.
Lemma D_6dd60 : decode_any W_6dd60 = Some (Auipc 14 1048487, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dd64 : bv 32 := 0xbc073803.
Lemma F_6dd64 : fetch_word Ubsan.M.loaded_segments (0x6dda4 : word) = Some W_6dd64.
Proof. vm_refl. Qed.
Lemma D_6dd64 : decode_any W_6dd64 = Some (Load SZ8 true 16 14 3008, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dd68 : bv 32 := 0x011688b3.
Lemma F_6dd68 : fetch_word Ubsan.M.loaded_segments (0x6dda8 : word) = Some W_6dd68.
Proof. vm_refl. Qed.
Lemma D_6dd68 : decode_any W_6dd68 = Some (Op ALU_ADD 17 13 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dd6c : bv 32 := 0x02060713.
Lemma F_6dd6c : fetch_word Ubsan.M.loaded_segments (0x6ddac : word) = Some W_6dd6c.
Proof. vm_refl. Qed.
Lemma D_6dd6c : decode_any W_6dd6c = Some (OpImm ALU_ADD 14 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dd70 : bv 32 := 0x00c506b3.
Lemma F_6dd70 : fetch_word Ubsan.M.loaded_segments (0x6ddb0 : word) = Some W_6dd70.
Proof. vm_refl. Qed.
Lemma D_6dd70 : decode_any W_6dd70 = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dd74 : bv 32 := 0x00e5c463.
Lemma F_6dd74 : fetch_word Ubsan.M.loaded_segments (0x6ddb4 : word) = Some W_6dd74.
Proof. vm_refl. Qed.
Lemma D_6dd74 : decode_any W_6dd74 = Some (Branch BC_LT 11 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dd78 : bv 32 := 0x00070593.
Lemma F_6dd78 : fetch_word Ubsan.M.loaded_segments (0x6ddb8 : word) = Some W_6dd78.
Proof. vm_refl. Qed.
Lemma D_6dd78 : decode_any W_6dd78 = Some (OpImm ALU_ADD 11 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dd7c : bv 32 := 0x00000713.
Lemma F_6dd7c : fetch_word Ubsan.M.loaded_segments (0x6ddbc : word) = Some W_6dd7c.
Proof. vm_refl. Qed.
Lemma D_6dd7c : decode_any W_6dd7c = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dd80 : bv 32 := 0xfffa7517.
Lemma F_6dd80 : fetch_word Ubsan.M.loaded_segments (0x6ddc0 : word) = Some W_6dd80.
Proof. vm_refl. Qed.
Lemma D_6dd80 : decode_any W_6dd80 = Some (Auipc 10 1048487, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dd84 : bv 32 := 0xc7053783.
Lemma F_6dd84 : fetch_word Ubsan.M.loaded_segments (0x6ddc4 : word) = Some W_6dd84.
Proof. vm_refl. Qed.
Lemma D_6dd84 : decode_any W_6dd84 = Some (Load SZ8 true 15 10 3184, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dd88 : bv 32 := 0x0108c533.
Lemma F_6dd88 : fetch_word Ubsan.M.loaded_segments (0x6ddc8 : word) = Some W_6dd88.
Proof. vm_refl. Qed.
Lemma D_6dd88 : decode_any W_6dd88 = Some (Op ALU_XOR 10 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dd8c : bv 32 := 0x40c585b3.
Lemma F_6dd8c : fetch_word Ubsan.M.loaded_segments (0x6ddcc : word) = Some W_6dd8c.
Proof. vm_refl. Qed.
Lemma D_6dd8c : decode_any W_6dd8c = Some (Op ALU_SUB 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dd90 : bv 32 := 0xfff6c613.
Lemma F_6dd90 : fetch_word Ubsan.M.loaded_segments (0x6ddd0 : word) = Some W_6dd90.
Proof. vm_refl. Qed.
Lemma D_6dd90 : decode_any W_6dd90 = Some (OpImm ALU_XOR 12 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dd94 : bv 32 := 0x04e66c63.
Lemma F_6dd94 : fetch_word Ubsan.M.loaded_segments (0x6ddd4 : word) = Some W_6dd94.
Proof. vm_refl. Qed.
Lemma D_6dd94 : decode_any W_6dd94 = Some (Branch BC_LTU 12 14 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dd98 : bv 32 := 0x00e68833.
Lemma F_6dd98 : fetch_word Ubsan.M.loaded_segments (0x6ddd8 : word) = Some W_6dd98.
Proof. vm_refl. Qed.
Lemma D_6dd98 : decode_any W_6dd98 = Some (Op ALU_ADD 16 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dd9c : bv 32 := 0x00651893.
Lemma F_6dd9c : fetch_word Ubsan.M.loaded_segments (0x6dddc : word) = Some W_6dd9c.
Proof. vm_refl. Qed.
Lemma D_6dd9c : decode_any W_6dd9c = Some (ShiftImm ALU_SLL 17 10 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dda0 : bv 32 := 0x00084803.
Lemma F_6dda0 : fetch_word Ubsan.M.loaded_segments (0x6dde0 : word) = Some W_6dda0.
Proof. vm_refl. Qed.
Lemma D_6dda0 : decode_any W_6dda0 = Some (Load SZ1 false 16 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dda4 : bv 32 := 0x00255293.
Lemma F_6dda4 : fetch_word Ubsan.M.loaded_segments (0x6dde4 : word) = Some W_6dda4.
Proof. vm_refl. Qed.
Lemma D_6dda4 : decode_any W_6dda4 = Some (ShiftImm ALU_SRL 5 10 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dda8 : bv 32 := 0x005888b3.
Lemma F_6dda8 : fetch_word Ubsan.M.loaded_segments (0x6dde8 : word) = Some W_6dda8.
Proof. vm_refl. Qed.
Lemma D_6dda8 : decode_any W_6dda8 = Some (Op ALU_ADD 17 17 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ddac : bv 32 := 0x00f888b3.
Lemma F_6ddac : fetch_word Ubsan.M.loaded_segments (0x6ddec : word) = Some W_6ddac.
Proof. vm_refl. Qed.
Lemma D_6ddac : decode_any W_6ddac = Some (Op ALU_ADD 17 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ddb0 : bv 32 := 0x01088833.
Lemma F_6ddb0 : fetch_word Ubsan.M.loaded_segments (0x6ddf0 : word) = Some W_6ddb0.
Proof. vm_refl. Qed.
Lemma D_6ddb0 : decode_any W_6ddb0 = Some (Op ALU_ADD 16 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ddb4 : bv 32 := 0x00170713.
Lemma F_6ddb4 : fetch_word Ubsan.M.loaded_segments (0x6ddf4 : word) = Some W_6ddb4.
Proof. vm_refl. Qed.
Lemma D_6ddb4 : decode_any W_6ddb4 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ddb8 : bv 32 := 0x00a84533.
Lemma F_6ddb8 : fetch_word Ubsan.M.loaded_segments (0x6ddf8 : word) = Some W_6ddb8.
Proof. vm_refl. Qed.
Lemma D_6ddb8 : decode_any W_6ddb8 = Some (Op ALU_XOR 10 16 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ddbc : bv 32 := 0xfce59ce3.
Lemma F_6ddbc : fetch_word Ubsan.M.loaded_segments (0x6ddfc : word) = Some W_6ddbc.
Proof. vm_refl. Qed.
Lemma D_6ddbc : decode_any W_6ddbc = Some (Branch BC_NE 11 14 8152, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ddc0 : bv 32 := 0x00008067.
Lemma F_6ddc0 : fetch_word Ubsan.M.loaded_segments (0x6de00 : word) = Some W_6ddc0.
Proof. vm_refl. Qed.
Lemma D_6ddc0 : decode_any W_6ddc0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
End U1_code_6dcb4_6ddf0.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac WalkTac StartupTac SumWalkTac StoreOk MemSplit Hoare ShapeAlg
  SRealizes RefMemcpyLib RefReadLib LibIface LibEff MmapSim LibMaskBits U1Layout.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContLib StrLib ContStmts Lib_RG U1Facts.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.U1Lib_RG.U1_code_6dcb4_6ddf0.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation SEGS := Ubsan.M.loaded_segments.

Ltac rdn_fix H :=
  first [ exact H
        | lazymatch goal with |- rdn _ _ (Z_to_bv 64 ?a) _ = _ =>
            lazymatch type of H with rdn _ _ (Z_to_bv 64 ?a') _ = _ =>
              replace a with a' by lia; exact H end end ].
Ltac b2z8 := apply bytes_le_to_Z_8.
Ltac close_pc := lazymatch goal with |- msteps _ ?a ?bb => replace bb with a; [apply mst_refl|] end; f_equal; apply bv_eq; vm_compute; reflexivity.
Ltac wl := lazymatch goal with |- msteps _ (mkst (regupd _ _ ?v) _ _ _) _ => wlit v | |- _ => idtac end.
Ltac snl F D := stepn F D; pin; wl.

Lemma u1_img_K_MTF : rdn SEGS (fun _ => None) (Z_to_bv 64 K_MTF) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 MT_F)).
Proof. vm_refl_bv. Qed.
Lemma u1_img_K1 : rdn SEGS (fun _ => None) (Z_to_bv 64 K1a) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 8298762835598203578)).
Proof. vm_refl_bv. Qed.
Lemma u1_img_K2 : rdn SEGS (fun _ => None) (Z_to_bv 64 K2a) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 14594272307789293969)).
Proof. vm_refl_bv. Qed.
Lemma u1_img_K3 : rdn SEGS (fun _ => None) (Z_to_bv 64 K3a) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 11400714819323198486)).
Proof. vm_refl_bv. Qed.

Lemma bv_signed_any64 : forall a, - 2 ^ 63 <= a < 2 ^ 63 -> bv_signed (Z_to_bv 64 a) = a.
Proof. intros a Ha. rewrite Z_to_bv_signed. apply bv_swrap_small. change (bv_half_modulus 64) with (2 ^ 63). lia. Qed.
Lemma c_lts_ZZ : forall a b, - 2 ^ 63 <= a < 2 ^ 63 -> - 2 ^ 63 <= b < 2 ^ 63 -> c_lts (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof. intros a b Ha Hb. unfold c_lts, bv_lts. rewrite !bv_signed_any64 by lia. reflexivity. Qed.
Lemma lxor_ones64 : forall a, 0 <= a < 2 ^ 64 -> Z.lxor a (2 ^ 64 - 1) = 2 ^ 64 - 1 - a.
Proof.
  intros a Ha. change (2 ^ 64 - 1) with (Z.ones 64) at 1.
  assert (Hl : Z.log2 a < 64).
  { destruct (Z.eq_dec a 0) as [->|Hne]; [cbn; lia|]. apply Z.log2_lt_pow2; lia. }
  rewrite <- Z.ldiff_ones_l_low by lia. rewrite Z.ldiff_land. rewrite Z.land_comm, Z.land_ones by lia.
  unfold Z.lnot. replace (Z.pred (- a)) with ((2 ^ 64 - 1 - a) + (- 1) * 2 ^ 64) by lia.
  rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma v_not_Z : forall a, 0 <= a < 2 ^ 64 -> v_xori (Z_to_bv 64 a) (- 1) = Z_to_bv 64 (2 ^ 64 - 1 - a).
Proof. intros a Ha. unfold v_xori. rewrite u64_of_Z by lia. change (bv_wrap 64 (- 1)) with (2 ^ 64 - 1). rewrite lxor_ones64 by lia. reflexivity. Qed.

Section RGU.
  Context {fx : FPState}.
Context {AC : AllocCeiling}.

  Lemma u1_ro_rdn : forall M (a : Z) (k : nat), ro_clear Ly.L M -> 0x10000 <= a -> a + Z.of_nat k <= 0xe8000 ->
    rdn SEGS M (Z_to_bv 64 a) k = rdn SEGS (fun _ => None) (Z_to_bv 64 a) k.
  Proof using.
    intros M a k ROC H1 H2. symmetry. apply rdn_agree_win; [lia|lia|]. intros x Hx. unfold zwin in Hx.
    symmetry. apply ROC. rewrite u64_of_Z by lia. unfold ro_addr. cbn [ly_img ly_rw ly_relro Ly.L]. rewrite !in_ranges_1. lia.
  Qed.

  Lemma u1_ro_clear_stores : forall W M M', ro_clear Ly.L M -> stores_in W M M' ->
    (forall a, W a -> alloc_ceiling <= a) -> ro_clear Ly.L M'.
  Proof using AC.
    intros W M M' ROC SI HW. eapply ro_clear_frame; [exact ROC | eapply stores_in_frame_eq; [exact SI | intros a Ha; exact Ha] |].
    intros a Hro Hw. pose proof (HW a Hw). pose proof ac_bounds_lit.
    unfold ro_addr in Hro. cbn [ly_img ly_rw ly_relro Ly.L] in Hro. rewrite !in_ranges_1 in Hro. lia.
  Qed.

  Lemma SEEDB_U : forall (i obj : Z) R Mi,
    1 <= i <= 311 -> 0 <= obj -> obj + RG_SZ <= 2 ^ 63 -> mdef Mi obj RG_SZ ->
    getr R 13%bv = Z_to_bv 64 MT_F -> getr R 14%bv = Z_to_bv 64 (Znth (i - 1) mt_init) ->
    getr R 15%bv = Z_to_bv 64 (obj + 8 * i) -> getr R 16%bv = Z_to_bv 64 i ->
    exists R1,
      msteps SEGS (@mkst fx R (Z_to_bv 64 0x6dd14) Mi (seg_rom SEGS))
                  (@mkst fx R1 (Z_to_bv 64 0x6dd30) (wbytes Mi (Z_to_bv 64 (obj + 8 * i)) (word_to_le_bytes 8 (Z_to_bv 64 (Znth i mt_init)))) (seg_rom SEGS))
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
      stepiv F_6dcd4 D_6dcd4 (Z_to_bv 64 (x / 2 ^ 62)) ltac:(gres; pin; imm_norm; rewrite v_srli_Z by lia; reflexivity).
      stepxor F_6dcd8 D_6dcd8 (Z_to_bv 64 (Z.lxor (x / 2 ^ 62) x)) ltac:(gres; pin; rewrite v_xor_Z by lia; reflexivity).
      stepiv F_6dcdc D_6dcdc (Z_to_bv 64 (Z.lxor (x / 2 ^ 62) x * MT_F)) ltac:(gres; pin; apply v_mul_wrap).
      stepiv F_6dce0 D_6dce0 (Z_to_bv 64 (Znth i mt_init)) ltac:(gres; pin; rewrite v_add_wrap; exact Hxi).
      sv F_6dce4 D_6dce4 (Z_to_bv 64 (i + 1)).
      stw F_6dce8 D_6dce8 (Z_to_bv 64 (obj + 8 * i)) (Z_to_bv 64 (Znth i mt_init)) ltac:(ok_mdef HD).
      stepiv F_6dcec D_6dcec (Z_to_bv 64 (obj + 8 * (i + 1))) ltac:(gres; pin; imm_norm; rewrite v_addi_Z by lia; f_equal; lia).
      close_pc.
    - gres. repeat split; try reflexivity; try assumption.
      intros r H5 H14' H15' H16'. rewrite !getr_other by assumption. reflexivity.
  Qed.

  Lemma SEED_U : forall (k : nat) (i obj : Z) R (M Mi : mem),
    1 <= i -> i + Z.of_nat k = 311 -> 0 <= obj -> obj + RG_SZ <= 2 ^ 63 ->
    getr R 13%bv = Z_to_bv 64 MT_F -> getr R 14%bv = Z_to_bv 64 (Znth (i - 1) mt_init) ->
    getr R 15%bv = Z_to_bv 64 (obj + 8 * i) -> getr R 16%bv = Z_to_bv 64 i -> getr R 17%bv = Z_to_bv 64 312 ->
    mdef M obj RG_SZ -> stores_in (zwin obj (obj + RG_SZ)) M Mi ->
    (forall j, 0 <= j < i -> fld SEGS Mi (obj + 8 * j) 8 (Znth j mt_init)) ->
    exists R' M',
      msteps SEGS (@mkst fx R (Z_to_bv 64 0x6dd14) Mi (seg_rom SEGS)) (@mkst fx R' (Z_to_bv 64 0x6dd34) M' (seg_rom SEGS))
      /\ (forall r, r <> 5%bv -> r <> 14%bv -> r <> 15%bv -> r <> 16%bv -> getr R' r = getr R r)
      /\ stores_in (zwin obj (obj + RG_SZ)) M M'
      /\ (forall j, 0 <= j < 312 -> fld SEGS M' (obj + 8 * j) 8 (Znth j mt_init)).
  Proof using fx.
    induction k as [|k IH]; intros i obj R M Mi Hi Hk Ho0 Ho1 H13 H14 H15 H16 H17 HD SI FJ.
    - assert (Hi' : i = 311) by lia.
      destruct (SEEDB_U i obj R Mi ltac:(lia) Ho0 Ho1 ltac:(eapply stores_in_mdef; [exact SI|exact HD]) H13 H14 H15 H16)
        as (R1 & RUN & G13 & G14 & G15 & G16 & GS).
      eexists R1, _. split; [|split; [|split]].
      + eapply msteps_trans; [exact RUN|]. norm_pc.
        stepb_ft F_6dcf0 D_6dcf0 ltac:(rewrite G16, (GS 17%bv), H17 by (intros HH; inversion HH); rewrite Hi'; apply c_eq_refl).
        close_pc.
      + exact GS.
      + eapply stores_in_trans; [exact SI|]. apply stores_in_wbytes; rewrite ?length_N_to_le_bytes; unfold RG_SZ in *; cbn; try lia.
        intros a Ha. unfold zwin. lia.
      + intros j Hj. unfold fld. destruct (Z.eq_dec j i) as [->|Hne].
        * apply rdn_wbytes_hit8. rewrite u64_of_Z by (unfold RG_SZ in *; lia). unfold RG_SZ in *; lia.
        * rewrite rdn_wbytes_out_Z by (rewrite length_N_to_le_bytes; cbn; unfold RG_SZ in *; lia). apply FJ. lia.
    - destruct (SEEDB_U i obj R Mi ltac:(lia) Ho0 Ho1 ltac:(eapply stores_in_mdef; [exact SI|exact HD]) H13 H14 H15 H16)
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
          stepb_tk F_6dcf0 D_6dcf0 ltac:(rewrite G16, (GS 17%bv), H17 by (intros HH; inversion HH); rewrite c_eq_Z' by lia; apply Z.eqb_neq; lia).
          close_pc.
        * intros r Ha Hb Hc Hd. rewrite (GS' r Ha Hb Hc Hd). apply GS; assumption.
        * exact SI'.
        * exact FJ'.
  Qed.

  Lemma CTOR_AU : forall R M (sp ret obj data size : Z),
    ro_clear Ly.L M -> 0 <= obj -> obj + RG_SZ <= 2 ^ 63 -> mdef M obj RG_SZ -> alloc_ceiling <= obj ->
    getr R 10%bv = Z_to_bv 64 obj -> getr R 11%bv = Z_to_bv 64 data -> getr R 12%bv = Z_to_bv 64 size ->
    exists R1 M1,
      msteps SEGS (@mkst fx R (Z_to_bv 64 0x6dcf4) M (seg_rom SEGS)) (@mkst fx R1 (Z_to_bv 64 0x6dd48) M1 (seg_rom SEGS))
      /\ getr R1 10%bv = Z_to_bv 64 data /\ getr R1 11%bv = Z_to_bv 64 size
      /\ (forall r, ~ In r [5; 10; 11; 13; 14; 15; 16; 17]%bv -> getr R1 r = getr R r)
      /\ stores_in (zwin obj (obj + RG_SZ)) M M1
      /\ (forall j, 0 <= j < 312 -> fld SEGS M1 (obj + 8 * j) 8 (Znth j mt_init))
      /\ fld SEGS M1 (obj + 8 * 312) 8 0.
  Proof using fx AC.
    intros R M sp ret obj data size ROC Ho0 Ho1 HD Hoc Ha0 Ha1 Ha2. pose proof ac_bounds_lit as Hcv. unfold RG_SZ in *.
    assert (RDK : rdn SEGS M (Z_to_bv 64 K_MTF) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 MT_F))).
    { rewrite u1_ro_rdn; [exact u1_img_K_MTF | exact ROC | unfold K_MTF; lia | unfold K_MTF; cbn; lia]. }
    set (M0 := wbytes M (Z_to_bv 64 obj) (word_to_le_bytes 8 (Z_to_bv 64 5489))).

    assert (PRE : exists R0, msteps SEGS (@mkst fx R (Z_to_bv 64 0x6dcf4) M (seg_rom SEGS)) (@mkst fx R0 (Z_to_bv 64 0x6dd14) M0 (seg_rom SEGS))
       /\ getr R0 13%bv = Z_to_bv 64 MT_F /\ getr R0 14%bv = Z_to_bv 64 (Znth (1 - 1) mt_init) /\ getr R0 15%bv = Z_to_bv 64 (obj + 8 * 1)
       /\ getr R0 16%bv = Z_to_bv 64 1 /\ getr R0 17%bv = Z_to_bv 64 312
       /\ getr R0 10%bv = Z_to_bv 64 obj /\ getr R0 11%bv = Z_to_bv 64 data /\ getr R0 12%bv = Z_to_bv 64 size
       /\ (forall r, ~ In r [5; 10; 11; 13; 14; 15; 16; 17]%bv -> getr R0 r = getr R r)).
    { eexists. split.
      - norm_pc.
        sv F_6dcb4 D_6dcb4 (Z_to_bv 64 0x1000).
        sv F_6dcb8 D_6dcb8 (Z_to_bv 64 0x14cf8).
        sv F_6dcbc D_6dcbc (Z_to_bv 64 5489).
        ld_step F_6dcc0 D_6dcc0 (word_to_le_bytes 8 (Z_to_bv 64 MT_F)) (Z_to_bv 64 MT_F) ltac:(rdn_fix RDK) ltac:(b2z8).
        stw F_6dcc4 D_6dcc4 (Z_to_bv 64 obj) (Z_to_bv 64 5489) ltac:(ok_mdef HD).
        sv F_6dcc8 D_6dcc8 (Z_to_bv 64 (obj + 8 * 1)).
        sv F_6dccc D_6dccc (Z_to_bv 64 1).
        sv F_6dcd0 D_6dcd0 (Z_to_bv 64 312).
        close_pc.
      - gres. change (1 - 1) with 0. rewrite mt_init_0. repeat split; try reflexivity; try assumption.
        intros r Hr. rewrite !getr_other by (intros ->; apply Hr; (first [solve [clear; cbv; tauto] | cbv; tauto])). reflexivity. }
    destruct PRE as (R0 & RUN0 & G13 & G14 & G15 & G16 & G17 & G10 & G11 & G12 & GS0).
    assert (SI0 : stores_in (zwin obj (obj + 2504)) M M0).
    { unfold M0. apply stores_in_wbytes; rewrite ?length_N_to_le_bytes; cbn; try lia. intros a Ha. unfold zwin. lia. }
    destruct (SEED_U 310 1 obj R0 M M0 ltac:(lia) ltac:(cbn; lia) Ho0 ltac:(unfold RG_SZ; lia) G13 G14 G15 G16 G17
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
      stepiv F_6dcf4 D_6dcf4 (Z_to_bv 64 (obj + 2047)) ltac:(gres; pin; imm_norm; rewrite v_addi_Z by lia; reflexivity).
      stw F_6dcf8 D_6dcf8 (Z_to_bv 64 (obj + 8 * 312)) (Z_to_bv 64 0) ltac:(ok_mdef HD1).
      sv F_6dcfc D_6dcfc (Z_to_bv 64 data).
      sv F_6dd00 D_6dd00 (Z_to_bv 64 size).
      stepj F_6dd04 D_6dd04.
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
  #[local] Ltac other_regs Hs :=
    intros r Hr; rewrite !getr_other by (intros ->; apply Hr; (first [solve [clear; cbv; tauto] | cbv; tauto]));
    first [ reflexivity | apply Hs; intros HH; apply Hr; revert HH; (first [solve [clear; cbv; tauto] | cbv; tauto]) ].

  Lemma HASHB_U : forall (base i : Z) R M (b : byte),
    getr R 13%bv = Z_to_bv 64 base -> getr R 12%bv = Z_to_bv 64 (2 ^ 64 - 1 - base) -> getr R 14%bv = Z_to_bv 64 i ->
    0 <= base -> 0 <= i -> base + i + 1 < 2 ^ 64 ->
    rdn SEGS M (Z_to_bv 64 (base + i)) 1 = Some [b] ->
    exists R1,
      msteps SEGS (@mkst fx R (Z_to_bv 64 0x6ddd4) M (seg_rom SEGS)) (@mkst fx R1 (Z_to_bv 64 0x6ddfc) M (seg_rom SEGS))
      /\ getr R1 14%bv = Z_to_bv 64 (i + 1) /\ getr R1 11%bv = getr R 11%bv
      /\ getr R1 13%bv = Z_to_bv 64 base /\ getr R1 12%bv = Z_to_bv 64 (2 ^ 64 - 1 - base)
      /\ (forall r, ~ In r [5; 10; 14; 16; 17]%bv -> getr R1 r = getr R r).
  Proof using fx.
    intros base i R M b H13 H12 H14 Hb0 Hi0 Hbi HB.
    eexists. split.
    - norm_pc.
      stepb_ft F_6dd94 D_6dd94 ltac:(rewrite H12, H14; rewrite c_ltu_Z by lia; apply Z.ltb_ge; lia).
      stepiv F_6dd98 D_6dd98 (Z_to_bv 64 (base + i)) ltac:(gres; pin; rewrite v_add_Z by lia; reflexivity).
      sn F_6dd9c D_6dd9c.
      lb_step F_6dda0 D_6dda0 b ltac:(rdn_fix HB).
      sn F_6dda4 D_6dda4.
      sn F_6dda8 D_6dda8.
      sn F_6ddac D_6ddac.
      sn F_6ddb0 D_6ddb0.
      stepiv F_6ddb4 D_6ddb4 (Z_to_bv 64 (i + 1)) ltac:(gres; pin; imm_norm; rewrite v_addi_Z by lia; reflexivity).
      sn F_6ddb8 D_6ddb8.
      close_pc.
    - gres. repeat split; try reflexivity; try assumption. other_regs I.
  Qed.

  Lemma HASH_U : forall (k : nat) (base i n : Z) R M,
    i + Z.of_nat (S k) = n -> 0 <= base -> 0 <= i -> base + n < 2 ^ 64 ->
    getr R 13%bv = Z_to_bv 64 base -> getr R 12%bv = Z_to_bv 64 (2 ^ 64 - 1 - base) -> getr R 14%bv = Z_to_bv 64 i ->
    getr R 11%bv = Z_to_bv 64 n ->
    (forall a, base + i <= a < base + n -> exists b, rdn SEGS M (Z_to_bv 64 a) 1 = Some [b]) ->
    exists R',
      msteps SEGS (@mkst fx R (Z_to_bv 64 0x6ddd4) M (seg_rom SEGS)) (@mkst fx R' (Z_to_bv 64 0x6de00) M (seg_rom SEGS))
      /\ (forall r, ~ In r [5; 10; 14; 16; 17]%bv -> getr R' r = getr R r).
  Proof using fx.
    induction k as [|k IH]; intros base i n R M Hk Hb0 Hi0 Hn H13 H12 H14 H11 HB.
    - destruct (HB (base + i) ltac:(lia)) as [b Hb].
      destruct (HASHB_U base i R M b H13 H12 H14 Hb0 Hi0 ltac:(lia) Hb) as (R1 & RUN & G14 & G11 & G13 & G12 & GS).
      exists R1. split.
      + eapply msteps_trans; [exact RUN|]. norm_pc.
        stepb_ft F_6ddbc D_6ddbc ltac:(rewrite G14, G11, H11; replace (i + 1) with n by lia; apply c_eq_refl).
        close_pc.
      + exact GS.
    - destruct (HB (base + i) ltac:(lia)) as [b Hb].
      destruct (HASHB_U base i R M b H13 H12 H14 Hb0 Hi0 ltac:(lia) Hb) as (R1 & RUN & G14 & G11 & G13 & G12 & GS).
      destruct (IH base (i + 1) n R1 M ltac:(lia) Hb0 ltac:(lia) Hn G13 G12 G14 ltac:(rewrite G11; exact H11) ltac:(intros a Ha; apply HB; lia))
        as (R' & RUN' & GS').
      exists R'. split.
      + eapply msteps_trans; [exact RUN|]. eapply msteps_trans; [|exact RUN']. norm_pc.
        stepb_tk F_6ddbc D_6ddbc ltac:(rewrite G14, G11, H11; rewrite c_eq_Z' by lia; apply Z.eqb_neq; lia).
        close_pc.
      + intros r Hr. rewrite (GS' r Hr). apply GS; assumption.
  Qed.
  Lemma max0_trick : forall z, - 2 ^ 62 <= z < 2 ^ 63 ->
    v_and (v_sub (Z_to_bv 64 0) (v_slt (Z_to_bv 64 0) (Z_to_bv 64 z))) (Z_to_bv 64 z) = Z_to_bv 64 (Z.max z 0).
  Proof using.
    intros z Hz. unfold v_slt. rewrite c_lts_ZZ by lia. destruct (Z.ltb_spec 0 z).
    - unfold v_sub. rewrite !u64_of_Z by lia. rewrite (Z_to_bv_mod64 (0 - 1)). change ((0 - 1) mod 2 ^ 64) with (2 ^ 64 - 1).
      unfold v_and. rewrite !u64_of_Z by lia. f_equal. rewrite Z.land_comm. change (2 ^ 64 - 1) with (Z.ones 64).
      rewrite Z.land_ones by lia. rewrite Z.mod_small by lia. lia.
    - unfold v_sub. rewrite !u64_of_Z by lia. change (0 - 0) with 0. unfold v_and. rewrite u64_of_Z by lia.
      rewrite Z.land_0_l. f_equal. lia.
  Qed.

  Lemma CSEED_U : forall R M1 (data size ret : Z) bs,
    ro_clear Ly.L M1 -> 0 < data -> data + size <= 2 ^ 63 -> 1 <= size ->
    rdn SEGS M1 (Z_to_bv 64 data) (Z.to_nat (Z.min size 37)) = Some bs ->
    ret_ok (Z_to_bv 64 ret) -> getr R 1%bv = Z_to_bv 64 ret ->
    getr R 10%bv = Z_to_bv 64 data -> getr R 11%bv = Z_to_bv 64 size ->
    exists R',
      msteps SEGS (@mkst fx R (Z_to_bv 64 0x6dd48) M1 (seg_rom SEGS))
                  (@mkst fx R' (Z_to_bv 64 ret) M1 (seg_rom SEGS))
      /\ (forall r, ~ In r [5; 10; 11; 12; 13; 14; 15; 16; 17]%bv -> getr R' r = getr R r).
  Proof using fx AC.
    intros R M1 data size ret bs ROC Hd0 Hd1 Hsz RD Hret Hra Ha0 Ha1. pose proof ac_bounds_lit as Hcv.
    set (m := Z.max (size - 4) 0). set (lo := Z.min m 5). set (hi := Z.min size (lo + 32)).
    assert (Hc : 0 <= lo <= 5 /\ lo < hi /\ hi <= Z.min size 37 /\ lo < size /\ hi <= size /\ hi - lo <= 32) by (unfold m, lo, hi; lia).
    assert (RO2 : forall K v, rdn SEGS (fun _ => None) (Z_to_bv 64 K) 8 = Some v -> 0x10000 <= K -> K + 8 <= 0xe8000 ->
                  rdn SEGS M1 (Z_to_bv 64 K) 8 = Some v).
    { intros K v HK H1 H2. rewrite u1_ro_rdn; [exact HK | exact ROC | lia | cbn; lia]. }

    assert (S1 : exists R1, msteps SEGS (@mkst fx R (Z_to_bv 64 0x6dd48) M1 (seg_rom SEGS)) (@mkst fx R1 (Z_to_bv 64 0x6dd60) M1 (seg_rom SEGS))
       /\ getr R1 12%bv = Z_to_bv 64 m /\ getr R1 10%bv = Z_to_bv 64 data /\ getr R1 11%bv = Z_to_bv 64 size
       /\ (forall r, ~ In r [12; 13]%bv -> getr R1 r = getr R r)).
    { eexists. split.
      - norm_pc.
        stepb_ft F_6dd08 D_6dd08 ltac:(rewrite Ha0; rewrite c_eq_Z' by lia; apply Z.eqb_neq; lia).
        stepiv F_6dd0c D_6dd0c (Z_to_bv 64 (size - 4)) ltac:(gres; pin; imm_norm; rewrite v_addi_Z by lia; f_equal; lia).
        stepb_ft F_6dd10 D_6dd10 ltac:(rewrite Ha1; rewrite c_lts_ZZ by lia; apply Z.ltb_lt; lia).
        sn F_6dd14 D_6dd14.
        sn F_6dd18 D_6dd18.
        sn F_6dd1c D_6dd1c.
        close_pc.
      - gres. repeat split; try assumption.
        + unfold m. rewrite <- max0_trick by lia. reflexivity.
        + other_regs I. }
    destruct S1 as (R1 & RUN1 & R1_12 & R1_10 & R1_11 & R1S).

    assert (S2 : exists R2, msteps SEGS (@mkst fx R1 (Z_to_bv 64 0x6dd60) M1 (seg_rom SEGS)) (@mkst fx R2 (Z_to_bv 64 0x6dd6c) M1 (seg_rom SEGS))
       /\ getr R2 12%bv = Z_to_bv 64 lo /\ getr R2 10%bv = Z_to_bv 64 data /\ getr R2 11%bv = Z_to_bv 64 size
       /\ (forall r, ~ In r [12; 13]%bv -> getr R2 r = getr R1 r)).
    { destruct (Z.lt_ge_cases m 5) as [Hlt|Hge].
      - eexists. split.
        + norm_pc. sv F_6dd20 D_6dd20 (Z_to_bv 64 5).
          stepb_tk F_6dd24 D_6dd24 ltac:(rewrite R1_12; rewrite c_lts_ZZ by (unfold m; lia); apply Z.ltb_lt; lia).
          close_pc.
        + gres. replace lo with m by (unfold lo; lia). repeat split; try assumption. other_regs I.
      - eexists. split.
        + norm_pc. sv F_6dd20 D_6dd20 (Z_to_bv 64 5).
          stepb_ft F_6dd24 D_6dd24 ltac:(rewrite R1_12; rewrite c_lts_ZZ by (unfold m; lia); apply Z.ltb_ge; lia).
          sv F_6dd28 D_6dd28 (Z_to_bv 64 5).
          close_pc.
        + gres. replace lo with 5 by (unfold lo; lia). repeat split; try assumption. other_regs I. }
    destruct S2 as (R2 & RUN2 & R2_12 & R2_10 & R2_11 & R2S).

    assert (S3 : exists R3, msteps SEGS (@mkst fx R2 (Z_to_bv 64 0x6dd6c) M1 (seg_rom SEGS)) (@mkst fx R3 (Z_to_bv 64 0x6dd84) M1 (seg_rom SEGS))
       /\ getr R3 12%bv = Z_to_bv 64 lo /\ getr R3 13%bv = Z_to_bv 64 hi
       /\ getr R3 10%bv = Z_to_bv 64 data /\ getr R3 11%bv = Z_to_bv 64 size
       /\ (forall r, ~ In r [13; 14]%bv -> getr R3 r = getr R2 r)).
    { destruct (Z.lt_ge_cases size (lo + 32)) as [Hlt|Hge].
      - eexists. split.
        + norm_pc.
          stepiv F_6dd2c D_6dd2c (Z_to_bv 64 (2 ^ 64 - 1 - data)) ltac:(gres; pin; imm_norm; apply v_not_Z; lia).
          stepb_ft F_6dd30 D_6dd30 ltac:(rewrite R2_12; rewrite c_ltu_Z by lia; apply Z.ltb_ge; lia).
          stepiv F_6dd34 D_6dd34 (Z_to_bv 64 (lo + 32)) ltac:(gres; pin; imm_norm; rewrite v_addi_Z by lia; reflexivity).
          sv F_6dd38 D_6dd38 (Z_to_bv 64 size).
          stepb_tk F_6dd3c D_6dd3c ltac:(rewrite R2_11; rewrite c_lts_ZZ by lia; apply Z.ltb_lt; lia).
          close_pc.
        + gres. replace hi with size by (unfold hi; lia). repeat split; try assumption. other_regs I.
      - eexists. split.
        + norm_pc.
          stepiv F_6dd2c D_6dd2c (Z_to_bv 64 (2 ^ 64 - 1 - data)) ltac:(gres; pin; imm_norm; apply v_not_Z; lia).
          stepb_ft F_6dd30 D_6dd30 ltac:(rewrite R2_12; rewrite c_ltu_Z by lia; apply Z.ltb_ge; lia).
          stepiv F_6dd34 D_6dd34 (Z_to_bv 64 (lo + 32)) ltac:(gres; pin; imm_norm; rewrite v_addi_Z by lia; reflexivity).
          sv F_6dd38 D_6dd38 (Z_to_bv 64 size).
          stepb_ft F_6dd3c D_6dd3c ltac:(rewrite R2_11; rewrite c_lts_ZZ by lia; apply Z.ltb_ge; lia).
          sv F_6dd40 D_6dd40 (Z_to_bv 64 (lo + 32)).
          close_pc.
        + gres. replace hi with (lo + 32) by (unfold hi; lia). repeat split; try assumption. other_regs I. }
    destruct S3 as (R3 & RUN3 & R3_12 & R3_13 & R3_10 & R3_11 & R3S).

    assert (S4 : exists R4, msteps SEGS (@mkst fx R3 (Z_to_bv 64 0x6dd84) M1 (seg_rom SEGS)) (@mkst fx R4 (Z_to_bv 64 0x6ddbc) M1 (seg_rom SEGS))
       /\ getr R4 12%bv = Z_to_bv 64 lo /\ getr R4 13%bv = Z_to_bv 64 (data + lo) /\ getr R4 11%bv = Z_to_bv 64 hi
       /\ (forall r, ~ In r [11; 13; 14; 16; 17]%bv -> getr R4 r = getr R3 r)).
    { destruct (Z.lt_ge_cases size (lo + 32)) as [Hlt|Hge].
      - eexists. split.
        + norm_pc.
          stepb_tk F_6dd44 D_6dd44 ltac:(rewrite R3_11, R3_12; rewrite c_eq_Z' by lia; apply Z.eqb_neq; lia).
          sv F_6dd54 D_6dd54 (Z_to_bv 64 0x14d94).
          ld_step F_6dd58 D_6dd58 (word_to_le_bytes 8 (Z_to_bv 64 8298762835598203578)) (Z_to_bv 64 8298762835598203578)
            ltac:(apply (RO2 K1a); [exact u1_img_K1 | unfold K1a; lia | unfold K1a; lia]) ltac:(b2z8).
          stepiv F_6dd5c D_6dd5c (Z_to_bv 64 (hi - lo)) ltac:(gres; pin; rewrite v_sub_Z by lia; reflexivity).
          sv F_6dd60 D_6dd60 (Z_to_bv 64 0x14da0).
          ld_step F_6dd64 D_6dd64 (word_to_le_bytes 8 (Z_to_bv 64 14594272307789293969)) (Z_to_bv 64 14594272307789293969)
            ltac:(apply (RO2 K2a); [exact u1_img_K2 | unfold K2a; lia | unfold K2a; lia]) ltac:(b2z8).
          sn F_6dd68 D_6dd68.
          stepiv F_6dd6c D_6dd6c (Z_to_bv 64 (lo + 32)) ltac:(gres; pin; imm_norm; rewrite v_addi_Z by lia; reflexivity).
          stepiv F_6dd70 D_6dd70 (Z_to_bv 64 (data + lo)) ltac:(gres; pin; rewrite v_add_Z by lia; reflexivity).
          stepb_tk F_6dd74 D_6dd74 ltac:(rewrite R3_11; rewrite c_lts_ZZ by lia; apply Z.ltb_lt; lia).
          close_pc.
        + gres. replace hi with size by (unfold hi; lia). repeat split; try assumption. other_regs I.
      - eexists. split.
        + norm_pc.
          stepb_tk F_6dd44 D_6dd44 ltac:(rewrite R3_11, R3_12; rewrite c_eq_Z' by lia; apply Z.eqb_neq; lia).
          sv F_6dd54 D_6dd54 (Z_to_bv 64 0x14d94).
          ld_step F_6dd58 D_6dd58 (word_to_le_bytes 8 (Z_to_bv 64 8298762835598203578)) (Z_to_bv 64 8298762835598203578)
            ltac:(apply (RO2 K1a); [exact u1_img_K1 | unfold K1a; lia | unfold K1a; lia]) ltac:(b2z8).
          stepiv F_6dd5c D_6dd5c (Z_to_bv 64 (hi - lo)) ltac:(gres; pin; rewrite v_sub_Z by lia; reflexivity).
          sv F_6dd60 D_6dd60 (Z_to_bv 64 0x14da0).
          ld_step F_6dd64 D_6dd64 (word_to_le_bytes 8 (Z_to_bv 64 14594272307789293969)) (Z_to_bv 64 14594272307789293969)
            ltac:(apply (RO2 K2a); [exact u1_img_K2 | unfold K2a; lia | unfold K2a; lia]) ltac:(b2z8).
          sn F_6dd68 D_6dd68.
          stepiv F_6dd6c D_6dd6c (Z_to_bv 64 (lo + 32)) ltac:(gres; pin; imm_norm; rewrite v_addi_Z by lia; reflexivity).
          stepiv F_6dd70 D_6dd70 (Z_to_bv 64 (data + lo)) ltac:(gres; pin; rewrite v_add_Z by lia; reflexivity).
          stepb_ft F_6dd74 D_6dd74 ltac:(rewrite R3_11; rewrite c_lts_ZZ by lia; apply Z.ltb_ge; lia).
          sv F_6dd78 D_6dd78 (Z_to_bv 64 (lo + 32)).
          close_pc.
        + gres. repeat split; try assumption; try reflexivity; try (f_equal; unfold hi; lia). other_regs I. }
    destruct S4 as (R4 & RUN4 & R4_12 & R4_13 & R4_11 & R4S).

    assert (S5 : exists R5, msteps SEGS (@mkst fx R4 (Z_to_bv 64 0x6ddbc) M1 (seg_rom SEGS)) (@mkst fx R5 (Z_to_bv 64 0x6ddd4) M1 (seg_rom SEGS))
       /\ getr R5 13%bv = Z_to_bv 64 (data + lo) /\ getr R5 12%bv = Z_to_bv 64 (2 ^ 64 - 1 - (data + lo))
       /\ getr R5 14%bv = Z_to_bv 64 0 /\ getr R5 11%bv = Z_to_bv 64 (hi - lo)
       /\ (forall r, ~ In r [10; 11; 12; 14; 15]%bv -> getr R5 r = getr R4 r)).
    { eexists. split.
      - norm_pc.
        sv F_6dd7c D_6dd7c (Z_to_bv 64 0).
        sv F_6dd80 D_6dd80 (Z_to_bv 64 0x14dc0).
        ld_step F_6dd84 D_6dd84 (word_to_le_bytes 8 (Z_to_bv 64 11400714819323198486)) (Z_to_bv 64 11400714819323198486)
          ltac:(apply (RO2 K3a); [exact u1_img_K3 | unfold K3a; lia | unfold K3a; lia]) ltac:(b2z8).
        sn F_6dd88 D_6dd88.
        stepiv F_6dd8c D_6dd8c (Z_to_bv 64 (hi - lo)) ltac:(gres; pin; rewrite v_sub_Z by lia; reflexivity).
        stepiv F_6dd90 D_6dd90 (Z_to_bv 64 (2 ^ 64 - 1 - (data + lo))) ltac:(gres; pin; imm_norm; apply v_not_Z; lia).
        close_pc.
      - gres. repeat split; try assumption; try reflexivity. other_regs I. }
    destruct S5 as (R5 & RUN5 & R5_13 & R5_12 & R5_14 & R5_11 & R5S).

    destruct (HASH_U (Z.to_nat (hi - lo - 1)) (data + lo) 0 (hi - lo) R5 M1 ltac:(rewrite Nat2Z.inj_succ, Z2Nat.id by lia; lia) ltac:(lia) ltac:(lia) ltac:(lia)
                R5_13 R5_12 R5_14 R5_11) as (R6 & RUN6 & R6S).
    { intros a Ha.
      exists (nth (Z.to_nat (a - data)) bs (Z_to_bv 8 0)).
      pose proof (rdn_sub SEGS M1 _ (Z_to_bv 64 data) bs (Z.to_nat (a - data)) 1 RD ltac:(lia)) as HS.
      unfold at_ in HS. rewrite u64_of_Z in HS by lia. replace (data + Z.of_nat (Z.to_nat (a - data))) with a in HS by lia.
      rewrite HS. f_equal. unfold sub.
      pose proof (rdn_length _ _ _ _ _ RD) as HL.
      rewrite (skipn_nth bs (Z.to_nat (a - data)) (Z_to_bv 8 0)) by lia. reflexivity. }

    assert (R6_1 : getr R6 1%bv = Z_to_bv 64 ret).
    { rewrite R6S by (first [solve [clear; cbv; intuition discriminate] | cbv; intuition discriminate]). rewrite R5S, R4S, R3S, R2S, R1S by (first [solve [clear; cbv; intuition discriminate] | cbv; intuition discriminate]). exact Hra. }
    eexists. split.
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|].
      eapply msteps_trans; [exact RUN4|]. eapply msteps_trans; [exact RUN5|]. eapply msteps_trans; [exact RUN6|]. norm_pc.
      stepjr F_6ddc0 D_6ddc0 (Z_to_bv 64 ret) ltac:(gres; exact R6_1).
      lazymatch goal with |- msteps _ (mkst ?r ?pc _ _) (mkst ?r' _ _ _) => unify r' r;
        replace pc with (Z_to_bv 64 ret) by (symmetry; imm_norm; exact Hret) end. apply mst_refl.
    - intros r Hr.
      rewrite R6S by (intros HH; apply Hr; revert HH; (first [solve [clear; cbv; tauto] | cbv; tauto])).
      rewrite R5S, R4S, R3S, R2S, R1S; [reflexivity | | | | |]; intros HH; apply Hr; revert HH; (first [solve [clear; cbv; tauto] | cbv; tauto]).
  Qed.
  Definition uRG : rg_consts := {| rc_ctor := 0x6dcf4; rc_gettargetenv := 0x6de30; rc_ctor_stack := 0; rc_gte_stack := 144 |}.
End RGU.

Theorem rg_ctor_6dc50_spec {AC : AllocCeiling} : rg_ctor_stmt SEGS Ly.L uRG.
Proof.
  intros fx M R sp ret obj data size bs. cbn [rc_ctor rc_ctor_stack uRG]. lazy zeta.
  intros ROC Ho0 Ho1 HDo Hd0 Hd1 Hsz RD DJ1 DJ2 HROOM Hspc Hsp47 Hoc Hret Hra Hsp Ha0 Ha1 Ha2.
  pose proof ac_bounds_lit as Hcv. unfold RG_SZ in *.
  destruct (CTOR_AU R M sp ret obj data size ROC Ho0 ltac:(unfold RG_SZ; lia) ltac:(unfold RG_SZ; exact HDo) Hoc Ha0 Ha1 Ha2)
    as (R1 & M1 & RUN1 & R1_10 & R1_11 & R1S & SI1 & FJ1 & FI1). unfold RG_SZ in SI1.
  assert (ROC1 : ro_clear Ly.L M1) by (eapply u1_ro_clear_stores; [exact ROC | exact SI1 | intros a Ha; unfold zwin in Ha; lia]).
  assert (RD1 : rdn SEGS M1 (Z_to_bv 64 data) (Z.to_nat (Z.min size 37)) = Some bs).
  { rewrite <- RD. apply rdn_agree_win; [lia | lia |]. eapply stores_in_agree; [exact SI1|].
    intros a Ha. unfold zwin in Ha. split; [lia|]. intros Hz. apply (DJ2 a); unfold zwin in *; lia. }
  destruct (CSEED_U R1 M1 data size ret bs ROC1 Hd0 Hd1 Hsz RD1 Hret
              ltac:(rewrite R1S by (first [solve [clear; cbv; intuition discriminate] | cbv; intuition discriminate]); exact Hra) R1_10 R1_11)
    as (R' & RUN2 & R'S).
  assert (SI : stores_in (fun a => zwin obj (obj + 2504) a \/ zwin (sp - 0) sp a) M M1).
  { eapply stores_in_weaken; [exact SI1|]. intros a Ha; left; exact Ha. }
  exists R', M1. split; [|split; [|split; [|split; [|split]]]].
  - eapply msteps_trans; [exact RUN1 | exact RUN2].
  - intros r Hr. unfold callee_saved in Hr.
    rewrite R'S by (first [ solve [clear - Hr H1 H2; cbv; intros HH; decompose [or] HH; try subst r; try contradiction; cbv in Hr; intuition discriminate] | cbv; intros HH; decompose [or] HH; try subst r; try contradiction; cbv in Hr; intuition discriminate ]).
    apply R1S. first [ solve [clear - Hr H1 H2; cbv; intros HH; decompose [or] HH; try subst r; cbv in Hr; intuition discriminate] | cbv; intros HH; decompose [or] HH; try subst r; cbv in Hr; intuition discriminate ].
  -
    split; [eapply stores_in_mdef; [exact SI | unfold RG_SZ; exact HDo] |]. split.
    + intros i Hi. unfold MT_N in Hi. apply FJ1. lia.
    + unfold MT_N. exact FI1.
  - eapply stores_in_frame_eq; [exact SI|]. intros a [Ha|Ha]; [left; unfold RG_SZ; exact Ha | right; exact Ha].
  - exact (proj2 SI).
  - exact ROC1.
Qed.
