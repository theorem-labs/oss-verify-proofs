(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Ubsan.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StepTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.WalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StartupTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SumWalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MemSplit OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ShapeAlg OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SRealizes OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefReadLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibEff OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MmapSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibMaskBits OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.U1Layout.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.CRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.StrLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.Lib_RG OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.Lib_RG2 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.U1Facts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.U1Lib_RG.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Module U1_code_6ddf0_6e138.

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Ubsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_6ddf0 : bv 32 := 0xfd010113.
Lemma F_6ddf0 : fetch_word Ubsan.M.loaded_segments (0x6de30 : word) = Some W_6ddf0.
Proof. vm_refl. Qed.
Lemma D_6ddf0 : decode_any W_6ddf0 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ddf4 : bv 32 := 0x02113423.
Lemma F_6ddf4 : fetch_word Ubsan.M.loaded_segments (0x6de34 : word) = Some W_6ddf4.
Proof. vm_refl. Qed.
Lemma D_6ddf4 : decode_any W_6ddf4 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ddf8 : bv 32 := 0x02813023.
Lemma F_6ddf8 : fetch_word Ubsan.M.loaded_segments (0x6de38 : word) = Some W_6ddf8.
Proof. vm_refl. Qed.
Lemma D_6ddf8 : decode_any W_6ddf8 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ddfc : bv 32 := 0x00913c23.
Lemma F_6ddfc : fetch_word Ubsan.M.loaded_segments (0x6de3c : word) = Some W_6ddfc.
Proof. vm_refl. Qed.
Lemma D_6ddfc : decode_any W_6ddfc = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_6de00 : bv 32 := 0x01213823.
Lemma F_6de00 : fetch_word Ubsan.M.loaded_segments (0x6de40 : word) = Some W_6de00.
Proof. vm_refl. Qed.
Lemma D_6de00 : decode_any W_6de00 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6de04 : bv 32 := 0x01313423.
Lemma F_6de04 : fetch_word Ubsan.M.loaded_segments (0x6de44 : word) = Some W_6de04.
Proof. vm_refl. Qed.
Lemma D_6de04 : decode_any W_6de04 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6de08 : bv 32 := 0x00050413.
Lemma F_6de08 : fetch_word Ubsan.M.loaded_segments (0x6de48 : word) = Some W_6de08.
Proof. vm_refl. Qed.
Lemma D_6de08 : decode_any W_6de08 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6de0c : bv 32 := 0x01a00913.
Lemma F_6de0c : fetch_word Ubsan.M.loaded_segments (0x6de4c : word) = Some W_6de0c.
Proof. vm_refl. Qed.
Lemma D_6de0c : decode_any W_6de0c = Some (OpImm ALU_ADD 18 0 26, 4%Z).
Proof. vm_refl. Qed.

Definition W_6de10 : bv 32 := 0x02000993.
Lemma F_6de10 : fetch_word Ubsan.M.loaded_segments (0x6de50 : word) = Some W_6de10.
Proof. vm_refl. Qed.
Lemma D_6de10 : decode_any W_6de10 = Some (OpImm ALU_ADD 19 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_6de14 : bv 32 := 0x00012023.
Lemma F_6de14 : fetch_word Ubsan.M.loaded_segments (0x6de54 : word) = Some W_6de14.
Proof. vm_refl. Qed.
Lemma D_6de14 : decode_any W_6de14 = Some (Store SZ4 2 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6de18 : bv 32 := 0x01212223.
Lemma F_6de18 : fetch_word Ubsan.M.loaded_segments (0x6de58 : word) = Some W_6de18.
Proof. vm_refl. Qed.
Lemma D_6de18 : decode_any W_6de18 = Some (Store SZ4 2 18 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_6de1c : bv 32 := 0x00010513.
Lemma F_6de1c : fetch_word Ubsan.M.loaded_segments (0x6de5c : word) = Some W_6de1c.
Proof. vm_refl. Qed.
Lemma D_6de1c : decode_any W_6de1c = Some (OpImm ALU_ADD 10 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6de20 : bv 32 := 0x00010613.
Lemma F_6de20 : fetch_word Ubsan.M.loaded_segments (0x6de60 : word) = Some W_6de20.
Proof. vm_refl. Qed.
Lemma D_6de20 : decode_any W_6de20 = Some (OpImm ALU_ADD 12 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6de24 : bv 32 := 0x00040593.
Lemma F_6de24 : fetch_word Ubsan.M.loaded_segments (0x6de64 : word) = Some W_6de24.
Proof. vm_refl. Qed.
Lemma D_6de24 : decode_any W_6de24 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6de28 : bv 32 := 0x038000ef.
Lemma F_6de28 : fetch_word Ubsan.M.loaded_segments (0x6de68 : word) = Some W_6de28.
Proof. vm_refl. Qed.
Lemma D_6de28 : decode_any W_6de28 = Some (Jal 1 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_6de2c : bv 32 := 0x03357863.
Lemma F_6de2c : fetch_word Ubsan.M.loaded_segments (0x6de6c : word) = Some W_6de2c.
Proof. vm_refl. Qed.
Lemma D_6de2c : decode_any W_6de2c = Some (Branch BC_GEU 10 19 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_6de30 : bv 32 := 0x00050493.
Lemma F_6de30 : fetch_word Ubsan.M.loaded_segments (0x6de70 : word) = Some W_6de30.
Proof. vm_refl. Qed.
Lemma D_6de30 : decode_any W_6de30 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6de34 : bv 32 := 0xa64ff0ef.
Lemma F_6de34 : fetch_word Ubsan.M.loaded_segments (0x6de74 : word) = Some W_6de34.
Proof. vm_refl. Qed.
Lemma D_6de34 : decode_any W_6de34 = Some (Jal 1 2093668, 4%Z).
Proof. vm_refl. Qed.

Definition W_6de38 : bv 32 := 0xfc050ee3.
Lemma F_6de38 : fetch_word Ubsan.M.loaded_segments (0x6de78 : word) = Some W_6de38.
Proof. vm_refl. Qed.
Lemma D_6de38 : decode_any W_6de38 = Some (Branch BC_EQ 10 0 8156, 4%Z).
Proof. vm_refl. Qed.

Definition W_6de3c : bv 32 := 0x00048513.
Lemma F_6de3c : fetch_word Ubsan.M.loaded_segments (0x6de7c : word) = Some W_6de3c.
Proof. vm_refl. Qed.
Lemma D_6de3c : decode_any W_6de3c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6de40 : bv 32 := 0x02813083.
Lemma F_6de40 : fetch_word Ubsan.M.loaded_segments (0x6de80 : word) = Some W_6de40.
Proof. vm_refl. Qed.
Lemma D_6de40 : decode_any W_6de40 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_6de44 : bv 32 := 0x02013403.
Lemma F_6de44 : fetch_word Ubsan.M.loaded_segments (0x6de84 : word) = Some W_6de44.
Proof. vm_refl. Qed.
Lemma D_6de44 : decode_any W_6de44 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_6de48 : bv 32 := 0x01813483.
Lemma F_6de48 : fetch_word Ubsan.M.loaded_segments (0x6de88 : word) = Some W_6de48.
Proof. vm_refl. Qed.
Lemma D_6de48 : decode_any W_6de48 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_6de4c : bv 32 := 0x01013903.
Lemma F_6de4c : fetch_word Ubsan.M.loaded_segments (0x6de8c : word) = Some W_6de4c.
Proof. vm_refl. Qed.
Lemma D_6de4c : decode_any W_6de4c = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6de50 : bv 32 := 0x00813983.
Lemma F_6de50 : fetch_word Ubsan.M.loaded_segments (0x6de90 : word) = Some W_6de50.
Proof. vm_refl. Qed.
Lemma D_6de50 : decode_any W_6de50 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6de54 : bv 32 := 0x03010113.
Lemma F_6de54 : fetch_word Ubsan.M.loaded_segments (0x6de94 : word) = Some W_6de54.
Proof. vm_refl. Qed.
Lemma D_6de54 : decode_any W_6de54 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_6de58 : bv 32 := 0x00008067.
Lemma F_6de58 : fetch_word Ubsan.M.loaded_segments (0x6de98 : word) = Some W_6de58.
Proof. vm_refl. Qed.
Lemma D_6de58 : decode_any W_6de58 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6de60 : bv 32 := 0xfa010113.
Lemma F_6de60 : fetch_word Ubsan.M.loaded_segments (0x6dea0 : word) = Some W_6de60.
Proof. vm_refl. Qed.
Lemma D_6de60 : decode_any W_6de60 = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_6de64 : bv 32 := 0x04113c23.
Lemma F_6de64 : fetch_word Ubsan.M.loaded_segments (0x6dea4 : word) = Some W_6de64.
Proof. vm_refl. Qed.
Lemma D_6de64 : decode_any W_6de64 = Some (Store SZ8 2 1 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_6de68 : bv 32 := 0x04813823.
Lemma F_6de68 : fetch_word Ubsan.M.loaded_segments (0x6dea8 : word) = Some W_6de68.
Proof. vm_refl. Qed.
Lemma D_6de68 : decode_any W_6de68 = Some (Store SZ8 2 8 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_6de6c : bv 32 := 0x04913423.
Lemma F_6de6c : fetch_word Ubsan.M.loaded_segments (0x6deac : word) = Some W_6de6c.
Proof. vm_refl. Qed.
Lemma D_6de6c : decode_any W_6de6c = Some (Store SZ8 2 9 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_6de70 : bv 32 := 0x00060413.
Lemma F_6de70 : fetch_word Ubsan.M.loaded_segments (0x6deb0 : word) = Some W_6de70.
Proof. vm_refl. Qed.
Lemma D_6de70 : decode_any W_6de70 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6de74 : bv 32 := 0x00062603.
Lemma F_6de74 : fetch_word Ubsan.M.loaded_segments (0x6deb4 : word) = Some W_6de74.
Proof. vm_refl. Qed.
Lemma D_6de74 : decode_any W_6de74 = Some (Load SZ4 true 12 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6de78 : bv 32 := 0x00442503.
Lemma F_6de78 : fetch_word Ubsan.M.loaded_segments (0x6deb8 : word) = Some W_6de78.
Proof. vm_refl. Qed.
Lemma D_6de78 : decode_any W_6de78 = Some (Load SZ4 true 10 8 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_6de7c : bv 32 := 0x0ec50863.
Lemma F_6de7c : fetch_word Ubsan.M.loaded_segments (0x6debc : word) = Some W_6de7c.
Proof. vm_refl. Qed.
Lemma D_6de7c : decode_any W_6de7c = Some (Branch BC_EQ 10 12 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_6de80 : bv 32 := 0x40c5053b.
Lemma F_6de80 : fetch_word Ubsan.M.loaded_segments (0x6dec0 : word) = Some W_6de80.
Proof. vm_refl. Qed.
Lemma D_6de80 : decode_any W_6de80 = Some (Op32 ALU_SUB 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6de84 : bv 32 := 0x0015049b.
Lemma F_6de84 : fetch_word Ubsan.M.loaded_segments (0x6dec4 : word) = Some W_6de84.
Proof. vm_refl. Qed.
Lemma D_6de84 : decode_any W_6de84 = Some (OpImm32 9 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6de88 : bv 32 := 0x0c048e63.
Lemma F_6de88 : fetch_word Ubsan.M.loaded_segments (0x6dec8 : word) = Some W_6de88.
Proof. vm_refl. Qed.
Lemma D_6de88 : decode_any W_6de88 = Some (Branch BC_EQ 9 0 220, 4%Z).
Proof. vm_refl. Qed.

Definition W_6de8c : bv 32 := 0x0014d51b.
Lemma F_6de8c : fetch_word Ubsan.M.loaded_segments (0x6decc : word) = Some W_6de8c.
Proof. vm_refl. Qed.
Lemma D_6de8c : decode_any W_6de8c = Some (ShiftImm32 ALU_SRL 10 9 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6de90 : bv 32 := 0x55555637.
Lemma F_6de90 : fetch_word Ubsan.M.loaded_segments (0x6ded0 : word) = Some W_6de90.
Proof. vm_refl. Qed.
Lemma D_6de90 : decode_any W_6de90 = Some (Lui 12 349525, 4%Z).
Proof. vm_refl. Qed.

Definition W_6de94 : bv 32 := 0x00a4e533.
Lemma F_6de94 : fetch_word Ubsan.M.loaded_segments (0x6ded4 : word) = Some W_6de94.
Proof. vm_refl. Qed.
Lemma D_6de94 : decode_any W_6de94 = Some (Op ALU_OR 10 9 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6de98 : bv 32 := 0x5556061b.
Lemma F_6de98 : fetch_word Ubsan.M.loaded_segments (0x6ded8 : word) = Some W_6de98.
Proof. vm_refl. Qed.
Lemma D_6de98 : decode_any W_6de98 = Some (OpImm32 12 12 1365, 4%Z).
Proof. vm_refl. Qed.

Definition W_6de9c : bv 32 := 0x0025569b.
Lemma F_6de9c : fetch_word Ubsan.M.loaded_segments (0x6dedc : word) = Some W_6de9c.
Proof. vm_refl. Qed.
Lemma D_6de9c : decode_any W_6de9c = Some (ShiftImm32 ALU_SRL 13 10 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dea0 : bv 32 := 0x00d56533.
Lemma F_6dea0 : fetch_word Ubsan.M.loaded_segments (0x6dee0 : word) = Some W_6dea0.
Proof. vm_refl. Qed.
Lemma D_6dea0 : decode_any W_6dea0 = Some (Op ALU_OR 10 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dea4 : bv 32 := 0x0045569b.
Lemma F_6dea4 : fetch_word Ubsan.M.loaded_segments (0x6dee4 : word) = Some W_6dea4.
Proof. vm_refl. Qed.
Lemma D_6dea4 : decode_any W_6dea4 = Some (ShiftImm32 ALU_SRL 13 10 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dea8 : bv 32 := 0x00d56533.
Lemma F_6dea8 : fetch_word Ubsan.M.loaded_segments (0x6dee8 : word) = Some W_6dea8.
Proof. vm_refl. Qed.
Lemma D_6dea8 : decode_any W_6dea8 = Some (Op ALU_OR 10 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_6deac : bv 32 := 0x0085569b.
Lemma F_6deac : fetch_word Ubsan.M.loaded_segments (0x6deec : word) = Some W_6deac.
Proof. vm_refl. Qed.
Lemma D_6deac : decode_any W_6deac = Some (ShiftImm32 ALU_SRL 13 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6deb0 : bv 32 := 0x00d56533.
Lemma F_6deb0 : fetch_word Ubsan.M.loaded_segments (0x6def0 : word) = Some W_6deb0.
Proof. vm_refl. Qed.
Lemma D_6deb0 : decode_any W_6deb0 = Some (Op ALU_OR 10 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_6deb4 : bv 32 := 0x0105569b.
Lemma F_6deb4 : fetch_word Ubsan.M.loaded_segments (0x6def4 : word) = Some W_6deb4.
Proof. vm_refl. Qed.
Lemma D_6deb4 : decode_any W_6deb4 = Some (ShiftImm32 ALU_SRL 13 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6deb8 : bv 32 := 0x00d56533.
Lemma F_6deb8 : fetch_word Ubsan.M.loaded_segments (0x6def8 : word) = Some W_6deb8.
Proof. vm_refl. Qed.
Lemma D_6deb8 : decode_any W_6deb8 = Some (Op ALU_OR 10 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_6debc : bv 32 := 0xfff54513.
Lemma F_6debc : fetch_word Ubsan.M.loaded_segments (0x6defc : word) = Some W_6debc.
Proof. vm_refl. Qed.
Lemma D_6debc : decode_any W_6debc = Some (OpImm ALU_XOR 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dec0 : bv 32 := 0x00155693.
Lemma F_6dec0 : fetch_word Ubsan.M.loaded_segments (0x6df00 : word) = Some W_6dec0.
Proof. vm_refl. Qed.
Lemma D_6dec0 : decode_any W_6dec0 = Some (ShiftImm ALU_SRL 13 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dec4 : bv 32 := 0x00c6f633.
Lemma F_6dec4 : fetch_word Ubsan.M.loaded_segments (0x6df04 : word) = Some W_6dec4.
Proof. vm_refl. Qed.
Lemma D_6dec4 : decode_any W_6dec4 = Some (Op ALU_AND 12 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dec8 : bv 32 := 0x333336b7.
Lemma F_6dec8 : fetch_word Ubsan.M.loaded_segments (0x6df08 : word) = Some W_6dec8.
Proof. vm_refl. Qed.
Lemma D_6dec8 : decode_any W_6dec8 = Some (Lui 13 209715, 4%Z).
Proof. vm_refl. Qed.

Definition W_6decc : bv 32 := 0x3336869b.
Lemma F_6decc : fetch_word Ubsan.M.loaded_segments (0x6df0c : word) = Some W_6decc.
Proof. vm_refl. Qed.
Lemma D_6decc : decode_any W_6decc = Some (OpImm32 13 13 819, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ded0 : bv 32 := 0x40c50533.
Lemma F_6ded0 : fetch_word Ubsan.M.loaded_segments (0x6df10 : word) = Some W_6ded0.
Proof. vm_refl. Qed.
Lemma D_6ded0 : decode_any W_6ded0 = Some (Op ALU_SUB 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ded4 : bv 32 := 0x00d57633.
Lemma F_6ded4 : fetch_word Ubsan.M.loaded_segments (0x6df14 : word) = Some W_6ded4.
Proof. vm_refl. Qed.
Lemma D_6ded4 : decode_any W_6ded4 = Some (Op ALU_AND 12 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_6ded8 : bv 32 := 0x00255513.
Lemma F_6ded8 : fetch_word Ubsan.M.loaded_segments (0x6df18 : word) = Some W_6ded8.
Proof. vm_refl. Qed.
Lemma D_6ded8 : decode_any W_6ded8 = Some (ShiftImm ALU_SRL 10 10 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dedc : bv 32 := 0x00d57533.
Lemma F_6dedc : fetch_word Ubsan.M.loaded_segments (0x6df1c : word) = Some W_6dedc.
Proof. vm_refl. Qed.
Lemma D_6dedc : decode_any W_6dedc = Some (Op ALU_AND 10 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dee0 : bv 32 := 0x0f0f16b7.
Lemma F_6dee0 : fetch_word Ubsan.M.loaded_segments (0x6df20 : word) = Some W_6dee0.
Proof. vm_refl. Qed.
Lemma D_6dee0 : decode_any W_6dee0 = Some (Lui 13 61681, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dee4 : bv 32 := 0x00a60533.
Lemma F_6dee4 : fetch_word Ubsan.M.loaded_segments (0x6df24 : word) = Some W_6dee4.
Proof. vm_refl. Qed.
Lemma D_6dee4 : decode_any W_6dee4 = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dee8 : bv 32 := 0x00455613.
Lemma F_6dee8 : fetch_word Ubsan.M.loaded_segments (0x6df28 : word) = Some W_6dee8.
Proof. vm_refl. Qed.
Lemma D_6dee8 : decode_any W_6dee8 = Some (ShiftImm ALU_SRL 12 10 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_6deec : bv 32 := 0x00c50533.
Lemma F_6deec : fetch_word Ubsan.M.loaded_segments (0x6df2c : word) = Some W_6deec.
Proof. vm_refl. Qed.
Lemma D_6deec : decode_any W_6deec = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6def0 : bv 32 := 0x01010637.
Lemma F_6def0 : fetch_word Ubsan.M.loaded_segments (0x6df30 : word) = Some W_6def0.
Proof. vm_refl. Qed.
Lemma D_6def0 : decode_any W_6def0 = Some (Lui 12 4112, 4%Z).
Proof. vm_refl. Qed.

Definition W_6def4 : bv 32 := 0xf0f68693.
Lemma F_6def4 : fetch_word Ubsan.M.loaded_segments (0x6df34 : word) = Some W_6def4.
Proof. vm_refl. Qed.
Lemma D_6def4 : decode_any W_6def4 = Some (OpImm ALU_ADD 13 13 3855, 4%Z).
Proof. vm_refl. Qed.

Definition W_6def8 : bv 32 := 0x10160613.
Lemma F_6def8 : fetch_word Ubsan.M.loaded_segments (0x6df38 : word) = Some W_6def8.
Proof. vm_refl. Qed.
Lemma D_6def8 : decode_any W_6def8 = Some (OpImm ALU_ADD 12 12 257, 4%Z).
Proof. vm_refl. Qed.

Definition W_6defc : bv 32 := 0x00d57533.
Lemma F_6defc : fetch_word Ubsan.M.loaded_segments (0x6df3c : word) = Some W_6defc.
Proof. vm_refl. Qed.
Lemma D_6defc : decode_any W_6defc = Some (Op ALU_AND 10 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_6df00 : bv 32 := 0x02c50533.
Lemma F_6df00 : fetch_word Ubsan.M.loaded_segments (0x6df40 : word) = Some W_6df00.
Proof. vm_refl. Qed.
Lemma D_6df00 : decode_any W_6df00 = Some (Mul M_MUL 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6df04 : bv 32 := 0x0185551b.
Lemma F_6df04 : fetch_word Ubsan.M.loaded_segments (0x6df44 : word) = Some W_6df04.
Proof. vm_refl. Qed.
Lemma D_6df04 : decode_any W_6df04 = Some (ShiftImm32 ALU_SRL 10 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_6df08 : bv 32 := 0x01f00613.
Lemma F_6df08 : fetch_word Ubsan.M.loaded_segments (0x6df48 : word) = Some W_6df08.
Proof. vm_refl. Qed.
Lemma D_6df08 : decode_any W_6df08 = Some (OpImm ALU_ADD 12 0 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_6df0c : bv 32 := 0x06c50c63.
Lemma F_6df0c : fetch_word Ubsan.M.loaded_segments (0x6df4c : word) = Some W_6df0c.
Proof. vm_refl. Qed.
Lemma D_6df0c : decode_any W_6df0c = Some (Branch BC_EQ 10 12 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_6df10 : bv 32 := 0x00a4963b.
Lemma F_6df10 : fetch_word Ubsan.M.loaded_segments (0x6df50 : word) = Some W_6df10.
Proof. vm_refl. Qed.
Lemma D_6df10 : decode_any W_6df10 = Some (Op32 ALU_SLL 12 9 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6df14 : bv 32 := 0x02000693.
Lemma F_6df14 : fetch_word Ubsan.M.loaded_segments (0x6df54 : word) = Some W_6df14.
Proof. vm_refl. Qed.
Lemma D_6df14 : decode_any W_6df14 = Some (OpImm ALU_ADD 13 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_6df18 : bv 32 := 0x02161613.
Lemma F_6df18 : fetch_word Ubsan.M.loaded_segments (0x6df58 : word) = Some W_6df18.
Proof. vm_refl. Qed.
Lemma D_6df18 : decode_any W_6df18 = Some (ShiftImm ALU_SLL 12 12 33, 4%Z).
Proof. vm_refl. Qed.

Definition W_6df1c : bv 32 := 0x02165613.
Lemma F_6df1c : fetch_word Ubsan.M.loaded_segments (0x6df5c : word) = Some W_6df1c.
Proof. vm_refl. Qed.
Lemma D_6df1c : decode_any W_6df1c = Some (ShiftImm ALU_SRL 12 12 33, 4%Z).
Proof. vm_refl. Qed.

Definition W_6df20 : bv 32 := 0x00163613.
Lemma F_6df20 : fetch_word Ubsan.M.loaded_segments (0x6df60 : word) = Some W_6df20.
Proof. vm_refl. Qed.
Lemma D_6df20 : decode_any W_6df20 = Some (OpImm ALU_SLTU 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6df24 : bv 32 := 0x40a686b3.
Lemma F_6df24 : fetch_word Ubsan.M.loaded_segments (0x6df64 : word) = Some W_6df24.
Proof. vm_refl. Qed.
Lemma D_6df24 : decode_any W_6df24 = Some (Op ALU_SUB 13 13 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6df28 : bv 32 := 0x40c68633.
Lemma F_6df28 : fetch_word Ubsan.M.loaded_segments (0x6df68 : word) = Some W_6df28.
Proof. vm_refl. Qed.
Lemma D_6df28 : decode_any W_6df28 = Some (Op ALU_SUB 12 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6df2c : bv 32 := 0x00010513.
Lemma F_6df2c : fetch_word Ubsan.M.loaded_segments (0x6df6c : word) = Some W_6df2c.
Proof. vm_refl. Qed.
Lemma D_6df2c : decode_any W_6df2c = Some (OpImm ALU_ADD 10 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6df30 : bv 32 := 0x058000ef.
Lemma F_6df30 : fetch_word Ubsan.M.loaded_segments (0x6df70 : word) = Some W_6df30.
Proof. vm_refl. Qed.
Lemma D_6df30 : decode_any W_6df30 = Some (Jal 1 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_6df34 : bv 32 := 0x00013503.
Lemma F_6df34 : fetch_word Ubsan.M.loaded_segments (0x6df74 : word) = Some W_6df34.
Proof. vm_refl. Qed.
Lemma D_6df34 : decode_any W_6df34 = Some (Load SZ8 true 10 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6df38 : bv 32 := 0x04050663.
Lemma F_6df38 : fetch_word Ubsan.M.loaded_segments (0x6df78 : word) = Some W_6df38.
Proof. vm_refl. Qed.
Lemma D_6df38 : decode_any W_6df38 = Some (Branch BC_EQ 10 0 76, 4%Z).
Proof. vm_refl. Qed.

Definition W_6df3c : bv 32 := 0x00757593.
Lemma F_6df3c : fetch_word Ubsan.M.loaded_segments (0x6df7c : word) = Some W_6df3c.
Proof. vm_refl. Qed.
Lemma D_6df3c : decode_any W_6df3c = Some (OpImm ALU_AND 11 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_6df40 : bv 32 := 0x04059263.
Lemma F_6df40 : fetch_word Ubsan.M.loaded_segments (0x6df80 : word) = Some W_6df40.
Proof. vm_refl. Qed.
Lemma D_6df40 : decode_any W_6df40 = Some (Branch BC_NE 11 0 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_6df44 : bv 32 := 0x0d4000ef.
Lemma F_6df44 : fetch_word Ubsan.M.loaded_segments (0x6df84 : word) = Some W_6df44.
Proof. vm_refl. Qed.
Lemma D_6df44 : decode_any W_6df44 = Some (Jal 1 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_6df48 : bv 32 := 0x03813583.
Lemma F_6df48 : fetch_word Ubsan.M.loaded_segments (0x6df88 : word) = Some W_6df48.
Proof. vm_refl. Qed.
Lemma D_6df48 : decode_any W_6df48 = Some (Load SZ8 true 11 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_6df4c : bv 32 := 0x00a5f533.
Lemma F_6df4c : fetch_word Ubsan.M.loaded_segments (0x6df8c : word) = Some W_6df4c.
Proof. vm_refl. Qed.
Lemma D_6df4c : decode_any W_6df4c = Some (Op ALU_AND 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6df50 : bv 32 := 0x0005059b.
Lemma F_6df50 : fetch_word Ubsan.M.loaded_segments (0x6df90 : word) = Some W_6df50.
Proof. vm_refl. Qed.
Lemma D_6df50 : decode_any W_6df50 = Some (OpImm32 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6df54 : bv 32 := 0xfe95f0e3.
Lemma F_6df54 : fetch_word Ubsan.M.loaded_segments (0x6df94 : word) = Some W_6df54.
Proof. vm_refl. Qed.
Lemma D_6df54 : decode_any W_6df54 = Some (Branch BC_GEU 11 9 8160, 4%Z).
Proof. vm_refl. Qed.

Definition W_6df58 : bv 32 := 0x00042583.
Lemma F_6df58 : fetch_word Ubsan.M.loaded_segments (0x6df98 : word) = Some W_6df58.
Proof. vm_refl. Qed.
Lemma D_6df58 : decode_any W_6df58 = Some (Load SZ4 true 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6df5c : bv 32 := 0x00a58533.
Lemma F_6df5c : fetch_word Ubsan.M.loaded_segments (0x6df9c : word) = Some W_6df5c.
Proof. vm_refl. Qed.
Lemma D_6df5c : decode_any W_6df5c = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6df60 : bv 32 := 0x00c0006f.
Lemma F_6df60 : fetch_word Ubsan.M.loaded_segments (0x6dfa0 : word) = Some W_6df60.
Proof. vm_refl. Qed.
Lemma D_6df60 : decode_any W_6df60 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6df6c : bv 32 := 0x0005051b.
Lemma F_6df6c : fetch_word Ubsan.M.loaded_segments (0x6dfac : word) = Some W_6df6c.
Proof. vm_refl. Qed.
Lemma D_6df6c : decode_any W_6df6c = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6df70 : bv 32 := 0x05813083.
Lemma F_6df70 : fetch_word Ubsan.M.loaded_segments (0x6dfb0 : word) = Some W_6df70.
Proof. vm_refl. Qed.
Lemma D_6df70 : decode_any W_6df70 = Some (Load SZ8 true 1 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_6df74 : bv 32 := 0x05013403.
Lemma F_6df74 : fetch_word Ubsan.M.loaded_segments (0x6dfb4 : word) = Some W_6df74.
Proof. vm_refl. Qed.
Lemma D_6df74 : decode_any W_6df74 = Some (Load SZ8 true 8 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_6df78 : bv 32 := 0x04813483.
Lemma F_6df78 : fetch_word Ubsan.M.loaded_segments (0x6dfb8 : word) = Some W_6df78.
Proof. vm_refl. Qed.
Lemma D_6df78 : decode_any W_6df78 = Some (Load SZ8 true 9 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_6df7c : bv 32 := 0x06010113.
Lemma F_6df7c : fetch_word Ubsan.M.loaded_segments (0x6dfbc : word) = Some W_6df7c.
Proof. vm_refl. Qed.
Lemma D_6df7c : decode_any W_6df7c = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_6df80 : bv 32 := 0x00008067.
Lemma F_6df80 : fetch_word Ubsan.M.loaded_segments (0x6dfc0 : word) = Some W_6df80.
Proof. vm_refl. Qed.
Lemma D_6df80 : decode_any W_6df80 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6df88 : bv 32 := 0x00665693.
Lemma F_6df88 : fetch_word Ubsan.M.loaded_segments (0x6dfc8 : word) = Some W_6df88.
Proof. vm_refl. Qed.
Lemma D_6df88 : decode_any W_6df88 = Some (ShiftImm ALU_SRL 13 12 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_6df8c : bv 32 := 0x03f67713.
Lemma F_6df8c : fetch_word Ubsan.M.loaded_segments (0x6dfcc : word) = Some W_6df8c.
Proof. vm_refl. Qed.
Lemma D_6df8c : decode_any W_6df8c = Some (OpImm ALU_AND 14 12 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_6df90 : bv 32 := 0x00e03733.
Lemma F_6df90 : fetch_word Ubsan.M.loaded_segments (0x6dfd0 : word) = Some W_6df90.
Proof. vm_refl. Qed.
Lemma D_6df90 : decode_any W_6df90 = Some (Op ALU_SLTU 14 0 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_6df94 : bv 32 := 0x00e686b3.
Lemma F_6df94 : fetch_word Ubsan.M.loaded_segments (0x6dfd4 : word) = Some W_6df94.
Proof. vm_refl. Qed.
Lemma D_6df94 : decode_any W_6df94 = Some (Op ALU_ADD 13 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_6df98 : bv 32 := 0x00b53023.
Lemma F_6df98 : fetch_word Ubsan.M.loaded_segments (0x6dfd8 : word) = Some W_6df98.
Proof. vm_refl. Qed.
Lemma D_6df98 : decode_any W_6df98 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6df9c : bv 32 := 0x00c53423.
Lemma F_6df9c : fetch_word Ubsan.M.loaded_segments (0x6dfdc : word) = Some W_6df9c.
Proof. vm_refl. Qed.
Lemma D_6df9c : decode_any W_6df9c = Some (Store SZ8 10 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dfa0 : bv 32 := 0x00d53c23.
Lemma F_6dfa0 : fetch_word Ubsan.M.loaded_segments (0x6dfe0 : word) = Some W_6dfa0.
Proof. vm_refl. Qed.
Lemma D_6dfa0 : decode_any W_6dfa0 = Some (Store SZ8 10 13 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dfa4 : bv 32 := 0x06068863.
Lemma F_6dfa4 : fetch_word Ubsan.M.loaded_segments (0x6dfe4 : word) = Some W_6dfa4.
Proof. vm_refl. Qed.
Lemma D_6dfa4 : decode_any W_6dfa4 = Some (Branch BC_EQ 13 0 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dfa8 : bv 32 := 0x02d655b3.
Lemma F_6dfa8 : fetch_word Ubsan.M.loaded_segments (0x6dfe8 : word) = Some W_6dfa8.
Proof. vm_refl. Qed.
Lemma D_6dfa8 : decode_any W_6dfa8 = Some (Mul M_DIVU 11 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dfac : bv 32 := 0x03f00713.
Lemma F_6dfac : fetch_word Ubsan.M.loaded_segments (0x6dfec : word) = Some W_6dfac.
Proof. vm_refl. Qed.
Lemma D_6dfac : decode_any W_6dfac = Some (OpImm ALU_ADD 14 0 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dfb0 : bv 32 := 0x02d587b3.
Lemma F_6dfb0 : fetch_word Ubsan.M.loaded_segments (0x6dff0 : word) = Some W_6dfb0.
Proof. vm_refl. Qed.
Lemma D_6dfb0 : decode_any W_6dfb0 = Some (Mul M_MUL 15 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dfb4 : bv 32 := 0x40c787b3.
Lemma F_6dfb4 : fetch_word Ubsan.M.loaded_segments (0x6dff4 : word) = Some W_6dfb4.
Proof. vm_refl. Qed.
Lemma D_6dfb4 : decode_any W_6dfb4 = Some (Op ALU_SUB 15 15 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dfb8 : bv 32 := 0x00f687b3.
Lemma F_6dfb8 : fetch_word Ubsan.M.loaded_segments (0x6dff8 : word) = Some W_6dfb8.
Proof. vm_refl. Qed.
Lemma D_6dfb8 : decode_any W_6dfb8 = Some (Op ALU_ADD 15 13 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dfbc : bv 32 := 0x00b53823.
Lemma F_6dfbc : fetch_word Ubsan.M.loaded_segments (0x6dffc : word) = Some W_6dfbc.
Proof. vm_refl. Qed.
Lemma D_6dfbc : decode_any W_6dfbc = Some (Store SZ8 10 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dfc0 : bv 32 := 0x02f53023.
Lemma F_6dfc0 : fetch_word Ubsan.M.loaded_segments (0x6e000 : word) = Some W_6dfc0.
Proof. vm_refl. Qed.
Lemma D_6dfc0 : decode_any W_6dfc0 = Some (Store SZ8 10 15 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dfc4 : bv 32 := 0x02053423.
Lemma F_6dfc4 : fetch_word Ubsan.M.loaded_segments (0x6e004 : word) = Some W_6dfc4.
Proof. vm_refl. Qed.
Lemma D_6dfc4 : decode_any W_6dfc4 = Some (Store SZ8 10 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dfc8 : bv 32 := 0x02053823.
Lemma F_6dfc8 : fetch_word Ubsan.M.loaded_segments (0x6e008 : word) = Some W_6dfc8.
Proof. vm_refl. Qed.
Lemma D_6dfc8 : decode_any W_6dfc8 = Some (Store SZ8 10 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dfcc : bv 32 := 0x00e5f863.
Lemma F_6dfcc : fetch_word Ubsan.M.loaded_segments (0x6e00c : word) = Some W_6dfcc.
Proof. vm_refl. Qed.
Lemma D_6dfcc : decode_any W_6dfcc = Some (Branch BC_GEU 11 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dfd0 : bv 32 := 0x00d67a63.
Lemma F_6dfd0 : fetch_word Ubsan.M.loaded_segments (0x6e010 : word) = Some W_6dfd0.
Proof. vm_refl. Qed.
Lemma D_6dfd0 : decode_any W_6dfd0 = Some (Branch BC_GEU 12 13 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dfe4 : bv 32 := 0x40b0063b.
Lemma F_6dfe4 : fetch_word Ubsan.M.loaded_segments (0x6e024 : word) = Some W_6dfe4.
Proof. vm_refl. Qed.
Lemma D_6dfe4 : decode_any W_6dfe4 = Some (Op32 ALU_SUB 12 0 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dfe8 : bv 32 := 0xfff00693.
Lemma F_6dfe8 : fetch_word Ubsan.M.loaded_segments (0x6e028 : word) = Some W_6dfe8.
Proof. vm_refl. Qed.
Lemma D_6dfe8 : decode_any W_6dfe8 = Some (OpImm ALU_ADD 13 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dfec : bv 32 := 0x00c6d633.
Lemma F_6dfec : fetch_word Ubsan.M.loaded_segments (0x6e02c : word) = Some W_6dfec.
Proof. vm_refl. Qed.
Lemma D_6dfec : decode_any W_6dfec = Some (Op ALU_SRL 12 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dff0 : bv 32 := 0xfff5c693.
Lemma F_6dff0 : fetch_word Ubsan.M.loaded_segments (0x6e030 : word) = Some W_6dff0.
Proof. vm_refl. Qed.
Lemma D_6dff0 : decode_any W_6dff0 = Some (OpImm ALU_XOR 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dff4 : bv 32 := 0xfff00713.
Lemma F_6dff4 : fetch_word Ubsan.M.loaded_segments (0x6e034 : word) = Some W_6dff4.
Proof. vm_refl. Qed.
Lemma D_6dff4 : decode_any W_6dff4 = Some (OpImm ALU_ADD 14 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dff8 : bv 32 := 0x00d756b3.
Lemma F_6dff8 : fetch_word Ubsan.M.loaded_segments (0x6e038 : word) = Some W_6dff8.
Proof. vm_refl. Qed.
Lemma D_6dff8 : decode_any W_6dff8 = Some (Op ALU_SRL 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dffc : bv 32 := 0x03f5b593.
Lemma F_6dffc : fetch_word Ubsan.M.loaded_segments (0x6e03c : word) = Some W_6dffc.
Proof. vm_refl. Qed.
Lemma D_6dffc : decode_any W_6dffc = Some (OpImm ALU_SLTU 11 11 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e000 : bv 32 := 0xfff58593.
Lemma F_6e000 : fetch_word Ubsan.M.loaded_segments (0x6e040 : word) = Some W_6e000.
Proof. vm_refl. Qed.
Lemma D_6e000 : decode_any W_6e000 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e004 : bv 32 := 0x00d5e5b3.
Lemma F_6e004 : fetch_word Ubsan.M.loaded_segments (0x6e044 : word) = Some W_6e004.
Proof. vm_refl. Qed.
Lemma D_6e004 : decode_any W_6e004 = Some (Op ALU_OR 11 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e008 : bv 32 := 0x02c53c23.
Lemma F_6e008 : fetch_word Ubsan.M.loaded_segments (0x6e048 : word) = Some W_6e008.
Proof. vm_refl. Qed.
Lemma D_6e008 : decode_any W_6e008 = Some (Store SZ8 10 12 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e00c : bv 32 := 0x04b53023.
Lemma F_6e00c : fetch_word Ubsan.M.loaded_segments (0x6e04c : word) = Some W_6e00c.
Proof. vm_refl. Qed.
Lemma D_6e00c : decode_any W_6e00c = Some (Store SZ8 10 11 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e010 : bv 32 := 0x00008067.
Lemma F_6e010 : fetch_word Ubsan.M.loaded_segments (0x6e050 : word) = Some W_6e010.
Proof. vm_refl. Qed.
Lemma D_6e010 : decode_any W_6e010 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e018 : bv 32 := 0x7ff50593.
Lemma F_6e018 : fetch_word Ubsan.M.loaded_segments (0x6e058 : word) = Some W_6e018.
Proof. vm_refl. Qed.
Lemma D_6e018 : decode_any W_6e018 = Some (OpImm ALU_ADD 11 10 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e01c : bv 32 := 0x1c15b703.
Lemma F_6e01c : fetch_word Ubsan.M.loaded_segments (0x6e05c : word) = Some W_6e01c.
Proof. vm_refl. Qed.
Lemma D_6e01c : decode_any W_6e01c = Some (Load SZ8 true 14 11 449, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e020 : bv 32 := 0x13800613.
Lemma F_6e020 : fetch_word Ubsan.M.loaded_segments (0x6e060 : word) = Some W_6e020.
Proof. vm_refl. Qed.
Lemma D_6e020 : decode_any W_6e020 = Some (OpImm ALU_ADD 12 0 312, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e024 : bv 32 := 0x10c77863.
Lemma F_6e024 : fetch_word Ubsan.M.loaded_segments (0x6e064 : word) = Some W_6e024.
Proof. vm_refl. Qed.
Lemma D_6e024 : decode_any W_6e024 = Some (Branch BC_GEU 14 12 272, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e028 : bv 32 := 0x00371793.
Lemma F_6e028 : fetch_word Ubsan.M.loaded_segments (0x6e068 : word) = Some W_6e028.
Proof. vm_refl. Qed.
Lemma D_6e028 : decode_any W_6e028 = Some (ShiftImm ALU_SLL 15 14 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e02c : bv 32 := 0xfff54693.
Lemma F_6e02c : fetch_word Ubsan.M.loaded_segments (0x6e06c : word) = Some W_6e02c.
Proof. vm_refl. Qed.
Lemma D_6e02c : decode_any W_6e02c = Some (OpImm ALU_XOR 13 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e030 : bv 32 := 0x10f6e263.
Lemma F_6e030 : fetch_word Ubsan.M.loaded_segments (0x6e070 : word) = Some W_6e030.
Proof. vm_refl. Qed.
Lemma D_6e030 : decode_any W_6e030 = Some (Branch BC_LTU 13 15 260, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e034 : bv 32 := 0xfffa7817.
Lemma F_6e034 : fetch_word Ubsan.M.loaded_segments (0x6e074 : word) = Some W_6e034.
Proof. vm_refl. Qed.
Lemma D_6e034 : decode_any W_6e034 = Some (Auipc 16 1048487, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e038 : bv 32 := 0x8d483803.
Lemma F_6e038 : fetch_word Ubsan.M.loaded_segments (0x6e078 : word) = Some W_6e038.
Proof. vm_refl. Qed.
Lemma D_6e038 : decode_any W_6e038 = Some (Load SZ8 true 16 16 2260, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e03c : bv 32 := 0x00170893.
Lemma F_6e03c : fetch_word Ubsan.M.loaded_segments (0x6e07c : word) = Some W_6e03c.
Proof. vm_refl. Qed.
Lemma D_6e03c : decode_any W_6e03c = Some (OpImm ALU_ADD 17 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e040 : bv 32 := 0x0038d293.
Lemma F_6e040 : fetch_word Ubsan.M.loaded_segments (0x6e080 : word) = Some W_6e040.
Proof. vm_refl. Qed.
Lemma D_6e040 : decode_any W_6e040 = Some (ShiftImm ALU_SRL 5 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e044 : bv 32 := 0x0302b833.
Lemma F_6e044 : fetch_word Ubsan.M.loaded_segments (0x6e084 : word) = Some W_6e044.
Proof. vm_refl. Qed.
Lemma D_6e044 : decode_any W_6e044 = Some (Mul M_MULHU 16 5 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e048 : bv 32 := 0x00185813.
Lemma F_6e048 : fetch_word Ubsan.M.loaded_segments (0x6e088 : word) = Some W_6e048.
Proof. vm_refl. Qed.
Lemma D_6e048 : decode_any W_6e048 = Some (ShiftImm ALU_SRL 16 16 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e04c : bv 32 := 0x02c80633.
Lemma F_6e04c : fetch_word Ubsan.M.loaded_segments (0x6e08c : word) = Some W_6e04c.
Proof. vm_refl. Qed.
Lemma D_6e04c : decode_any W_6e04c = Some (Mul M_MUL 12 16 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e050 : bv 32 := 0x40c88633.
Lemma F_6e050 : fetch_word Ubsan.M.loaded_segments (0x6e090 : word) = Some W_6e050.
Proof. vm_refl. Qed.
Lemma D_6e050 : decode_any W_6e050 = Some (Op ALU_SUB 12 17 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e054 : bv 32 := 0x00361813.
Lemma F_6e054 : fetch_word Ubsan.M.loaded_segments (0x6e094 : word) = Some W_6e054.
Proof. vm_refl. Qed.
Lemma D_6e054 : decode_any W_6e054 = Some (ShiftImm ALU_SLL 16 12 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e058 : bv 32 := 0x0d06ee63.
Lemma F_6e058 : fetch_word Ubsan.M.loaded_segments (0x6e098 : word) = Some W_6e058.
Proof. vm_refl. Qed.
Lemma D_6e058 : decode_any W_6e058 = Some (Branch BC_LTU 13 16 220, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e05c : bv 32 := 0x09c00893.
Lemma F_6e05c : fetch_word Ubsan.M.loaded_segments (0x6e09c : word) = Some W_6e05c.
Proof. vm_refl. Qed.
Lemma D_6e05c : decode_any W_6e05c = Some (OpImm ALU_ADD 17 0 156, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e060 : bv 32 := 0x01176463.
Lemma F_6e060 : fetch_word Ubsan.M.loaded_segments (0x6e0a0 : word) = Some W_6e060.
Proof. vm_refl. Qed.
Lemma D_6e060 : decode_any W_6e060 = Some (Branch BC_LTU 14 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e068 : bv 32 := 0x01170733.
Lemma F_6e068 : fetch_word Ubsan.M.loaded_segments (0x6e0a8 : word) = Some W_6e068.
Proof. vm_refl. Qed.
Lemma D_6e068 : decode_any W_6e068 = Some (Op ALU_ADD 14 14 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e06c : bv 32 := 0x00371713.
Lemma F_6e06c : fetch_word Ubsan.M.loaded_segments (0x6e0ac : word) = Some W_6e06c.
Proof. vm_refl. Qed.
Lemma D_6e06c : decode_any W_6e06c = Some (ShiftImm ALU_SLL 14 14 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e070 : bv 32 := 0x0ce6e263.
Lemma F_6e070 : fetch_word Ubsan.M.loaded_segments (0x6e0b0 : word) = Some W_6e070.
Proof. vm_refl. Qed.
Lemma D_6e070 : decode_any W_6e070 = Some (Branch BC_LTU 13 14 196, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e074 : bv 32 := 0x00f507b3.
Lemma F_6e074 : fetch_word Ubsan.M.loaded_segments (0x6e0b4 : word) = Some W_6e074.
Proof. vm_refl. Qed.
Lemma D_6e074 : decode_any W_6e074 = Some (Op ALU_ADD 15 10 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e078 : bv 32 := 0x00e50733.
Lemma F_6e078 : fetch_word Ubsan.M.loaded_segments (0x6e0b8 : word) = Some W_6e078.
Proof. vm_refl. Qed.
Lemma D_6e078 : decode_any W_6e078 = Some (Op ALU_ADD 14 10 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e07c : bv 32 := 0x01050833.
Lemma F_6e07c : fetch_word Ubsan.M.loaded_segments (0x6e0bc : word) = Some W_6e07c.
Proof. vm_refl. Qed.
Lemma D_6e07c : decode_any W_6e07c = Some (Op ALU_ADD 16 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e080 : bv 32 := 0x800008b7.
Lemma F_6e080 : fetch_word Ubsan.M.loaded_segments (0x6e0c0 : word) = Some W_6e080.
Proof. vm_refl. Qed.
Lemma D_6e080 : decode_any W_6e080 = Some (Lui 17 524288, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e084 : bv 32 := 0x0007b283.
Lemma F_6e084 : fetch_word Ubsan.M.loaded_segments (0x6e0c4 : word) = Some W_6e084.
Proof. vm_refl. Qed.
Lemma D_6e084 : decode_any W_6e084 = Some (Load SZ8 true 5 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e088 : bv 32 := 0xfffa7317.
Lemma F_6e088 : fetch_word Ubsan.M.loaded_segments (0x6e0c8 : word) = Some W_6e088.
Proof. vm_refl. Qed.
Lemma D_6e088 : decode_any W_6e088 = Some (Auipc 6 1048487, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e08c : bv 32 := 0x00073703.
Lemma F_6e08c : fetch_word Ubsan.M.loaded_segments (0x6e0cc : word) = Some W_6e08c.
Proof. vm_refl. Qed.
Lemma D_6e08c : decode_any W_6e08c = Some (Load SZ8 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e090 : bv 32 := 0x00083803.
Lemma F_6e090 : fetch_word Ubsan.M.loaded_segments (0x6e0d0 : word) = Some W_6e090.
Proof. vm_refl. Qed.
Lemma D_6e090 : decode_any W_6e090 = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e094 : bv 32 := 0x0112f2b3.
Lemma F_6e094 : fetch_word Ubsan.M.loaded_segments (0x6e0d4 : word) = Some W_6e094.
Proof. vm_refl. Qed.
Lemma D_6e094 : decode_any W_6e094 = Some (Op ALU_AND 5 5 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e098 : bv 32 := 0xffe8889b.
Lemma F_6e098 : fetch_word Ubsan.M.loaded_segments (0x6e0d8 : word) = Some W_6e098.
Proof. vm_refl. Qed.
Lemma D_6e098 : decode_any W_6e098 = Some (OpImm32 17 17 4094, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e09c : bv 32 := 0x94833303.
Lemma F_6e09c : fetch_word Ubsan.M.loaded_segments (0x6e0dc : word) = Some W_6e09c.
Proof. vm_refl. Qed.
Lemma D_6e09c : decode_any W_6e09c = Some (Load SZ8 true 6 6 2376, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e0a0 : bv 32 := 0x011878b3.
Lemma F_6e0a0 : fetch_word Ubsan.M.loaded_segments (0x6e0e0 : word) = Some W_6e0a0.
Proof. vm_refl. Qed.
Lemma D_6e0a0 : decode_any W_6e0a0 = Some (Op ALU_AND 17 16 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e0a4 : bv 32 := 0x03f81813.
Lemma F_6e0a4 : fetch_word Ubsan.M.loaded_segments (0x6e0e4 : word) = Some W_6e0a4.
Proof. vm_refl. Qed.
Lemma D_6e0a4 : decode_any W_6e0a4 = Some (ShiftImm ALU_SLL 16 16 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e0a8 : bv 32 := 0x0058e8b3.
Lemma F_6e0a8 : fetch_word Ubsan.M.loaded_segments (0x6e0e8 : word) = Some W_6e0a8.
Proof. vm_refl. Qed.
Lemma D_6e0a8 : decode_any W_6e0a8 = Some (Op ALU_OR 17 17 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e0ac : bv 32 := 0x43f85813.
Lemma F_6e0ac : fetch_word Ubsan.M.loaded_segments (0x6e0ec : word) = Some W_6e0ac.
Proof. vm_refl. Qed.
Lemma D_6e0ac : decode_any W_6e0ac = Some (ShiftImm ALU_SRA 16 16 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e0b0 : bv 32 := 0x0018d893.
Lemma F_6e0b0 : fetch_word Ubsan.M.loaded_segments (0x6e0f0 : word) = Some W_6e0b0.
Proof. vm_refl. Qed.
Lemma D_6e0b0 : decode_any W_6e0b0 = Some (ShiftImm ALU_SRL 17 17 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e0b4 : bv 32 := 0x00687833.
Lemma F_6e0b4 : fetch_word Ubsan.M.loaded_segments (0x6e0f4 : word) = Some W_6e0b4.
Proof. vm_refl. Qed.
Lemma D_6e0b4 : decode_any W_6e0b4 = Some (Op ALU_AND 16 16 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e0b8 : bv 32 := 0x0108c833.
Lemma F_6e0b8 : fetch_word Ubsan.M.loaded_segments (0x6e0f8 : word) = Some W_6e0b8.
Proof. vm_refl. Qed.
Lemma D_6e0b8 : decode_any W_6e0b8 = Some (Op ALU_XOR 16 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e0bc : bv 32 := 0x00e84733.
Lemma F_6e0bc : fetch_word Ubsan.M.loaded_segments (0x6e0fc : word) = Some W_6e0bc.
Proof. vm_refl. Qed.
Lemma D_6e0bc : decode_any W_6e0bc = Some (Op ALU_XOR 14 16 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e0c0 : bv 32 := 0x00e7b023.
Lemma F_6e0c0 : fetch_word Ubsan.M.loaded_segments (0x6e100 : word) = Some W_6e0c0.
Proof. vm_refl. Qed.
Lemma D_6e0c0 : decode_any W_6e0c0 = Some (Store SZ8 15 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e0c4 : bv 32 := 0x1c15b703.
Lemma F_6e0c4 : fetch_word Ubsan.M.loaded_segments (0x6e104 : word) = Some W_6e0c4.
Proof. vm_refl. Qed.
Lemma D_6e0c4 : decode_any W_6e0c4 = Some (Load SZ8 true 14 11 449, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e0c8 : bv 32 := 0x13700793.
Lemma F_6e0c8 : fetch_word Ubsan.M.loaded_segments (0x6e108 : word) = Some W_6e0c8.
Proof. vm_refl. Qed.
Lemma D_6e0c8 : decode_any W_6e0c8 = Some (OpImm ALU_ADD 15 0 311, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e0cc : bv 32 := 0x06e7e463.
Lemma F_6e0cc : fetch_word Ubsan.M.loaded_segments (0x6e10c : word) = Some W_6e0cc.
Proof. vm_refl. Qed.
Lemma D_6e0cc : decode_any W_6e0cc = Some (Branch BC_LTU 15 14 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e0d0 : bv 32 := 0x00371713.
Lemma F_6e0d0 : fetch_word Ubsan.M.loaded_segments (0x6e110 : word) = Some W_6e0d0.
Proof. vm_refl. Qed.
Lemma D_6e0d0 : decode_any W_6e0d0 = Some (ShiftImm ALU_SLL 14 14 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e0d4 : bv 32 := 0x06e6e063.
Lemma F_6e0d4 : fetch_word Ubsan.M.loaded_segments (0x6e114 : word) = Some W_6e0d4.
Proof. vm_refl. Qed.
Lemma D_6e0d4 : decode_any W_6e0d4 = Some (Branch BC_LTU 13 14 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e0d8 : bv 32 := 0x00e50533.
Lemma F_6e0d8 : fetch_word Ubsan.M.loaded_segments (0x6e118 : word) = Some W_6e0d8.
Proof. vm_refl. Qed.
Lemma D_6e0d8 : decode_any W_6e0d8 = Some (Op ALU_ADD 10 10 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e0dc : bv 32 := 0x005556b7.
Lemma F_6e0dc : fetch_word Ubsan.M.loaded_segments (0x6e11c : word) = Some W_6e0dc.
Proof. vm_refl. Qed.
Lemma D_6e0dc : decode_any W_6e0dc = Some (Lui 13 1365, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e0e0 : bv 32 := 0xfffa7717.
Lemma F_6e0e0 : fetch_word Ubsan.M.loaded_segments (0x6e120 : word) = Some W_6e0e0.
Proof. vm_refl. Qed.
Lemma D_6e0e0 : decode_any W_6e0e0 = Some (Auipc 14 1048487, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e0e4 : bv 32 := 0x00053503.
Lemma F_6e0e4 : fetch_word Ubsan.M.loaded_segments (0x6e124 : word) = Some W_6e0e4.
Proof. vm_refl. Qed.
Lemma D_6e0e4 : decode_any W_6e0e4 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e0e8 : bv 32 := 0x5556869b.
Lemma F_6e0e8 : fetch_word Ubsan.M.loaded_segments (0x6e128 : word) = Some W_6e0e8.
Proof. vm_refl. Qed.
Lemma D_6e0e8 : decode_any W_6e0e8 = Some (OpImm32 13 13 1365, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e0ec : bv 32 := 0x86073703.
Lemma F_6e0ec : fetch_word Ubsan.M.loaded_segments (0x6e12c : word) = Some W_6e0ec.
Proof. vm_refl. Qed.
Lemma D_6e0ec : decode_any W_6e0ec = Some (Load SZ8 true 14 14 2144, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e0f0 : bv 32 := 0x00c69693.
Lemma F_6e0f0 : fetch_word Ubsan.M.loaded_segments (0x6e130 : word) = Some W_6e0f0.
Proof. vm_refl. Qed.
Lemma D_6e0f0 : decode_any W_6e0f0 = Some (ShiftImm ALU_SLL 13 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e0f4 : bv 32 := 0x55568693.
Lemma F_6e0f4 : fetch_word Ubsan.M.loaded_segments (0x6e134 : word) = Some W_6e0f4.
Proof. vm_refl. Qed.
Lemma D_6e0f4 : decode_any W_6e0f4 = Some (OpImm ALU_ADD 13 13 1365, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e0f8 : bv 32 := 0x01d55793.
Lemma F_6e0f8 : fetch_word Ubsan.M.loaded_segments (0x6e138 : word) = Some W_6e0f8.
Proof. vm_refl. Qed.
Lemma D_6e0f8 : decode_any W_6e0f8 = Some (ShiftImm ALU_SRL 15 10 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e0fc : bv 32 := 0x00d7f6b3.
Lemma F_6e0fc : fetch_word Ubsan.M.loaded_segments (0x6e13c : word) = Some W_6e0fc.
Proof. vm_refl. Qed.
Lemma D_6e0fc : decode_any W_6e0fc = Some (Op ALU_AND 13 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e100 : bv 32 := 0x00a6c533.
Lemma F_6e100 : fetch_word Ubsan.M.loaded_segments (0x6e140 : word) = Some W_6e100.
Proof. vm_refl. Qed.
Lemma D_6e100 : decode_any W_6e100 = Some (Op ALU_XOR 10 13 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e104 : bv 32 := 0x01151693.
Lemma F_6e104 : fetch_word Ubsan.M.loaded_segments (0x6e144 : word) = Some W_6e104.
Proof. vm_refl. Qed.
Lemma D_6e104 : decode_any W_6e104 = Some (ShiftImm ALU_SLL 13 10 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e108 : bv 32 := 0x00e6f6b3.
Lemma F_6e108 : fetch_word Ubsan.M.loaded_segments (0x6e148 : word) = Some W_6e108.
Proof. vm_refl. Qed.
Lemma D_6e108 : decode_any W_6e108 = Some (Op ALU_AND 13 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e10c : bv 32 := 0xfbf77737.
Lemma F_6e10c : fetch_word Ubsan.M.loaded_segments (0x6e14c : word) = Some W_6e10c.
Proof. vm_refl. Qed.
Lemma D_6e10c : decode_any W_6e10c = Some (Lui 14 1032055, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e110 : bv 32 := 0x00a6c533.
Lemma F_6e110 : fetch_word Ubsan.M.loaded_segments (0x6e150 : word) = Some W_6e110.
Proof. vm_refl. Qed.
Lemma D_6e110 : decode_any W_6e110 = Some (Op ALU_XOR 10 13 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e114 : bv 32 := 0x02551693.
Lemma F_6e114 : fetch_word Ubsan.M.loaded_segments (0x6e154 : word) = Some W_6e114.
Proof. vm_refl. Qed.
Lemma D_6e114 : decode_any W_6e114 = Some (ShiftImm ALU_SLL 13 10 37, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e118 : bv 32 := 0x01971713.
Lemma F_6e118 : fetch_word Ubsan.M.loaded_segments (0x6e158 : word) = Some W_6e118.
Proof. vm_refl. Qed.
Lemma D_6e118 : decode_any W_6e118 = Some (ShiftImm ALU_SLL 14 14 25, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e11c : bv 32 := 0x00e6f6b3.
Lemma F_6e11c : fetch_word Ubsan.M.loaded_segments (0x6e15c : word) = Some W_6e11c.
Proof. vm_refl. Qed.
Lemma D_6e11c : decode_any W_6e11c = Some (Op ALU_AND 13 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e120 : bv 32 := 0x00a6c533.
Lemma F_6e120 : fetch_word Ubsan.M.loaded_segments (0x6e160 : word) = Some W_6e120.
Proof. vm_refl. Qed.
Lemma D_6e120 : decode_any W_6e120 = Some (Op ALU_XOR 10 13 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e124 : bv 32 := 0x02b55693.
Lemma F_6e124 : fetch_word Ubsan.M.loaded_segments (0x6e164 : word) = Some W_6e124.
Proof. vm_refl. Qed.
Lemma D_6e124 : decode_any W_6e124 = Some (ShiftImm ALU_SRL 13 10 43, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e128 : bv 32 := 0x00a6c533.
Lemma F_6e128 : fetch_word Ubsan.M.loaded_segments (0x6e168 : word) = Some W_6e128.
Proof. vm_refl. Qed.
Lemma D_6e128 : decode_any W_6e128 = Some (Op ALU_XOR 10 13 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e12c : bv 32 := 0x1cc5b0a3.
Lemma F_6e12c : fetch_word Ubsan.M.loaded_segments (0x6e16c : word) = Some W_6e12c.
Proof. vm_refl. Qed.
Lemma D_6e12c : decode_any W_6e12c = Some (Store SZ8 11 12 449, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e130 : bv 32 := 0x00008067.
Lemma F_6e130 : fetch_word Ubsan.M.loaded_segments (0x6e170 : word) = Some W_6e130.
Proof. vm_refl. Qed.
Lemma D_6e130 : decode_any W_6e130 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
End U1_code_6ddf0_6e138.

Module U1_code_6d098_6d0bc.

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Ubsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_6d098 : bv 32 := 0x02000593.
Lemma F_6d098 : fetch_word Ubsan.M.loaded_segments (0x6d0d8 : word) = Some W_6d098.
Proof. vm_refl. Qed.
Lemma D_6d098 : decode_any W_6d098 = Some (OpImm ALU_ADD 11 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_6d09c : bv 32 := 0x00b57e63.
Lemma F_6d09c : fetch_word Ubsan.M.loaded_segments (0x6d0dc : word) = Some W_6d09c.
Proof. vm_refl. Qed.
Lemma D_6d09c : decode_any W_6d09c = Some (Branch BC_GEU 10 11 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_6d0a0 : bv 32 := 0x01b53593.
Lemma F_6d0a0 : fetch_word Ubsan.M.loaded_segments (0x6d0e0 : word) = Some W_6d0a0.
Proof. vm_refl. Qed.
Lemma D_6d0a0 : decode_any W_6d0a0 = Some (OpImm ALU_SLTU 11 10 27, 4%Z).
Proof. vm_refl. Qed.

Definition W_6d0a4 : bv 32 := 0x07f80637.
Lemma F_6d0a4 : fetch_word Ubsan.M.loaded_segments (0x6d0e4 : word) = Some W_6d0a4.
Proof. vm_refl. Qed.
Lemma D_6d0a4 : decode_any W_6d0a4 = Some (Lui 12 32640, 4%Z).
Proof. vm_refl. Qed.

Definition W_6d0a8 : bv 32 := 0xfff6061b.
Lemma F_6d0a8 : fetch_word Ubsan.M.loaded_segments (0x6d0e8 : word) = Some W_6d0a8.
Proof. vm_refl. Qed.
Lemma D_6d0a8 : decode_any W_6d0a8 = Some (OpImm32 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_6d0ac : bv 32 := 0x00a65533.
Lemma F_6d0ac : fetch_word Ubsan.M.loaded_segments (0x6d0ec : word) = Some W_6d0ac.
Proof. vm_refl. Qed.
Lemma D_6d0ac : decode_any W_6d0ac = Some (Op ALU_SRL 10 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6d0b0 : bv 32 := 0x00a5f533.
Lemma F_6d0b0 : fetch_word Ubsan.M.loaded_segments (0x6d0f0 : word) = Some W_6d0b0.
Proof. vm_refl. Qed.
Lemma D_6d0b0 : decode_any W_6d0b0 = Some (Op ALU_AND 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6d0b4 : bv 32 := 0x00008067.
Lemma F_6d0b4 : fetch_word Ubsan.M.loaded_segments (0x6d0f4 : word) = Some W_6d0b4.
Proof. vm_refl. Qed.
Lemma D_6d0b4 : decode_any W_6d0b4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
End U1_code_6d098_6d0bc.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac WalkTac StartupTac SumWalkTac StoreOk MemSplit Hoare ShapeAlg
  SRealizes RefMemcpyLib RefReadLib LibIface LibEff MmapSim LibMaskBits U1Layout.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContLib StrLib ContStmts Lib_RG Lib_RG2 U1Facts U1Lib_RG.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.U1Lib_RG2.U1_code_6ddf0_6e138. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.U1Lib_RG2.U1_code_6d098_6d0bc.
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
Ltac slotv SL k H :=
  pose proof (SL k ltac:(lia)) as H;
  lazymatch type of H with rdn _ _ _ _ = Some (word_to_le_bytes 8 ?v) =>
    let v' := eval simpl in v in change v with v' in H end.
Ltac close_pc := lazymatch goal with |- msteps _ ?a ?bb => replace bb with a; [apply mst_refl|] end; f_equal; apply bv_eq; vm_compute; reflexivity.
Ltac wl := lazymatch goal with |- msteps _ (mkst (regupd _ _ ?v) _ _ _) _ => wlit v | |- _ => idtac end.
Ltac snl F D := stepn F D; pin; wl.
Ltac zval := gres; pin; imm_norm; apply bv_eq; unfold v_add, v_addi, v_sub, v_slli;
  rewrite ?Z_to_bv_unsigned, ?bv_wrap64_mod; imm_norm;
  rewrite ?Z.add_0_r, ?Zplus_mod_idemp_l, ?Zplus_mod_idemp_r, ?Z.mod_mod by lia;
  first [ reflexivity | f_equal; lia | rewrite !Z.mod_small by lia; lia ].
Ltac cmpz := pin; unfold c_ltu, c_eq, c_lts, bv_ltu, bv_lts, bv_eqb; imm_norm; rewrite ?u64_of_Z by lia; rewrite ?bv_signed_small64 by lia;
  first [apply Z.ltb_lt; lia | apply Z.ltb_ge; lia | apply Z.eqb_eq; lia | apply Z.eqb_neq; lia | reflexivity].

Lemma u1_img_K_DIV : rdn SEGS (fun _ => None) (Z_to_bv 64 K_DIV) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 945986875574848801)).
Proof. vm_refl_bv. Qed.
Lemma u1_img_K_A : rdn SEGS (fun _ => None) (Z_to_bv 64 K_A) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 13043109905998158313)).
Proof. vm_refl_bv. Qed.
Lemma u1_img_K_B : rdn SEGS (fun _ => None) (Z_to_bv 64 K_B) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 8202884508482404352)).
Proof. vm_refl_bv. Qed.

Section GTEU.
  Context {fx : FPState}.
Context {AC : AllocCeiling}.

  Lemma ENGINE_U : forall R M (obj ret : Z),
    0 <= obj -> obj + 2504 <= 2 ^ 63 -> alloc_ceiling <= obj -> ro_clear Ly.L M -> mdef M obj 2504 ->
    fld SEGS M (obj + 2496) 8 0 -> fld SEGS M obj 8 5489 -> fld SEGS M (obj + 8) 8 X1 -> fld SEGS M (obj + 1248) 8 X156 ->
    getr R 10%bv = Z_to_bv 64 obj -> getr R 1%bv = Z_to_bv 64 ret -> ret_ok (Z_to_bv 64 ret) ->
    exists R',
      msteps SEGS (@mkst fx R (Z_to_bv 64 0x6e058) M (seg_rom SEGS))
                  (@mkst fx R' (Z_to_bv 64 ret)
                     (wbytes (wbytes M (Z_to_bv 64 obj) (word_to_le_bytes 8 (Z_to_bv 64 NX0))) (Z_to_bv 64 (obj + 2496)) (word_to_le_bytes 8 (Z_to_bv 64 1)))
                     (seg_rom SEGS))
      /\ getr R' 10%bv = Z_to_bv 64 OUT0
      /\ (forall r, ~ In r [5; 6; 10; 11; 12; 13; 14; 15; 16; 17]%bv -> getr R' r = getr R r).
  Proof using fx AC.
    intros R M obj ret Ho0 Ho1 Hoc ROC HD F2496 F0 F1 F156 Ha0 Hra Hret. pose proof ac_bounds_lit as Hcv.
    assert (RO : forall K v, rdn SEGS (fun _ => None) (Z_to_bv 64 K) 8 = Some v -> 0x10000 <= K -> K + 8 <= 0xe8000 ->
                  rdn SEGS M (Z_to_bv 64 K) 8 = Some v).
    { intros K v HK H1 H2. rewrite (u1_ro_rdn M K 8 ROC); [exact HK | lia | cbn; lia]. }
    unfold fld in F2496, F0, F1, F156.
    eexists. split.
    - norm_pc.
      stepiv F_6e018 D_6e018 (Z_to_bv 64 (obj + 2047)) ltac:(gres; pin; imm_norm; rewrite v_addi_Z by lia; reflexivity).
      ld_step F_6e01c D_6e01c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rdn_fix F2496) ltac:(b2z8).
      snl F_6e020 D_6e020.
      stepb_ft F_6e024 D_6e024 ltac:(cmpz).
      snl F_6e028 D_6e028.
      stepiv F_6e02c D_6e02c (Z_to_bv 64 (2 ^ 64 - 1 - obj)) ltac:(gres; pin; imm_norm; apply v_not_Z; lia).
      stepb_ft F_6e030 D_6e030 ltac:(cmpz).
      snl F_6e034 D_6e034.
      ld_step F_6e038 D_6e038 (word_to_le_bytes 8 (Z_to_bv 64 945986875574848801)) (Z_to_bv 64 945986875574848801)
        ltac:(apply (RO K_DIV); [exact u1_img_K_DIV | unfold K_DIV; lia | unfold K_DIV; lia]) ltac:(b2z8).
      snl F_6e03c D_6e03c. snl F_6e040 D_6e040. snl F_6e044 D_6e044. snl F_6e048 D_6e048. snl F_6e04c D_6e04c.
      snl F_6e050 D_6e050. snl F_6e054 D_6e054.
      stepb_ft F_6e058 D_6e058 ltac:(cmpz).
      snl F_6e05c D_6e05c.
      stepb_tk F_6e060 D_6e060 ltac:(cmpz).
      snl F_6e068 D_6e068. snl F_6e06c D_6e06c.
      stepb_ft F_6e070 D_6e070 ltac:(cmpz).
      stepiv F_6e074 D_6e074 (Z_to_bv 64 obj) ltac:(zval).
      stepiv F_6e078 D_6e078 (Z_to_bv 64 (obj + 1248)) ltac:(zval).
      stepiv F_6e07c D_6e07c (Z_to_bv 64 (obj + 8)) ltac:(zval).
      snl F_6e080 D_6e080.
      ld_step F_6e084 D_6e084 (word_to_le_bytes 8 (Z_to_bv 64 5489)) (Z_to_bv 64 5489) ltac:(rdn_fix F0) ltac:(b2z8).
      snl F_6e088 D_6e088.
      ld_step F_6e08c D_6e08c (word_to_le_bytes 8 (Z_to_bv 64 X156)) (Z_to_bv 64 X156) ltac:(rdn_fix F156) ltac:(b2z8).
      ld_step F_6e090 D_6e090 (word_to_le_bytes 8 (Z_to_bv 64 X1)) (Z_to_bv 64 X1) ltac:(rdn_fix F1) ltac:(b2z8).
      unfold X1, X156.
      snl F_6e094 D_6e094. snl F_6e098 D_6e098.
      ld_step F_6e09c D_6e09c (word_to_le_bytes 8 (Z_to_bv 64 13043109905998158313)) (Z_to_bv 64 13043109905998158313)
        ltac:(apply (RO K_A); [exact u1_img_K_A | unfold K_A; lia | unfold K_A; lia]) ltac:(b2z8).
      snl F_6e0a0 D_6e0a0. snl F_6e0a4 D_6e0a4. snl F_6e0a8 D_6e0a8. snl F_6e0ac D_6e0ac. snl F_6e0b0 D_6e0b0.
      snl F_6e0b4 D_6e0b4. snl F_6e0b8 D_6e0b8. snl F_6e0bc D_6e0bc.
      stw F_6e0c0 D_6e0c0 (Z_to_bv 64 obj) (Z_to_bv 64 NX0) ltac:(ok_mdef HD).
      ld_step F_6e0c4 D_6e0c4 (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(peel; rdn_fix F2496) ltac:(b2z8).
      snl F_6e0c8 D_6e0c8.
      stepb_ft F_6e0cc D_6e0cc ltac:(cmpz).
      snl F_6e0d0 D_6e0d0.
      stepb_ft F_6e0d4 D_6e0d4 ltac:(cmpz).
      stepiv F_6e0d8 D_6e0d8 (Z_to_bv 64 obj) ltac:(zval).
      snl F_6e0dc D_6e0dc. snl F_6e0e0 D_6e0e0.
      ld_step F_6e0e4 D_6e0e4 (word_to_le_bytes 8 (Z_to_bv 64 NX0)) (Z_to_bv 64 NX0) ltac:(apply rdn_wbytes_hit8; rewrite u64_of_Z by lia; lia) ltac:(b2z8).
      snl F_6e0e8 D_6e0e8.
      ld_step F_6e0ec D_6e0ec (word_to_le_bytes 8 (Z_to_bv 64 8202884508482404352)) (Z_to_bv 64 8202884508482404352)
        ltac:(peel; apply (RO K_B); [exact u1_img_K_B | unfold K_B; lia | unfold K_B; lia]) ltac:(b2z8).
      unfold NX0.
      snl F_6e0f0 D_6e0f0. snl F_6e0f4 D_6e0f4. snl F_6e0f8 D_6e0f8. snl F_6e0fc D_6e0fc. snl F_6e100 D_6e100.
      snl F_6e104 D_6e104. snl F_6e108 D_6e108. snl F_6e10c D_6e10c. snl F_6e110 D_6e110. snl F_6e114 D_6e114.
      snl F_6e118 D_6e118. snl F_6e11c D_6e11c. snl F_6e120 D_6e120. snl F_6e124 D_6e124. snl F_6e128 D_6e128.
      stw F_6e12c D_6e12c (Z_to_bv 64 (obj + 2496)) (Z_to_bv 64 1) ltac:(ok_mdef HD).
      stepjr F_6e130 D_6e130 (Z_to_bv 64 ret) ltac:(gres; exact Hra).
      lazymatch goal with |- msteps _ (mkst ?r ?pc ?m _) (mkst ?r' ?pc' ?m' _) =>
        unify r' r; replace pc with pc' by (symmetry; imm_norm; exact Hret);
        replace m with m' by (repeat f_equal; apply bv_eq; vm_compute; reflexivity) end.
      apply mst_refl.
    - split.
      + gres. apply bv_eq. vm_compute. reflexivity.
      + intros r Hr. rewrite !getr_other by (intros ->; apply Hr; (first [solve [clear; cbv; tauto] | cbv; tauto])). reflexivity.
  Qed.

  Lemma IBE_U : forall R M (fr obj ret : Z),
    0 <= fr -> fr + 72 <= 2 ^ 63 -> mdef M fr 72 -> 0 <= obj < 2 ^ 64 ->
    getr R 10%bv = Z_to_bv 64 fr -> getr R 11%bv = Z_to_bv 64 obj -> getr R 12%bv = Z_to_bv 64 5 ->
    getr R 1%bv = Z_to_bv 64 ret -> ret_ok (Z_to_bv 64 ret) ->
    exists R' M',
      msteps SEGS (@mkst fx R (Z_to_bv 64 0x6dfc8) M (seg_rom SEGS)) (@mkst fx R' (Z_to_bv 64 ret) M' (seg_rom SEGS))
      /\ stores_in (zwin fr (fr + 72)) M M'
      /\ fld SEGS M' fr 8 obj /\ fld SEGS M' (fr + 56) 8 31
      /\ (forall r, ~ In r [11; 12; 13; 14; 15]%bv -> getr R' r = getr R r).
  Proof using fx.
    intros R M fr obj ret Hf0 Hf1 HD Hobj Ha0 Ha1 Ha2 Hra Hret.
    eexists. eexists. split; [|split; [|split; [|split]]].
    - norm_pc.
      snl F_6df88 D_6df88. snl F_6df8c D_6df8c. snl F_6df90 D_6df90. snl F_6df94 D_6df94.
      stw F_6df98 D_6df98 (Z_to_bv 64 fr) (Z_to_bv 64 obj) ltac:(ok_mdef HD).
      stw F_6df9c D_6df9c (Z_to_bv 64 (fr + 8)) (Z_to_bv 64 5) ltac:(ok_mdef HD).
      stw F_6dfa0 D_6dfa0 (Z_to_bv 64 (fr + 24)) (Z_to_bv 64 1) ltac:(ok_mdef HD).
      stepb_ft F_6dfa4 D_6dfa4 ltac:(cmpz).
      chain_step; [reflexivity | eapply step_divu; [exact F_6dfa8 | reflexivity | exact D_6dfa8 | gres; pin; first [rewrite u64_of_Z by lia; lia | vm_compute; lia]] | step_simpl]; pin; wl.
      snl F_6dfac D_6dfac. snl F_6dfb0 D_6dfb0. snl F_6dfb4 D_6dfb4. snl F_6dfb8 D_6dfb8.
      stw F_6dfbc D_6dfbc (Z_to_bv 64 (fr + 16)) (Z_to_bv 64 5) ltac:(ok_mdef HD).
      stw F_6dfc0 D_6dfc0 (Z_to_bv 64 (fr + 32)) (Z_to_bv 64 1) ltac:(ok_mdef HD).
      stw F_6dfc4 D_6dfc4 (Z_to_bv 64 (fr + 40)) (Z_to_bv 64 0) ltac:(ok_mdef HD).
      stw F_6dfc8 D_6dfc8 (Z_to_bv 64 (fr + 48)) (Z_to_bv 64 0) ltac:(ok_mdef HD).
      stepb_ft F_6dfcc D_6dfcc ltac:(cmpz).
      stepb_tk F_6dfd0 D_6dfd0 ltac:(cmpz).
      snl F_6dfe4 D_6dfe4. snl F_6dfe8 D_6dfe8. snl F_6dfec D_6dfec. snl F_6dff0 D_6dff0. snl F_6dff4 D_6dff4.
      snl F_6dff8 D_6dff8. snl F_6dffc D_6dffc. snl F_6e000 D_6e000. snl F_6e004 D_6e004.
      stw F_6e008 D_6e008 (Z_to_bv 64 (fr + 56)) (Z_to_bv 64 31) ltac:(ok_mdef HD).
      stw F_6e00c D_6e00c (Z_to_bv 64 (fr + 64)) (Z_to_bv 64 63) ltac:(ok_mdef HD).
      stepjr F_6e010 D_6e010 (Z_to_bv 64 ret) ltac:(gres; exact Hra).
      lazymatch goal with |- msteps _ (mkst ?r ?pc ?m _) (mkst ?r' ?pc' ?m' _) =>
        unify r' r; unify m' m; replace pc with pc' by (symmetry; imm_norm; exact Hret) end.
      apply mst_refl.
    - do 8 (eapply stores_in_wbytes_more; [ | lia | rewrite length_N_to_le_bytes; cbn; lia
                                            | intros a Ha; rewrite length_N_to_le_bytes in Ha; cbn in Ha; unfold zwin; lia ]).
      apply stores_in_wbytes; [lia | rewrite length_N_to_le_bytes; cbn; lia | intros a Ha; rewrite length_N_to_le_bytes in Ha; cbn in Ha; unfold zwin; lia].
    - unfold fld. rewrite !rdn_wbytes_out_Z by (rewrite length_N_to_le_bytes; cbn; lia). apply rdn_wbytes_hit8. rewrite u64_of_Z by lia. lia.
    - unfold fld. rewrite rdn_wbytes_out_Z by (rewrite length_N_to_le_bytes; cbn; lia). apply rdn_wbytes_hit8. rewrite u64_of_Z by lia. lia.
    - intros r Hr. rewrite !getr_other by (intros ->; apply Hr; (first [solve [clear; cbv; tauto] | cbv; tauto])). reflexivity.
  Qed.

  Lemma rd_keep : forall W M M' (a : Z) (k : nat) v,
    stores_in W M M' -> 0 <= a -> a + Z.of_nat k < 2 ^ 64 ->
    (forall x, a <= x < a + Z.of_nat k -> ~ W x) ->
    rdn SEGS M (Z_to_bv 64 a) k = Some v -> rdn SEGS M' (Z_to_bv 64 a) k = Some v.
  Proof using.
    intros W M M' a k v SI Ha Hk HW HR. rewrite <- HR. apply rdn_agree_win; [lia|lia|].
    eapply stores_in_agree; [exact SI|]. intros x Hx. unfold zwin in Hx. split; [lia|]. apply HW. lia.
  Qed.

  Lemma UNIF_U : forall R M (obj P sp ret : Z),
    0 <= obj -> obj + 2504 <= 2 ^ 63 -> alloc_ceiling <= obj -> obj mod 8 = 0 -> ro_clear Ly.L M -> mdef M obj 2504 ->
    fld SEGS M (obj + 2496) 8 0 -> fld SEGS M obj 8 5489 -> fld SEGS M (obj + 8) 8 X1 -> fld SEGS M (obj + 1248) 8 X156 ->
    fld SEGS M P 4 0 -> fld SEGS M (P + 4) 4 26 -> 0 <= P -> P + 8 <= 2 ^ 63 ->
    mdef M (sp - 96) 96 -> alloc_ceiling <= sp - 96 -> sp <= 2 ^ 47 ->
    (sp <= P) -> (obj + 2504 <= sp - 96 \/ sp <= obj) -> (P + 8 <= obj \/ obj + 2504 <= P) ->
    getr R 12%bv = Z_to_bv 64 P -> getr R 11%bv = Z_to_bv 64 obj -> getr R 1%bv = Z_to_bv 64 ret -> getr R 2%bv = Z_to_bv 64 sp ->
    ret_ok (Z_to_bv 64 ret) ->
    exists R' M',
      msteps SEGS (@mkst fx R (Z_to_bv 64 0x6dea0) M (seg_rom SEGS)) (@mkst fx R' (Z_to_bv 64 ret) M' (seg_rom SEGS))
      /\ getr R' 10%bv = Z_to_bv 64 6 /\ getr R' 2%bv = Z_to_bv 64 sp
      /\ (forall r, ~ In r [5; 6; 10; 11; 12; 13; 14; 15; 16; 17]%bv -> getr R' r = getr R r)
      /\ stores_in (fun a => zwin (sp - 96) sp a \/ zwin obj (obj + 2504) a) M M'.
  Proof using fx AC.
    intros R M obj P sp ret Ho0 Ho1 Hoc Ho8 ROC HD F2496 F0 F1 F156 FP0 FP4 HP0 HP1 HDW Hspc Hsp47 HPsp DJo DJP Ha2 Ha1 Hra Hsp Hret.
    pose proof ac_bounds_lit as Hcv.
    set (M1 := wslots M sp [getr R 9%bv; getr R 8%bv; Z_to_bv 64 ret]).
    assert (SI1 : stores_in (zwin (sp - 24) sp) M M1).
    { unfold M1. eapply stores_in_weaken; [apply wslots_stores_in; unfold Zlen; cbn; lia|]. intros a Ha. unfold zwin, Zlen in *. cbn in *. lia. }
    unfold fld in F2496, F0, F1, F156, FP0, FP4.
    assert (SL : forall k, 1 <= k <= 3 -> rdn SEGS M1 (Z_to_bv 64 (sp - 8 * k)) 8
              = Some (word_to_le_bytes 8 (nth (Z.to_nat (3 - k)) [getr R 9%bv; getr R 8%bv; Z_to_bv 64 ret] (Z_to_bv 64 0)))).
    { intros k Hk. unfold M1. apply wslots_read; unfold Zlen; cbn; lia. }
    slotv SL 1 SL1. slotv SL 2 SL2. slotv SL 3 SL3. clear SL.

    assert (B1 : exists R1, msteps SEGS (@mkst fx R (Z_to_bv 64 0x6dea0) M (seg_rom SEGS)) (@mkst fx R1 (Z_to_bv 64 0x6dfc8) M1 (seg_rom SEGS))
      /\ getr R1 10%bv = Z_to_bv 64 (sp - 96) /\ getr R1 11%bv = Z_to_bv 64 obj /\ getr R1 12%bv = Z_to_bv 64 5
      /\ getr R1 1%bv = Z_to_bv 64 0x6df74 /\ getr R1 2%bv = Z_to_bv 64 (sp - 96)
      /\ getr R1 8%bv = Z_to_bv 64 P /\ getr R1 9%bv = Z_to_bv 64 27
      /\ (forall r, ~ In r [1; 2; 8; 9; 10; 12; 13]%bv -> getr R1 r = getr R r)).
    { eexists. split.
      - norm_pc.
        sv F_6de60 D_6de60 (Z_to_bv 64 (sp - 96)).
        stw F_6de64 D_6de64 (Z_to_bv 64 (sp - 8)) (Z_to_bv 64 ret) ltac:(ok_mdef HDW).
        stw F_6de68 D_6de68 (Z_to_bv 64 (sp - 16)) (getr R 8%bv) ltac:(ok_mdef HDW).
        stw F_6de6c D_6de6c (Z_to_bv 64 (sp - 24)) (getr R 9%bv) ltac:(ok_mdef HDW).
        sv F_6de70 D_6de70 (Z_to_bv 64 P).
        ld_step F_6de74 D_6de74 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0)
          ltac:(apply (rd_keep _ M M1 P 4%nat _ SI1); [lia | cbn; lia | intros x Hx; unfold zwin; cbn in Hx; lia | rdn_fix FP0]) ltac:(apply lwu_val; lia). wl.
        ld_step F_6de78 D_6de78 (word_to_le_bytes 4 (Z_to_bv 64 26)) (Z_to_bv 64 26)
          ltac:(apply (rd_keep _ M M1 (P + 4) 4%nat _ SI1); [lia | cbn; lia | intros x Hx; unfold zwin; cbn in Hx; lia | rdn_fix FP4]) ltac:(apply lwu_val; lia). wl.
        stepb F_6de7c D_6de7c.
        snl F_6de80 D_6de80. snl F_6de84 D_6de84.
        stepb F_6de88 D_6de88.
        snl F_6de8c D_6de8c. snl F_6de90 D_6de90. snl F_6de94 D_6de94. snl F_6de98 D_6de98.
        snl F_6de9c D_6de9c. snl F_6dea0 D_6dea0. snl F_6dea4 D_6dea4. snl F_6dea8 D_6dea8.
        snl F_6deac D_6deac. snl F_6deb0 D_6deb0. snl F_6deb4 D_6deb4. snl F_6deb8 D_6deb8.
        snl F_6debc D_6debc. snl F_6dec0 D_6dec0. snl F_6dec4 D_6dec4. snl F_6dec8 D_6dec8.
        snl F_6decc D_6decc. snl F_6ded0 D_6ded0. snl F_6ded4 D_6ded4. snl F_6ded8 D_6ded8.
        snl F_6dedc D_6dedc. snl F_6dee0 D_6dee0. snl F_6dee4 D_6dee4. snl F_6dee8 D_6dee8.
        snl F_6deec D_6deec. snl F_6def0 D_6def0. snl F_6def4 D_6def4. snl F_6def8 D_6def8.
        snl F_6defc D_6defc. snl F_6df00 D_6df00. snl F_6df04 D_6df04. snl F_6df08 D_6df08.
        stepb F_6df0c D_6df0c.
        snl F_6df10 D_6df10. snl F_6df14 D_6df14. snl F_6df18 D_6df18. snl F_6df1c D_6df1c.
        snl F_6df20 D_6df20. snl F_6df24 D_6df24. snl F_6df28 D_6df28.
        sv F_6df2c D_6df2c (Z_to_bv 64 (sp - 96)).
        stepj F_6df30 D_6df30.
        fold M1. close_pc.
      - gres. repeat split; try reflexivity; try assumption; try (apply bv_eq; vm_compute; reflexivity).
        intros r Hr. rewrite !getr_other by (intros ->; apply Hr; (first [solve [clear; cbv; tauto] | cbv; tauto])). reflexivity. }
    destruct B1 as (R1 & RUN1 & G10 & G11 & G12 & G1 & G2 & G8 & G9 & GS1).

    destruct (IBE_U R1 M1 (sp - 96) obj 0x6df74 ltac:(lia) ltac:(lia)
                ltac:(eapply stores_in_mdef; [exact SI1|]; eapply mdef_sub; [exact HDW | lia | lia]) ltac:(lia)
                G10 G11 G12 G1 ltac:(unfold ret_ok; apply bv_eq; vm_compute; reflexivity))
      as (R2 & M2 & RUN2 & SI2 & Fe & Fm & GS2).
    unfold fld in Fe, Fm.
    assert (SI12 : stores_in (zwin (sp - 96) sp) M M2).
    { eapply stores_in_trans; [eapply stores_in_weaken; [exact SI1|] | eapply stores_in_weaken; [exact SI2|]]; intros a Ha; unfold zwin in *; lia. }
    assert (HD2 : mdef M2 obj 2504) by (eapply stores_in_mdef; [exact SI12 | exact HD]).
    assert (ROC2 : ro_clear Ly.L M2) by (eapply u1_ro_clear_stores; [exact ROC | exact SI12 | intros a Ha; unfold zwin in Ha; lia]).
    assert (G2_2 : getr R2 2%bv = Z_to_bv 64 (sp - 96)) by (rewrite GS2 by (first [solve [clear; cbv; intuition discriminate] | cbv; intuition discriminate]); exact G2).
    assert (G2_8 : getr R2 8%bv = Z_to_bv 64 P) by (rewrite GS2 by (first [solve [clear; cbv; intuition discriminate] | cbv; intuition discriminate]); exact G8).
    assert (G2_9 : getr R2 9%bv = Z_to_bv 64 27) by (rewrite GS2 by (first [solve [clear; cbv; intuition discriminate] | cbv; intuition discriminate]); exact G9).

    assert (B2 : exists R3, msteps SEGS (@mkst fx R2 (Z_to_bv 64 0x6df74) M2 (seg_rom SEGS)) (@mkst fx R3 (Z_to_bv 64 0x6e058) M2 (seg_rom SEGS))
      /\ getr R3 10%bv = Z_to_bv 64 obj /\ getr R3 1%bv = Z_to_bv 64 0x6df88
      /\ (forall r, ~ In r [1; 10; 11]%bv -> getr R3 r = getr R2 r)).
    { eexists. split.
      - norm_pc.
        ld_step F_6df34 D_6df34 (word_to_le_bytes 8 (Z_to_bv 64 obj)) (Z_to_bv 64 obj) ltac:(rdn_fix Fe) ltac:(b2z8).
        stepb_ft F_6df38 D_6df38 ltac:(rewrite c_eq_Z' by lia; apply Z.eqb_neq; lia).
        stepiv F_6df3c D_6df3c (Z_to_bv 64 0)
          ltac:(gres; pin; imm_norm; rewrite v_andi_Z by lia; f_equal; change 7 with (2 ^ 3 - 1); rewrite land_ones_mod by lia; change (2 ^ 3) with 8; exact Ho8).
        stepb_ft F_6df40 D_6df40 ltac:(apply c_eq_refl).
        stepj F_6df44 D_6df44.
        close_pc.
      - gres. repeat split; try reflexivity.
        intros r Hr. rewrite !getr_other by (intros ->; apply Hr; (first [solve [clear; cbv; tauto] | cbv; tauto])). reflexivity. }
    destruct B2 as (R3 & RUN3 & G3_10 & G3_1 & GS3).

    assert (OBJK : forall a vv, obj <= a -> a + 8 <= obj + 2504 -> rdn SEGS M (Z_to_bv 64 a) 8 = Some vv -> rdn SEGS M2 (Z_to_bv 64 a) 8 = Some vv).
    { intros a vv H1 H2 H3. apply (rd_keep _ M M2 a 8%nat _ SI12); [lia | cbn; lia | intros x Hx; unfold zwin; cbn in Hx; lia | exact H3]. }
    destruct (ENGINE_U R3 M2 obj 0x6df88 Ho0 Ho1 Hoc ROC2 HD2
                ltac:(apply OBJK; [lia | lia | exact F2496]) ltac:(apply OBJK; [lia | lia | exact F0])
                ltac:(apply OBJK; [lia | lia | exact F1]) ltac:(apply OBJK; [lia | lia | exact F156])
                G3_10 G3_1 ltac:(unfold ret_ok; apply bv_eq; vm_compute; reflexivity)) as (R4 & RUN4 & G4_10 & GS4).
    set (M3 := wbytes (wbytes M2 (Z_to_bv 64 obj) (word_to_le_bytes 8 (Z_to_bv 64 NX0))) (Z_to_bv 64 (obj + 2496)) (word_to_le_bytes 8 (Z_to_bv 64 1))) in *.
    assert (SI23 : stores_in (zwin obj (obj + 2504)) M2 M3).
    { unfold M3. eapply stores_in_wbytes_more; [apply stores_in_wbytes | | |]; rewrite ?length_N_to_le_bytes; cbn; try lia; intros a Ha; unfold zwin; lia. }
    assert (SI : stores_in (fun a => zwin (sp - 96) sp a \/ zwin obj (obj + 2504) a) M M3).
    { eapply stores_in_trans; [eapply stores_in_weaken; [exact SI12|]; intros a Ha; left; exact Ha |].
      eapply stores_in_weaken; [exact SI23|]. intros a Ha; right; exact Ha. }
    assert (G4_2 : getr R4 2%bv = Z_to_bv 64 (sp - 96)) by (rewrite GS4, GS3 by (first [solve [clear; cbv; intuition discriminate] | cbv; intuition discriminate]); exact G2_2).
    assert (G4_8 : getr R4 8%bv = Z_to_bv 64 P) by (rewrite GS4, GS3 by (first [solve [clear; cbv; intuition discriminate] | cbv; intuition discriminate]); exact G2_8).
    assert (G4_9 : getr R4 9%bv = Z_to_bv 64 27) by (rewrite GS4, GS3 by (first [solve [clear; cbv; intuition discriminate] | cbv; intuition discriminate]); exact G2_9).
    assert (FRK : forall a vv, sp - 96 <= a -> a + 8 <= sp -> rdn SEGS M2 (Z_to_bv 64 a) 8 = Some vv -> rdn SEGS M3 (Z_to_bv 64 a) 8 = Some vv).
    { intros a vv H1 H2 H3. apply (rd_keep _ M2 M3 a 8%nat _ SI23); [lia | cbn; lia | intros x Hx; unfold zwin; cbn in Hx; lia | exact H3]. }
    assert (Fm' : rdn SEGS M3 (Z_to_bv 64 (sp - 96 + 56)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 31))) by (apply FRK; [lia | lia | exact Fm]).
    assert (SLK : forall a vv, sp - 24 <= a -> a + 8 <= sp -> rdn SEGS M1 (Z_to_bv 64 a) 8 = Some vv -> rdn SEGS M3 (Z_to_bv 64 a) 8 = Some vv).
    { intros a vv H1 H2 H3. apply FRK; [lia | lia |]. apply (rd_keep _ M1 M2 a 8%nat _ SI2); [lia | cbn; lia | intros x Hx; unfold zwin; cbn in Hx; lia | exact H3]. }
    assert (FP0' : rdn SEGS M3 (Z_to_bv 64 P) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0))).
    { apply (rd_keep _ M M3 P 4%nat _ SI); [lia | cbn; lia | intros x Hx [Hw|Hw]; unfold zwin in Hw; cbn in Hx; lia | exact FP0]. }
    eexists. exists M3. split; [|split; [|split; [|split]]].
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|]. eapply msteps_trans; [exact RUN4|]. norm_pc.
      ld_step F_6df48 D_6df48 (word_to_le_bytes 8 (Z_to_bv 64 31)) (Z_to_bv 64 31) ltac:(rdn_fix Fm') ltac:(b2z8). wl.
      snl F_6df4c D_6df4c. snl F_6df50 D_6df50.
      stepb_ft F_6df54 D_6df54 ltac:(rewrite G4_9; vm_compute; reflexivity).
      ld_step F_6df58 D_6df58 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(rdn_fix FP0') ltac:(apply lwu_val; lia). wl.
      snl F_6df5c D_6df5c.
      stepj F_6df60 D_6df60.
      snl F_6df6c D_6df6c.
      ld_step F_6df70 D_6df70 (word_to_le_bytes 8 (Z_to_bv 64 ret)) (Z_to_bv 64 ret) ltac:(apply SLK; [lia|lia| rdn_fix SL1]) ltac:(b2z8).
      ld_step F_6df74 D_6df74 (word_to_le_bytes 8 (getr R 8%bv)) (getr R 8%bv) ltac:(apply SLK; [lia|lia| rdn_fix SL2]) ltac:(b2z8).
      ld_step F_6df78 D_6df78 (word_to_le_bytes 8 (getr R 9%bv)) (getr R 9%bv) ltac:(apply SLK; [lia|lia| rdn_fix SL3]) ltac:(b2z8).
      sv F_6df7c D_6df7c (Z_to_bv 64 sp).
      stepjr F_6df80 D_6df80 (Z_to_bv 64 ret) ltac:(gres; reflexivity).
      lazymatch goal with |- msteps _ (mkst ?r ?pc ?m _) (mkst ?r' ?pc' ?m' _) =>
        unify r' r; replace pc with pc' by (symmetry; imm_norm; exact Hret) end.
      apply mst_refl.
    - gres. apply bv_eq. vm_compute. reflexivity.
    - gres. reflexivity.
    - intros r Hr.
      destruct (bv_eq_dec _ r 2%bv) as [->|N2]; [gres; symmetry; exact Hsp|].
      destruct (bv_eq_dec _ r 1%bv) as [->|N1]; [gres; symmetry; exact Hra|].
      destruct (bv_eq_dec _ r 8%bv) as [->|N8]; [gres; reflexivity|].
      destruct (bv_eq_dec _ r 9%bv) as [->|N9]; [gres; reflexivity|].
      repeat (rewrite getr_other; [| first [assumption | intros ->; apply Hr; (first [solve [clear; cbv; tauto] | cbv; tauto])]]).
      rewrite GS4 by (intros HH; apply Hr; revert HH; (first [solve [clear; cbv; tauto] | cbv; tauto])).
      rewrite GS3 by (cbv; intros HH; decompose [or] HH; subst; try contradiction; apply Hr; (first [solve [clear; cbv; tauto] | cbv; tauto])).
      rewrite GS2 by (cbv; intros HH; decompose [or] HH; subst; try contradiction; apply Hr; (first [solve [clear; cbv; tauto] | cbv; tauto])).
      apply GS1. cbv. intros HH; decompose [or] HH; clear HH; subst; try contradiction; apply Hr; (first [solve [clear; cbv; tauto] | cbv; tauto]).
    - exact SI.
  Qed.
End GTEU.

Theorem rg_gettargetenv_6dd8c_spec {AC : AllocCeiling} : rg_gettargetenv_stmt SEGS Ly.L uRG.
Proof.
  intros fx M R sp ret obj. cbn [rc_gettargetenv rc_gte_stack uRG]. lazy zeta.
  intros ROC Ho0 Ho1 SEEDED DJ HROOM Hspc Hsp47 Hsp16 Hoc Ho8 Hret Hra Hsp Ha0.
  pose proof ac_bounds_lit as Hcv. unfold RG_SZ in *.
  destruct SEEDED as (HD & FJ & FI). unfold MT_N in FJ, FI.
  assert (DJo : obj + 2504 <= sp - 144 \/ sp <= obj).
  { destruct (Z.lt_ge_cases obj sp); [left|right; lia].
    destruct (Z.lt_ge_cases (obj + 2504) (sp - 144 + 1)); [lia|]. exfalso.
    destruct (Z.lt_ge_cases obj (sp - 144)).
    - apply (DJ (sp - 144)); unfold zwin; lia.
    - apply (DJ obj); unfold zwin; lia. }
  clear DJ.
  assert (HDW : mdef M (sp - 144) 144).
  { unfold stack_room in HROOM. eapply store_ok_mdef_offimg; [exact HROOM | lia | lia | lia |]. intros w Hw. apply ly_noseg. lia. }
  set (Mg0 := wslots M sp [getr R 19%bv; getr R 18%bv; getr R 9%bv; getr R 8%bv; Z_to_bv 64 ret]).
  set (Mg := wbytes (wbytes Mg0 (Z_to_bv 64 (sp - 48)) (word_to_le_bytes 4 (Z_to_bv 64 0))) (Z_to_bv 64 (sp - 44)) (word_to_le_bytes 4 (Z_to_bv 64 26))).
  assert (SIg : stores_in (zwin (sp - 48) sp) M Mg).
  { unfold Mg, Mg0. eapply stores_in_wbytes_more; [eapply stores_in_wbytes_more; [eapply stores_in_weaken; [apply wslots_stores_in; unfold Zlen; cbn; lia|] | | |] | | |];
      rewrite ?length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ length]; unfold Zlen; cbn; try lia; intros a Ha; unfold zwin in *; lia. }
  assert (AGg : forall a (k : nat) v, (a + Z.of_nat k <= sp - 48 \/ sp <= a) -> 0 <= a -> a + Z.of_nat k < 2 ^ 64 ->
            rdn SEGS M (Z_to_bv 64 a) k = Some v -> rdn SEGS Mg (Z_to_bv 64 a) k = Some v).
  { intros a k v H1 H2 H3 H4. rewrite <- H4. apply rdn_agree_win; [lia|lia|]. eapply stores_in_agree; [exact SIg|].
    intros x Hx. unfold zwin in *. lia. }
  assert (SL : forall k, 1 <= k <= 5 -> rdn SEGS Mg0 (Z_to_bv 64 (sp - 8 * k)) 8
            = Some (word_to_le_bytes 8 (nth (Z.to_nat (5 - k)) [getr R 19%bv; getr R 18%bv; getr R 9%bv; getr R 8%bv; Z_to_bv 64 ret] (Z_to_bv 64 0)))).
  { intros k Hk. unfold Mg0. apply wslots_read; unfold Zlen; cbn; lia. }
  slotv SL 1 SL1. slotv SL 2 SL2. slotv SL 3 SL3. slotv SL 4 SL4. slotv SL 5 SL5. clear SL.

  set (R1 := regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd R
              2%bv (Z_to_bv 64 (sp - 48))) 8%bv (Z_to_bv 64 obj)) 18%bv (Z_to_bv 64 26)) 19%bv (Z_to_bv 64 32))
              10%bv (Z_to_bv 64 (sp - 48))) 12%bv (Z_to_bv 64 (sp - 48))) 11%bv (Z_to_bv 64 obj)) 1%bv (Z_to_bv 64 0x6de6c)).
  assert (RUN1 : msteps SEGS (@mkst fx R (Z_to_bv 64 0x6de30) M (seg_rom SEGS)) (@mkst fx R1 (Z_to_bv 64 0x6dea0) Mg (seg_rom SEGS))).
  { unfold R1. norm_pc.
    sv F_6ddf0 D_6ddf0 (Z_to_bv 64 (sp - 48)).
    stw F_6ddf4 D_6ddf4 (Z_to_bv 64 (sp - 8)) (Z_to_bv 64 ret) ltac:(ok_mdef HDW).
    stw F_6ddf8 D_6ddf8 (Z_to_bv 64 (sp - 16)) (getr R 8%bv) ltac:(ok_mdef HDW).
    stw F_6ddfc D_6ddfc (Z_to_bv 64 (sp - 24)) (getr R 9%bv) ltac:(ok_mdef HDW).
    stw F_6de00 D_6de00 (Z_to_bv 64 (sp - 32)) (getr R 18%bv) ltac:(ok_mdef HDW).
    stw F_6de04 D_6de04 (Z_to_bv 64 (sp - 40)) (getr R 19%bv) ltac:(ok_mdef HDW).
    sv F_6de08 D_6de08 (Z_to_bv 64 obj).
    sv F_6de0c D_6de0c (Z_to_bv 64 26).
    sv F_6de10 D_6de10 (Z_to_bv 64 32).
    stw F_6de14 D_6de14 (Z_to_bv 64 (sp - 48)) (Z_to_bv 64 0) ltac:(ok_mdef HDW).
    stw F_6de18 D_6de18 (Z_to_bv 64 (sp - 44)) (Z_to_bv 64 26) ltac:(ok_mdef HDW).
    sv F_6de1c D_6de1c (Z_to_bv 64 (sp - 48)).
    sv F_6de20 D_6de20 (Z_to_bv 64 (sp - 48)).
    sv F_6de24 D_6de24 (Z_to_bv 64 obj).
    stepj F_6de28 D_6de28.
    lazymatch goal with |- msteps _ (mkst ?r ?pc ?m _) (mkst ?r' ?pc' ?m' _) =>
      change m with m'; replace pc with pc' by (apply bv_eq; vm_compute; reflexivity) end. apply mst_refl. }
  destruct (UNIF_U R1 Mg obj (sp - 48) (sp - 48) 0x6de6c Ho0 ltac:(lia) Hoc Ho8
              ltac:(eapply u1_ro_clear_stores; [exact ROC | exact SIg | intros a Ha; unfold zwin in Ha; lia])
              ltac:(eapply stores_in_mdef; [exact SIg | exact HD])
              ltac:(apply (AGg (obj + 2496) 8%nat); [cbn; lia | lia | cbn; lia | exact FI])
              ltac:(apply (AGg obj 8%nat); [cbn; lia | lia | cbn; lia | pose proof (FJ 0 ltac:(lia)) as X; rewrite mt_init_0, Z.mul_0_r, Z.add_0_r in X; exact X])
              ltac:(apply (AGg (obj + 8) 8%nat); [cbn; lia | lia | cbn; lia | pose proof (FJ 1 ltac:(lia)) as X; rewrite mt_init_1 in X; exact X])
              ltac:(apply (AGg (obj + 1248) 8%nat); [cbn; lia | lia | cbn; lia | pose proof (FJ 156 ltac:(lia)) as X; rewrite mt_init_156 in X; exact X])
              ltac:(unfold fld, Mg; rewrite rdn_wbytes_out_Z by (rewrite length_N_to_le_bytes; cbn; lia); apply rdn_wbytes_hit4; rewrite u64_of_Z by lia; lia)
              ltac:(unfold fld, Mg; replace (sp - 48 + 4) with (sp - 44) by lia; apply rdn_wbytes_hit4; rewrite u64_of_Z by lia; lia)
              ltac:(lia) ltac:(lia)
              ltac:(replace (sp - 48 - 96) with (sp - 144) by lia; eapply stores_in_mdef; [exact SIg|]; eapply mdef_sub; [exact HDW | lia | lia])
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(unfold R1; gres; reflexivity) ltac:(unfold R1; gres; reflexivity) ltac:(unfold R1; gres; reflexivity) ltac:(unfold R1; gres; reflexivity)
              ltac:(unfold ret_ok; apply bv_eq; vm_compute; reflexivity))
    as (R3 & Mu & RUN3 & G3_10 & G3_2 & GS3 & SIu).
  assert (SLT : forall a vv, sp - 40 <= a -> a + 8 <= sp -> rdn SEGS Mg0 (Z_to_bv 64 a) 8 = Some vv -> rdn SEGS Mu (Z_to_bv 64 a) 8 = Some vv).
  { intros a vv H1 H2 H3. rewrite <- H3.
    transitivity (rdn SEGS Mg (Z_to_bv 64 a) 8).
    - apply rdn_agree_win; [lia | cbn; lia |]. eapply stores_in_agree; [exact SIu|]. intros x Hx. unfold zwin in *. cbn in Hx. lia.
    - unfold Mg. rewrite !rdn_wbytes_out_Z by (rewrite length_N_to_le_bytes; cbn; lia). reflexivity. }
  assert (G3_19 : getr R3 19%bv = Z_to_bv 64 32) by (rewrite GS3 by (first [solve [clear; cbv; intuition discriminate] | cbv; intuition discriminate]); unfold R1; gres; reflexivity).
  assert (SI : stores_in (fun a => zwin obj (obj + 2504) a \/ zwin (sp - 144) sp a) M Mu).
  { eapply stores_in_trans; [eapply stores_in_weaken; [exact SIg|]; intros a Ha; right; unfold zwin in *; lia |].
    eapply stores_in_weaken; [exact SIu|]. intros a [Ha|Ha]; [right; unfold zwin in *; lia | left; exact Ha]. }
  eexists. exists Mu. split; [|split; [|split; [|split; [|split; [|split]]]]].
  - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN3|]. norm_pc.
    stepb_ft F_6de2c D_6de2c ltac:(rewrite G3_10, G3_19; vm_compute; reflexivity).
    snl F_6de30 D_6de30.
    stepj F_6de34 D_6de34.
    snl F_6d098 D_6d098.
    stepb_ft F_6d09c D_6d09c ltac:(pin; vm_compute; reflexivity).
    snl F_6d0a0 D_6d0a0. snl F_6d0a4 D_6d0a4. snl F_6d0a8 D_6d0a8. snl F_6d0ac D_6d0ac. snl F_6d0b0 D_6d0b0.
    stepjr F_6d0b4 D_6d0b4 (Z_to_bv 64 0x6de78) ltac:(gres; reflexivity).
    stepb_ft F_6de38 D_6de38 ltac:(vm_compute; reflexivity).
    snl F_6de3c D_6de3c.
    ld_step F_6de40 D_6de40 (word_to_le_bytes 8 (Z_to_bv 64 ret)) (Z_to_bv 64 ret) ltac:(apply SLT; [lia|lia|rdn_fix SL1]) ltac:(b2z8).
    ld_step F_6de44 D_6de44 (word_to_le_bytes 8 (getr R 8%bv)) (getr R 8%bv) ltac:(apply SLT; [lia|lia|rdn_fix SL2]) ltac:(b2z8).
    ld_step F_6de48 D_6de48 (word_to_le_bytes 8 (getr R 9%bv)) (getr R 9%bv) ltac:(apply SLT; [lia|lia|rdn_fix SL3]) ltac:(b2z8).
    ld_step F_6de4c D_6de4c (word_to_le_bytes 8 (getr R 18%bv)) (getr R 18%bv) ltac:(apply SLT; [lia|lia|rdn_fix SL4]) ltac:(b2z8).
    ld_step F_6de50 D_6de50 (word_to_le_bytes 8 (getr R 19%bv)) (getr R 19%bv) ltac:(apply SLT; [lia|lia|rdn_fix SL5]) ltac:(b2z8).
    sv F_6de54 D_6de54 (Z_to_bv 64 sp).
    stepjr F_6de58 D_6de58 (Z_to_bv 64 ret) ltac:(gres; reflexivity).
    lazymatch goal with |- msteps _ (mkst ?r ?pc ?m _) (mkst ?r' ?pc' ?m' _) =>
      unify r' r; replace pc with pc' by (symmetry; imm_norm; exact Hret) end. apply mst_refl.
  - intros r Hr. unfold callee_saved in Hr.
    destruct (bv_eq_dec _ r 1%bv) as [->|N1]; [gres; symmetry; exact Hra|].
    destruct (bv_eq_dec _ r 2%bv) as [->|N2]; [gres; symmetry; exact Hsp|].
    destruct (bv_eq_dec _ r 8%bv) as [->|N8]; [gres; reflexivity|].
    destruct (bv_eq_dec _ r 9%bv) as [->|N9]; [gres; reflexivity|].
    destruct (bv_eq_dec _ r 18%bv) as [->|N18]; [gres; reflexivity|].
    destruct (bv_eq_dec _ r 19%bv) as [->|N19]; [gres; reflexivity|].
    repeat (rewrite getr_other; [| first [assumption | intros ->; cbv in Hr; intuition discriminate]]).
    rewrite GS3 by (cbv; intros HH; decompose [or] HH; clear HH; subst; cbv in Hr; intuition discriminate).
    unfold R1. repeat (rewrite getr_other; [| first [assumption | intros ->; cbv in Hr; intuition discriminate]]). reflexivity.
  - gres. apply bv_eq. vm_compute. reflexivity.
  - eapply stores_in_mdef; [exact SI | exact HD].
  - eapply stores_in_frame_eq; [exact SI|]. intros a Ha; exact Ha.
  - exact (proj2 SI).
  - eapply u1_ro_clear_stores; [exact ROC | exact SI |]. intros a [Ha|Ha]; unfold zwin in Ha; lia.
Qed.
