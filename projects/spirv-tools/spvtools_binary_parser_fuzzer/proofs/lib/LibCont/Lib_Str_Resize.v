(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Plain.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StepTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.WalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StartupTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SumWalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MemSplit OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ShapeAlg OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SRealizes OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefReadLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibEff OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MmapSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SumMemsetLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SumMemset OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibMaskBits OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.S1Layout.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.CRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.StrLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.S1Facts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.Lib_Str_PushBack.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Module S1_code_8b58c_8b764.

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_8b58c : bv 32 := 0xfb010113.
Lemma F_8b58c : fetch_word Plain.M.loaded_segments (0x8b5cc : word) = Some W_8b58c.
Proof. vm_refl. Qed.
Lemma D_8b58c : decode_any W_8b58c = Some (OpImm ALU_ADD 2 2 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b590 : bv 32 := 0x04113423.
Lemma F_8b590 : fetch_word Plain.M.loaded_segments (0x8b5d0 : word) = Some W_8b590.
Proof. vm_refl. Qed.
Lemma D_8b590 : decode_any W_8b590 = Some (Store SZ8 2 1 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b594 : bv 32 := 0x04813023.
Lemma F_8b594 : fetch_word Plain.M.loaded_segments (0x8b5d4 : word) = Some W_8b594.
Proof. vm_refl. Qed.
Lemma D_8b594 : decode_any W_8b594 = Some (Store SZ8 2 8 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b598 : bv 32 := 0x02913c23.
Lemma F_8b598 : fetch_word Plain.M.loaded_segments (0x8b5d8 : word) = Some W_8b598.
Proof. vm_refl. Qed.
Lemma D_8b598 : decode_any W_8b598 = Some (Store SZ8 2 9 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b59c : bv 32 := 0x03213823.
Lemma F_8b59c : fetch_word Plain.M.loaded_segments (0x8b5dc : word) = Some W_8b59c.
Proof. vm_refl. Qed.
Lemma D_8b59c : decode_any W_8b59c = Some (Store SZ8 2 18 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b5a0 : bv 32 := 0x03313423.
Lemma F_8b5a0 : fetch_word Plain.M.loaded_segments (0x8b5e0 : word) = Some W_8b5a0.
Proof. vm_refl. Qed.
Lemma D_8b5a0 : decode_any W_8b5a0 = Some (Store SZ8 2 19 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b5a4 : bv 32 := 0x03413023.
Lemma F_8b5a4 : fetch_word Plain.M.loaded_segments (0x8b5e4 : word) = Some W_8b5a4.
Proof. vm_refl. Qed.
Lemma D_8b5a4 : decode_any W_8b5a4 = Some (Store SZ8 2 20 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b5a8 : bv 32 := 0x01513c23.
Lemma F_8b5a8 : fetch_word Plain.M.loaded_segments (0x8b5e8 : word) = Some W_8b5a8.
Proof. vm_refl. Qed.
Lemma D_8b5a8 : decode_any W_8b5a8 = Some (Store SZ8 2 21 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b5ac : bv 32 := 0x01613823.
Lemma F_8b5ac : fetch_word Plain.M.loaded_segments (0x8b5ec : word) = Some W_8b5ac.
Proof. vm_refl. Qed.
Lemma D_8b5ac : decode_any W_8b5ac = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b5b0 : bv 32 := 0x01713423.
Lemma F_8b5b0 : fetch_word Plain.M.loaded_segments (0x8b5f0 : word) = Some W_8b5b0.
Proof. vm_refl. Qed.
Lemma D_8b5b0 : decode_any W_8b5b0 = Some (Store SZ8 2 23 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b5b4 : bv 32 := 0x01813023.
Lemma F_8b5b4 : fetch_word Plain.M.loaded_segments (0x8b5f4 : word) = Some W_8b5b4.
Proof. vm_refl. Qed.
Lemma D_8b5b4 : decode_any W_8b5b4 = Some (Store SZ8 2 24 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b5b8 : bv 32 := 0x00050413.
Lemma F_8b5b8 : fetch_word Plain.M.loaded_segments (0x8b5f8 : word) = Some W_8b5b8.
Proof. vm_refl. Qed.
Lemma D_8b5b8 : decode_any W_8b5b8 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b5bc : bv 32 := 0x16058863.
Lemma F_8b5bc : fetch_word Plain.M.loaded_segments (0x8b5fc : word) = Some W_8b5bc.
Proof. vm_refl. Qed.
Lemma D_8b5bc : decode_any W_8b5bc = Some (Branch BC_EQ 11 0 368, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b5c0 : bv 32 := 0x00058493.
Lemma F_8b5c0 : fetch_word Plain.M.loaded_segments (0x8b600 : word) = Some W_8b5c0.
Proof. vm_refl. Qed.
Lemma D_8b5c0 : decode_any W_8b5c0 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b5c4 : bv 32 := 0x00044503.
Lemma F_8b5c4 : fetch_word Plain.M.loaded_segments (0x8b604 : word) = Some W_8b5c4.
Proof. vm_refl. Qed.
Lemma D_8b5c4 : decode_any W_8b5c4 = Some (Load SZ1 false 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b5c8 : bv 32 := 0x00043583.
Lemma F_8b5c8 : fetch_word Plain.M.loaded_segments (0x8b608 : word) = Some W_8b5c8.
Proof. vm_refl. Qed.
Lemma D_8b5c8 : decode_any W_8b5c8 = Some (Load SZ8 true 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b5cc : bv 32 := 0x00157513.
Lemma F_8b5cc : fetch_word Plain.M.loaded_segments (0x8b60c : word) = Some W_8b5cc.
Proof. vm_refl. Qed.
Lemma D_8b5cc : decode_any W_8b5cc = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b5d0 : bv 32 := 0x02051663.
Lemma F_8b5d0 : fetch_word Plain.M.loaded_segments (0x8b610 : word) = Some W_8b5d0.
Proof. vm_refl. Qed.
Lemma D_8b5d0 : decode_any W_8b5d0 = Some (Branch BC_NE 10 0 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b5d4 : bv 32 := 0x01600b93.
Lemma F_8b5d4 : fetch_word Plain.M.loaded_segments (0x8b614 : word) = Some W_8b5d4.
Proof. vm_refl. Qed.
Lemma D_8b5d4 : decode_any W_8b5d4 = Some (OpImm ALU_ADD 23 0 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b5d8 : bv 32 := 0x0015f513.
Lemma F_8b5d8 : fetch_word Plain.M.loaded_segments (0x8b618 : word) = Some W_8b5d8.
Proof. vm_refl. Qed.
Lemma D_8b5d8 : decode_any W_8b5d8 = Some (OpImm ALU_AND 10 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b5dc : bv 32 := 0x02051863.
Lemma F_8b5dc : fetch_word Plain.M.loaded_segments (0x8b61c : word) = Some W_8b5dc.
Proof. vm_refl. Qed.
Lemma D_8b5dc : decode_any W_8b5dc = Some (Branch BC_NE 10 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b5e0 : bv 32 := 0x03859593.
Lemma F_8b5e0 : fetch_word Plain.M.loaded_segments (0x8b620 : word) = Some W_8b5e0.
Proof. vm_refl. Qed.
Lemma D_8b5e0 : decode_any W_8b5e0 = Some (ShiftImm ALU_SLL 11 11 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b5e4 : bv 32 := 0x0395d913.
Lemma F_8b5e4 : fetch_word Plain.M.loaded_segments (0x8b624 : word) = Some W_8b5e4.
Proof. vm_refl. Qed.
Lemma D_8b5e4 : decode_any W_8b5e4 = Some (ShiftImm ALU_SRL 18 11 57, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b5e8 : bv 32 := 0x412b85b3.
Lemma F_8b5e8 : fetch_word Plain.M.loaded_segments (0x8b628 : word) = Some W_8b5e8.
Proof. vm_refl. Qed.
Lemma D_8b5e8 : decode_any W_8b5e8 = Some (Op ALU_SUB 11 23 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b5ec : bv 32 := 0x0295e663.
Lemma F_8b5ec : fetch_word Plain.M.loaded_segments (0x8b62c : word) = Some W_8b5ec.
Proof. vm_refl. Qed.
Lemma D_8b5ec : decode_any W_8b5ec = Some (Branch BC_LTU 11 9 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b5f0 : bv 32 := 0x06050663.
Lemma F_8b5f0 : fetch_word Plain.M.loaded_segments (0x8b630 : word) = Some W_8b5f0.
Proof. vm_refl. Qed.
Lemma D_8b5f0 : decode_any W_8b5f0 = Some (Branch BC_EQ 10 0 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b5f4 : bv 32 := 0x01043a03.
Lemma F_8b5f4 : fetch_word Plain.M.loaded_segments (0x8b634 : word) = Some W_8b5f4.
Proof. vm_refl. Qed.
Lemma D_8b5f4 : decode_any W_8b5f4 = Some (Load SZ8 true 20 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b5f8 : bv 32 := 0x0680006f.
Lemma F_8b5f8 : fetch_word Plain.M.loaded_segments (0x8b638 : word) = Some W_8b5f8.
Proof. vm_refl. Qed.
Lemma D_8b5f8 : decode_any W_8b5f8 = Some (Jal 0 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b5fc : bv 32 := 0xffe5fb93.
Lemma F_8b5fc : fetch_word Plain.M.loaded_segments (0x8b63c : word) = Some W_8b5fc.
Proof. vm_refl. Qed.
Lemma D_8b5fc : decode_any W_8b5fc = Some (OpImm ALU_AND 23 11 4094, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b600 : bv 32 := 0xfffb8b93.
Lemma F_8b600 : fetch_word Plain.M.loaded_segments (0x8b640 : word) = Some W_8b600.
Proof. vm_refl. Qed.
Lemma D_8b600 : decode_any W_8b600 = Some (OpImm ALU_ADD 23 23 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b604 : bv 32 := 0x0015f513.
Lemma F_8b604 : fetch_word Plain.M.loaded_segments (0x8b644 : word) = Some W_8b604.
Proof. vm_refl. Qed.
Lemma D_8b604 : decode_any W_8b604 = Some (OpImm ALU_AND 10 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b608 : bv 32 := 0xfc050ce3.
Lemma F_8b608 : fetch_word Plain.M.loaded_segments (0x8b648 : word) = Some W_8b608.
Proof. vm_refl. Qed.
Lemma D_8b608 : decode_any W_8b608 = Some (Branch BC_EQ 10 0 8152, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b60c : bv 32 := 0x00843903.
Lemma F_8b60c : fetch_word Plain.M.loaded_segments (0x8b64c : word) = Some W_8b60c.
Proof. vm_refl. Qed.
Lemma D_8b60c : decode_any W_8b60c = Some (Load SZ8 true 18 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b610 : bv 32 := 0x412b85b3.
Lemma F_8b610 : fetch_word Plain.M.loaded_segments (0x8b650 : word) = Some W_8b610.
Proof. vm_refl. Qed.
Lemma D_8b610 : decode_any W_8b610 = Some (Op ALU_SUB 11 23 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b614 : bv 32 := 0xfc95fee3.
Lemma F_8b614 : fetch_word Plain.M.loaded_segments (0x8b654 : word) = Some W_8b614.
Proof. vm_refl. Qed.
Lemma D_8b614 : decode_any W_8b614 = Some (Branch BC_GEU 11 9 8156, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b65c : bv 32 := 0x00140a13.
Lemma F_8b65c : fetch_word Plain.M.loaded_segments (0x8b69c : word) = Some W_8b65c.
Proof. vm_refl. Qed.
Lemma D_8b65c : decode_any W_8b65c = Some (OpImm ALU_ADD 20 8 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b660 : bv 32 := 0x00990b33.
Lemma F_8b660 : fetch_word Plain.M.loaded_segments (0x8b6a0 : word) = Some W_8b660.
Proof. vm_refl. Qed.
Lemma D_8b660 : decode_any W_8b660 = Some (Op ALU_ADD 22 18 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b664 : bv 32 := 0x0940006f.
Lemma F_8b664 : fetch_word Plain.M.loaded_segments (0x8b6a4 : word) = Some W_8b664.
Proof. vm_refl. Qed.
Lemma D_8b664 : decode_any W_8b664 = Some (Jal 0 148, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b6f8 : bv 32 := 0x012a0533.
Lemma F_8b6f8 : fetch_word Plain.M.loaded_segments (0x8b738 : word) = Some W_8b6f8.
Proof. vm_refl. Qed.
Lemma D_8b6f8 : decode_any W_8b6f8 = Some (Op ALU_ADD 10 20 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b6fc : bv 32 := 0x00060593.
Lemma F_8b6fc : fetch_word Plain.M.loaded_segments (0x8b73c : word) = Some W_8b6fc.
Proof. vm_refl. Qed.
Lemma D_8b6fc : decode_any W_8b6fc = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b700 : bv 32 := 0x00048613.
Lemma F_8b700 : fetch_word Plain.M.loaded_segments (0x8b740 : word) = Some W_8b700.
Proof. vm_refl. Qed.
Lemma D_8b700 : decode_any W_8b700 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b704 : bv 32 := 0x481550ef.
Lemma F_8b704 : fetch_word Plain.M.loaded_segments (0x8b744 : word) = Some W_8b704.
Proof. vm_refl. Qed.
Lemma D_8b704 : decode_any W_8b704 = Some (Jal 1 351360, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b708 : bv 32 := 0x00044503.
Lemma F_8b708 : fetch_word Plain.M.loaded_segments (0x8b748 : word) = Some W_8b708.
Proof. vm_refl. Qed.
Lemma D_8b708 : decode_any W_8b708 = Some (Load SZ1 false 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b70c : bv 32 := 0x00157513.
Lemma F_8b70c : fetch_word Plain.M.loaded_segments (0x8b74c : word) = Some W_8b70c.
Proof. vm_refl. Qed.
Lemma D_8b70c : decode_any W_8b70c = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b710 : bv 32 := 0x00051863.
Lemma F_8b710 : fetch_word Plain.M.loaded_segments (0x8b750 : word) = Some W_8b710.
Proof. vm_refl. Qed.
Lemma D_8b710 : decode_any W_8b710 = Some (Branch BC_NE 10 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b714 : bv 32 := 0x001b1513.
Lemma F_8b714 : fetch_word Plain.M.loaded_segments (0x8b754 : word) = Some W_8b714.
Proof. vm_refl. Qed.
Lemma D_8b714 : decode_any W_8b714 = Some (ShiftImm ALU_SLL 10 22 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b718 : bv 32 := 0x00a40023.
Lemma F_8b718 : fetch_word Plain.M.loaded_segments (0x8b758 : word) = Some W_8b718.
Proof. vm_refl. Qed.
Lemma D_8b718 : decode_any W_8b718 = Some (Store SZ1 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b71c : bv 32 := 0x0080006f.
Lemma F_8b71c : fetch_word Plain.M.loaded_segments (0x8b75c : word) = Some W_8b71c.
Proof. vm_refl. Qed.
Lemma D_8b71c : decode_any W_8b71c = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b720 : bv 32 := 0x01643423.
Lemma F_8b720 : fetch_word Plain.M.loaded_segments (0x8b760 : word) = Some W_8b720.
Proof. vm_refl. Qed.
Lemma D_8b720 : decode_any W_8b720 = Some (Store SZ8 8 22 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b724 : bv 32 := 0x016a0a33.
Lemma F_8b724 : fetch_word Plain.M.loaded_segments (0x8b764 : word) = Some W_8b724.
Proof. vm_refl. Qed.
Lemma D_8b724 : decode_any W_8b724 = Some (Op ALU_ADD 20 20 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b728 : bv 32 := 0x000a0023.
Lemma F_8b728 : fetch_word Plain.M.loaded_segments (0x8b768 : word) = Some W_8b728.
Proof. vm_refl. Qed.
Lemma D_8b728 : decode_any W_8b728 = Some (Store SZ1 20 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b72c : bv 32 := 0x00040513.
Lemma F_8b72c : fetch_word Plain.M.loaded_segments (0x8b76c : word) = Some W_8b72c.
Proof. vm_refl. Qed.
Lemma D_8b72c : decode_any W_8b72c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b730 : bv 32 := 0x04813083.
Lemma F_8b730 : fetch_word Plain.M.loaded_segments (0x8b770 : word) = Some W_8b730.
Proof. vm_refl. Qed.
Lemma D_8b730 : decode_any W_8b730 = Some (Load SZ8 true 1 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b734 : bv 32 := 0x04013403.
Lemma F_8b734 : fetch_word Plain.M.loaded_segments (0x8b774 : word) = Some W_8b734.
Proof. vm_refl. Qed.
Lemma D_8b734 : decode_any W_8b734 = Some (Load SZ8 true 8 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b738 : bv 32 := 0x03813483.
Lemma F_8b738 : fetch_word Plain.M.loaded_segments (0x8b778 : word) = Some W_8b738.
Proof. vm_refl. Qed.
Lemma D_8b738 : decode_any W_8b738 = Some (Load SZ8 true 9 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b73c : bv 32 := 0x03013903.
Lemma F_8b73c : fetch_word Plain.M.loaded_segments (0x8b77c : word) = Some W_8b73c.
Proof. vm_refl. Qed.
Lemma D_8b73c : decode_any W_8b73c = Some (Load SZ8 true 18 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b740 : bv 32 := 0x02813983.
Lemma F_8b740 : fetch_word Plain.M.loaded_segments (0x8b780 : word) = Some W_8b740.
Proof. vm_refl. Qed.
Lemma D_8b740 : decode_any W_8b740 = Some (Load SZ8 true 19 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b744 : bv 32 := 0x02013a03.
Lemma F_8b744 : fetch_word Plain.M.loaded_segments (0x8b784 : word) = Some W_8b744.
Proof. vm_refl. Qed.
Lemma D_8b744 : decode_any W_8b744 = Some (Load SZ8 true 20 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b748 : bv 32 := 0x01813a83.
Lemma F_8b748 : fetch_word Plain.M.loaded_segments (0x8b788 : word) = Some W_8b748.
Proof. vm_refl. Qed.
Lemma D_8b748 : decode_any W_8b748 = Some (Load SZ8 true 21 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b74c : bv 32 := 0x01013b03.
Lemma F_8b74c : fetch_word Plain.M.loaded_segments (0x8b78c : word) = Some W_8b74c.
Proof. vm_refl. Qed.
Lemma D_8b74c : decode_any W_8b74c = Some (Load SZ8 true 22 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b750 : bv 32 := 0x00813b83.
Lemma F_8b750 : fetch_word Plain.M.loaded_segments (0x8b790 : word) = Some W_8b750.
Proof. vm_refl. Qed.
Lemma D_8b750 : decode_any W_8b750 = Some (Load SZ8 true 23 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b754 : bv 32 := 0x00013c03.
Lemma F_8b754 : fetch_word Plain.M.loaded_segments (0x8b794 : word) = Some W_8b754.
Proof. vm_refl. Qed.
Lemma D_8b754 : decode_any W_8b754 = Some (Load SZ8 true 24 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b758 : bv 32 := 0x05010113.
Lemma F_8b758 : fetch_word Plain.M.loaded_segments (0x8b798 : word) = Some W_8b758.
Proof. vm_refl. Qed.
Lemma D_8b758 : decode_any W_8b758 = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b75c : bv 32 := 0x00008067.
Lemma F_8b75c : fetch_word Plain.M.loaded_segments (0x8b79c : word) = Some W_8b75c.
Proof. vm_refl. Qed.
Lemma D_8b75c : decode_any W_8b75c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
End S1_code_8b58c_8b764.

Module S1_code_8b874_8b8c8.

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_8b874 : bv 32 := 0x00054703.
Lemma F_8b874 : fetch_word Plain.M.loaded_segments (0x8b8b4 : word) = Some W_8b874.
Proof. vm_refl. Qed.
Lemma D_8b874 : decode_any W_8b874 = Some (Load SZ1 false 14 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b878 : bv 32 := 0x00177693.
Lemma F_8b878 : fetch_word Plain.M.loaded_segments (0x8b8b8 : word) = Some W_8b878.
Proof. vm_refl. Qed.
Lemma D_8b878 : decode_any W_8b878 = Some (OpImm ALU_AND 13 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b87c : bv 32 := 0x02068463.
Lemma F_8b87c : fetch_word Plain.M.loaded_segments (0x8b8bc : word) = Some W_8b87c.
Proof. vm_refl. Qed.
Lemma D_8b87c : decode_any W_8b87c = Some (Branch BC_EQ 13 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b880 : bv 32 := 0x00853703.
Lemma F_8b880 : fetch_word Plain.M.loaded_segments (0x8b8c0 : word) = Some W_8b880.
Proof. vm_refl. Qed.
Lemma D_8b880 : decode_any W_8b880 = Some (Load SZ8 true 14 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b884 : bv 32 := 0x02b76463.
Lemma F_8b884 : fetch_word Plain.M.loaded_segments (0x8b8c4 : word) = Some W_8b884.
Proof. vm_refl. Qed.
Lemma D_8b884 : decode_any W_8b884 = Some (Branch BC_LTU 14 11 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b888 : bv 32 := 0x02069663.
Lemma F_8b888 : fetch_word Plain.M.loaded_segments (0x8b8c8 : word) = Some W_8b888.
Proof. vm_refl. Qed.
Lemma D_8b888 : decode_any W_8b888 = Some (Branch BC_NE 13 0 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b88c : bv 32 := 0x00150613.
Lemma F_8b88c : fetch_word Plain.M.loaded_segments (0x8b8cc : word) = Some W_8b88c.
Proof. vm_refl. Qed.
Lemma D_8b88c : decode_any W_8b88c = Some (OpImm ALU_ADD 12 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b890 : bv 32 := 0x00159693.
Lemma F_8b890 : fetch_word Plain.M.loaded_segments (0x8b8d0 : word) = Some W_8b890.
Proof. vm_refl. Qed.
Lemma D_8b890 : decode_any W_8b890 = Some (ShiftImm ALU_SLL 13 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b894 : bv 32 := 0x00d50023.
Lemma F_8b894 : fetch_word Plain.M.loaded_segments (0x8b8d4 : word) = Some W_8b894.
Proof. vm_refl. Qed.
Lemma D_8b894 : decode_any W_8b894 = Some (Store SZ1 10 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b898 : bv 32 := 0x00b605b3.
Lemma F_8b898 : fetch_word Plain.M.loaded_segments (0x8b8d8 : word) = Some W_8b898.
Proof. vm_refl. Qed.
Lemma D_8b898 : decode_any W_8b898 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b89c : bv 32 := 0x00058023.
Lemma F_8b89c : fetch_word Plain.M.loaded_segments (0x8b8dc : word) = Some W_8b89c.
Proof. vm_refl. Qed.
Lemma D_8b89c : decode_any W_8b89c = Some (Store SZ1 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b8a0 : bv 32 := 0x00008067.
Lemma F_8b8a0 : fetch_word Plain.M.loaded_segments (0x8b8e0 : word) = Some W_8b8a0.
Proof. vm_refl. Qed.
Lemma D_8b8a0 : decode_any W_8b8a0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b8a4 : bv 32 := 0x00175713.
Lemma F_8b8a4 : fetch_word Plain.M.loaded_segments (0x8b8e4 : word) = Some W_8b8a4.
Proof. vm_refl. Qed.
Lemma D_8b8a4 : decode_any W_8b8a4 = Some (ShiftImm ALU_SRL 14 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b8a8 : bv 32 := 0xfeb770e3.
Lemma F_8b8a8 : fetch_word Plain.M.loaded_segments (0x8b8e8 : word) = Some W_8b8a8.
Proof. vm_refl. Qed.
Lemma D_8b8a8 : decode_any W_8b8a8 = Some (Branch BC_GEU 14 11 8160, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b8ac : bv 32 := 0x40e585b3.
Lemma F_8b8ac : fetch_word Plain.M.loaded_segments (0x8b8ec : word) = Some W_8b8ac.
Proof. vm_refl. Qed.
Lemma D_8b8ac : decode_any W_8b8ac = Some (Op ALU_SUB 11 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b8b0 : bv 32 := 0xcddff06f.
Lemma F_8b8b0 : fetch_word Plain.M.loaded_segments (0x8b8f0 : word) = Some W_8b8b0.
Proof. vm_refl. Qed.
Lemma D_8b8b0 : decode_any W_8b8b0 = Some (Jal 0 2096348, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b8b4 : bv 32 := 0x01053603.
Lemma F_8b8b4 : fetch_word Plain.M.loaded_segments (0x8b8f4 : word) = Some W_8b8b4.
Proof. vm_refl. Qed.
Lemma D_8b8b4 : decode_any W_8b8b4 = Some (Load SZ8 true 12 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b8b8 : bv 32 := 0x00b53423.
Lemma F_8b8b8 : fetch_word Plain.M.loaded_segments (0x8b8f8 : word) = Some W_8b8b8.
Proof. vm_refl. Qed.
Lemma D_8b8b8 : decode_any W_8b8b8 = Some (Store SZ8 10 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b8bc : bv 32 := 0x00b605b3.
Lemma F_8b8bc : fetch_word Plain.M.loaded_segments (0x8b8fc : word) = Some W_8b8bc.
Proof. vm_refl. Qed.
Lemma D_8b8bc : decode_any W_8b8bc = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b8c0 : bv 32 := 0x00058023.
Lemma F_8b8c0 : fetch_word Plain.M.loaded_segments (0x8b900 : word) = Some W_8b8c0.
Proof. vm_refl. Qed.
Lemma D_8b8c0 : decode_any W_8b8c0 = Some (Store SZ1 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8b8c4 : bv 32 := 0x00008067.
Lemma F_8b8c4 : fetch_word Plain.M.loaded_segments (0x8b904 : word) = Some W_8b8c4.
Proof. vm_refl. Qed.
Lemma D_8b8c4 : decode_any W_8b8c4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
End S1_code_8b874_8b8c8.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac WalkTac StartupTac SumWalkTac StoreOk MemSplit Hoare ShapeAlg
  SRealizes RefMemcpyLib RefReadLib LibIface LibEff MmapSim SumMemsetLib SumMemset LibMaskBits S1Layout.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContLib StrLib ContStmts S1Facts Lib_Str_PushBack.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.Lib_Str_Resize.S1_code_8b58c_8b764. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.Lib_Str_Resize.S1_code_8b874_8b8c8.
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
Ltac slotv SL k H :=
  pose proof (SL k ltac:(lia)) as H;
  lazymatch type of H with rdn _ _ _ _ = Some (word_to_le_bytes 8 ?v) =>
    let v' := eval simpl in v in change v with v' in H end.
Ltac peel1 := repeat first [ rewrite rdn_wbytes_out_Z by (cbn [length]; rewrite ?repeat_length; len_simpl; lia) | rewrite rdn_wbytes_out by region_side ].
Ltac close_pc := lazymatch goal with |- msteps _ ?a ?bb => replace bb with a; [apply mst_refl|] end; f_equal; apply bv_eq; vm_compute; reflexivity.

Section Resize.
Context {AC : AllocCeiling}.
  Variable MI : MallocIface SEGS Ly.L.
  Variable ST : StaticsIface SEGS Ly.L.

  Definition APRO_vals (R : bvmap 5 word) (ret : Z) : list word :=
    [getr R 24%bv; getr R 23%bv; getr R 22%bv; getr R 21%bv; getr R 20%bv; getr R 19%bv; getr R 18%bv; getr R 9%bv; getr R 8%bv; Z_to_bv 64 ret].

  Lemma app_prologue : forall (fx : FPState) R M sp ret p,
    getr R 2%bv = Z_to_bv 64 sp -> getr R 1%bv = Z_to_bv 64 ret -> getr R 10%bv = Z_to_bv 64 p ->
    store_ok SEGS M (Z_to_bv 64 (sp - 80)) 80 = true -> 80 <= sp < 2 ^ 63 ->
    msteps SEGS (@mkst fx R (Z_to_bv 64 0x8b5cc) M (seg_rom SEGS))
                (@mkst fx (regupd (regupd R 2%bv (Z_to_bv 64 (sp - 80))) 8%bv (Z_to_bv 64 p))
                          (Z_to_bv 64 0x8b5fc) (wslots M sp (APRO_vals R ret)) (seg_rom SEGS)).
  Proof using.
    intros fx R M sp ret p Hsp Hra Ha0 HOK Hsp'.
    norm_pc.
    sv F_8b58c D_8b58c (Z_to_bv 64 (sp - 80)).
    stw F_8b590 D_8b590 (Z_to_bv 64 (sp - 8)) (Z_to_bv 64 ret) ltac:(ok_sub HOK).
    stw F_8b594 D_8b594 (Z_to_bv 64 (sp - 16)) (getr R 8%bv) ltac:(ok_sub HOK).
    stw F_8b598 D_8b598 (Z_to_bv 64 (sp - 24)) (getr R 9%bv) ltac:(ok_sub HOK).
    stw F_8b59c D_8b59c (Z_to_bv 64 (sp - 32)) (getr R 18%bv) ltac:(ok_sub HOK).
    stw F_8b5a0 D_8b5a0 (Z_to_bv 64 (sp - 40)) (getr R 19%bv) ltac:(ok_sub HOK).
    stw F_8b5a4 D_8b5a4 (Z_to_bv 64 (sp - 48)) (getr R 20%bv) ltac:(ok_sub HOK).
    stw F_8b5a8 D_8b5a8 (Z_to_bv 64 (sp - 56)) (getr R 21%bv) ltac:(ok_sub HOK).
    stw F_8b5ac D_8b5ac (Z_to_bv 64 (sp - 64)) (getr R 22%bv) ltac:(ok_sub HOK).
    stw F_8b5b0 D_8b5b0 (Z_to_bv 64 (sp - 72)) (getr R 23%bv) ltac:(ok_sub HOK).
    stw F_8b5b4 D_8b5b4 (Z_to_bv 64 (sp - 80)) (getr R 24%bv) ltac:(ok_sub HOK).
    sv F_8b5b8 D_8b5b8 (Z_to_bv 64 p).
    close_pc.
  Qed.

  Lemma app_epilogue : forall (fx : FPState) R M sp ret p (v8 v9 v18 v19 v20 v21 v22 v23 v24 : word),
    getr R 2%bv = Z_to_bv 64 (sp - 80) -> getr R 8%bv = Z_to_bv 64 p -> 80 <= sp < 2 ^ 63 ->
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
    msteps SEGS (@mkst fx R (Z_to_bv 64 0x8b76c) M (seg_rom SEGS))
                (@mkst fx (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd R
                             10%bv (Z_to_bv 64 p))
                             1%bv (Z_to_bv 64 ret)) 8%bv v8) 9%bv v9) 18%bv v18) 19%bv v19) 20%bv v20) 21%bv v21) 22%bv v22) 23%bv v23) 24%bv v24)
                             2%bv (Z_to_bv 64 sp))
                          (Z_to_bv 64 ret) M (seg_rom SEGS)).
  Proof using.
    intros fx R M sp ret p v8 v9 v18 v19 v20 v21 v22 v23 v24 Hsp Hs0 Hsp' L1 L8 L9 L18 L19 L20 L21 L22 L23 L24 Hret.
    norm_pc.
    sv F_8b72c D_8b72c (Z_to_bv 64 p).
    ld_step F_8b730 D_8b730 (word_to_le_bytes 8 (Z_to_bv 64 ret)) (Z_to_bv 64 ret) ltac:(rdn_fix L1) ltac:(b2z8).
    ld_step F_8b734 D_8b734 (word_to_le_bytes 8 v8) v8 ltac:(rdn_fix L8) ltac:(b2z8).
    ld_step F_8b738 D_8b738 (word_to_le_bytes 8 v9) v9 ltac:(rdn_fix L9) ltac:(b2z8).
    ld_step F_8b73c D_8b73c (word_to_le_bytes 8 v18) v18 ltac:(rdn_fix L18) ltac:(b2z8).
    ld_step F_8b740 D_8b740 (word_to_le_bytes 8 v19) v19 ltac:(rdn_fix L19) ltac:(b2z8).
    ld_step F_8b744 D_8b744 (word_to_le_bytes 8 v20) v20 ltac:(rdn_fix L20) ltac:(b2z8).
    ld_step F_8b748 D_8b748 (word_to_le_bytes 8 v21) v21 ltac:(rdn_fix L21) ltac:(b2z8).
    ld_step F_8b74c D_8b74c (word_to_le_bytes 8 v22) v22 ltac:(rdn_fix L22) ltac:(b2z8).
    ld_step F_8b750 D_8b750 (word_to_le_bytes 8 v23) v23 ltac:(rdn_fix L23) ltac:(b2z8).
    ld_step F_8b754 D_8b754 (word_to_le_bytes 8 v24) v24 ltac:(rdn_fix L24) ltac:(b2z8).
    sv F_8b758 D_8b758 (Z_to_bv 64 sp).
    stepjr F_8b75c D_8b75c (Z_to_bv 64 ret) ltac:(gres; reflexivity).
    lazymatch goal with |- msteps _ ?a ?bb => replace bb with a; [apply mst_refl|] end.
    f_equal. exact Hret.
  Qed.
  Theorem str_resize_8b820_spec : str_resize_stmt SEGS Ly.L MI c8b3ec.
  Proof using AC MI.
    intros fx A M R sp ret p n ch m cs.
    cbn [sc_resize sc_resize_stack c8b3ec]. lazy zeta.
    intros STR Hn HDd DISJ HROOM Hsplo Hsphi Hret Hra Hsp Ha0 Ha1 Ha2.
    pose proof HROOM as HOK. unfold stack_room in HOK.
    destruct STR as (Hp0 & Hp1 & HDp & Hlen & HM & FC & FN).
    remember (Zlen cs) as len eqn:Elen. remember (str_data p m) as dat eqn:Edat. remember (str_cap m) as cap eqn:Ecap.
    assert (Hlencs : Z.of_nat (length cs) = len) by (rewrite Elen; reflexivity).
    assert (DJp : p + 24 <= sp - 80 \/ sp <= p).
    { destruct (Z.lt_ge_cases p sp); [left|right; lia].
      destruct (Z.lt_ge_cases (p + 24) (sp - 80 + 1)); [lia|]. exfalso.
      destruct (Z.lt_ge_cases p (sp - 80)).
      - apply (DISJ (sp - 80)); [left|]; unfold zwin; lia.
      - apply (DISJ p); [left|]; unfold zwin; lia. }
    assert (Hdat : 0 <= dat /\ dat + cap + 1 <= 2 ^ 63).
    { destruct m as [|d asz]; subst dat cap; cbn [str_data str_cap]; unfold SSO_CAP; [lia|].
      destruct HM as (Hd0 & Hd16 & Hdsz & _). lia. }
    destruct Hdat as [Hdat0 Hdat1].
    assert (DJd : dat + cap + 1 <= sp - 80 \/ sp <= dat).
    { destruct (Z.lt_ge_cases dat sp); [left|right; lia].
      destruct (Z.lt_ge_cases (dat + cap + 1) (sp - 80 + 1)); [lia|]. exfalso.
      destruct (Z.lt_ge_cases dat (sp - 80)).
      - apply (DISJ (sp - 80)); [right|]; unfold zwin; lia.
      - apply (DISJ dat); [right|]; unfold zwin; lia. }
    clear DISJ. hide DJp. hide DJd.
    set (bch := Z_to_bv 8 (bv_unsigned (Z_to_bv 64 ch))).
    assert (Hbch : [bch] = word_to_le_bytes 1 (Z_to_bv 64 (ch mod 256))) by (unfold bch; apply sb_byte_w1).
    assert (Hcb : cbyte (Z_to_bv 64 ch) = bch) by reflexivity.
    assert (Hchr : 0 <= ch mod 256 < 256) by (apply Z.mod_pos_bound; lia).
    destruct m as [|d asz].
    -
      cbn [str_data str_cap] in Edat, Ecap. unfold SSO_CAP in Ecap. subst dat.
      assert (B0 : rdn SEGS M (Z_to_bv 64 p) 1 = Some [Z_to_bv 8 (2 * len)]).
      { pose proof (fld1_rdn SEGS M p (2 * len) HM) as X. rewrite Z.mod_small in X by lia. exact X. }
      destruct (Z.le_gt_cases n len) as [LE|GT].
      +
        set (M1 := wbytes M (Z_to_bv 64 p) [Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (n * 2 ^ 1)))]).
        set (M2 := wbytes M1 (Z_to_bv 64 (p + 1 + n)) [Z_to_bv 8 0]).
        assert (SI : stores_in (fun a => zwin p (p + 1) a \/ zwin (p + 1 + n) (p + 1 + n + 1) a) M M2).
        { unfold M2, M1. eapply stores_in_wbytes_more; [apply stores_in_wbytes | | |];
            cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; try lia; intros a Ha; unfold zwin in *; lia. }
        eexists. exists M2. split; [|split; [|split; [|split]]].
        * norm_pc.
          lb_step F_8b874 D_8b874 (Z_to_bv 8 (2 * len)) ltac:(rdn_fix B0).
          replace (Z_to_bv 64 (bv_unsigned (Z_to_bv 8 (2 * len)))) with (Z_to_bv 64 (2 * len)) by (rewrite u8_of_Z by lia; reflexivity).
          stepiv F_8b878 D_8b878 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite v_andi_Z by lia; rewrite even_land_1 by lia; reflexivity).
          stepb_tk F_8b87c D_8b87c ltac:(apply c_eq_refl).
          stepiv F_8b8a4 D_8b8a4 (Z_to_bv 64 len) ltac:(gres; pin; imm_norm; rewrite v_srli_Z by lia; f_equal; change (2^1) with 2; rewrite Z.mul_comm; apply Z.div_mul; lia).
          stepb_tk F_8b8a8 D_8b8a8 ltac:(rewrite Ha1; rewrite c_ltu_Z by lia; apply Z.ltb_ge; lia).
          stepb_ft F_8b888 D_8b888 ltac:(apply c_eq_refl).
          stepiv F_8b88c D_8b88c (Z_to_bv 64 (p + 1)) ltac:(gres; pin; imm_norm; rewrite v_addi_Z by lia; reflexivity).
          stepiv F_8b890 D_8b890 (Z_to_bv 64 (n * 2 ^ 1)) ltac:(gres; pin; imm_norm; rewrite v_slli_Z by lia; reflexivity).
          stw F_8b894 D_8b894 (Z_to_bv 64 p) (Z_to_bv 64 (n * 2 ^ 1)) ltac:(ok_mdef HDp).
          stepiv F_8b898 D_8b898 (Z_to_bv 64 (p + 1 + n)) ltac:(gres; pin; rewrite v_add_Z by lia; reflexivity).
          stw F_8b89c D_8b89c (Z_to_bv 64 (p + 1 + n)) (Z_to_bv 64 0) ltac:(ok_mdef HDp).
          stepjr F_8b8a0 D_8b8a0 (Z_to_bv 64 ret) ltac:(gres; exact Hra).
          fold M1. fold M2.
          lazymatch goal with |- msteps _ (mkst ?r ?pc _ _) (mkst ?r' _ _ _) => unify r' r;
            replace pc with (Z_to_bv 64 ret) by (symmetry; imm_norm; exact Hret) end. apply mst_refl.
        * intros r Hr; unfold callee_saved in Hr.
          repeat (destruct Hr as [<-|Hr]; [gres; first [reflexivity | assumption | symmetry; assumption] |]). destruct Hr.
        * assert (AG : forall lo hi, 0 <= lo -> hi < 2 ^ 64 -> (hi <= p \/ p + 1 <= lo) -> (hi <= p + 1 + n \/ p + 1 + n + 1 <= lo) ->
                       agree_on (zwin lo hi) M M2).
          { intros lo hi H1 H2 H3 H4. eapply stores_in_agree; [exact SI|]. intros a Ha. unfold zwin in *. lia. }
          unfold sresize_cs. rewrite <- Elen. destruct (Z.leb_spec n len); [|lia].
          unfold CRep.str_rep. rewrite Zlen_firstn by lia. cbn [str_cap str_data].
          split; [exact Hp0|]. split; [exact Hp1|]. split; [eapply stores_in_mdef; [exact SI|exact HDp]|].
          split; [unfold SSO_CAP; lia|].
          split. { unfold fld, M2, M1. peel1. replace (2 * n) with (n * 2 ^ 1) by lia.
                   change (word_to_le_bytes 1 (Z_to_bv 64 (n * 2 ^ 1))) with [Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (n * 2 ^ 1)))].
                   change 1%nat with (length [Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (n * 2 ^ 1)))]).
                   apply SeqExec.rdn_wbytes_hit. cbn [length]. rewrite u64_of_Z by lia. lia. }
          split.
          -- intros i Hi. rewrite Znth_firstn by lia. destruct (FC i ltac:(lia)) as [Hr HF]. split; [exact Hr|].
             eapply fld_agree; [lia|cbn; lia|exact HF|]. apply AG; cbn; lia.
          -- unfold fld, M2. change (word_to_le_bytes 1 (Z_to_bv 64 0)) with [Z_to_bv 8 0].
             change 1%nat with (length [Z_to_bv 8 0]). apply SeqExec.rdn_wbytes_hit. cbn [length]. rewrite u64_of_Z by lia. lia.
        * eapply stores_in_frame_eq; [exact SI|]. intros a [Ha|Ha]; [left | left]; unfold zwin in *; lia.
        * exact (proj2 SI).
      +
        set (cnt := n - len).
        destruct (mdef_rdn SEGS M p 24 1 7 HDp ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; lia)) as (bs7 & R7 & L7).
        assert (W0 : rdn SEGS M (Z_to_bv 64 p) 8 = Some (Z_to_bv 8 (2 * len) :: bs7)).
        { change 8%nat with (1 + 7)%nat. change (Z_to_bv 8 (2 * len) :: bs7) with ([Z_to_bv 8 (2 * len)] ++ bs7).
          apply rdn_app; [exact B0|]. replace (Z_to_bv 64 p + nat_to_word 1)%bv with (Z_to_bv 64 (p + 1)); [exact R7|].
          apply bv_eq. unfold nat_to_word. rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
          change (Z.of_nat 1) with 1. rewrite <- Zplus_mod. reflexivity. }
        set (V := bytes_le_to_Z (Z_to_bv 8 (2 * len) :: bs7)).
        assert (HV : V = 2 * len + 256 * bytes_le_to_Z bs7) by (unfold V; rewrite bytes_le_to_Z_cons, u8_of_Z by lia; reflexivity).
        pose proof (bytes_le_to_Z_nonneg bs7) as HX0.
        assert (HVr : 0 <= V < 2 ^ 64).
        { pose proof (bytes_le_to_Z_bound bs7) as HB. rewrite L7 in HB. cbn in HB. lia. }
        assert (HV1 : Z.land V 1 = 0).
        { rewrite land_1_mod by lia. rewrite HV. replace (2 * len + 256 * bytes_le_to_Z bs7) with ((len + 128 * bytes_le_to_Z bs7) * 2) by lia. apply Z_mod_mult. }
        assert (HV56 : Z_to_bv 64 (V * 2 ^ 56) = Z_to_bv 64 (2 * len * 2 ^ 56)) by (rewrite HV; apply shl56_low_byte; lia).

        set (R1 := regupd (regupd (regupd (regupd R 14%bv (Z_to_bv 64 (2 * len))) 13%bv (Z_to_bv 64 0)) 14%bv (Z_to_bv 64 len)) 11%bv (Z_to_bv 64 cnt)).
        assert (RUN1 : msteps SEGS (@mkst fx R (Z_to_bv 64 0x8b8b4) M (seg_rom SEGS)) (@mkst fx R1 (Z_to_bv 64 0x8b5cc) M (seg_rom SEGS))).
        { unfold R1. norm_pc.
          lb_step F_8b874 D_8b874 (Z_to_bv 8 (2 * len)) ltac:(rdn_fix B0).
          replace (Z_to_bv 64 (bv_unsigned (Z_to_bv 8 (2 * len)))) with (Z_to_bv 64 (2 * len)) by (rewrite u8_of_Z by lia; reflexivity).
          stepiv F_8b878 D_8b878 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite v_andi_Z by lia; rewrite even_land_1 by lia; reflexivity).
          stepb_tk F_8b87c D_8b87c ltac:(apply c_eq_refl).
          stepiv F_8b8a4 D_8b8a4 (Z_to_bv 64 len) ltac:(gres; pin; imm_norm; rewrite v_srli_Z by lia; f_equal; change (2^1) with 2; rewrite Z.mul_comm; apply Z.div_mul; lia).
          stepb_ft F_8b8a8 D_8b8a8 ltac:(rewrite Ha1; rewrite c_ltu_Z by lia; apply Z.ltb_lt; lia).
          stepiv F_8b8ac D_8b8ac (Z_to_bv 64 cnt) ltac:(gres; pin; unfold cnt; rewrite v_sub_Z by lia; reflexivity).
          stepj F_8b8b0 D_8b8b0. close_pc. }
        set (M1 := wslots M sp (APRO_vals R1 ret)).
        assert (SI1 : stores_in (zwin (sp - 80) sp) M M1).
        { unfold M1. apply (wslots_stores_in M sp (APRO_vals R1 ret)); unfold Zlen; cbn; lia. }
        assert (SL : forall k, 1 <= k <= 10 ->
                  rdn SEGS M1 (Z_to_bv 64 (sp - 8 * k)) 8
                  = Some (word_to_le_bytes 8 (nth (Z.to_nat (10 - k)) (APRO_vals R1 ret) (Z_to_bv 64 0)))).
        { intros k Hk. unfold M1. apply wslots_read; unfold Zlen; cbn; lia. }
        slotv SL 1 SL1. slotv SL 2 SL2. slotv SL 3 SL3. slotv SL 4 SL4. slotv SL 5 SL5.
        slotv SL 6 SL6. slotv SL 7 SL7. slotv SL 8 SL8. slotv SL 9 SL9. slotv SL 10 SL10. clear SL.
        assert (HDp1 : mdef M1 p 24) by (eapply stores_in_mdef; [exact SI1 | exact HDp]).
        assert (B01 : rdn SEGS M1 (Z_to_bv 64 p) 1 = Some [Z_to_bv 8 (2 * len)]).
        { unfold M1. rewrite wslots_out; [exact B0 | unfold Zlen; cbn; lia | lia | lia | cbn; lia | unfold Zlen; cbn; unhide DJp; lia]. }
        assert (W01 : rdn SEGS M1 (Z_to_bv 64 p) 8 = Some (Z_to_bv 8 (2 * len) :: bs7)).
        { unfold M1. rewrite wslots_out; [exact W0 | unfold Zlen; cbn; lia | lia | lia | cbn; lia | unfold Zlen; cbn; unhide DJp; lia]. }

        assert (B2 : exists R3,
          msteps SEGS (@mkst fx (regupd (regupd R1 2%bv (Z_to_bv 64 (sp - 80))) 8%bv (Z_to_bv 64 p)) (Z_to_bv 64 0x8b5fc) M1 (seg_rom SEGS))
                      (@mkst fx R3 s1_memset_entry M1 (seg_rom SEGS))
          /\ getr R3 10%bv = Z_to_bv 64 (p + 1 + len) /\ getr R3 11%bv = Z_to_bv 64 ch /\ getr R3 12%bv = Z_to_bv 64 cnt
          /\ getr R3 1%bv = Z_to_bv 64 0x8b748 /\ getr R3 2%bv = Z_to_bv 64 (sp - 80) /\ getr R3 8%bv = Z_to_bv 64 p
          /\ getr R3 20%bv = Z_to_bv 64 (p + 1) /\ getr R3 22%bv = Z_to_bv 64 n /\ getr R3 3%bv = getr R 3%bv /\ getr R3 4%bv = getr R 4%bv
          /\ (forall r, In r [25; 26; 27]%bv -> getr R3 r = getr R r)).
        { eexists. split.
          - unfold R1. norm_pc.
            stepb_ft F_8b5bc D_8b5bc ltac:(rewrite c_eq_Z' by lia; apply Z.eqb_neq; unfold cnt; lia).
            sv F_8b5c0 D_8b5c0 (Z_to_bv 64 cnt).
            lb_step F_8b5c4 D_8b5c4 (Z_to_bv 8 (2 * len)) ltac:(rdn_fix B01).
            replace (Z_to_bv 64 (bv_unsigned (Z_to_bv 8 (2 * len)))) with (Z_to_bv 64 (2 * len)) by (rewrite u8_of_Z by lia; reflexivity).
            ld_step F_8b5c8 D_8b5c8 (Z_to_bv 8 (2 * len) :: bs7) (Z_to_bv 64 V) ltac:(rdn_fix W01) ltac:(apply lez8_val; cbn [length]; rewrite L7; reflexivity).
            stepiv F_8b5cc D_8b5cc (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite v_andi_Z by lia; rewrite even_land_1 by lia; reflexivity).
            stepb_ft F_8b5d0 D_8b5d0 ltac:(apply c_eq_refl).
            sv F_8b5d4 D_8b5d4 (Z_to_bv 64 22).
            stepiv F_8b5d8 D_8b5d8 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite v_andi_Z by lia; rewrite HV1; reflexivity).
            stepb_ft F_8b5dc D_8b5dc ltac:(apply c_eq_refl).
            stepiv F_8b5e0 D_8b5e0 (Z_to_bv 64 (2 * len * 2 ^ 56)) ltac:(gres; pin; imm_norm; rewrite v_slli_Z by lia; exact HV56).
            stepiv F_8b5e4 D_8b5e4 (Z_to_bv 64 len) ltac:(gres; pin; imm_norm; rewrite v_srli_Z by lia; f_equal; replace (2 * len * 2 ^ 56) with (len * 2 ^ 57) by lia; apply Z.div_mul; lia).
            stepiv F_8b5e8 D_8b5e8 (Z_to_bv 64 (22 - len)) ltac:(gres; pin; rewrite v_sub_Z by lia; reflexivity).
            stepb_ft F_8b5ec D_8b5ec ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_ge; unfold cnt; lia).
            stepb_tk F_8b5f0 D_8b5f0 ltac:(apply c_eq_refl).
            stepiv F_8b65c D_8b65c (Z_to_bv 64 (p + 1)) ltac:(gres; pin; imm_norm; rewrite v_addi_Z by lia; reflexivity).
            stepiv F_8b660 D_8b660 (Z_to_bv 64 n) ltac:(gres; pin; unfold cnt; rewrite v_add_Z by lia; f_equal; lia).
            stepj F_8b664 D_8b664.
            stepiv F_8b6f8 D_8b6f8 (Z_to_bv 64 (p + 1 + len)) ltac:(gres; pin; rewrite v_add_Z by lia; reflexivity).
            sv F_8b6fc D_8b6fc (Z_to_bv 64 ch).
            sv F_8b700 D_8b700 (Z_to_bv 64 cnt).
            stepj F_8b704 D_8b704. close_pc.
          - gres. repeat split; try reflexivity; try assumption.
            intros r Hr. pose proof Hr as Hr'. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr. }
        destruct B2 as (R3 & RUN2 & R3_10 & R3_11 & R3_12 & R3_1 & R3_2 & R3_8 & R3_20 & R3_22 & R3_3 & R3_4 & R3S).

        destruct (s1_memset M1 (Z_to_bv 64 (p + 1 + len)) (Z_to_bv 64 ch) (Z_to_bv 64 0x8b748) cnt (seg_rom SEGS) R3
                    ltac:(unfold cnt; lia) ltac:(rewrite u64_of_Z by lia; unfold cnt; lia)
                    ltac:(replace (p + 1 + len) with (p + (1 + len)) by lia; apply (mdef_store_ok_off SEGS M1 p 24 (1 + len) (Z.to_nat cnt) HDp1); unfold cnt; lia)
                    ltac:(unfold ret_ok; apply bv_eq; vm_compute; reflexivity)
                    R3_10 R3_11 R3_12 R3_1)
          as (R4 & RUN4 & R4a0 & AGR4).
        rewrite Hcb in RUN4.
        set (M2 := wbytes M1 (Z_to_bv 64 (p + 1 + len)) (repeat bch (Z.to_nat cnt))) in *.
        assert (R4_2 : getr R4 2%bv = Z_to_bv 64 (sp - 80)) by (rewrite (ms_agree_getr _ _ 2%bv AGR4) by (first [solve [clear; cbv; intuition discriminate] | cbv; intuition discriminate]); exact R3_2).
        assert (R4_8 : getr R4 8%bv = Z_to_bv 64 p) by (rewrite (ms_agree_getr _ _ 8%bv AGR4) by (first [solve [clear; cbv; intuition discriminate] | cbv; intuition discriminate]); exact R3_8).
        assert (R4_20 : getr R4 20%bv = Z_to_bv 64 (p + 1)) by (rewrite (ms_agree_getr _ _ 20%bv AGR4) by (first [solve [clear; cbv; intuition discriminate] | cbv; intuition discriminate]); exact R3_20).
        assert (R4_22 : getr R4 22%bv = Z_to_bv 64 n) by (rewrite (ms_agree_getr _ _ 22%bv AGR4) by (first [solve [clear; cbv; intuition discriminate] | cbv; intuition discriminate]); exact R3_22).
        assert (R4_3 : getr R4 3%bv = getr R 3%bv) by (rewrite (ms_agree_getr _ _ 3%bv AGR4) by (first [solve [clear; cbv; intuition discriminate] | cbv; intuition discriminate]); exact R3_3).
        assert (R4_4 : getr R4 4%bv = getr R 4%bv) by (rewrite (ms_agree_getr _ _ 4%bv AGR4) by (first [solve [clear; cbv; intuition discriminate] | cbv; intuition discriminate]); exact R3_4).
        assert (R4S : forall r, In r [25; 26; 27]%bv -> getr R4 r = getr R r).
        { intros r Hr. pose proof Hr as Hr'. repeat (destruct Hr as [<-|Hr]; [rewrite (ms_agree_getr _ _ _ AGR4) by (first [solve [clear; cbv; intuition discriminate] | cbv; intuition discriminate]); apply R3S; exact Hr' |]). destruct Hr. }
        assert (B02 : rdn SEGS M2 (Z_to_bv 64 p) 1 = Some [Z_to_bv 8 (2 * len)]).
        { unfold M2. rewrite rdn_wbytes_out_Z by (rewrite repeat_length; cbn [Z.of_nat]; unfold cnt; lia). exact B01. }
        set (M3 := wbytes M2 (Z_to_bv 64 p) [Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (n * 2 ^ 1)))]).
        set (M4 := wbytes M3 (Z_to_bv 64 (p + 1 + n)) [Z_to_bv 8 0]).
        assert (HDp2 : mdef M2 p 24) by (unfold M2; apply mdef_wbytes; exact HDp1).
        assert (SI : stores_in (fun a => zwin (sp - 80) sp a \/ zwin p (p + 1) a \/ zwin (p + 1 + len) (p + 1 + n + 1) a) M M4).
        { unfold M4, M3, M2. eapply stores_in_wbytes_more; [eapply stores_in_wbytes_more; [eapply stores_in_wbytes_more; [eapply stores_in_weaken; [exact SI1|] | | |] | | |] | | |];
            rewrite ?repeat_length; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; unfold cnt; try lia; intros a Ha; unfold zwin in *; lia. }
        assert (SLT : forall a vv, sp - 80 <= a -> a + 8 <= sp -> rdn SEGS M1 (Z_to_bv 64 a) 8 = Some vv -> rdn SEGS M4 (Z_to_bv 64 a) 8 = Some vv).
        { intros a vv H1 H2 H3. unhide DJp. unfold M4, M3, M2. peel1. exact H3. }

        assert (B5 : msteps SEGS (@mkst fx R4 (Z_to_bv 64 0x8b748) M2 (seg_rom SEGS))
                       (@mkst fx (regupd (regupd (regupd (regupd R4 10%bv (Z_to_bv 64 (2 * len))) 10%bv (Z_to_bv 64 0)) 10%bv (Z_to_bv 64 (n * 2 ^ 1))) 20%bv (Z_to_bv 64 (p + 1 + n)))
                          (Z_to_bv 64 0x8b76c) M4 (seg_rom SEGS))).
        { norm_pc.
          lb_step F_8b708 D_8b708 (Z_to_bv 8 (2 * len)) ltac:(rdn_fix B02).
          replace (Z_to_bv 64 (bv_unsigned (Z_to_bv 8 (2 * len)))) with (Z_to_bv 64 (2 * len)) by (rewrite u8_of_Z by lia; reflexivity).
          stepiv F_8b70c D_8b70c (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite v_andi_Z by lia; rewrite even_land_1 by lia; reflexivity).
          stepb_ft F_8b710 D_8b710 ltac:(apply c_eq_refl).
          stepiv F_8b714 D_8b714 (Z_to_bv 64 (n * 2 ^ 1)) ltac:(gres; pin; imm_norm; rewrite v_slli_Z by lia; reflexivity).
          stw F_8b718 D_8b718 (Z_to_bv 64 p) (Z_to_bv 64 (n * 2 ^ 1)) ltac:(ok_mdef HDp2).
          stepj F_8b71c D_8b71c.
          stepiv F_8b724 D_8b724 (Z_to_bv 64 (p + 1 + n)) ltac:(gres; pin; rewrite v_add_Z by lia; f_equal; lia).
          stw F_8b728 D_8b728 (Z_to_bv 64 (p + 1 + n)) (Z_to_bv 64 0) ltac:(ok_mdef HDp2).
          fold M3. fold M4.
          lazymatch goal with |- msteps _ (mkst ?r ?pc _ _) (mkst ?r' ?pc' _ _) =>
            unify r r'; replace pc with pc' by (apply bv_eq; vm_compute; reflexivity); apply mst_refl end. }
        eexists. exists M4. split; [|split; [|split; [|split]]].
        * eapply msteps_trans; [exact RUN1|].
          eapply msteps_trans. { apply (app_prologue fx R1 M sp ret p); [unfold R1; gres; exact Hsp | unfold R1; gres; exact Hra | unfold R1; gres; exact Ha0 | ok_sub HOK | lia]. }
          fold M1.
          eapply msteps_trans; [exact RUN2|].
          eapply msteps_trans; [exact RUN4|].
          eapply msteps_trans; [exact B5|].
          apply (app_epilogue fx _ M4 sp ret p (getr R1 8%bv) (getr R1 9%bv) (getr R1 18%bv) (getr R1 19%bv) (getr R1 20%bv)
                   (getr R1 21%bv) (getr R1 22%bv) (getr R1 23%bv) (getr R1 24%bv));
            [ gres; exact R4_2 | gres; exact R4_8 | lia | | | | | | | | | | | exact Hret ].
          -- apply SLT; [lia|lia|rdn_fix SL1].
          -- apply SLT; [lia|lia|rdn_fix SL2].
          -- apply SLT; [lia|lia|rdn_fix SL3].
          -- apply SLT; [lia|lia|rdn_fix SL4].
          -- apply SLT; [lia|lia|rdn_fix SL5].
          -- apply SLT; [lia|lia|rdn_fix SL6].
          -- apply SLT; [lia|lia|rdn_fix SL7].
          -- apply SLT; [lia|lia|rdn_fix SL8].
          -- apply SLT; [lia|lia|rdn_fix SL9].
          -- apply SLT; [lia|lia|rdn_fix SL10].
        * intros r Hr; unfold callee_saved in Hr.
          repeat (destruct Hr as [<-|Hr]; [gres; first [reflexivity | assumption | symmetry; assumption | unfold R1; gres; reflexivity | apply R4S; in_cs] |]). destruct Hr.
        * assert (AG : forall lo hi, 0 <= lo -> hi < 2 ^ 64 -> (hi <= sp - 80 \/ sp <= lo) -> (hi <= p \/ p + 1 <= lo) ->
                       (hi <= p + 1 + len \/ p + 1 + n + 1 <= lo) -> agree_on (zwin lo hi) M M4).
          { intros lo hi H1 H2 H3 H4 H5. eapply stores_in_agree; [exact SI|]. intros a Ha. unfold zwin in *. lia. }
          unfold sresize_cs. rewrite <- Elen. destruct (Z.leb_spec n len); [lia|].
          unfold CRep.str_rep. rewrite Zlen_app, Zlen_repeat, <- Elen by lia. cbn [str_cap str_data].
          split; [exact Hp0|]. split; [exact Hp1|]. split; [eapply stores_in_mdef; [exact SI|exact HDp]|].
          split; [unfold SSO_CAP; lia|].
          split. { unfold fld, M4, M3. peel1. replace (2 * (len + (n - len))) with (n * 2 ^ 1) by lia.
                   change (word_to_le_bytes 1 (Z_to_bv 64 (n * 2 ^ 1))) with [Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (n * 2 ^ 1)))].
                   change 1%nat with (length [Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (n * 2 ^ 1)))]).
                   apply SeqExec.rdn_wbytes_hit. cbn [length]. rewrite u64_of_Z by lia. lia. }
          split.
          -- intros i Hi. destruct (Z.lt_ge_cases i len) as [Hlt|Hge].
             ++ rewrite Znth_app_l by lia. destruct (FC i ltac:(lia)) as [Hr HF]. split; [exact Hr|].
                eapply fld_agree; [lia|cbn; lia|exact HF|]. unhide DJp. apply AG; cbn; lia.
             ++ rewrite Znth_app_r, <- Elen, Znth_repeat by lia. split; [exact Hchr|].
                unfold fld, M4, M3. peel1. rewrite <- Hbch. unfold M2.
                replace (p + 1 + i) with (p + 1 + len + (i - len)) by lia.
                change [bch] with (repeat bch 1). apply rdn_repeat_sub; cbn [Z.of_nat]; unfold cnt; lia.
          -- unfold fld, M4. replace (p + 1 + (len + (n - len))) with (p + 1 + n) by lia.
             change (word_to_le_bytes 1 (Z_to_bv 64 0)) with [Z_to_bv 8 0].
             change 1%nat with (length [Z_to_bv 8 0]). apply SeqExec.rdn_wbytes_hit. cbn [length]. rewrite u64_of_Z by lia. lia.
        * eapply stores_in_frame_eq; [exact SI|]. intros a [Ha|[Ha|Ha]]; [right; right | left | right; left]; unfold zwin in *; lia.
        * exact (proj2 SI).
    -
      cbn [str_data str_cap] in Edat, Ecap. subst dat. rewrite Ecap in HDd. replace (asz - 1 + 1) with asz in HDd by lia.
      destruct HM as (Hd0 & Hd16 & Hdsz & Hsz8 & Hsz46 & HIn & Hdj & G0 & G1 & G2). unfold SSO_CAP in Hsz46.
      pose proof (Z.div_mod asz 8 ltac:(lia)) as Hd8. set (k8 := asz / 8) in Hd8. rewrite Hsz8, Z.add_0_r in Hd8.
      assert (Hodd : (asz + 1) mod 2 = 1).
      { rewrite Hd8. replace (8 * k8 + 1) with (1 + (4 * k8) * 2) by lia. rewrite Z_mod_plus_full. reflexivity. }
      assert (Hb0r : 0 <= (asz + 1) mod 256 < 256) by (apply Z.mod_pos_bound; lia).
      assert (B0 : rdn SEGS M (Z_to_bv 64 p) 1 = Some [Z_to_bv 8 ((asz + 1) mod 256)]) by (apply fld8_byte0; exact G0).
      unfold fld in G0, G1, G2.
      destruct (Z.le_gt_cases n len) as [LE|GT].
      +
        set (M1 := wbytes M (Z_to_bv 64 (p + 8)) (word_to_le_bytes 8 (Z_to_bv 64 n))).
        set (M2 := wbytes M1 (Z_to_bv 64 (d + n)) [Z_to_bv 8 0]).
        assert (SI : stores_in (fun a => zwin (p + 8) (p + 16) a \/ zwin (d + n) (d + n + 1) a) M M2).
        { unfold M2, M1. eapply stores_in_wbytes_more; [apply stores_in_wbytes | | |];
            rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; try lia; intros a Ha; unfold zwin in *; lia. }
        eexists. exists M2. split; [|split; [|split; [|split]]].
        * norm_pc.
          lb_step F_8b874 D_8b874 (Z_to_bv 8 ((asz + 1) mod 256)) ltac:(rdn_fix B0).
          replace (Z_to_bv 64 (bv_unsigned (Z_to_bv 8 ((asz + 1) mod 256)))) with (Z_to_bv 64 ((asz + 1) mod 256)) by (rewrite u8_of_Z by lia; reflexivity).
          stepiv F_8b878 D_8b878 (Z_to_bv 64 1) ltac:(gres; pin; imm_norm; rewrite v_andi_Z by lia; rewrite odd_byte0 by lia; reflexivity).
          stepb_ft F_8b87c D_8b87c ltac:(rewrite c_eq_Z' by lia; reflexivity).
          ld_step F_8b880 D_8b880 (word_to_le_bytes 8 (Z_to_bv 64 len)) (Z_to_bv 64 len) ltac:(rdn_fix G1) ltac:(b2z8).
          stepb_ft F_8b884 D_8b884 ltac:(rewrite Ha1; rewrite c_ltu_Z by lia; apply Z.ltb_ge; lia).
          stepb_tk F_8b888 D_8b888 ltac:(rewrite c_eq_Z' by lia; reflexivity).
          ld_step F_8b8b4 D_8b8b4 (word_to_le_bytes 8 (Z_to_bv 64 d)) (Z_to_bv 64 d) ltac:(rdn_fix G2) ltac:(b2z8).
          stw F_8b8b8 D_8b8b8 (Z_to_bv 64 (p + 8)) (Z_to_bv 64 n) ltac:(ok_mdef HDp).
          stepiv F_8b8bc D_8b8bc (Z_to_bv 64 (d + n)) ltac:(gres; pin; rewrite v_add_Z by lia; reflexivity).
          stw F_8b8c0 D_8b8c0 (Z_to_bv 64 (d + n)) (Z_to_bv 64 0) ltac:(ok_mdef HDd).
          stepjr F_8b8c4 D_8b8c4 (Z_to_bv 64 ret) ltac:(gres; exact Hra).
          fold M1. fold M2.
          lazymatch goal with |- msteps _ (mkst ?r ?pc _ _) (mkst ?r' _ _ _) => unify r' r;
            replace pc with (Z_to_bv 64 ret) by (symmetry; imm_norm; exact Hret) end. apply mst_refl.
        * intros r Hr; unfold callee_saved in Hr.
          repeat (destruct Hr as [<-|Hr]; [gres; first [reflexivity | assumption | symmetry; assumption] |]). destruct Hr.
        * assert (AG : forall lo hi, 0 <= lo -> hi < 2 ^ 64 -> (hi <= p + 8 \/ p + 16 <= lo) -> (hi <= d + n \/ d + n + 1 <= lo) ->
                       agree_on (zwin lo hi) M M2).
          { intros lo hi H1 H2 H3 H4. eapply stores_in_agree; [exact SI|]. intros a Ha. unfold zwin in *. lia. }
          unfold sresize_cs. rewrite <- Elen. destruct (Z.leb_spec n len); [|lia].
          unfold CRep.str_rep. rewrite Zlen_firstn by lia. cbn [str_cap str_data].
          split; [exact Hp0|]. split; [exact Hp1|]. split; [eapply stores_in_mdef; [exact SI|exact HDp]|].
          split; [lia|].
          split. { split; [lia|]. split; [exact Hd16|]. split; [lia|]. split; [exact Hsz8|]. split; [unfold SSO_CAP; lia|].
                   split; [exact HIn|]. split; [exact Hdj|].
                   split. { unfold fld. rewrite <- G0. apply rdn_agree_win; [lia|cbn; lia|]. apply AG; cbn; lia. }
                   split. { unfold fld, M2, M1. peel1. apply rdn_wbytes_hit8. rewrite u64_of_Z by lia. lia. }
                   unfold fld. rewrite <- G2. apply rdn_agree_win; [lia|cbn; lia|]. apply AG; cbn; lia. }
          split.
          -- intros i Hi. rewrite Znth_firstn by lia. destruct (FC i ltac:(lia)) as [Hr HF]. split; [exact Hr|].
             eapply fld_agree; [lia|cbn; lia|exact HF|]. apply AG; cbn; lia.
          -- unfold fld, M2. change (word_to_le_bytes 1 (Z_to_bv 64 0)) with [Z_to_bv 8 0].
             change 1%nat with (length [Z_to_bv 8 0]). apply SeqExec.rdn_wbytes_hit. cbn [length]. rewrite u64_of_Z by lia. lia.
        * eapply stores_in_frame_eq; [exact SI|]. intros a [Ha|Ha]; [left | right; left]; unfold zwin in *; lia.
        * exact (proj2 SI).
      +
        set (cnt := n - len).
        set (R1 := regupd (regupd (regupd (regupd R 14%bv (Z_to_bv 64 ((asz + 1) mod 256))) 13%bv (Z_to_bv 64 1)) 14%bv (Z_to_bv 64 len)) 11%bv (Z_to_bv 64 cnt)).
        assert (RUN1 : msteps SEGS (@mkst fx R (Z_to_bv 64 0x8b8b4) M (seg_rom SEGS)) (@mkst fx R1 (Z_to_bv 64 0x8b5cc) M (seg_rom SEGS))).
        { unfold R1. norm_pc.
          lb_step F_8b874 D_8b874 (Z_to_bv 8 ((asz + 1) mod 256)) ltac:(rdn_fix B0).
          replace (Z_to_bv 64 (bv_unsigned (Z_to_bv 8 ((asz + 1) mod 256)))) with (Z_to_bv 64 ((asz + 1) mod 256)) by (rewrite u8_of_Z by lia; reflexivity).
          stepiv F_8b878 D_8b878 (Z_to_bv 64 1) ltac:(gres; pin; imm_norm; rewrite v_andi_Z by lia; rewrite odd_byte0 by lia; reflexivity).
          stepb_ft F_8b87c D_8b87c ltac:(rewrite c_eq_Z' by lia; reflexivity).
          ld_step F_8b880 D_8b880 (word_to_le_bytes 8 (Z_to_bv 64 len)) (Z_to_bv 64 len) ltac:(rdn_fix G1) ltac:(b2z8).
          stepb_tk F_8b884 D_8b884 ltac:(rewrite Ha1; rewrite c_ltu_Z by lia; apply Z.ltb_lt; lia).
          stepiv F_8b8ac D_8b8ac (Z_to_bv 64 cnt) ltac:(gres; pin; unfold cnt; rewrite v_sub_Z by lia; reflexivity).
          stepj F_8b8b0 D_8b8b0. close_pc. }
        set (M1 := wslots M sp (APRO_vals R1 ret)).
        assert (SI1 : stores_in (zwin (sp - 80) sp) M M1).
        { unfold M1. apply (wslots_stores_in M sp (APRO_vals R1 ret)); unfold Zlen; cbn; lia. }
        assert (SL : forall k, 1 <= k <= 10 ->
                  rdn SEGS M1 (Z_to_bv 64 (sp - 8 * k)) 8
                  = Some (word_to_le_bytes 8 (nth (Z.to_nat (10 - k)) (APRO_vals R1 ret) (Z_to_bv 64 0)))).
        { intros k Hk. unfold M1. apply wslots_read; unfold Zlen; cbn; lia. }
        slotv SL 1 SL1. slotv SL 2 SL2. slotv SL 3 SL3. slotv SL 4 SL4. slotv SL 5 SL5.
        slotv SL 6 SL6. slotv SL 7 SL7. slotv SL 8 SL8. slotv SL 9 SL9. slotv SL 10 SL10. clear SL.
        assert (HDp1 : mdef M1 p 24) by (eapply stores_in_mdef; [exact SI1 | exact HDp]).
        assert (HDd1 : mdef M1 d asz) by (eapply stores_in_mdef; [exact SI1 | exact HDd]).
        assert (WSO : forall a (k : nat) v, (a + Z.of_nat k <= sp - 80 \/ sp <= a) -> 0 <= a -> a + Z.of_nat k < 2 ^ 64 ->
                  rdn SEGS M (Z_to_bv 64 a) k = Some v -> rdn SEGS M1 (Z_to_bv 64 a) k = Some v).
        { intros a k v H1 H2 H3 H4. unfold M1. rewrite wslots_out; [exact H4 | unfold Zlen; cbn; lia | lia | lia | lia | unfold Zlen; cbn; lia]. }
        unhide DJp.
        pose proof (WSO p 1%nat _ ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia) B0) as B01.
        pose proof (WSO p 8%nat _ ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia) G0) as G01.
        pose proof (WSO (p + 8) 8%nat _ ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia) G1) as G11.
        pose proof (WSO (p + 16) 8%nat _ ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia) G2) as G21.
        hide DJp.

        assert (B2 : exists R3,
          msteps SEGS (@mkst fx (regupd (regupd R1 2%bv (Z_to_bv 64 (sp - 80))) 8%bv (Z_to_bv 64 p)) (Z_to_bv 64 0x8b5fc) M1 (seg_rom SEGS))
                      (@mkst fx R3 s1_memset_entry M1 (seg_rom SEGS))
          /\ getr R3 10%bv = Z_to_bv 64 (d + len) /\ getr R3 11%bv = Z_to_bv 64 ch /\ getr R3 12%bv = Z_to_bv 64 cnt
          /\ getr R3 1%bv = Z_to_bv 64 0x8b748 /\ getr R3 2%bv = Z_to_bv 64 (sp - 80) /\ getr R3 8%bv = Z_to_bv 64 p
          /\ getr R3 20%bv = Z_to_bv 64 d /\ getr R3 22%bv = Z_to_bv 64 n /\ getr R3 3%bv = getr R 3%bv /\ getr R3 4%bv = getr R 4%bv
          /\ (forall r, In r [25; 26; 27]%bv -> getr R3 r = getr R r)).
        { eexists. split.
          - unfold R1. norm_pc.
            stepb_ft F_8b5bc D_8b5bc ltac:(rewrite c_eq_Z' by lia; apply Z.eqb_neq; unfold cnt; lia).
            sv F_8b5c0 D_8b5c0 (Z_to_bv 64 cnt).
            lb_step F_8b5c4 D_8b5c4 (Z_to_bv 8 ((asz + 1) mod 256)) ltac:(rdn_fix B01).
            replace (Z_to_bv 64 (bv_unsigned (Z_to_bv 8 ((asz + 1) mod 256)))) with (Z_to_bv 64 ((asz + 1) mod 256)) by (rewrite u8_of_Z by lia; reflexivity).
            ld_step F_8b5c8 D_8b5c8 (word_to_le_bytes 8 (Z_to_bv 64 (asz + 1))) (Z_to_bv 64 (asz + 1)) ltac:(rdn_fix G01) ltac:(b2z8).
            stepiv F_8b5cc D_8b5cc (Z_to_bv 64 1) ltac:(gres; pin; imm_norm; rewrite v_andi_Z by lia; rewrite odd_byte0 by lia; reflexivity).
            stepb_tk F_8b5d0 D_8b5d0 ltac:(rewrite c_eq_Z' by lia; reflexivity).
            stepiv F_8b5fc D_8b5fc (Z_to_bv 64 asz)
              ltac:(gres; pin; imm_norm; unfold v_andi; rewrite u64_of_Z by lia; change (bv_wrap 64 (-2)) with (2 ^ 64 - 2);
                    rewrite land_m2_64 by lia; rewrite Hodd; f_equal; lia).
            stepiv F_8b600 D_8b600 (Z_to_bv 64 (asz - 1)) ltac:(gres; pin; imm_norm; rewrite v_addi_Z by lia; f_equal; lia).
            stepiv F_8b604 D_8b604 (Z_to_bv 64 1) ltac:(gres; pin; imm_norm; rewrite v_andi_Z by lia; rewrite land_1_mod, Hodd by lia; reflexivity).
            stepb_ft F_8b608 D_8b608 ltac:(rewrite c_eq_Z' by lia; reflexivity).
            ld_step F_8b60c D_8b60c (word_to_le_bytes 8 (Z_to_bv 64 len)) (Z_to_bv 64 len) ltac:(rdn_fix G11) ltac:(b2z8).
            stepiv F_8b610 D_8b610 (Z_to_bv 64 (asz - 1 - len)) ltac:(gres; pin; rewrite v_sub_Z by lia; reflexivity).
            stepb_tk F_8b614 D_8b614 ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_ge; unfold cnt; lia).
            stepb_ft F_8b5f0 D_8b5f0 ltac:(rewrite c_eq_Z' by lia; reflexivity).
            ld_step F_8b5f4 D_8b5f4 (word_to_le_bytes 8 (Z_to_bv 64 d)) (Z_to_bv 64 d) ltac:(rdn_fix G21) ltac:(b2z8).
            stepj F_8b5f8 D_8b5f8.
            stepiv F_8b660 D_8b660 (Z_to_bv 64 n) ltac:(gres; pin; unfold cnt; rewrite v_add_Z by lia; f_equal; lia).
            stepj F_8b664 D_8b664.
            stepiv F_8b6f8 D_8b6f8 (Z_to_bv 64 (d + len)) ltac:(gres; pin; rewrite v_add_Z by lia; reflexivity).
            sv F_8b6fc D_8b6fc (Z_to_bv 64 ch).
            sv F_8b700 D_8b700 (Z_to_bv 64 cnt).
            stepj F_8b704 D_8b704. close_pc.
          - gres. repeat split; try reflexivity; try assumption.
            intros r Hr. pose proof Hr as Hr'. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr. }
        destruct B2 as (R3 & RUN2 & R3_10 & R3_11 & R3_12 & R3_1 & R3_2 & R3_8 & R3_20 & R3_22 & R3_3 & R3_4 & R3S).

        destruct (s1_memset M1 (Z_to_bv 64 (d + len)) (Z_to_bv 64 ch) (Z_to_bv 64 0x8b748) cnt (seg_rom SEGS) R3
                    ltac:(unfold cnt; lia) ltac:(rewrite u64_of_Z by lia; unfold cnt; lia)
                    ltac:(apply (mdef_store_ok_off SEGS M1 d asz len (Z.to_nat cnt) HDd1); unfold cnt; lia)
                    ltac:(unfold ret_ok; apply bv_eq; vm_compute; reflexivity)
                    R3_10 R3_11 R3_12 R3_1)
          as (R4 & RUN4 & R4a0 & AGR4).
        rewrite Hcb in RUN4.
        set (M2 := wbytes M1 (Z_to_bv 64 (d + len)) (repeat bch (Z.to_nat cnt))) in *.
        assert (R4_2 : getr R4 2%bv = Z_to_bv 64 (sp - 80)) by (rewrite (ms_agree_getr _ _ 2%bv AGR4) by (first [solve [clear; cbv; intuition discriminate] | cbv; intuition discriminate]); exact R3_2).
        assert (R4_8 : getr R4 8%bv = Z_to_bv 64 p) by (rewrite (ms_agree_getr _ _ 8%bv AGR4) by (first [solve [clear; cbv; intuition discriminate] | cbv; intuition discriminate]); exact R3_8).
        assert (R4_20 : getr R4 20%bv = Z_to_bv 64 d) by (rewrite (ms_agree_getr _ _ 20%bv AGR4) by (first [solve [clear; cbv; intuition discriminate] | cbv; intuition discriminate]); exact R3_20).
        assert (R4_22 : getr R4 22%bv = Z_to_bv 64 n) by (rewrite (ms_agree_getr _ _ 22%bv AGR4) by (first [solve [clear; cbv; intuition discriminate] | cbv; intuition discriminate]); exact R3_22).
        assert (R4_3 : getr R4 3%bv = getr R 3%bv) by (rewrite (ms_agree_getr _ _ 3%bv AGR4) by (first [solve [clear; cbv; intuition discriminate] | cbv; intuition discriminate]); exact R3_3).
        assert (R4_4 : getr R4 4%bv = getr R 4%bv) by (rewrite (ms_agree_getr _ _ 4%bv AGR4) by (first [solve [clear; cbv; intuition discriminate] | cbv; intuition discriminate]); exact R3_4).
        assert (R4S : forall r, In r [25; 26; 27]%bv -> getr R4 r = getr R r).
        { intros r Hr. pose proof Hr as Hr'. repeat (destruct Hr as [<-|Hr]; [rewrite (ms_agree_getr _ _ _ AGR4) by (first [solve [clear; cbv; intuition discriminate] | cbv; intuition discriminate]); apply R3S; exact Hr' |]). destruct Hr. }
        assert (B02 : rdn SEGS M2 (Z_to_bv 64 p) 1 = Some [Z_to_bv 8 ((asz + 1) mod 256)]).
        { unfold M2. rewrite rdn_wbytes_out_Z by (rewrite repeat_length; cbn [Z.of_nat]; unfold cnt; lia). exact B01. }
        set (M3 := wbytes M2 (Z_to_bv 64 (p + 8)) (word_to_le_bytes 8 (Z_to_bv 64 n))).
        set (M4 := wbytes M3 (Z_to_bv 64 (d + n)) [Z_to_bv 8 0]).
        assert (HDp2 : mdef M2 p 24) by (unfold M2; apply mdef_wbytes; exact HDp1).
        assert (HDd2 : mdef M2 d asz) by (unfold M2; apply mdef_wbytes; exact HDd1).
        assert (SI : stores_in (fun a => zwin (sp - 80) sp a \/ zwin (p + 8) (p + 16) a \/ zwin (d + len) (d + n + 1) a) M M4).
        { unfold M4, M3, M2. eapply stores_in_wbytes_more; [eapply stores_in_wbytes_more; [eapply stores_in_wbytes_more; [eapply stores_in_weaken; [exact SI1|] | | |] | | |] | | |];
            rewrite ?repeat_length, ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; unfold cnt; try lia; intros a Ha; unfold zwin in *; lia. }
        assert (SLT : forall a vv, sp - 80 <= a -> a + 8 <= sp -> rdn SEGS M1 (Z_to_bv 64 a) 8 = Some vv -> rdn SEGS M4 (Z_to_bv 64 a) 8 = Some vv).
        { intros a vv H1 H2 H3. unhide DJp. unhide DJd. unfold M4, M3, M2. peel1. exact H3. }
        assert (B5 : msteps SEGS (@mkst fx R4 (Z_to_bv 64 0x8b748) M2 (seg_rom SEGS))
                       (@mkst fx (regupd (regupd (regupd R4 10%bv (Z_to_bv 64 ((asz + 1) mod 256))) 10%bv (Z_to_bv 64 1)) 20%bv (Z_to_bv 64 (d + n)))
                          (Z_to_bv 64 0x8b76c) M4 (seg_rom SEGS))).
        { norm_pc.
          lb_step F_8b708 D_8b708 (Z_to_bv 8 ((asz + 1) mod 256)) ltac:(rdn_fix B02).
          replace (Z_to_bv 64 (bv_unsigned (Z_to_bv 8 ((asz + 1) mod 256)))) with (Z_to_bv 64 ((asz + 1) mod 256)) by (rewrite u8_of_Z by lia; reflexivity).
          stepiv F_8b70c D_8b70c (Z_to_bv 64 1) ltac:(gres; pin; imm_norm; rewrite v_andi_Z by lia; rewrite odd_byte0 by lia; reflexivity).
          stepb_tk F_8b710 D_8b710 ltac:(rewrite c_eq_Z' by lia; reflexivity).
          stw F_8b720 D_8b720 (Z_to_bv 64 (p + 8)) (Z_to_bv 64 n) ltac:(ok_mdef HDp2).
          stepiv F_8b724 D_8b724 (Z_to_bv 64 (d + n)) ltac:(gres; pin; unfold cnt; rewrite v_add_Z by lia; f_equal; lia).
          stw F_8b728 D_8b728 (Z_to_bv 64 (d + n)) (Z_to_bv 64 0) ltac:(ok_mdef HDd2).
          fold M3. fold M4.
          lazymatch goal with |- msteps _ (mkst ?r ?pc _ _) (mkst ?r' ?pc' _ _) =>
            unify r r'; replace pc with pc' by (apply bv_eq; vm_compute; reflexivity); apply mst_refl end. }
        eexists. exists M4. split; [|split; [|split; [|split]]].
        * eapply msteps_trans; [exact RUN1|].
          eapply msteps_trans. { apply (app_prologue fx R1 M sp ret p); [unfold R1; gres; exact Hsp | unfold R1; gres; exact Hra | unfold R1; gres; exact Ha0 | ok_sub HOK | lia]. }
          fold M1.
          eapply msteps_trans; [exact RUN2|].
          eapply msteps_trans; [exact RUN4|].
          eapply msteps_trans; [exact B5|].
          apply (app_epilogue fx _ M4 sp ret p (getr R1 8%bv) (getr R1 9%bv) (getr R1 18%bv) (getr R1 19%bv) (getr R1 20%bv)
                   (getr R1 21%bv) (getr R1 22%bv) (getr R1 23%bv) (getr R1 24%bv));
            [ gres; exact R4_2 | gres; exact R4_8 | lia | | | | | | | | | | | exact Hret ].
          -- apply SLT; [lia|lia|rdn_fix SL1].
          -- apply SLT; [lia|lia|rdn_fix SL2].
          -- apply SLT; [lia|lia|rdn_fix SL3].
          -- apply SLT; [lia|lia|rdn_fix SL4].
          -- apply SLT; [lia|lia|rdn_fix SL5].
          -- apply SLT; [lia|lia|rdn_fix SL6].
          -- apply SLT; [lia|lia|rdn_fix SL7].
          -- apply SLT; [lia|lia|rdn_fix SL8].
          -- apply SLT; [lia|lia|rdn_fix SL9].
          -- apply SLT; [lia|lia|rdn_fix SL10].
        * intros r Hr; unfold callee_saved in Hr.
          repeat (destruct Hr as [<-|Hr]; [gres; first [reflexivity | assumption | symmetry; assumption | unfold R1; gres; reflexivity | apply R4S; in_cs] |]). destruct Hr.
        * assert (AG : forall lo hi, 0 <= lo -> hi < 2 ^ 64 -> (hi <= sp - 80 \/ sp <= lo) -> (hi <= p + 8 \/ p + 16 <= lo) ->
                       (hi <= d + len \/ d + n + 1 <= lo) -> agree_on (zwin lo hi) M M4).
          { intros lo hi H1 H2 H3 H4 H5. eapply stores_in_agree; [exact SI|]. intros a Ha. unfold zwin in *. lia. }
          unhide DJp. unhide DJd.
          unfold sresize_cs. rewrite <- Elen. destruct (Z.leb_spec n len); [lia|].
          unfold CRep.str_rep. rewrite Zlen_app, Zlen_repeat, <- Elen by lia. cbn [str_cap str_data].
          split; [exact Hp0|]. split; [exact Hp1|]. split; [eapply stores_in_mdef; [exact SI|exact HDp]|].
          split; [lia|].
          split. { split; [lia|]. split; [exact Hd16|]. split; [lia|]. split; [exact Hsz8|]. split; [unfold SSO_CAP; lia|].
                   split; [exact HIn|]. split; [exact Hdj|].
                   split. { unfold fld. rewrite <- G0. apply rdn_agree_win; [lia|cbn; lia|]. apply AG; cbn; lia. }
                   split. { unfold fld, M4, M3. peel1. replace (len + (n - len)) with n by lia. apply rdn_wbytes_hit8. rewrite u64_of_Z by lia. lia. }
                   unfold fld. rewrite <- G2. apply rdn_agree_win; [lia|cbn; lia|]. apply AG; cbn; lia. }
          split.
          -- intros i Hi. destruct (Z.lt_ge_cases i len) as [Hlt|Hge].
             ++ rewrite Znth_app_l by lia. destruct (FC i ltac:(lia)) as [Hr HF]. split; [exact Hr|].
                eapply fld_agree; [lia|cbn; lia|exact HF|]. apply AG; cbn; lia.
             ++ rewrite Znth_app_r, <- Elen, Znth_repeat by lia. split; [exact Hchr|].
                unfold fld, M4, M3. peel1. rewrite <- Hbch. unfold M2.
                replace (d + i) with (d + len + (i - len)) by lia.
                change [bch] with (repeat bch 1). apply rdn_repeat_sub; cbn [Z.of_nat]; unfold cnt; lia.
          -- unfold fld, M4. replace (d + (len + (n - len))) with (d + n) by lia.
             change (word_to_le_bytes 1 (Z_to_bv 64 0)) with [Z_to_bv 8 0].
             change 1%nat with (length [Z_to_bv 8 0]). apply SeqExec.rdn_wbytes_hit. cbn [length]. rewrite u64_of_Z by lia. lia.
        * eapply stores_in_frame_eq; [exact SI|]. intros a [Ha|[Ha|Ha]]; [right; right | left | right; left]; unfold zwin in *; lia.
        * exact (proj2 SI).
  Qed.
End Resize.
